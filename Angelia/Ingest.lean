import Angelia.Db
import Angelia.Config

/-!
# Ingestion

The single path every event takes, whichever connector delivered it: store the raw event
(deduplicated on `(source, externalId)`), normalise it, write the notification, apply the rules.
Because the raw insert is idempotent, connectors are free to deliver at-least-once — a push path
and a backfill path overlapping is harmless.
-/

open Lean

namespace Angelia

/-- How one kind of source turns its raw payloads into notifications. Pure, so it can be replayed
    over the stored history and tested against recorded payloads. -/
abbrev Normalizer := Json → Except String NotificationData

/-- What changed: some notifications, or `none` for a change that may touch any of them. -/
abbrev Change := Option (Array Int)

/-- A sequence number and the most recent changes, so live clients (SSE) can tell something they
    may see happened without polling the database. -/
initialize changeLog : IO.Ref (Nat × Array (Nat × Change)) ← IO.mkRef (0, #[])

private def changeLogSize : Nat := 256

def bumpChanges (c : Change) : IO Unit := changeLog.modify fun (seq, log) =>
  let log := log.push (seq + 1, c)
  let log := if log.size > changeLogSize then log.extract (log.size - changeLogSize) log.size else log
  (seq + 1, log)

/-- The current sequence number and what changed after `seen`, merged. A client further behind
    than the log reaches gets `none`, i.e. "anything may have changed". -/
def changesSince (seen : Nat) : IO (Nat × Change) := do
  let (seq, log) ← changeLog.get
  let newer := log.filter (·.1 > seen)
  if newer.size < seq - seen then return (seq, none)
  return (seq, newer.foldl (fun acc (_, c) => do (← acc) ++ (← c)) (some #[]))

/-- The context a connector runs in. -/
structure ConnectorCtx where
  source : SourceConfig
  dbPath : System.FilePath
  /-- A connection owned by this connector's thread. -/
  db : Db.Conn
  normalize : Normalizer
  /-- Set when the server is shutting down. -/
  stop : IO.Ref Bool

namespace ConnectorCtx

def name (c : ConnectorCtx) : String := c.source.name

/-- A copy of the context with its own database connection, for a worker on another thread. -/
def fork (c : ConnectorCtx) : IO ConnectorCtx := return { c with db := ← Db.connect c.dbPath }

def log (c : ConnectorCtx) (msg : String) : IO Unit := Angelia.log c.name msg

/-- Ingest a batch in one transaction. Returns how many events were new. A payload that fails to
    normalise is still stored raw (and logged), so fixing the normaliser and replaying recovers it. -/
def ingest (c : ConnectorCtx) (events : Array RawEvent) : IO Nat := do
  if events.isEmpty then return 0
  let now ← nowSeconds
  let (fresh, ids) ← Db.withTransaction c.db do
    let rules ← Db.listRules c.db
    let mut fresh := 0
    let mut ids := #[]
    for ev in events do
      let some rawId ← Db.insertRaw c.db c.name ev now | continue
      fresh := fresh + 1
      match c.normalize ev.payload with
      | .error e => c.log s!"cannot normalise {ev.externalId}: {e}"
      | .ok n =>
        let o := evaluate rules c.name n
        let id ← Db.upsertNotification c.db rawId c.name ev.externalId n now
          (n.read || o.markRead) o.archive
        Db.applyOutcomeLabels c.db id o
        ids := ids.push id
    return (fresh, ids)
  if fresh > 0 then
    Db.countEvents c.db c.name fresh
    bumpChanges (some ids)
  return fresh

def getCursor (c : ConnectorCtx) (key : String) : IO (Option Json) := Db.getCursor c.db c.name key

def setCursor (c : ConnectorCtx) (key : String) (v : Json) : IO Unit := Db.setCursor c.db c.name key v

def health (c : ConnectorCtx) (state : String) (detail : Option String := none)
    (error : Option String := none) : IO Unit :=
  Db.reportHealth c.db c.name c.source.kind state detail error

def stopping (c : ConnectorCtx) : IO Bool := c.stop.get

/-- Sleep in small steps so a shutdown is noticed promptly. Returns `false` if stopping. -/
def sleep (c : ConnectorCtx) (seconds : Nat) : IO Bool := do
  for _ in [0:seconds] do
    if ← c.stopping then return false
    IO.sleep 1000
  return !(← c.stopping)

/-- Run `body` forever, restarting it after a failure with exponential backoff (capped at five
    minutes). A failure is recorded in the health table, which is how a broken connector becomes
    visible rather than merely quiet. -/
partial def supervise (c : ConnectorCtx) (body : IO Unit) : IO Unit := do
  let rec loop (backoff : Nat) : IO Unit := do
    if ← c.stopping then return
    let started ← IO.monoMsNow
    try
      body
    catch e =>
      c.log s!"error: {e}"
      try c.health "error" none (some (toString e)) catch _ => pure ()
    -- A run that lasted a while was healthy; start the backoff over.
    let ranFor := (← IO.monoMsNow) - started
    let backoff := if ranFor > 120000 then 5 else backoff
    if ← c.sleep backoff then loop (min (backoff * 2) 300)
  loop 5

end ConnectorCtx

/-- Re-derive every notification from its raw event with the current normalisers. User state
    (read/archived/starred, manual labels) is kept. Returns `(replayed, failed)`. -/
def replay (db : Db.Conn) (normalizerFor : String → Option Normalizer) (source : Option String) :
    IO (Nat × Nat) := Db.withTransaction db do
  let mut ok := 0
  let mut failed := 0
  for (rawId, src, externalId, receivedAt, payload) in ← Db.rawEvents db source do
    let some normalize := normalizerFor src | failed := failed + 1; continue
    match normalize payload with
    | .ok n =>
      discard <| Db.upsertNotification db rawId src externalId n receivedAt n.read false
      ok := ok + 1
    | .error e =>
      log "replay" s!"{src}/{externalId}: {e}"
      failed := failed + 1
  return (ok, failed)

end Angelia