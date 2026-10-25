import Angelia.Ingest
import Angelia.Imap.Client
import Angelia.Mail.Mime
import Angelia.OAuth2
import Std.Sync.Mutex

/-!
# E-mail over IMAP

Works with any provider that speaks IMAP4rev1. One worker (and connection) per watched folder:

* **Backfill** — on every (re)connect and after every `IDLE` cycle, fetch everything above the
  stored `(UIDVALIDITY, last UID)` cursor. This is what guarantees nothing is missed: a dropped
  connection or a lost `IDLE` notification only delays a message until the next sync.
* **Push** — between syncs, sit in `IDLE` (RFC 2177) and wake as soon as the server reports new
  mail. `IDLE` is re-issued every `idleMinutes`, and a connection that does not answer `DONE`
  within a minute is treated as dead — a NAT box silently dropping the connection is otherwise
  indistinguishable from a quiet mailbox, so this bounds how late mail can be in that case. Servers without `IDLE` are polled.

On first sync (or if the server reset `UIDVALIDITY`) only the newest `initialSync` messages are
imported. Messages are deduplicated on `Message-ID`, so a message filed in two watched folders, or
re-numbered by a `UIDVALIDITY` reset, is stored once.

Settings: `host`, `port` (993), `tls` (`implicit` | `starttls`), `username`, and either `password` /
`passwordCommand` or, for providers that only allow OAuth (Microsoft 365, Gmail without app
passwords), either `accessTokenCommand` — a helper such as `mutt_oauth2.py` or `oama` that prints a
fresh access token; it is run on every connect, so it owns refreshing — or `oauth2` (`{"tokenUrl",
"clientId", "scope"}`) with `refreshToken` / `refreshTokenCommand`, and angelia refreshes by itself:
access tokens are cached until shortly before they expire, and a rotated refresh token is kept
(encrypted) in the database, preferred over the configured one, which stays the fallback. Further:
`folders` (`["INBOX"]`), `initialSync` (50), `maxBytes` (52428800), `idleMinutes` (5), `pollSeconds`
(120, without `IDLE`), `transport` (argv, overrides the TLS transport — for tests).
-/

open Lean Angelia.Imap

namespace Angelia.Connector.ImapSource

/-- How much of a message is fetched: whole messages, attachments included, up to a size no mail
    server sends anyway. A larger one is stored cut off there, and marked `truncated`. -/
def defaultMaxBytes : Nat := 50 * 1024 * 1024

structure Settings where
  transport : Transport
  username : String
  /-- Looked up on every connect, so a token helper can hand out fresh tokens. -/
  credentials : IO Conn.Credentials
  folders : Array String
  initialSync : Nat
  maxBytes : Nat
  idleMinutes : Nat
  pollSeconds : Nat

/-- Access tokens from a refresh token, renewed two minutes before they expire. The newest refresh
    token is kept in the database; the configured one is tried when that fails, so provisioning a
    fresh one after a revocation is just changing the configuration. -/
def oauth2Credentials (source : String) (dbPath : System.FilePath) (j : Json) (username : String)
    (client : OAuth2.Client) : IO (IO Conn.Credentials) := do
  let cache ← Std.Mutex.new (none : Option (String × Int))
  return cache.atomically do
    let now ← nowSeconds
    if let some (token, expires) ← get then
      if now + 120 < expires then return .oauth2 username token
    let db ← Db.connect dbPath
    let stored ← Db.getSecret db source "oauth2RefreshToken"
    let configured ← secret j "refreshToken"
    let candidates := [stored, configured.filter (some · != stored)].filterMap id
    if candidates.isEmpty then
      throw (IO.userError "imap: 'oauth2' needs 'refreshToken' or 'refreshTokenCommand'")
    let mut errors := #[]
    for rt in candidates do
      match ← client.refresh rt with
      | .ok g =>
        if let some next := g.refreshToken then Db.setSecret db source "oauth2RefreshToken" next
        set (some (g.accessToken, now + g.expiresIn))
        return .oauth2 username g.accessToken
      | .error e => errors := errors.push e
    throw (IO.userError s!"imap: token refresh failed: {"; ".intercalate errors.toList}")

def Settings.load (source : String) (dbPath : System.FilePath) (j : Json) : IO Settings := do
  let get {α} [FromJson α] (k : String) (d : α) : α := (j.getObjValAs? α k).toOption.getD d
  let host : String := get "host" ""
  let port : Nat := get "port" (if get "tls" "implicit" == "starttls" then 143 else 993)
  let transport ← match j.getObjValAs? (Array String) "transport" with
    | .ok argv => pure (Transport.command argv)
    | .error _ =>
      if host.isEmpty then throw (IO.userError "imap: 'host' is required")
      pure (if (get "tls" "implicit" : String) == "starttls" then .startTls host port else .implicitTls host port)
  let username : String := get "username" ""
  let credentials : IO Conn.Credentials ← match j.getObjValAs? OAuth2.Client "oauth2" with
    | .ok client => oauth2Credentials source dbPath j username client
    | .error _ => pure do
      if let some token ← secret j "accessToken" then return .oauth2 username token
      let some password ← secret j "password"
        | throw (IO.userError
            "imap: 'password', 'passwordCommand', 'accessTokenCommand' or 'oauth2' is required")
      return .password username password
  -- Fail at startup, not on the first connect, if the secret cannot be had at all.
  let _ ← credentials
  return {
    transport, username, credentials
    folders := get "folders" #["INBOX"]
    initialSync := get "initialSync" 50
    maxBytes := get "maxBytes" defaultMaxBytes
    idleMinutes := get "idleMinutes" 5
    pollSeconds := get "pollSeconds" 120 }

/-! ## Normalisation -/

/-- The longest body kept on the notification itself; the raw event keeps everything fetched. -/
def maxBodyChars : Nat := 20000

def normalize (payload : Json) : Except String NotificationData := do
  let raw ← payload.getObjValAs? String "raw"
  let flags := (payload.getObjValAs? (Array String) "flags").toOption.getD #[]
  let internalDate := (payload.getObjValAs? String "internalDate").toOption
  let truncated := (payload.getObjValAs? Bool "truncated").toOption.getD false
  let m := Mail.parseMessage raw
  -- INTERNALDATE is `17-Jul-1996 02:44:25 -0700`; `parseDate` reads it once the dashes go.
  let sentAt := m.date.orElse fun _ => internalDate.bind fun d => Mail.parseDate (d.replace "-" " " |>.replace "  " " -")
  return {
    kind := "mail"
    threadKey := m.threadKey
    author := Mail.displayName m.from
    title := if m.subject.isEmpty then "(no subject)" else m.subject
    body := truncate m.text maxBodyChars
    url := none
    sentAt
    read := flags.contains "\\Seen"
    -- The parser marks the part a cut would fall in; whether there was a cut is known here.
    attachments := m.attachments.map fun a => { a with «partial» := truncated && a.partial } }

/-- The dedupe key: the `Message-ID` where there is one, else the message's position. -/
def externalId (folder : String) (uidValidity : Nat) (f : Fetched) : String :=
  let raw := f.body.getD ""
  match Mail.messageIdOf raw with
  | some id => s!"mid:{id}"
  | none => s!"uid:{folder}/{uidValidity}/{f.uid.getD f.seq}"

def toRawEvent (folder : String) (uidValidity maxBytes : Nat) (f : Fetched) : RawEvent :=
  let raw := f.body.getD ""
  { externalId := externalId folder uidValidity f
    payload := Json.mkObj [
      ("folder", folder), ("uid", toJson f.uid), ("uidValidity", uidValidity),
      ("flags", toJson f.flags), ("internalDate", toJson f.internalDate),
      ("truncated", decide (raw.length ≥ maxBytes)), ("raw", raw)] }

/-! ## Sync -/

/-- At most this many messages are fetched by one command... -/
def batchMessages : Nat := 100

/-- ...and about this many bytes of them: a batch is held in memory while it is parsed,
    encrypted and stored, which takes a few times its size. A message larger than this is a batch
    of its own. -/
def batchBytes : Nat := 32 * 1024 * 1024

/-- Split messages, as `(uid, size)` in UID order, into batches of at most `count` messages and
    `bytes` bytes, counting each message at most `maxBytes`, which is what is fetched of it. -/
def planBatches (msgs : Array (Nat × Nat)) (count bytes maxBytes : Nat) : Array (Array Nat) :=
  Id.run do
    let mut out := #[]
    let mut cur := #[]
    let mut size := 0
    for (uid, s) in msgs do
      let s := min s maxBytes
      if !cur.isEmpty && (cur.size ≥ count || size + s > bytes) then
        out := out.push cur
        cur := #[]
        size := 0
      cur := cur.push uid
      size := size + s
    if !cur.isEmpty then out := out.push cur
    return out

/-- A UID set, with runs of consecutive UIDs written as ranges: `3:5,9`. -/
def uidSet (uids : Array Nat) : String :=
  let runs := uids.foldl (fun (acc : Array (Nat × Nat)) u =>
    match acc.back? with
    | some (a, b) => if u == b + 1 then acc.pop.push (a, u) else acc.push (u, u)
    | none => #[(u, u)]) #[]
  ",".intercalate (runs.toList.map fun (a, b) => if a == b then toString a else s!"{a}:{b}")

/-- Fetch everything above the cursor and ingest it, in batches (see `batchBytes`), the cursor
    moving past each batch once it is stored. So a first sync of thousands of messages takes a
    bounded amount of memory, and one interrupted halfway -- the connection dropped, the server
    restarted -- carries on where it stopped. Returns the number of new events. -/
def syncFolder (ctx : ConnectorCtx) (s : Settings) (c : Conn) (folder : String) : IO Nat := do
  let mb ← c.examine folder
  let cursor ← ctx.getCursor folder
  let known := cursor.bind fun j => do
    let v ← (j.getObjValAs? Nat "uidValidity").toOption
    let u ← (j.getObjValAs? Nat "lastUid").toOption
    if v == mb.uidValidity then some u else none
  let listed ← match known with
    | some lastUid =>
      -- `n:*` always includes the highest UID, even when it is below `n`; drop what we have.
      let fs ← if mb.exists_ == 0 then pure #[] else c.fetchSizes s!"{lastUid + 1}:*" true
      pure (fs.filter fun f => f.uid.getD 0 > lastUid)
    | none =>
      if cursor.isSome then ctx.log s!"{folder}: UIDVALIDITY changed, resynchronising"
      if mb.exists_ == 0 || s.initialSync == 0 then pure #[]
      else
        let start := if mb.exists_ > s.initialSync then mb.exists_ - s.initialSync + 1 else 1
        c.fetchSizes s!"{start}:*" false
  let msgs := (listed.filterMap fun f => f.uid.map (·, f.size.getD s.maxBytes)).qsort (·.1 < ·.1)
  let batches := planBatches msgs batchMessages batchBytes s.maxBytes
  let cursorAt (lastUid : Nat) :=
    ctx.setCursor folder (Json.mkObj [("uidValidity", mb.uidValidity), ("lastUid", lastUid)])
  if batches.isEmpty && known.isNone then cursorAt 0
  let mut fresh := 0
  let mut done := 0
  for batch in batches do
    if ← ctx.stopping then break
    let fetched ← c.fetch (uidSet batch) true s.maxBytes
    fresh := fresh + (← ctx.ingest (fetched.map (toRawEvent folder mb.uidValidity s.maxBytes)))
    -- Past the whole batch, a message expunged meanwhile included; and only once the batch is
    -- committed, so a crash in between re-fetches it, which the dedupe absorbs.
    cursorAt batch.back!
    done := done + batch.size
    if batches.size > 1 then
      ctx.log s!"{folder}: {done} of {msgs.size} fetched"
      ctx.health "ok" (some s!"{folder}: syncing, {done} of {msgs.size}")
  return fresh

/-- Arrange for `IDLE` to end after `minutes`, and for the connection to be killed if the server
    does not complete it within a minute after that. Cancelled by bumping `generation`. -/
def idleWatchdog (ctx : ConnectorCtx) (c : Conn) (generation : IO.Ref Nat) (minutes : Nat) :
    IO Unit := do
  let g ← generation.get
  let current : IO Bool := return (← generation.get) == g
  discard <| IO.asTask (prio := .dedicated) do
    let mut waited := 0
    while waited < minutes * 60 do
      if !(← current) then return
      if ← ctx.stopping then break
      IO.sleep 1000
      waited := waited + 1
    if !(← current) then return
    c.sendDone
    for _ in [0:60] do
      if !(← current) then return
      IO.sleep 1000
    if ← current then
      ctx.log "server did not complete IDLE, dropping the connection"
      c.close

/-- One connection's lifetime: connect, then sync and wait for changes until something fails. -/
partial def session (ctx : ConnectorCtx) (s : Settings) (folder : String) : IO Unit := do
  ctx.health "connecting" (some folder)
  let c ← Conn.open s.transport
  try
    c.login (← s.credentials)
    let canIdle ← c.hasCap "IDLE"
    let generation ← IO.mkRef 0
    let rec loop : IO Unit := do
      if ← ctx.stopping then return
      let n ← syncFolder ctx s c folder
      if n > 0 then ctx.log s!"{folder}: {n} new"
      if canIdle then
        ctx.health "ok" (some s!"{folder}: idle")
        idleWatchdog ctx c generation s.idleMinutes
        discard c.idle
        generation.modify (· + 1)
      else
        ctx.health "ok" (some s!"{folder}: polling every {s.pollSeconds}s (no IDLE)")
        if !(← ctx.sleep s.pollSeconds) then return
      loop
    loop
    c.logout
  catch e =>
    c.close
    throw e

def run (ctx : ConnectorCtx) : IO Unit := do
  let s ← Settings.load ctx.name ctx.dbPath ctx.source.settings
  let workers ← s.folders.mapM fun folder => do
    let wctx ← ctx.fork
    IO.asTask (prio := .dedicated) (wctx.supervise (session wctx s folder))
  for w in workers do
    match ← IO.wait w with
    | .ok _ => pure ()
    | .error e => ctx.log s!"worker ended: {e}"

end Angelia.Connector.ImapSource