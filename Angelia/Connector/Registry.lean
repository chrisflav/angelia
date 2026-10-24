import Angelia.Connector.Imap
import Angelia.Connector.GitHub

/-!
# Source kinds

Every kind of source is a normaliser plus, for sources angelia fetches from itself, a long-running
worker. Adding a source in Lean is a module and a line here. Adding one *outside* Lean needs no
code at all: a source of kind `ingest` is fed by any program that POSTs to `/api/ingest/<name>`.
-/

open Lean

namespace Angelia.Connector

structure Kind where
  name : String
  normalize : Normalizer
  /-- The worker, for sources angelia fetches from; `none` for push-only kinds. -/
  run : Option (ConnectorCtx → IO Unit)

/-- An `ingest` source's events carry their canonical fields under `notification`, already
    normalised by the program that sent them. -/
def normalizeIngest (payload : Json) : Except String NotificationData := do
  fromJson? (← payload.getObjVal? "notification")

/-- Bumped whenever a normaliser changes what it produces. At start, notifications derived by an
    older version are re-derived from their raw events (see `Angelia.replay`), so a change shows
    on what is already stored, not only on what arrives next. -/
def normalizerVersion : Nat := 2

def kinds : Array Kind := #[
  { name := "imap", normalize := ImapSource.normalize, run := some ImapSource.run },
  { name := "github", normalize := GitHub.normalize, run := some GitHub.run },
  { name := "ingest", normalize := normalizeIngest, run := none }]

def kind? (name : String) : Option Kind := kinds.find? (·.name == name)

/-- The normaliser for a configured source, by source name. -/
def normalizerFor (sources : Array SourceConfig) (source : String) : Option Normalizer := do
  let s ← sources.find? (·.name == source)
  return (← kind? s.kind).normalize

end Angelia.Connector