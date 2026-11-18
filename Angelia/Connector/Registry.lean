import Angelia.Connector.Imap
import Angelia.Connector.GitHub

/-!
# Source kinds

Every kind of source is a normaliser plus, for sources angelia fetches from itself, a long-running
worker, and -- for those that can -- a way to send: a `Draft` in, the raw event of what was sent
out, and the prefilled reply to a notification. The API and the web client send through any of
them alike (`Angelia.Server`); a kind that cannot send (GitHub) leaves those out. Adding a source
in Lean is a module and a line here. Adding one *outside* Lean needs no
code at all: a source of kind `ingest` is fed by any program that POSTs to `/api/ingest/<name>`.
-/

open Lean

namespace Angelia.Connector

/-- Sending a message through a source: given the source and the database, a draft and -- for a
    reply -- the raw payload of what it answers; returns the raw event of what was sent, which is
    stored like anything received, as an outgoing notification. -/
abbrev Sender := SourceConfig → System.FilePath → Draft → Option Json → IO RawEvent

structure Kind where
  name : String
  normalize : Normalizer
  /-- The worker, for sources angelia fetches from; `none` for push-only kinds. -/
  run : Option (ConnectorCtx → IO Unit)
  /-- Whether a source of this kind, as configured, can send. A kind that never can (GitHub's
      notifications have nothing to answer to) leaves the default. -/
  canSend : SourceConfig → Bool := fun _ => false
  send : Sender := fun s _ _ _ => throw (IO.userError s!"source '{s.name}' cannot send")
  /-- The prefilled reply to a notification, from its raw payload (`true`: to everyone it went
      to); `none` where it has none. -/
  replyDraft : SourceConfig → Json → Bool → Option Draft := fun _ _ _ => none

/-- An `ingest` source's events carry their canonical fields under `notification`, already
    normalised by the program that sent them. -/
def normalizeIngest (payload : Json) : Except String NotificationData := do
  fromJson? (← payload.getObjVal? "notification")

/-- Bumped whenever a normaliser changes what it produces. At start, notifications derived by an
    older version are re-derived from their raw events (see `Angelia.replay`), so a change shows
    on what is already stored, not only on what arrives next. -/
def normalizerVersion : Nat := 4

def kinds : Array Kind := #[
  { name := "imap", normalize := ImapSource.normalize, run := some ImapSource.run
    canSend := ImapSource.canSend, send := ImapSource.send, replyDraft := ImapSource.replyDraft },
  { name := "github", normalize := GitHub.normalize, run := some GitHub.run },
  { name := "ingest", normalize := normalizeIngest, run := none }]

def kind? (name : String) : Option Kind := kinds.find? (·.name == name)

/-- The normaliser for a configured source, by source name. -/
def normalizerFor (sources : Array SourceConfig) (source : String) : Option Normalizer := do
  let s ← sources.find? (·.name == source)
  return (← kind? s.kind).normalize

end Angelia.Connector