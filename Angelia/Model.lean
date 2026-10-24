import Lean.Data.Json

/-!
# Domain model

A notification goes through two shapes. A `RawEvent` is what a source delivered, kept verbatim and
forever; a `Notification` is derived from it by the source kind's `normalize`, and can always be
rebuilt from the raw event (`angelia replay`), so a normalisation bug costs a replay, never data.
-/

open Lean

namespace Angelia

/-- An event as a source delivered it. `externalId` is unique per source and is the dedupe key
    that makes every delivery path idempotent: the same event arriving by push and by backfill is
    stored once. -/
structure RawEvent where
  externalId : String
  payload : Json
deriving Inhabited

/-- The canonical fields every source normalises into. -/
structure NotificationData where
  /-- Kind of item within the source, e.g. `mail`, `PullRequest`, `Issue`. -/
  kind : String := "message"
  /-- The conversation this belongs to, in the source's own terms (mail thread root, GitHub
      thread id, …). Grouping works on this without knowing which source it came from. -/
  threadKey : Option String := none
  author : String := ""
  title : String := ""
  body : String := ""
  url : Option String := none
  /-- When the source says it happened (Unix seconds), if it says. -/
  sentAt : Option Int := none
  /-- Whether the source already considers it read. -/
  read : Bool := false
deriving Inhabited, Repr, ToJson

/-- Every field is optional except `title`, so a pushing program sends only what it has. -/
instance : FromJson NotificationData where
  fromJson? j := do
    let opt {α} [FromJson α] (k : String) (d : α) : Except String α :=
      match j.getObjVal? k with
      | .ok .null | .error _ => pure d
      | .ok v => fromJson? v
    let d : NotificationData := {}
    return {
      kind := ← opt "kind" d.kind, threadKey := ← opt "threadKey" none
      author := ← opt "author" d.author, title := ← j.getObjValAs? String "title"
      body := ← opt "body" d.body, url := ← opt "url" none, sentAt := ← opt "sentAt" none
      read := ← opt "read" d.read }

/-- A stored notification. -/
structure Notification where
  id : Int
  source : String
  externalId : String
  data : NotificationData
  receivedAt : Int
  read : Bool
  archived : Bool
  starred : Bool
  labels : Array Int
  /-- The time it is sorted and shown by: when it was sent, unless that is unknown or claims to
      be later than its arrival (a wrong clock), else when it arrived. -/
  time : Int
deriving Inhabited

instance : ToJson Notification where
  toJson n := Json.mkObj [
    ("id", n.id), ("source", n.source), ("externalId", n.externalId),
    ("kind", n.data.kind), ("threadKey", toJson n.data.threadKey), ("author", n.data.author),
    ("title", n.data.title), ("body", n.data.body), ("url", toJson n.data.url),
    ("sentAt", toJson n.data.sentAt), ("receivedAt", n.receivedAt), ("read", n.read),
    ("archived", n.archived), ("starred", n.starred), ("labels", toJson n.labels),
    ("time", n.time)]

/-- A user-defined label. Labels are how notifications are organised, independently of where they
    came from. -/
structure Label where
  id : Int
  name : String
  color : String
deriving Inhabited, ToJson, FromJson

/-- A saved filter configuration for the frontend's sidebar. `query` is opaque to the backend. -/
structure View where
  id : Int
  name : String
  query : Json
deriving Inhabited, ToJson, FromJson

/-- What an API token may see and do. A notification is visible when it comes from one of
    `sources` *and* carries one of `labels`; `none` means "no restriction". A browser session has
    the full scope.

    Label scopes follow the rules: a token scoped to label "Uni" sees whatever the rules (or the
    user) label "Uni", including notifications labelled later, and stops seeing one whose label is
    removed.

    A scope can also be limited in time, by its notifications' time (when they were sent, or
    when they arrived if that is unknown or earlier): `since` a fixed point, or `within` a
    moving window back from now. With both, the later of the two applies. -/
structure Scope where
  sources : Option (Array String) := none
  labels : Option (Array Int) := none
  /-- Whether the token may change notifications (read/archived/starred, labels in scope). -/
  write : Bool := false
  /-- Only notifications from this time on (Unix seconds). -/
  since : Option Int := none
  /-- Only notifications from the past this many seconds. -/
  within : Option Nat := none
deriving Inhabited, Repr, BEq, ToJson

instance : FromJson Scope where
  fromJson? j := do
    let opt {α} [FromJson α] (k : String) : Except String (Option α) :=
      match j.getObjVal? k with
      | .ok .null | .error _ => pure none
      | .ok v => some <$> fromJson? v
    let within : Option Nat ← opt "within"
    if within == some 0 then throw "'within' must be positive"
    return { sources := ← opt "sources", labels := ← opt "labels"
             write := (← opt "write").getD false, since := ← opt "since", within }

/-- The scope of a logged-in session. -/
def Scope.full : Scope := { write := true }

/-- The scope parameters as SQL arguments: JSON arrays for `json_each`, or `NULL`. -/
def Scope.sqlArgs (s : Scope) : Option String × Option String :=
  (s.sources.map (toJson · |>.compress), s.labels.map (toJson · |>.compress))

/-- The earliest notification time visible at `now`, if the scope is limited in time. -/
def Scope.minTime (s : Scope) (now : Int) : Option Int :=
  match s.since, s.within.map (now - ·) with
  | some a, some b => some (max a b)
  | a, b => a.orElse fun _ => b

/-- Whether a label may be read or changed under this scope. -/
def Scope.allowsLabel (s : Scope) (label : Int) : Bool :=
  s.labels.all (·.contains label)

def Scope.allowsSource (s : Scope) (source : String) : Bool :=
  s.sources.all (·.contains source)

end Angelia