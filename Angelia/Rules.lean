import Angelia.Model

/-!
# Rules

A rule is a declarative predicate over a notification's canonical fields plus what to do on a
match. Rules are data (stored as JSON), evaluated purely here, and re-runnable over history, so
editing a rule reorganises past notifications as well as future ones.

```json
{ "match": "all",
  "conditions": [{"field": "source", "op": "equals", "value": "github"},
                 {"field": "title", "op": "contains", "value": "CI"}],
  "labels": [3], "archive": false, "markRead": true }
```
-/

open Lean

namespace Angelia

/-- A field a condition can test. -/
inductive Field where
  | source | kind | author | title | body | thread | url
deriving Repr, BEq, Inhabited

def Field.ofString? : String → Option Field
  | "source" => some .source | "kind" => some .kind | "author" => some .author
  | "title" => some .title | "body" => some .body | "thread" => some .thread | "url" => some .url
  | _ => none

def Field.toString : Field → String
  | .source => "source" | .kind => "kind" | .author => "author" | .title => "title"
  | .body => "body" | .thread => "thread" | .url => "url"

instance : ToJson Field := ⟨fun f => f.toString⟩
instance : FromJson Field where
  fromJson? j := do
    let s ← j.getStr?
    (Field.ofString? s).elim (.error s!"unknown rule field '{s}'") .ok

/-- A string comparison. All of them ignore case: rules are written by hand against text that
    senders capitalise however they like. -/
inductive Op where
  | equals | contains | startsWith | endsWith
deriving Repr, BEq, Inhabited

instance : ToJson Op := ⟨fun
  | .equals => "equals" | .contains => "contains"
  | .startsWith => "startsWith" | .endsWith => "endsWith"⟩
instance : FromJson Op where
  fromJson? j := do
    match ← j.getStr? with
    | "equals" => pure .equals | "contains" => pure .contains
    | "startsWith" => pure .startsWith | "endsWith" => pure .endsWith
    | s => .error s!"unknown rule operator '{s}'"

structure Condition where
  field : Field
  op : Op
  value : String
  /-- Invert the test. -/
  negate : Bool := false
deriving Repr, Inhabited, ToJson

/-- Look up an optional field, falling back to `d` when it is absent or null. -/
private def optField {α} [FromJson α] (j : Json) (k : String) (d : α) : Except String α :=
  match j.getObjVal? k with
  | .ok .null | .error _ => pure d
  | .ok v => fromJson? v

instance : FromJson Condition where
  fromJson? j := do
    return { field := ← j.getObjValAs? Field "field", op := ← j.getObjValAs? Op "op"
             value := ← j.getObjValAs? String "value", negate := ← optField j "negate" false }

/-- The part of a rule that is stored as JSON. -/
structure RuleSpec where
  /-- `all` (every condition) or `any` (at least one). -/
  «match» : String := "all"
  conditions : Array Condition := #[]
  labels : Array Int := #[]
  archive : Bool := false
  markRead : Bool := false
deriving Repr, Inhabited, ToJson

instance : FromJson RuleSpec where
  fromJson? j := do
    let d : RuleSpec := {}
    return { «match» := ← optField j "match" d.match, conditions := ← optField j "conditions" #[]
             labels := ← optField j "labels" #[], archive := ← optField j "archive" false
             markRead := ← optField j "markRead" false }

structure Rule where
  id : Int
  name : String
  enabled : Bool
  position : Int
  spec : RuleSpec
deriving Inhabited

instance : ToJson Rule where
  toJson r := Json.mkObj [("id", r.id), ("name", r.name), ("enabled", r.enabled),
    ("position", r.position), ("spec", toJson r.spec)]

def fieldValue (source : String) (n : NotificationData) : Field → String
  | .source => source
  | .kind => n.kind
  | .author => n.author
  | .title => n.title
  | .body => n.body
  | .thread => n.threadKey.getD ""
  | .url => n.url.getD ""

def Condition.holds (c : Condition) (source : String) (n : NotificationData) : Bool :=
  let v := (fieldValue source n c.field).toLower
  let w := c.value.toLower
  let r := match c.op with
    | .equals => v == w
    | .contains => (v.splitOn w).length > 1 || w.isEmpty
    | .startsWith => v.startsWith w
    | .endsWith => v.endsWith w
  r != c.negate

/-- Whether a rule matches. A rule without conditions matches nothing, so that a half-written
    rule cannot label everything. -/
def RuleSpec.matches (r : RuleSpec) (source : String) (n : NotificationData) : Bool :=
  if r.conditions.isEmpty then false
  else if r.match == "any" then r.conditions.any (·.holds source n)
  else r.conditions.all (·.holds source n)

/-- The combined effect of a rule set on one notification. -/
structure Outcome where
  labels : Array (Int × Int) := #[]
  archive : Bool := false
  markRead : Bool := false
deriving Repr, Inhabited, BEq

/-- Evaluate enabled rules in order. Returns `(rule id, label id)` pairs so a later re-run can
    tell rule-assigned labels from ones the user set by hand. -/
def evaluate (rules : Array Rule) (source : String) (n : NotificationData) : Outcome :=
  rules.foldl (fun acc r =>
    if r.enabled && r.spec.matches source n then
      { labels := acc.labels ++ r.spec.labels.map (r.id, ·)
        archive := acc.archive || r.spec.archive
        markRead := acc.markRead || r.spec.markRead }
    else acc) {}

end Angelia