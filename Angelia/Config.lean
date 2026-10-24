import Lean.Data.Json

/-!
# Configuration

Read from a JSON file (`--config`, default `config.json`). Sources are listed there, each with a
unique `name` (what notifications record as their source, and what cursors are keyed by) and a
`kind` selecting the connector. The kind-specific settings stay as raw JSON and are decoded by the
connector itself, so adding a kind never touches this module.

Secrets may be given inline or as a command whose output is the secret (`passwordCommand`,
`tokenCommand`, e.g. `["pass", "show", "mail/imap"]`), so the file need not hold them.
-/

open Lean

namespace Angelia

structure SourceConfig where
  name : String
  kind : String
  enabled : Bool := true
  /-- The whole JSON object, for the connector to decode. -/
  settings : Json
deriving Inhabited

instance : FromJson SourceConfig where
  fromJson? j := do
    let name ← j.getObjValAs? String "name"
    let kind ← j.getObjValAs? String "kind"
    let enabled := (j.getObjValAs? Bool "enabled").toOption.getD true
    return { name, kind, enabled, settings := j }

structure Config where
  host : String := "127.0.0.1"
  port : UInt16 := 8090
  dbPath : System.FilePath := "angelia.sqlite"
  staticDir : System.FilePath := "static"
  /-- Salted PBKDF2 hash of the login password, from `angelia hash-password`. Without it the API is
      refused entirely and the server never unlocks. -/
  passwordHash : Option String := none
  /-- Mark the session cookie `Secure`; set this whenever the server is behind HTTPS. -/
  secureCookies : Bool := false
  /-- Session lifetime, in days since last use. -/
  sessionDays : Nat := 30
  sources : Array SourceConfig := #[]
deriving Inhabited

instance : FromJson Config where
  fromJson? j := do
    if (j.getObjVal? "passwordSha256").isOk then
      throw "passwordSha256 is no longer supported; set passwordHash to the output of \
        `angelia hash-password`"
    let d : Config := {}
    let opt {α} [FromJson α] (k : String) (dflt : α) : Except String α :=
      match j.getObjVal? k with
      | .ok v => fromJson? v
      | .error _ => pure dflt
    return {
      host := ← opt "host" d.host
      port := (← opt "port" d.port.toNat).toUInt16
      dbPath := (← opt "dbPath" d.dbPath.toString : String)
      staticDir := (← opt "staticDir" d.staticDir.toString : String)
      passwordHash := ← opt "passwordHash" none
      secureCookies := ← opt "secureCookies" d.secureCookies
      sessionDays := ← opt "sessionDays" d.sessionDays
      sources := ← opt "sources" #[] }

def Config.load (path : System.FilePath) : IO Config := do
  let text ← IO.FS.readFile path
  match Json.parse text >>= fromJson? with
  | .ok c =>
    let names := c.sources.map (·.name)
    for n in names do
      if (names.filter (· == n)).size > 1 then
        throw (IO.userError s!"source name '{n}' is used more than once")
    return c
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- Resolve a secret given either inline under `key` or as a command under `key ++ "Command"`. -/
def secret (settings : Json) (key : String) : IO (Option String) := do
  if let .ok v := settings.getObjValAs? String key then return some v
  match settings.getObjValAs? (Array String) (key ++ "Command") with
  | .ok argv =>
    match argv.toList with
    | [] => return none
    | cmd :: args =>
      let out ← IO.Process.output { cmd, args := args.toArray }
      if out.exitCode != 0 then
        throw (IO.userError s!"{key}Command failed ({out.exitCode}): {out.stderr.trimAscii}")
      -- `pass` and friends print the secret on the first line.
      return some ((out.stdout.splitOn "\n").headD "").trimAscii.toString
  | .error _ => return none

end Angelia