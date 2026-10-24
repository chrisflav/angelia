import Angelia

open Angelia Angelia.Server Std.Async

def usage : String := "usage: angelia [serve | replay [--source NAME] | hash-password
              | change-password | reset-second-factors] [--config PATH]

  serve             run the server; the sources start at the first sign-in (default)
  replay            re-derive notifications from the stored raw events; reads the password
                    on stdin
  hash-password     read a password on stdin, print the passwordHash for the config
  change-password   read the old and the new password on stdin (one per line), re-encrypt the
                    database key under the new one, print the new passwordHash
  reset-second-factors
                    read the password on stdin and remove every security key and
                    authenticator app, for when all of them are lost"

def flag (args : List String) (name : String) : Option String :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => some v
  | _ => none

def loadConfig (args : List String) : IO Config := do
  let path := (flag args "--config").getD "config.json"
  try Config.load path catch e =>
    IO.eprintln s!"configuration error: {e}"
    IO.Process.exit 1

def readLine : IO String := do
  return ((← (← IO.getStdin).getLine).dropEndWhile (· == '\n')).toString

/-- Unlock from a password on stdin, as the CLI commands that touch content do. -/
def unlockFromStdin (config : Config) (db : Db.Conn) : IO Unit := do
  let password ← readLine
  let some stored := config.passwordHash | throw (IO.userError "no passwordHash configured")
  if !(← IO.ofExcept (Vault.PasswordHash.parse stored)).verify password then
    throw (IO.userError "wrong password")
  Db.unlock db password

def startSources (config : Config) : IO Unit := do
  let stop ← IO.mkRef false
  for source in config.sources do
    if !source.enabled then continue
    let some kind := Connector.kind? source.kind
      | log "main" s!"source '{source.name}': unknown kind '{source.kind}', skipped"
    let some run := kind.run | continue
    let cdb ← Db.connect config.dbPath
    let ctx : ConnectorCtx := { source, dbPath := config.dbPath, db := cdb
                                normalize := kind.normalize, stop }
    ctx.health "starting"
    discard <| IO.asTask (prio := .dedicated) do
      try run ctx catch e => ctx.log s!"stopped: {e}"
    log "main" s!"source '{source.name}' ({source.kind}) started"

def serve (config : Config) : IO Unit := do
  let db ← Db.connect config.dbPath
  Db.migrate db
  if config.passwordHash.isNone then
    log "main" "no passwordHash configured: the API will refuse every login"
  let ctx : AppContext := { config, db := ← Std.Mutex.new db, onUnlock := startSources config
                            loginLock := ← Std.Mutex.new (), pending := ← IO.mkRef #[] }
  log "main" s!"listening on http://{config.host}:{config.port}; locked until the first sign-in"
  Async.block do
    let server ← Server.serve ctx
    server.waitShutdown

def main (args : List String) : IO UInt32 := do
  match args.filter (!·.startsWith "-") |>.filter (fun a => flag args "--config" != some a
      && flag args "--source" != some a) with
  | [] | ["serve"] => serve (← loadConfig args); return 0
  | ["replay"] =>
    let config ← loadConfig args
    let db ← Db.connect config.dbPath
    Db.migrate db
    unlockFromStdin config db
    let (n, failed) ← replay db (Connector.normalizerFor config.sources) (flag args "--source")
    IO.println s!"replayed {n} event(s), {failed} failed"
    return (if failed == 0 then 0 else 1)
  | ["hash-password"] =>
    IO.println (← Vault.PasswordHash.create (← readLine)).toString
    return 0
  | ["reset-second-factors"] =>
    let config ← loadConfig args
    let db ← Db.connect config.dbPath
    Db.migrate db
    unlockFromStdin config db
    IO.println s!"removed {← Db.deleteAllFactors db} second factor(s); signing in takes the password alone"
    return 0
  | ["change-password"] =>
    let config ← loadConfig args
    let db ← Db.connect config.dbPath
    Db.migrate db
    let old ← readLine
    let new ← readLine
    if new.isEmpty then throw (IO.userError "the new password is empty")
    let some stored := config.passwordHash | throw (IO.userError "no passwordHash configured")
    if !(← IO.ofExcept (Vault.PasswordHash.parse stored)).verify old then
      throw (IO.userError "wrong password")
    Db.changePassword db old new
    IO.println (← Vault.PasswordHash.create new).toString
    IO.eprintln "set passwordHash in the configuration to the line above, then restart"
    return 0
  | _ => IO.eprintln usage; return 2