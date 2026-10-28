import Std.Http
import Std.Sync.Mutex
import Angelia.Connector.Registry
import Angelia.Crypto
import Angelia.SecondFactor

/-!
# HTTP server

The read/write API for the frontend, a server-sent-events stream for live updates, the ingest
endpoint for out-of-process sources, and the static frontend — all on `Std.Http`'s HTTP/1.1
server. TLS is left to a reverse proxy in front.

Authentication is a single password (stored as a salted PBKDF2 hash in the configuration)
exchanged for an opaque session token in an `HttpOnly` cookie, or — for clients other than the
browser — an API token sent as `Authorization: Bearer agl_…`. A token carries a `Scope`: the
sources and labels it may see, and whether it may change anything. The scope is applied inside
the database queries, so nothing outside it is ever read on a token's behalf. Labels, rules, views and tokens
themselves are managed from a logged-in session only, so a leaked token cannot widen itself or
mint more tokens. Only hashes of sessions and tokens are stored.
`/api/ingest/<source>` is authenticated separately, by that source's own bearer token, since the
programs posting to it are not clients of the inbox.

When second factors are registered, a sign-in takes the password and then a tap on a security
key or a code from an authenticator app (see `Angelia.SecondFactor`); registering or removing
one takes the password again, so a stolen session cookie cannot swap in its own.

With an unlock key configured the server unlocks itself at start (see `Angelia.Vault`).
Otherwise, or until the first sign-in with an existing database takes the key up, it is locked:
the first sign-in unwraps the database key and starts the sources, and everything else answers
503 meanwhile.
-/

open Std.Http Std.Http.Server Std.Async Std.Net Lean

namespace Angelia.Server

/-- A challenge waiting for its answer, under a key saying what it is for. -/
structure Pending where
  key : String
  value : String
  expires : Int
  attempts : Nat := 0

structure AppContext where
  config : Config
  db : Std.Mutex Db.Conn
  /-- Starts the sources; run once, by the sign-in that unlocks the server. -/
  onUnlock : IO Unit
  /-- The configured unlock key, which a sign-in wraps the database key under. -/
  unlockKey : Option ByteArray := none
  /-- Held while a password is checked, so attempts are made one at a time. -/
  loginLock : Std.Mutex Unit
  /-- Challenges in flight: a sign-in waiting for its second factor, or a factor being
      registered. Kept in memory only; a restart simply makes them start over. -/
  pending : IO.Ref (Array Pending)

def AppContext.withDb (ctx : AppContext) (act : Db.Conn → IO α) : IO α :=
  ctx.db.atomically do act (← get)

/-! ## Requests and responses -/

structure Req where
  method : Method
  segments : List String
  query : String → Option String
  body : String
  header : String → Option String

def Req.cookie (r : Req) (name : String) : Option String := do
  let raw ← r.header "cookie"
  (raw.splitOn ";").findSome? fun pair =>
    match pair.trimAscii.toString.splitOn "=" with
    | [k, v] => if k == name then some v else none
    | _ => none

def Req.bearer (r : Req) : Option String := do
  let h ← r.header "authorization"
  if h.startsWith "Bearer " then some (h.drop 7).toString else none

structure ApiResponse where
  status : Status := .ok
  body : Json := Json.mkObj []
  headers : Array (String × String) := #[]
  /-- Sent instead of `body`, for the one endpoint that answers with a file. -/
  bytes : Option ByteArray := none

inductive ApiError where
  | badRequest (msg : String)
  | unauthorized (msg : String)
  | forbidden (msg : String)
  | notFound (msg : String)
  | server (msg : String)
  | locked

def ApiError.toResponse : ApiError → ApiResponse
  | .badRequest m => { status := .badRequest, body := Json.mkObj [("error", m)] }
  | .unauthorized m => { status := .unauthorized, body := Json.mkObj [("error", m)] }
  | .forbidden m => { status := .forbidden, body := Json.mkObj [("error", m)] }
  | .notFound m => { status := .notFound, body := Json.mkObj [("error", m)] }
  | .server m => { status := .internalServerError, body := Json.mkObj [("error", m)] }
  | .locked => { status := .serviceUnavailable
                 body := Json.mkObj [("error", "angelia was restarted: sign in to unlock it"),
                   ("locked", true)] }

abbrev ApiM := ExceptT ApiError IO

def fail (e : ApiError) : ApiM α := throwThe ApiError e

def ok (j : Json) : ApiM ApiResponse := pure { body := j }

def liftIO (act : IO α) : ApiM α := ExceptT.lift act

def AppContext.dbM (ctx : AppContext) (act : Db.Conn → IO α) : ApiM α := liftIO (ctx.withDb act)

def parseJson (body : String) : ApiM Json :=
  match Json.parse body with
  | .ok j => pure j
  | .error e => fail (.badRequest s!"invalid JSON: {e}")

def field? {α} [FromJson α] (j : Json) (k : String) : ApiM (Option α) :=
  match j.getObjVal? k with
  | .error _ => pure none
  | .ok .null => pure none
  | .ok v => match fromJson? v with
    | .ok a => pure (some a)
    | .error e => fail (.badRequest s!"'{k}': {e}")

def field {α} [FromJson α] (j : Json) (k : String) : ApiM α := do
  match ← field? j k with
  | some a => pure a
  | none => fail (.badRequest s!"'{k}' is required")

def parseId (s : String) : ApiM Int :=
  match s.toInt? with
  | some n => pure n
  | none => fail (.badRequest s!"invalid id: {s}")

/-! ## Authentication -/

def sessionCookie : String := "angelia_session"

/-- API tokens carry a recognisable prefix, so a leaked one can be found by secret scanners. -/
def tokenPrefix : String := "agl_"

/-- Who a request is from. -/
inductive Principal where
  | session
  | token (id : Int) (scope : Scope)

def Principal.scope : Principal → Scope
  | .session => Scope.full
  | .token _ s => s

def Principal.toJson : Principal → Json
  | .session => Json.mkObj [("authenticated", true), ("via", "session"), ("scope", Lean.toJson Scope.full)]
  | .token id s => Json.mkObj [("authenticated", true), ("via", "token"), ("tokenId", id),
      ("scope", Lean.toJson s)]

/-- Authenticate by API token if the request carries one, else by session cookie. A request with
    a bad token is refused even if it also has a valid cookie, so a client is never silently
    acting under a different identity than it presented. -/
def AppContext.authenticate (ctx : AppContext) (r : Req) : IO (Option Principal) := do
  if let some token := r.bearer then
    if !token.startsWith tokenPrefix then return none
    return (← ctx.withDb (Db.checkToken · (Crypto.sha256Hex token))).map fun (id, s) => .token id s
  let some token := r.cookie sessionCookie | return none
  if ← ctx.withDb (Db.checkSession · (Crypto.sha256Hex token) (ctx.config.sessionDays * 86400)) then
    return some .session
  return none

def cookieAttrs (ctx : AppContext) : String :=
  "; Path=/; HttpOnly; SameSite=Strict" ++ (if ctx.config.secureCookies then "; Secure" else "")

def AppContext.rp (ctx : AppContext) : SecondFactor.RelyingParty :=
  .ofOrigin ctx.config.publicOrigin

/-- How long a challenge stays answerable, in seconds. -/
def pendingSeconds : Int := 300

/-- How many answers one sign-in challenge takes before it is spent; with a six-digit code and a
    password needed for every new challenge, guessing a code is hopeless. -/
def pendingAttempts : Nat := 5

def AppContext.putPending (ctx : AppContext) (key value : String) : IO Unit := do
  let now ← nowSeconds
  ctx.pending.modify fun ps =>
    (ps.filter fun p => p.key != key && p.expires > now).push
      { key, value, expires := now + pendingSeconds }

/-- The challenge under `key`, counting this as one attempt at answering it. -/
def AppContext.attemptPending (ctx : AppContext) (key : String) : IO (Option Pending) := do
  let now ← nowSeconds
  ctx.pending.modifyGet fun ps =>
    let ps := ps.filter (·.expires > now)
    match ps.find? (·.key == key) with
    | none => (none, ps)
    | some p =>
      let others := ps.filter (·.key != key)
      if p.attempts + 1 ≥ pendingAttempts then (some p, others)
      else (some p, others.push { p with attempts := p.attempts + 1 })

def AppContext.dropPending (ctx : AppContext) (key : String) : IO Unit :=
  ctx.pending.modify (·.filter (·.key != key))

/-- Check the password, one attempt at a time; a wrong one holds the lock a second longer, so
    guessing runs at about one try per second however many connections it uses. -/
def checkPassword (ctx : AppContext) (password : String) : ApiM Unit := do
  let some stored := ctx.config.passwordHash
    | fail (.unauthorized "no password configured (set passwordHash)")
  let hash ← match Vault.PasswordHash.parse stored with
    | .ok h => pure h
    | .error e => fail (.server e)
  let correct ← liftIO <| ctx.loginLock.atomically do
    if hash.verify password then return true
    IO.sleep 1000
    return false
  if !correct then fail (.unauthorized "wrong password")

def startSession (ctx : AppContext) : ApiM ApiResponse := do
  let token ← liftIO (randomToken 32)
  ctx.dbM fun db => Db.createSession db (Crypto.sha256Hex token)
  pure { body := Json.mkObj [("ok", true)]
         headers := #[("Set-Cookie", s!"{sessionCookie}={token}{cookieAttrs ctx}; Max-Age={ctx.config.sessionDays * 86400}")] }

/-- A fresh WebAuthn challenge, base64url. -/
def newChallenge : IO String := return SecondFactor.base64url (← IO.getRandomBytes 32)

/-- Check the password and, on the first sign-in after a start, unlock the server with it. With
    second factors registered, the answer is a challenge for one of them instead of a session. -/
def login (ctx : AppContext) (r : Req) : ApiM ApiResponse := do
  let password : String ← field (← parseJson r.body) "password"
  checkPassword ctx password
  liftIO <| ctx.loginLock.atomically do
    if !(← Vault.unlocked) then
      ctx.withDb (Db.unlock · password ctx.unlockKey)
      log "main" (if ctx.unlockKey.isSome then "unlocked; from now on at start, by the unlock key"
        else "unlocked")
      ctx.onUnlock
    else
      ctx.withDb (Db.ensurePasswordWrap · password)
  let keys ← ctx.dbM Db.webauthnCredentials
  let apps ← ctx.dbM Db.totpSecrets
  if keys.isEmpty && apps.isEmpty then return ← startSession ctx
  let id ← liftIO (randomToken 16)
  let challenge ← liftIO newChallenge
  liftIO (ctx.putPending s!"login:{id}" challenge)
  ok (Json.mkObj [("secondFactor", Json.mkObj [
    ("pending", id),
    ("webauthn", if keys.isEmpty then Json.null else Json.mkObj [
      ("challenge", challenge), ("rpId", ctx.rp.id),
      ("allowCredentials", toJson (keys.map (·.2.id)))]),
    ("totp", !apps.isEmpty)])])

def bytesField (j : Json) (k : String) : ApiM ByteArray := do
  let some b := SecondFactor.unbase64url (← field j k)
    | fail (.badRequest s!"'{k}' is not base64url")
  pure b

/-- `POST /api/login/second-factor`: answer the sign-in's challenge, with `{"pending", "code"}`
    from an app or `{"pending", "credentialId", "clientDataJSON", "authenticatorData",
    "signature"}` from a security key. -/
def loginSecondFactor (ctx : AppContext) (r : Req) : ApiM ApiResponse := do
  let j ← parseJson r.body
  let id : String ← field j "pending"
  let key := s!"login:{id}"
  let some p ← liftIO (ctx.attemptPending key)
    | fail (.unauthorized "the sign-in expired; enter the password again")
  match (← field? j "code" : Option String) with
  | some code =>
    let now := (← liftIO nowSeconds).toNat
    let apps ← ctx.dbM Db.totpSecrets
    let some (factor, step) := apps.findSome? fun (fid, secret, last) =>
        (SecondFactor.totpMatch secret now last code).map (fid, ·)
      | fail (.unauthorized "wrong code")
    ctx.dbM (Db.factorUsed · factor none (some step))
  | none =>
    let credId : String ← field j "credentialId"
    let keys ← ctx.dbM Db.webauthnCredentials
    let some (factor, cred) := keys.find? (·.2.id == credId)
      | fail (.unauthorized "this security key is not registered")
    match SecondFactor.verifyAssertion ctx.rp p.value cred (← bytesField j "clientDataJSON")
        (← bytesField j "authenticatorData") (← bytesField j "signature") with
    | .ok count => ctx.dbM (Db.factorUsed · factor (some count) none)
    | .error e => fail (.unauthorized e)
  liftIO (ctx.dropPending key)
  startSession ctx

/-! ## Managing second factors

From a logged-in session only, and each change takes the password again. -/

def sessionKey (r : Req) : String := Crypto.sha256Hex ((r.cookie sessionCookie).getD "")

def webauthnChallenge (ctx : AppContext) (r : Req) : ApiM ApiResponse := do
  let challenge ← liftIO newChallenge
  liftIO (ctx.putPending s!"webauthn:{sessionKey r}" challenge)
  let keys ← ctx.dbM Db.webauthnCredentials
  ok (Json.mkObj [("challenge", challenge),
    ("rp", Json.mkObj [("id", ctx.rp.id), ("name", "angelia")]),
    -- One account, so one fixed user handle.
    ("user", Json.mkObj [("id", SecondFactor.base64url "angelia owner".toUTF8),
      ("name", "angelia"), ("displayName", "angelia")]),
    ("excludeCredentials", toJson (keys.map (·.2.id)))])

/-- Body: `{"password", "name", "clientDataJSON", "authenticatorData", "publicKey", "alg"}`, the
    last four from the browser's `AuthenticatorAttestationResponse`. -/
def addWebAuthn (ctx : AppContext) (r : Req) : ApiM ApiResponse := do
  let j ← parseJson r.body
  checkPassword ctx (← field j "password")
  let name : String ← field j "name"
  let key := s!"webauthn:{sessionKey r}"
  let some p ← liftIO (ctx.attemptPending key)
    | fail (.badRequest "the challenge expired; try again")
  let cred ← match SecondFactor.verifyRegistration ctx.rp p.value (← bytesField j "clientDataJSON")
      (← bytesField j "authenticatorData") (← bytesField j "publicKey") (← field j "alg") with
    | .ok c => pure c
    | .error e => fail (.badRequest e)
  if (← ctx.dbM Db.webauthnCredentials).any (·.2.id == cred.id) then
    fail (.badRequest "this security key is already registered")
  ctx.dbM (Db.addWebAuthn · name cred)
  liftIO (ctx.dropPending key)
  ok (Json.mkObj [("ok", true)])

def totpSecret (ctx : AppContext) (r : Req) : ApiM ApiResponse := do
  let secret ← liftIO (IO.getRandomBytes 20)
  liftIO (ctx.putPending s!"totp:{sessionKey r}" (Crypto.toHex secret))
  ok (Json.mkObj [("secret", SecondFactor.base32 secret),
    ("uri", SecondFactor.totpUri "angelia" ctx.rp.id secret)])

/-- Body: `{"password", "name", "code"}`; the code proves the app has the secret. -/
def addTotp (ctx : AppContext) (r : Req) : ApiM ApiResponse := do
  let j ← parseJson r.body
  checkPassword ctx (← field j "password")
  let name : String ← field j "name"
  let key := s!"totp:{sessionKey r}"
  let some p ← liftIO (ctx.attemptPending key) | fail (.badRequest "the setup expired; start again")
  let secret := Crypto.unhex p.value
  let now := (← liftIO nowSeconds).toNat
  let some _ := SecondFactor.totpMatch secret now 0 (← field j "code")
    | fail (.badRequest "wrong code; check that the phone's clock is right")
  ctx.dbM (Db.addTotp · name secret)
  liftIO (ctx.dropPending key)
  ok (Json.mkObj [("ok", true)])

def deleteFactor (ctx : AppContext) (r : Req) (id : Int) : ApiM ApiResponse := do
  checkPassword ctx (← field (← parseJson r.body) "password")
  if ← ctx.dbM (Db.deleteFactor · id) then ok (Json.mkObj [("ok", true)])
  else fail (.notFound "no such second factor")

def logout (ctx : AppContext) (r : Req) : ApiM ApiResponse := do
  if let some token := r.cookie sessionCookie then
    ctx.dbM fun db => Db.deleteSession db (Crypto.sha256Hex token)
  pure { body := Json.mkObj [("ok", true)]
         headers := #[("Set-Cookie", s!"{sessionCookie}={cookieAttrs ctx}; Max-Age=0")] }

/-! ## Handlers -/

def listNotifications (ctx : AppContext) (scope : Scope) (r : Req) : ApiM ApiResponse := do
  let num (k : String) : ApiM (Option Int) := match r.query k with
    | some v => if v.isEmpty then pure none else some <$> parseId v
    | none => pure none
  let nonEmpty (k : String) := (r.query k).filter (!·.isEmpty)
  -- The cursor is `<time>.<id>` of the last item of the previous page.
  let before ← match nonEmpty "before" with
    | none => pure none
    | some c => match c.splitOn "." |>.map String.toInt? with
      | [some t, some id] => pure (some (t, id))
      | _ => fail (.badRequest "invalid 'before' cursor")
  let sort := (nonEmpty "sort").getD "newest"
  if !["newest", "oldest", "arrived"].contains sort then
    fail (.badRequest "'sort' is one of newest, oldest, arrived")
  let f : Db.Filter := {
    q := nonEmpty "q", source := nonEmpty "source", thread := nonEmpty "thread"
    label := ← num "label", before, sort
    state := (nonEmpty "state").getD "inbox"
    limit := ((← num "limit").map Int.toNat).getD 100 }
  let ns ← ctx.dbM (Db.listNotifications · scope f)
  ok (Json.mkObj [("notifications", toJson ns),
    ("next", toJson (if ns.size < f.limit then none
      else ns.back?.map fun n => s!"{n.time}.{n.id}"))])

/-- A notification the scope cannot see is reported as missing, not as forbidden, so a token cannot
    probe which ids exist outside its scope. -/
def visible (ctx : AppContext) (scope : Scope) (id : Int) : ApiM Notification := do
  let some n ← ctx.dbM (Db.getNotification · scope id) | fail (.notFound "no such notification")
  pure n

def getNotification (ctx : AppContext) (scope : Scope) (id : Int) (withRaw : Bool) :
    ApiM ApiResponse := do
  let n ← visible ctx scope id
  let raw ← if withRaw then ctx.dbM (Db.rawPayload · id) else pure none
  ok ((toJson n).setObjVal! "raw" (toJson raw))

/-- A `Content-Disposition` that makes the browser save the file, under its name: an ASCII
    fallback, and the name itself in RFC 5987 form. -/
def downloadDisposition (name : String) : String :=
  let fallback := String.ofList (name.toList.map fun c =>
    if c.toNat ≥ 0x20 && c.toNat < 0x7F && c != '"' && c != '\\' then c else '_')
  let unreserved (b : UInt8) : Bool :=
    let c := Char.ofNat b.toNat
    c.isAlphanum || c == '-' || c == '.' || c == '_' || c == '~'
  let hex := "0123456789ABCDEF".toList.toArray
  let encoded := name.toUTF8.foldl (fun s b =>
    if unreserved b then s.push (Char.ofNat b.toNat)
    else s.push '%' |>.push hex[b.toNat / 16]! |>.push hex[b.toNat % 16]!) ""
  s!"attachment; filename=\"{fallback}\"; filename*=UTF-8''{encoded}"

/-- `GET /api/notifications/<id>/attachments/<n>`: attachment `n` of a mail, extracted from the
    stored message. What a sender put in a mail must never run as this site, so it is always a
    download -- never shown inline -- and its type is passed on only if it is a plain media type,
    with sniffing off and a sandboxing CSP should a browser render it anyway. -/
def getAttachment (ctx : AppContext) (scope : Scope) (id index : Int) : ApiM ApiResponse := do
  discard <| visible ctx scope id
  if index < 0 then fail (.notFound "no such attachment")
  let raw := (← ctx.dbM (Db.rawPayload · id)).bind (·.getObjValAs? String "raw" |>.toOption)
  let some (a, bytes) := raw.bind (Mail.attachmentAt · index.toNat)
    | fail (.notFound "no such attachment")
  let plain := a.mime.toList.all (fun c => c.isAlphanum || "/.+-_".toList.contains c)
    && (a.mime.splitOn "/").length == 2
  pure { bytes := some bytes, headers := #[
    ("Content-Type", if plain then a.mime else "application/octet-stream"),
    ("Content-Disposition", downloadDisposition a.name),
    ("X-Content-Type-Options", "nosniff"),
    ("Content-Security-Policy", "sandbox; default-src 'none'")] }

def patchNotifications (ctx : AppContext) (scope : Scope) (r : Req) : ApiM ApiResponse := do
  let j ← parseJson r.body
  let ids : Array Int ← field j "ids"
  let read ← field? j "read"
  let archived ← field? j "archived"
  let starred ← field? j "starred"
  let changed ← ctx.dbM fun db => Db.setFlags db scope ids read archived starred
  liftIO (bumpChanges (some changed))
  ok (Json.mkObj [("updated", changed.size)])

/-- Attach or detach a label. Under a label scope only the scope's own labels can be touched;
    detaching one may take the notification out of the token's sight, which is allowed. -/
def setLabel (ctx : AppContext) (scope : Scope) (id label : Int) (on : Bool) : ApiM ApiResponse := do
  discard <| visible ctx scope id
  if !scope.allowsLabel label then fail (.forbidden "label outside this token's scope")
  ctx.dbM (Db.setLabel · id label on)
  liftIO (bumpChanges (some #[id]))
  ok (Json.mkObj [("ok", true)])

def createLabel (ctx : AppContext) (r : Req) : ApiM ApiResponse := do
  let j ← parseJson r.body
  let name : String ← field j "name"
  let color := ((← field? j "color") : Option String).getD "#6b7280"
  ok (toJson (← ctx.dbM fun db => Db.createLabel db name color))

def createRule (ctx : AppContext) (r : Req) : ApiM ApiResponse := do
  let j ← parseJson r.body
  let id ← ctx.dbM fun db => do
    Db.createRule db (← IO.ofExcept (j.getObjValAs? String "name"))
      ((j.getObjValAs? Bool "enabled").toOption.getD true)
      ((j.getObjValAs? Int "position").toOption.getD 0)
      (← IO.ofExcept (j.getObjValAs? RuleSpec "spec"))
  ok (Json.mkObj [("id", id)])

def updateRule (ctx : AppContext) (id : Int) (r : Req) : ApiM ApiResponse := do
  let j ← parseJson r.body
  let name ← field? j "name"
  let enabled ← field? j "enabled"
  let position ← field? j "position"
  let spec ← field? j "spec"
  ctx.dbM fun db => Db.updateRule db id name enabled position spec
  ok (Json.mkObj [("ok", true)])

def sources (ctx : AppContext) (scope : Scope) : ApiM ApiResponse := do
  let health ← match ← ctx.dbM Db.listHealth with
    | .arr hs => pure (hs.filter fun h =>
        scope.allowsSource ((h.getObjValAs? String "source").toOption.getD ""))
    | _ => pure #[]
  ok (Json.mkObj [
    ("configured", toJson ((ctx.config.sources.filter (scope.allowsSource ·.name)).map fun s =>
      Json.mkObj [("name", s.name), ("kind", s.kind), ("enabled", s.enabled)])),
    ("health", toJson health)])

/-- `POST /api/tokens` body: `{"name": ..., "scope": {"sources": [...]|null,
    "labels": [...]|null, "write": bool}}`. Unknown sources and labels are refused rather than
    stored, since a typo would otherwise silently produce a token that sees nothing. -/
def createToken (ctx : AppContext) (r : Req) : ApiM ApiResponse := do
  let j ← parseJson r.body
  let name : String ← field j "name"
  if name.trimAscii.isEmpty then fail (.badRequest "a token needs a name")
  let scope : Scope := (← field? j "scope").getD {}
  for src in scope.sources.getD #[] do
    if !ctx.config.sources.any (·.name == src) then fail (.badRequest s!"no source named '{src}'")
  let labels ← ctx.dbM Db.listLabels
  for l in scope.labels.getD #[] do
    if !labels.any (·.id == l) then fail (.badRequest s!"no label with id {l}")
  let token := tokenPrefix ++ (← liftIO (randomToken 32))
  let id ← ctx.dbM (Db.createToken · name (Crypto.sha256Hex token) scope)
  -- The only time the token itself is ever seen.
  ok (Json.mkObj [("id", id), ("name", name), ("token", token), ("scope", toJson scope)])

/-- `POST /api/ingest/<source>` — the extension point for sources implemented outside angelia.
    Body: `{"externalId": "...", "notification": {"title": ..., ...}, ...anything else}`; the
    whole body is stored as the raw event. A batch is a JSON array of such objects. -/
def ingest (ctx : AppContext) (sourceName : String) (r : Req) : ApiM ApiResponse := do
  let some source := ctx.config.sources.find? (·.name == sourceName)
    | fail (.notFound s!"no source named '{sourceName}'")
  let some kind := Connector.kind? source.kind | fail (.server s!"unknown kind '{source.kind}'")
  let some expected ← liftIO (secret source.settings "token")
    | fail (.unauthorized s!"source '{sourceName}' has no ingest token configured")
  -- Compared as digests, so the time taken says nothing about how much of the token matched.
  let digest (t : String) := Crypto.sha256 t.toUTF8
  if (r.bearer.map digest) != some (digest expected) then fail (.unauthorized "invalid ingest token")
  let j ← parseJson r.body
  let items := match j with
    | .arr xs => xs
    | x => #[x]
  let events ← items.mapM fun item => do
    let externalId : String ← field item "externalId"
    -- Reject what would not normalise, rather than storing an event that never shows up.
    match kind.normalize item with
    | .error e => fail (.badRequest s!"{externalId}: {e}")
    | .ok _ => pure ({ externalId, payload := item } : RawEvent)
  let n ← ctx.dbM fun db => do
    let cctx : ConnectorCtx := { source, dbPath := ctx.config.dbPath, db
                                 normalize := kind.normalize, stop := ← IO.mkRef false }
    cctx.health "ok" (some "last push accepted")
    cctx.ingest events
  ok (Json.mkObj [("received", events.size), ("new", n)])

/-- The first path segments of the routes only a logged-in session may use. -/
def sessionOnly : List String := ["second-factors", "tokens", "labels", "rules", "views"]

def dispatch (ctx : AppContext) (r : Req) : ApiM ApiResponse := do
  match r.method, r.segments with
  | .post, ["login"] => login ctx r
  | .post, ["logout"] => logout ctx r
  | .post, ["login", "second-factor"] => loginSecondFactor ctx r
  | _, _ =>
  if !(← liftIO Vault.unlocked) then fail .locked
  match r.method, r.segments with
  | .post, ["ingest", source] => ingest ctx source r
  | _, _ =>
  let some principal ← liftIO (ctx.authenticate r) | fail (.unauthorized "not logged in")
  let scope := principal.scope
  -- Everything that shapes the whole inbox (labels, rules, views, tokens) is the owner's, i.e. a
  -- logged-in session's. Tokens read and triage notifications within their scope, nothing else.
  let requireSession : ApiM Unit := match principal with
    | .session => pure ()
    | .token .. => fail (.forbidden "only a logged-in session may do this")
  let requireWrite : ApiM Unit :=
    if scope.write then pure () else fail (.forbidden "this token is read-only")
  match r.method, r.segments with
  | .get, ["me"] => ok principal.toJson
  | .get, ["notifications"] => listNotifications ctx scope r
  | .patch, ["notifications"] => requireWrite; patchNotifications ctx scope r
  | .get, ["notifications", id] =>
    getNotification ctx scope (← parseId id) (["1", "true"].contains ((r.query "raw").getD ""))
  | .get, ["notifications", id, "attachments", n] =>
    getAttachment ctx scope (← parseId id) (← parseId n)
  | .put, ["notifications", id, "labels", label] =>
    requireWrite; setLabel ctx scope (← parseId id) (← parseId label) true
  | .delete, ["notifications", id, "labels", label] =>
    requireWrite; setLabel ctx scope (← parseId id) (← parseId label) false
  | .get, ["counts"] => ok (← ctx.dbM (Db.counts · scope))
  | .get, ["labels"] =>
    ok (toJson ((← ctx.dbM Db.listLabels).filter (scope.allowsLabel ·.id)))
  | .get, ["sources"] => sources ctx scope
  | _, _ =>
  -- Past here only the owner's settings. A path that is not one of them is unknown to a token
  -- as much as to a session, and said so: a 403 would read as "tokens may not do this".
  if !sessionOnly.contains (r.segments.headD "") then fail (.notFound "no such endpoint")
  requireSession
  match r.method, r.segments with
  | .get, ["second-factors"] => ok (← ctx.dbM Db.listFactors)
  | .post, ["second-factors", "webauthn", "challenge"] => webauthnChallenge ctx r
  | .post, ["second-factors", "webauthn"] => addWebAuthn ctx r
  | .post, ["second-factors", "totp", "secret"] => totpSecret ctx r
  | .post, ["second-factors", "totp"] => addTotp ctx r
  | .delete, ["second-factors", id] => deleteFactor ctx r (← parseId id)
  | .get, ["tokens"] => ok (← ctx.dbM Db.listTokens)
  | .post, ["tokens"] => createToken ctx r
  | .delete, ["tokens", id] =>
    if ← ctx.dbM (Db.deleteToken · (← parseId id)) then ok (Json.mkObj [("ok", true)])
    else fail (.notFound "no such token")
  | .post, ["labels"] => createLabel ctx r
  | .patch, ["labels", id] =>
    let j ← parseJson r.body
    ctx.dbM (Db.updateLabel · (← parseId id) (← field? j "name") (← field? j "color"))
    ok (Json.mkObj [("ok", true)])
  | .delete, ["labels", id] =>
    ctx.dbM (Db.deleteLabel · (← parseId id))
    ok (Json.mkObj [("ok", true)])
  | .get, ["rules"] => ok (toJson (← ctx.dbM Db.listRules))
  | .post, ["rules"] => createRule ctx r
  | .post, ["rules", "rerun"] =>
    let n ← ctx.dbM Db.rerunRules
    liftIO (bumpChanges none)
    ok (Json.mkObj [("matched", n)])
  | .patch, ["rules", id] => updateRule ctx (← parseId id) r
  | .delete, ["rules", id] =>
    ctx.dbM (Db.deleteRule · (← parseId id))
    ok (Json.mkObj [("ok", true)])
  | .get, ["views"] => ok (toJson (← ctx.dbM Db.listViews))
  | .post, ["views"] =>
    let j ← parseJson r.body
    let name : String ← field j "name"
    let query : Json ← field j "query"
    ok (Json.mkObj [("id", ← ctx.dbM (Db.createView · name query))])
  | .delete, ["views", id] =>
    ctx.dbM (Db.deleteView · (← parseId id))
    ok (Json.mkObj [("ok", true)])
  | _, _ => fail (.notFound "no such endpoint")

def runApi (ctx : AppContext) (r : Req) : IO ApiResponse := do
  try
    match ← (dispatch ctx r).run with
    | .ok resp => pure resp
    | .error e => pure e.toResponse
  catch e =>
    log "http" s!"{r.method} /{"/".intercalate r.segments}: {e}"
    pure (ApiError.server (toString e)).toResponse

/-! ## Wire -/

def headerValue (r : Request Body.Stream) (name : String) : Option String :=
  (Header.Name.ofString? name).bind (r.line.headers.get? ·) |>.map toString

def buildResponse (r : ApiResponse) : Async (Response Body.Full) :=
  let base := Response.withStatus r.status |>.header! "Cache-Control" "no-store"
  let b := r.headers.foldl (fun b (k, v) => b.header! k v) base
  match r.bytes with
  | some bytes => b.fromBytes bytes
  | none => b.json r.body.compress

def contentTypeOf (name : String) : String :=
  if name.endsWith ".html" then "text/html; charset=utf-8"
  else if name.endsWith ".js" then "text/javascript; charset=utf-8"
  else if name.endsWith ".css" then "text/css; charset=utf-8"
  else if name.endsWith ".svg" then "image/svg+xml"
  else if name.endsWith ".woff2" then "font/woff2"
  else if name.endsWith ".txt" then "text/plain; charset=utf-8"
  else "application/octet-stream"

/-- Security headers for the frontend: the app loads nothing from anywhere else. -/
def withPageHeaders (b : Response.Builder) : Response.Builder :=
  b |>.header! "Content-Security-Policy"
      "default-src 'self'; img-src 'self' data:; style-src 'self'; frame-ancestors 'none'"
    |>.header! "X-Content-Type-Options" "nosniff"
    |>.header! "Referrer-Policy" "no-referrer"

def serveStatic (ctx : AppContext) (segs : List String) : Async (Response Body.Full) := do
  if segs.any (fun s => s == ".." || s.startsWith ".") then
    return ← Response.notFound.text "not found"
  let rel := if segs.isEmpty then "index.html" else "/".intercalate segs
  let path := ctx.config.staticDir / rel
  let file := if (← (path.pathExists : IO Bool)) && !(← (path.isDir : IO Bool)) then path
    else ctx.config.staticDir / "index.html"
  if !(← (file.pathExists : IO Bool)) then
    return ← Response.notFound.text s!"no frontend at {ctx.config.staticDir}"
  let bytes ← (IO.FS.readBinFile file : IO ByteArray)
  (withPageHeaders Response.ok
    |>.header! "Content-Type" (contentTypeOf file.toString)
    |>.header! "Cache-Control" "no-cache").fromBytes bytes

/-- `GET /api/events`: a server-sent-events stream that says `change` whenever notifications the
    principal may see change, and pings every 15 s: well inside the server's own idle limit (see
    `serve`) and a proxy's read timeout, either of which would otherwise end a quiet stream. The
    event carries nothing else, so a scoped token learns nothing about activity outside its
    scope. -/
def eventStream (ctx : AppContext) (principal : Principal) : Async (Response Body.Stream) :=
  let relevant : Change → IO Bool := fun c => match principal, c with
    | .session, _ | _, none => pure true
    | .token _ scope, some ids => ctx.withDb (Db.anyVisible · scope ids)
  (Response.ok
    |>.header! "Content-Type" "text/event-stream"
    |>.header! "Cache-Control" "no-store"
    |>.header! "X-Accel-Buffering" "no").stream fun s => do
    let send (text : String) : Async Unit := s.send (Chunk.ofByteArray text.toUTF8)
    send "retry: 3000\n\n"
    let mut seen := (← (changeLog.get : IO _)).1
    let mut ticks := 0
    while !(← s.isClosed) do
      Std.Async.sleep ⟨500⟩
      let (now, change) ← (changesSince seen : IO _)
      if now != seen then
        seen := now
        if ← (relevant change : IO Bool) then send "event: change\ndata: 1\n\n"
      ticks := ticks + 1
      if ticks % 30 == 0 then send ": ping\n\n"

structure AppHandler where
  ctx : AppContext

instance : Handler AppHandler where
  ResponseBody := Body.Any
  onRequest h req := do
    let segs := (req.line.uri.path.toDecodedSegments.filter (· ≠ "")).toList
    match segs with
    | ["api", "events"] =>
      let r : Req := { method := req.line.method, segments := [], query := fun _ => none
                       body := "", header := headerValue req }
      if !(← (Vault.unlocked : IO Bool)) then
        return ((← (Response.withStatus .serviceUnavailable).text "locked" : Response Body.Full) :
          Response Body.Any)
      if let some p ← (h.ctx.authenticate r : IO (Option Principal)) then
        return ((← eventStream h.ctx p : Response Body.Stream) : Response Body.Any)
      else
        return ((← (Response.withStatus .unauthorized).text "not logged in" : Response Body.Full) :
          Response Body.Any)
    | "api" :: rest =>
      let body ← req.body.readAll (maximumSize := some (16 * 1024 * 1024 : UInt64))
      let r : Req := { method := req.line.method, segments := rest
                       query := fun k => req.line.uri.query.get k, body
                       header := headerValue req }
      return ((← buildResponse (← (runApi h.ctx r : IO ApiResponse)) : Response Body.Full) :
        Response Body.Any)
    | _ => return ((← serveStatic h.ctx segs : Response Body.Full) : Response Body.Any)
  onFailure _ err := do
    log "http" s!"connection error: {err}"

def serve (ctx : AppContext) : Async Server := do
  let ip := IPv4Addr.ofString ctx.config.host |>.getD (IPv4Addr.ofParts 127 0 0 1)
  let addr : SocketAddress := .v4 { addr := ip, port := ctx.config.port }
  -- `lingeringTimeout` is how long a connection may go without traffic while a request is in
  -- progress, and an event stream is a request in progress for as long as it is open. Its 10 s
  -- default is shorter than the ping interval, which ended every quiet stream; 30 s is twice it.
  Std.Http.Server.serve addr (AppHandler.mk ctx) { maxHeaders := 256, lingeringTimeout := 30000 }

end Angelia.Server