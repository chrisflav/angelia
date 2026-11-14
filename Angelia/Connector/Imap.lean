import Angelia.Ingest
import Angelia.Imap.Client
import Angelia.Mail.Compose
import Angelia.Smtp
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

## Sent mail, and sending

The sent folder is watched too (`syncSent`, on by default): the mailbox the server flags `\Sent`
(RFC 6154), or `sentFolder` by name. What it holds is stored as *outgoing* -- out of the inbox,
in its conversation -- so what was sent from any mail program shows.

With `smtp` settings a source can send, replies and new messages alike (`send`): by SMTP
submission, from `address` (default: the username) as `displayName`, then into the sent folder
with `APPEND` (`smtp.saveSent`, on by default; off for Gmail and Microsoft 365, which file what
they send themselves). `smtp` takes `host`, `port` (465, or 587 with `tls: "starttls"`), `tls`,
and `username` and `password` / `passwordCommand`, which default to the account's own. An OAuth
account sends with a token from the same refresh token, for `smtp.oauth2Scope` (default: the
account's scope) -- Microsoft 365 wants `https://outlook.office.com/SMTP.Send offline_access`,
which the refresh token must have been granted, and SMTP AUTH enabled for the mailbox.
-/

open Lean Angelia.Imap

namespace Angelia.Connector.ImapSource

/-- How much of a message is fetched: whole messages, attachments included, up to a size no mail
    server sends anyway. A larger one is stored cut off there, and marked `truncated`. -/
def defaultMaxBytes : Nat := 50 * 1024 * 1024

/-- How mail is sent from the account, where it can be. -/
structure Smtp where
  transport : Transport
  credentials : IO Conn.Credentials
  /-- Put a copy of what is sent into the sent folder, as mail programs do. Off for a server
      that does it itself (Gmail, Microsoft 365), which would otherwise keep two. -/
  saveSent : Bool

structure Settings where
  transport : Transport
  username : String
  /-- Looked up on every connect, so a token helper can hand out fresh tokens. -/
  credentials : IO Conn.Credentials
  folders : Array String
  /-- What mail is sent from (`address`, else the username), and the name it carries
      (`displayName`). -/
  address : String
  name : String
  /-- Also watch the sent folder, so that what is sent from anywhere shows, as sent. -/
  syncSent : Bool
  /-- The sent folder by name, for a server that flags none `\Sent`. -/
  sentFolder : Option String
  smtp : Option Smtp
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

/-- Where a server is, from `host`, `port` and `tls` in `j` (or `transport`, for tests). -/
def transportOf (what : String) (j : Json) (implicitPort starttlsPort : Nat) : IO Transport := do
  let get {α} [FromJson α] (k : String) (d : α) : α := (j.getObjValAs? α k).toOption.getD d
  let starttls := (get "tls" "implicit" : String) == "starttls"
  match j.getObjValAs? (Array String) "transport" with
  | .ok argv => pure (Transport.command argv)
  | .error _ =>
    let host : String := get "host" ""
    if host.isEmpty then throw (IO.userError s!"{what}: 'host' is required")
    let port : Nat := get "port" (if starttls then starttlsPort else implicitPort)
    pure (if starttls then .startTls host port else .implicitTls host port)

/-- How to log in as `username`: with `oauth`, tokens from the refresh token; else the secret in
    `j` (an access token or a password), falling back to the account's own in `account`, which
    is how the SMTP side shares the IMAP password unless it is given another. -/
def credentialsFor (source : String) (dbPath : System.FilePath) (j account : Json)
    (username : String) (oauth : Option OAuth2.Client) : IO (IO Conn.Credentials) :=
  match oauth with
  | some client => oauth2Credentials source dbPath account username client
  | none => pure do
    let first (k : String) : IO (Option String) := do
      if let some v ← secret j k then return some v
      secret account k
    if let some token ← first "accessToken" then return .oauth2 username token
    let some password ← first "password"
      | throw (IO.userError
          "imap: 'password', 'passwordCommand', 'accessTokenCommand' or 'oauth2' is required")
    return .password username password

/-- The address the account sends from: `address`, else the username. -/
def ownAddress (j : Json) : String :=
  ((j.getObjValAs? String "address").toOption.filter (!·.isEmpty)).getD
    ((j.getObjValAs? String "username").toOption.getD "")

def Settings.load (source : String) (dbPath : System.FilePath) (j : Json)
    (checkCredentials := true) : IO Settings := do
  let get {α} [FromJson α] (k : String) (d : α) : α := (j.getObjValAs? α k).toOption.getD d
  let transport ← transportOf "imap" j 993 143
  let username : String := get "username" ""
  let oauth := (j.getObjValAs? OAuth2.Client "oauth2").toOption
  let credentials ← credentialsFor source dbPath j j username oauth
  -- Fail at startup, not on the first connect, if the secret cannot be had at all.
  if checkCredentials then discard credentials
  let smtp ← match j.getObjVal? "smtp" with
    | .ok sj@(.obj _) => do
      let sget {α} [FromJson α] (k : String) (d : α) : α := (sj.getObjValAs? α k).toOption.getD d
      let smtpUser : String := sget "username" username
      -- The same OAuth client, for a token SMTP accepts: Microsoft wants another scope.
      let soauth := oauth.map fun c => { c with scope := sget "oauth2Scope" c.scope }
      pure (some { transport := ← transportOf "smtp" sj 465 587
                   credentials := ← credentialsFor source dbPath sj j smtpUser soauth
                   saveSent := sget "saveSent" true : Smtp })
    | _ => pure none
  return {
    transport, username, credentials, smtp
    address := ownAddress j
    name := get "displayName" ""
    folders := get "folders" #["INBOX"]
    syncSent := get "syncSent" true
    sentFolder := (j.getObjValAs? String "sentFolder").toOption
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
  let outgoing := (payload.getObjValAs? Bool "outgoing").toOption.getD false
  let m := Mail.parseMessage raw
  let hs := Mail.parseHeaders (Mail.splitHeaderBody raw).1
  let recipients := #["to", "cc"].flatMap fun h => Mail.parseAddressList ((hs.get? h).getD "")
    |>.map fun a => if a.name.isEmpty then a.addr else a.name
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
    -- What the account sent is read, whatever the server's flags say.
    read := outgoing || flags.contains "\\Seen"
    -- The parser marks the part a cut would fall in; whether there was a cut is known here.
    attachments := m.attachments.map fun a => { a with «partial» := truncated && a.partial }
    outgoing
    recipients := ", ".intercalate recipients.toList }

/-- The dedupe key: the `Message-ID` where there is one, else the message's position. -/
def externalId (folder : String) (uidValidity : Nat) (f : Fetched) : String :=
  let raw := f.body.getD ""
  match Mail.messageIdOf raw with
  | some id => s!"mid:{id}"
  | none => s!"uid:{folder}/{uidValidity}/{f.uid.getD f.seq}"

/-- The raw event of a fetched message; `outgoing` for one from the sent folder. -/
def toRawEvent (folder : String) (uidValidity maxBytes : Nat) (outgoing : Bool) (f : Fetched) :
    RawEvent :=
  let raw := f.body.getD ""
  { externalId := externalId folder uidValidity f
    payload := Json.mkObj (([
      ("folder", folder), ("uid", toJson f.uid), ("uidValidity", uidValidity),
      ("flags", toJson f.flags), ("internalDate", toJson f.internalDate),
      ("truncated", decide (raw.length ≥ maxBytes)), ("raw", raw)] : List (String × Json)) ++
      (if outgoing then [("outgoing", toJson true)] else [])) }

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
def syncFolder (ctx : ConnectorCtx) (s : Settings) (c : Conn) (folder : String)
    (outgoing : Bool := false) : IO Nat := do
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
    let events := fetched.map (toRawEvent folder mb.uidValidity s.maxBytes outgoing)
    fresh := fresh + (← ctx.ingest events)
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

/-- What a worker watches: a folder by name, or the account's sent folder, whatever the server
    calls it (`sentFolder`, else the mailbox it flags `\Sent`), looked up on every connect. -/
inductive Target where
  | folder (name : String)
  | sent

/-- The sent folder's name, if the account has one. -/
def sentFolderOf (s : Settings) (c : Conn) : IO (Option String) := do
  if let some f := s.sentFolder then return some f
  return sentMailbox? (← c.list)

/-- One connection's lifetime: connect, then sync and wait for changes until something fails. -/
partial def session (ctx : ConnectorCtx) (s : Settings) (target : Target) : IO Unit := do
  let label := match target with | .folder f => f | .sent => "sent folder"
  ctx.health "connecting" (some label)
  let c ← Conn.open s.transport
  try
    c.login (← s.credentials)
    let folder ← match target with
      | .folder f => pure (some f)
      | .sent => sentFolderOf s c
    -- No sent folder, or one already watched as an ordinary folder: nothing to do here. Asked
    -- again in a while, since a mail program may create one.
    let some folder := folder.filter (fun f => !(target matches .sent) || !s.folders.contains f)
      | c.logout
        discard <| ctx.sleep (6 * 3600)
        return
    let outgoing := target matches .sent
    let canIdle ← c.hasCap "IDLE"
    let generation ← IO.mkRef 0
    let rec loop : IO Unit := do
      if ← ctx.stopping then return
      let n ← syncFolder ctx s c folder outgoing
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
  let targets := s.folders.map Target.folder ++ (if s.syncSent then #[Target.sent] else #[])
  let workers ← targets.mapM fun target => do
    let wctx ← ctx.fork
    IO.asTask (prio := .dedicated) (wctx.supervise (session wctx s target))
  for w in workers do
    match ← IO.wait w with
    | .ok _ => pure ()
    | .error e => ctx.log s!"worker ended: {e}"

/-! ## Sending -/

/-- Whether a source can send: it has `smtp` settings. -/
def canSend (source : SourceConfig) : Bool :=
  source.settings.getObjVal? "smtp" matches .ok (.obj _)

/-- Put a sent message into the sent folder. Returns the folder, or `none` if there is none. -/
def saveToSent (s : Settings) (message : String) : IO (Option String) := do
  let c ← Conn.open s.transport
  try
    c.login (← s.credentials)
    let some folder ← sentFolderOf s c | c.logout; return none
    c.append folder message
    c.logout
    return some folder
  catch e =>
    c.close
    throw e

/-- Send a draft from the account by SMTP, in reply to the message whose raw payload is given, if
    one is: `In-Reply-To` and `References` keep it in its thread. A copy goes into the sent folder
    (`saveSent`); failing that is logged, not thrown, since the message is sent by then. Returns
    the raw event of the message as sent, to be stored as an outgoing one -- the same event, by
    its `Message-ID`, that syncing the sent folder finds later. -/
def send (source : SourceConfig) (dbPath : System.FilePath) (d : Draft) (original : Option Json) :
    IO RawEvent := do
  let s ← Settings.load source.name dbPath source.settings (checkCredentials := false)
  let some smtp := s.smtp
    | throw (IO.userError s!"source '{source.name}' cannot send: it has no 'smtp' settings")
  let recipients := d.recipients.map (·.addr)
  if recipients.isEmpty then throw (IO.userError "a message needs at least one recipient")
  let raw := original.bind (·.getObjValAs? String "raw" |>.toOption)
  let (inReplyTo, references) := (raw.map Mail.replyThreading).getD (none, [])
  let sender : Mail.Address := { name := s.name, addr := s.address }
  let messageId := s!"{← randomToken 16}@{sender.domain}"
  let message := Mail.compose
    { «from» := sender, date := ← nowSeconds, messageId, inReplyTo, references } d
  Smtp.send smtp.transport (← smtp.credentials) s.address recipients message
  let folder ← if !smtp.saveSent then pure none else
    try saveToSent s message
    catch e =>
      Angelia.log source.name s!"sent, but not saved to the sent folder: {e}"
      pure none
  return { externalId := s!"mid:{messageId}"
           payload := Json.mkObj [("folder", toJson folder), ("flags", toJson #["\\Seen"]),
             ("outgoing", true), ("truncated", false), ("raw", message)] }

/-- The prefilled reply to a mail, from its raw payload: to its sender (or `Reply-To`), and with
    `all` to its other recipients too, never to the account itself. -/
def replyDraft (source : SourceConfig) (payload : Json) (all : Bool) : Option Draft := do
  let raw ← (payload.getObjValAs? String "raw").toOption
  let own := [ownAddress source.settings,
    (source.settings.getObjValAs? String "username").toOption.getD ""].filter (!·.isEmpty)
  return Mail.replyDraft raw own all

end Angelia.Connector.ImapSource
