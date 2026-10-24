import Angelia.Imap.Protocol

/-!
# IMAP client

The I/O half of the IMAP client. Lean's standard library has TCP but no TLS, so the encrypted
stream is provided by an `openssl s_client` child process — it does the handshake and certificate
verification and nothing else; every byte of the IMAP conversation is produced and parsed here.
For testing, any command that connects stdin/stdout to a server can stand in (`transport`).

Reads are blocking, so a client belongs to one dedicated thread. The one exception is `IDLE`,
which another thread may end by sending `DONE` (`Conn.sendDone`), which is written at most once
per `IDLE`.
-/

namespace Angelia.Imap

/-- How to reach the server. -/
inductive Transport where
  /-- TLS from the first byte (port 993). -/
  | implicitTls (host : String) (port : Nat)
  /-- Plain connection upgraded with `STARTTLS` (port 143); openssl performs the upgrade. -/
  | startTls (host : String) (port : Nat)
  /-- Any command bridging stdin/stdout to a server, e.g. `nc 127.0.0.1 1143` for tests. -/
  | command (argv : Array String)
deriving Repr, Inhabited

def Transport.argv : Transport → Array String
  | .implicitTls host port =>
    #["openssl", "s_client", "-quiet", "-verify_return_error", "-verify_hostname", host,
      "-servername", host, "-connect", s!"{host}:{port}"]
  | .startTls host port =>
    #["openssl", "s_client", "-quiet", "-verify_return_error", "-verify_hostname", host,
      "-servername", host, "-starttls", "imap", "-connect", s!"{host}:{port}"]
  | .command argv => argv

abbrev Child := IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .null }

structure Conn where
  child : Child
  tag : IO.Ref Nat
  /-- Whether `DONE` has been sent for the current `IDLE`. -/
  doneSent : IO.Ref Bool
  /-- Capabilities, as last announced. -/
  caps : IO.Ref (List String)

/-- A server refused a command (`NO`/`BAD`), as opposed to the connection failing. -/
def commandError (cmd status text : String) : IO.Error :=
  IO.userError s!"IMAP {cmd.splitOn " " |>.headD cmd} failed: {status} {text}"

namespace Conn

def write (c : Conn) (s : String) : IO Unit := do
  c.child.stdin.write (toBytes s)
  c.child.stdin.flush

/-- Read one line (without its CRLF). End of stream is an error: the connection is gone. -/
partial def readLine (c : Conn) : IO String := do
  let rec go (acc : ByteArray) : IO ByteArray := do
    let b ← c.child.stdout.read 1
    if b.isEmpty then throw (IO.userError "IMAP connection closed")
    if b[0]! == 10 then return acc
    go (acc.push b[0]!)
  let line ← go ByteArray.empty
  let line := if line.size > 0 && line[line.size - 1]! == 13 then line.extract 0 (line.size - 1) else line
  return latin1 line

/-- Read exactly `n` bytes. -/
partial def readExact (c : Conn) (n : Nat) : IO String := do
  let rec go (acc : ByteArray) : IO ByteArray := do
    if acc.size ≥ n then return acc
    let chunk ← c.child.stdout.read (n - acc.size).toUSize
    if chunk.isEmpty then throw (IO.userError "IMAP connection closed inside a literal")
    go (acc ++ chunk)
  return latin1 (← go ByteArray.empty)

/-- Read one complete response, including any literals it carries. -/
partial def readResponse (c : Conn) : IO Response := do
  let rec go (acc : Response) : IO Response := do
    let line ← c.readLine
    let acc := acc.push (.text line)
    match literalSize? line with
    | some n => go (acc.push (.literal (← c.readExact n)))
    | none => return acc
  go #[]

def nextTag (c : Conn) : IO String := do
  let n ← c.tag.modifyGet fun n => (n, n + 1)
  return s!"h{n}"

/-- Run a command and collect its untagged responses. `onContinuation` answers `+` requests
    (for `AUTHENTICATE`). A `NO`/`BAD` completion is thrown as `commandError`. -/
partial def command (c : Conn) (cmd : String) (onContinuation : Option String := none) :
    IO (Array Response) := do
  let tag ← c.nextTag
  c.write s!"{tag} {cmd}\r\n"
  let rec loop (acc : Array Response) : IO (Array Response) := do
    let r ← c.readResponse
    if r.isContinuation then
      c.write ((onContinuation.getD "") ++ "\r\n")
      loop acc
    else match r.tagged? with
      | some (t, status, text) =>
        if t != tag then loop acc
        else if status == "OK" then
          if let some caps := r.capabilities? then c.caps.set caps
          return acc
        else throw (commandError cmd status text)
      | none =>
        if let some caps := r.capabilities? then c.caps.set caps
        loop (acc.push r)
  loop #[]

/-- Connect and read the greeting (or, after `STARTTLS`, the capabilities). -/
def «open» (t : Transport) : IO Conn := do
  let argv := t.argv
  let child ← IO.Process.spawn {
    cmd := argv[0]!, args := argv.extract 1, stdin := .piped, stdout := .piped, stderr := .null }
  let c : Conn := { child, tag := ← IO.mkRef 1, doneSent := ← IO.mkRef false, caps := ← IO.mkRef [] }
  match t with
  | .startTls .. =>
    -- openssl read the greeting before upgrading, and a server sends none after `STARTTLS`.
    discard <| c.command "CAPABILITY"
  | _ =>
    let greeting ← c.readResponse
    if greeting.head.startsWith "* BYE" then throw (IO.userError s!"IMAP server refused: {greeting.head}")
    if let some caps := greeting.capabilities? then c.caps.set caps
  return c

/-- Terminate the transport. Safe to call more than once; unblocks a thread reading from it. -/
def close (c : Conn) : IO Unit := do
  try c.child.kill catch _ => pure ()
  try discard c.child.wait catch _ => pure ()

def hasCap (c : Conn) (cap : String) : IO Bool := return (← c.caps.get).contains cap.toUpper

/-- How to authenticate. -/
inductive Credentials where
  | password (user password : String)
  /-- An OAuth 2 access token, for providers that disable password login (Microsoft 365). -/
  | oauth2 (user accessToken : String)

/-- Authenticate: XOAUTH2 for a token; for a password, SASL PLAIN if offered, else `LOGIN`. -/
def login (c : Conn) : Credentials → IO Unit
  | .oauth2 user token => do
    -- On failure the server sends a `+` challenge with a JSON error; an empty reply ends it.
    discard <| c.command s!"AUTHENTICATE XOAUTH2 {saslXOAuth2 user token}" (onContinuation := some "")
  | .password user password => do
  if (← c.caps.get).isEmpty then discard <| c.command "CAPABILITY"
  if ← c.hasCap "AUTH=PLAIN" then
    discard <| c.command "AUTHENTICATE PLAIN" (onContinuation := some (saslPlain user password))
  else
    match quote user, quote password with
    | .ok u, .ok p => discard <| c.command s!"LOGIN {u} {p}"
    | .error e, _ | _, .error e => throw (IO.userError e)
  -- Servers commonly announce more capabilities after login.
  if !(← c.hasCap "IDLE") then discard <| c.command "CAPABILITY"

/-- The state of a mailbox after `EXAMINE`. -/
structure Mailbox where
  uidValidity : Nat
  uidNext : Option Nat
  exists_ : Nat
deriving Repr

/-- Open a mailbox read-only. Nothing the client does ever changes the mailbox. -/
def examine (c : Conn) (mailbox : String) : IO Mailbox := do
  let name ← match quote (encodeMailbox mailbox) with
    | .ok n => pure n
    | .error e => throw (IO.userError e)
  let rs ← c.command s!"EXAMINE {name}"
  let uidValidity := (rs.findSome? (·.codeNat? "UIDVALIDITY")).getD 0
  let uidNext := rs.findSome? (·.codeNat? "UIDNEXT")
  let exists_ := (rs.findSome? Response.exists?).getD 0
  return { uidValidity, uidNext, exists_ }

/-- Fetch messages. `set` is a sequence set (`10:*`), interpreted as UIDs when `byUid`. Bodies are
    fetched with `PEEK` (no `\Seen` side effect) and truncated at `maxBytes`. -/
def fetch (c : Conn) (set : String) (byUid : Bool) (maxBytes : Nat) : IO (Array Fetched) := do
  let pre := if byUid then "UID " else ""
  let rs ← c.command s!"{pre}FETCH {set} (UID FLAGS INTERNALDATE BODY.PEEK[]<0.{maxBytes}>)"
  return rs.filterMap Response.fetch?

/-- End the current `IDLE`. Only the first call per `IDLE` writes anything. -/
def sendDone (c : Conn) : IO Unit := do
  let already ← c.doneSent.modifyGet fun d => (d, true)
  if !already then
    try c.write "DONE\r\n" catch _ => pure ()

/-- Enter `IDLE` and wait until the server reports a change or `DONE` is sent (by `sendDone`,
    typically from a timer). Returns whether new mail may have arrived. -/
partial def idle (c : Conn) : IO Bool := do
  let tag ← c.nextTag
  c.doneSent.set false
  c.write s!"{tag} IDLE\r\n"
  let rec loop (changed : Bool) : IO Bool := do
    let r ← c.readResponse
    if r.isContinuation then loop changed
    else match r.tagged? with
      | some (t, status, text) =>
        if t != tag then loop changed
        else if status == "OK" then return changed
        else throw (commandError "IDLE" status text)
      | none =>
        let changed := changed || (r.exists?).isSome || (r.head.splitOn " ").contains "RECENT"
        if changed then c.sendDone
        loop changed
  loop false

def logout (c : Conn) : IO Unit := do
  try discard <| c.command "LOGOUT" catch _ => pure ()
  c.close

end Conn

end Angelia.Imap