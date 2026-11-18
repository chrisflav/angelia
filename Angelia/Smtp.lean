import Angelia.Imap.Client

/-!
# SMTP client

Message submission (RFC 6409): enough of SMTP to hand one message to a mail server, over the same
`openssl s_client` child process the IMAP client uses for TLS -- implicit TLS on 465, or
`STARTTLS` on 587, which openssl performs. Authentication is `AUTH PLAIN` or `LOGIN` with a
password, or `XOAUTH2` with an access token (Microsoft 365, Gmail), the credentials the IMAP
side already has.
-/

namespace Angelia.Smtp

open Angelia.Imap (Transport Child)

def argv : Transport → Array String
  | .startTls host port =>
    #["openssl", "s_client", "-quiet", "-verify_return_error", "-verify_hostname", host,
      "-servername", host, "-starttls", "smtp", "-connect", s!"{host}:{port}"]
  | t => t.argv

structure Conn where
  child : Child

/-- A server's reply: its code, and the text of its lines. -/
structure Reply where
  code : Nat
  lines : List String
deriving Repr

def Reply.text (r : Reply) : String := " / ".intercalate r.lines

/-- The code and text of one reply line, and whether more lines follow (`250-...`). -/
def parseLine (l : String) : Option (Nat × Bool × String) := do
  let code ← (l.take 3).toString.toNat?
  let sep := (l.drop 3).toString.front
  return (code, sep == '-', (l.drop 4).toString)

namespace Conn

def write (c : Conn) (s : String) : IO Unit := do
  c.child.stdin.write (toBytes s)
  c.child.stdin.flush

partial def readLine (c : Conn) : IO String := do
  let rec go (acc : ByteArray) : IO ByteArray := do
    let b ← c.child.stdout.read 1
    if b.isEmpty then throw (IO.userError "SMTP connection closed")
    if b[0]! == 10 then return acc
    go (acc.push b[0]!)
  let line ← go ByteArray.empty
  let line := if line.size > 0 && line[line.size - 1]! == 13 then line.extract 0 (line.size - 1) else line
  return latin1 line

partial def readReply (c : Conn) : IO Reply := do
  let rec go (lines : List String) : IO Reply := do
    let l ← c.readLine
    let some (code, more, text) := parseLine l
      | throw (IO.userError s!"SMTP: malformed reply: {l}")
    if more then go (text :: lines) else return { code, lines := (text :: lines).reverse }
  go []

/-- Send a command (none: just read, as for the greeting) and check the reply's code. `what`
    names the step in an error, so an `AUTH` line, which carries a secret, is never quoted. -/
def step (c : Conn) (what : String) (cmd : Option String) (ok : Nat → Bool) : IO Reply := do
  if let some s := cmd then c.write (s ++ "\r\n")
  let r ← c.readReply
  if !ok r.code then throw (IO.userError s!"SMTP {what} refused: {r.code} {r.text}")
  return r

def close (c : Conn) : IO Unit := do
  try c.child.kill catch _ => pure ()
  try discard c.child.wait catch _ => pure ()

end Conn

/-- A message as `DATA` carries it: CRLF line ends, a line starting with `.` given another, and
    the final line ending. -/
def dotStuff (message : String) : String :=
  let lines := (message.replace "\r\n" "\n").splitOn "\n"
  let lines := if lines.getLast? == some "" then lines.dropLast else lines
  String.join (lines.map fun l => (if l.startsWith "." then "." ++ l else l) ++ "\r\n")

/-- Hand `message` to the server for `recipients`, from `sender` (envelope addresses, bare).
    Throws with the server's words if any step is refused; returns once the server has taken
    responsibility for the message. -/
def send (t : Transport) (creds : Imap.Conn.Credentials) (sender : String)
    (recipients : Array String) (message : String) : IO Unit := do
  let a := argv t
  let child ← IO.Process.spawn {
    cmd := a[0]!, args := a.extract 1, stdin := .piped, stdout := .piped, stderr := .null }
  let c : Conn := { child }
  try
    -- After `STARTTLS` the server sends no new greeting; openssl read the first one.
    match t with
    | .startTls .. => pure ()
    | _ => discard <| c.step "greeting" none (· == 220)
    let domain := (sender.splitOn "@").getLast!
    let ehlo ← c.step "EHLO" (some s!"EHLO {domain}") (· == 250)
    let mechs := (ehlo.lines.filterMap fun l =>
        if l.toUpper.startsWith "AUTH" then some ((l.drop 5).toString.toUpper.splitOn " ")
        else none)
      |>.flatten
    match creds with
    | .oauth2 user token =>
      -- A refusal comes as a 334 challenge with the reason; an empty line ends the exchange.
      let r ← c.step "AUTH XOAUTH2" (some s!"AUTH XOAUTH2 {Imap.saslXOAuth2 user token}")
        (fun n => n == 235 || n == 334)
      if r.code == 334 then
        discard <| c.step "AUTH XOAUTH2" (some "") (· == 235)
    | .password user password =>
      if mechs.contains "PLAIN" || !mechs.contains "LOGIN" then
        let plain := Imap.saslPlain user password
        discard <| c.step "AUTH PLAIN" (some s!"AUTH PLAIN {plain}") (· == 235)
      else
        discard <| c.step "AUTH LOGIN" (some "AUTH LOGIN") (· == 334)
        discard <| c.step "AUTH LOGIN" (some (Imap.base64Encode user.toUTF8)) (· == 334)
        discard <| c.step "AUTH LOGIN" (some (Imap.base64Encode password.toUTF8)) (· == 235)
    discard <| c.step "MAIL FROM" (some s!"MAIL FROM:<{sender}>") (· == 250)
    for r in recipients do
      discard <| c.step s!"RCPT TO <{r}>" (some s!"RCPT TO:<{r}>") (fun n => n == 250 || n == 251)
    discard <| c.step "DATA" (some "DATA") (· == 354)
    c.write (dotStuff message)
    discard <| c.step "the message" (some ".") (· == 250)
    -- The message is accepted; how the server takes leave does not matter.
    discard <| (c.step "QUIT" (some "QUIT") (fun _ => true)).toBaseIO
  finally
    c.close

end Angelia.Smtp
