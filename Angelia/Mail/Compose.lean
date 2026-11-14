import Angelia.Mail.Mime
import Angelia.Imap.Protocol

/-!
# Writing messages

The other direction of `Angelia.Mail`: an internet message from a `Draft`, and the draft of a
reply to a received message. What is written is plain ASCII whatever the text -- header text in
RFC 2047 encoded words, the body (UTF-8) in quoted-printable -- so it passes through any server,
and through the byte-string handling here, unchanged.
-/

namespace Angelia.Mail

/-! ## Addresses -/

/-- A mailbox: a display name (decoded, possibly empty) and an address. -/
structure Address where
  name : String := ""
  addr : String
deriving Repr, BEq, Inhabited

/-- Split an address list at the commas that separate addresses: not those inside a quoted
    display name, a comment or angle brackets. -/
def splitAddresses (v : String) : List String :=
  go v.toList [] [] false 0 false
where
  go : List Char → List Char → List String → Bool → Nat → Bool → List String
    | [], cur, acc, _, _, _ => (String.ofList cur.reverse :: acc).reverse
    | '\\' :: c :: rest, cur, acc, q, d, a => go rest (c :: '\\' :: cur) acc q d a
    | '"' :: rest, cur, acc, q, d, a => go rest ('"' :: cur) acc (!q) d a
    | '(' :: rest, cur, acc, false, d, a => go rest ('(' :: cur) acc false (d + 1) a
    | ')' :: rest, cur, acc, false, d, a => go rest (')' :: cur) acc false (d - 1) a
    | '<' :: rest, cur, acc, false, d, _ => go rest ('<' :: cur) acc false d true
    | '>' :: rest, cur, acc, false, d, _ => go rest ('>' :: cur) acc false d false
    | ',' :: rest, cur, acc, false, 0, false =>
      go rest [] (String.ofList cur.reverse :: acc) false 0 false
    | c :: rest, cur, acc, q, d, a => go rest (c :: cur) acc q d a

/-- One address as written in a header or by a person: `Name <a@b>`, `"Doe, Jane" <a@b>`,
    `a@b`, or `a@b (Name)`. The display name is decoded (RFC 2047). Anything without an `@`
    -- a group's name, `undisclosed-recipients:;` -- is not an address. -/
def parseAddress (s : String) : Option Address := do
  let s := s.trimAscii.toString
  let unquote (n : String) : String :=
    let n := n.trimAscii.toString
    let n := if n.startsWith "\"" && n.endsWith "\"" && n.length ≥ 2 then
      ((n.drop 1).dropEnd 1).toString.replace "\\\"" "\"" |>.replace "\\\\" "\\" else n
    decodeHeader n
  let (name, addr) ← match s.splitOn "<" with
    | name :: rest@(_ :: _) =>
      let inner := "<".intercalate rest
      some (unquote name, ((inner.splitOn ">").headD "").trimAscii.toString)
    | _ =>
      match s.splitOn "(" with
      | a :: rest@(_ :: _) =>
        some (unquote (((("(".intercalate rest).splitOn ")").headD "")), a.trimAscii.toString)
      | _ => some ("", s)
  -- A group is `name: a, b;`, whose first member arrives here with the name in front.
  let addr := (addr.splitOn ":").getLast!.replace ";" "" |>.trimAscii.toString
  if !addr.contains '@' || addr.any (fun c => c.isWhitespace || c == ',' || c == '"') then none
  return { name, addr }

/-- Every address in an address-list header value, or in what a person typed into a field. -/
def parseAddressList (v : String) : Array Address :=
  (splitAddresses v).toArray.filterMap parseAddress

/-! ## Encoding -/

/-- Whether text can go into a header as it is: printable ASCII and spaces. -/
def plainAscii (s : String) : Bool := s.all fun c => c.toNat ≥ 0x20 && c.toNat < 0x7F

/-- RFC 2047 B-encoded words for `s`, each at most 75 characters as the RFC requires, split
    between characters rather than inside one. -/
def encodedWords (s : String) : List String :=
  -- 12 characters of `=?UTF-8?B??=` leave 63 of base64: 45 bytes of UTF-8.
  let chunks := s.toList.foldl (fun (acc : List (List Char)) c =>
    match acc with
    | cur :: rest =>
      if (String.ofList (cur.reverse ++ [c])).utf8ByteSize > 45 then [c] :: acc
      else (c :: cur) :: rest
    | [] => [[c]]) []
  chunks.reverse.map fun cs =>
    s!"=?UTF-8?B?{Imap.base64Encode (String.ofList cs.reverse).toUTF8}?="

/-- Unstructured header text (a subject): as it is if it is plain ASCII, else encoded words,
    one per folded line. -/
def encodeText (s : String) : String :=
  if plainAscii s then s else "\r\n ".intercalate (encodedWords s)

/-- A display name: as it is if it is all atoms, quoted if it has specials (`Doe, Jane`), and
    encoded words if it is not ASCII. -/
def encodePhrase (s : String) : String :=
  let atext (c : Char) := c.isAlphanum || "!#$%&'*+-/=?^_`{|}~ ".toList.contains c
  if !plainAscii s then " ".intercalate (encodedWords s)
  else if s.all atext then s
  else "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

def Address.format (a : Address) : String :=
  if a.name.isEmpty then a.addr else s!"{encodePhrase a.name} <{a.addr}>"

/-- The domain of an address, for the message id. -/
def Address.domain (a : Address) : String := (a.addr.splitOn "@").getLast!

/-- Quoted-printable (RFC 2045) of UTF-8 text, with CRLF line ends and lines of at most 76
    characters. Text is never at risk of the `.` a lone line would mean to SMTP, since a line
    of just `.` is written `=2E`. -/
def quotedPrintableEncode (text : String) : String :=
  let hex := "0123456789ABCDEF".toList.toArray
  let esc (b : UInt8) : String := String.ofList ['=', hex[b.toNat / 16]!, hex[b.toNat % 16]!]
  let line (l : String) : String := Id.run do
    let bytes := l.toUTF8
    let mut out := ""
    let mut width := 0
    for i in [0:bytes.size] do
      let b := bytes[i]!
      let last := i + 1 == bytes.size
      let tok :=
        if (b == 0x20 || b == 0x09) && !last then String.singleton (Char.ofNat b.toNat)
        else if b > 0x20 && b < 0x7F && b != 0x3D && !(b == 0x2E && i == 0 && last) then
          String.singleton (Char.ofNat b.toNat)
        else esc b
      -- Room for the `=` of a soft break.
      if width + tok.length > 75 then
        out := out ++ "=\r\n"
        width := 0
      out := out ++ tok
      width := width + tok.length
    return out
  let lines := (text.replace "\r\n" "\n").splitOn "\n"
  "\r\n".intercalate (lines.map line)

/-! ## Dates -/

/-- Days since 1970-01-01 to a proleptic Gregorian date (Howard Hinnant's `civil_from_days`). -/
def civilFromDays (z : Int) : Int × Nat × Nat :=
  let z := z + 719468
  -- `/` on `Int` rounds down, so no correction for negative days is needed.
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  ((if m ≤ 2 then y + 1 else y), m.toNat, d.toNat)

/-- An RFC 5322 date in UTC: `Sat, 14 Nov 2026 18:20:05 +0000`. -/
def formatDate (t : Int) : String :=
  let days := t / 86400
  let secs := (t % 86400).toNat
  let (y, m, d) := civilFromDays days
  let wd := ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"][((days + 4) % 7).toNat]!
  let mon := ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov",
    "Dec"][m - 1]!
  let two (n : Nat) := if n < 10 then s!"0{n}" else toString n
  s!"{wd}, {d} {mon} {y} {two (secs / 3600)}:{two (secs / 60 % 60)}:{two (secs % 60)} +0000"

/-! ## Messages -/

/-- Everything a message is written from, besides the draft. -/
structure Envelope where
  «from» : Address
  date : Int
  /-- Without angle brackets. -/
  messageId : String
  /-- The message this answers, and the thread before it, oldest first; ids without brackets. -/
  inReplyTo : Option String := none
  references : List String := []

/-- The message, as sent and stored: ASCII, CRLF line ends. Bcc is not written, only sent to. -/
def compose (e : Envelope) (d : Draft) : String :=
  let list (xs : Array String) := ",\r\n ".intercalate
    ((xs.flatMap parseAddressList).toList.map Address.format)
  let ids (xs : List String) := "\r\n ".intercalate (xs.map (s!"<{·}>"))
  let headers := [
      some s!"From: {e.from.format}",
      some s!"To: {list d.to}",
      if (d.cc.flatMap parseAddressList).isEmpty then none else some s!"Cc: {list d.cc}",
      some s!"Subject: {encodeText d.subject}",
      some s!"Date: {formatDate e.date}",
      some s!"Message-ID: <{e.messageId}>",
      e.inReplyTo.map (s!"In-Reply-To: <{·}>"),
      if e.references.isEmpty then none else some s!"References: {ids e.references}",
      some "MIME-Version: 1.0",
      some "Content-Type: text/plain; charset=utf-8",
      some "Content-Transfer-Encoding: quoted-printable",
      some "User-Agent: angelia"].filterMap id
  "\r\n".intercalate headers ++ "\r\n\r\n" ++ quotedPrintableEncode d.body ++ "\r\n"

/-- Every address a draft goes to, Bcc included: the SMTP envelope's recipients. -/
def _root_.Angelia.Draft.recipients (d : Draft) : Array Address :=
  (d.to ++ d.cc ++ d.bcc).flatMap parseAddressList

/-! ## Replies -/

/-- What a reply to a raw message needs to stay in its thread: the id it answers, and the
    references, the original's own last. -/
def replyThreading (raw : String) : Option String × List String :=
  let hs := parseHeaders (splitHeaderBody raw).1
  let id := (messageIds ((hs.get? "message-id").getD "")).head?
  let refs := messageIds ((hs.get? "references").getD "")
  let refs := if refs.isEmpty then (messageIds ((hs.get? "in-reply-to").getD "")) else refs
  (id, refs ++ id.toList)

/-- The subject of a reply: `Re: ` before it, unless it has one (or `AW:`, `SV:`, ...) already. -/
def replySubject (s : String) : String :=
  let l := s.trimAscii.toString.toLower
  if ["re:", "aw:", "sv:", "antw:", "r:"].any (l.startsWith ·) then s.trimAscii.toString
  else s!"Re: {s.trimAscii}"

/-- The draft of a reply to a raw message, from the account with addresses `own`: to its
    `Reply-To`, else its sender -- or, for one of the account's own messages, to whom it went.
    Replying to all adds the other recipients as copies, never the account itself. The body
    quotes the original under a line saying who wrote it. -/
def replyDraft (raw : String) (own : List String) (all : Bool) : Draft :=
  let hs := parseHeaders (splitHeaderBody raw).1
  let addrs (n : String) := parseAddressList ((hs.get? n).getD "")
  let own := own.map String.toLower
  let mine (a : Address) := own.contains a.addr.toLower
  let replyTo := addrs "reply-to"
  let sender := if replyTo.isEmpty then addrs "from" else replyTo
  let to := if !sender.isEmpty && sender.all mine then addrs "to" else sender
  let others := if all then (addrs "to" ++ addrs "cc") else #[]
  let cc := others.foldl (fun (acc : Array Address) a =>
    if mine a || (to ++ acc).any (·.addr.toLower == a.addr.toLower) then acc else acc.push a) #[]
  let m := parseMessage raw
  let who := if (addrs "from").isEmpty then "someone" else
    let a := (addrs "from")[0]!
    if a.name.isEmpty then a.addr else a.name
  let quoted := (m.text.splitOn "\n").map fun l => if l.startsWith ">" then ">" ++ l else "> " ++ l
  let date := (hs.get? "date").getD ""
  let intro := if date.isEmpty then s!"{who} wrote:" else s!"On {date}, {who} wrote:"
  { to := to.map Address.format, cc := cc.map Address.format
    subject := replySubject m.subject
    body := "\n\n" ++ intro ++ "\n" ++ "\n".intercalate quoted }

end Angelia.Mail
