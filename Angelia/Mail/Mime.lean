import Angelia.Util

/-!
# Internet message parsing

Just enough of RFC 5322, MIME (RFC 2045/2046) and encoded words (RFC 2047) to turn a raw message
into the handful of fields a notification needs: who sent it, what it is about, when, which thread
it belongs to, and a readable text body.

Everything here is pure. The raw message is held as a *byte string*: a `String` whose characters
are exactly the message's bytes (see `Angelia.latin1`), so splitting on headers and boundaries never
has to care about the character set, and each part is decoded to real text only once its transfer
encoding and charset are known.
-/

namespace Angelia.Mail

/-! ## Transfer encodings -/

private def b64Value (c : Char) : Option Nat :=
  if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat + 52)
  else if c == '+' || c == '-' then some 62
  else if c == '/' || c == '_' then some 63
  else none

/-- Decode base64, skipping whitespace and anything else outside the alphabet (as RFC 2045
    requires of a decoder). Accepts the URL-safe alphabet too, which GitHub uses. -/
def base64Decode (s : String) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut acc : Nat := 0
  let mut bits : Nat := 0
  for c in s.toList do
    if c == '=' then break
    match b64Value c with
    | none => pure ()
    | some v =>
      acc := (acc <<< 6 ||| v) &&& 0xFFFFFF
      bits := bits + 6
      if bits ≥ 8 then
        bits := bits - 8
        out := out.push (UInt8.ofNat ((acc >>> bits) &&& 0xFF))
  return out

private def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Decode quoted-printable. With `header := true` this is RFC 2047's "Q" encoding, where `_`
    stands for a space. A malformed escape is kept literally rather than dropped. -/
def quotedPrintableDecode (s : String) (header : Bool := false) : ByteArray :=
  go s.toList ByteArray.empty
where
  go : List Char → ByteArray → ByteArray
    | [], out => out
    | '=' :: '\r' :: '\n' :: rest, out => go rest out
    | '=' :: '\n' :: rest, out => go rest out
    | '=' :: a :: b :: rest, out =>
      match hexValue a, hexValue b with
      | some x, some y => go rest (out.push (UInt8.ofNat (x * 16 + y)))
      | _, _ => go (a :: b :: rest) (out.push '='.toNat.toUInt8)
    | '_' :: rest, out => go rest (out.push (if header then 0x20 else '_'.toNat.toUInt8))
    | c :: rest, out => go rest (pushChar out c)
  /-- Append a character of the byte string as the byte it stands for. -/
  pushChar (out : ByteArray) (c : Char) : ByteArray :=
    if c.toNat < 256 then out.push c.toNat.toUInt8 else out ++ c.toString.toUTF8

/-! ## Character sets -/

/-- Code points of windows-1252's 0x80–0x9F block, which mail labelled ISO-8859-1 very often
    actually uses. Unassigned positions map to themselves. -/
private def cp1252High : Array Nat := #[
  0x20AC, 0x81, 0x201A, 0x0192, 0x201E, 0x2026, 0x2020, 0x2021, 0x02C6, 0x2030, 0x0160, 0x2039,
  0x0152, 0x8D, 0x017D, 0x8F, 0x90, 0x2018, 0x2019, 0x201C, 0x201D, 0x2022, 0x2013, 0x2014,
  0x02DC, 0x2122, 0x0161, 0x203A, 0x0153, 0x9D, 0x017E, 0x0178]

/-- Decode bytes in the named charset. UTF-8 and the Latin-1 family are decoded exactly; anything
    else is tried as UTF-8 and falls back to Latin-1, which never fails and keeps ASCII intact. -/
def decodeCharset (charset : String) (b : ByteArray) : String :=
  let cs := charset.toLower
  let latin := cs == "iso-8859-1" || cs == "latin1" || cs == "us-ascii" || cs == "ascii"
    || cs == "windows-1252" || cs == "cp1252" || cs == "iso-8859-15"
  if latin then
    String.ofList (b.toList.map fun x =>
      let n := x.toNat
      if 0x80 ≤ n && n < 0xA0 then Char.ofNat (cp1252High[n - 0x80]!) else Char.ofNat n)
  else
    (String.fromUTF8? b).getD (latin1 b)

/-! ## Encoded words (RFC 2047) -/

/-- Decode one `=?charset?enc?text?=` word, given the three inner fields. -/
private def decodeWord (charset enc text : String) : Option String :=
  -- RFC 2231 allows a language suffix: `utf-8*en`.
  let charset := (charset.splitOn "*").headD charset
  match enc.toUpper with
  | "B" => some (decodeCharset charset (base64Decode text))
  | "Q" => some (decodeCharset charset (quotedPrintableDecode text (header := true)))
  | _ => none

/-- Try to read an encoded word at the start of `cs` (which begins after `=?`). Returns the decoded
    text and the remaining input. -/
private def readWord (cs : List Char) : Option (String × List Char) := do
  let (charset, r1) ← takeUntil '?' cs
  let (enc, r2) ← takeUntil '?' r1
  let (text, r3) ← takeUntil '?' r2
  match r3 with
  | '=' :: rest => return (← decodeWord (String.ofList charset) (String.ofList enc) (String.ofList text), rest)
  | _ => none
where
  takeUntil (stop : Char) (cs : List Char) : Option (List Char × List Char) :=
    match cs.span (· != stop) with
    | (pre, _ :: post) => if pre.any (fun c => c == ' ' || c == '\n') then none else some (pre, post)
    | (_, []) => none

/-- Decode every encoded word in a header value. Whitespace *between* two encoded words is dropped
    (RFC 2047 §6.2); everything else passes through, with raw 8-bit bytes read as UTF-8 if they
    form valid UTF-8, since that is what non-conforming senders mean by them. -/
partial def decodeHeader (value : String) : String :=
  go value.toList [] false
where
  go : List Char → List String → Bool → String
    | [], acc, _ => String.join acc.reverse
    | '=' :: '?' :: rest, acc, prevWord =>
      match readWord rest with
      | some (decoded, rest') =>
        -- Drop the whitespace-only run that separated this word from the previous one.
        let acc := if prevWord then
            match acc with
            | ws :: acc' => if ws.toList.all Char.isWhitespace then acc' else acc
            | [] => acc
          else acc
        go rest' (decoded :: acc) true
      | none => go rest ("=?" :: acc) false
    | c :: rest, acc, prevWord =>
      if c.isWhitespace then
        let (ws, rest') := (c :: rest).span Char.isWhitespace
        go rest' (String.ofList ws :: acc) prevWord
      else
        let (plain, rest') := rest.span (fun d => !d.isWhitespace && d != '=')
        go rest' (rawText (String.ofList (c :: plain)) :: acc) false
  rawText (s : String) : String :=
    if s.toList.all (·.toNat < 128) then s else decodeCharset "utf-8" (toBytes s)

/-! ## Headers -/

/-- A message's header fields, names lowercased, in order. -/
abbrev Headers := Array (String × String)

/-- The first value of a header field. -/
def Headers.get? (hs : Headers) (name : String) : Option String :=
  hs.find? (·.1 == name.toLower) |>.map (·.2)

/-- Split a byte string into its header block and body at the first empty line. -/
def splitHeaderBody (raw : String) : String × String :=
  match raw.splitOn "\r\n\r\n" with
  | h :: rest@(_ :: _) => (h, "\r\n\r\n".intercalate rest)
  | _ =>
    match raw.splitOn "\n\n" with
    | h :: rest@(_ :: _) => (h, "\n\n".intercalate rest)
    | _ => (raw, "")

/-- Parse a header block: unfold continuation lines and split each field at its first colon. -/
def parseHeaders (block : String) : Headers := Id.run do
  let lines := (block.splitOn "\n").map fun l => if l.endsWith "\r" then (l.dropEnd 1).toString else l
  let mut fields : Array String := #[]
  for line in lines do
    if line.startsWith " " || line.startsWith "\t" then
      if let some last := fields.back? then
        fields := fields.pop.push (last ++ " " ++ line.trimAscii.toString)
    else if !line.isEmpty then
      fields := fields.push line
  let mut out : Headers := #[]
  for f in fields do
    match f.splitOn ":" with
    | name :: rest@(_ :: _) =>
      out := out.push (name.trimAscii.toString.toLower, (":".intercalate rest).trimAscii.toString)
    | _ => pure ()
  return out

/-- A parsed `Content-Type` (or `Content-Disposition`): the lowercased value and its parameters,
    with parameter names lowercased and quotes removed. -/
structure ContentType where
  mime : String
  params : List (String × String)
deriving Repr, Inhabited

def ContentType.param? (ct : ContentType) (name : String) : Option String :=
  ct.params.lookup name

/-- Split on `;` outside double quotes. -/
private def splitParams (s : String) : List String :=
  go s.toList [] [] false
where
  go : List Char → List Char → List String → Bool → List String
    | [], cur, acc, _ => (String.ofList cur.reverse :: acc).reverse
    | '"' :: rest, cur, acc, q => go rest ('"' :: cur) acc (!q)
    | ';' :: rest, cur, acc, false => go rest [] (String.ofList cur.reverse :: acc) false
    | c :: rest, cur, acc, q => go rest (c :: cur) acc q

def parseContentType (value : String) : ContentType :=
  match splitParams value with
  | [] => { mime := "text/plain", params := [] }
  | mime :: params =>
    let params := params.filterMap fun p =>
      match p.splitOn "=" with
      | k :: v@(_ :: _) =>
        let v := ("=".intercalate v).trimAscii.toString
        let v := if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
          ((v.drop 1).dropEnd 1).toString else v
        some (k.trimAscii.toString.toLower, v)
      | _ => none
    { mime := mime.trimAscii.toString.toLower, params }

/-! ## Bodies -/

/-- Undo a part's `Content-Transfer-Encoding`. -/
def decodeTransfer (encoding : String) (body : String) : ByteArray :=
  match encoding.toLower.trimAscii.toString with
  | "base64" => base64Decode body
  | "quoted-printable" => quotedPrintableDecode body
  | _ => toBytes body

/-- A very small HTML-to-text pass for messages that only come as HTML: drop `<style>`/`<script>`
    blocks and tags, turn block ends into newlines, and resolve the common entities. -/
partial def htmlToText (html : String) : String :=
  let s := dropBlocks (dropBlocks html "style") "script"
  let text := go s.toList [] false
  collapseBlankLines (decodeEntities text)
where
  dropBlocks (s tag : String) : String :=
    match s.splitOn s!"<{tag}" with
    | [] => s
    | first :: rest => first ++ String.join (rest.map fun chunk =>
        match chunk.splitOn s!"</{tag}>" with
        | _ :: after@(_ :: _) => s!"</{tag}>".intercalate after
        | _ => "")
  go : List Char → List Char → Bool → String
    | [], acc, _ => String.ofList acc.reverse
    | '<' :: rest, acc, _ =>
      let (tag, rest') := rest.span (· != '>')
      let name := (String.ofList (tag.takeWhile (fun c => c.isAlphanum || c == '/'))).toLower
      let block := ["br", "/p", "p", "/div", "/tr", "/li", "/h1", "/h2", "/h3", "/table"].contains name
      go (rest'.drop 1) (if block then '\n' :: acc else acc) true
    | c :: rest, acc, inTag => go rest (c :: acc) inTag
  decodeEntities (s : String) : String :=
    [("&nbsp;", " "), ("&lt;", "<"), ("&gt;", ">"), ("&quot;", "\""), ("&#39;", "'"),
      ("&apos;", "'"), ("&euro;", "€"), ("&amp;", "&")].foldl (fun acc (e, r) => acc.replace e r) s
  collapseBlankLines (s : String) : String :=
    let lines := (s.splitOn "\n").map (·.trimAscii.toString)
    let kept := lines.foldl (fun (acc : List String) l =>
      if l.isEmpty && (acc.head?.map String.isEmpty |>.getD true) then acc else l :: acc) []
    "\n".intercalate kept.reverse |>.trimAscii.toString

/-- The readable text of a MIME entity, given its headers and (byte-string) body: the first
    `text/plain` leaf, else the first `text/html` leaf converted to text. Returns `none` if the
    entity has neither. Nested multiparts are searched depth-first, at most `depth` levels. -/
partial def extractText (hs : Headers) (body : String) (depth : Nat := 8) : Option String :=
  let ct := parseContentType ((hs.get? "content-type").getD "text/plain")
  let enc := (hs.get? "content-transfer-encoding").getD "7bit"
  let disposition := parseContentType ((hs.get? "content-disposition").getD "inline")
  if disposition.mime == "attachment" then none
  else if ct.mime.startsWith "multipart/" then
    if depth == 0 then none else
    match ct.param? "boundary" with
    | none => none
    | some boundary =>
      let parts := splitMultipart body boundary |>.map fun p =>
        let (h, b) := splitHeaderBody p
        -- A part with no header fields starts directly with the blank line.
        let (h, b) := if p.startsWith "\r\n" || p.startsWith "\n" then ("", (p.dropWhile (· == '\r')).drop 1 |>.toString) else (h, b)
        (parseHeaders h, b)
      let plain := parts.findSome? fun (h, b) =>
        let pct := parseContentType ((h.get? "content-type").getD "text/plain")
        if pct.mime == "text/plain" || pct.mime.startsWith "multipart/" then
          (extractText h b (depth - 1)).filter (!·.isEmpty) else none
      plain.orElse fun _ => parts.findSome? fun (h, b) => extractText h b (depth - 1)
  else if ct.mime == "text/plain" || ct.mime == "text/html" then
    let text := decodeCharset ((ct.param? "charset").getD "us-ascii") (decodeTransfer enc body)
    let text := text.replace "\r\n" "\n"
    some (if ct.mime == "text/html" then htmlToText text else text.trimAscii.toString)
  else none
where
  /-- The parts between `--boundary` delimiter lines, excluding preamble and epilogue. -/
  splitMultipart (body boundary : String) : List String :=
    let delim := "--" ++ boundary
    let lines := body.splitOn "\n"
    let (_, parts, cur, _) := lines.foldl (fun (st : Bool × List String × List String × Bool) line =>
      let (inPart, parts, cur, done) := st
      if done then st else
      let l := if line.endsWith "\r" then (line.dropEnd 1).toString else line
      if l == delim ++ "--" then
        (false, (if inPart then ("\n".intercalate cur.reverse) :: parts else parts), [], true)
      else if l == delim then
        (true, (if inPart then ("\n".intercalate cur.reverse) :: parts else parts), [], false)
      else if inPart then (inPart, parts, line :: cur, false)
      else st) (false, [], [], false)
    let parts := if !cur.isEmpty then ("\n".intercalate cur.reverse) :: parts else parts
    parts.reverse

/-! ## Addresses and dates -/

/-- The display part of an address: `"Jane Doe" <jane@x>` → `Jane Doe`, `jane@x` → `jane@x`. -/
def displayName (addr : String) : String :=
  match addr.splitOn "<" with
  | name :: _ :: _ =>
    let n := name.trimAscii.toString
    let n := if n.startsWith "\"" && n.endsWith "\"" && n.length ≥ 2 then ((n.drop 1).dropEnd 1).toString else n
    if n.isEmpty then (addr.splitOn "<").getLast!.replace ">" "" |>.trimAscii.toString else n
  | _ => addr.trimAscii.toString

private def months : List String :=
  ["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"]

/-- Parse an RFC 5322 date (`Tue, 1 Jul 2003 10:52:37 +0200`, day name and seconds optional) into
    Unix seconds. Obsolete zone names other than `UT`/`GMT`/`Z` are read as UTC. -/
def parseDate (s : String) : Option Int := do
  let s := (s.splitOn "(").headD s
  let toks := (s.replace "," " ").splitOn " " |>.filter (!·.isEmpty)
  let toks := match toks with
    | t :: rest => if t.toNat?.isNone && t.length == 3 && (months.idxOf? t.toLower).isNone then rest else toks
    | [] => []
  match toks with
  | d :: mon :: y :: time :: rest =>
    let day ← d.toNat?
    let month := (← months.idxOf? (mon.toLower.take 3).toString) + 1
    let year ← y.toNat?
    let year := if year < 50 then year + 2000 else if year < 1000 then year + 1900 else year
    let hms := time.splitOn ":" |>.map String.toNat?
    let (hh, mm, ss) ← match hms with
      | [some h, some m] => some (h, m, 0)
      | [some h, some m, some sec] => some (h, m, sec)
      | _ => none
    let offset : Int := match rest.head? with
      | some z =>
        if (z.startsWith "+" || z.startsWith "-") && z.length == 5 then
          let n := ((z.drop 1).toString.toNat?).getD 0
          let mins : Int := (n / 100) * 60 + n % 100
          if z.startsWith "-" then -mins else mins
        else 0
      | none => 0
    return daysFromCivil year month day * 86400 + hh * 3600 + mm * 60 + ss - offset * 60
  | _ => none

/-! ## Messages -/

/-- What a notification needs from an e-mail. -/
structure Message where
  messageId : Option String
  subject : String
  «from» : String
  to : String
  date : Option Int
  /-- The thread root: the first `References` id, else `In-Reply-To`, else the message itself. -/
  threadKey : Option String
  text : String
deriving Repr, Inhabited

/-- The `<…>` message ids in a header value, in order. -/
def messageIds (v : String) : List String :=
  (v.splitOn "<").drop 1 |>.filterMap fun chunk =>
    match chunk.splitOn ">" with
    | id :: _ :: _ => if id.isEmpty then none else some id
    | _ => none

/-- Parse a raw message (a byte string). -/
def parseMessage (raw : String) : Message :=
  let (block, body) := splitHeaderBody raw
  let hs := parseHeaders block
  let hdr (n : String) := decodeHeader ((hs.get? n).getD "")
  let messageId := (messageIds ((hs.get? "message-id").getD "")).head?
  let threadKey := (messageIds ((hs.get? "references").getD "")).head?
    |>.orElse (fun _ => (messageIds ((hs.get? "in-reply-to").getD "")).head?)
    |>.orElse (fun _ => messageId)
  { messageId
    subject := hdr "subject"
    «from» := hdr "from"
    to := hdr "to"
    date := (hs.get? "date").bind parseDate
    threadKey
    text := (extractText hs body).getD "" }

end Angelia.Mail