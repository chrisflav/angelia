import Angelia.Util
import Angelia.Model

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
def base64Decode (s : String) : ByteArray :=
  -- A fold rather than a loop over `s.toList`, which would hold a list cell per character, and
  -- an attachment can be tens of megabytes. The state: output, bit buffer, bits in it, done.
  let start :=
    (ByteArray.emptyWithCapacity (s.utf8ByteSize * 3 / 4), (0 : UInt32), (0 : UInt32), false)
  let (out, _, _, _) := s.foldl (fun (st : ByteArray × UInt32 × UInt32 × Bool) c =>
    let (out, acc, bits, done) := st
    if done then st
    else if c == '=' then (out, acc, bits, true)
    else match b64Value c with
      | none => st
      | some v =>
        let acc := ((acc <<< 6) ||| v.toUInt32) &&& 0xFFFFFF
        if bits + 6 ≥ 8 then
          (out.push ((acc >>> (bits - 2)) &&& 0xFF).toUInt8, acc, bits - 2, false)
        else (out, acc, bits + 6, false)) start
  out

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

/-- The value of attribute `name` in the inside of a tag (`a href="…" class=…`), if present. -/
def tagAttr (tag name : String) : Option String := do
  let lower := tag.toLower
  let parts := lower.splitOn s!"{name}="
  if parts.length < 2 then none
  -- The position in the original, so the value keeps its case.
  let start := (parts.headD "").length + name.length + 1
  let rest := (tag.drop start).toString
  match rest.front with
  | '"' => some ((rest.drop 1).takeWhile (· != '"')).toString
  | '\'' => some ((rest.drop 1).takeWhile (· != '\'')).toString
  | _ => some (rest.takeWhile (fun c => !c.isWhitespace && c != '>')).toString

/-- A small HTML-to-text pass for messages that only come as HTML. Tags go, block ends become
    line breaks, `<blockquote>` becomes `> `-prefixed lines (so a quoted reply looks like one in a
    plain-text mail), list items get a `- `, and a link keeps its target as `[text](url)` -- the
    one piece of Markdown the reader renders in mail. `<style>` and `<script>` blocks are dropped
    and entities resolved. -/
partial def htmlToText (html : String) : String := Id.run do
  let s := dropBlocks (dropBlocks (dropBlocks html "style") "script") "head"
  let cs := s.toList.toArray
  let mut out : Array Char := #[]
  let mut depth := 0
  let mut link : Option (String × Nat) := none
  let mut i := 0
  let newline (out : Array Char) (depth : Nat) : Array Char :=
    (out.push '\n') ++ (List.replicate depth "> ".toList).flatten.toArray
  while i < cs.size do
    let c := cs[i]!
    if c != '<' then
      out := out.push (if c == '\n' || c == '\r' || c == '\t' then ' ' else c)
      i := i + 1
      continue
    let mut j := i + 1
    while j < cs.size && cs[j]! != '>' do j := j + 1
    let tag := String.ofList (cs.extract (i + 1) j).toList
    i := j + 1
    let name := (tag.takeWhile (fun c => c.isAlphanum || c == '/')).toString.toLower
    match name with
    | "br" | "p" | "/p" | "div" | "/div" | "/tr" | "/h1" | "/h2" | "/h3" | "/h4" | "/table"
    | "hr" | "/ul" | "/ol" => out := newline out depth
    | "li" => out := newline out depth ++ "- ".toList.toArray
    | "blockquote" => depth := depth + 1; out := newline out depth
    | "/blockquote" => depth := depth - 1; out := newline out depth
    | "a" => link := (tagAttr tag "href").map (·.trimAscii.toString, out.size)
    | "/a" =>
      if let some (href, start) := link then
        let text := String.ofList (out.extract start out.size).toList |>.trimAscii |>.toString
        let usable := href.startsWith "http://" || href.startsWith "https://" ||
          href.startsWith "mailto:"
        if usable && !text.isEmpty && text != href then
          out := (out.extract 0 start) ++ s!"[{text}]({href})".toList.toArray
        else if usable && text.isEmpty then
          out := out ++ href.toList.toArray
      link := none
    | _ => pure ()
  return collapseBlankLines (decodeEntities (String.ofList out.toList))
where
  dropBlocks (s tag : String) : String :=
    match s.splitOn s!"<{tag}" with
    | [] => s
    | first :: rest => first ++ String.join (rest.map fun chunk =>
        match chunk.splitOn s!"</{tag}>" with
        | _ :: after@(_ :: _) => s!"</{tag}>".intercalate after
        | _ => "")
  decodeEntities (s : String) : String :=
    let named := [("&nbsp;", " "), ("&lt;", "<"), ("&gt;", ">"), ("&quot;", "\""), ("&#39;", "'"),
      ("&apos;", "'"), ("&euro;", "€"), ("&ndash;", "–"), ("&mdash;", "—"), ("&hellip;", "…"),
      ("&rsquo;", "’"), ("&lsquo;", "‘"), ("&rdquo;", "”"), ("&ldquo;", "“"), ("&shy;", ""),
      ("&zwnj;", ""), ("&auml;", "ä"), ("&ouml;", "ö"), ("&uuml;", "ü"), ("&Auml;", "Ä"),
      ("&Ouml;", "Ö"), ("&Uuml;", "Ü"), ("&szlig;", "ß")]
    let s := named.foldl (fun acc (e, r) => acc.replace e r) s
    numeric s |>.replace "&amp;" "&"
  /-- `&#8212;` and `&#x2014;`. -/
  numeric (s : String) : String :=
    match s.splitOn "&#" with
    | [] => s
    | first :: rest => first ++ String.join (rest.map fun chunk =>
        let (num, after) := (chunk.takeWhile (· != ';'), chunk.dropWhile (· != ';'))
        let n := if num.startsWith "x" || num.startsWith "X" then
            (num.drop 1).toString.toList.foldl (fun acc c =>
              acc.bind fun a => (if c.isDigit then some (c.toNat - '0'.toNat)
                else if 'a' ≤ c.toLower && c.toLower ≤ 'f' then
                  some (c.toLower.toNat - 'a'.toNat + 10)
                else none).map (a * 16 + ·)) (some 0)
          else num.toString.toNat?
        match n, after.toString.startsWith ";" with
        | some n, true => (Char.ofNat n).toString ++ (after.drop 1).toString
        | _, _ => "&#" ++ chunk)
  collapseBlankLines (s : String) : String :=
    let lines := (s.splitOn "\n").map (·.trimAscii.toString)
    let blank (l : String) := l.isEmpty || l.all (fun c => c == '>' || c == ' ')
    let kept := lines.foldl (fun (acc : List String) l =>
      if blank l && (acc.head?.map blank |>.getD true) then acc else l :: acc) []
    "\n".intercalate kept.reverse |>.trimAscii.toString

/-- The parts between `--boundary` delimiter lines, excluding preamble and epilogue, and whether
    the closing `--boundary--` was there: a message cut off in the middle has its last part
    without one. The line break before a delimiter belongs to the delimiter (RFC 2046 §5.1.1),
    so a part keeps no trailing CR -- which matters for a binary part. -/
def splitMultipart (body boundary : String) : List String × Bool :=
  let delim := "--" ++ boundary
  let lines := body.splitOn "\n"
  let join (cur : List String) : String :=
    let s := "\n".intercalate cur.reverse
    if s.endsWith "\r" then (s.dropEnd 1).toString else s
  let step (st : Bool × List String × List String × Bool) (line : String) :=
    let (inPart, parts, cur, done) := st
    if done then st else
    let l := if line.endsWith "\r" then (line.dropEnd 1).toString else line
    if l == delim ++ "--" then
      (false, (if inPart then join cur :: parts else parts), [], true)
    else if l == delim then
      (true, (if inPart then join cur :: parts else parts), [], false)
    else if inPart then (inPart, parts, line :: cur, false)
    else st
  let (_, parts, cur, done) := lines.foldl step (false, [], [], false)
  let parts := if !cur.isEmpty then join cur :: parts else parts
  (parts.reverse, done)

/-- A body part's header fields and body. -/
def splitPart (p : String) : Headers × String :=
  -- A part with no header fields starts directly with the blank line.
  if p.startsWith "\r\n" || p.startsWith "\n" then
    (#[], (p.dropWhile (· == '\r')).drop 1 |>.toString)
  else
    let (h, b) := splitHeaderBody p
    (parseHeaders h, b)

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
      let parts := (splitMultipart body boundary).1.map splitPart
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

/-! ## Attachments -/

/-- Undo `%XX` escapes (RFC 2231's extended values); anything else is kept as its byte. -/
def percentDecode (s : String) : ByteArray :=
  go s.toList ByteArray.empty
where
  go : List Char → ByteArray → ByteArray
    | [], out => out
    | '%' :: a :: b :: rest, out =>
      match hexValue a, hexValue b with
      | some x, some y => go rest (out.push (UInt8.ofNat (x * 16 + y)))
      | _, _ => go (a :: b :: rest) (out.push '%'.toNat.toUInt8)
    | c :: rest, out => go rest (out ++ toBytes c.toString)

/-- A parameter's value, decoded. RFC 2231 first -- `name*=utf-8''%C3%A4.pdf`, or split into
    `name*0*`, `name*1`, ... -- else the plain `name`, with RFC 2047 encoded words decoded, which
    is not what the standard allows in a parameter but what most mail programs send. -/
def paramValue (ct : ContentType) (name : String) : Option String :=
  if let some v := ct.param? (name ++ "*") then some (extended v)
  else
    let pieces := (List.range 64).map fun i =>
      ((ct.param? s!"{name}*{i}*").map (·, true)).orElse fun _ =>
        (ct.param? s!"{name}*{i}").map (·, false)
    let pieces := pieces.takeWhile Option.isSome |>.filterMap id
    match pieces with
    | [] => (ct.param? name).map decodeHeader
    | (first, encoded) :: rest =>
      -- Only the first piece may say the charset, and only if it is an encoded one.
      let (charset, first) := if encoded then charsetOf first else (none, first)
      let bytes := ((first, encoded) :: rest).foldl (fun acc (v, enc) =>
        acc ++ (if enc then percentDecode v else toBytes v)) ByteArray.empty
      match charset with
      | some cs => some (decodeCharset cs bytes)
      | none => some (decodeHeader (latin1 bytes))
where
  /-- `charset'language'value` -> the charset (if given) and the value. -/
  charsetOf (v : String) : Option String × String :=
    match v.splitOn "'" with
    | cs :: _ :: rest@(_ :: _) => (if cs.isEmpty then none else some cs, "'".intercalate rest)
    | _ => (none, v)
  extended (v : String) : String :=
    let (cs, value) := charsetOf v
    decodeCharset (cs.getD "utf-8") (percentDecode value)

/-- A file name as a sender gave it, made safe to show and to save under: no directories, no
    control characters. -/
def cleanFileName (name : String) : Option String :=
  let base := ((name.splitOn "/").getLast!.splitOn "\\").getLast!
  let base := String.ofList (base.toList.filter fun c => c.toNat ≥ 0x20 && c.toNat != 0x7F)
  let base := base.trimAscii.toString
  if base.isEmpty || base == "." || base == ".." then none else some base

/-- A leaf part that is an attachment, with what it takes to decode it. -/
structure AttachmentPart where
  info : Attachment
  encoding : String
  body : String

/-- The decoded size of a part's body, without decoding it where that can be avoided. -/
def decodedSize (encoding body : String) : Nat :=
  match encoding.toLower.trimAscii.toString with
  | "base64" =>
    -- Four characters of the alphabet per three bytes; `=` padding is not in it.
    (body.foldl (fun n c => if c != '=' && (b64Value c).isSome then n + 1 else n) 0) * 3 / 4
  | "quoted-printable" => (quotedPrintableDecode body).size
  | _ => body.length

/-- The attachments of a MIME entity, in the order they appear: every leaf that is not the text
    of the message. That is a part sent as an attachment, or one with a file name, or one that is
    neither plain text nor HTML -- an inline image, a calendar invitation, a forwarded message.
    `partial` is set on the last part of a multipart that never closed, which is where a message
    that was cut off ends; whether it *was* cut off only the caller knows. -/
partial def attachmentParts (hs : Headers) (body : String) (unclosed : Bool := true)
    (depth : Nat := 8) : Array AttachmentPart :=
  let ct := parseContentType ((hs.get? "content-type").getD "text/plain")
  if ct.mime.startsWith "multipart/" then
    if depth == 0 then #[] else
    match ct.param? "boundary" with
    | none => #[]
    | some boundary =>
      let (parts, closed) := splitMultipart body boundary
      let n := parts.length
      (parts.toArray.mapIdx fun i p =>
        let (h, b) := splitPart p
        attachmentParts h b (!closed && i + 1 == n) (depth - 1)).flatten
  else
    let disposition := parseContentType ((hs.get? "content-disposition").getD "inline")
    let name := ((paramValue disposition "filename").orElse fun _ => paramValue ct "name")
      |>.bind cleanFileName
    let text := ct.mime == "text/plain" || ct.mime == "text/html"
    if text && disposition.mime != "attachment" && name.isNone then #[] else
    let encoding := (hs.get? "content-transfer-encoding").getD "7bit"
    #[{ info := { name := name.getD "", mime := ct.mime, size := decodedSize encoding body
                  «partial» := unclosed }
        encoding, body }]

/-- The attachments of a message, given its headers and body, with the unnamed ones named by their
    position. -/
def namedAttachments (hs : Headers) (body : String) : Array AttachmentPart :=
  (attachmentParts hs body).mapIdx fun i p =>
    if !p.info.name.isEmpty then p else
    let ext := match p.info.mime with
      | "message/rfc822" => ".eml"
      | "text/calendar" => ".ics"
      | _ => ""
    { p with info := { p.info with name := s!"attachment-{i + 1}{ext}" } }

/-- The attachments of a raw message. -/
def messageAttachments (raw : String) : Array AttachmentPart :=
  let (block, body) := splitHeaderBody raw
  namedAttachments (parseHeaders block) body

/-- Attachment `i` of a raw message and its decoded content. -/
def attachmentAt (raw : String) (i : Nat) : Option (Attachment × ByteArray) := do
  let p ← (messageAttachments raw)[i]?
  return (p.info, decodeTransfer p.encoding p.body)

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
  /-- `partial` marks the last part of a multipart that never closed; see `attachmentParts`. -/
  attachments : Array Attachment := #[]
deriving Repr, Inhabited

/-- The `<…>` message ids in a header value, in order. -/
def messageIds (v : String) : List String :=
  (v.splitOn "<").drop 1 |>.filterMap fun chunk =>
    match chunk.splitOn ">" with
    | id :: _ :: _ => if id.isEmpty then none else some id
    | _ => none

/-- The `Message-ID` of a raw message, from its header alone. -/
def messageIdOf (raw : String) : Option String :=
  (messageIds (((parseHeaders (splitHeaderBody raw).1).get? "message-id").getD "")).head?

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
    text := (extractText hs body).getD ""
    attachments := (namedAttachments hs body).map (·.info) }

end Angelia.Mail