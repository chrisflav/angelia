import Angelia.Util

/-!
# IMAP4rev1 responses

The pure half of the IMAP client: turning the server's responses into values. A response is a
line of text that may carry *literals* — `{n}` at the end of a line announces that `n` raw bytes
follow, after which the line continues. The transport (`Angelia.Imap.Client`) reads those bytes
exactly and hands the parser the pieces; everything here is a function of them, so it is tested
against recorded server output.

All text is held as byte strings (`Angelia.latin1`).
-/

namespace Angelia.Imap

/-- One piece of a response as read off the wire. -/
inductive Piece where
  | text (s : String)
  | literal (s : String)
deriving Repr, Inhabited, BEq

/-- A complete server response. -/
abbrev Response := Array Piece

/-- A parsed value: the s-expression-like syntax of IMAP data. -/
inductive Value where
  | atom (s : String)
  | str (s : String)
  | list (vs : Array Value)
  | nil
deriving Repr, Inhabited, BEq

namespace Value

/-- The text of an atom or string. -/
def text? : Value → Option String
  | .atom s | .str s => some s
  | _ => none

def nat? (v : Value) : Option Nat := v.text? >>= String.toNat?

def list? : Value → Option (Array Value)
  | .list vs => some vs
  | _ => none

end Value

/-- If a text line ends with a literal announcement `{n}` or `{n+}`, the byte count. -/
def literalSize? (line : String) : Option Nat := do
  guard (line.endsWith "}")
  let open_ := (line.splitOn "{").getLast?
  let inner ← open_
  let inner := (inner.dropEnd 1).toString
  let inner := if inner.endsWith "+" then (inner.dropEnd 1).toString else inner
  inner.toNat?

private inductive Item where
  | ch (c : Char)
  | lit (s : String)

/-- Flatten pieces to items, replacing each `{n}` announcement by the literal it announced. -/
private def items (r : Response) : List Item :=
  r.toList.flatMap fun
    | .text s =>
      let s := if (literalSize? s).isSome then
          String.intercalate "{" ((s.splitOn "{").dropLast) else s
      s.toList.map .ch
    | .literal s => [.lit s]

/-- Parse a sequence of values. Unknown syntax degrades to atoms rather than failing, because a
    server-specific extension in one response must not stop the client. -/
partial def parseValues (r : Response) : Array Value :=
  (go (items r) #[]).1
where
  go : List Item → Array Value → Array Value × List Item
    | [], acc => (acc, [])
    | .ch ' ' :: rest, acc => go rest acc
    | .ch ')' :: rest, acc => (acc, rest)
    | .ch '(' :: rest, acc =>
      let (inner, rest') := go rest #[]
      go rest' (acc.push (.list inner))
    | .ch '"' :: rest, acc =>
      let (s, rest') := quoted rest []
      go rest' (acc.push (.str s))
    | .lit s :: rest, acc => go rest (acc.push (.str s))
    | items@(.ch _ :: _), acc =>
      let (a, rest') := atom items [] 0
      go rest' (acc.push (if a == "NIL" then .nil else .atom a))
  quoted : List Item → List Char → String × List Item
    | .ch '\\' :: .ch c :: rest, acc => quoted rest (c :: acc)
    | .ch '"' :: rest, acc => (String.ofList acc.reverse, rest)
    | .ch c :: rest, acc => quoted rest (c :: acc)
    | .lit s :: rest, acc => quoted rest (s.toList.reverse ++ acc)
    | [], acc => (String.ofList acc.reverse, [])
  /-- An atom runs to a space or parenthesis — except inside `[...]`, as in
      `BODY[HEADER.FIELDS (FROM)]`, which is one atom. -/
  atom : List Item → List Char → Nat → String × List Item
    | .ch c :: rest, acc, depth =>
      if depth == 0 && (c == ' ' || c == '(' || c == ')') then
        (String.ofList acc.reverse, .ch c :: rest)
      else
        let depth := if c == '[' then depth + 1 else if c == ']' && depth > 0 then depth - 1 else depth
        atom rest (c :: acc) depth
    | rest, acc, _ => (String.ofList acc.reverse, rest)

/-- The first text piece, which carries the tag and status. -/
def Response.head (r : Response) : String :=
  match (r[0]? : Option Piece) with
  | some (.text s) => s
  | _ => ""

/-- Tagged completion: `(tag, status, text)` for `a1 OK done`. -/
def Response.tagged? (r : Response) : Option (String × String × String) :=
  match r.head.splitOn " " with
  | tag :: status :: rest =>
    if tag == "*" || tag == "+" then none else some (tag, status.toUpper, " ".intercalate rest)
  | _ => none

def Response.isContinuation (r : Response) : Bool := r.head.startsWith "+"

/-- An untagged response's values, without the leading `*`. -/
def Response.untagged? (r : Response) : Option (Array Value) :=
  if r.head.startsWith "* " then some ((parseValues r).extract 1) else none

/-- `* n EXISTS`. -/
def Response.exists? (r : Response) : Option Nat := do
  let vs ← r.untagged?
  guard ((vs[1]? >>= Value.text?).map String.toUpper == some "EXISTS")
  (← vs[0]?).nat?

/-- The response code of a status response, e.g. `UIDVALIDITY 3857529045` from
    `* OK [UIDVALIDITY 3857529045] UIDs valid`, as its words. -/
def Response.code? (r : Response) : Option (List String) := do
  let h := r.head
  let afterOpen ← (h.splitOn "[")[1]?
  let inside ← (afterOpen.splitOn "]")[0]?
  return inside.splitOn " "

/-- The value of a numeric response code such as `UIDVALIDITY` or `UIDNEXT`. -/
def Response.codeNat? (r : Response) (name : String) : Option Nat := do
  match ← r.code? with
  | n :: v :: _ => if n.toUpper == name then v.toNat? else none
  | _ => none

/-- Capabilities from `* CAPABILITY ...` or an `OK [CAPABILITY ...]` code. -/
def Response.capabilities? (r : Response) : Option (List String) :=
  match r.code? with
  | some ("CAPABILITY" :: caps) => some (caps.map String.toUpper)
  | _ =>
    match r.head.splitOn " " with
    | "*" :: kw :: caps => if kw.toUpper == "CAPABILITY" then some (caps.map String.toUpper) else none
    | _ => none

/-- A message from a `FETCH` response. -/
structure Fetched where
  seq : Nat
  uid : Option Nat := none
  flags : Array String := #[]
  internalDate : Option String := none
  /-- `BODY[]` (or a partial `BODY[]<0>`), as a byte string. -/
  body : Option String := none
  /-- `RFC822.SIZE`: the whole message's size in bytes. -/
  size : Option Nat := none
deriving Repr, Inhabited

/-- Interpret `* n FETCH (...)`. -/
def Response.fetch? (r : Response) : Option Fetched := do
  let vs ← r.untagged?
  let seq ← (← vs[0]?).nat?
  guard ((vs[1]? >>= Value.text?).map String.toUpper == some "FETCH")
  let items ← (← vs[2]?).list?
  let mut f : Fetched := { seq }
  let mut i := 0
  while h : i + 1 < items.size do
    let key := (items[i].text?.getD "").toUpper
    let v := items[i + 1]
    if key == "UID" then f := { f with uid := v.nat? }
    else if key == "FLAGS" then f := { f with flags := (v.list?.getD #[]).filterMap Value.text? }
    else if key == "INTERNALDATE" then f := { f with internalDate := v.text? }
    else if key == "RFC822.SIZE" then f := { f with size := v.nat? }
    else if key.startsWith "BODY[]" || key == "RFC822" then f := { f with body := v.text? }
    i := i + 2
  return f

/-! ## Encoding commands -/

/-- An IMAP quoted string. Rejects CR/LF, which a quoted string cannot carry. -/
def quote (s : String) : Except String String :=
  if s.toList.any (fun c => c == '\r' || c == '\n') then .error "line break in IMAP string"
  else .ok ("\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\"")

private def b64Chars : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

/-- Standard base64 with padding. -/
def base64Encode (b : ByteArray) : String := Id.run do
  let mut out : Array Char := #[]
  let mut i := 0
  while i < b.size do
    let b0 := b[i]!.toNat
    let b1 := if i + 1 < b.size then b[i + 1]!.toNat else 0
    let b2 := if i + 2 < b.size then b[i + 2]!.toNat else 0
    let n := (b0 <<< 16) ||| (b1 <<< 8) ||| b2
    out := out.push b64Chars[(n >>> 18) &&& 63]!
    out := out.push b64Chars[(n >>> 12) &&& 63]!
    out := out.push (if i + 1 < b.size then b64Chars[(n >>> 6) &&& 63]! else '=')
    out := out.push (if i + 2 < b.size then b64Chars[n &&& 63]! else '=')
    i := i + 3
  return String.ofList out.toList

/-- The SASL PLAIN initial response for `user`/`password` (RFC 4616). -/
def saslPlain (user password : String) : String :=
  base64Encode ((ByteArray.mk #[0]) ++ user.toUTF8 ++ (ByteArray.mk #[0]) ++ password.toUTF8)

/-- The SASL XOAUTH2 initial response (as Gmail and Microsoft 365 define it). -/
def saslXOAuth2 (user accessToken : String) : String :=
  base64Encode s!"user={user}\x01auth=Bearer {accessToken}\x01\x01".toUTF8

/-- RFC 3501 modified UTF-7 for mailbox names, encoding only what needs encoding. Names given in
    plain ASCII pass through unchanged (with `&` escaped as `&-`). -/
def encodeMailbox (name : String) : String := Id.run do
  let mut out := ""
  let mut pending : Array Char := #[]
  let flush (pending : Array Char) : String :=
    if pending.isEmpty then "" else
    -- UTF-16BE, then base64 with `,` for `/` and no padding.
    let bytes := pending.foldl (fun (acc : ByteArray) c =>
      let n := c.toNat
      if n < 0x10000 then acc.push (n >>> 8).toUInt8 |>.push (n &&& 0xFF).toUInt8
      else
        let v := n - 0x10000
        let hi := 0xD800 + (v >>> 10)
        let lo := 0xDC00 + (v &&& 0x3FF)
        acc.push (hi >>> 8).toUInt8 |>.push (hi &&& 0xFF).toUInt8
          |>.push (lo >>> 8).toUInt8 |>.push (lo &&& 0xFF).toUInt8) ByteArray.empty
    let enc := (base64Encode bytes).replace "=" "" |>.replace "/" ","
    "&" ++ enc ++ "-"
  for c in name.toList do
    if c.toNat ≥ 0x20 && c.toNat < 0x7F then
      out := out ++ flush pending
      pending := #[]
      out := out ++ (if c == '&' then "&-" else c.toString)
    else
      pending := pending.push c
  return out ++ flush pending

end Angelia.Imap