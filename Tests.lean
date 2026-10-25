import Angelia

/-!
# Tests

Pure-function tests over recorded or hand-written protocol data. `lake test` runs them.
-/

open Lean Angelia Angelia.Mail Angelia.Imap Angelia.SecondFactor

structure Suite where
  failures : IO.Ref (Array String)

def Suite.check (s : Suite) (name : String) (cond : Bool) (detail : String := "") : IO Unit := do
  if cond then IO.println s!"  ok  {name}"
  else
    IO.println s!"  FAIL {name} {detail}"
    s.failures.modify (·.push name)

def Suite.eq [BEq α] [Repr α] (s : Suite) (name : String) (actual expected : α) : IO Unit :=
  s.check name (actual == expected) s!"\n    expected {repr expected}\n    actual   {repr actual}"

/-- Lines joined with CRLF, as on the wire. -/
def crlf (lines : List String) : String := "\r\n".intercalate lines

def multipartMail : String := crlf [
  "From: =?UTF-8?B?SsO8cmdlbiBNw7xsbGVy?= <jm@example.org>",
  "To: me@example.org",
  "Subject: =?ISO-8859-1?Q?Gr=FC=DFe?= =?ISO-8859-1?Q?_aus_K=F6ln?=",
  "Date: Tue, 20 Oct 2026 14:03:07 +0200",
  "Message-ID: <abc@example.org>",
  "References: <root@example.org> <mid@example.org>",
  "MIME-Version: 1.0",
  "Content-Type: multipart/alternative;",
  " boundary=\"XYZ\"",
  "",
  "preamble",
  "--XYZ",
  "Content-Type: text/plain; charset=utf-8",
  "Content-Transfer-Encoding: quoted-printable",
  "",
  "Hallo Welt, sch=C3=B6n =",
  "hier.",
  "--XYZ",
  "Content-Type: text/html; charset=utf-8",
  "",
  "<p>Hallo</p>",
  "--XYZ--",
  "epilogue"]

def htmlMail : String := crlf [
  "From: Shop <noreply@shop.example>",
  "Subject: Your order",
  "Content-Type: text/html; charset=windows-1252",
  "Content-Transfer-Encoding: base64",
  "",
  "PGh0bWw+PHN0eWxlPnB7Y29sb3I6cmVkfTwvc3R5bGU+PHA+T3JkZXIgJmFtcDsgc2hpcHBpbmc8",
  "L3A+PHA+NSAmZXVybzsgY2hhcmdlZCCAPC9wPjwvaHRtbD4="]

/-- A report with a PDF (RFC 2231 name), a text file (encoded-word name), an inline image in a
    nested `multipart/related`, a forwarded message without a name, and a binary part. -/
def attachmentMail : String := crlf [
  "From: a@example.org",
  "Subject: report",
  "Message-ID: <att@example.org>",
  "Content-Type: multipart/mixed; boundary=\"OUT\"",
  "",
  "--OUT",
  "Content-Type: multipart/related; boundary=\"REL\"",
  "",
  "--REL",
  "Content-Type: text/html; charset=utf-8",
  "",
  "<p>See <img src=\"cid:logo\"></p>",
  "--REL",
  "Content-Type: image/png; name=\"logo.png\"",
  "Content-Transfer-Encoding: base64",
  "Content-ID: <logo>",
  "",
  "iVBORw0K",
  "--REL--",
  "--OUT",
  "Content-Type: application/pdf",
  "Content-Disposition: attachment; filename*=UTF-8''Pr%C3%BCfung%202026.pdf",
  "Content-Transfer-Encoding: base64",
  "",
  "aGVsbG8g",
  "d29ybGQ=",
  "--OUT",
  "Content-Type: text/plain; name=\"=?UTF-8?B?w5xiZXJzaWNodC50eHQ=?=\"",
  "Content-Disposition: attachment",
  "Content-Transfer-Encoding: quoted-printable",
  "",
  "Gr=C3=BC=C3=9Fe",
  "--OUT",
  "Content-Type: message/rfc822",
  "",
  "Subject: inner",
  "",
  "inner body",
  "--OUT",
  "Content-Type: application/octet-stream; name=\"../../bin.dat\"",
  "Content-Transfer-Encoding: binary",
  "",
  "\x00\xff\r",
  "--OUT--",
  ""]

def attachmentTests (s : Suite) : IO Unit := do
  IO.println "attachments"
  let m := parseMessage attachmentMail
  s.eq "the html is the text, not an attachment" m.text "See"
  s.eq "attachment names" (m.attachments.map (·.name))
    #["logo.png", "Prüfung 2026.pdf", "Übersicht.txt", "attachment-4.eml", "bin.dat"]
  s.eq "attachment types" (m.attachments.map (·.mime))
    #["image/png", "application/pdf", "text/plain", "message/rfc822", "application/octet-stream"]
  s.eq "sizes: base64 exact, qp decoded" ((m.attachments.map (·.size)).extract 0 3) #[6, 11, 7]
  s.eq "none partial in a closed message" (m.attachments.map (·.partial)) #[false, false, false, false, false]
  s.eq "pdf content" ((attachmentAt attachmentMail 1).map (·.2.toList)) (some "hello world".toUTF8.toList)
  s.eq "qp content" ((attachmentAt attachmentMail 2).map (fun (_, b) => String.fromUTF8? b))
    (some (some "Grüße"))
  -- The CRLF before a delimiter is the delimiter's; the part's own trailing CR stays.
  s.eq "binary content is exact" ((attachmentAt attachmentMail 4).map (·.2.toList))
    (some [0x00, 0xff, 0x0d])
  s.eq "forwarded message content" ((attachmentAt attachmentMail 3).map (fun (_, b) => latin1 b))
    (some "Subject: inner\r\n\r\ninner body")
  s.eq "no attachment past the last" ((attachmentAt attachmentMail 5).map (·.1.name)) none
  s.eq "rfc 2231 continuations" (paramValue (parseContentType
      "attachment; filename*0*=UTF-8''%C3%A4; filename*1=\"bc.txt\"") "filename") (some "äbc.txt")
  s.eq "plain mail has none" (parseMessage multipartMail).attachments #[]
  s.eq "no directories in a file name" (cleanFileName "C:\\Users\\x\\..\\a.doc") (some "a.doc")
  s.eq "a name of dots is none" (cleanFileName "..") none
  -- Cut off in the middle of the PDF: the PDF is the part that never closed.
  let cut := (attachmentMail.splitOn "d29ybGQ=").headD ""
  let c := parseMessage cut
  s.eq "cut: parts up to the cut" (c.attachments.map (·.name)) #["logo.png", "Prüfung 2026.pdf"]
  s.eq "cut: the last one is marked" (c.attachments.map (·.partial)) #[false, true]
  let normalizeCut (truncated : Bool) :=
    (Connector.ImapSource.normalize (Json.mkObj [("raw", cut), ("truncated", truncated)])).toOption
      |>.map (·.attachments.map (·.partial))
  s.eq "cut and truncated: partial" (normalizeCut true) (some #[false, true])
  s.eq "unclosed but whole (a sloppy sender): not partial" (normalizeCut false) (some #[false, false])
  s.eq "download disposition"
    (Server.downloadDisposition "Prüfung \"1\".pdf")
    "attachment; filename=\"Pr_fung _1_.pdf\"; filename*=UTF-8''Pr%C3%BCfung%20%221%22.pdf"
  IO.println "encodings"
  s.eq "base64 with line breaks" (String.fromUTF8? (base64Decode "aGVs\r\nbG8gd29y\r\nbGQ=")) (some "hello world")
  s.eq "base64, no padding" (base64Decode "aGk").toList "hi".toUTF8.toList
  let bytes := ByteArray.mk #[0, 0x41, 0x80, 0xff, 0x0d, 0x0a]
  s.eq "latin1 round trip" (toBytes (latin1 bytes)).toList bytes.toList

def mimeTests (s : Suite) : IO Unit := do
  s.eq "html: links keep their target"
    (htmlToText "see <a href=\"https://x.org/a?b=1&amp;c=2\" target=_blank>the slides</a>, <a href='https://y.org'>https://y.org</a>")
    "see [the slides](https://x.org/a?b=1&c=2), https://y.org"
  s.eq "html: blockquotes become quoted lines"
    (htmlToText "Fine.<div>On Monday A wrote:</div><blockquote>Sure.<br>Which room?</blockquote>")
    "Fine.\nOn Monday A wrote:\n\n> Sure.\n> Which room?"
  s.eq "html: list items and numeric entities"
    (htmlToText "<ul><li>one</li><li>two &#8211; &#x2603;</li></ul>") "- one\n- two – ☃"
  s.eq "html: script links are not kept" (htmlToText "<a href=\"javascript:alert(1)\">click</a>") "click"
  IO.println "mime"
  let m := parseMessage multipartMail
  s.eq "encoded-word from" m.from "Jürgen Müller <jm@example.org>"
  s.eq "adjacent encoded words joined" m.subject "Grüße aus Köln"
  s.eq "display name" (displayName m.from) "Jürgen Müller"
  s.eq "message id" m.messageId (some "abc@example.org")
  s.eq "thread key is the references root" m.threadKey (some "root@example.org")
  s.eq "date with offset" m.date (some 1792497787)
  s.eq "plain part preferred, QP soft breaks" m.text "Hallo Welt, schön hier."
  let h := parseMessage htmlMail
  s.eq "html fallback, base64, cp1252" h.text "Order & shipping\n\n5 € charged €"
  s.eq "thread key falls back to nothing" h.threadKey none
  s.eq "date without day name" (parseDate "1 Jan 2026 00:00:00 +0000") (some 1767225600)
  s.eq "two-digit year" (parseDate "Mon, 3 Feb 99 10:00 GMT") (some 918036000)
  s.eq "iso8601" (parseIso8601 "2026-10-20T12:34:56Z") (some 1792499696)
  s.eq "iso8601 offset" (parseIso8601 "2026-10-20T14:34:56+02:00") (some 1792499696)
  s.eq "plain header passes through" (decodeHeader "plain = text") "plain = text"
  s.eq "raw utf-8 header" (decodeHeader (latin1 "Café".toUTF8)) "Café"

def imapTests (s : Suite) : IO Unit := do
  IO.println "imap"
  let body := crlf ["Subject: hi", "", "x"]
  let fetchResp : Response := #[
    .text s!"* 12 FETCH (UID 4827 FLAGS (\\Seen \\Answered) INTERNALDATE \"17-Jul-2026 02:44:25 -0700\" BODY[]<0> \{{body.length}}",
    .literal body,
    .text ")"]
  match fetchResp.fetch? with
  | none => s.check "fetch parses" false
  | some f =>
    s.eq "fetch seq" f.seq 12
    s.eq "fetch uid" f.uid (some 4827)
    s.eq "fetch flags" f.flags #["\\Seen", "\\Answered"]
    s.eq "fetch body literal" f.body (some body)
    s.eq "fetch internaldate" f.internalDate (some "17-Jul-2026 02:44:25 -0700")
  s.eq "fetch rfc822.size" ((Response.fetch? #[.text "* 3 FETCH (UID 17 RFC822.SIZE 52011)"]).map
    fun f => (f.uid, f.size)) (some (some 17, some 52011))
  s.eq "batches by count" (Connector.ImapSource.planBatches #[(1, 10), (2, 10), (3, 10)] 2 100 100)
    #[#[1, 2], #[3]]
  s.eq "batches by bytes, a big one alone"
    (Connector.ImapSource.planBatches #[(1, 40), (2, 70), (3, 10), (4, 10)] 10 100 1000)
    #[#[1], #[2, 3, 4]]
  s.eq "batches count a message at most maxBytes"
    (Connector.ImapSource.planBatches #[(1, 500), (2, 500)] 10 100 50) #[#[1, 2]]
  s.eq "uid set ranges" (Connector.ImapSource.uidSet #[3, 4, 5, 9, 11, 12]) "3:5,9,11:12"
  s.eq "literal size" (literalSize? "* 1 FETCH (BODY[] {123}") (some 123)
  s.eq "literal+ size" (literalSize? "a LOGIN {5+}") (some 5)
  s.eq "no literal" (literalSize? "* OK done") none
  let ok : Response := #[.text "* OK [UIDVALIDITY 3857529045] UIDs valid"]
  s.eq "uidvalidity code" (ok.codeNat? "UIDVALIDITY") (some 3857529045)
  s.eq "exists" (Response.exists? #[.text "* 172 EXISTS"]) (some 172)
  s.eq "tagged" (Response.tagged? #[.text "h3 NO [AUTHENTICATIONFAILED] bad"])
    (some ("h3", "NO", "[AUTHENTICATIONFAILED] bad"))
  s.eq "capabilities" (Response.capabilities? #[.text "* OK [CAPABILITY IMAP4rev1 IDLE AUTH=PLAIN] hi"])
    (some ["IMAP4REV1", "IDLE", "AUTH=PLAIN"])
  s.eq "bracketed atom stays whole"
    (parseValues #[.text "BODY[HEADER.FIELDS (FROM TO)] NIL \"a\\\"b\""])
    #[.atom "BODY[HEADER.FIELDS (FROM TO)]", .nil, .str "a\"b"]
  s.eq "quote escapes" (quote "a\"b\\c").toOption (some "\"a\\\"b\\\\c\"")
  s.eq "sasl plain" (saslPlain "user" "pass") "AHVzZXIAcGFzcw=="
  s.eq "sasl xoauth2" (saslXOAuth2 "u@x.org" "tok") "dXNlcj11QHgub3JnAWF1dGg9QmVhcmVyIHRvawEB"
  s.eq "mailbox utf-7" (encodeMailbox "Entwürfe") "Entw&APw-rfe"
  s.eq "mailbox ampersand" (encodeMailbox "A&B") "A&-B"
  match Connector.ImapSource.normalize (Json.mkObj [("raw", multipartMail),
      ("flags", toJson #["\\Seen"])]) with
  | .ok n =>
    s.eq "imap normalize title" n.title "Grüße aus Köln"
    s.eq "imap normalize read from \\Seen" n.read true
    s.eq "imap normalize author" n.author "Jürgen Müller"
  | .error e => s.check "imap normalize" false e

def githubThread : String := "{
  \"id\": \"9001\", \"unread\": true, \"reason\": \"review_requested\",
  \"updated_at\": \"2026-10-20T12:34:56Z\",
  \"subject\": {\"title\": \"Add IMAP IDLE\", \"type\": \"PullRequest\",
    \"url\": \"https://api.github.com/repos/chrisflav/angelia/pulls/7\",
    \"latest_comment_url\": null},
  \"repository\": {\"full_name\": \"chrisflav/angelia\",
    \"html_url\": \"https://github.com/chrisflav/angelia\"}}"

def githubTests (s : Suite) : IO Unit := do
  IO.println "github"
  let t := (Json.parse githubThread).toOption.get!
  match Connector.GitHub.normalize t with
  | .ok n =>
    s.eq "title" n.title "Add IMAP IDLE"
    s.eq "kind" n.kind "PullRequest"
    s.eq "url" n.url (some "https://github.com/chrisflav/angelia/pull/7")
    s.eq "thread" n.threadKey (some "9001")
    s.eq "body without comment" n.body "PullRequest — review requested"
    s.eq "sentAt" n.sentAt (some 1792499696)
  | .error e => s.check "normalize" false e
  s.eq "external id" (Connector.GitHub.externalId t) "9001@2026-10-20T12:34:56Z"
  s.eq "next link" (Connector.GitHub.nextLink
    "<https://api.github.com/notifications?page=2>; rel=\"next\", <https://x?page=5>; rel=\"last\"")
    (some "https://api.github.com/notifications?page=2")
  let (hs, body) := Http.parseHeadersAndBody
    "HTTP/1.1 100 Continue\r\n\r\nHTTP/2 200\r\nLast-Modified: Tue\r\nX-Poll-Interval: 60\r\n\r\n[]" 5
  s.eq "curl headers" hs #[("last-modified", "Tue"), ("x-poll-interval", "60")]
  s.eq "curl body" body "[]"

def ruleTests (s : Suite) : IO Unit := do
  IO.println "rules"
  let n : NotificationData := { title := "CI failed on master", author := "github-actions" }
  let rule (id : Int) (spec : RuleSpec) : Rule := { id, name := "", enabled := true, position := 0, spec }
  let ci := rule 1 { conditions := #[{ field := .title, op := .contains, value := "ci failed" }],
                     labels := #[10], markRead := true }
  let notBot := rule 2 { conditions := #[{ field := .author, op := .startsWith, value := "github",
                                            negate := true }], labels := #[11] }
  let empty := rule 3 { labels := #[12] }
  s.eq "contains, case-insensitive, with actions"
    (evaluate #[ci, notBot, empty] "github" n) { labels := #[(1, 10)], markRead := true }
  s.eq "any" ((rule 4 { «match» := "any", conditions := #[
      { field := .source, op := .equals, value := "mail" },
      { field := .source, op := .equals, value := "github" }] }).spec.matches "github" n) true
  let j := toJson ci.spec
  s.check "spec json roundtrip" ((fromJson? j : Except String RuleSpec).toOption.map toJson == some j)

def scopeTests (s : Suite) : IO Unit := do
  IO.println "scopes"
  let parse (j : String) : Option Scope := (Json.parse j >>= fromJson?).toOption
  s.eq "empty scope: everything, read-only" (parse "{}") (some {})
  s.eq "explicit nulls are unrestricted" (parse "{\"sources\":null,\"labels\":null,\"write\":true}")
    (some Scope.full)
  let sc : Scope := { sources := some #["mail"], labels := some #[1, 2] }
  s.eq "sql args" sc.sqlArgs (some "[\"mail\"]", some "[1,2]")
  s.eq "full scope has no sql restriction" Scope.full.sqlArgs (none, none)
  s.check "allows own label" (sc.allowsLabel 2)
  s.check "refuses other label" (!sc.allowsLabel 3)
  s.check "refuses other source" (!sc.allowsSource "github")
  s.check "empty source list sees nothing" (!({ sources := some #[] } : Scope).allowsSource "mail")
  s.eq "scope json roundtrip" (parse (toJson sc).compress) (some sc)
  let timed : Scope := { since := some 1000, within := some 3600 }
  s.eq "time scope json roundtrip" (parse (toJson timed).compress) (some timed)
  s.eq "no time limit" (({} : Scope).minTime 10000) none
  s.eq "since only" (({ since := some 1000 } : Scope).minTime 10000) (some 1000)
  s.eq "within only" (({ within := some 3600 } : Scope).minTime 10000) (some 6400)
  s.eq "both: the later wins" (timed.minTime 10000) (some 6400)
  s.eq "both: the later wins, other way" (timed.minTime 4000) (some 1000)
  s.eq "a zero window is refused" (parse "{\"within\":0}") none

def cryptoTests (s : Suite) : IO Unit := do
  IO.println "crypto"
  let bytes (l : List Nat) := ByteArray.mk (l.map Nat.toUInt8).toArray
  -- RFC 8439, section 2.8.2.
  let key := bytes ((List.range 32).map (0x80 + ·))
  let nonce := bytes [7, 0, 0, 0, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]
  let aad := bytes [0x50, 0x51, 0x52, 0x53, 0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7]
  let msg := "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the \
    future, sunscreen would be it.".toUTF8
  let sealed := Aead.encrypt key nonce aad msg
  s.eq "chacha20-poly1305 ciphertext" (Crypto.toHex (sealed.extract 0 16))
    "d31a8d34648e60db7b86afbc53ef7ec2"
  s.eq "chacha20-poly1305 tag" (Crypto.toHex (sealed.extract msg.size sealed.size))
    "1ae10b594f09e26a7e902ecbd0600691"
  s.eq "decrypts" ((Aead.decrypt key nonce aad sealed).map (·.data)) (some msg.data)
  s.eq "wrong aad is refused" ((Aead.decrypt key nonce (bytes [1]) sealed).map (·.data)) none
  let flipped := sealed.set! 3 (sealed[3]! ^^^ 1)
  s.eq "altered ciphertext is refused" ((Aead.decrypt key nonce aad flipped).map (·.data)) none
  s.eq "pbkdf2" (Crypto.toHex (Crypto.pbkdf2Sha256 "password".toUTF8 "salt".toUTF8 4096))
    "c5e478d59288c841aa530db6845c4c8d962893a001ce4e11a4963873aa98134a"
  s.eq "pbkdf2, long key, two blocks"
    (Crypto.toHex (Crypto.pbkdf2Sha256 (bytes (List.replicate 100 120)) "salt".toUTF8 3 40))
    "59bfa49750dd5462ce38370a1e7abe0736ff334cf1c2f0d84f23a03435d660d1537367bcfb776a10"

def vaultTests (s : Suite) : IO Unit := do
  IO.println "vault"
  let h ← Vault.PasswordHash.create "correct horse" 1000
  s.check "password verifies" (h.verify "correct horse")
  s.check "wrong password fails" (!h.verify "correct hors")
  s.check "hash roundtrips"
    ((Vault.PasswordHash.parse h.toString).toOption.map (·.verify "correct horse") == some true)
  let other ← Vault.PasswordHash.create "correct horse" 1000
  s.check "salted" (h.hash.data != other.hash.data)
  let dataKey ← IO.getRandomBytes 32
  let w ← Vault.WrappedKey.wrap dataKey "pw" 1000
  s.eq "key unwraps" ((w.unwrap "pw").map (·.data)) (some dataKey.data)
  s.eq "key needs the password" ((w.unwrap "pW").map (·.data)) none
  let k := Vault.Keys.derive dataKey
  let id := Vault.keyedId k
  s.eq "keyed ids are stable" (id "mail" "mid:<a@b>") (id "mail" "mid:<a@b>")
  s.check "keyed ids depend on the source" (id "mail" "x" != id "work" "x")
  let c ← Vault.seal k "row 1" "Grüße"
  s.eq "content roundtrips" (← Vault.open k "row 1" c) "Grüße"
  s.check "content is bound to its row" ((← (Vault.open k "row 2" c).toBaseIO) matches .error _)

def changeTests (s : Suite) : IO Unit := do
  IO.println "changes"
  let (start, _) ← changesSince 0
  bumpChanges (some #[1, 2])
  bumpChanges (some #[3])
  let (now, c) ← changesSince start
  s.eq "merged ids" (now, c) (start + 2, some #[1, 2, 3])
  bumpChanges none
  s.eq "unknown change" (← changesSince now).2 none
  for _ in [0:300] do bumpChanges (some #[4])
  s.eq "too far behind" (← changesSince now).2 none

def oauthTests (s : Suite) : IO Unit := do
  IO.println "oauth2"
  s.eq "form encoding" (OAuth2.formEncode "a b/c+d~é") "a%20b%2Fc%2Bd~%C3%A9"
  let err (r : Except String OAuth2.Grant) : Option String := match r with
    | .error e => some e
    | .ok _ => none
  s.eq "grant" (OAuth2.parseResponse 200
      "{\"token_type\":\"Bearer\",\"expires_in\":4049,\"access_token\":\"at\",\"refresh_token\":\"rt\"}").toOption
    (some { accessToken := "at", refreshToken := some "rt", expiresIn := 4049 })
  s.eq "grant without rotation" (OAuth2.parseResponse 200 "{\"access_token\":\"at\"}").toOption
    (some { accessToken := "at", refreshToken := none, expiresIn := 3600 })
  s.eq "error, first line of the description" (err (OAuth2.parseResponse 400
      "{\"error\":\"invalid_grant\",\"error_description\":\"AADSTS70008: expired.\\r\\nTrace ID: x\"}"))
    (some "invalid_grant: AADSTS70008: expired.")
  s.eq "curl config quoting" (Http.configQuote "a\"b\\c\nd") "\"a\\\"b\\\\c\\nd\""
  s.eq "curl config" (Http.configFor #[("Authorization", "Bearer t")] (some "x=1"))
    "header = \"Authorization: Bearer t\"\ndata-binary = \"x=1\"\n"

/-- Bytes from lowercase hex, for test vectors. -/
def unhex (s : String) : ByteArray := Id.run do
  let d (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    out := out.push (d cs[2 * i]! * 16 + d cs[2 * i + 1]!).toUInt8
  return out

def secondFactorCryptoTests (s : Suite) : IO Unit := do
  IO.println "second-factor crypto"
  s.eq "sha1" (Crypto.toHex (Crypto.sha1 "abc".toUTF8)) "a9993e364706816aba3e25717850c26c9cd0d89d"
  s.eq "hmac-sha1, RFC 6238 seed at step 1"
    (Crypto.toHex (Crypto.hmacSha1 "12345678901234567890".toUTF8 (unhex "0000000000000001")))
    "75a48a19d4cbe100644e8ac1397eea747a2d33ab"
  -- From Python's `cryptography`: a P-256 key, a message and its ES256 signature.
  let spki := unhex "3059301306072a8648ce3d020106082a8648ce3d03010703420004471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714cdd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a858"
  let msg := "angelia webauthn test".toUTF8
  let sig := unhex "3045022070c834624418539efb019c0ec7b1d9de8eca92b7a2ff29209a6473592885e986022100946b54c9e5eb55764487d8e5093ae4dadebc5fe8167683d56ef74fe49f6cc781"
  let some key := P256.parseSpki spki | s.check "spki parses" false
  let some (r, sv) := P256.parseDerSignature sig | s.check "signature parses" false
  s.check "es256 verifies" (P256.verify key (Crypto.sha256 msg) r sv)
  s.check "es256 rejects another message" (!P256.verify key (Crypto.sha256 "angelia".toUTF8) r sv)
  s.check "es256 rejects another signature" (!P256.verify key (Crypto.sha256 msg) r (sv + 1))
  s.check "off-curve key refused" (P256.parseSpki (spki.set! 90 (spki[90]! ^^^ 1))).isNone
  s.eq "base64url" (base64url "any carnal pleas".toUTF8) "YW55IGNhcm5hbCBwbGVhcw"
  s.eq "base64url roundtrip" ((unbase64url (base64url (unhex "fbff00"))).map (·.data)) (some (unhex "fbff00").data)
  s.eq "base32" (base32 "foobar".toUTF8) "MZXW6YTBOI"
  let seed := "12345678901234567890".toUTF8
  s.eq "hotp, RFC 4226" ((List.range 3).map (hotp seed)) [755224, 287082, 359152]
  -- 59 s is step 1, whose code is 287082.
  s.eq "totp accepts the current code" (totpMatch seed 59 0 "287 082") (some 1)
  s.eq "totp accepts one step of drift" (totpMatch seed 89 0 "287082") (some 1)
  s.eq "totp refuses a spent code" (totpMatch seed 59 1 "287082") none
  s.eq "totp refuses a wrong code" (totpMatch seed 59 0 "287083") none
  let rp := RelyingParty.ofOrigin "http://localhost:8093"
  s.eq "relying party id" rp.id "localhost"
  -- Built in Python as a browser would hand them over, signed with the key above.
  let regAuth := unhex "49960de5880e8c687434170f6476605b8fe4aeb9a28632c7995cf3ba831d97634100000000000000000000000000000000000000000010000102030405060708090a0b0c0d0e0fa5010203262001215820471c3e758c4904285bba7e53118ed0f524adeb0757d25bd2f8e7b0d76dfa714c225820dd520f7aca8a8b917acc37f51de8f0c9bbe3ad858382e702dc25a12d09f7a858"
  let regCd := unhex "7b2274797065223a2022776562617574686e2e637265617465222c20226368616c6c656e6765223a2022636d566e4c574e6f595778735a57356e5a51222c20226f726967696e223a2022687474703a2f2f6c6f63616c686f73743a38303933227d"
  match verifyRegistration rp "cmVnLWNoYWxsZW5nZQ" regCd regAuth spki (-7) with
  | .ok c => s.eq "registration: credential id" c.id (base64url (unhex "000102030405060708090a0b0c0d0e0f"))
  | .error e => s.check "registration verifies" false e
  s.check "registration with another challenge is refused"
    (verifyRegistration rp "b3RoZXI" regCd regAuth spki (-7) matches .error _)
  s.check "registration with a key not in the authenticator data is refused"
    (verifyRegistration rp "cmVnLWNoYWxsZW5nZQ" regCd regAuth
      (unhex "3059301306072a8648ce3d020106082a8648ce3d030107034200046b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c2964fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5")
      (-7) matches .error _)
  let auth := unhex "49960de5880e8c687434170f6476605b8fe4aeb9a28632c7995cf3ba831d97630100000005"
  let cd := unhex "7b2274797065223a2022776562617574686e2e676574222c20226368616c6c656e6765223a20226247396e61573474593268686247786c626d646c222c20226f726967696e223a2022687474703a2f2f6c6f63616c686f73743a38303933222c202263726f73734f726967696e223a2066616c73657d"
  let asig := unhex "304402204707e6064566433603c83d0cfa38ac5a94c939712e3178ef89e70ae8630fee1f02202c0770b1323c505aef2622b6587e8a878503df8a3fc9d713eff33c333febb768"
  let cred : Credential := { id := "", publicKey := spki, signCount := 4 }
  s.eq "assertion verifies, counter advances"
    (verifyAssertion rp "bG9naW4tY2hhbGxlbmdl" cred cd auth asig).toOption (some 5)
  s.check "assertion with a stale counter is refused"
    (verifyAssertion rp "bG9naW4tY2hhbGxlbmdl" { cred with signCount := 5 } cd auth asig matches .error _)
  s.check "assertion for another origin is refused"
    (verifyAssertion (RelyingParty.ofOrigin "http://localhost:9999") "bG9naW4tY2hhbGxlbmdl" cred cd auth asig
      matches .error _)
  s.check "assertion with a flipped byte is refused"
    (verifyAssertion rp "bG9naW4tY2hhbGxlbmdl" cred cd (auth.set! 36 6) asig matches .error _)

def main : IO UInt32 := do
  let s : Suite := { failures := ← IO.mkRef #[] }
  mimeTests s
  attachmentTests s
  imapTests s
  githubTests s
  ruleTests s
  scopeTests s
  cryptoTests s
  vaultTests s
  changeTests s
  oauthTests s
  secondFactorCryptoTests s
  let failures ← s.failures.get
  if failures.isEmpty then
    IO.println "all tests passed"
    return 0
  else
    IO.println s!"{failures.size} failure(s): {failures}"
    return 1