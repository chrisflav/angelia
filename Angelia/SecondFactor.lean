import Lean.Data.Json
import Angelia.Crypto
import Angelia.P256

/-!
# Second factors

What a sign-in needs besides the password, when any is registered: a tap on a security key
(WebAuthn, which covers U2F-only keys such as older Titans as well as FIDO2 ones) or a code from
an authenticator app (TOTP, RFC 6238). Both are checked here, as pure functions over what the
browser sent; storing them and the challenges is the server's business.

Only ES256 credentials are accepted. Every FIDO authenticator supports it, and it is what U2F
keys can do at all, so nothing is lost by not also implementing EdDSA. The attestation is not
checked (`"none"` is requested): registering a factor already takes the password and a session,
and which make of key it is would not change what it may do.
-/

open Lean

namespace Angelia.SecondFactor

/-! ## Encodings -/

private def b64Alphabet : String :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"

/-- base64url without padding, as WebAuthn uses for ids and challenges. -/
def base64url (b : ByteArray) : String := Id.run do
  let cs := b64Alphabet.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < b.size do
    let n := (b[i]!.toNat <<< 16) ||| ((b[i + 1]?.getD 0).toNat <<< 8) ||| (b[i + 2]?.getD 0).toNat
    let chars := min 4 ((b.size - i) * 4 / 3 + (if (b.size - i) % 3 == 0 then 0 else 1))
    for j in [0:chars] do
      out := out.push cs[(n >>> (18 - 6 * j)) &&& 63]!
    i := i + 3
  return out

/-- Inverse of `base64url`; standard base64 and padding are accepted too. -/
def unbase64url (s : String) : Option ByteArray := do
  let value (c : Char) : Option Nat :=
    if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat)
    else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
    else if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat + 52)
    else if c == '-' || c == '+' then some 62
    else if c == '_' || c == '/' then some 63
    else none
  let mut acc := 0
  let mut bits := 0
  let mut out := ByteArray.empty
  for c in s.toList do
    if c == '=' then continue
    acc := (acc <<< 6) ||| (← value c)
    bits := bits + 6
    if bits ≥ 8 then
      bits := bits - 8
      out := out.push ((acc >>> bits) &&& 0xff).toUInt8
      acc := acc &&& ((1 <<< bits) - 1)
  return out

/-- RFC 4648 base32 without padding: how authenticator apps take a secret. -/
def base32 (b : ByteArray) : String := Id.run do
  let cs := "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567".toList.toArray
  let mut out := ""
  let mut acc := 0
  let mut bits := 0
  for x in b do
    acc := (acc <<< 8) ||| x.toNat
    bits := bits + 8
    while bits ≥ 5 do
      bits := bits - 5
      out := out.push cs[(acc >>> bits) &&& 31]!
    acc := acc &&& ((1 <<< bits) - 1)
  if bits > 0 then out := out.push cs[(acc <<< (5 - bits)) &&& 31]!
  return out

/-! ## TOTP -/

/-- TOTP's step length in seconds, the one every app assumes. -/
def totpPeriod : Nat := 30

/-- The six-digit HOTP value (RFC 4226) of `secret` at counter `step`. -/
def hotp (secret : ByteArray) (step : Nat) : Nat :=
  let counter := ByteArray.mk ((Array.range 8).map fun i => (step >>> (8 * (7 - i))).toUInt8)
  let mac := Crypto.hmacSha1 secret counter
  let off := (mac[19]! &&& 0x0f).toNat
  let code := ((mac[off]!.toNat &&& 0x7f) <<< 24) ||| (mac[off + 1]!.toNat <<< 16) |||
    (mac[off + 2]!.toNat <<< 8) ||| mac[off + 3]!.toNat
  code % 1000000

/-- The step a six-digit `code` is valid for, allowing one step of clock drift either way, if
    it is valid and later than `lastStep` -- a code is accepted at most once, so one read over a
    shoulder or out of a log is spent. -/
def totpMatch (secret : ByteArray) (now : Nat) (lastStep : Nat) (code : String) : Option Nat :=
  let code := code.trimAscii.toString.replace " " ""
  if code.length != 6 || !code.all Char.isDigit then none else
  let current := now / totpPeriod
  [current - 1, current, current + 1].find? fun step =>
    step > lastStep && hotp secret step == code.toNat!

/-- The `otpauth://` URI an authenticator app reads from the QR code. -/
def totpUri (issuer account : String) (secret : ByteArray) : String :=
  s!"otpauth://totp/{issuer}:{account}?secret={base32 secret}&issuer={issuer}" ++
    s!"&period={totpPeriod}&digits=6&algorithm=SHA1"

/-! ## WebAuthn -/

/-- Where the server is reached, which is what a credential is bound to. -/
structure RelyingParty where
  /-- The page's origin as the browser reports it, e.g. `https://angelia.merten.dev`. -/
  origin : String
  /-- The host name credentials are scoped to: the origin without scheme or port. -/
  id : String

def RelyingParty.ofOrigin (origin : String) : RelyingParty :=
  let host := ((origin.splitOn "://").getLast!.splitOn "/").headD ""
  { origin, id := (host.splitOn ":").headD host }

/-- Check the `clientDataJSON` the browser assembled: the ceremony, our challenge, our origin. -/
def checkClientData (rp : RelyingParty) (type challenge : String) (clientData : ByteArray) :
    Except String Unit := do
  let some text := String.fromUTF8? clientData | throw "clientDataJSON is not UTF-8"
  let j ← Json.parse text
  if (j.getObjValAs? String "type").toOption != some type then throw s!"not a {type} response"
  if (j.getObjValAs? String "challenge").toOption != some challenge then
    throw "the challenge does not match; try again"
  if (j.getObjValAs? String "origin").toOption != some rp.origin then
    throw s!"signed for another origin than {rp.origin}"

/-- Check the authenticator data's relying-party hash and the user-presence flag (the tap);
    return its signature counter. -/
def checkAuthenticatorData (rp : RelyingParty) (authData : ByteArray) : Except String Nat := do
  if authData.size < 37 then throw "authenticator data too short"
  if authData.extract 0 32 != Crypto.sha256 rp.id.toUTF8 then
    throw s!"the key signed for another site than {rp.id}"
  if authData[32]! &&& 0x01 == 0 then throw "the key was not touched"
  return (authData.extract 33 37).foldl (fun acc x => acc * 256 + x.toNat) 0

/-- A security key, as registered. -/
structure Credential where
  /-- The key's credential id, base64url. -/
  id : String
  /-- Its public key, a P-256 `SubjectPublicKeyInfo` in DER. -/
  publicKey : ByteArray
  signCount : Nat

/-- Check a registration (`navigator.credentials.create`). The browser hands over the public key
    already in SPKI form (`getPublicKey()`); it is checked against the COSE key inside the
    authenticator data, so both say the same thing. -/
def verifyRegistration (rp : RelyingParty) (challenge : String) (clientData authData : ByteArray)
    (publicKey : ByteArray) (alg : Int) : Except String Credential := do
  checkClientData rp "webauthn.create" challenge clientData
  let signCount ← checkAuthenticatorData rp authData
  if authData[32]! &&& 0x40 == 0 then throw "no credential in the authenticator data"
  if alg != -7 then throw "only ES256 keys are supported"
  let some (x, y) := P256.parseSpki publicKey | throw "not a P-256 public key"
  -- Attested credential data: 16-byte AAGUID, 2-byte length, the credential id, the COSE key.
  if authData.size < 55 then throw "authenticator data too short"
  let idLen := authData[53]!.toNat * 256 + authData[54]!.toNat
  if authData.size < 55 + idLen then throw "authenticator data too short"
  let credId := authData.extract 55 (55 + idLen)
  let cose := authData.extract (55 + idLen) authData.size
  -- The EC2 key's x (-2) and y (-3) are 32-byte byte strings: CBOR `58 20` and the bytes.
  let coordinate (v : Nat) : ByteArray :=
    ByteArray.mk #[0x58, 0x20] ++
      ByteArray.mk ((Array.range 32).map fun i => (v >>> (8 * (31 - i))).toUInt8)
  let contains (hay needle : ByteArray) : Bool :=
    (List.range (hay.size + 1 - needle.size)).any fun i => hay.extract i (i + needle.size) == needle
  if !(contains cose (coordinate x) && contains cose (coordinate y)) then
    throw "the public key does not match the authenticator data"
  return { id := base64url credId, publicKey, signCount }

/-- Check a sign-in (`navigator.credentials.get`) against the registered credential; return the
    new signature counter. A counter that does not move forward means the key was cloned, or the
    response replayed, unless the key keeps no counter at all (always 0). -/
def verifyAssertion (rp : RelyingParty) (challenge : String) (cred : Credential)
    (clientData authData signature : ByteArray) : Except String Nat := do
  checkClientData rp "webauthn.get" challenge clientData
  let count ← checkAuthenticatorData rp authData
  if (count != 0 || cred.signCount != 0) && count <= cred.signCount then
    throw "the key's signature counter went backwards; it may have been cloned"
  let some key := P256.parseSpki cred.publicKey | throw "stored public key is unusable"
  let some (r, s) := P256.parseDerSignature signature | throw "malformed signature"
  if !P256.verify key (Crypto.sha256 (authData ++ Crypto.sha256 clientData)) r s then
    throw "the signature does not verify"
  return count

end Angelia.SecondFactor