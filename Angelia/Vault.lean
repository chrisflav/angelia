import Lean.Data.Json
import Angelia.Aead
import Angelia.Crypto

/-!
# Keys and the password

What the database stores of a notification's content is encrypted under a random 256-bit data
key, which the database holds only wrapped (encrypted): under the *unlock key* from the
configuration, so the server unlocks by itself at start, and under a key derived from the login
password with PBKDF2, as the fallback should the unlock key be lost. A copy of the database alone
-- a backup without the configuration and its secrets -- reveals no content.

Without an unlock key the server starts *locked*, and the first sign-in unwraps the data key with
the password. That protects little in practice: whoever can read the database where the server
runs can also read the credentials the sources need, and with them the mail itself.

What stays in the clear is what the server must query on: sources, kinds, timestamps, flags and
labels, plus rules, views, cursors and health. External ids and thread keys are stored only as
keyed hashes (HMAC under a key derived from the data key), which keeps deduplication and thread
grouping working without revealing message ids.

The login password is checked against a salted PBKDF2 hash in the configuration, in the format
`pbkdf2-sha256$<iterations>$<salt hex>$<hash hex>`.
-/

open Lean

namespace Angelia.Vault

/-- PBKDF2 iterations for new password hashes and wrapped keys. Lower than OWASP's 600 000, since
    this pure-Lean SHA-256 is slower than native ones; about a second per derivation. The count is
    stored with each hash, so raising it later keeps old hashes valid. -/
def defaultIterations : Nat := 200000

private def unhex (s : String) : Option ByteArray := do
  let digit (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
  let cs := s.toLower.toList.toArray
  if cs.size % 2 != 0 then none
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    out := out.push (((← digit cs[2 * i]!) * 16 + (← digit cs[2 * i + 1]!)).toUInt8)
  return out

structure PasswordHash where
  iterations : Nat
  salt : ByteArray
  hash : ByteArray

def PasswordHash.parse (s : String) : Except String PasswordHash :=
  match s.splitOn "$" with
  | ["pbkdf2-sha256", it, salt, hash] =>
    match it.toNat?, unhex salt, unhex hash with
    | some iterations, some salt, some hash => .ok { iterations, salt, hash }
    | _, _, _ => .error "malformed passwordHash"
  | _ => .error "passwordHash must look like pbkdf2-sha256$<iterations>$<salt>$<hash>"

def PasswordHash.toString (h : PasswordHash) : String :=
  s!"pbkdf2-sha256${h.iterations}${Crypto.toHex h.salt}${Crypto.toHex h.hash}"

def PasswordHash.create (password : String) (iterations := defaultIterations) :
    IO PasswordHash := do
  let salt ← IO.getRandomBytes 16
  return { iterations, salt, hash := Crypto.pbkdf2Sha256 password.toUTF8 salt iterations }

def PasswordHash.verify (h : PasswordHash) (password : String) : Bool :=
  Crypto.constantTimeEq (Crypto.pbkdf2Sha256 password.toUTF8 h.salt h.iterations h.hash.size) h.hash

/-- The data key and the keys derived from it, each for one purpose. -/
structure Keys where
  dataKey : ByteArray
  content : ByteArray
  ids : ByteArray

def Keys.derive (dataKey : ByteArray) : Keys :=
  { dataKey, content := Crypto.hmac dataKey "angelia content"
    ids := Crypto.hmac dataKey "angelia ids" }

initialize current : IO.Ref (Option Keys) ← IO.mkRef none

def unlocked : IO Bool := return (← current.get).isSome

/-- The keys, or an error while the server is locked. -/
def keys : IO Keys := do
  let some k ← current.get | throw (IO.userError "locked: sign in to unlock")
  return k

def install (dataKey : ByteArray) : IO Unit := current.set (some (Keys.derive dataKey))

/-- A keyed hash standing in for an identifier: equal inputs give equal outputs, but without the
    key nothing about the input can be learnt or tested. -/
def keyedId (k : Keys) (source value : String) : String :=
  Crypto.toHex ((Crypto.hmac k.ids (source ++ "\x00" ++ value)).extract 0 16)

def «seal» (k : Keys) (aad : String) (plaintext : String) : IO ByteArray :=
  Aead.seal k.content aad.toUTF8 plaintext.toUTF8

def «open» (k : Keys) (aad : String) (sealed : ByteArray) : IO String := do
  let some b := Aead.open k.content aad.toUTF8 sealed
    | throw (IO.userError s!"stored data failed authentication ({aad})")
  let some s := String.fromUTF8? b | throw (IO.userError s!"stored data is not UTF-8 ({aad})")
  return s

/-- The data key under a password-derived key, as stored in the database. -/
structure WrappedKey where
  salt : ByteArray
  iterations : Nat
  wrapped : ByteArray

private def wrapAad : ByteArray := "angelia data key".toUTF8

def WrappedKey.wrap (dataKey : ByteArray) (password : String) (iterations := defaultIterations) :
    IO WrappedKey := do
  let salt ← IO.getRandomBytes 16
  let kek := Crypto.pbkdf2Sha256 password.toUTF8 salt iterations
  return { salt, iterations, wrapped := ← Aead.seal kek wrapAad dataKey }

def WrappedKey.unwrap (w : WrappedKey) (password : String) : Option ByteArray :=
  Aead.open (Crypto.pbkdf2Sha256 password.toUTF8 w.salt w.iterations) wrapAad w.wrapped

private def unlockAad : ByteArray := "angelia data key, unlock key".toUTF8

/-- The data key wrapped under the configured unlock key, itself a random 256-bit key, so no key
    derivation is needed. -/
def wrapUnder (unlockKey dataKey : ByteArray) : IO ByteArray :=
  Aead.seal unlockKey unlockAad dataKey

def unwrapUnder (unlockKey wrapped : ByteArray) : Option ByteArray :=
  Aead.open unlockKey unlockAad wrapped

/-- An unlock key from the configuration: 64 hex digits. -/
def parseUnlockKey (s : String) : Except String ByteArray :=
  let s := s.trimAscii.toString.toLower
  if s.length == 64 && s.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then .ok (Crypto.unhex s)
  else .error "unlockKey must be 64 hex digits (`openssl rand -hex 32`)"

end Angelia.Vault