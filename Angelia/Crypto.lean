/-!
# SHA-256, HMAC-SHA256 and PBKDF2

A small, self-contained SHA-256 implementation over `ByteArray` (taken from taxis), used to hash
session and API tokens before storing them, the HMAC construction over it, and PBKDF2 on top of
that for the login password and the key that encrypts the database.
-/

namespace Angelia.Crypto

private def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

private def kConsts : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Pad a message per the SHA-256 spec: a `0x80` byte, zero padding to 56 mod 64, then the
    64-bit big-endian bit length. -/
private def pad (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := (UInt64.ofNat msg.size) * 8
  let mut out := msg.push 0x80
  while out.size % 64 != 56 do
    out := out.push 0
  for i in [0:8] do
    let shift : UInt64 := UInt64.ofNat ((7 - i) * 8)
    out := out.push (UInt8.ofNat ((bitLen >>> shift).toNat % 256))
  return out

/-- SHA-256's initial hash value. -/
private def iv : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- The compression function: absorb one 64-byte block, given as its sixteen big-endian words. -/
private def compress (h : Array UInt32) (block : Array UInt32) : Array UInt32 := Id.run do
  let mut w := block ++ Array.replicate 48 0
  for i in [16:64] do
    let w15 := w[i - 15]!
    let w2 := w[i - 2]!
    let s0 := (rotr w15 7) ^^^ (rotr w15 18) ^^^ (w15 >>> 3)
    let s1 := (rotr w2 17) ^^^ (rotr w2 19) ^^^ (w2 >>> 10)
    w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut cc := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for i in [0:64] do
    let s1 := (rotr e 6) ^^^ (rotr e 11) ^^^ (rotr e 25)
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let temp1 := hh + s1 + ch + kConsts[i]! + w[i]!
    let s0 := (rotr a 2) ^^^ (rotr a 13) ^^^ (rotr a 22)
    let maj := (a &&& b) ^^^ (a &&& cc) ^^^ (b &&& cc)
    let temp2 := s0 + maj
    hh := g; g := f; f := e; e := d + temp1; d := cc; cc := b; b := a; a := temp1 + temp2
  return #[h[0]! + a, h[1]! + b, h[2]! + cc, h[3]! + d,
           h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-- The big-endian words of `data` from byte `base` on. -/
private def wordsAt (data : ByteArray) (base n : Nat) : Array UInt32 := Id.run do
  let mut w := Array.mkEmpty n
  for i in [0:n] do
    let b0 := data[base + i*4]!.toUInt32
    let b1 := data[base + i*4 + 1]!.toUInt32
    let b2 := data[base + i*4 + 2]!.toUInt32
    let b3 := data[base + i*4 + 3]!.toUInt32
    w := w.push ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3)
  return w

private def wordBytes (h : Array UInt32) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (h.size * 4)
  for x in h do
    out := out.push (UInt8.ofNat ((x >>> 24).toNat % 256))
    out := out.push (UInt8.ofNat ((x >>> 16).toNat % 256))
    out := out.push (UInt8.ofNat ((x >>> 8).toNat % 256))
    out := out.push (UInt8.ofNat (x.toNat % 256))
  return out

/-- Compute the SHA-256 digest of `msg` as a 32-byte `ByteArray`. -/
def sha256 (msg : ByteArray) : ByteArray := Id.run do
  let data := pad msg
  let mut h := iv
  for c in [0:data.size / 64] do
    h := compress h (wordsAt data (c * 64) 16)
  return wordBytes h

private def hexChars : Array Char := "0123456789abcdef".toList.toArray

/-- Lowercase hex encoding of a byte array. -/
def toHex (bytes : ByteArray) : String := Id.run do
  let mut s := ""
  for b in bytes do
    s := (s.push hexChars[b.toNat >>> 4]!).push hexChars[b.toNat &&& 0xf]!
  return s

/-- Bytes from hex; characters that are not hex digits count as zero. -/
def unhex (s : String) : ByteArray := Id.run do
  let digit (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat
    else if 'a' ≤ c.toLower && c.toLower ≤ 'f' then c.toLower.toNat - 'a'.toNat + 10 else 0
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    out := out.push (digit cs[2 * i]! * 16 + digit cs[2 * i + 1]!).toUInt8
  return out

/-- Hex-encoded SHA-256 digest of a string (UTF-8). -/
def sha256Hex (s : String) : String := toHex (sha256 s.toUTF8)

/-- SHA-256's block size in bytes. HMAC pads the key out to it — and hashes a longer key down to a
    digest first, which is then padded like any other short key. -/
private def blockSize : Nat := 64

/-- HMAC-SHA256 of `msg` under `key`, per RFC 2104: `H((K ⊕ opad) ‖ H((K ⊕ ipad) ‖ msg))`. -/
def hmacSha256 (key msg : ByteArray) : ByteArray := Id.run do
  let k := if key.size > blockSize then sha256 key else key
  let mut inner := ByteArray.empty
  let mut outer := ByteArray.empty
  for i in [0:blockSize] do
    -- Reading past the (short) key yields the zero padding the construction calls for.
    let b := k[i]?.getD 0
    inner := inner.push (b ^^^ 0x36)
    outer := outer.push (b ^^^ 0x5c)
  return sha256 (outer ++ sha256 (inner ++ msg))

/-- HMAC-SHA256 of a string message under a byte-array key, as a byte array. The asymmetry is
    deliberate: signing chains feed one digest in as the next key, while the messages being signed
    are always text. -/
def hmac (key : ByteArray) (msg : String) : ByteArray := hmacSha256 key msg.toUTF8

/-- Hex-encoded HMAC-SHA256. -/
def hmacHex (key : ByteArray) (msg : String) : String := toHex (hmac key msg)

/-- Compare two byte arrays in time that depends only on their lengths. -/
def constantTimeEq (a b : ByteArray) : Bool := Id.run do
  if a.size != b.size then return false
  let mut acc : UInt8 := 0
  for i in [0:a.size] do
    acc := acc ||| (a[i]! ^^^ b[i]!)
  return acc == 0

/-- PBKDF2-HMAC-SHA256 (RFC 8018), `dkLen` bytes. The HMAC key schedule is absorbed once, so each
    iteration costs two compressions; the iteration count is what makes guessing expensive. -/
def pbkdf2Sha256 (password salt : ByteArray) (iterations : Nat) (dkLen : Nat := 32) : ByteArray :=
  Id.run do
  let k := if password.size > blockSize then sha256 password else password
  let keyBlock (x : UInt8) : Array UInt32 := Id.run do
    let mut b := ByteArray.emptyWithCapacity blockSize
    for i in [0:blockSize] do
      b := b.push (k[i]?.getD 0 ^^^ x)
    return wordsAt b 0 16
  let inner := compress iv (keyBlock 0x36)
  let outer := compress iv (keyBlock 0x5c)
  -- The final block after a 64-byte key block and a 32-byte message: the message, `0x80`, zeros,
  -- and the bit length 96 * 8.
  let tail : Array UInt32 := #[0x80000000, 0, 0, 0, 0, 0, 0, 768]
  let prf (u : Array UInt32) : Array UInt32 := compress outer (compress inner (u ++ tail) ++ tail)
  let mut out := ByteArray.empty
  let mut i : Nat := 1
  while out.size < dkLen do
    let be := ByteArray.mk #[(i >>> 24).toUInt8, (i >>> 16).toUInt8, (i >>> 8).toUInt8, i.toUInt8]
    let mut u := wordsAt (hmacSha256 password (salt ++ be)) 0 8
    let mut t := u
    for _ in [1:iterations] do
      u := prf u
      t := (t.zip u).map fun (x, y) => x ^^^ y
    out := out ++ wordBytes t
    i := i + 1
  return out.extract 0 dkLen

/-! ## SHA-1

Only for HMAC-SHA1 in TOTP (RFC 6238), which is what authenticator apps compute. HMAC does not
rely on the collision resistance SHA-1 has lost. -/

/-- The SHA-1 digest of `msg`, 20 bytes. -/
def sha1 (msg : ByteArray) : ByteArray := Id.run do
  let rotl (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))
  let data := pad msg
  let mut h : Array UInt32 := #[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]
  for c in [0:data.size / 64] do
    let mut w := wordsAt data (c * 64) 16 ++ Array.replicate 64 0
    for i in [16:80] do
      w := w.set! i (rotl (w[i - 3]! ^^^ w[i - 8]! ^^^ w[i - 14]! ^^^ w[i - 16]!) 1)
    let mut a := h[0]!
    let mut b := h[1]!
    let mut cc := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    for i in [0:80] do
      let (f, k) : UInt32 × UInt32 :=
        if i < 20 then ((b &&& cc) ||| ((~~~b) &&& d), 0x5a827999)
        else if i < 40 then (b ^^^ cc ^^^ d, 0x6ed9eba1)
        else if i < 60 then ((b &&& cc) ||| (b &&& d) ||| (cc &&& d), 0x8f1bbcdc)
        else (b ^^^ cc ^^^ d, 0xca62c1d6)
      let t := rotl a 5 + f + e + k + w[i]!
      e := d; d := cc; cc := rotl b 30; b := a; a := t
    h := #[h[0]! + a, h[1]! + b, h[2]! + cc, h[3]! + d, h[4]! + e]
  return wordBytes h

/-- HMAC-SHA1 (RFC 2104); SHA-1's block size is SHA-256's. -/
def hmacSha1 (key msg : ByteArray) : ByteArray := Id.run do
  let k := if key.size > blockSize then sha1 key else key
  let mut inner := ByteArray.empty
  let mut outer := ByteArray.empty
  for i in [0:blockSize] do
    let b := k[i]?.getD 0
    inner := inner.push (b ^^^ 0x36)
    outer := outer.push (b ^^^ 0x5c)
  return sha1 (outer ++ sha1 (inner ++ msg))

end Angelia.Crypto