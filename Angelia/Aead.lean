/-!
# ChaCha20-Poly1305

The AEAD construction of RFC 8439, used to encrypt what the database stores. `seal` draws a fresh
random 96-bit nonce per message and returns `nonce ‖ ciphertext ‖ tag`; `open` checks the tag
before returning anything. The associated data binds a ciphertext to where it is stored, so one
row's ciphertext cannot be moved into another.
-/

namespace Angelia.Aead

private def rotl (x n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

private def le32 (b : ByteArray) (i : Nat) : UInt32 :=
  b[i]!.toUInt32 ||| (b[i + 1]!.toUInt32 <<< 8) ||| (b[i + 2]!.toUInt32 <<< 16) |||
    (b[i + 3]!.toUInt32 <<< 24)

private def quarter (s : Array UInt32) (a b c d : Nat) : Array UInt32 := Id.run do
  let mut s := s
  s := s.set! a (s[a]! + s[b]!); s := s.set! d (rotl (s[d]! ^^^ s[a]!) 16)
  s := s.set! c (s[c]! + s[d]!); s := s.set! b (rotl (s[b]! ^^^ s[c]!) 12)
  s := s.set! a (s[a]! + s[b]!); s := s.set! d (rotl (s[d]! ^^^ s[a]!) 8)
  s := s.set! c (s[c]! + s[d]!); s := s.set! b (rotl (s[b]! ^^^ s[c]!) 7)
  return s

/-- The ChaCha20 block function: twenty rounds over the state, added back to it. -/
private def block (init : Array UInt32) : Array UInt32 := Id.run do
  let mut x := init
  for _ in [0:10] do
    x := quarter x 0 4 8 12; x := quarter x 1 5 9 13
    x := quarter x 2 6 10 14; x := quarter x 3 7 11 15
    x := quarter x 0 5 10 15; x := quarter x 1 6 11 12
    x := quarter x 2 7 8 13; x := quarter x 3 4 9 14
  return (init.zip x).map fun (a, b) => a + b

private def initState (key nonce : ByteArray) : Array UInt32 :=
  #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] ++
    (Array.range 8).map (fun i => le32 key (4 * i)) ++ #[0] ++
    (Array.range 3).map (fun i => le32 nonce (4 * i))

/-- XOR `data` with the ChaCha20 key stream starting at block `counter`. -/
def chacha20 (key nonce : ByteArray) (counter : UInt32) (data : ByteArray) : ByteArray := Id.run do
  let st := initState key nonce
  let mut out := ByteArray.emptyWithCapacity data.size
  for j in [0:(data.size + 63) / 64] do
    let ks := block (st.set! 12 (counter + j.toUInt32))
    for i in [j * 64:min data.size (j * 64 + 64)] do
      let w := ks[(i % 64) / 4]!
      out := out.push (data[i]! ^^^ (w >>> (8 * (i % 4)).toUInt32).toUInt8)
  return out

private def leNat (b : ByteArray) (start stop : Nat) : Nat := Id.run do
  let mut n := 0
  for i in [start:stop] do
    n := n + (b[i]!.toNat <<< (8 * (i - start)))
  return n

/-- The Poly1305 one-time authenticator over `msg` under a 32-byte one-time key. -/
def poly1305 (key msg : ByteArray) : ByteArray := Id.run do
  let r := leNat key 0 16 &&& 0x0ffffffc0ffffffc0ffffffc0fffffff
  let s := leNat key 16 32
  let p := 2 ^ 130 - 5
  let mut acc := 0
  for j in [0:(msg.size + 15) / 16] do
    let stop := min msg.size (j * 16 + 16)
    let n := leNat msg (j * 16) stop + 2 ^ (8 * (stop - j * 16))
    acc := (acc + n) * r % p
  let tag := (acc + s) % 2 ^ 128
  return ByteArray.mk ((Array.range 16).map fun i => (tag >>> (8 * i)).toUInt8)

private def le64 (n : Nat) : ByteArray :=
  ByteArray.mk ((Array.range 8).map fun i => (n >>> (8 * i)).toUInt8)

private def pad16 (b : ByteArray) : ByteArray :=
  ByteArray.mk (Array.replicate ((16 - b.size % 16) % 16) 0)

private def tag (key nonce aad ct : ByteArray) : ByteArray :=
  let otk := (chacha20 key nonce 0 (ByteArray.mk (Array.replicate 32 0)))
  poly1305 otk (aad ++ pad16 aad ++ ct ++ pad16 ct ++ le64 aad.size ++ le64 ct.size)

/-- Encrypt and authenticate under an explicit nonce: `ciphertext ‖ tag`. -/
def encrypt (key nonce aad plaintext : ByteArray) : ByteArray :=
  let ct := chacha20 key nonce 1 plaintext
  ct ++ tag key nonce aad ct

/-- Check and decrypt `ciphertext ‖ tag`. -/
def decrypt (key nonce aad sealed : ByteArray) : Option ByteArray := Id.run do
  if sealed.size < 16 then return none
  let ct := sealed.extract 0 (sealed.size - 16)
  let expected := tag key nonce aad ct
  let mut diff : UInt8 := 0
  for i in [0:16] do
    diff := diff ||| (expected[i]! ^^^ sealed[ct.size + i]!)
  if diff != 0 then return none
  return some (chacha20 key nonce 1 ct)

/-- Encrypt under a fresh random nonce: `nonce ‖ ciphertext ‖ tag`. -/
def «seal» (key aad plaintext : ByteArray) : IO ByteArray := do
  let nonce ← IO.getRandomBytes 12
  return nonce ++ encrypt key nonce aad plaintext

/-- Inverse of `seal`; `none` if the data was altered, or sealed under another key or `aad`. -/
def «open» (key aad sealed : ByteArray) : Option ByteArray :=
  if sealed.size < 28 then none
  else decrypt key (sealed.extract 0 12) aad (sealed.extract 12 sealed.size)

end Angelia.Aead