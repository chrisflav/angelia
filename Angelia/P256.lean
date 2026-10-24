/-!
# ECDSA verification on P-256

What a security key signs with: WebAuthn's ES256 (COSE algorithm -7), which every FIDO
authenticator supports, U2F-only ones included. Only verification is needed, and it involves
only public data, so it does not have to run in constant time. Points are in Jacobian
coordinates, so the only inversions are two at the end.
-/

namespace Angelia.P256

def p : Nat := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1
def n : Nat := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
def b : Nat := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
def gx : Nat := 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
def gy : Nat := 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5

/-- `x ^ e mod m`, by squaring. -/
def powMod (x e m : Nat) : Nat := Id.run do
  let mut result := 1
  let mut base := x % m
  let mut e := e
  while e > 0 do
    if e % 2 == 1 then result := result * base % m
    base := base * base % m
    e := e / 2
  return result

/-- Inverse modulo a prime, by Fermat. -/
def invMod (x m : Nat) : Nat := powMod x (m - 2) m

private def sub (x y : Nat) : Nat := (x + p - y % p) % p

/-- A point in Jacobian coordinates, `(X / Z², Y / Z³)`; `Z = 0` is the point at infinity. -/
structure Point where
  x : Nat
  y : Nat
  z : Nat

def Point.infinity : Point := ⟨1, 1, 0⟩

/-- Doubling, using `a = -3` (dbl-2001-b). -/
def Point.double (q : Point) : Point :=
  if q.z == 0 || q.y == 0 then .infinity else
  let delta := q.z * q.z % p
  let gamma := q.y * q.y % p
  let beta := q.x * gamma % p
  let alpha := 3 * (sub q.x delta) * ((q.x + delta) % p) % p
  let x3 := sub (alpha * alpha % p) (8 * beta % p)
  let z3 := sub (sub ((q.y + q.z) * (q.y + q.z) % p) gamma) delta
  let y3 := sub (alpha * sub (4 * beta % p) x3 % p) (8 * (gamma * gamma % p) % p)
  ⟨x3, y3, z3⟩

/-- Addition (add-2007-bl). -/
def Point.add (q r : Point) : Point :=
  if q.z == 0 then r else if r.z == 0 then q else
  let z1z1 := q.z * q.z % p
  let z2z2 := r.z * r.z % p
  let u1 := q.x * z2z2 % p
  let u2 := r.x * z1z1 % p
  let s1 := q.y * r.z % p * z2z2 % p
  let s2 := r.y * q.z % p * z1z1 % p
  let h := sub u2 u1
  let rr := 2 * sub s2 s1 % p
  if h == 0 then (if rr == 0 then q.double else .infinity) else
  let i := 4 * h * h % p
  let j := h * i % p
  let v := u1 * i % p
  let x3 := sub (sub (rr * rr % p) j) (2 * v % p)
  let y3 := sub (rr * sub v x3 % p) (2 * s1 * j % p)
  let z3 := sub (sub ((q.z + r.z) * (q.z + r.z) % p) z1z1) z2z2 * h % p
  ⟨x3, y3, z3⟩

/-- The affine `x` coordinate. -/
def Point.affineX (q : Point) : Nat := q.x * invMod (q.z * q.z % p) p % p

/-- `u * g + v * q`, with both scalars walked together (Shamir's trick). -/
def mulAdd (u : Nat) (g : Point) (v : Nat) (q : Point) : Point := Id.run do
  let gq := g.add q
  let mut acc := Point.infinity
  for i' in [0:256] do
    let i := 255 - i'
    acc := acc.double
    match u.testBit i, v.testBit i with
    | true, true => acc := acc.add gq
    | true, false => acc := acc.add g
    | false, true => acc := acc.add q
    | false, false => pure ()
  return acc

/-- Whether `(x, y)` is a point on the curve `y² = x³ - 3x + b`. -/
def onCurve (x y : Nat) : Bool :=
  x < p && y < p && y * y % p == (sub (x * x % p * x % p) (3 * x % p) + b) % p

private def beNat (bytes : ByteArray) : Nat :=
  bytes.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- The DER prefix of a P-256 `SubjectPublicKeyInfo`, which is what a browser's
    `getPublicKey()` returns for an ES256 credential; the uncompressed point follows it. -/
private def spkiPrefix : ByteArray := ByteArray.mk #[
  0x30, 0x59, 0x30, 0x13, 0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01, 0x06, 0x08, 0x2a,
  0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07, 0x03, 0x42, 0x00, 0x04]

/-- The public point of a P-256 `SubjectPublicKeyInfo`, if it is one and lies on the curve. -/
def parseSpki (der : ByteArray) : Option (Nat × Nat) :=
  if der.size != 91 || der.extract 0 27 != spkiPrefix then none else
  let x := beNat (der.extract 27 59)
  let y := beNat (der.extract 59 91)
  if onCurve x y then some (x, y) else none

/-- `(r, s)` from a DER `Ecdsa-Sig-Value`, the format WebAuthn signatures come in. -/
def parseDerSignature (der : ByteArray) : Option (Nat × Nat) := do
  let int (at_ : Nat) : Option (Nat × Nat) := do
    if der[at_]? != some 0x02 then none
    let len := (← der[at_ + 1]?).toNat
    if len == 0 || len > 33 || at_ + 2 + len > der.size then none
    return (beNat (der.extract (at_ + 2) (at_ + 2 + len)), at_ + 2 + len)
  if der[0]? != some 0x30 || (← der[1]?).toNat != der.size - 2 then none
  let (r, next) ← int 2
  let (s, stop) ← int next
  if stop != der.size then none
  return (r, s)

/-- Verify an ECDSA signature `(r, s)` over a message whose SHA-256 is `digest`. -/
def verify (key : Nat × Nat) (digest : ByteArray) (r s : Nat) : Bool :=
  if r == 0 || r >= n || s == 0 || s >= n then false else
  let e := beNat digest % n
  let w := invMod s n
  let point := mulAdd (e * w % n) ⟨gx, gy, 1⟩ (r * w % n) ⟨key.1, key.2, 1⟩
  point.z != 0 && point.affineX % n == r

end Angelia.P256