import Lean.Data.Json
import Std.Time

/-!
# Small shared helpers
-/

namespace Angelia

/-- Read bytes as Latin-1: one character per byte. Lossless, which is what makes it the right way
    to hold protocol data (mail, IMAP lines) whose character set is not yet known. -/
def latin1 (b : ByteArray) : String :=
  String.ofList (b.toList.map fun x => Char.ofNat x.toNat)

/-- Inverse of `latin1` for byte strings; characters above U+00FF are written as UTF-8. -/
def toBytes (s : String) : ByteArray :=
  s.toList.foldl (fun out c => if c.toNat < 256 then out.push c.toNat.toUInt8
    else out ++ c.toString.toUTF8) ByteArray.empty

/-- Current Unix time in seconds. -/
def nowSeconds : IO Int := do
  return (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val

/-- Log a line to stderr with a component prefix. -/
def log (component msg : String) : IO Unit :=
  IO.eprintln s!"[angelia:{component}] {msg}"

/-- Lowercase hex of a byte array. -/
def hexOf (b : ByteArray) : String :=
  let digits := "0123456789abcdef".toList
  String.ofList (b.toList.flatMap fun x => [digits[x.toNat / 16]!, digits[x.toNat % 16]!])

/-- A random token of `n` bytes, hex encoded. -/
def randomToken (n : Nat := 32) : IO String :=
  return hexOf (← IO.getRandomBytes n.toUSize)

/-- Truncate a string to at most `n` characters. -/
def truncate (s : String) (n : Nat) : String :=
  if s.length ≤ n then s else (s.take n).toString ++ "…"

/-- Days since 1970-01-01 of a proleptic Gregorian date (Howard Hinnant's `days_from_civil`). -/
def daysFromCivil (y : Int) (m d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400
  let mp : Int := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- Parse an ISO 8601 UTC timestamp as GitHub writes them (`2026-10-20T12:34:56Z`) into Unix
    seconds. A numeric offset suffix is honoured; fractional seconds are ignored. -/
def parseIso8601 (s : String) : Option Int := do
  match s.splitOn "T" with
  | [date, time] =>
    let (y, m, d) ← match date.splitOn "-" |>.map String.toNat? with
      | [some y, some m, some d] => some (y, m, d)
      | _ => none
    let (clock, offset) : String × Int :=
      if time.endsWith "Z" then ((time.dropEnd 1).toString, 0)
      else match time.splitOn "+", time.splitOn "-" with
        | [c, o], _ => (c, offsetMinutes o)
        | _, [c, o] => (c, -offsetMinutes o)
        | _, _ => (time, 0)
    let clock := (clock.splitOn ".").headD clock
    let (hh, mm, ss) ← match clock.splitOn ":" |>.map String.toNat? with
      | [some h, some mi, some sec] => some (h, mi, sec)
      | [some h, some mi] => some (h, mi, 0)
      | _ => none
    return daysFromCivil y m d * 86400 + hh * 3600 + mm * 60 + ss - offset * 60
  | _ => none
where
  offsetMinutes (o : String) : Int :=
    match o.splitOn ":" |>.map String.toNat? with
    | [some h, some m] => h * 60 + m
    | _ => 0

end Angelia