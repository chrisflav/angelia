import Lean.Data.Json
import Angelia.Http.Curl

/-!
# OAuth 2 token refresh

For mail providers that accept only OAuth (Microsoft 365): exchange a refresh token for an access
token at the provider's token endpoint (RFC 6749 §6). Getting the first refresh token takes a
human signing in once, which happens outside angelia; from then on angelia renews by itself.
Providers may rotate the refresh token on every use, so the caller has to keep the newest one.
-/

open Lean

namespace Angelia.OAuth2

/-- A provider's token endpoint and the public client to present to it. -/
structure Client where
  tokenUrl : String
  clientId : String
  scope : String
deriving Inhabited, Repr, FromJson, ToJson

/-- What a successful refresh returns. -/
structure Grant where
  accessToken : String
  /-- A replacement refresh token, when the provider rotates them. -/
  refreshToken : Option String
  /-- Seconds the access token is valid for. -/
  expiresIn : Nat
deriving Inhabited, Repr, BEq

/-- `application/x-www-form-urlencoded` escaping: everything but the unreserved characters. -/
def formEncode (s : String) : String :=
  String.join (s.toUTF8.toList.map fun b =>
    let c := Char.ofNat b.toNat
    if c.isAlphanum || c == '-' || c == '.' || c == '_' || c == '~' then c.toString
    else "%" ++ (hexOf (ByteArray.mk #[b])).toUpper)

/-- Read a token endpoint's answer: the grant, or the provider's error and its description. -/
def parseResponse (status : Nat) (body : String) : Except String Grant := do
  let j ← Json.parse body
  if status != 200 then
    let err := (j.getObjValAs? String "error").toOption.getD s!"HTTP {status}"
    let desc := (j.getObjValAs? String "error_description").toOption.getD ""
    -- Microsoft's descriptions run to several lines of trace and correlation ids.
    throw s!"{err}: {(desc.splitOn "\r\n").headD desc}"
  return { accessToken := ← j.getObjValAs? String "access_token"
           refreshToken := (j.getObjValAs? String "refresh_token").toOption
           expiresIn := (j.getObjValAs? Nat "expires_in").toOption.getD 3600 }

def Client.refresh (c : Client) (refreshToken : String) : IO (Except String Grant) := do
  let form := "&".intercalate [
    s!"grant_type=refresh_token", s!"client_id={formEncode c.clientId}",
    s!"refresh_token={formEncode refreshToken}", s!"scope={formEncode c.scope}"]
  let r ← Http.request "POST" c.tokenUrl #[("Content-Type", "application/x-www-form-urlencoded")]
    (some form)
  return parseResponse r.status r.body

end Angelia.OAuth2