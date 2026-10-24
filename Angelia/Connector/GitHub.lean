import Angelia.Ingest
import Angelia.Http.Curl

/-!
# GitHub notifications

GitHub offers no push channel for a user's own notifications (webhooks are per repository or
organisation), so this polls `GET /notifications`, the way GitHub asks clients to: conditionally,
with `If-Modified-Since`, so an unchanged inbox costs a `304` that does not count against the rate
limit, and no more often than the `X-Poll-Interval` it returns (60 s).

A thread's every update is its own event (`externalId` = thread id + `updated_at`), grouped back
together by `threadKey`. New events are enriched with the latest comment when there is one, so the
notification says what happened rather than only that something did.

Settings: `token` / `tokenCommand` (a classic PAT with the `notifications` scope, or a fine-grained
one with notification access), `intervalSeconds` (60), `fetchComments` (true), `apiUrl`
(`https://api.github.com`, for GitHub Enterprise).
-/

open Lean

namespace Angelia.Connector.GitHub

/-- The web page for an API URL, e.g. `…/repos/o/r/pulls/12` → `https://github.com/o/r/pull/12`. -/
def htmlUrl (apiUrl : String) : Option String := do
  let path ← (apiUrl.splitOn "/repos/")[1]?
  let parts := path.splitOn "/"
  match parts with
  | [o, r, "pulls", n] => some s!"https://github.com/{o}/{r}/pull/{n}"
  | [o, r, "issues", n] => some s!"https://github.com/{o}/{r}/issues/{n}"
  | [o, r, "commits", sha] => some s!"https://github.com/{o}/{r}/commit/{sha}"
  | [o, r, "releases", _] => some s!"https://github.com/{o}/{r}/releases"
  | [o, r, "discussions", n] => some s!"https://github.com/{o}/{r}/discussions/{n}"
  | o :: r :: _ => some s!"https://github.com/{o}/{r}"
  | _ => none

def normalize (thread : Json) : Except String NotificationData := do
  let subject ← thread.getObjVal? "subject"
  let title ← subject.getObjValAs? String "title"
  let kind := (subject.getObjValAs? String "type").toOption.getD "Notification"
  let repo := ((thread.getObjVal? "repository") >>= (·.getObjValAs? String "full_name")).toOption.getD ""
  let reason := (thread.getObjValAs? String "reason").toOption.getD ""
  let comment := (thread.getObjVal? "comment").toOption
  let commentBody := comment.bind fun c => (c.getObjValAs? String "body").toOption
  let commentUser := comment.bind fun c => (c.getObjVal? "user" >>= (·.getObjValAs? String "login")).toOption
  let commentUrl := comment.bind fun c => (c.getObjValAs? String "html_url").toOption
  let subjectUrl := (subject.getObjValAs? String "url").toOption.bind htmlUrl
  let repoUrl := ((thread.getObjVal? "repository") >>= (·.getObjValAs? String "html_url")).toOption
  return {
    kind
    threadKey := (thread.getObjValAs? String "id").toOption
    author := match commentUser with
      | some u => s!"{u} · {repo}"
      | none => repo
    title
    body := match commentBody with
      | some b => truncate b 20000
      | none => s!"{kind} — {reason.replace "_" " "}"
    url := commentUrl.orElse fun _ => subjectUrl.orElse fun _ => repoUrl
    sentAt := (thread.getObjValAs? String "updated_at").toOption.bind parseIso8601
    -- GitHub's unread flag is about GitHub's own inbox; a new update is new here.
    read := false }

structure Settings where
  token : String
  intervalSeconds : Nat
  fetchComments : Bool
  apiUrl : String

def Settings.load (j : Json) : IO Settings := do
  let some token ← secret j "token" | throw (IO.userError "github: 'token' or 'tokenCommand' is required")
  return {
    token
    intervalSeconds := (j.getObjValAs? Nat "intervalSeconds").toOption.getD 60
    fetchComments := (j.getObjValAs? Bool "fetchComments").toOption.getD true
    apiUrl := (j.getObjValAs? String "apiUrl").toOption.getD "https://api.github.com" }

def headers (s : Settings) : Array (String × String) :=
  #[("Authorization", s!"Bearer {s.token}"), ("Accept", "application/vnd.github+json"),
    ("X-GitHub-Api-Version", "2022-11-28"), ("User-Agent", "angelia-notifications")]

/-- The `rel="next"` target of a `Link` header. -/
def nextLink (link : String) : Option String :=
  (link.splitOn ",").findSome? fun part =>
    match part.splitOn ";" with
    | [url, rel] =>
      if (rel.splitOn "rel=\"next\"").length > 1 then
        some ((url.trimAscii.toString.replace "<" "").replace ">" "")
      else none
    | _ => none

def externalId (thread : Json) : String :=
  let id := (thread.getObjValAs? String "id").toOption.getD "?"
  let updated := (thread.getObjValAs? String "updated_at").toOption.getD ""
  s!"{id}@{updated}"

/-- One poll. Returns the interval GitHub asks for before the next one. -/
def poll (ctx : ConnectorCtx) (s : Settings) : IO Nat := do
  let lastModified := (← ctx.getCursor "poll").bind fun j => (j.getObjValAs? String "lastModified").toOption
  let cond := match lastModified with
    | some lm => #[("If-Modified-Since", lm)]
    | none => #[]
  let first ← Http.request "GET" s!"{s.apiUrl}/notifications?all=false&per_page=50" (headers s ++ cond)
  let interval := max s.intervalSeconds ((first.header? "x-poll-interval" >>= String.toNat?).getD 60)
  if first.status == 304 then
    ctx.health "ok" (some "no changes")
    return interval
  if first.status != 200 then
    throw (IO.userError s!"GitHub answered {first.status}: {truncate first.body 300}")
  -- Follow pagination, a bounded number of pages.
  let mut threads : Array Json := #[]
  let mut resp := first
  for _ in [0:10] do
    match Json.parse resp.body with
    | .ok (.arr ts) => threads := threads ++ ts
    | _ => throw (IO.userError "GitHub returned something other than a list")
    match resp.header? "link" >>= nextLink with
    | some next => resp ← Http.request "GET" next (headers s)
    | none => break
  let mut events : Array RawEvent := #[]
  for t in threads do
    let eid := externalId t
    if ← Db.rawExists ctx.db ctx.name eid then continue
    let mut payload := t
    if s.fetchComments then
      let commentUrl := (t.getObjVal? "subject" >>= (·.getObjValAs? String "latest_comment_url")).toOption
      if let some url := commentUrl then
        try
          let r ← Http.request "GET" url (headers s)
          if r.status == 200 then
            if let .ok c := Json.parse r.body then payload := payload.setObjVal! "comment" c
        catch e => ctx.log s!"could not fetch {url}: {e}"
    events := events.push { externalId := eid, payload }
  let n ← ctx.ingest events
  if n > 0 then ctx.log s!"{n} new"
  if let some lm := first.header? "last-modified" then
    ctx.setCursor "poll" (Json.mkObj [("lastModified", lm)])
  ctx.health "ok" (some s!"{threads.size} unread thread(s) on GitHub")
  return interval

partial def run (ctx : ConnectorCtx) : IO Unit := do
  let s ← Settings.load ctx.source.settings
  ctx.supervise do
    let rec loop : IO Unit := do
      let interval ← poll ctx s
      if ← ctx.sleep interval then loop
    loop

end Angelia.Connector.GitHub