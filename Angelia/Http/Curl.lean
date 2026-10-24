import Angelia.Util

/-!
# Outbound HTTPS

`Std.Http` is a server only and Lean has no TLS, so outbound requests go through the `curl`
binary, as in taxis. Unlike there, connectors need response headers (`Last-Modified`,
`X-Poll-Interval`), so they are captured too. Request headers and the body are written to
curl's stdin as a config file (`--config -`) rather than to its argument list, so tokens never
show up in `ps`.
-/

namespace Angelia.Http

structure Response where
  status : Nat
  /-- Header names lowercased. -/
  headers : Array (String × String)
  body : String
deriving Repr, Inhabited

def Response.header? (r : Response) (name : String) : Option String :=
  r.headers.find? (·.1 == name.toLower) |>.map (·.2)

/-- Header fields of a header block (its status line skipped), names lowercased. -/
def parseHeaderBlock (head : String) : Array (String × String) :=
  ((head.splitOn "\r\n").drop 1).toArray.filterMap fun l =>
    match l.splitOn ":" with
    | k :: v@(_ :: _) => some (k.trimAscii.toString.toLower, (":".intercalate v).trimAscii.toString)
    | _ => none

/-- Split `curl -i` output into the final header block and the body. With `-i` every response in
    a `100 Continue` or redirect chain contributes a header block; the last one is the one that
    matters. -/
def parseHeadersAndBody (out : String) (fuel : Nat) : Array (String × String) × String :=
  match out.splitOn "\r\n\r\n", fuel with
  | head :: rest@(_ :: _), fuel + 1 =>
    let body := "\r\n\r\n".intercalate rest
    if body.startsWith "HTTP/" then parseHeadersAndBody body fuel else (parseHeaderBlock head, body)
  | head :: rest@(_ :: _), 0 => (parseHeaderBlock head, "\r\n\r\n".intercalate rest)
  | _, _ => (#[], out)

/-- A string in curl's config syntax: double-quoted, with backslash escapes. -/
def configQuote (s : String) : String :=
  let esc (c : Char) : String := match c with
    | '\\' => "\\\\" | '"' => "\\\"" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
    | c => c.toString
  "\"" ++ String.join (s.toList.map esc) ++ "\""

/-- The config curl reads from stdin: one `header` line per header, and the body. -/
def configFor (headers : Array (String × String)) (body : Option String) : String :=
  String.join (headers.toList.map fun (k, v) => s!"header = {configQuote s!"{k}: {v}"}\n") ++
    (body.map fun b => s!"data-binary = {configQuote b}\n").getD ""

def request (method url : String) (headers : Array (String × String) := #[])
    (body : Option String := none) (timeoutSeconds : Nat := 60) : IO Response := do
  let args := #["-sS", "-i", "--max-time", toString timeoutSeconds, "-X", method,
    "-w", "\n%{http_code}", "--config", "-", url]
  let child ← IO.Process.spawn {
    cmd := "curl", args, stdin := .piped, stdout := .piped, stderr := .piped }
  -- The handle is closed when it is dropped at the end of this block, which ends curl's input.
  let child ← do
    let (stdin, child) ← child.takeStdin
    stdin.putStr (configFor headers body)
    stdin.flush
    pure child
  let stderrTask ← IO.asTask child.stderr.readToEnd .dedicated
  let stdout ← child.stdout.readToEnd
  let stderr ← IO.ofExcept stderrTask.get
  let exitCode ← child.wait
  if exitCode != 0 then
    throw (IO.userError s!"curl {url}: exit {exitCode}: {stderr.trimAscii}")
  let lines := stdout.splitOn "\n"
  let status := (lines.getLast?.bind (·.trimAscii.toString.toNat?)).getD 0
  let (hs, body) := parseHeadersAndBody ("\n".intercalate lines.dropLast) 5
  return { status, headers := hs, body }

end Angelia.Http