import SQLite
import Angelia.Model
import Angelia.Rules
import Angelia.Util
import Angelia.Vault
import Angelia.SecondFactor

/-!
# Storage

SQLite via `leansqlite`. `raw_event` is append-only and is the source of truth; `notification` is
derived from it (one row per raw event) and carries the user's state on top. Each connector thread
opens its own connection; WAL journalling and a busy timeout let them write alongside the server.

Notification content and raw payloads are stored encrypted, and external ids and thread keys as
keyed hashes (see `Angelia.Vault`), so everything here but the keyring needs the server unlocked.
Text search therefore runs over decrypted rows rather than in SQL.
-/

open Lean

namespace Angelia.Db

abbrev Conn := SQLite

def schemaSql : String := "
  CREATE TABLE IF NOT EXISTS raw_event (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    source TEXT NOT NULL,
    external_id TEXT NOT NULL,
    received_at INTEGER NOT NULL,
    -- The sealed external id and payload, as JSON.
    payload BLOB NOT NULL,
    UNIQUE (source, external_id)
  );

  CREATE TABLE IF NOT EXISTS notification (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    raw_id INTEGER NOT NULL UNIQUE REFERENCES raw_event(id) ON DELETE CASCADE,
    source TEXT NOT NULL,
    external_id TEXT NOT NULL,
    kind TEXT NOT NULL,
    thread_key TEXT,
    -- Sealed JSON of the external id, author, title, body, url and thread key.
    content BLOB NOT NULL,
    sent_at INTEGER,
    received_at INTEGER NOT NULL,
    read INTEGER NOT NULL DEFAULT 0,
    archived INTEGER NOT NULL DEFAULT 0,
    starred INTEGER NOT NULL DEFAULT 0,
    UNIQUE (source, external_id)
  );
  CREATE INDEX IF NOT EXISTS notification_order ON notification (archived, received_at DESC);
  CREATE INDEX IF NOT EXISTS notification_thread ON notification (source, thread_key);

  CREATE TABLE IF NOT EXISTS label (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL UNIQUE,
    color TEXT NOT NULL DEFAULT '#6b7280'
  );

  -- `rule_id` is NULL for labels set by hand; a rule re-run replaces only the others.
  CREATE TABLE IF NOT EXISTS notification_label (
    notification_id INTEGER NOT NULL REFERENCES notification(id) ON DELETE CASCADE,
    label_id INTEGER NOT NULL REFERENCES label(id) ON DELETE CASCADE,
    rule_id INTEGER REFERENCES rule(id) ON DELETE CASCADE,
    PRIMARY KEY (notification_id, label_id)
  );
  CREATE INDEX IF NOT EXISTS notification_label_label ON notification_label (label_id);

  CREATE TABLE IF NOT EXISTS rule (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL,
    enabled INTEGER NOT NULL DEFAULT 1,
    position INTEGER NOT NULL DEFAULT 0,
    spec TEXT NOT NULL
  );

  CREATE TABLE IF NOT EXISTS view (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL,
    query TEXT NOT NULL
  );

  -- A connector's durable sync position, opaque JSON owned by the connector.
  CREATE TABLE IF NOT EXISTS cursor (
    source TEXT NOT NULL,
    key TEXT NOT NULL,
    value TEXT NOT NULL,
    updated_at INTEGER NOT NULL,
    PRIMARY KEY (source, key)
  );

  CREATE TABLE IF NOT EXISTS health (
    source TEXT PRIMARY KEY,
    kind TEXT NOT NULL,
    state TEXT NOT NULL,
    detail TEXT,
    last_ok INTEGER,
    last_error TEXT,
    last_error_at INTEGER,
    events INTEGER NOT NULL DEFAULT 0
  );

  CREATE TABLE IF NOT EXISTS session (
    token_hash TEXT PRIMARY KEY,
    created_at INTEGER NOT NULL,
    last_seen INTEGER NOT NULL
  );

  -- Long-lived bearer tokens for non-browser clients. Only the hash is stored.
  CREATE TABLE IF NOT EXISTS api_token (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL,
    token_hash TEXT NOT NULL UNIQUE,
    created_at INTEGER NOT NULL,
    last_used INTEGER,
    scope TEXT NOT NULL DEFAULT '{}'
  );

  -- Credentials a connector maintains itself, such as a rotated OAuth refresh token. Sealed.
  CREATE TABLE IF NOT EXISTS secret (
    source TEXT NOT NULL,
    key TEXT NOT NULL,
    value BLOB NOT NULL,
    PRIMARY KEY (source, key)
  );

  -- What a sign-in needs besides the password. A security key's public key is not secret; an
  -- authenticator app's shared secret is, and is sealed. `handle` is the WebAuthn credential id,
  -- or a random id for an app.
  CREATE TABLE IF NOT EXISTS second_factor (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    kind TEXT NOT NULL,
    name TEXT NOT NULL,
    handle TEXT NOT NULL UNIQUE,
    public_key BLOB,
    sign_count INTEGER NOT NULL DEFAULT 0,
    secret BLOB,
    last_step INTEGER NOT NULL DEFAULT 0,
    created_at INTEGER NOT NULL,
    last_used INTEGER
  );

  -- Small facts about the database itself, such as which normalisers derived its notifications.
  CREATE TABLE IF NOT EXISTS meta (
    key TEXT PRIMARY KEY,
    value TEXT NOT NULL
  );

  -- The data key, wrapped under the configured unlock key, so the server unlocks at start.
  CREATE TABLE IF NOT EXISTS unlock_key (
    id INTEGER PRIMARY KEY CHECK (id = 1),
    wrapped BLOB NOT NULL
  );

  -- The data key, wrapped under a key derived from the login password.
  CREATE TABLE IF NOT EXISTS keyring (
    id INTEGER PRIMARY KEY CHECK (id = 1),
    salt BLOB NOT NULL,
    iterations INTEGER NOT NULL,
    wrapped BLOB NOT NULL
  );
"

/-- Bumped when the schema changes incompatibly. Version 2 is the first with encrypted content. -/
def schemaVersion : Int64 := 2

def connect (path : System.FilePath) : IO Conn := do
  let db ← SQLite.openWith path .readWriteCreate (busyTimeoutMs := 10000)
  db.exec "PRAGMA foreign_keys = ON"
  db.exec "PRAGMA journal_mode = WAL"
  -- Overwrite deleted content instead of leaving it in free pages.
  db.exec "PRAGMA secure_delete = ON"
  pure db

def migrate (db : Conn) : IO Unit := do
  let version ← (← db query!"PRAGMA user_version" as Int64).toArray
  let tables ← (← db query!"SELECT count(*) FROM sqlite_master WHERE name = 'notification'"
    as Int64).toArray
  if tables[0]! != 0 && version[0]! != schemaVersion then
    throw (IO.userError "the database was created by an earlier, unencrypted version of angelia; \
      move it away and let the sources fetch again")
  db.exec schemaSql
  db.exec s!"PRAGMA user_version = {schemaVersion}"

def withTransaction (db : Conn) (act : IO α) : IO α := do
  db.exec "BEGIN IMMEDIATE"
  try
    let r ← act
    db.exec "COMMIT"
    pure r
  catch e =>
    try db.exec "ROLLBACK" catch _ => pure ()
    throw e

private def i64 (n : Int) : Int64 := Int64.ofInt n

/-! ## Raw events and notifications -/

/-- Store a raw event unless one with the same `(source, externalId)` exists. Returns its id when
    it was new. -/
def insertRaw (db : Conn) (source : String) (ev : RawEvent) (now : Int) : IO (Option Int) := do
  let k ← Vault.keys
  let kid := Vault.keyedId k source ev.externalId
  let payload ← Vault.seal k s!"raw\x00{source}\x00{kid}"
    (Json.mkObj [("externalId", ev.externalId), ("payload", ev.payload)]).compress
  let rows ← (← db query!"INSERT INTO raw_event (source, external_id, received_at, payload)
    VALUES ({source}, {kid}, {i64 now}, {payload})
    ON CONFLICT (source, external_id) DO NOTHING RETURNING id" as Int64).toArray
  pure (rows[0]?.map (·.toInt))

/-- Whether a raw event is already stored. Lets a connector skip enriching events it has. -/
def rawExists (db : Conn) (source externalId : String) : IO Bool := do
  let kid := Vault.keyedId (← Vault.keys) source externalId
  let rows ← (← db query!"SELECT 1 FROM raw_event WHERE source = {source}
    AND external_id = {kid}" as Int64).toArray
  pure !rows.isEmpty

private def contentAad (source kid : String) : String := s!"notification\x00{source}\x00{kid}"

/-- Insert the notification derived from raw event `rawId`, or refresh its derived columns if it
    exists (a replay), leaving the user's read/archived/starred state alone. -/
def upsertNotification (db : Conn) (rawId : Int) (source externalId : String)
    (n : NotificationData) (receivedAt : Int) (read archived : Bool) : IO Int := do
  let k ← Vault.keys
  let kid := Vault.keyedId k source externalId
  let threadKey := n.threadKey.map (Vault.keyedId k source)
  let content ← Vault.seal k (contentAad source kid) (Json.mkObj [("externalId", externalId),
    ("author", n.author), ("title", n.title), ("body", n.body), ("url", toJson n.url),
    ("threadKey", toJson n.threadKey)]).compress
  let sentAt := n.sentAt.map i64
  let rows ← (← db query!"INSERT INTO notification
      (raw_id, source, external_id, kind, thread_key, content, sent_at, received_at, read, archived)
    VALUES ({i64 rawId}, {source}, {kid}, {n.kind}, {threadKey}, {content}, {sentAt},
       {i64 receivedAt}, {read}, {archived})
    ON CONFLICT (raw_id) DO UPDATE SET kind = excluded.kind, thread_key = excluded.thread_key,
       content = excluded.content, sent_at = excluded.sent_at
    RETURNING id" as Int64).toArray
  pure rows[0]!.toInt

private def openRaw (k : Vault.Keys) (source kid : String) (payload : ByteArray) :
    IO (String × Json) := do
  let j ← IO.ofExcept (Json.parse (← Vault.open k s!"raw\x00{source}\x00{kid}" payload))
  return (← IO.ofExcept (j.getObjValAs? String "externalId"),
    (j.getObjVal? "payload").toOption.getD .null)

/-- Every raw event of a source (or of all sources), oldest first, for replay. -/
def rawEvents (db : Conn) (source : Option String) :
    IO (Array (Int × String × String × Int × Json)) := do
  let k ← Vault.keys
  let rows ← (← db query!"SELECT id, source, external_id, received_at, payload FROM raw_event
    WHERE {source} IS NULL OR source = {source} ORDER BY id"
    as (Int64 × String × String × Int64 × ByteArray)).toArray
  rows.mapM fun (a, src, kid, d, payload) => do
    let (externalId, p) ← openRaw k src kid payload
    return (a.toInt, src, externalId, d.toInt, p)

private structure NotificationRow where
  id : Int64
  source : String
  keyedId : String
  kind : String
  threadKey : Option String
  content : ByteArray
  sentAt : Option Int64
  receivedAt : Int64
  read : Bool
  archived : Bool
  starred : Bool
  labels : Option String
  time : Int64
deriving SQLite.Row, Inhabited

/-- The decrypted content: the external id and the normalised fields, with the thread key in the
    clear (which rules match on). -/
private def NotificationRow.decrypt (k : Vault.Keys) (r : NotificationRow) :
    IO (String × NotificationData) := do
  let j ← IO.ofExcept (Json.parse (← Vault.open k (contentAad r.source r.keyedId) r.content))
  let str (f : String) := (j.getObjValAs? String f).toOption
  return ((str "externalId").getD "",
    { kind := r.kind, threadKey := str "threadKey", author := (str "author").getD ""
      title := (str "title").getD "", body := (str "body").getD "", url := str "url"
      sentAt := r.sentAt.map (·.toInt), read := r.read })

/-- As the API shows it. The thread key is the keyed hash, which groups just as well. -/
private def NotificationRow.toNotification (k : Vault.Keys) (r : NotificationRow) :
    IO Notification := do
  let (externalId, data) ← r.decrypt k
  return { id := r.id.toInt, source := r.source, externalId
           data := { data with threadKey := r.threadKey }
           receivedAt := r.receivedAt.toInt, read := r.read, archived := r.archived
           starred := r.starred
           labels := ((r.labels.getD "").splitOn ",").filterMap String.toInt? |>.toArray
           time := r.time.toInt }

/-- A notification list query. `none` means "don't filter on this". -/
structure Filter where
  q : Option String := none
  source : Option String := none
  label : Option Int := none
  /-- `inbox` (not archived), `unread`, `archived`, `starred`, or `all`. -/
  state : String := "inbox"
  thread : Option String := none
  /-- `newest` (by the time it was sent), `oldest`, or `arrived` (newest by when it arrived). -/
  sort : String := "newest"
  /-- Keyset pagination: only rows after this `(time, id)` in the sort order. -/
  before : Option (Int × Int) := none
  limit : Nat := 100
deriving Inhabited

/-- The scope's time limit as an SQL argument, evaluated now: a window moves with the clock. -/
private def scopeMinTime (scope : Scope) : IO (Option Int64) := do
  return (scope.minTime (← nowSeconds)).map Int64.ofInt

/-- One page of a notification query without the text search, in the filter's sort order. -/
private def queryPage (db : Conn) (scope : Scope) (f : Filter) (limit : Nat) :
    IO (Array NotificationRow) := do
  let (srcs, lbls) := scope.sqlArgs
  let minT ← scopeMinTime scope
  let label := f.label.map i64
  let bt := f.before.map (i64 ·.1)
  let bid := f.before.map (i64 ·.2)
  let limit : Int64 := Int64.ofNat limit
  (← db query!"SELECT * FROM (SELECT n.id, n.source, n.external_id, n.kind, n.thread_key,
      n.content, n.sent_at, n.received_at, n.read, n.archived, n.starred,
      (SELECT group_concat(label_id) FROM notification_label WHERE notification_id = n.id),
      CASE WHEN {f.sort} = 'arrived' OR n.sent_at IS NULL OR n.sent_at > n.received_at
        THEN n.received_at ELSE n.sent_at END AS t
    FROM notification n
    WHERE ({f.source} IS NULL OR n.source = {f.source})
      AND ({f.thread} IS NULL OR n.thread_key = {f.thread})
      AND ({label} IS NULL OR EXISTS (SELECT 1 FROM notification_label l
            WHERE l.notification_id = n.id AND l.label_id = {label}))
      AND ({srcs} IS NULL OR n.source IN (SELECT value FROM json_each({srcs})))
      AND ({lbls} IS NULL OR EXISTS (SELECT 1 FROM notification_label sl
            WHERE sl.notification_id = n.id AND sl.label_id IN (SELECT value FROM json_each({lbls}))))
      AND ({minT} IS NULL OR (CASE WHEN n.sent_at IS NULL OR n.sent_at > n.received_at
        THEN n.received_at ELSE n.sent_at END) >= {minT})
      AND CASE {f.state}
        WHEN 'inbox' THEN n.archived = 0
        WHEN 'unread' THEN n.archived = 0 AND n.read = 0
        WHEN 'archived' THEN n.archived = 1
        WHEN 'starred' THEN n.starred = 1
        ELSE 1 END)
    WHERE {bt} IS NULL OR CASE WHEN {f.sort} = 'oldest'
      THEN t > {bt} OR (t = {bt} AND id > {bid})
      ELSE t < {bt} OR (t = {bt} AND id < {bid}) END
    ORDER BY CASE WHEN {f.sort} = 'oldest' THEN t ELSE -t END,
      CASE WHEN {f.sort} = 'oldest' THEN id ELSE -id END
    LIMIT {limit}" as NotificationRow).toArray

/-- Run a notification query, newest first. A text search (case-insensitive, on title, body and
    author) decrypts candidates page by page until it has `limit` matches. -/
def listNotifications (db : Conn) (scope : Scope) (f : Filter) : IO (Array Notification) := do
  let k ← Vault.keys
  let limit := min f.limit 500
  let some q := f.q.map String.toLower
    | (← queryPage db scope f limit).mapM (·.toNotification k)
  let pageSize := 500
  let mut out := #[]
  let mut f := f
  repeat
    let rows ← queryPage db scope f pageSize
    for r in rows do
      let n ← r.toNotification k
      let hit (s : String) := (s.toLower.splitOn q).length > 1
      if out.size < limit && (hit n.data.title || hit n.data.body || hit n.data.author) then
        out := out.push n
    if rows.size < pageSize || out.size ≥ limit then break
    f := { f with before := rows.back?.map fun r => (r.time.toInt, r.id.toInt) }
  return out

/-- A notification, if it exists and is visible under `scope`. -/
def getNotification (db : Conn) (scope : Scope) (id : Int) : IO (Option Notification) := do
  let (srcs, lbls) := scope.sqlArgs
  let minT ← scopeMinTime scope
  let rows ← (← db query!"SELECT n.id, n.source, n.external_id, n.kind, n.thread_key, n.content,
      n.sent_at, n.received_at, n.read, n.archived, n.starred,
      (SELECT group_concat(label_id) FROM notification_label WHERE notification_id = n.id),
      CASE WHEN n.sent_at IS NULL OR n.sent_at > n.received_at THEN n.received_at
        ELSE n.sent_at END
    FROM notification n WHERE n.id = {i64 id}
      AND ({srcs} IS NULL OR n.source IN (SELECT value FROM json_each({srcs})))
      AND ({lbls} IS NULL OR EXISTS (SELECT 1 FROM notification_label sl
            WHERE sl.notification_id = n.id AND sl.label_id IN (SELECT value FROM json_each({lbls}))))
      AND ({minT} IS NULL OR (CASE WHEN n.sent_at IS NULL OR n.sent_at > n.received_at
        THEN n.received_at ELSE n.sent_at END) >= {minT})" as NotificationRow).toArray
  rows[0]?.mapM (·.toNotification (← Vault.keys))

/-- Whether any of these notifications is visible under `scope`. -/
def anyVisible (db : Conn) (scope : Scope) (ids : Array Int) : IO Bool := do
  let (srcs, lbls) := scope.sqlArgs
  let minT ← scopeMinTime scope
  let idList := (toJson ids).compress
  let rows ← (← db query!"SELECT 1 FROM notification n
    WHERE n.id IN (SELECT value FROM json_each({idList}))
      AND ({srcs} IS NULL OR n.source IN (SELECT value FROM json_each({srcs})))
      AND ({lbls} IS NULL OR EXISTS (SELECT 1 FROM notification_label sl
            WHERE sl.notification_id = n.id AND sl.label_id IN (SELECT value FROM json_each({lbls}))))
      AND ({minT} IS NULL OR (CASE WHEN n.sent_at IS NULL OR n.sent_at > n.received_at
        THEN n.received_at ELSE n.sent_at END) >= {minT})
    LIMIT 1" as Int64).toArray
  pure !rows.isEmpty

/-- The raw payload behind a notification. -/
def rawPayload (db : Conn) (id : Int) : IO (Option Json) := do
  let rows ← (← db query!"SELECT r.source, r.external_id, r.payload FROM raw_event r
    JOIN notification n ON n.raw_id = r.id WHERE n.id = {i64 id}"
    as (String × String × ByteArray)).toArray
  let k ← Vault.keys
  rows[0]?.mapM fun (src, kid, payload) => return (← openRaw k src kid payload).2

/-- Set the user-state flags given; absent ones are unchanged. Notifications outside `scope` are
    left alone. Returns the ids of those changed. -/
def setFlags (db : Conn) (scope : Scope) (ids : Array Int) (read archived starred : Option Bool) :
    IO (Array Int) := do
  let (srcs, lbls) := scope.sqlArgs
  let minT ← scopeMinTime scope
  withTransaction db do
    let mut changed := #[]
    for id in ids do
      let rows ← (← db query!"UPDATE notification SET read = coalesce({read}, read),
        archived = coalesce({archived}, archived), starred = coalesce({starred}, starred)
        WHERE id IN (SELECT n.id FROM notification n WHERE n.id = {i64 id}
          AND ({srcs} IS NULL OR n.source IN (SELECT value FROM json_each({srcs})))
          AND ({lbls} IS NULL OR EXISTS (SELECT 1 FROM notification_label sl
            WHERE sl.notification_id = n.id AND sl.label_id IN (SELECT value FROM json_each({lbls}))))
      AND ({minT} IS NULL OR (CASE WHEN n.sent_at IS NULL OR n.sent_at > n.received_at
        THEN n.received_at ELSE n.sent_at END) >= {minT}))
        RETURNING id" as Int64).toArray
      changed := changed ++ rows.map (·.toInt)
    return changed

/-- Unread count per source and per label, for the sidebar, counting only what `scope` sees. -/
def counts (db : Conn) (scope : Scope) : IO Json := do
  let (srcs, lbls) := scope.sqlArgs
  let minT ← scopeMinTime scope
  let bySource ← (← db query!"SELECT n.source, count(*) FROM notification n
    WHERE n.archived = 0 AND n.read = 0 AND ({srcs} IS NULL OR n.source IN (SELECT value FROM json_each({srcs})))
      AND ({lbls} IS NULL OR EXISTS (SELECT 1 FROM notification_label sl
            WHERE sl.notification_id = n.id AND sl.label_id IN (SELECT value FROM json_each({lbls}))))
      AND ({minT} IS NULL OR (CASE WHEN n.sent_at IS NULL OR n.sent_at > n.received_at
        THEN n.received_at ELSE n.sent_at END) >= {minT}) GROUP BY n.source"
    as (String × Int64)).toArray
  let byLabel ← (← db query!"SELECT l.label_id, count(*) FROM notification_label l
    JOIN notification n ON n.id = l.notification_id WHERE n.archived = 0 AND n.read = 0
      AND ({lbls} IS NULL OR l.label_id IN (SELECT value FROM json_each({lbls})))
      AND ({srcs} IS NULL OR n.source IN (SELECT value FROM json_each({srcs})))
      AND ({lbls} IS NULL OR EXISTS (SELECT 1 FROM notification_label sl
            WHERE sl.notification_id = n.id AND sl.label_id IN (SELECT value FROM json_each({lbls}))))
      AND ({minT} IS NULL OR (CASE WHEN n.sent_at IS NULL OR n.sent_at > n.received_at
        THEN n.received_at ELSE n.sent_at END) >= {minT})
    GROUP BY l.label_id" as (Int64 × Int64)).toArray
  let total ← (← db query!"SELECT count(*) FROM notification n
    WHERE n.archived = 0 AND n.read = 0 AND ({srcs} IS NULL OR n.source IN (SELECT value FROM json_each({srcs})))
      AND ({lbls} IS NULL OR EXISTS (SELECT 1 FROM notification_label sl
            WHERE sl.notification_id = n.id AND sl.label_id IN (SELECT value FROM json_each({lbls}))))
      AND ({minT} IS NULL OR (CASE WHEN n.sent_at IS NULL OR n.sent_at > n.received_at
        THEN n.received_at ELSE n.sent_at END) >= {minT})" as Int64).toArray
  return Json.mkObj [
    ("unread", total[0]!.toInt),
    ("sources", Json.mkObj (bySource.toList.map fun (s, c) => (s, toJson c.toInt))),
    ("labels", Json.mkObj (byLabel.toList.map fun (l, c) => (toString l.toInt, toJson c.toInt)))]

/-! ## Labels -/

def listLabels (db : Conn) : IO (Array Label) := do
  let rows ← (← db query!"SELECT id, name, color FROM label ORDER BY name"
    as (Int64 × String × String)).toArray
  pure (rows.map fun (id, name, color) => { id := id.toInt, name, color })

def createLabel (db : Conn) (name color : String) : IO Label := do
  let rows ← (← db query!"INSERT INTO label (name, color) VALUES ({name}, {color}) RETURNING id"
    as Int64).toArray
  pure { id := rows[0]!.toInt, name, color }

def updateLabel (db : Conn) (id : Int) (name color : Option String) : IO Unit :=
  db exec!"UPDATE label SET name = coalesce({name}, name), color = coalesce({color}, color)
    WHERE id = {i64 id}"

def deleteLabel (db : Conn) (id : Int) : IO Unit :=
  db exec!"DELETE FROM label WHERE id = {i64 id}"

/-- Attach (or detach) a label by hand. A manual attach takes the label over from a rule, so a
    later rule re-run will not remove it. -/
def setLabel (db : Conn) (notification label : Int) (on : Bool) : IO Unit :=
  if on then
    db exec!"INSERT INTO notification_label (notification_id, label_id, rule_id)
      VALUES ({i64 notification}, {i64 label}, NULL)
      ON CONFLICT DO UPDATE SET rule_id = NULL"
  else
    db exec!"DELETE FROM notification_label
      WHERE notification_id = {i64 notification} AND label_id = {i64 label}"

/-! ## Rules -/

private def toRule (row : Int64 × String × Bool × Int64 × String) : Option Rule :=
  let (id, name, enabled, position, spec) := row
  match Json.parse spec >>= fromJson? with
  | .ok spec => some { id := id.toInt, name, enabled, position := position.toInt, spec }
  | .error _ => none

def listRules (db : Conn) : IO (Array Rule) := do
  let rows ← (← db query!"SELECT id, name, enabled, position, spec FROM rule
    ORDER BY position, id" as (Int64 × String × Bool × Int64 × String)).toArray
  pure (rows.filterMap toRule)

def createRule (db : Conn) (name : String) (enabled : Bool) (position : Int) (spec : RuleSpec) :
    IO Int := do
  let s := (toJson spec).compress
  let rows ← (← db query!"INSERT INTO rule (name, enabled, position, spec)
    VALUES ({name}, {enabled}, {i64 position}, {s}) RETURNING id" as Int64).toArray
  pure rows[0]!.toInt

def updateRule (db : Conn) (id : Int) (name : Option String) (enabled : Option Bool)
    (position : Option Int) (spec : Option RuleSpec) : IO Unit :=
  let s := spec.map fun sp => (toJson sp).compress
  let pos := position.map i64
  db exec!"UPDATE rule SET name = coalesce({name}, name), enabled = coalesce({enabled}, enabled),
    position = coalesce({pos}, position), spec = coalesce({s}, spec) WHERE id = {i64 id}"

def deleteRule (db : Conn) (id : Int) : IO Unit :=
  db exec!"DELETE FROM rule WHERE id = {i64 id}"

/-- Record the labels a rule evaluation produced. Never overrides a label set by hand. -/
def applyOutcomeLabels (db : Conn) (notification : Int) (o : Outcome) : IO Unit := do
  for (rule, label) in o.labels do
    db exec!"INSERT INTO notification_label (notification_id, label_id, rule_id)
      SELECT {i64 notification}, {i64 label}, {i64 rule}
      WHERE EXISTS (SELECT 1 FROM label WHERE id = {i64 label})
      ON CONFLICT DO NOTHING"

/-- Re-run every rule over every notification: drop the rule-assigned labels and assign them
    afresh. Archive/mark-read actions are *not* re-applied, since that would undo what the user did
    to old notifications. Returns how many notifications matched at least one rule. -/
def rerunRules (db : Conn) : IO Nat := withTransaction db do
  let rules ← listRules db
  db.exec "DELETE FROM notification_label WHERE rule_id IS NOT NULL"
  let k ← Vault.keys
  let rows ← (← db query!"SELECT n.id, n.source, n.external_id, n.kind, n.thread_key, n.content,
      n.sent_at, n.received_at, n.read, n.archived, n.starred, NULL, n.received_at
    FROM notification n" as NotificationRow).toArray
  let mut matched := 0
  for r in rows do
    let o := evaluate rules r.source (← r.decrypt k).2
    if !o.labels.isEmpty then
      matched := matched + 1
      applyOutcomeLabels db r.id.toInt o
  return matched

/-! ## Views -/

def listViews (db : Conn) : IO (Array View) := do
  let rows ← (← db query!"SELECT id, name, query FROM view ORDER BY id"
    as (Int64 × String × String)).toArray
  pure (rows.map fun (id, name, q) => { id := id.toInt, name, query := (Json.parse q).toOption.getD .null })

def createView (db : Conn) (name : String) (query : Json) : IO Int := do
  let rows ← (← db query!"INSERT INTO view (name, query) VALUES ({name}, {query.compress})
    RETURNING id" as Int64).toArray
  pure rows[0]!.toInt

def deleteView (db : Conn) (id : Int) : IO Unit :=
  db exec!"DELETE FROM view WHERE id = {i64 id}"

/-! ## Cursors and health -/

def getCursor (db : Conn) (source key : String) : IO (Option Json) := do
  let rows ← (← db query!"SELECT value FROM cursor WHERE source = {source} AND key = {key}"
    as String).toArray
  pure (rows[0]?.bind fun s => (Json.parse s).toOption)

def setCursor (db : Conn) (source key : String) (value : Json) : IO Unit := do
  let now ← nowSeconds
  db exec!"INSERT INTO cursor (source, key, value, updated_at)
    VALUES ({source}, {key}, {value.compress}, {i64 now})
    ON CONFLICT (source, key) DO UPDATE SET value = excluded.value, updated_at = excluded.updated_at"

/-- Record a connector's state. `ok` also stamps `last_ok`; an error stamps `last_error`. -/
def reportHealth (db : Conn) (source kind state : String) (detail : Option String)
    (error : Option String := none) : IO Unit := do
  let now ← nowSeconds
  let ok : Option Int64 := if error.isNone && state != "starting" then some (i64 now) else none
  let errAt : Option Int64 := error.map fun _ => i64 now
  db exec!"INSERT INTO health (source, kind, state, detail, last_ok, last_error, last_error_at)
    VALUES ({source}, {kind}, {state}, {detail}, {ok}, {error}, {errAt})
    ON CONFLICT (source) DO UPDATE SET kind = excluded.kind, state = excluded.state,
      detail = excluded.detail, last_ok = coalesce(excluded.last_ok, last_ok),
      last_error = coalesce(excluded.last_error, last_error),
      last_error_at = coalesce(excluded.last_error_at, last_error_at)"

def countEvents (db : Conn) (source : String) (n : Nat) : IO Unit :=
  db exec!"UPDATE health SET events = events + {Int64.ofNat n} WHERE source = {source}"

def listHealth (db : Conn) : IO Json := do
  let rows ← (← db query!"SELECT source, kind, state, detail, last_ok, last_error, last_error_at,
      events FROM health ORDER BY source"
    as (String × String × String × Option String × Option Int64 × Option String × Option Int64 ×
      Int64)).toArray
  return toJson (rows.map fun (source, kind, state, detail, lastOk, lastError, lastErrorAt, events) =>
    Json.mkObj [("source", source), ("kind", kind), ("state", state), ("detail", toJson detail),
      ("lastOk", toJson (lastOk.map Int64.toInt)), ("lastError", toJson lastError),
      ("lastErrorAt", toJson (lastErrorAt.map Int64.toInt)), ("events", events.toInt)])

/-! ## Connector secrets -/

private def secretAad (source key : String) : String := s!"secret\x00{source}\x00{key}"

def getSecret (db : Conn) (source key : String) : IO (Option String) := do
  let rows ← (← db query!"SELECT value FROM secret WHERE source = {source} AND key = {key}"
    as ByteArray).toArray
  let k ← Vault.keys
  rows[0]?.mapM (Vault.open k (secretAad source key))

def setSecret (db : Conn) (source key value : String) : IO Unit := do
  let sealed ← Vault.seal (← Vault.keys) (secretAad source key) value
  db exec!"INSERT INTO secret (source, key, value) VALUES ({source}, {key}, {sealed})
    ON CONFLICT (source, key) DO UPDATE SET value = excluded.value"

/-! ## Meta -/

def getMeta (db : Conn) (key : String) : IO (Option String) := do
  let rows ← (← db query!"SELECT value FROM meta WHERE key = {key}" as String).toArray
  return rows[0]?

def setMeta (db : Conn) (key value : String) : IO Unit :=
  db exec!"INSERT INTO meta (key, value) VALUES ({key}, {value})
    ON CONFLICT (key) DO UPDATE SET value = excluded.value"

/-! ## Second factors -/

/-- Every second factor, without key material. -/
def listFactors (db : Conn) : IO Json := do
  let rows ← (← db query!"SELECT id, kind, name, created_at, last_used FROM second_factor
    ORDER BY id" as (Int64 × String × String × Int64 × Option Int64)).toArray
  return toJson (rows.map fun (id, kind, name, createdAt, lastUsed) =>
    Json.mkObj [("id", id.toInt), ("kind", kind), ("name", name), ("createdAt", createdAt.toInt),
      ("lastUsed", toJson (lastUsed.map Int64.toInt))])

def webauthnCredentials (db : Conn) : IO (Array (Int × SecondFactor.Credential)) := do
  let rows ← (← db query!"SELECT id, handle, public_key, sign_count FROM second_factor
    WHERE kind = 'webauthn' ORDER BY id" as (Int64 × String × ByteArray × Int64)).toArray
  return rows.map fun (id, handle, publicKey, count) =>
    (id.toInt, { id := handle, publicKey, signCount := count.toNatClampNeg })

private def totpAad (handle : String) : String := s!"totp\x00{handle}"

/-- Every authenticator app's id, secret and last accepted step. -/
def totpSecrets (db : Conn) : IO (Array (Int × ByteArray × Nat)) := do
  let k ← Vault.keys
  let rows ← (← db query!"SELECT id, handle, secret, last_step FROM second_factor
    WHERE kind = 'totp' ORDER BY id" as (Int64 × String × ByteArray × Int64)).toArray
  rows.mapM fun (id, handle, sealed, lastStep) => do
    let hex ← Vault.open k (totpAad handle) sealed
    return (id.toInt, Crypto.unhex hex, lastStep.toNatClampNeg)

def addWebAuthn (db : Conn) (name : String) (c : SecondFactor.Credential) : IO Unit := do
  let now ← nowSeconds
  db exec!"INSERT INTO second_factor (kind, name, handle, public_key, sign_count, created_at)
    VALUES ('webauthn', {name}, {c.id}, {c.publicKey}, {Int64.ofNat c.signCount}, {i64 now})"

def addTotp (db : Conn) (name : String) (secret : ByteArray) : IO Unit := do
  let now ← nowSeconds
  let handle ← randomToken 16
  let sealed ← Vault.seal (← Vault.keys) (totpAad handle) (Crypto.toHex secret)
  db exec!"INSERT INTO second_factor (kind, name, handle, secret, created_at)
    VALUES ('totp', {name}, {handle}, {sealed}, {i64 now})"

/-- Record a successful use: the new signature counter or TOTP step, and when. -/
def factorUsed (db : Conn) (id : Int) (signCount lastStep : Option Nat) : IO Unit := do
  let now ← nowSeconds
  let count := signCount.map Int64.ofNat
  let step := lastStep.map Int64.ofNat
  db exec!"UPDATE second_factor SET last_used = {i64 now},
    sign_count = coalesce({count}, sign_count), last_step = coalesce({step}, last_step)
    WHERE id = {i64 id}"

def deleteFactor (db : Conn) (id : Int) : IO Bool := do
  let rows ← (← db query!"DELETE FROM second_factor WHERE id = {i64 id} RETURNING id"
    as Int64).toArray
  pure !rows.isEmpty

/-- Remove every second factor, for `angelia reset-second-factors`. -/
def deleteAllFactors (db : Conn) : IO Nat := do
  let rows ← (← db query!"DELETE FROM second_factor RETURNING id" as Int64).toArray
  pure rows.size

/-! ## Sessions -/

def createSession (db : Conn) (tokenHash : String) : IO Unit := do
  let now ← nowSeconds
  db exec!"INSERT INTO session (token_hash, created_at, last_seen) VALUES ({tokenHash}, {i64 now}, {i64 now})"

/-- Whether a session is live; touches it if so. -/
def checkSession (db : Conn) (tokenHash : String) (maxIdleSeconds : Int) : IO Bool := do
  let now ← nowSeconds
  let cutoff := i64 (now - maxIdleSeconds)
  let rows ← (← db query!"UPDATE session SET last_seen = {i64 now}
    WHERE token_hash = {tokenHash} AND last_seen > {cutoff} RETURNING 1" as Int64).toArray
  pure !rows.isEmpty

def deleteSession (db : Conn) (tokenHash : String) : IO Unit :=
  db exec!"DELETE FROM session WHERE token_hash = {tokenHash}"

/-! ## API tokens -/

def createToken (db : Conn) (name tokenHash : String) (scope : Scope) : IO Int := do
  let now ← nowSeconds
  let scopeJson := (toJson scope).compress
  let rows ← (← db query!"INSERT INTO api_token (name, token_hash, created_at, scope)
    VALUES ({name}, {tokenHash}, {i64 now}, {scopeJson}) RETURNING id" as Int64).toArray
  pure rows[0]!.toInt

/-- The id and scope of the token with this hash, if there is one; stamps its last use. A scope that
    fails to parse denies the token rather than widening it. -/
def checkToken (db : Conn) (tokenHash : String) : IO (Option (Int × Scope)) := do
  let now ← nowSeconds
  let rows ← (← db query!"UPDATE api_token SET last_used = {i64 now}
    WHERE token_hash = {tokenHash} RETURNING id, scope" as (Int64 × String)).toArray
  pure <| rows[0]?.bind fun (id, scope) =>
    (Json.parse scope >>= fromJson?).toOption.map (id.toInt, ·)

/-- All tokens, without their hashes. -/
def listTokens (db : Conn) : IO Json := do
  let rows ← (← db query!"SELECT id, name, created_at, last_used, scope FROM api_token ORDER BY id"
    as (Int64 × String × Int64 × Option Int64 × String)).toArray
  return toJson (rows.map fun (id, name, createdAt, lastUsed, scope) =>
    Json.mkObj [("id", id.toInt), ("name", name), ("createdAt", createdAt.toInt),
      ("lastUsed", toJson (lastUsed.map Int64.toInt)),
      ("scope", (Json.parse scope).toOption.getD .null)])

def deleteToken (db : Conn) (id : Int) : IO Bool := do
  let rows ← (← db query!"DELETE FROM api_token WHERE id = {i64 id} RETURNING id" as Int64).toArray
  pure !rows.isEmpty

/-! ## Keyring -/

private def wrappedKey (db : Conn) : IO (Option Vault.WrappedKey) := do
  let rows ← (← db query!"SELECT salt, iterations, wrapped FROM keyring"
    as (ByteArray × Int64 × ByteArray)).toArray
  return rows[0]?.map fun (salt, iterations, wrapped) =>
    { salt, iterations := iterations.toNatClampNeg, wrapped }

private def unlockWrapped (db : Conn) : IO (Option ByteArray) := do
  let rows ← (← db query!"SELECT wrapped FROM unlock_key" as ByteArray).toArray
  return rows[0]?

/-- Wrap the data key (the server has to be unlocked) under `unlockKey`, replacing any earlier
    wrapping, so a changed unlock key takes effect at the next sign-in. -/
def wrapForUnlockKey (db : Conn) (unlockKey : ByteArray) : IO Unit := do
  let wrapped ← Vault.wrapUnder unlockKey (← Vault.keys).dataKey
  db exec!"INSERT INTO unlock_key (id, wrapped) VALUES (1, {wrapped})
    ON CONFLICT (id) DO UPDATE SET wrapped = excluded.wrapped"

/-- Wrap the data key under the password too, if it is not yet: the fallback for a database
    that was created unlocked by the unlock key. -/
def ensurePasswordWrap (db : Conn) (password : String) : IO Unit := do
  if (← wrappedKey db).isSome then return
  let w ← Vault.WrappedKey.wrap (← Vault.keys).dataKey password
  db exec!"INSERT INTO keyring (id, salt, iterations, wrapped)
    VALUES (1, {w.salt}, {Int64.ofNat w.iterations}, {w.wrapped})"

/-- Unlock at start with the configured unlock key. A new database gets its data key here.
    Returns why it could not, in which case the first sign-in unlocks with the password -- and
    then wraps the key under the unlock key, which is how an existing database takes one up. -/
def unlockAtStart (db : Conn) (unlockKey : ByteArray) : IO (Except String Unit) := do
  match ← unlockWrapped db with
  | some w =>
    let some key := Vault.unwrapUnder unlockKey w
      | return .error "the unlock key does not open the database key (was it changed?)"
    Vault.install key
    return .ok ()
  | none =>
    if (← wrappedKey db).isSome then
      return .error "the database key is not yet wrapped under the unlock key"
    Vault.install (← IO.getRandomBytes 32)
    wrapForUnlockKey db unlockKey
    return .ok ()

/-- Unlock with the login password: unwrap the data key, or on the first unlock of a new database
    create one. With an unlock key configured, the data key is (re-)wrapped under it as well. -/
def unlock (db : Conn) (password : String) (unlockKey : Option ByteArray := none) : IO Unit := do
  match ← wrappedKey db with
  | some w =>
    let some key := w.unwrap password
      | throw (IO.userError "the password does not unlock the database key; if the password was \
          changed, it has to be changed with `angelia change-password`")
    Vault.install key
  | none =>
    if (← unlockWrapped db).isSome then
      throw (IO.userError "the database key is wrapped only under the unlock key, which did not \
        open it; configure the unlock key it was created with")
    let key ← IO.getRandomBytes 32
    let w ← Vault.WrappedKey.wrap key password
    db exec!"INSERT INTO keyring (id, salt, iterations, wrapped)
      VALUES (1, {w.salt}, {Int64.ofNat w.iterations}, {w.wrapped})"
    Vault.install key
  if let some k := unlockKey then wrapForUnlockKey db k

/-- Re-wrap the data key under a new password. The content stays as it is. -/
def changePassword (db : Conn) (old new : String) : IO Unit := do
  let some w ← wrappedKey db | return
  let some key := w.unwrap old
    | throw (IO.userError "the old password does not unlock the database key")
  let w ← Vault.WrappedKey.wrap key new
  db exec!"UPDATE keyring SET salt = {w.salt}, iterations = {Int64.ofNat w.iterations},
    wrapped = {w.wrapped} WHERE id = 1"

end Angelia.Db