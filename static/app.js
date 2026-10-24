"use strict";

// Everything shown here comes from other people (mail, GitHub, ...), so the DOM is only ever
// built with `h()` — text goes in as text nodes, never through innerHTML.

const state = {
  filter: { state: "inbox", source: null, label: null, q: "", thread: null },
  view: "list", // or "rules" | "sources"
  items: [],
  next: null,
  selected: -1,
  labels: [],
  views: [],
  counts: { unread: 0, sources: {}, labels: {} },
  sources: { configured: [], health: [] },
  group: localStorage.getItem("angelia.group") || "",
};

function h(tag, attrs, ...children) {
  const el = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs || {})) {
    if (v === null || v === undefined || v === false) continue;
    if (k.startsWith("on")) el.addEventListener(k.slice(2), v);
    else if (k === "style") Object.assign(el.style, v);
    else el.setAttribute(k, v === true ? "" : v);
  }
  for (const c of children.flat()) {
    if (c === null || c === undefined || c === false) continue;
    el.append(c instanceof Node ? c : document.createTextNode(String(c)));
  }
  return el;
}

const $ = (id) => document.getElementById(id);

async function api(method, path, body) {
  const res = await fetch("/api/" + path, {
    method,
    headers: body ? { "Content-Type": "application/json" } : {},
    body: body ? JSON.stringify(body) : undefined,
    credentials: "same-origin",
  });
  if (res.status === 401 && path !== "login") { showLogin(); throw new Error("unauthorized"); }
  const data = await res.json().catch(() => ({}));
  if (data.locked && path !== "login") { showLogin(data.error); throw new Error("locked"); }
  if (!res.ok) throw new Error(data.error || res.statusText);
  return data;
}

/* ---------- login ---------- */

function showLogin(message) {
  events?.close();
  $("login-error").textContent = message || "";
  $("app").hidden = true;
  $("login").hidden = false;
  $("password").focus();
}

$("login-form")?.addEventListener("submit", async (e) => {
  e.preventDefault();
  const button = e.target.querySelector("button");
  button.disabled = true;
  try {
    await api("POST", "login", { password: $("password").value });
    $("password").value = "";
    $("login-error").textContent = "";
    start();
  } catch (err) {
    $("login-error").textContent = err.message;
  } finally {
    button.disabled = false;
  }
});

/* ---------- data ---------- */

function query(extra) {
  const f = state.filter;
  const p = new URLSearchParams();
  p.set("state", f.state);
  if (f.source) p.set("source", f.source);
  if (f.label) p.set("label", f.label);
  if (f.q) p.set("q", f.q);
  if (f.thread) p.set("thread", f.thread);
  for (const [k, v] of Object.entries(extra || {})) p.set(k, v);
  return p.toString();
}

async function loadList(keepSelection) {
  const selectedId = state.items[state.selected]?.id;
  const data = await api("GET", "notifications?" + query({ limit: 100 }));
  state.items = data.notifications;
  state.next = data.next;
  state.selected = keepSelection ? state.items.findIndex((n) => n.id === selectedId) : -1;
  renderList();
}

async function loadMore() {
  if (!state.next) return;
  const data = await api("GET", "notifications?" + query({ limit: 100, before: state.next }));
  state.items = state.items.concat(data.notifications);
  state.next = data.next;
  renderList();
}

async function loadMeta() {
  const [labels, views, counts, sources] = await Promise.all([
    api("GET", "labels"), api("GET", "views"), api("GET", "counts"), api("GET", "sources"),
  ]);
  Object.assign(state, { labels, views, counts, sources });
  renderSidebar();
}

async function refresh() {
  await Promise.all([loadList(true), loadMeta()]);
  if (state.view === "list" && state.selected >= 0) renderDetail();
}

/* ---------- sidebar ---------- */

function navItem(label, active, onclick, count, extra) {
  return h("div", { class: "nav-item" + (active ? " active" : ""), onclick },
    extra?.before, h("span", {}, label),
    count ? h("span", { class: "count" }, count) : null, extra?.after);
}

function setFilter(f) {
  state.view = "list";
  state.filter = { state: "inbox", source: null, label: null, q: state.filter.q, thread: null, ...f };
  $("search").value = state.filter.q;
  loadList(false).then(renderSidebar);
  $("detail").replaceChildren();
}

function renderSidebar() {
  const f = state.filter;
  const plain = state.view === "list" && !f.source && !f.label && !f.thread;
  const health = Object.fromEntries(state.sources.health.map((s) => [s.source, s]));
  const items = [
    navItem("Inbox", plain && f.state === "inbox", () => setFilter({}), state.counts.unread),
    navItem("Unread", plain && f.state === "unread", () => setFilter({ state: "unread" })),
    navItem("Starred", plain && f.state === "starred", () => setFilter({ state: "starred" })),
    navItem("Archived", plain && f.state === "archived", () => setFilter({ state: "archived" })),
    navItem("Everything", plain && f.state === "all", () => setFilter({ state: "all" })),
  ];
  if (state.views.length) {
    items.push(h("h2", {}, "Views"));
    for (const v of state.views) {
      items.push(navItem(v.name, false, () => setFilter(v.query), null, {
        after: h("span", { class: "x", title: "Delete view", onclick: async (e) => {
          e.stopPropagation();
          await api("DELETE", "views/" + v.id);
          loadMeta();
        } }, "×"),
      }));
    }
  }
  items.push(h("h2", {}, "Labels", h("button", { title: "New label", onclick: newLabel }, "+")));
  for (const l of state.labels) {
    items.push(navItem(l.name, state.view === "list" && f.label === l.id,
      () => setFilter({ label: l.id }), state.counts.labels[l.id], {
        before: h("span", { class: "dot", style: { background: l.color } }),
        after: h("span", { class: "x", title: "Delete label", onclick: async (e) => {
          e.stopPropagation();
          if (!confirm(`Delete label "${l.name}"?`)) return;
          await api("DELETE", "labels/" + l.id);
          refresh();
        } }, "×"),
      }));
  }
  items.push(h("h2", {}, "Sources"));
  for (const s of state.sources.configured) {
    const st = health[s.name]?.state || (s.enabled ? "starting" : "disabled");
    items.push(navItem(s.name, state.view === "list" && f.source === s.name,
      () => setFilter({ source: s.name }), state.counts.sources[s.name], {
        before: h("span", { class: "dot " + st, title: st }),
      }));
  }
  items.push(h("h2", {}, "Settings"));
  items.push(navItem("Rules", state.view === "rules", showRules));
  items.push(navItem("Source health", state.view === "sources", showSources));
  items.push(navItem("API tokens", state.view === "tokens", () => showTokens()));
  $("sidebar").replaceChildren(...items);
}

async function newLabel() {
  const name = prompt("Label name");
  if (!name) return;
  const palette = ["#2f5bd3", "#2e8b57", "#c0392b", "#d4a017", "#8e44ad", "#16a085", "#d35400"];
  await api("POST", "labels", { name, color: palette[state.labels.length % palette.length] });
  loadMeta();
}

/* ---------- list ---------- */

function when(ts) {
  if (!ts) return "";
  const d = new Date(ts * 1000);
  const now = new Date();
  if (d.toDateString() === now.toDateString())
    return d.toLocaleTimeString([], { hour: "2-digit", minute: "2-digit" });
  return d.toLocaleDateString([], { month: "short", day: "numeric",
    year: d.getFullYear() === now.getFullYear() ? undefined : "numeric" });
}

function labelChips(n) {
  const byId = Object.fromEntries(state.labels.map((l) => [l.id, l]));
  return h("span", { class: "chips" }, n.labels.map((id) => byId[id]).filter(Boolean)
    .map((l) => h("span", { class: "chip", style: { background: l.color } }, l.name)));
}

function groupKey(n) {
  switch (state.group) {
    case "thread": return n.source + "\u0000" + (n.threadKey || n.id);
    case "source": return n.source;
    case "day": return new Date((n.sentAt || n.receivedAt) * 1000).toDateString();
    default: return "";
  }
}

function groupTitle(n, members) {
  switch (state.group) {
    case "thread": return `${n.title} · ${members} message${members === 1 ? "" : "s"}`;
    case "source": return n.source;
    case "day": return new Date((n.sentAt || n.receivedAt) * 1000).toLocaleDateString([],
      { weekday: "long", month: "long", day: "numeric" });
    default: return "";
  }
}

/** Indices of `state.items` in display order, with group headings. */
function displayOrder() {
  if (!state.group) return state.items.map((n, i) => ({ i }));
  const groups = new Map();
  state.items.forEach((n, i) => {
    const k = groupKey(n);
    if (!groups.has(k)) groups.set(k, []);
    groups.get(k).push(i);
  });
  const out = [];
  for (const idx of groups.values()) {
    out.push({ head: groupTitle(state.items[idx[0]], idx.length) });
    for (const i of idx) out.push({ i });
  }
  return out;
}

function renderList() {
  const list = $("list");
  if (!state.items.length) {
    list.replaceChildren(h("div", { class: "empty" }, "Nothing here."));
    return;
  }
  const rows = displayOrder().map((e) => {
    if (e.head !== undefined) return h("div", { class: "group-head" }, e.head);
    const n = state.items[e.i];
    return h("div", {
      class: "item" + (n.read ? "" : " unread") + (e.i === state.selected ? " selected" : ""),
      "data-i": e.i,
      onclick: () => select(e.i),
    },
    h("span", { class: "who" }, h("span", { class: "source-tag" }, n.source), n.author),
    h("span", { class: "when" }, (n.starred ? "★ " : "") + when(n.sentAt || n.receivedAt)),
    h("span", { class: "title" }, n.title, labelChips(n)),
    h("span", { class: "snippet" }, n.body.slice(0, 200)));
  });
  if (state.next) rows.push(h("button", { class: "more", onclick: loadMore }, "Load more"));
  list.replaceChildren(...rows);
  list.querySelector(".selected")?.scrollIntoView({ block: "nearest" });
}

async function select(i) {
  state.selected = i;
  state.view = "list";
  const n = state.items[i];
  if (!n) return;
  renderList();
  renderDetail();
  if (!n.read) await update([n.id], { read: true });
}

async function update(ids, flags) {
  for (const n of state.items) if (ids.includes(n.id)) Object.assign(n, flags);
  renderList();
  if (state.selected >= 0) renderDetail();
  await api("PATCH", "notifications", { ids, ...flags });
  loadMeta();
}

/* ---------- detail ---------- */

function renderDetail() {
  const n = state.items[state.selected];
  if (!n) { $("detail").replaceChildren(); return; }
  const toggleLabel = async (l, on) => {
    await api(on ? "PUT" : "DELETE", `notifications/${n.id}/labels/${l.id}`);
    n.labels = on ? [...n.labels, l.id] : n.labels.filter((x) => x !== l.id);
    renderList();
    loadMeta();
  };
  $("detail").replaceChildren(
    h("h1", {}, n.title),
    h("div", { class: "meta" },
      [n.author, n.source, n.kind, new Date((n.sentAt || n.receivedAt) * 1000).toLocaleString()]
        .filter(Boolean).join(" · ")),
    h("div", { class: "actions" },
      h("button", { onclick: () => update([n.id], { archived: !n.archived }) },
        n.archived ? "Unarchive" : "Archive", " ", h("kbd", {}, "e")),
      h("button", { onclick: () => update([n.id], { starred: !n.starred }) },
        n.starred ? "Unstar" : "Star", " ", h("kbd", {}, "s")),
      h("button", { onclick: () => update([n.id], { read: !n.read }) },
        n.read ? "Mark unread" : "Mark read", " ", h("kbd", {}, "u")),
      n.threadKey ? h("button", { onclick: () => setFilter({ state: "all", thread: n.threadKey, source: n.source }) },
        "Whole thread", " ", h("kbd", {}, "t")) : null,
      n.url ? h("a", { href: n.url, target: "_blank", rel: "noopener noreferrer" }, "Open in source ↗") : null),
    state.labels.length ? h("div", { class: "labels" }, state.labels.map((l) =>
      h("label", {},
        h("input", { type: "checkbox", checked: n.labels.includes(l.id),
          onchange: (e) => toggleLabel(l, e.target.checked) }),
        h("span", { class: "chip", style: { background: l.color } }, l.name)))) : null,
    h("div", { class: "body" }, n.body || "(no text)"));
}

/* ---------- rules ---------- */

const FIELDS = ["source", "kind", "author", "title", "body", "thread", "url"];
const OPS = ["contains", "equals", "startsWith", "endsWith"];

function select_(options, value, onchange) {
  return h("select", { onchange: (e) => onchange(e.target.value) },
    options.map(([v, label]) => h("option", { value: v, selected: v === value }, label)));
}

function ruleEditor(rule, onSave, onCancel) {
  const spec = structuredClone(rule.spec);
  let name = rule.name;
  const root = h("div", { class: "rule" });
  const draw = () => {
    root.replaceChildren(
      h("div", { class: "row" },
        h("input", { value: name, placeholder: "Rule name", oninput: (e) => { name = e.target.value; } }),
        "match", select_([["all", "all conditions"], ["any", "any condition"]], spec.match,
          (v) => { spec.match = v; })),
      spec.conditions.map((c, i) => h("div", { class: "cond" },
        select_(FIELDS.map((f) => [f, f]), c.field, (v) => { c.field = v; }),
        select_([["false", "is"], ["true", "is not"]], String(c.negate), (v) => { c.negate = v === "true"; }),
        select_(OPS.map((o) => [o, o]), c.op, (v) => { c.op = v; }),
        h("input", { value: c.value, oninput: (e) => { c.value = e.target.value; } }),
        h("button", { onclick: () => { spec.conditions.splice(i, 1); draw(); } }, "−"))),
      h("div", { class: "row" }, h("button", { onclick: () => {
        spec.conditions.push({ field: "title", op: "contains", value: "", negate: false }); draw();
      } }, "+ condition")),
      h("div", { class: "row" }, "then label:",
        state.labels.map((l) => h("label", {},
          h("input", { type: "checkbox", checked: spec.labels.includes(l.id), onchange: (e) => {
            spec.labels = e.target.checked ? [...spec.labels, l.id] : spec.labels.filter((x) => x !== l.id);
          } }), " ", l.name)),
        state.labels.length ? null : h("span", { class: "hint" }, "(create labels in the sidebar first)")),
      h("div", { class: "row" },
        h("label", {}, h("input", { type: "checkbox", checked: spec.archive,
          onchange: (e) => { spec.archive = e.target.checked; } }), " archive"),
        h("label", {}, h("input", { type: "checkbox", checked: spec.markRead,
          onchange: (e) => { spec.markRead = e.target.checked; } }), " mark read")),
      h("div", { class: "row" },
        h("button", { class: "primary", onclick: () => onSave(name, spec) }, "Save"),
        onCancel ? h("button", { onclick: onCancel }, "Cancel") : null));
  };
  draw();
  return root;
}

async function showRules() {
  state.view = "rules";
  renderSidebar();
  const rules = await api("GET", "rules");
  const byId = Object.fromEntries(state.labels.map((l) => [l.id, l]));
  const pane = $("detail");
  const describe = (r) => h("div", { class: "rule" },
    h("div", { class: "row" },
      h("strong", {}, r.name || "(unnamed)"),
      h("label", {}, h("input", { type: "checkbox", checked: r.enabled, onchange: async (e) => {
        await api("PATCH", "rules/" + r.id, { enabled: e.target.checked });
      } }), " enabled"),
      h("button", { onclick: () => pane.replaceChildren(ruleEditor(r, async (name, spec) => {
        await api("PATCH", "rules/" + r.id, { name, spec });
        showRules();
      }, showRules)) }, "Edit"),
      h("button", { onclick: async () => {
        if (!confirm("Delete this rule?")) return;
        await api("DELETE", "rules/" + r.id);
        showRules();
      } }, "Delete")),
    h("div", { class: "hint" },
      `if ${r.spec.match} of: `,
      r.spec.conditions.map((c) => `${c.field} ${c.negate ? "not " : ""}${c.op} "${c.value}"`).join("; "),
      " → ",
      [...r.spec.labels.map((id) => byId[id]?.name || "?"),
        r.spec.archive ? "archive" : null, r.spec.markRead ? "mark read" : null]
        .filter(Boolean).join(", ")));
  pane.replaceChildren(
    h("h1", {}, "Rules"),
    h("p", { class: "hint" }, "Rules run on every new notification. Labels are organisation, not sources: ",
      "a rule can put mail and GitHub notifications under the same label. ",
      "Re-running applies the current label rules to all past notifications."),
    h("div", { class: "actions" },
      h("button", { class: "primary", onclick: () => pane.replaceChildren(ruleEditor(
        { name: "", spec: { match: "all", conditions: [{ field: "title", op: "contains", value: "", negate: false }],
          labels: [], archive: false, markRead: false } },
        async (name, spec) => { await api("POST", "rules", { name, spec }); showRules(); }, showRules)) },
        "New rule"),
      h("button", { onclick: async (e) => {
        const r = await api("POST", "rules/rerun");
        e.target.textContent = `Re-ran: ${r.matched} matched`;
        refresh();
      } }, "Re-run over history")),
    ...rules.map(describe));
}

/* ---------- sources ---------- */

async function showSources() {
  state.view = "sources";
  await loadMeta();
  const ago = (t) => t ? `${Math.max(0, Math.round(Date.now() / 1000 - t))} s ago` : "never";
  $("detail").replaceChildren(
    h("h1", {}, "Source health"),
    h("p", { class: "hint" }, "A source that is quiet and has not synced recently is broken, not idle."),
    h("table", {},
      h("tr", {}, ["Source", "Kind", "State", "Detail", "Last OK", "Last error", "Events"].map((t) => h("th", {}, t))),
      state.sources.health.map((s) => h("tr", {},
        h("td", {}, s.source), h("td", {}, s.kind),
        h("td", {}, h("span", { class: "dot " + s.state, style: { display: "inline-block" } }), " ", s.state),
        h("td", {}, s.detail || ""), h("td", {}, ago(s.lastOk)),
        h("td", {}, s.lastError ? `${s.lastError} (${ago(s.lastErrorAt)})` : ""),
        h("td", {}, s.events)))));
}

/* ---------- API tokens ---------- */

/** Checkboxes for a subset of `options` ([value, label] pairs); unticking "all" restricts. */
function subsetPicker(title, options, picked) {
  const all = h("input", { type: "checkbox", checked: true });
  const boxes = options.map(([v, label]) => [v, h("input", { type: "checkbox", disabled: true })]);
  all.addEventListener("change", () => boxes.forEach(([, b]) => { b.disabled = all.checked; }));
  picked.get = () => all.checked ? null : boxes.filter(([, b]) => b.checked).map(([v]) => v);
  return h("div", { class: "row" }, h("strong", {}, title),
    h("label", {}, all, " all"),
    boxes.map(([v, b], i) => h("label", {}, b, " ", options[i][1])));
}

function describeScope(scope) {
  const byId = Object.fromEntries(state.labels.map((l) => [l.id, l.name]));
  const parts = [
    scope.sources ? "sources: " + (scope.sources.join(", ") || "none") : "all sources",
    scope.labels ? "labels: " + (scope.labels.map((id) => byId[id] || "#" + id).join(", ") || "none") : "all labels",
    scope.write ? "read + write" : "read-only",
  ];
  return parts.join(" · ");
}

async function showTokens(created) {
  state.view = "tokens";
  renderSidebar();
  const tokens = await api("GET", "tokens");
  const date = (t) => t ? new Date(t * 1000).toLocaleString() : "never";
  const name = h("input", { placeholder: "Token name, e.g. laptop CLI" });
  const sources = {}, labels = {};
  const write = h("input", { type: "checkbox" });
  const error = h("span", { class: "error" });
  const create = async () => {
    if (!name.value.trim()) { name.focus(); return; }
    try {
      showTokens(await api("POST", "tokens", { name: name.value.trim(),
        scope: { sources: sources.get(), labels: labels.get(), write: write.checked } }));
    } catch (err) { error.textContent = err.message; }
  };
  name.addEventListener("keydown", (e) => { if (e.key === "Enter") create(); });
  $("detail").replaceChildren(
    h("h1", {}, "API tokens"),
    h("p", { class: "hint" }, "Tokens let clients other than this browser use the API, sent as ",
      h("code", {}, "Authorization: Bearer agl_…"), ". A token only ever sees notifications from its ",
      "sources that carry one of its labels, and can change them only if it may write. ",
      "Labels, rules, views and tokens can only be managed from a logged-in session."),
    ...(created ? [h("div", { class: "rule" },
      h("strong", {}, `Token "${created.name}" created. Copy it now; it will not be shown again.`),
      h("div", { class: "hint" }, describeScope(created.scope)),
      h("div", { class: "row" },
        h("input", { class: "token", value: created.token, readonly: true, onfocus: (e) => e.target.select() }),
        h("button", { onclick: async (e) => {
          await navigator.clipboard.writeText(created.token);
          e.target.textContent = "Copied";
        } }, "Copy")))] : []),
    h("div", { class: "rule" },
      h("div", { class: "row" }, name),
      subsetPicker("Sources", state.sources.configured.map((x) => [x.name, x.name]), sources),
      subsetPicker("Labels", state.labels.map((l) => [l.id, l.name]), labels),
      h("div", { class: "row" }, h("label", {}, write, " may mark read, archive, star and label")),
      h("div", { class: "row" }, h("button", { class: "primary", onclick: create }, "Create token"), error)),
    tokens.length ? h("table", {},
      h("tr", {}, ["Name", "Scope", "Created", "Last used", ""].map((t) => h("th", {}, t))),
      tokens.map((t) => h("tr", {},
        h("td", {}, t.name), h("td", {}, t.scope ? describeScope(t.scope) : "?"),
        h("td", {}, date(t.createdAt)), h("td", {}, date(t.lastUsed)),
        h("td", {}, h("button", { onclick: async () => {
          if (!confirm(`Revoke token "${t.name}"? Clients using it stop working immediately.`)) return;
          await api("DELETE", "tokens/" + t.id);
          showTokens();
        } }, "Revoke")))))
      : h("p", { class: "hint" }, "No tokens yet."));
}

/* ---------- keyboard, search, live updates ---------- */

function move(delta) {
  const order = displayOrder().filter((e) => e.i !== undefined).map((e) => e.i);
  if (!order.length) return;
  const pos = order.indexOf(state.selected);
  const next = order[Math.min(order.length - 1, Math.max(0, pos + delta))];
  select(pos === -1 ? order[0] : next);
}

document.addEventListener("keydown", (e) => {
  if (e.target.matches("input, textarea, select")) {
    if (e.key === "Escape") e.target.blur();
    return;
  }
  const n = state.items[state.selected];
  switch (e.key) {
    case "j": move(1); break;
    case "k": move(-1); break;
    case "/": e.preventDefault(); $("search").focus(); break;
    case "e": if (n) update([n.id], { archived: !n.archived }).then(() => {
      if (state.filter.state === "inbox" || state.filter.state === "unread") move(1);
    }); break;
    case "s": if (n) update([n.id], { starred: !n.starred }); break;
    case "u": if (n) update([n.id], { read: !n.read }); break;
    case "t": if (n?.threadKey) setFilter({ state: "all", thread: n.threadKey, source: n.source }); break;
    case "o": if (n?.url) window.open(n.url, "_blank", "noopener,noreferrer"); break;
    case "Escape": setFilter({}); break;
    default: return;
  }
  e.preventDefault();
});

let searchTimer;
$("search").addEventListener("input", (e) => {
  clearTimeout(searchTimer);
  searchTimer = setTimeout(() => {
    state.filter.q = e.target.value.trim();
    state.view = "list";
    loadList(false);
  }, 250);
});

$("group").addEventListener("change", (e) => {
  state.group = e.target.value;
  try { localStorage.setItem("angelia.group", state.group); } catch (_) { /* private mode */ }
  renderList();
});

$("save-view").addEventListener("click", async () => {
  const name = prompt("Name for this view");
  if (!name) return;
  await api("POST", "views", { name, query: { ...state.filter } });
  loadMeta();
});

let events;
function connectEvents() {
  events?.close();
  events = new EventSource("/api/events");
  events.addEventListener("open", () => $("live").classList.add("on"));
  events.addEventListener("error", () => $("live").classList.remove("on"));
  let pending;
  events.addEventListener("change", () => {
    clearTimeout(pending);
    pending = setTimeout(refresh, 150);
  });
}

async function start() {
  try { await api("GET", "me"); } catch (_) { return; }
  $("login").hidden = true;
  $("app").hidden = false;
  $("group").value = state.group;
  await refresh();
  connectEvents();
}

start();