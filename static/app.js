"use strict";

// Everything shown here comes from other people (mail, GitHub, ...), so the DOM is only ever
// built with `h()` and `fill()` -- text goes in as text nodes, never through innerHTML.

const store = {
  get: (k, d) => { try { return localStorage.getItem(k) ?? d; } catch (_) { return d; } },
  set: (k, v) => { try { localStorage.setItem(k, v); } catch (_) { /* private mode */ } },
};

const state = {
  filter: { state: "inbox", source: null, label: null, q: "", thread: null },
  view: "list", // or "rules" | "sources" | "tokens" | "security"
  items: [],
  next: null,
  selected: -1,
  labels: [],
  views: [],
  counts: { unread: 0, sources: {}, labels: {} },
  sources: { configured: [], health: [] },
  sort: store.get("angelia.sort", "newest"),
  group: store.get("angelia.group", ""),
};

/** Children for `h` and `fill`: nested arrays are flattened, and null, undefined and false
    skipped -- unlike the DOM's own `append`, which would print them. */
function nodes(children) {
  return children.flat(Infinity).filter((c) => c !== null && c !== undefined && c !== false)
    .map((c) => c instanceof Node ? c : document.createTextNode(String(c)));
}

function h(tag, attrs, ...children) {
  const el = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs || {})) {
    if (v === null || v === undefined || v === false) continue;
    if (k.startsWith("on")) el.addEventListener(k.slice(2), v);
    else if (k === "style") Object.assign(el.style, v);
    else el.setAttribute(k, v === true ? "" : v);
  }
  el.append(...nodes(children));
  return el;
}

function fill(el, ...children) {
  el.replaceChildren(...nodes(children));
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
  if (res.status === 401 && !path.startsWith("login")) { showLogin(); throw new Error("Signed out."); }
  const data = await res.json().catch(() => ({}));
  if (data.locked && !path.startsWith("login")) { showLogin(data.error); throw new Error("Locked."); }
  if (!res.ok) throw new Error(data.error || res.statusText);
  return data;
}

/* ---------- time ---------- */

const dayStart = (d) => new Date(d.getFullYear(), d.getMonth(), d.getDate()).getTime();

/** For the list: the time today, the weekday this week, the date otherwise. */
function shortTime(ts) {
  const d = new Date(ts * 1000), now = new Date();
  const days = Math.round((dayStart(now) - dayStart(d)) / 86400000);
  if (days === 0) return d.toLocaleTimeString([], { hour: "2-digit", minute: "2-digit" });
  if (days > 0 && days < 7) return d.toLocaleDateString([], { weekday: "short" });
  return d.toLocaleDateString([], { day: "numeric", month: "short",
    year: d.getFullYear() === now.getFullYear() ? undefined : "numeric" });
}

function longTime(ts) {
  return new Date(ts * 1000).toLocaleString([], { weekday: "long", day: "numeric", month: "long",
    year: "numeric", hour: "2-digit", minute: "2-digit" });
}

function dayTitle(ts) {
  const d = new Date(ts * 1000);
  const days = Math.round((dayStart(new Date()) - dayStart(d)) / 86400000);
  if (days === 0) return "Today";
  if (days === 1) return "Yesterday";
  return d.toLocaleDateString([], { weekday: "long", day: "numeric", month: "long",
    year: d.getFullYear() === new Date().getFullYear() ? undefined : "numeric" });
}

function ago(t) {
  if (!t) return "never";
  const s = Math.max(0, Math.round(Date.now() / 1000 - t));
  if (s < 90) return `${s} s ago`;
  if (s < 5400) return `${Math.round(s / 60)} min ago`;
  if (s < 129600) return `${Math.round(s / 3600)} h ago`;
  return shortTime(t);
}

/* ---------- message bodies ---------- */

// A link written as [text](url) -- what angelia makes of a link in HTML mail, and Markdown's
// own syntax in GitHub comments -- or a bare http(s) URL, without trailing punctuation.
const LINK = /\[([^\]\n]{1,500})\]\(((?:https?:\/\/|mailto:)[^\s)]+)\)|(https?:\/\/[^\s<>"'`]*[^\s<>"'`.,;:!?)\]])/g;

function linkTo(href, text) {
  return h("a", { href, target: "_blank", rel: "noopener noreferrer nofollow" }, text);
}

/** Text with its links made clickable, and `code` spans if `markdown`. */
function inline(text, markdown) {
  const out = [];
  const pushText = (t) => {
    if (!markdown) { out.push(t); return; }
    t.split(/(`[^`\n]+`)/).forEach((part, i) => out.push(i % 2 ? h("code", {}, part.slice(1, -1)) : part));
  };
  let last = 0;
  for (const m of text.matchAll(LINK)) {
    pushText(text.slice(last, m.index));
    out.push(m[1] ? linkTo(m[2], m[1]) : linkTo(m[3], m[3]));
    last = m.index + m[0].length;
  }
  pushText(text.slice(last));
  return out;
}

function paragraph(lines, markdown) {
  const parts = [];
  lines.forEach((l, i) => {
    if (i) parts.push(h("br"));
    parts.push(...inline(l, markdown));
  });
  return h("p", {}, parts);
}

// "On Mon, 19 Oct 2026 Anna wrote:", "Am ... schrieb ...:", "Op ... schreef ...:"
const ATTRIBUTION = /^(on|am|op|le|el)\b.{0,200}(wrote|schrieb|schreef|a écrit|escribió)\s*:\s*$/i;
// Outlook's quoted header: From:/Von:/Van: followed by Sent:/Gesendet:/Verzonden: or Date:.
const OUTLOOK_FROM = /^\*?(from|von|van|de)\s*:\*?\s/i;
const OUTLOOK_SENT = /^\*?(sent|gesendet|verzonden|date|datum|envoyé)\s*:/i;

const lines_ = (n) => n === 1 ? "1 line" : `${n} lines`;

/** Message text as paragraphs, with quoted earlier messages folded away, links clickable, and
    for GitHub's Markdown, code blocks and spans. */
function renderBody(text, markdown) {
  const lines = text.replace(/\r\n/g, "\n").split("\n");
  const blocks = [];
  let para = [];
  const flush = () => { if (para.length) blocks.push(paragraph(para, markdown)); para = []; };
  const folded = (summaryText, inner) =>
    h("details", {}, h("summary", {}, summaryText), h("blockquote", {}, inner));
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const trimmed = line.trim();
    if (markdown && trimmed.startsWith("```")) {
      flush();
      const code = [];
      for (i++; i < lines.length && !lines[i].trim().startsWith("```"); i++) code.push(lines[i]);
      blocks.push(h("pre", {}, h("code", {}, code.join("\n"))));
      continue;
    }
    if (markdown && /^#{1,6}\s/.test(trimmed)) {
      flush();
      blocks.push(h("p", { class: "heading" }, inline(trimmed.replace(/^#+\s*/, ""), true)));
      continue;
    }
    const nextQuoted = () => {
      let j = i + 1;
      while (j < lines.length && !lines[j].trim()) j++;
      return j < lines.length && lines[j].trimStart().startsWith(">");
    };
    if (trimmed.startsWith(">") || (ATTRIBUTION.test(trimmed) && nextQuoted())) {
      flush();
      const attribution = trimmed.startsWith(">") ? null : trimmed;
      if (attribution) i++;
      const quoted = [];
      for (; i < lines.length; i++) {
        const l = lines[i].trimStart();
        if (l.startsWith(">")) quoted.push(l.replace(/^>\s?/, ""));
        else if (!l.trim() && i + 1 < lines.length && lines[i + 1].trimStart().startsWith(">")) quoted.push("");
        else if (l.trim()) break;
      }
      i--;
      const n = quoted.filter((q) => q.trim()).length;
      // A short quote without an attribution is context for what follows, so it stays visible.
      if (n && !attribution && n <= 3) blocks.push(h("blockquote", {}, renderBody(quoted.join("\n"), markdown)));
      else if (n) blocks.push(folded(attribution ? `${attribution} (${lines_(n)})` : `Quoted text (${lines_(n)})`,
        renderBody(quoted.join("\n"), markdown)));
      continue;
    }
    const outlook = OUTLOOK_FROM.test(trimmed) && lines.slice(i + 1, i + 5).some((l) => OUTLOOK_SENT.test(l.trim()));
    // Not on the first line: that is where the folded part itself begins.
    const earlier = outlook ||
      /^-{2,}\s*(original message|ursprüngliche nachricht|oorspronkelijk bericht)\s*-{2,}$/i.test(trimmed);
    if (earlier && i > 0) {
      flush();
      const rest = lines.slice(i);
      blocks.push(folded(`Earlier messages (${lines_(rest.filter((l) => l.trim()).length)})`,
        renderBody(rest.join("\n"), markdown)));
      break;
    }
    if (line === "-- " || line === "--") {
      flush();
      blocks.push(h("div", { class: "signature" }, inline(lines.slice(i + 1).join("\n").trim(), false)));
      break;
    }
    if (!trimmed) flush(); else para.push(line);
  }
  flush();
  return blocks;
}

/** One line of text for the list: no quotes, no link syntax, no Markdown fences. */
function snippet(text) {
  return text.split("\n").filter((l) => l.trim() && !l.trimStart().startsWith(">") && !l.startsWith("```"))
    .join(" ").replace(/\[([^\]]*)\]\([^)]*\)/g, "$1").replace(/\s+/g, " ").slice(0, 220);
}

/* ---------- sign-in ---------- */

const fromB64 = (s) => Uint8Array.from(atob(s.replace(/-/g, "+").replace(/_/g, "/")), (c) => c.charCodeAt(0));
const toB64 = (buf) => btoa(String.fromCharCode(...new Uint8Array(buf)))
  .replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");

function showLogin(message) {
  events?.close();
  $("login-error").textContent = message || "";
  $("second-factor").hidden = true;
  $("login-form").hidden = false;
  $("app").hidden = true;
  $("login").hidden = false;
  $("password").focus();
}

/** The second step of signing in: a tap on a security key, or a code from an app. */
function showSecondFactor(sf) {
  const error = h("p", { class: "error", role: "alert" });
  const finish = async (answer) => {
    try {
      await api("POST", "login/second-factor", { pending: sf.pending, ...answer });
      $("login").hidden = true;
      start();
    } catch (err) { error.textContent = err.message; }
  };
  // The request starts on its own as soon as this shows; the button restarts it, which a
  // browser allows only once the one still waiting has been cancelled.
  let waiting;
  const tap = async () => {
    error.textContent = "";
    waiting?.abort();
    waiting = new AbortController();
    try {
      const cred = await navigator.credentials.get({ signal: waiting.signal, publicKey: {
        challenge: fromB64(sf.webauthn.challenge), rpId: sf.webauthn.rpId,
        allowCredentials: sf.webauthn.allowCredentials.map((id) => ({ type: "public-key", id: fromB64(id) })),
        userVerification: "discouraged", timeout: 60000 } });
      await finish({ credentialId: cred.id, clientDataJSON: toB64(cred.response.clientDataJSON),
        authenticatorData: toB64(cred.response.authenticatorData), signature: toB64(cred.response.signature) });
    } catch (err) {
      if (err.name === "AbortError") return;
      error.textContent = err.name === "NotAllowedError" ? "No key was tapped. Try again." : err.message;
    }
  };
  const code = h("input", { placeholder: "6-digit code", inputmode: "numeric", autocomplete: "one-time-code",
    "aria-label": "Code from your authenticator app" });
  code.addEventListener("keydown", (e) => { if (e.key === "Enter") finish({ code: code.value }); });
  $("login-form").hidden = true;
  $("second-factor").hidden = false;
  fill($("second-factor"),
    h("h1", {}, "angelia"),
    sf.webauthn && h("p", {}, "Insert your security key and tap it."),
    sf.webauthn && h("button", { type: "button", class: "primary", onclick: tap }, "Use security key"),
    sf.totp && h("p", {}, sf.webauthn ? "Or enter the code from your authenticator app." : "Enter the code from your authenticator app."),
    sf.totp && code,
    sf.totp && h("button", { type: "button", onclick: () => finish({ code: code.value }) }, "Verify code"),
    error,
    h("a", { href: "#", onclick: (e) => { e.preventDefault(); showLogin(); } }, "Start over"));
  if (sf.webauthn) tap(); else code.focus();
}

$("login-form").addEventListener("submit", async (e) => {
  e.preventDefault();
  const button = e.target.querySelector("button");
  button.disabled = true;
  try {
    const res = await api("POST", "login", { password: $("password").value });
    $("password").value = "";
    $("login-error").textContent = "";
    if (res.secondFactor) showSecondFactor(res.secondFactor);
    else start();
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
  // A conversation reads top to bottom.
  p.set("sort", f.thread ? "oldest" : state.sort);
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
  await Promise.all([state.view === "list" ? loadList(true) : null, loadMeta()]);
  if (state.view === "list" && state.selected >= 0) renderDetail();
}

/* ---------- sidebar ---------- */

function navItem(label, active, onclick, count, extra) {
  return h("button", { class: "nav-item" + (active ? " active" : ""), onclick: (e) => {
    $("app").classList.remove("menu-open");
    onclick(e);
  }, "aria-current": active ? "page" : null },
  extra?.before, h("span", {}, label),
  count ? h("span", { class: "count" }, count) : null, extra?.after);
}

function showList() {
  state.view = "list";
  $("app").classList.remove("on-page");
  $("page").hidden = true;
  $("panes").hidden = false;
}

function setFilter(f) {
  showList();
  state.filter = { state: "inbox", source: null, label: null, q: state.filter.q, thread: null, ...f };
  $("search").value = state.filter.q;
  $("panes").classList.remove("reading");
  fill($("detail"));
  loadList(false).then(renderSidebar);
}

function renderSidebar() {
  const f = state.filter;
  const plain = state.view === "list" && !f.source && !f.label && !f.thread;
  const health = Object.fromEntries(state.sources.health.map((s) => [s.source, s]));
  const remove = (title, act) => h("span", { class: "remove", title, role: "button", tabindex: 0,
    onclick: (e) => { e.stopPropagation(); act(); } }, "×");
  fill($("sidebar"),
    navItem("Inbox", plain && f.state === "inbox", () => setFilter({}), state.counts.unread),
    navItem("Unread", plain && f.state === "unread", () => setFilter({ state: "unread" })),
    navItem("Starred", plain && f.state === "starred", () => setFilter({ state: "starred" })),
    navItem("Archived", plain && f.state === "archived", () => setFilter({ state: "archived" })),
    navItem("Everything", plain && f.state === "all", () => setFilter({ state: "all" })),
    state.views.length > 0 && h("h2", {}, "Views"),
    state.views.map((v) => navItem(v.name, false, () => setFilter(v.query), null, {
      after: remove("Delete view", async () => { await api("DELETE", "views/" + v.id); loadMeta(); }),
    })),
    h("h2", {}, "Labels", h("button", { title: "New label", "aria-label": "New label", onclick: newLabel }, "+")),
    state.labels.map((l) => navItem(l.name, state.view === "list" && f.label === l.id,
      () => setFilter({ label: l.id }), state.counts.labels[l.id], {
        before: h("span", { class: "dot", style: { background: l.color } }),
        after: remove("Delete label", async () => {
          if (!confirm(`Delete the label "${l.name}"? Notifications keep everything else.`)) return;
          await api("DELETE", "labels/" + l.id);
          refresh();
        }),
      })),
    h("h2", {}, "Sources"),
    state.sources.configured.map((s) => {
      const st = health[s.name]?.state || (s.enabled ? "starting" : "disabled");
      return navItem(s.name, state.view === "list" && f.source === s.name,
        () => setFilter({ source: s.name }), state.counts.sources[s.name], {
          before: h("span", { class: "dot " + st, title: st }),
        });
    }),
    h("h2", {}, "Settings"),
    navItem("Rules", state.view === "rules", showRules),
    navItem("Source health", state.view === "sources", showSources),
    navItem("API tokens", state.view === "tokens", () => showTokens()),
    navItem("Sign-in security", state.view === "security", () => showSecurity()));
}

async function newLabel() {
  const name = prompt("Name of the new label");
  if (!name?.trim()) return;
  const palette = ["#0c6b73", "#2f6fbd", "#1d7a46", "#b42318", "#9a5b00", "#7a3fa8", "#56606b"];
  await api("POST", "labels", { name: name.trim(), color: palette[state.labels.length % palette.length] });
  loadMeta();
}

/* ---------- list ---------- */

function labelDots(n) {
  const byId = Object.fromEntries(state.labels.map((l) => [l.id, l]));
  const ls = n.labels.map((id) => byId[id]).filter(Boolean);
  if (!ls.length && !n.starred) return null;
  return h("span", { class: "marks" },
    n.starred && h("span", { class: "star", title: "Starred" }, "★"),
    ls.map((l) => h("span", { class: "label-dot", title: l.name, style: { background: l.color } })));
}

function groupKey(n) {
  switch (state.group) {
    case "thread": return n.source + "\u0000" + (n.threadKey || n.id);
    case "source": return n.source;
    case "sender": return n.author || n.source;
    case "day": return String(dayStart(new Date(n.time * 1000)));
    default: return "";
  }
}

function groupTitle(n, count) {
  switch (state.group) {
    case "thread": return `${n.title.replace(/^((re|aw|fwd?|wg)\s*:\s*)+/i, "")} (${count})`;
    case "source": return n.source;
    case "sender": return n.author || n.source;
    case "day": return dayTitle(n.time);
    default: return "";
  }
}

/** Indices of `state.items` in display order, with group headings. Groups keep the order in
    which their first member appears, so they follow the chosen sort. */
function displayOrder() {
  if (!state.group || state.filter.thread) return state.items.map((n, i) => ({ i }));
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
    const f = state.filter;
    fill(list, h("p", { class: "empty" }, f.q ? `Nothing matches "${f.q}".`
      : f.state === "inbox" && !f.source && !f.label ? "The inbox is empty." : "Nothing here."));
    return;
  }
  const rows = displayOrder().map((e) => {
    if (e.head !== undefined) return h("div", { class: "group-head" }, e.head);
    const n = state.items[e.i];
    return h("div", {
      class: "item" + (n.read ? "" : " unread") + (e.i === state.selected ? " selected" : ""),
      "data-i": e.i, onclick: () => select(e.i),
    },
    h("span", { class: "from" }, h("span", { class: "author" }, n.author || n.source),
      n.author ? h("span", { class: "source" }, n.source) : null),
    h("span", { class: "when", title: longTime(n.time) }, shortTime(n.time)),
    h("span", { class: "title" }, labelDots(n), n.title),
    h("span", { class: "snippet" }, snippet(n.body)));
  });
  fill(list, rows, state.next && h("button", { class: "more", onclick: loadMore }, "Load older"));
  list.querySelector(".selected")?.scrollIntoView({ block: "nearest" });
}

async function select(i) {
  showList();
  state.selected = i;
  const n = state.items[i];
  if (!n) return;
  $("panes").classList.add("reading");
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

/* ---------- reader ---------- */

function renderDetail() {
  const n = state.items[state.selected];
  if (!n) { fill($("detail")); return; }
  const toggleLabel = async (l, on) => {
    await api(on ? "PUT" : "DELETE", `notifications/${n.id}/labels/${l.id}`);
    n.labels = on ? [...n.labels, l.id] : n.labels.filter((x) => x !== l.id);
    renderList();
    loadMeta();
  };
  const markdown = n.kind !== "mail";
  const key = (k) => h("kbd", {}, k);
  fill($("detail"), h("div", { class: "reader" },
    h("button", { class: "quiet back", onclick: () => $("panes").classList.remove("reading") }, "Back to the list"),
    h("h1", {}, n.title),
    h("div", { class: "byline" },
      h("span", { class: "author" }, n.author || n.source),
      h("span", {}, n.source),
      h("time", { datetime: new Date(n.time * 1000).toISOString() }, longTime(n.time))),
    h("div", { class: "actions" },
      h("button", { onclick: () => update([n.id], { archived: !n.archived }) },
        n.archived ? "Move to inbox" : "Archive", key("e")),
      h("button", { onclick: () => update([n.id], { starred: !n.starred }) },
        n.starred ? "Unstar" : "Star", key("s")),
      h("button", { onclick: () => update([n.id], { read: !n.read }) },
        n.read ? "Mark unread" : "Mark read", key("u")),
      n.threadKey && h("button", { onclick: () => setFilter({ state: "all", thread: n.threadKey, source: n.source }) },
        "Conversation", key("t")),
      n.url && linkTo(n.url, n.kind === "mail" ? "Open original" : `Open on ${n.source}`)),
    state.labels.length > 0 && h("div", { class: "labels", role: "group", "aria-label": "Labels" },
      state.labels.map((l) => h("label", { class: "label-toggle" },
        h("input", { type: "checkbox", checked: n.labels.includes(l.id),
          onchange: (e) => toggleLabel(l, e.target.checked) }),
        h("span", { class: "label-dot", style: { background: l.color } }), l.name))),
    h("div", { class: "body" }, n.body.trim() ? renderBody(n.body, markdown) : h("p", { class: "hint" }, "No text."))));
  $("detail").scrollTop = 0;
}

/* ---------- settings pages ---------- */

/** Show a settings page in place of the list and the reader. */
function showPage(view, ...children) {
  state.view = view;
  $("app").classList.add("on-page");
  $("panes").hidden = true;
  $("page").hidden = false;
  fill($("page"), h("div", { class: "page-inner" }, children));
  $("page").scrollTop = 0;
  renderSidebar();
}

function field(label, control, id) {
  if (id) control.id = id;
  return [h("label", { class: "label", for: id }, label), control];
}

/* ---------- rules ---------- */

const FIELDS = [["title", "Title"], ["body", "Text"], ["author", "Sender"], ["source", "Source"],
  ["kind", "Kind"], ["thread", "Conversation"], ["url", "Link"]];
const OPS = [["contains", "contains"], ["equals", "is exactly"], ["startsWith", "starts with"],
  ["endsWith", "ends with"]];

function select_(options, value, onchange, label) {
  return h("select", { onchange: (e) => onchange(e.target.value), "aria-label": label },
    options.map(([v, text]) => h("option", { value: v, selected: v === value }, text)));
}

function ruleEditor(rule, onSave, onCancel) {
  const spec = structuredClone(rule.spec);
  let name = rule.name;
  const root = h("div", { class: "editor" });
  const error = h("p", { class: "error", role: "alert" });
  const draw = () => fill(root,
    h("div", { class: "form" },
      field("Name", h("input", { value: name, placeholder: "e.g. Seminar mail",
        oninput: (e) => { name = e.target.value; } }), "rule-name"),
      h("span", { class: "label" }, "Applies when"),
      select_([["all", "all conditions hold"], ["any", "any condition holds"]], spec.match,
        (v) => { spec.match = v; }, "Match")),
    spec.conditions.map((c, i) => h("div", { class: "cond" },
      select_(FIELDS, c.field, (v) => { c.field = v; }, "Field"),
      select_([["false", "—"], ["true", "not"]], String(c.negate), (v) => { c.negate = v === "true"; }, "Negate"),
      select_(OPS, c.op, (v) => { c.op = v; }, "Comparison"),
      h("input", { value: c.value, placeholder: "text", "aria-label": "Value",
        oninput: (e) => { c.value = e.target.value; } }),
      h("button", { class: "quiet", "aria-label": "Remove condition", onclick: () => { spec.conditions.splice(i, 1); draw(); } }, "Remove"))),
    h("div", { class: "buttons" }, h("button", { onclick: () => {
      spec.conditions.push({ field: "title", op: "contains", value: "", negate: false });
      draw();
    } }, "Add condition")),
    h("div", { class: "form" },
      h("span", { class: "label" }, "Then label it"),
      state.labels.length ? h("div", { class: "choices" }, state.labels.map((l) => h("label", {},
        h("input", { type: "checkbox", checked: spec.labels.includes(l.id), onchange: (e) => {
          spec.labels = e.target.checked ? [...spec.labels, l.id] : spec.labels.filter((x) => x !== l.id);
        } }), l.name))) : h("span", { class: "hint" }, "Create labels in the sidebar first."),
      h("span", { class: "label" }, "And"),
      h("div", { class: "choices" },
        h("label", {}, h("input", { type: "checkbox", checked: spec.archive,
          onchange: (e) => { spec.archive = e.target.checked; } }), "archive it"),
        h("label", {}, h("input", { type: "checkbox", checked: spec.markRead,
          onchange: (e) => { spec.markRead = e.target.checked; } }), "mark it read"))),
    h("div", { class: "buttons" },
      h("button", { class: "primary", onclick: async () => {
        try { await onSave(name.trim(), spec); } catch (err) { error.textContent = err.message; }
      } }, "Save rule"),
      h("button", { onclick: onCancel }, "Cancel"), error));
  draw();
  return root;
}

const NEGATED = { contains: "does not contain", equals: "is not exactly", startsWith: "does not start with",
  endsWith: "does not end with" };

function describeRule(r, byId) {
  const conds = r.spec.conditions.map((c) => {
    const fieldName = FIELDS.find(([f]) => f === c.field)?.[1] || c.field;
    const op = c.negate ? NEGATED[c.op] : OPS.find(([o]) => o === c.op)?.[1];
    return `${fieldName.toLowerCase()} ${op || c.op} "${c.value}"`;
  });
  const actions = [...r.spec.labels.map((id) => `label ${byId[id]?.name || "?"}`),
    r.spec.archive && "archive", r.spec.markRead && "mark read"].filter(Boolean);
  const when = conds.length ? conds.join(r.spec.match === "any" ? ", or " : ", and ") : "always";
  return `When ${when}: ${actions.join(", ") || "nothing"}.`;
}

async function showRules(editing) {
  const rules = await api("GET", "rules");
  const byId = Object.fromEntries(state.labels.map((l) => [l.id, l]));
  const blank = { name: "", spec: { match: "all", labels: [], archive: false, markRead: false,
    conditions: [{ field: "title", op: "contains", value: "", negate: false }] } };
  const rerun = h("button", { onclick: async (e) => {
    e.target.disabled = true;
    const r = await api("POST", "rules/rerun");
    e.target.textContent = `Applied: ${r.matched} matched`;
    refresh();
  } }, "Apply labels to past notifications");
  showPage("rules",
    h("header", {}, h("h1", {}, "Rules"),
      h("p", { class: "hint" }, "Rules run on every new notification and label, archive or mark it. ",
        "A label can collect notifications from any source.")),
    editing === "new" ? ruleEditor(blank, async (name, spec) => {
      await api("POST", "rules", { name, spec });
      showRules();
    }, () => showRules()) : h("div", { class: "buttons" },
      h("button", { class: "primary", onclick: () => showRules("new") }, "New rule"), rerun),
    h("section", {}, rules.length ? rules.map((r) => editing === r.id
      ? ruleEditor(r, async (name, spec) => {
        await api("PATCH", "rules/" + r.id, { name, spec });
        showRules();
      }, () => showRules())
      : h("div", { class: "rule-row" + (r.enabled ? "" : " disabled") },
        h("strong", {}, r.name || "Unnamed rule"),
        h("div", { class: "buttons" },
          h("label", { class: "status" }, h("input", { type: "checkbox", checked: r.enabled, onchange: async (e) => {
            await api("PATCH", "rules/" + r.id, { enabled: e.target.checked });
            showRules();
          } }), "On"),
          h("button", { onclick: () => showRules(r.id) }, "Edit"),
          h("button", { class: "danger", onclick: async () => {
            if (!confirm(`Delete the rule "${r.name || "Unnamed rule"}"?`)) return;
            await api("DELETE", "rules/" + r.id);
            showRules();
          } }, "Delete")),
        h("span", { class: "sub" }, describeRule(r, byId))))
      : h("p", { class: "hint" }, "No rules yet.")));
}

/* ---------- source health ---------- */

async function showSources() {
  await loadMeta();
  showPage("sources",
    h("header", {}, h("h1", {}, "Source health"),
      h("p", { class: "hint" }, "A source that has not synced for a while is broken, not quiet.")),
    h("table", { class: "table" },
      h("thead", {}, h("tr", {}, ["Source", "State", "Last synced", "Notifications"].map((t) => h("th", {}, t)))),
      h("tbody", {}, state.sources.health.map((s) => h("tr", {},
        h("td", {}, h("strong", {}, s.source), h("div", { class: "sub" }, s.kind)),
        h("td", {}, h("span", { class: "status" }, h("span", { class: "dot " + s.state }), s.state),
          s.detail && h("div", { class: "sub" }, s.detail),
          s.lastError && h("div", { class: "sub" }, `Last error ${ago(s.lastErrorAt)}: ${s.lastError}`)),
        h("td", {}, ago(s.lastOk)),
        h("td", { class: "num" }, s.events))))));
}

/* ---------- API tokens ---------- */

/** "All" or a chosen subset of `options` ([value, label] pairs). */
function subsetPicker(name, options, picked) {
  const all = h("input", { type: "radio", name, checked: true });
  const some = h("input", { type: "radio", name });
  const boxes = options.map(([v, label]) => [v, h("input", { type: "checkbox" }), label]);
  const list = h("div", { class: "choices", hidden: true }, boxes.map(([, b, label]) => h("label", {}, b, label)));
  const sync = () => { list.hidden = all.checked; };
  all.addEventListener("change", sync);
  some.addEventListener("change", sync);
  picked.get = () => all.checked ? null : boxes.filter(([, b]) => b.checked).map(([v]) => v);
  return h("div", {}, h("div", { class: "choices" },
    h("label", {}, all, "All"), h("label", {}, some, "Only these:")), list);
}

function describeScope(scope) {
  const byId = Object.fromEntries(state.labels.map((l) => [l.id, l.name]));
  const sources = scope.sources ? (scope.sources.join(", ") || "none") : "all sources";
  const labels = scope.labels ? (scope.labels.map((id) => byId[id] || "#" + id).join(", ") || "none") : "any label";
  return [`Sees ${sources}, ${scope.labels ? "labelled " + labels : "with " + labels}.`,
    scope.write ? "May mark read, archive, star and label." : "Read-only."];
}

async function showTokens(created) {
  const tokens = await api("GET", "tokens");
  const name = h("input", { placeholder: "e.g. phone" });
  const sources = {}, labels = {};
  const write = h("input", { type: "checkbox" });
  const error = h("p", { class: "error", role: "alert" });
  const create = async () => {
    if (!name.value.trim()) { error.textContent = "Give the token a name."; name.focus(); return; }
    try {
      showTokens(await api("POST", "tokens", { name: name.value.trim(),
        scope: { sources: sources.get(), labels: labels.get(), write: write.checked } }));
    } catch (err) { error.textContent = err.message; }
  };
  name.addEventListener("keydown", (e) => { if (e.key === "Enter") create(); });
  const copy = async (e) => {
    await navigator.clipboard.writeText(created.token);
    e.target.textContent = "Copied";
  };
  showPage("tokens",
    h("header", {}, h("h1", {}, "API tokens"),
      h("p", { class: "hint" }, "Programs other than this browser sign in with a token, sent as ",
        h("code", {}, "Authorization: Bearer agl_…"), ". A token sees only notifications from its sources ",
        "that carry one of its labels. Labels, rules and tokens are managed here only.")),
    created && h("section", { class: "secret-box", role: "status" },
      h("strong", {}, `Token "${created.name}" created. Copy it now: it will not be shown again.`),
      h("div", { class: "buttons" },
        h("input", { value: created.token, readonly: true, "aria-label": "New token", onfocus: (e) => e.target.select() }),
        h("button", { class: "primary", onclick: copy }, "Copy")),
      h("span", { class: "hint" }, describeScope(created.scope).join(" "))),
    h("section", {}, h("h2", {}, "New token"),
      h("div", { class: "form" },
        field("Name", name, "token-name"),
        h("span", { class: "label" }, "Sources"),
        subsetPicker("token-sources", state.sources.configured.map((x) => [x.name, x.name]), sources),
        h("span", { class: "label" }, "Labels"),
        subsetPicker("token-labels", state.labels.map((l) => [l.id, l.name]), labels),
        h("span", { class: "label" }, "Changes"),
        h("div", { class: "choices" }, h("label", {}, write, "May mark read, archive, star and label")),
        h("div", { class: "wide buttons" }, h("button", { class: "primary", onclick: create }, "Create token"), error))),
    h("section", {}, h("h2", {}, "Tokens"),
      tokens.length ? h("table", { class: "table" },
        h("thead", {}, h("tr", {}, ["Name", "Access", "Last used", ""].map((t) => h("th", {}, t)))),
        h("tbody", {}, tokens.map((t) => h("tr", {},
          h("td", {}, h("strong", {}, t.name), h("div", { class: "sub" }, `Created ${shortTime(t.createdAt)}`)),
          h("td", {}, t.scope ? describeScope(t.scope).map((line) => h("div", {}, line)) : "?"),
          h("td", {}, ago(t.lastUsed)),
          h("td", { class: "actions" }, h("button", { class: "danger", onclick: async () => {
            if (!confirm(`Revoke "${t.name}"? Programs using it stop working at once.`)) return;
            await api("DELETE", "tokens/" + t.id);
            showTokens();
          } }, "Revoke"))))))
        : h("p", { class: "hint" }, "No tokens yet.")));
}

/* ---------- sign-in security ---------- */

async function showSecurity(notice) {
  const factors = await api("GET", "second-factors");
  const password = h("input", { type: "password", autocomplete: "current-password" });
  const error = h("p", { class: "error", role: "alert" });
  const run = (act) => async () => {
    error.textContent = "";
    if (!password.value) {
      error.textContent = "Enter your password first.";
      password.focus();
      return;
    }
    try { await act(); } catch (err) {
      error.textContent = err.name === "NotAllowedError" ? "No key was tapped. Try again." : err.message;
    }
  };

  const keyName = h("input", { placeholder: "e.g. Titan" });
  const addKey = run(async () => {
    const o = await api("POST", "second-factors/webauthn/challenge");
    const cred = await navigator.credentials.create({ publicKey: {
      challenge: fromB64(o.challenge), rp: o.rp,
      user: { id: fromB64(o.user.id), name: o.user.name, displayName: o.user.displayName },
      pubKeyCredParams: [{ type: "public-key", alg: -7 }],
      excludeCredentials: o.excludeCredentials.map((id) => ({ type: "public-key", id: fromB64(id) })),
      authenticatorSelection: { residentKey: "discouraged", userVerification: "discouraged" },
      attestation: "none", timeout: 60000 } });
    await api("POST", "second-factors/webauthn", { password: password.value,
      name: keyName.value.trim() || "Security key",
      clientDataJSON: toB64(cred.response.clientDataJSON),
      authenticatorData: toB64(cred.response.getAuthenticatorData()),
      publicKey: toB64(cred.response.getPublicKey()), alg: cred.response.getPublicKeyAlgorithm() });
    showSecurity("Security key added.");
  });

  const appName = h("input", { placeholder: "e.g. phone" });
  const appSetup = h("div", { class: "wide" });
  const addApp = run(async () => {
    const o = await api("POST", "second-factors/totp/secret");
    const qr = qrcode(0, "M");
    qr.addData(o.uri);
    qr.make();
    const code = h("input", { placeholder: "6-digit code", inputmode: "numeric", "aria-label": "Code from the app" });
    const confirmApp = run(async () => {
      await api("POST", "second-factors/totp", { password: password.value,
        name: appName.value.trim() || "Authenticator app", code: code.value });
      showSecurity("Authenticator app added.");
    });
    code.addEventListener("keydown", (e) => { if (e.key === "Enter") confirmApp(); });
    fill(appSetup, h("div", { class: "secret-box" },
      h("span", {}, "Scan this with the app, then enter the code it shows."),
      h("img", { class: "qr", src: qr.createDataURL(5, 0), alt: "QR code for the authenticator app" }),
      h("span", { class: "hint" }, "Or type the key into the app: ", h("code", {}, o.secret)),
      h("div", { class: "buttons" }, code, h("button", { class: "primary", onclick: confirmApp }, "Add app"))));
    code.focus();
  });

  const kinds = { webauthn: "Security key", totp: "Authenticator app" };
  showPage("security",
    h("header", {}, h("h1", {}, "Sign-in security"),
      h("p", { class: "hint" }, "With a security key or an authenticator app added, signing in takes the ",
        "password and then a tap on the key or a code from the app. Add two, so that losing one does not ",
        "lock you out. API tokens are not affected.")),
    notice && h("p", { class: "notice", role: "status" }, notice),
    h("section", {}, h("h2", {}, "Add a security key or an app"),
      h("p", { class: "hint" }, "Each change needs your password."),
      h("div", { class: "form" },
        field("Password", password, "security-password"),
        field("Security key", keyName, "key-name"),
        h("div", { class: "wide buttons" }, h("button", { class: "primary", onclick: addKey }, "Add key and tap it")),
        field("Authenticator app", appName, "app-name"),
        h("div", { class: "wide buttons" }, h("button", { onclick: addApp }, "Set up app")),
        appSetup,
        h("div", { class: "wide" }, error))),
    h("section", {}, h("h2", {}, "Added"),
      factors.length ? h("table", { class: "table" },
        h("thead", {}, h("tr", {}, ["Name", "Kind", "Last used", ""].map((t) => h("th", {}, t)))),
        h("tbody", {}, factors.map((f) => h("tr", {},
          h("td", {}, h("strong", {}, f.name), h("div", { class: "sub" }, `Added ${shortTime(f.createdAt)}`)),
          h("td", {}, kinds[f.kind] || f.kind),
          h("td", {}, ago(f.lastUsed)),
          h("td", { class: "actions" }, h("button", { class: "danger", onclick: run(async () => {
            if (!confirm(`Remove "${f.name}"?`)) return;
            await api("DELETE", "second-factors/" + f.id, { password: password.value });
            showSecurity(`Removed "${f.name}".`);
          }) }, "Remove"))))))
        : h("p", { class: "hint" }, "Nothing yet: signing in takes the password alone.")));
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
  if (e.ctrlKey || e.metaKey || e.altKey || state.view !== "list" || $("app").hidden) return;
  const n = state.items[state.selected];
  switch (e.key) {
    case "j": move(1); break;
    case "k": move(-1); break;
    case "/": $("search").focus(); break;
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
    showList();
    loadList(false);
  }, 250);
});

$("sort").addEventListener("change", (e) => {
  state.sort = e.target.value;
  store.set("angelia.sort", state.sort);
  loadList(true);
});

$("group").addEventListener("change", (e) => {
  state.group = e.target.value;
  store.set("angelia.group", state.group);
  renderList();
});

$("save-view").addEventListener("click", async () => {
  const name = prompt("Name for this view");
  if (!name?.trim()) return;
  await api("POST", "views", { name: name.trim(), query: { ...state.filter } });
  loadMeta();
});

$("menu").addEventListener("click", () => $("app").classList.toggle("menu-open"));

let events;
function connectEvents() {
  events?.close();
  events = new EventSource("/api/events");
  const live = (on) => {
    $("live").classList.toggle("on", on);
    $("live").title = on ? "Live updates are on" : "Live updates are off; reconnecting";
  };
  events.addEventListener("open", () => live(true));
  events.addEventListener("error", () => live(false));
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
  $("sort").value = state.sort;
  $("group").value = state.group;
  showList();
  await refresh();
  connectEvents();
}

start();