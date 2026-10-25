"use strict";

// Everything shown here comes from other people (mail, GitHub, ...), so the DOM is only ever
// built with `h()` — text goes in as text nodes, never through innerHTML.

const prefs = {
  get: (k, d) => { try { return localStorage.getItem("angelia." + k) ?? d; } catch (_) { return d; } },
  set: (k, v) => { try { localStorage.setItem("angelia." + k, v); } catch (_) { /* private mode */ } },
};
document.documentElement.dataset.theme = prefs.get("theme", "system");
document.documentElement.dataset.density = prefs.get("density", "comfortable");

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
  sort: localStorage.getItem("angelia.sort") || "newest",
};

function h(tag, attrs, ...children) {
  const el = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs || {})) {
    if (v === null || v === undefined || v === false) continue;
    if (k.startsWith("on")) el.addEventListener(k.slice(2), v);
    else if (k === "style") Object.assign(el.style, v);
    else el.setAttribute(k, v === true ? "" : v);
  }
  for (const c of children.flat(Infinity)) {
    if (c === null || c === undefined || c === false) continue;
    el.append(c instanceof Node ? c : document.createTextNode(String(c)));
  }
  return el;
}

/** Replace an element's children like `replaceChildren`, but skipping null, undefined and false
    as `h` does -- the DOM's own method would print them as text. */
function fill(el, ...children) {
  el.replaceChildren(...children.flat(Infinity).filter((c) => c !== null && c !== undefined && c !== false)
    .map((c) => c instanceof Node ? c : document.createTextNode(String(c))));
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
  const error = h("p", { class: "error" });
  const finish = async (answer) => {
    try {
      await api("POST", "login/second-factor", { pending: sf.pending, ...answer });
      $("login").hidden = true;
      start();
    } catch (err) { error.textContent = err.message; }
  };
  // The request is started on its own as soon as this shows; the button restarts it, which a
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
      error.textContent = err.name === "NotAllowedError" ? "No key was tapped." : err.message;
    }
  };
  const code = h("input", { placeholder: "6-digit code", inputmode: "numeric", autocomplete: "one-time-code" });
  code.addEventListener("keydown", (e) => { if (e.key === "Enter") finish({ code: code.value }); });
  $("login-form").hidden = true;
  $("second-factor").hidden = false;
  fill($("second-factor"),
    h("h1", {}, "angelia"),
    sf.webauthn ? h("p", {}, "Insert your security key and tap it.") : null,
    sf.webauthn ? h("button", { type: "button", onclick: tap }, "Use security key") : null,
    sf.totp ? h("p", {}, sf.webauthn ? "Or enter the code from your authenticator app:" : "Enter the code from your authenticator app:") : null,
    sf.totp ? code : null,
    sf.totp ? h("button", { type: "button", onclick: () => finish({ code: code.value }) }, "Verify code") : null,
    error,
    h("a", { href: "#", onclick: (e) => { e.preventDefault(); showLogin(); } }, "Start over"));
  if (sf.webauthn) tap(); else code.focus();
}

$("login-form")?.addEventListener("submit", async (e) => {
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
  // A thread reads top to bottom.
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
  showList();
  state.filter = { state: "inbox", source: null, label: null, q: state.filter.q, thread: null, ...f };
  $("search").value = state.filter.q;
  loadList(false).then(renderSidebar);
  fill($("detail"));
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
  items.push(h("div", { class: "sidebar-end" }, navItem("Settings", false, () => showSettings())));
  fill($("sidebar"), ...items);
}

async function newLabel() {
  const name = prompt("Label name");
  if (!name) return;
  const palette = ["#2f5bd3", "#2e8b57", "#c0392b", "#d4a017", "#8e44ad", "#16a085", "#d35400"];
  await api("POST", "labels", { name, color: palette[state.labels.length % palette.length] });
  loadMeta();
}

/* ---------- list ---------- */

const clock = (d) => d.toLocaleTimeString([], { hour: "2-digit", minute: "2-digit", hourCycle: "h23" });

/** The time for today, the date and time otherwise; 24-hour. */
function when(ts) {
  if (!ts) return "";
  const d = new Date(ts * 1000);
  const now = new Date();
  if (d.toDateString() === now.toDateString()) return clock(d);
  return d.toLocaleDateString([], { day: "numeric", month: "short",
    year: d.getFullYear() === now.getFullYear() ? undefined : "numeric" }) + ", " + clock(d);
}

/** In full, for the message header: "Friday, 24 October 2026, 09:12". */
function longTime(ts) {
  const d = new Date(ts * 1000);
  return d.toLocaleDateString([], { weekday: "long", day: "numeric", month: "long", year: "numeric" }) +
    ", " + clock(d);
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
    case "day": return new Date(n.time * 1000).toDateString();
    default: return "";
  }
}

function groupTitle(n, members) {
  switch (state.group) {
    case "thread": return `${n.title} · ${members} message${members === 1 ? "" : "s"}`;
    case "source": return n.source;
    case "day": return new Date(n.time * 1000).toLocaleDateString([],
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
    fill(list, h("div", { class: "empty" }, "Nothing here."));
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
    h("span", { class: "when" }, (n.starred ? "★ " : "") + when(n.time)),
    h("span", { class: "title" }, n.title, labelChips(n)),
    h("span", { class: "snippet" }, snippet(n.body)));
  });
  if (state.next) rows.push(h("button", { class: "more", onclick: loadMore }, "Load more"));
  fill(list, ...rows);
  list.querySelector(".selected")?.scrollIntoView({ block: "nearest" });
}

async function select(i) {
  state.selected = i;
  showList();
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
  if (!n) { fill($("detail")); return; }
  const toggleLabel = async (l, on) => {
    await api(on ? "PUT" : "DELETE", `notifications/${n.id}/labels/${l.id}`);
    n.labels = on ? [...n.labels, l.id] : n.labels.filter((x) => x !== l.id);
    renderList();
    loadMeta();
  };
  const key = (k) => h("kbd", {}, k);
  fill($("detail"),
    h("header", { class: "msg-header" },
      h("h1", {}, n.title),
      h("dl", {},
        h("dt", {}, "From"), h("dd", {}, h("strong", {}, n.author || n.source)),
        h("dt", {}, "Source"), h("dd", {}, n.source, n.kind && n.kind !== "mail" ? ` (${n.kind})` : null),
        h("dt", {}, "Date"), h("dd", {}, h("time", { datetime: new Date(n.time * 1000).toISOString() }, longTime(n.time)))),
      h("div", { class: "actions" },
        h("button", { onclick: () => update([n.id], { archived: !n.archived }) },
          n.archived ? "Move to inbox" : "Archive", key("e")),
        h("button", { onclick: () => update([n.id], { starred: !n.starred }) },
          n.starred ? "Unstar" : "Star", key("s")),
        h("button", { onclick: () => update([n.id], { read: !n.read }) },
          n.read ? "Mark unread" : "Mark read", key("u")),
        n.threadKey && h("button", { onclick: () => setFilter({ state: "all", thread: n.threadKey, source: n.source }) },
          "Conversation", key("t")),
        n.url && h("a", { class: "button", href: n.url, target: "_blank", rel: "noopener noreferrer" },
          n.kind === "mail" ? "Open original" : `Open on ${n.source}`)),
      state.labels.length > 0 && h("div", { class: "labels", role: "group", "aria-label": "Labels" },
        state.labels.map((l) => h("label", { class: "label-toggle" },
          h("input", { type: "checkbox", checked: n.labels.includes(l.id),
            onchange: (e) => toggleLabel(l, e.target.checked) }),
          h("span", { class: "dot", style: { background: l.color } }), l.name))),
      attachmentList(n)),
    h("div", { class: "body" }, n.body.trim() ? renderMessage(n.body) : h("p", { class: "hint" }, "No text.")));
}

/** A byte count as people read it: 812 B, 4.2 KB, 31 MB. */
function byteSize(n) {
  if (n < 1024) return `${n} B`;
  const units = ["KB", "MB", "GB"];
  let v = n / 1024, i = 0;
  while (v >= 1024 && i < units.length - 1) { v /= 1024; i++; }
  return `${v < 10 ? v.toFixed(1) : Math.round(v)} ${units[i]}`;
}

/** The message's attachments, each a download; the server sends them only as downloads. */
function attachmentList(n) {
  if (!n.attachments?.length) return null;
  return h("ul", { class: "attachments", "aria-label": "Attachments" },
    n.attachments.map((a, i) => h("li", {},
      h("a", { href: `/api/notifications/${n.id}/attachments/${i}`, download: a.name, title: a.mime }, a.name),
      h("span", { class: "size", title: a.partial ? "The message was larger than what is fetched of it" : null },
        byteSize(a.size) + (a.partial ? ", incomplete" : "")))));
}

/* ---------- message bodies ---------- */

/** The text for the list's preview line: no quoted lines, code blocks or Markdown markup. */
function snippet(text) {
  let fenced = false;
  return text.split("\n").filter((l) => {
    if (FENCE.test(l)) { fenced = !fenced; return false; }
    return !fenced && l.trim() && !QUOTED.test(l) && !RULE.test(l) && !TABLE_SEP.test(l);
  }).join(" ")
    .replace(/!?\[([^\]\n]*)\]\([^)\s]*\)/g, "$1")
    .replace(/(^|\s)(#{1,6}|[-*+]|\d{1,3}[.)])\s+/g, "$1")
    .replace(/[`*~|]|(?<![\w])_|_(?![\w])/g, "")
    .replace(/\s+/g, " ").slice(0, 200);
}

// Rendered the way a mail client does: quoted earlier messages indented behind a bar coloured by
// quote level, the signature greyed out, and Markdown formatting. All of it is built as DOM
// nodes from text; nothing in a message is ever interpreted as HTML.

function linkTo(href, text) {
  return h("a", { href, target: "_blank", rel: "noopener noreferrer nofollow" }, text);
}

// Emphasis only around whole words, so snake_case names, file paths and URLs stay as they are.
const INLINE = new RegExp([
  "`(?<code>[^`\\n]+)`",
  "!?\\[(?<label>[^\\]\\n]{1,500})\\]\\((?<href>(?:https?:\\/\\/|mailto:)[^\\s)]+)\\)",
  "(?<url>https?:\\/\\/[^\\s<>\"'`]*[^\\s<>\"'`.,;:!?)\\]])",
  "(?<![\\w*])\\*\\*(?=\\S)(?<b1>.+?)(?<=\\S)\\*\\*(?![\\w*])",
  "(?<![\\w_])__(?=\\S)(?<b2>.+?)(?<=\\S)__(?![\\w_])",
  "(?<![\\w*])\\*(?=[^\\s*])(?<i1>[^*\\n]+?)(?<=[^\\s*])\\*(?![\\w*])",
  "(?<![\\w_])_(?=[^\\s_])(?<i2>[^_\\n]+?)(?<=[^\\s_])_(?![\\w_])",
  "~~(?=\\S)(?<s>[^~\\n]+?)(?<=\\S)~~",
].join("|"), "g");

function inline(text) {
  const out = [];
  let last = 0;
  for (const m of text.matchAll(INLINE)) {
    out.push(text.slice(last, m.index));
    const g = m.groups;
    if (g.code !== undefined) out.push(h("code", {}, g.code));
    else if (g.href !== undefined) out.push(linkTo(g.href, g.label));
    else if (g.url !== undefined) out.push(linkTo(g.url, g.url));
    else if (g.b1 !== undefined || g.b2 !== undefined) out.push(h("strong", {}, inline(g.b1 ?? g.b2)));
    else if (g.i1 !== undefined || g.i2 !== undefined) out.push(h("em", {}, inline(g.i1 ?? g.i2)));
    else if (g.s !== undefined) out.push(h("s", {}, inline(g.s)));
    last = m.index + m[0].length;
  }
  out.push(text.slice(last));
  return out;
}

const FENCE = /^\s*(```|~~~)/;
const HEADING = /^\s*(#{1,6})\s+(.*?)\s*#*\s*$/;
const RULE = /^\s*([-*_])(\s*\1){2,}\s*$/;
const ITEM = /^(\s*)([-*+]|\d{1,3}[.)])\s+(.*)$/;
const TABLE_SEP = /^\s*\|?\s*:?-{3,}:?\s*(\|\s*:?-{3,}:?\s*)*\|?\s*$/;
const startsBlock = (l) => FENCE.test(l) || HEADING.test(l) || RULE.test(l) || ITEM.test(l);

function cells(row) {
  return row.trim().replace(/^\||\|$/g, "").split("|").map((c) => c.trim());
}

/** Markdown blocks of unquoted lines. A line break inside a paragraph is kept, as mail and
    GitHub comments both mean it. */
function blocks(lines) {
  const out = [];
  for (let i = 0; i < lines.length;) {
    const line = lines[i];
    if (!line.trim()) { i++; continue; }
    if (FENCE.test(line)) {
      const fence = line.trim().slice(0, 3);
      const code = [];
      for (i++; i < lines.length && !lines[i].trim().startsWith(fence); i++) code.push(lines[i]);
      out.push(h("pre", {}, h("code", {}, code.join("\n"))));
      i++;
      continue;
    }
    const heading = line.match(HEADING);
    if (heading) {
      out.push(h("p", { class: "md-h md-h" + Math.min(heading[1].length, 3) }, inline(heading[2])));
      i++;
      continue;
    }
    if (RULE.test(line)) { out.push(h("hr")); i++; continue; }
    if (line.includes("|") && i + 1 < lines.length && TABLE_SEP.test(lines[i + 1])) {
      const head = cells(line);
      const rows = [];
      for (i += 2; i < lines.length && lines[i].includes("|") && lines[i].trim(); i++) rows.push(cells(lines[i]));
      out.push(h("table", {}, h("thead", {}, h("tr", {}, head.map((c) => h("th", {}, inline(c))))),
        h("tbody", {}, rows.map((r) => h("tr", {}, head.map((_, k) => h("td", {}, inline(r[k] || ""))))))));
      continue;
    }
    const item = line.match(ITEM);
    if (item) {
      const ordered = /\d/.test(item[2]);
      const items = [];
      while (i < lines.length) {
        const m = lines[i].match(ITEM);
        if (m && /\d/.test(m[2]) === ordered) { items.push({ depth: m[1].length >= 2 ? 1 : 0, text: [m[3]] }); i++; }
        else if (lines[i].trim() && /^\s{2,}/.test(lines[i]) && items.length) { items.at(-1).text.push(lines[i].trim()); i++; }
        else break;
      }
      out.push(h(ordered ? "ol" : "ul", {}, items.map((it) =>
        h("li", { class: it.depth ? "nested" : null }, it.text.map((t, k) => [k ? h("br") : null, inline(t)])))));
      continue;
    }
    const para = [];
    for (; i < lines.length && lines[i].trim() && (!para.length || !startsBlock(lines[i])); i++) para.push(lines[i]);
    out.push(h("p", {}, para.map((l, k) => [k ? h("br") : null, inline(l)])));
  }
  return out;
}

// "On Thu, 23 Oct 2026 Anna wrote:", "Am ... schrieb ...:", "Op ... schreef ...:"
const ATTRIBUTION = /^(on|am|op|le|el)\b.{0,250}(wrote|schrieb|schreef|a écrit|escribió)\s*:\s*$/i;
// Outlook's header above an earlier message, which it does not mark with ">".
const OUTLOOK_FROM = /^\*?(from|von|van|de)\s*:\*?\s/i;
const OUTLOOK_SENT = /^\*?(sent|gesendet|verzonden|date|datum|envoyé)\s*:/i;
const ORIGINAL = /^-{2,}\s*(original message|ursprüngliche nachricht|oorspronkelijk bericht)\s*-{2,}$/i;
const SEPARATOR = /^(-- ?|---|—)$/;
const QUOTED = /^\s*>/;

/** Lines quoted one level deeper below `lines`, plus the attribution above them. */
function quoteTree(lines, level) {
  const out = [];
  for (let i = 0; i < lines.length;) {
    if (QUOTED.test(lines[i])) {
      const inner = [];
      // Blank lines between quoted ones belong to the quote.
      for (; i < lines.length && (QUOTED.test(lines[i]) || (!lines[i].trim() && QUOTED.test(lines[i + 1] || ""))); i++)
        inner.push(lines[i].replace(/^\s*>\s?/, ""));
      const q = (level % 4) + 1;
      out.push(h("blockquote", { class: "quote q" + q }, quoteTree(inner, level + 1)));
      continue;
    }
    const plain = [];
    for (; i < lines.length && !QUOTED.test(lines[i]); i++) plain.push(lines[i]);
    // The line introducing a quote goes with it, set apart from the text.
    let attribution = null;
    if (i < lines.length) {
      let k = plain.length - 1;
      while (k >= 0 && !plain[k].trim()) k--;
      if (k >= 0 && (ATTRIBUTION.test(plain[k].trim()) || /\b(wrote|schrieb|schreef)\s*:\s*$/i.test(plain[k]))) {
        attribution = plain[k].trim();
        plain.length = k;
      }
    }
    out.push(blocks(plain));
    if (attribution) out.push(h("p", { class: "attribution" }, inline(attribution)));
  }
  return out;
}

function renderMessage(text) {
  let lines = text.replace(/\r\n?/g, "\n").split("\n");
  // Outlook's earlier messages are quoted in all but the ">".
  const earlier = lines.findIndex((l, i) => i > 0 && (ORIGINAL.test(l.trim()) ||
    (OUTLOOK_FROM.test(l.trim()) && lines.slice(i + 1, i + 6).some((n) => OUTLOOK_SENT.test(n.trim())))));
  if (earlier > 0) lines = [...lines.slice(0, earlier), ...lines.slice(earlier).map((l) => "> " + l)];
  // The signature: after the last separator line, if what follows is short and quotes nothing.
  let signature = null;
  for (let i = lines.length - 1; i > 0; i--) {
    if (QUOTED.test(lines[i])) break;
    if (SEPARATOR.test(lines[i].trimEnd()) || lines[i] === "-- ") {
      const rest = lines.slice(i + 1);
      const filled = rest.filter((l) => l.trim()).length;
      const tail = lines.slice(rest.length + i + 1);
      if (filled >= 1 && filled <= 12 && !tail.length) {
        signature = rest.join("\n").trim();
        lines = lines.slice(0, i);
      }
      break;
    }
  }
  return [quoteTree(lines, 0),
    signature && h("div", { class: "signature" }, "-- ", h("br"),
      signature.split("\n").map((l, k) => [k ? h("br") : null, inline(l)]))];
}

/* ---------- settings ---------- */

// Settings is a page of its own, as in a mail client: it takes the place of the folders, the
// list and the message, with its own sections on the left.

function showList() {
  state.view = "list";
  $("app").classList.remove("settings-open");
  $("settings").hidden = true;
}

const SECTIONS = [
  ["appearance", "Appearance"],
  ["rules", "Rules"],
  ["sources", "Sources"],
  ["tokens", "API tokens"],
  ["security", "Sign-in security"],
];

async function showSettings(section = prefs.get("settings", "appearance"), ...args) {
  state.view = "settings";
  prefs.set("settings", section);
  $("app").classList.add("settings-open");
  $("settings").hidden = false;
  const content = await ({ appearance: appearancePage, rules: rulesPage, sources: sourcesPage,
    tokens: tokensPage, security: securityPage })[section](...args);
  fill($("settings"),
    h("nav", { class: "settings-nav", "aria-label": "Settings" },
      h("button", { class: "back", onclick: () => { showList(); renderSidebar(); } }, "Back to messages"),
      SECTIONS.map(([key, label]) => h("button", { class: "nav-item" + (key === section ? " active" : ""),
        "aria-current": key === section ? "page" : null, onclick: () => showSettings(key) }, label))),
    h("div", { class: "settings-page" }, content));
  $("settings").scrollTop = 0;
}

/** A labelled control in a settings form. */
function row(label, control, hint) {
  const id = "f" + Math.random().toString(36).slice(2, 8);
  if (control instanceof HTMLElement && control.matches("input, select")) control.id = id;
  return h("div", { class: "form-row" },
    h("label", { class: "form-label", for: control instanceof HTMLElement && control.id ? id : null }, label),
    h("div", { class: "form-field" }, control, hint && h("p", { class: "hint" }, hint)));
}

/** A modal step, closed with Escape or Cancel. Resolves when it closes. */
function openDialog(title, build) {
  const dlg = h("dialog", { class: "dialog" });
  const close = () => dlg.close();
  fill(dlg, h("h2", {}, title), build(close));
  document.body.append(dlg);
  dlg.addEventListener("close", () => dlg.remove());
  dlg.showModal();
  dlg.querySelector("input")?.focus();
  return dlg;
}

/* Appearance */

const THEMES = [
  ["system", "System", "Light or dark, following this computer"],
  ["light", "Light", ""],
  ["dark", "Dark", ""],
  ["solarized-light", "Solarized light", ""],
  ["solarized-dark", "Solarized dark", ""],
];

function appearancePage() {
  const current = prefs.get("theme", "system");
  const density = prefs.get("density", "comfortable");
  const choose = (theme) => {
    prefs.set("theme", theme);
    document.documentElement.dataset.theme = theme;
  };
  return [
    h("h1", {}, "Appearance"),
    h("p", { class: "hint" }, "Saved in this browser only."),
    h("section", {}, h("h2", {}, "Theme"),
      h("div", { class: "themes", role: "radiogroup" }, THEMES.map(([key, label, note]) =>
        h("label", { class: "theme-choice" },
          h("input", { type: "radio", name: "theme", value: key, checked: key === current,
            onchange: () => choose(key) }),
          h("span", { class: "swatch", "data-swatch": key },
            h("span", { class: "sw-pane" }), h("span", { class: "sw-list" }), h("span", { class: "sw-accent" })),
          h("span", {}, label, note && h("span", { class: "hint" }, note)))))),
    h("section", {}, h("h2", {}, "Density"),
      h("div", { class: "choices" }, [["comfortable", "Comfortable"], ["compact", "Compact"]].map(([key, label]) =>
        h("label", {}, h("input", { type: "radio", name: "density", checked: key === density, onchange: () => {
          prefs.set("density", key);
          document.documentElement.dataset.density = key;
        } }), label)))),
  ];
}

/* Rules */

const FIELDS = [["title", "Subject"], ["body", "Text"], ["author", "Sender"], ["source", "Source"],
  ["kind", "Kind"], ["thread", "Conversation"], ["url", "Link"]];
const OPS = [["contains", "contains"], ["equals", "is"], ["startsWith", "begins with"], ["endsWith", "ends with"]];
const NOT_OPS = { contains: "does not contain", equals: "is not", startsWith: "does not begin with",
  endsWith: "does not end with" };

function select_(options, value, onchange, label) {
  return h("select", { onchange: (e) => onchange(e.target.value), "aria-label": label },
    options.map(([v, text]) => h("option", { value: v, selected: v === value }, text)));
}

function describeRule(r) {
  const byId = Object.fromEntries(state.labels.map((l) => [l.id, l.name]));
  const conds = r.spec.conditions.map((c) =>
    `${(FIELDS.find(([f]) => f === c.field)?.[1] || c.field).toLowerCase()} ${
      c.negate ? NOT_OPS[c.op] : OPS.find(([o]) => o === c.op)?.[1]} "${c.value}"`);
  const actions = [...r.spec.labels.map((id) => `label ${byId[id] || "?"}`),
    r.spec.archive && "archive", r.spec.markRead && "mark read"].filter(Boolean);
  return `If ${conds.join(r.spec.match === "any" ? " or " : " and ") || "always"}: ${actions.join(", ") || "nothing"}.`;
}

function ruleEditor(rule, onSave, onCancel) {
  const spec = structuredClone(rule.spec);
  let name = rule.name;
  const root = h("div", { class: "editor" });
  const error = h("p", { class: "error", role: "alert" });
  const draw = () => fill(root,
    row("Name", h("input", { value: name, placeholder: "e.g. Seminar mail", oninput: (e) => { name = e.target.value; } })),
    row("Applies if", select_([["all", "all of these match"], ["any", "any of these matches"]], spec.match,
      (v) => { spec.match = v; }, "Match")),
    h("div", { class: "conditions" }, spec.conditions.map((c, i) => h("div", { class: "cond" },
      select_(FIELDS, c.field, (v) => { c.field = v; }, "Field"),
      select_(OPS.map(([o, t]) => [o, t]).concat(OPS.map(([o]) => ["not:" + o, NOT_OPS[o]])),
        (c.negate ? "not:" : "") + c.op, (v) => { c.negate = v.startsWith("not:"); c.op = v.replace("not:", ""); }, "Comparison"),
      h("input", { value: c.value, "aria-label": "Value", oninput: (e) => { c.value = e.target.value; } }),
      h("button", { class: "quiet", onclick: () => { spec.conditions.splice(i, 1); draw(); } }, "Remove"))),
      h("button", { onclick: () => { spec.conditions.push({ field: "title", op: "contains", value: "", negate: false }); draw(); } },
        "Add condition")),
    row("Then", h("div", { class: "choices" },
      state.labels.map((l) => h("label", {},
        h("input", { type: "checkbox", checked: spec.labels.includes(l.id), onchange: (e) => {
          spec.labels = e.target.checked ? [...spec.labels, l.id] : spec.labels.filter((x) => x !== l.id);
        } }), h("span", { class: "dot", style: { background: l.color } }), `label ${l.name}`)),
      h("label", {}, h("input", { type: "checkbox", checked: spec.archive,
        onchange: (e) => { spec.archive = e.target.checked; } }), "archive"),
      h("label", {}, h("input", { type: "checkbox", checked: spec.markRead,
        onchange: (e) => { spec.markRead = e.target.checked; } }), "mark read"))),
    h("div", { class: "buttons" },
      h("button", { class: "primary", onclick: async () => {
        try { await onSave(name.trim(), spec); } catch (err) { error.textContent = err.message; }
      } }, "Save rule"),
      h("button", { onclick: onCancel }, "Cancel"), error));
  draw();
  return root;
}

async function rulesPage(editing) {
  const rules = await api("GET", "rules");
  const blank = { name: "", spec: { match: "all", labels: [], archive: false, markRead: false,
    conditions: [{ field: "title", op: "contains", value: "", negate: false }] } };
  const back = () => showSettings("rules");
  return [
    h("h1", {}, "Rules"),
    h("p", { class: "hint" }, "Rules run on each new notification, in this order."),
    editing === "new"
      ? ruleEditor(blank, async (name, spec) => { await api("POST", "rules", { name, spec }); back(); }, back)
      : h("div", { class: "buttons" },
        h("button", { class: "primary", onclick: () => showSettings("rules", "new") }, "New rule"),
        h("button", { onclick: async (e) => {
          e.target.disabled = true;
          const r = await api("POST", "rules/rerun");
          e.target.textContent = `Applied to past notifications: ${r.matched} matched`;
          refresh();
        } }, "Apply to past notifications")),
    rules.length ? h("ul", { class: "rows" }, rules.map((r) => editing === r.id
      ? h("li", {}, ruleEditor(r, async (name, spec) => { await api("PATCH", "rules/" + r.id, { name, spec }); back(); }, back))
      : h("li", { class: r.enabled ? null : "off" },
        h("div", { class: "row-main" }, h("strong", {}, r.name || "Unnamed rule"), h("p", { class: "hint" }, describeRule(r))),
        h("div", { class: "buttons" },
          h("label", {}, h("input", { type: "checkbox", checked: r.enabled, onchange: async (e) => {
            await api("PATCH", "rules/" + r.id, { enabled: e.target.checked });
            back();
          } }), "On"),
          h("button", { onclick: () => showSettings("rules", r.id) }, "Edit"),
          h("button", { class: "danger", onclick: async () => {
            if (!confirm(`Delete the rule "${r.name || "Unnamed rule"}"?`)) return;
            await api("DELETE", "rules/" + r.id);
            back();
          } }, "Delete")))))
      : h("p", { class: "empty" }, "No rules yet."),
  ];
}

/* Sources */

function ago(t) {
  if (!t) return "never";
  const s = Math.max(0, Math.round(Date.now() / 1000 - t));
  if (s < 90) return `${s} s ago`;
  if (s < 5400) return `${Math.round(s / 60)} min ago`;
  return when(t);
}

async function sourcesPage() {
  await loadMeta();
  return [
    h("h1", {}, "Sources"),
    h("p", { class: "hint" }, "A source that has not synced for a while is broken, not quiet."),
    h("table", { class: "table" },
      h("thead", {}, h("tr", {}, ["Source", "State", "Last synced", "Notifications"].map((t) => h("th", {}, t)))),
      h("tbody", {}, state.sources.health.map((s) => h("tr", {},
        h("td", {}, h("strong", {}, s.source), h("div", { class: "hint" }, s.kind)),
        h("td", {}, h("span", { class: "status" }, h("span", { class: "dot " + s.state }), s.state),
          s.detail && h("div", { class: "hint" }, s.detail),
          s.lastError && h("div", { class: "error" }, `Last error ${ago(s.lastErrorAt)}: ${s.lastError}`)),
        h("td", {}, ago(s.lastOk)),
        h("td", { class: "num" }, s.events))))),
  ];
}

/* API tokens */

function subsetPicker(name, options, picked) {
  const all = h("input", { type: "radio", name, checked: true });
  const some = h("input", { type: "radio", name });
  const boxes = options.map(([v, label]) => [v, h("input", { type: "checkbox" }), label]);
  const list = h("div", { class: "choices sub", hidden: true }, boxes.map(([, b, label]) => h("label", {}, b, label)));
  const sync = () => { list.hidden = all.checked; };
  all.addEventListener("change", sync);
  some.addEventListener("change", sync);
  picked.get = () => all.checked ? null : boxes.filter(([, b]) => b.checked).map(([v]) => v);
  return h("div", {}, h("div", { class: "choices" }, h("label", {}, all, "All"), h("label", {}, some, "Only these")), list);
}

/** "7 days", "36 hours": a window in seconds, in the unit it was given in. */
function span(seconds) {
  const [n, unit] = seconds % 86400 === 0 ? [seconds / 86400, "day"] : [Math.round(seconds / 3600), "hour"];
  return `${n} ${unit}${n === 1 ? "" : "s"}`;
}

function describeScope(scope) {
  const byId = Object.fromEntries(state.labels.map((l) => [l.id, l.name]));
  const sources = scope.sources ? scope.sources.join(", ") || "no sources" : "all sources";
  const labels = scope.labels ? "labelled " + (scope.labels.map((id) => byId[id] || "#" + id).join(" or ") || "nothing") : "";
  const time = [scope.since && `from ${when(scope.since)} on`, scope.within && `from the past ${span(scope.within)}`]
    .filter(Boolean).join(" and ");
  return [`Sees ${sources}${labels ? ", " + labels : ""}${time ? ", " + time : ""}.`,
    scope.write ? "May mark read, archive, star and label." : "Read-only."];
}

/** Any time, since a date, or a moving window of hours or days. */
function timePicker(picked) {
  const any = h("input", { type: "radio", name: "t-time", checked: true });
  const sinceOn = h("input", { type: "radio", name: "t-time" });
  const windowOn = h("input", { type: "radio", name: "t-time" });
  const date = h("input", { type: "date", class: "date", "aria-label": "Since", value: new Date().toISOString().slice(0, 10),
    onfocus: () => { sinceOn.checked = true; } });
  const amount = h("input", { type: "number", min: 1, value: 7, "aria-label": "How many", class: "narrow",
    onfocus: () => { windowOn.checked = true; } });
  const unit = h("select", { "aria-label": "Unit", onfocus: () => { windowOn.checked = true; } },
    h("option", { value: "86400" }, "days"), h("option", { value: "3600" }, "hours"));
  picked.get = () => {
    if (sinceOn.checked) {
      if (!date.value) throw new Error("Choose the date the token sees notifications from.");
      // Midnight at the start of that day, here.
      return { since: Math.floor(new Date(date.value + "T00:00").getTime() / 1000) };
    }
    if (windowOn.checked) {
      const n = Number(amount.value);
      if (!(n >= 1)) throw new Error("The window needs at least 1 hour or day.");
      return { within: Math.round(n) * Number(unit.value) };
    }
    return {};
  };
  return h("div", { class: "time-choices" },
    h("label", {}, any, "Any time"),
    h("label", {}, sinceOn, "Since", date),
    h("label", {}, windowOn, "From the past", amount, unit));
}

async function tokensPage(created) {
  const tokens = await api("GET", "tokens");
  const newToken = () => openDialog("New API token", (close) => {
    const name = h("input", { placeholder: "e.g. phone" });
    const sources = {}, labels = {}, time = {};
    const write = h("input", { type: "checkbox" });
    const error = h("p", { class: "error", role: "alert" });
    const create = async () => {
      if (!name.value.trim()) { error.textContent = "Give the token a name."; return; }
      try {
        const t = await api("POST", "tokens", { name: name.value.trim(),
          scope: { sources: sources.get(), labels: labels.get(), write: write.checked, ...time.get() } });
        close();
        showSettings("tokens", t);
      } catch (err) { error.textContent = err.message; }
    };
    return [
      row("Name", name),
      row("Sources", subsetPicker("t-sources", state.sources.configured.map((x) => [x.name, x.name]), sources)),
      row("Labels", subsetPicker("t-labels", state.labels.map((l) => [l.id, l.name]), labels)),
      row("Time", timePicker(time), "By when a notification was sent. A window moves: older ones drop out."),
      row("Changes", h("label", { class: "check" }, write, "May mark read, archive, star and label")),
      error,
      h("div", { class: "buttons end" }, h("button", { onclick: close }, "Cancel"),
        h("button", { class: "primary", onclick: create }, "Create token")),
    ];
  });
  return [
    h("h1", {}, "API tokens"),
    h("p", { class: "hint" }, "Other programs sign in with a token, sent as ", h("code", {}, "Authorization: Bearer agl_…"),
      ". A token sees only notifications from its sources that carry one of its labels."),
    created && h("div", { class: "callout", role: "status" },
      h("strong", {}, `Token "${created.name}" created. Copy it now: it is not shown again.`),
      h("div", { class: "buttons" },
        h("input", { class: "mono", value: created.token, readonly: true, onfocus: (e) => e.target.select() }),
        h("button", { onclick: async (e) => {
          await navigator.clipboard.writeText(created.token);
          e.target.textContent = "Copied";
        } }, "Copy"))),
    h("div", { class: "buttons" }, h("button", { class: "primary", onclick: newToken }, "New token")),
    tokens.length ? h("ul", { class: "rows" }, tokens.map((t) => h("li", {},
      h("div", { class: "row-main" }, h("strong", {}, t.name),
        t.scope && describeScope(t.scope).map((line) => h("p", { class: "hint" }, line)),
        h("p", { class: "hint" }, `Created ${when(t.createdAt)} · last used ${ago(t.lastUsed)}`)),
      h("div", { class: "buttons" }, h("button", { class: "danger", onclick: async () => {
        if (!confirm(`Revoke "${t.name}"? Programs using it stop working at once.`)) return;
        await api("DELETE", "tokens/" + t.id);
        showSettings("tokens");
      } }, "Revoke")))))
      : h("p", { class: "empty" }, "No tokens yet."),
  ];
}

/* Sign-in security */

/** The password, asked for in the dialog of the change it confirms. */
const passwordField = () => h("input", { type: "password", autocomplete: "current-password" });

function addKeyDialog() {
  openDialog("Add a security key", (close) => {
    const name = h("input", { placeholder: "e.g. Titan" });
    const password = passwordField();
    const status = h("p", { class: "hint", role: "status" });
    const error = h("p", { class: "error", role: "alert" });
    const go = h("button", { class: "primary", onclick: async () => {
      error.textContent = "";
      if (!password.value) { error.textContent = "Enter your password."; return; }
      go.disabled = true;
      try {
        const o = await api("POST", "second-factors/webauthn/challenge");
        status.textContent = "Insert the key and tap it now.";
        const cred = await navigator.credentials.create({ publicKey: {
          challenge: fromB64(o.challenge), rp: o.rp,
          user: { id: fromB64(o.user.id), name: o.user.name, displayName: o.user.displayName },
          pubKeyCredParams: [{ type: "public-key", alg: -7 }],
          excludeCredentials: o.excludeCredentials.map((id) => ({ type: "public-key", id: fromB64(id) })),
          authenticatorSelection: { residentKey: "discouraged", userVerification: "discouraged" },
          attestation: "none", timeout: 60000 } });
        await api("POST", "second-factors/webauthn", { password: password.value,
          name: name.value.trim() || "Security key",
          clientDataJSON: toB64(cred.response.clientDataJSON),
          authenticatorData: toB64(cred.response.getAuthenticatorData()),
          publicKey: toB64(cred.response.getPublicKey()), alg: cred.response.getPublicKeyAlgorithm() });
        close();
        showSettings("security", "Security key added.");
      } catch (err) {
        status.textContent = "";
        error.textContent = err.name === "NotAllowedError" ? "No key was tapped. Try again." : err.message;
        go.disabled = false;
      }
    } }, "Add and tap the key");
    return [row("Name", name), row("Password", password, "Needed for every change here."), status, error,
      h("div", { class: "buttons end" }, h("button", { onclick: close }, "Cancel"), go)];
  });
}

function addAppDialog() {
  openDialog("Add an authenticator app", (close) => {
    const name = h("input", { placeholder: "e.g. phone" });
    const password = passwordField();
    const error = h("p", { class: "error", role: "alert" });
    const body = h("div");
    const step1 = () => fill(body,
      row("Name", name), row("Password", password, "Needed for every change here."), error,
      h("div", { class: "buttons end" }, h("button", { onclick: close }, "Cancel"),
        h("button", { class: "primary", onclick: async () => {
          if (!password.value) { error.textContent = "Enter your password."; return; }
          try { step2(await api("POST", "second-factors/totp/secret")); } catch (err) { error.textContent = err.message; }
        } }, "Continue")));
    const step2 = (o) => {
      const qr = qrcode(0, "M");
      qr.addData(o.uri);
      qr.make();
      const code = h("input", { placeholder: "123456", inputmode: "numeric", autocomplete: "one-time-code" });
      const add = async () => {
        try {
          await api("POST", "second-factors/totp", { password: password.value,
            name: name.value.trim() || "Authenticator app", code: code.value });
          close();
          showSettings("security", "Authenticator app added.");
        } catch (err) { error.textContent = err.message; }
      };
      code.addEventListener("keydown", (e) => { if (e.key === "Enter") add(); });
      fill(body,
        h("p", {}, "Scan the code with the app, then enter the six digits it shows."),
        h("img", { class: "qr", src: qr.createDataURL(5, 2), alt: "QR code for the authenticator app" }),
        h("p", { class: "hint" }, "Or type this key into the app: ", h("code", {}, o.secret)),
        row("Code", code), error,
        h("div", { class: "buttons end" }, h("button", { onclick: close }, "Cancel"),
          h("button", { class: "primary", onclick: add }, "Add app")));
      code.focus();
    };
    step1();
    return body;
  });
}

function removeFactorDialog(f) {
  openDialog(`Remove "${f.name}"`, (close) => {
    const password = passwordField();
    const error = h("p", { class: "error", role: "alert" });
    return [h("p", {}, "It can no longer be used to sign in."), row("Password", password), error,
      h("div", { class: "buttons end" }, h("button", { onclick: close }, "Cancel"),
        h("button", { class: "danger", onclick: async () => {
          try {
            await api("DELETE", "second-factors/" + f.id, { password: password.value });
            close();
            showSettings("security", `Removed "${f.name}".`);
          } catch (err) { error.textContent = err.message; }
        } }, "Remove"))];
  });
}

async function securityPage(notice) {
  const factors = await api("GET", "second-factors");
  const kinds = { webauthn: "Security key", totp: "Authenticator app" };
  const on = factors.length > 0;
  return [
    h("h1", {}, "Sign-in security"),
    notice && h("p", { class: "notice", role: "status" }, notice),
    h("section", {},
      h("h2", {}, "Two-step sign-in"),
      h("div", { class: "status-line " + (on ? "on" : "off") },
        h("strong", {}, on ? "On" : "Off"),
        h("span", {}, on
          ? `Signing in takes the password and one of these ${factors.length === 1 ? "method" : `${factors.length} methods`}.`
          : "Signing in takes the password alone.")),
      on && factors.length === 1 && h("p", { class: "hint" }, "Add a second method, so that losing one does not lock you out."),
      on && h("ul", { class: "rows" }, factors.map((f) => h("li", {},
        h("div", { class: "row-main" }, h("strong", {}, f.name),
          h("p", { class: "hint" }, `${kinds[f.kind] || f.kind} · added ${when(f.createdAt)} · last used ${ago(f.lastUsed)}`)),
        h("div", { class: "buttons" }, h("button", { onclick: () => removeFactorDialog(f) }, "Remove"))))),
      h("div", { class: "buttons" },
        h("button", { class: on ? null : "primary", onclick: addKeyDialog }, "Add a security key"),
        h("button", { onclick: addAppDialog }, "Add an authenticator app"))),
    h("section", {},
      h("h2", {}, "API tokens"),
      h("p", { class: "hint" }, "Tokens sign in without a second step; each sees only what its scope allows. ",
        h("a", { href: "#", onclick: (e) => { e.preventDefault(); showSettings("tokens"); } }, "Manage tokens"))),
  ];
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
  if (e.ctrlKey || e.metaKey || e.altKey || state.view !== "list" || document.querySelector("dialog[open]")) return;
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
    showList();
    loadList(false);
  }, 250);
});

$("sort").addEventListener("change", (e) => {
  state.sort = e.target.value;
  try { localStorage.setItem("angelia.sort", state.sort); } catch (_) { /* private mode */ }
  loadList(true);
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
  $("sort").value = state.sort;
  await refresh();
  connectEvents();
}

start();