// SQLSpec: the book of SQLSpec's definitions (data/sqlspec.json, written by build/pages/sqlspec.mjs from the Verus
// source). #/sqlspec is the overview: the meaning ⟦Q⟧(db) and its definition, a search box and the chapters.
// #/sqlspec/<chapter>[/<section>][?d=<name>] shows one chapter: the contents and search beside it, its picture,
// then its sections, each with its definitions grouped as Syntax, Meaning, Typing, Well-formed and Capacity. Code is
// shown verbatim with its source line numbers; a name in the code links to the section that defines it.
import { h, s, icon, math } from "../lib.js";

/** Lines of Meaning code open at first in a section (the first block opens up to FIRST_MAX lines). */
const OPEN_LINES = 36, FIRST_MAX = 70;
const KEYWORDS = new Set(["pub", "open", "closed", "spec", "proof", "fn", "let", "if", "else", "match", "enum", "struct", "type", "const",
  "decreases", "requires", "ensures", "forall", "exists", "assert", "by", "is", "as", "implies", "true", "false", "in", "mut", "return"]);
const TYPES = new Set(["int", "nat", "bool", "u8", "u32", "u128", "i32", "i64", "i128", "Seq", "Box", "Option", "Result", "Some", "None", "Ok", "Err"]);

// ------------------------------------------------------------------------------------------------ the book index
const indexes = new WeakMap();
/** Chapter and section numbers, lookups and the search entries of one data object. */
function bookOf(data) {
  if (indexes.has(data)) return indexes.get(data);
  const sections = new Map();
  const entries = [];
  data.chapters.forEach((ch, i) => {
    ch.n = i + 1;
    entries.push({ kind: "chapter", title: ch.title, sub: `Chapter ${ch.n}`, href: `#/sqlspec/${ch.id}`, text: ch.title.toLowerCase(), order: entries.length });
    ch.sections.forEach((sec, j) => {
      sec.num = `${ch.n}.${j + 1}`;
      sections.set(`${ch.id}/${sec.id}`, { ch, sec });
      entries.push({ kind: "section", title: sec.title, sub: `${sec.num} · ${ch.title}`, href: `#/sqlspec/${ch.id}/${sec.id}`, text: `${sec.title} ${ch.title}`.toLowerCase(), order: entries.length });
      for (const g of sec.groups) for (const b of g.blocks) {
        if (b.kind === "arm") continue;
        if (b.kind === "variant" && g.key !== "syntax") continue;
        entries.push({ kind: b.kind, title: b.name, sub: `${sec.num} ${sec.title}`, href: hrefOf(`${ch.id}/${sec.id}`, b.name),
          doc: b.doc ? b.doc.replace(/\s+/g, " ") : "", text: `${b.name} ${b.doc || ""}`.toLowerCase(), order: entries.length });
      }
    });
  });
  const B = { data, sections, entries, chapter: (id) => data.chapters.find((c) => c.id === id) || null };
  indexes.set(data, B);
  return B;
}
const hrefOf = (at, d) => `#/sqlspec/${at}${d ? `?d=${encodeURIComponent(d)}` : ""}`;

// ------------------------------------------------------------------------------------------------ text and code
/** Text with `code` set in mono. */
const inline = (t) => t.split(/`([^`]+)`/).map((p, i) => (i % 2 ? h("code", p) : p));

/** Doc comment text: paragraphs and `- ` lists, `code` set in mono. */
function docEl(text) {
  const out = h("div.doc");
  let list = null, para = null;
  for (const raw of text.split("\n")) {
    const line = raw.trim();
    if (!line) { list = para = null; continue; }
    const item = /^(-|\d+\.)\s+(.*)$/.exec(line);
    if (item) {
      if (!list) { list = h(item[1] === "-" ? "ul" : "ol"); out.append(list); }
      para = h("li", inline(item[2]));
      list.append(para);
    } else if (para) para.append(" ", ...inline(line));
    else { para = h("p", inline(line)); out.append(para); }
  }
  return out;
}

const TOKEN = /(\/\/.*$)|("(?:[^"\\]|\\.)*")|([A-Z]\w*)::([A-Z]\w*)|(0x[0-9a-fA-F_]+\w*|\d[\d_]*(?:[a-z]\w*)?)|([A-Za-z_]\w*)|([^\w\s]+|\s+)/g;
/** One line of code as tokens: keywords, types, comments, and links to the sections of named definitions (in an
 *  enum's own code, its constructors link to the sections that show them). */
function tokens(line, B, self) {
  const out = [];
  const link = (at, d, text) => h("a.ref", { href: hrefOf(at, d), "data-ref": d }, text);
  for (const m of line.matchAll(TOKEN)) {
    const [all, comment, str, pathA, pathB, num, word] = m;
    if (comment) out.push(h("span.c", comment));
    else if (str) out.push(h("span.s", str));
    else if (pathA) {
      const full = `${pathA}::${pathB}`;
      if (B.data.variants[full]) out.push(link(B.data.variants[full], full, full));
      else {
        const d = B.data.defs[pathA];
        out.push(d && pathA !== self ? link(d.at, pathA, pathA) : h("span.t", pathA), `::${pathB}`);
      }
    } else if (num) out.push(h("span.n", num));
    else if (word) {
      const d = B.data.defs[word], own = self && B.data.variants[`${self}::${word}`];
      if (d && word !== self) out.push(link(d.at, word, word));
      else if (own) out.push(link(own, `${self}::${word}`, word));
      else if (KEYWORDS.has(word)) out.push(h("span.k", word));
      else if (TYPES.has(word) || /^[A-Z]/.test(word)) out.push(h("span.t", word));
      else out.push(word);
    } else out.push(all);
  }
  return out;
}

/** Verbatim code with its source line numbers; indentation kept as a hanging indent so long lines wrap. `omit`:
 *  [first line, count] of the runs of comment lines left out (build/pages/sqlspec.mjs, OMIT), each shown as "⋯". */
function codeView(code, first, B, self, omit = []) {
  const gaps = new Map(omit);
  const rows = [];
  let n = first;
  for (const line of code.split("\n")) {
    const ind = line.length - line.trimStart().length;
    while (gaps.has(n)) {
      rows.push(h("div.ln.ln--gap", { style: `--ind:${ind}` }, h("span.ln__n"), h("span.ln__c", "⋯")));
      n += gaps.get(n);
    }
    rows.push(h("div.ln", { "data-ind": ind, style: `--ind:${ind}` },
      h("span.ln__n", { "aria-hidden": "true" }, String(n)),
      h("span.ln__c", tokens(line.slice(ind), B, self))));
    n++;
  }
  return h("div.code-lines", rows);
}

// ------------------------------------------------------------------------------------------------ blocks
const lineCount = (b) => b.code.split("\n").length;

/** One definition, constructor or match arm: its head (a toggle), its doc comment, its code (built when opened). */
function blockEl(b, B, open) {
  const n = lineCount(b);
  const self = b.kind === "def" ? b.name : b.kind === "arm" ? b.of : null;
  const label = b.kind === "arm" ? [h("span.blk__name", b.of), h("span.blk__arm", b.pat)] : h("span.blk__name", b.name);
  const size = h("span.blk__size", `${n} line${n === 1 ? "" : "s"}`);
  const toggle = h("button.blk__toggle", { type: "button", "aria-expanded": "false" }, icon("chevron-right", { cls: "blk__chev" }), label);
  const code = h("div.blk__code");
  const el = h(`div.blk.is-${b.kind}`, { "data-name": b.name },
    h("div.blk__head", toggle, size, h("span.blk__file", b.file)),
    b.doc ? docEl(b.doc) : null,
    code);
  el.isOpen = () => !code.hidden && Boolean(code.firstChild);
  el.setOpen = (on) => {
    if (on && !code.firstChild) code.append(codeView(b.code, b.line, B, self, b.omit));
    code.hidden = !on;
    size.hidden = on;
    el.classList.toggle("is-open", on);
    toggle.setAttribute("aria-expanded", String(on));
  };
  toggle.addEventListener("click", () => el.setOpen(!el.isOpen()));
  el.setOpen(open);
  return el;
}

/** The blocks of one section by group (labelled when there are two or more); Syntax open, Meaning open while it
 *  fits OPEN_LINES, the rest closed. */
function sectionEl(ch, sec, B) {
  let budget = OPEN_LINES, first = true;
  const groups = sec.groups.map((g) => h(`div.grp.grp--${g.key}`,
    sec.groups.length > 1 ? h("h3.grp__label", g.label) : null,
    g.blocks.map((b) => {
      let open = g.key === "syntax";
      if (g.key === "meaning") {
        const n = lineCount(b);
        open = (first && n <= FIRST_MAX) || n <= budget;
        if (open) budget -= n;
        else budget = 0;
        first = false;
      }
      return blockEl(b, B, open);
    })));
  const at = `${ch.id}/${sec.id}`;
  return h("section.sec", { id: `sec-${sec.id}`, "data-sec": sec.id },
    h("header.sec__head",
      h("span.sec__num", sec.num),
      h("h2", sec.title),
      h("a.sec__link", { href: hrefOf(at), "aria-label": `Link to ${sec.num} ${sec.title}` }, icon("link"))),
    groups);
}

// ------------------------------------------------------------------------------------------------ pictures
function picture(P) {
  if (!P) return null;
  const box = (b, cls = "") => h(`a.pbox${cls}`, { href: hrefOf(b.to) }, h("b", b.name), b.sub ? h("span", b.sub) : null);
  const root = h("div.pic__top", h("a.pbox.is-root", { href: hrefOf(P.root.to) }, h("b", P.root.name)));
  if (P.kind === "pipeline") {
    return h("figure.pic.pic--pipe", root,
      h("ol.pic__steps", P.steps.map((s, i) => h("li",
        i ? icon("arrow-right", { cls: "pic__arrow" }) : null,
        h("a.pbox", { href: hrefOf(s.to) }, h("b", s.name), h("span", s.sub), h("em", s.fn))))));
  }
  return h("figure.pic.pic--tree", root,
    h("div.pic__boxes", P.boxes.map((b) => (b.kids
      ? h("div.pic__nest", box(b, ".is-parent"), h("div.pic__kids", b.kids.map((k) => box(k, ".is-kid"))))
      : box(b)))),
    P.notes.length ? h("div.pic__notes", P.notes.map((n) => h("a.pnote", { href: hrefOf(n.to) }, h("b", n.label), h("span", n.text)))) : null);
}

// ------------------------------------------------------------------------------------------------ search
const KIND_ICON = { chapter: "book-open", section: "rows-3", def: "square-function", variant: "braces" };
const KIND_RANK = { chapter: 0, section: 1, def: 2, variant: 3 };

function find(B, q) {
  const query = q.trim().toLowerCase();
  if (!query) return [];
  const words = query.split(/\s+/);
  const out = [];
  for (const e of B.entries) {
    const t = e.title.toLowerCase();
    let score = 0;
    if (t === query) score = 100;
    else if (t.startsWith(query)) score = 80;
    else if (t.includes(query)) score = 60;
    else if (words.every((w) => t.includes(w))) score = 50;
    else if (words.every((w) => e.text.includes(w))) score = 20;
    if (score) out.push([score, e]);
  }
  out.sort((a, b) => b[0] - a[0] || KIND_RANK[a[1].kind] - KIND_RANK[b[1].kind] || a[1].order - b[1].order);
  return out.map(([, e]) => e);
}

/** The first `n` characters (whole words; a `code` span cut short is closed). */
function shorten(t, n) {
  if (t.length <= n) return t;
  const cut = t.slice(0, n).replace(/\s+\S*$/, "");
  return `${cut}${(cut.match(/`/g) || []).length % 2 ? "`" : ""} …`;
}

/** The search box: results as you type; arrows and Enter choose one; "/" focuses it. */
function searchBox(B, { big } = {}) {
  const input = h("input", { type: "search", placeholder: "Search SQLSpec", "aria-label": "Search SQLSpec", autocomplete: "off", spellcheck: "false", "aria-controls": "sq-results", "aria-expanded": "false" });
  const list = h("div.search__list", { id: "sq-results", role: "listbox", hidden: true });
  const glass = s("svg", { class: "ic search__ic", viewBox: "0 0 24 24", "aria-hidden": "true" }, s("circle", { cx: 11, cy: 11, r: 8 }), s("path", { d: "m21 21-4.3-4.3" }));
  const el = h(`div.search${big ? ".is-big" : ""}`, h("label.search__field", glass, input, h("kbd", "/")), list);
  let results = [], active = 0;
  const LIMIT = 8;
  const close = () => { list.hidden = true; input.setAttribute("aria-expanded", "false"); };
  const go = (e) => { close(); input.value = ""; input.blur(); visit(e.href); };
  const paint = () => {
    list.replaceChildren();
    if (!input.value.trim()) return close();
    list.hidden = false;
    input.setAttribute("aria-expanded", "true");
    if (!results.length) { list.append(h("p.search__none", "No match")); return; }
    results.slice(0, LIMIT).forEach((e, i) => {
      const mono = e.kind === "def" || e.kind === "variant";
      const a = h(`a.hit${i === active ? ".is-active" : ""}`, { href: e.href, role: "option", "aria-selected": String(i === active) },
        h("span.hit__ic", icon(KIND_ICON[e.kind])),
        h("span.hit__t", h(mono ? "code" : "span", e.title), h("small", e.sub)),
        e.doc ? h("span.hit__d", inline(shorten(e.doc, 110))) : null);
      a.addEventListener("mousedown", (ev) => ev.preventDefault());
      a.addEventListener("click", (ev) => { ev.preventDefault(); go(e); });
      list.append(a);
    });
    if (results.length > LIMIT) list.append(h("p.search__more", `${results.length - LIMIT} more`));
  };
  input.addEventListener("input", () => { results = find(B, input.value); active = 0; paint(); });
  input.addEventListener("focus", () => { if (input.value.trim()) paint(); });
  input.addEventListener("blur", () => setTimeout(close, 120));
  input.addEventListener("keydown", (ev) => {
    const n = Math.min(results.length, LIMIT);
    if (ev.key === "ArrowDown" && n) { active = (active + 1) % n; paint(); ev.preventDefault(); }
    else if (ev.key === "ArrowUp" && n) { active = (active + n - 1) % n; paint(); ev.preventDefault(); }
    else if (ev.key === "Enter" && n) { go(results[active]); ev.preventDefault(); }
    else if (ev.key === "Escape") { input.value = ""; close(); input.blur(); }
  });
  return el;
}

/** Go to an address of the page; the address on screen again jumps again (the browser sends no hashchange). */
function visit(href) {
  if (location.hash === href) dispatchEvent(new HashChangeEvent("hashchange"));
  else location.hash = href;
}

let bound = false;
/** Once: "/" focuses the search box of the page on screen; scrolling hides a preview; a link to the address on
 *  screen jumps again. */
function bindOnce() {
  if (bound) return;
  bound = true;
  document.addEventListener("click", (ev) => {
    const a = ev.target.closest && ev.target.closest('.page-sqlspec a[href^="#/sqlspec"]');
    if (!a || ev.defaultPrevented || ev.button !== 0 || ev.metaKey || ev.ctrlKey || ev.shiftKey || ev.altKey) return;
    if (a.getAttribute("href") === location.hash) { ev.preventDefault(); visit(location.hash); }
  });
  addEventListener("scroll", () => { for (const c of document.querySelectorAll(".page-sqlspec .peek")) c.hidden = true; }, { passive: true });
  document.addEventListener("keydown", (ev) => {
    if (ev.key !== "/" || ev.metaKey || ev.ctrlKey || ev.altKey) return;
    const t = ev.target;
    if (t && (t.isContentEditable || /^(INPUT|TEXTAREA|SELECT)$/.test(t.tagName))) return;
    const input = document.querySelector(".page-sqlspec .search input");
    if (input && input.offsetParent) { ev.preventDefault(); input.focus(); }
  });
}

// ------------------------------------------------------------------------------------------------ preview
/** A small card under a code link on hover: the name, the first sentence of its doc comment, its section. */
function preview(root, B) {
  const card = h("div.peek", { hidden: true, role: "tooltip" });
  let timer = 0;
  const hide = () => { clearTimeout(timer); card.hidden = true; };
  root.addEventListener("mouseover", (ev) => {
    const a = ev.target.closest && ev.target.closest("a.ref");
    if (!a || !matchMedia("(hover: hover)").matches) return;
    clearTimeout(timer);
    timer = setTimeout(() => {
      const name = a.dataset.ref;
      const d = B.data.defs[name];
      const at = d ? d.at : B.data.variants[name];
      const where = B.sections.get(at);
      if (!where) return;
      card.replaceChildren(h("code.peek__n", name), d && d.sum ? docEl(d.sum) : null, h("span.peek__w", `${where.sec.num} ${where.sec.title}`));
      card.hidden = false;
      const r = a.getBoundingClientRect(), w = Math.min(360, innerWidth - 16);
      card.style.width = `${w}px`;
      card.style.left = `${Math.max(8, Math.min(r.left, innerWidth - w - 8))}px`;
      const below = r.bottom + 8, hgt = card.offsetHeight;
      card.style.top = `${below + hgt > innerHeight - 8 ? Math.max(8, r.top - hgt - 8) : below}px`;
    }, 220);
  });
  root.addEventListener("mouseout", (ev) => { if (ev.target.closest && ev.target.closest("a.ref")) hide(); });
  return card;
}

// ------------------------------------------------------------------------------------------------ the overview
function overview(B) {
  const { data } = B;
  const M = data.meaning;
  const withMath = (t) => t.split(/\{([^}]+)\}/).map((p, i) => (i % 2 ? math(p) : p));
  const chips = (ch) => {
    const P = ch.picture;
    return P.kind === "pipeline" ? P.steps.map((s) => s.name) : P.boxes.map((b) => b.name);
  };
  return h("div", h("div.wrap.sq-home",
    h("header.page-head",
      h("h1", data.title),
      h("p", data.lead)),
    searchBox(B, { big: true }),
    h("section.card.meaning",
      h("div.meaning__f",
        h("div.meaning__math", math(M.formula)),
        h("p", withMath(M.text)),
        h("a.go", { href: hrefOf(B.data.defs[M.def].at, M.def) }, h("code", M.def), icon("arrow-right"))),
      h("div.meaning__code", h("div.blk__head", h("span.blk__name", M.def), h("span.blk__file", M.file)),
        codeView(M.code, M.line, B, M.def, M.omit))),
    h("ol.chaps", data.chapters.map((ch) => h("li", h("a.chap", { href: `#/sqlspec/${ch.id}` },
      h("span.chap__n", String(ch.n)),
      h("strong.chap__t", ch.title, icon("arrow-right")),
      h("span.chap__c", chips(ch).map((c) => h("code", c)))))))));
}

// ------------------------------------------------------------------------------------------------ a chapter
function chapterView(B, ch) {
  const { data } = B;
  const i = data.chapters.indexOf(ch);
  const prev = data.chapters[i - 1], next = data.chapters[i + 1];
  const toc = h("nav.toc", { "aria-label": "Chapters" },
    h("ol", data.chapters.map((c) => h(`li${c === ch ? ".is-current" : ""}`,
      h("a.toc__ch", { href: `#/sqlspec/${c.id}`, "aria-current": c === ch ? "true" : null }, h("span", String(c.n)), c.title),
      c === ch ? h("ol", c.sections.map((s) => h("li", h("a.toc__sec", { href: hrefOf(`${c.id}/${s.id}`), "data-sec": s.id }, h("span", s.num), s.title)))) : null))));
  const contents = h("details.toc-m", h("summary", icon("menu"), `${ch.n} ${ch.title}`, icon("chevron-down", { cls: "toc-m__chev" })), toc.cloneNode(true));
  contents.addEventListener("click", (ev) => { if (ev.target.closest("a")) contents.open = false; });
  const secs = ch.sections.map((sec) => sectionEl(ch, sec, B));
  const pager = h("nav.pager", { "aria-label": "Previous and next chapter" },
    prev ? h("a.pager__a.is-prev", { href: `#/sqlspec/${prev.id}` }, icon("arrow-right", { cls: "pager__back" }), h("span", h("small", `Chapter ${prev.n}`), prev.title)) : h("span"),
    next ? h("a.pager__a.is-next", { href: `#/sqlspec/${next.id}` }, h("span", h("small", `Chapter ${next.n}`), next.title), icon("arrow-right")) : h("span"));
  const el = h("div", h("div.wrap.sq-doc",
    h("header.ch-head",
      h("a.ch-head__book", { href: "#/sqlspec" }, data.title),
      h("h1", h("span.ch-head__n", String(ch.n)), ch.title)),
    h("aside.side", searchBox(B), contents, toc),
    h("article.chapter", picture(ch.picture), secs, pager)));
  el.sections = secs;
  return el;
}

/** Scroll to a section, or to a definition (opened); mark it for a moment. */
function jump(el, secId, name, smooth) {
  let target = null;
  if (name) {
    target = [...el.querySelectorAll(".blk")].find((b) => b.dataset.name === name) || null;
    if (target && !target.isOpen()) target.setOpen(true);
  }
  if (!target && secId) target = el.querySelector(`#sec-${CSS.escape(secId)}`);
  for (const x of el.querySelectorAll(".is-hit")) x.classList.remove("is-hit");
  if (!target) { scrollTo({ top: 0, behavior: smooth ? "smooth" : "auto" }); return; }
  target.scrollIntoView({ behavior: smooth ? "smooth" : "auto", block: "start" });
  target.classList.add("is-hit");
}

/** The contents mark the section at the top of the screen. */
function spy(el) {
  const links = new Map([...el.querySelectorAll(".side > .toc .toc__sec")].map((a) => [a.dataset.sec, a]));
  const seen = new Set();
  const mark = () => {
    const top = el.sections.find((s) => seen.has(s.dataset.sec)) || null;
    for (const [id, a] of links) a.classList.toggle("is-here", Boolean(top) && id === top.dataset.sec);
  };
  const io = new IntersectionObserver((xs) => {
    for (const x of xs) (x.isIntersecting ? seen.add(x.target.dataset.sec) : seen.delete(x.target.dataset.sec));
    mark();
  }, { rootMargin: "-80px 0px -55% 0px" });
  for (const s of el.sections) io.observe(s);
}

export default function render({ data, path, params }) {
  const B = bookOf(data);
  bindOnce();
  const ch = path[0] ? B.chapter(path[0]) : null;
  const el = ch ? chapterView(B, ch) : overview(B);
  el.append(preview(el, B));
  if (ch) {
    el.shown = () => { spy(el); if (path[1] || params.get("d")) jump(el, path[1], params.get("d"), false); };
    el.reroute = (p, q) => {
      if (p[0] !== ch.id) return false;
      jump(el, p[1], q.get("d"), true);
      return true;
    };
  } else el.reroute = (p) => !p[0];
  return el;
}
