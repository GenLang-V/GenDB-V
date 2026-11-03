// Example: one query from SQL to a verified answer. 1, the meaning: four aligned views (SQL template with its table and
// data, typed AST, SQLSpec tree, semantics), operator by operator, data flowing bottom to top; 2, the agent's code with
// its proof annotations and the proof chain to the fixed target; 3, the answer. Data: data/example.json
// (build/pages/example.mjs). Hovering an operator lights it in every view; hovering a proof step lights its code.
import { h, s, icon, math } from "../lib.js";

/** A formula: math() plus `^{x}` superscripts, `𝟙` the indicator, ` + ` ` − ` ` | ` spaced operators, `a_b` names. */
function fx(src) {
  const out = h("span.math", { role: "math", "aria-label": src.replace(/\^\{([^}]+)\}/g, "^$1").replace("𝟙", "1") });
  for (const part of src.split(/(\^\{[^}]+\}|𝟙| \+ | − | \| |: |\b[a-z]+(?:_[a-z]+)+\b)/u)) {
    if (!part) continue;
    if (part.startsWith("^{")) out.append(h("sup", part.slice(2, -1)));
    else if (part === "𝟙") out.append(h("span.f.ind", "1"));
    else if (part === " + " || part === " − " || part === " | ") out.append(h("span.s.bin", part.trim()));
    else if (part === ": ") out.append(h("span.s.colon", ":"));
    else if (part.includes("_")) out.append(h("span.f", part));
    else out.append(...math(part).childNodes);
  }
  return out;
}

/** Text with {x} parts set as math. */
const withMath = (t) => t.split(/\{([^}]+)\}/).map((p, i) => (i % 2 ? fx(p) : p));

/** A small arrow: up (data flow), down (proof chain) or right (between views). */
function arrow(dir) {
  const up = dir !== "right";
  return s("svg", { class: `ar ar--${dir}`, viewBox: up ? "0 0 14 30" : "0 0 30 14", "aria-hidden": "true" },
    s("path", { d: up ? "M7 28V6" : "M2 7H24" }),
    s("path", { class: "ar__head", d: up ? "M2 10 7 3l5 7" : "M20 2l7 5-7 5" }));
}

function part(n, id, title, line, ...body) {
  return h(`section.ex-part.ex-part--${id}`, { "aria-labelledby": `ex-${id}` },
    h("header.ex-part__head",
      h("span.ex-part__n", String(n)),
      h("div", h("h2", { id: `ex-${id}` }, title), line ? h("p", line) : null)),
    ...body);
}

/** Hovering (or tapping) an element with data-key="v" lights every element of `root` with the same key. */
function linkHover(root, key) {
  let hot = null;
  const light = (v) => {
    if (v === hot) return;
    hot = v;
    for (const el of root.querySelectorAll(`[data-${key}]`)) el.classList.toggle("is-hot", el.dataset[key] === v);
    root.classList.toggle("has-hot", Boolean(v));
  };
  root.addEventListener("pointerover", (e) => light(e.target.closest(`[data-${key}]`)?.dataset[key] || null));
  root.addEventListener("pointerleave", () => light(null));
  root.addEventListener("click", (e) => light(e.target.closest(`[data-${key}]`)?.dataset[key] || null));   // touch: stays lit
  root.addEventListener("focusin", (e) => light(e.target.closest(`[data-${key}]`)?.dataset[key] || null));
  root.addEventListener("focusout", () => light(null));
}

// ---------------------------------------------------------------- 1: the meaning

/** One-column rows as cells: kept rows, then dropped ones crossed out. */
const cells = (rows, dropped = [], cls = "") => h(`div.cells${cls}`,
  rows.map((v) => h("span.cell", String(v))),
  dropped.map((v) => h("span.cell.is-out", { "aria-label": `${v}, dropped` }, String(v))));

function sqlPanel(data) {
  const t = data.table;
  return h("div.fl-sql",
    h("pre.code.fl-code", data.sql.clauses.map((c) => h("span.fl-clause", { "data-l": c.level }, c.text))),
    h("div.fl-table",
      h("div.fl-table__name", icon("database"), t.name),
      h("div.fl-table__col", h("code", t.column), h("span", t.type)),
      cells(t.rows, [], ".is-col"),
      h("code.fl-table__check", t.check)),
    h("div.fl-param", fx(`${data.param.name} = ${data.param.value}`)));
}

function level(l, k, heads) {
  const view = (v) => h("span.fl-view", heads[v - 1]);
  return h(`div.fl-level.l${k}`,
    h(`div.fl-cell.v2.l${k}`, { "data-l": l.id }, view(2),
      h("div.fl-node.is-ast", h("strong", l.ast.op), h("code", l.ast.arg))),
    h(`div.fl-cell.v3.l${k}`, { "data-l": l.id }, view(3),
      h("div.fl-node.is-spec", h("code.fl-ctor", l.spec.ctor), l.spec.arg ? h("code.fl-arg", l.spec.arg) : null)),
    h(`div.fl-cell.v4.l${k}`, { "data-l": l.id }, view(4),
      h("div.fl-node.is-sem", h("div.fl-f", fx(l.sem)), cells(l.rows, l.dropped || [], k === 0 ? ".is-answer" : ""))));
}

function flow(data) {
  const heads = data.parts.meaning.heads;
  const head = (v) => h(`div.fl-head.v${v}`, h("span.fl-num", String(v)), heads[v - 1]);
  const ups = (g) => h(`div.fl-ups.g${g}`, { "aria-hidden": "true" }, [2, 3, 4].map((v) => h(`div.fl-up.v${v}.g${g}`, arrow("up"))));
  const fig = h("figure.fl",
    [1, 2, 3, 4].map((v) => h(`div.fl-bg.v${v}`, { "aria-hidden": "true" })),
    h("div.fl-p1", head(1), sqlPanel(data)),
    [2, 3, 4].map(head),
    [2, 3, 4].map((v) => h(`div.fl-side.v${v}`, { "aria-hidden": "true" }, arrow("right"))),
    level(data.levels[0], 0, heads), ups(0),
    level(data.levels[1], 1, heads), ups(1),
    level(data.levels[2], 2, heads),
    h("div.fl-foots",
      h("div.fl-foot.v2", h("span.fl-view", heads[1]), data.foot.types.map((t) => h("code", t))),
      h("div.fl-foot.v3", h("span.fl-view", heads[2]), fx(data.foot.domain)),
      h("div.fl-foot.v4", h("span.fl-view", heads[3]), fx(data.foot.result))));
  linkHover(fig, "l");
  return fig;
}

// ---------------------------------------------------------------- 2: code and proof

const KEYWORDS = new Set(["pub", "fn", "let", "mut", "ghost", "while", "if", "else", "proof", "requires", "ensures", "invariant", "decreases", "assert", "forall", "implies", "by", "use", "mod", "as"]);

/** One code line's text as spans: comments, keywords, lemma names, numbers. */
function tokens(text) {
  const out = [];
  const comment = text.indexOf("//");
  const body = comment >= 0 ? text.slice(0, comment) : text;
  for (const part of body.split(/(\b[A-Za-z_][A-Za-z0-9_]*\b|\b\d[\d_]*(?:u64|usize|int|nat)?\b)/)) {
    if (!part) continue;
    if (KEYWORDS.has(part)) out.push(h("span.t-kw", part));
    else if (/^lemma_/.test(part)) out.push(h("span.t-lemma", part));
    else if (/^\d/.test(part)) out.push(h("span.t-num", part));
    else out.push(part);
  }
  if (comment >= 0) out.push(h("span.t-com", text.slice(comment)));
  return out;
}

function codeView(code, legend) {
  const regionAt = new Map();
  for (const r of code.regions) for (let n = r.from; n <= r.to; n++) regionAt.set(n, r);
  const key = new Set(code.key);
  const byN = new Map(code.lines.map((l) => [l.n, l]));
  // a comment inside a proof block is proof
  const role = (l) => {
    if (l.kind !== "comment") return l.kind;
    const near = (d) => { for (let n = l.n + d; byN.has(n); n += d) if (byN.get(n).kind !== "comment" && byN.get(n).kind !== "blank") return byN.get(n).kind; return null; };
    return near(-1) === "proof" && near(1) === "proof" ? "proof" : "comment";
  };
  const pre = h("pre.code.ex-code", { "aria-label": code.file });
  // a gap mark for hidden lines between key lines, tinted when all of them are proof (or all fixed)
  const gap = (from, to) => {
    const kinds = new Set(code.lines.slice(from - 1, to).map(role).filter((k) => k !== "blank"));
    if (!kinds.size) return null;
    const one = kinds.size === 1 ? [...kinds][0] : "";
    return h(`span.ln-gap${one === "proof" || one === "fixed" ? `.k-${one}` : ""}`, { "aria-hidden": "true" }, "⋯");
  };
  let lastKey = 0;
  for (const l of code.lines) {
    const isKey = key.has(l.n);
    const mark = isKey && lastKey && l.n > lastKey + 1 ? gap(lastKey + 1, l.n - 1) : null;
    if (mark) pre.append(mark);
    if (isKey) lastKey = l.n;
    const r = regionAt.get(l.n);
    const tagged = r && r.tag && r.from === l.n;
    const indent = /^ */.exec(l.text)[0].length;
    const k = role(l);
    pre.append(h(`span.ln.k-${k}${isKey ? "" : ".nk"}${tagged ? ".has-tag" : ""}`, { "data-node": r ? r.node : null },
      h("span.ln__n", String(l.n)),
      h("span.ln__c", { style: `--ind:${indent}ch` }, tokens(l.text.slice(indent))),
      tagged ? h(`span.ln__tag.k-${byN.get(r.from).kind}`, r.tag) : null));
  }
  const mode = (full) => {
    pre.classList.toggle("is-full", full);
    for (const b of bar.querySelectorAll("button")) b.setAttribute("aria-pressed", String((b.dataset.full === "1") === full));
  };
  const bar = h("div.ex-codebar",
    h("ul.ex-legend", ["exec", "proof", "fixed"].map((k) => h(`li.k-${k}`, legend[k]))),
    h("div.ex-toggle", { role: "group", "aria-label": "Lines" },
      h("button", { type: "button", "data-full": "0", "aria-pressed": "true", onclick: () => mode(false) }, "Key lines"),
      h("button", { type: "button", "data-full": "1", "aria-pressed": "false", onclick: () => mode(true) }, "Full code")));
  return h("div.ex-codebox", bar, pre);
}

function chainView(chain, title) {
  return h("div.ex-chain",
    h("div.ex-chain__head", title),
    h("div.chain", chain.map((n, i) => [
      i ? h("div.chain__ar", { "aria-hidden": "true" }, arrow("down"), chain[i - 1].edge ? h("span.chain__edge", fx(chain[i - 1].edge)) : null) : null,
      h(`div.cnode.k-${n.kind}`, { "data-node": n.id, tabindex: "0" },
        h("div.cnode__head", h("span.cnode__role", n.role), n.name ? h("code.cnode__name", n.name) : null),
        h("div.cnode__f", n.formula.map((f) => h("span", fx(f)))),
        n.extra ? h("div.cnode__x", h("code", n.extra.kw), " ", fx(n.extra.formula)) : null),
    ])));
}

// ---------------------------------------------------------------- 3: the answer

function answer(a) {
  return h("div.ex-answer",
    h("span.ex-answer__bind", fx(a.binding)),
    h("div.ex-answer__f", fx(a.formula)),
    h("p.ex-answer__ok", icon("shield-check"), h("strong", a.verified), h("span", a.count)),
    h("p.ex-answer__scope", withMath(a.scope)));
}

export default function render({ data }) {
  const { meaning, proof } = data.parts;
  const proofBox = h("div.ex-proof", codeView(data.code, proof.legend), chainView(data.chain, proof.chainHead));
  linkHover(proofBox, "node");
  const fig = flow(data);
  const el = h("div.wrap",
    h("header.page-head.ex-head",
      h("h1", data.title),
      h("p", data.lead)),
    part(1, "meaning", meaning.title, meaning.line, fig),
    part(2, "proof", proof.title, proof.line, proofBox),
    part(3, "answer", data.parts.answer.title, null, answer(data.answer)));
  // the data flow plays once, when the page opens with the figure on screen (the final state is the default)
  el.shown = () => {
    if (fig.getBoundingClientRect().top < innerHeight * 0.8 && !matchMedia("(prefers-reduced-motion: reduce)").matches) fig.classList.add("play");
  };
  return el;
}
