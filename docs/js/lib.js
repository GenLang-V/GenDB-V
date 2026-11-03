// Small helpers every page may use: h() and s() build HTML and SVG elements, icon() a sprite icon, math() a formula.

export const svgNS = "http://www.w3.org/2000/svg";

function build(el, attrs, children) {
  for (const [k, v] of Object.entries(attrs)) {
    if (v == null || v === false) continue;
    if (k === "html") el.innerHTML = v;
    else if (k === "text") el.textContent = v;
    else if (k.startsWith("on") && typeof v === "function") el.addEventListener(k.slice(2), v);
    else el.setAttribute(k, v === true ? "" : v);
  }
  for (const c of children.flat(Infinity)) if (c != null && c !== false) el.append(c instanceof Node ? c : String(c));
  return el;
}
const isAttrs = (a) => a && typeof a === "object" && !(a instanceof Node) && !Array.isArray(a);

/** h("a.go#id", {href}, ...children): an HTML element; classes and id from the tag string; attrs optional. */
export function h(tag, attrs, ...children) {
  if (!isAttrs(attrs)) { if (attrs !== undefined) children.unshift(attrs); attrs = {}; }
  const [name, ...rest] = tag.split(/(?=[.#])/);
  const el = document.createElement(name || "div");
  for (const p of rest) if (p[0] === ".") el.classList.add(p.slice(1)); else el.id = p.slice(1);
  return build(el, attrs, children);
}

/** s("path", {d}): an SVG element. */
export function s(tag, attrs, ...children) {
  if (!isAttrs(attrs)) { if (attrs !== undefined) children.unshift(attrs); attrs = {}; }
  return build(document.createElementNS(svgNS, tag), attrs, children);
}

/** icon("arrow-right"): an icon of assets/icons.svg; decorative unless it has a label. */
export function icon(name, { label, cls } = {}) {
  return s("svg", { class: `ic${cls ? ` ${cls}` : ""}`, role: label ? "img" : null, "aria-label": label || null, "aria-hidden": label ? null : "true" },
    s("use", { href: `assets/icons.svg#${name}` }));
}

/** fetch a JSON file of the site; null when it is not there. */
export async function json(path) {
  const r = await fetch(path, { cache: "no-cache" });
  if (r.status === 404) return null;
  if (!r.ok) throw new Error(`${path}: HTTP ${r.status}`);
  return r.json();
}

const REL = new Set(["∈", "∉", "=", "≠", "≤", "≥", "<", ">", "⟹", "⇒", "→", "↦", "∧", "∨", "⊆", "⊂", "≡", ":"]);
const SYM = new Set(["⟦", "⟧", "(", ")", "[", "]", "{", "}", "|", "∀", "∃", "¬", "×", "·", "∅", "′"]);
/**
 * math("engine(build(db), Q) ∈ ⟦Q⟧(db)"): a formula set in STIX Two. Words of two or more letters are upright names,
 * except `db`; single letters and `db` are italic variables; `x_1` puts 1 below x; relations get space around them.
 * The plain text is the element's accessible name.
 */
export function math(src, { label } = {}) {
  const out = h("span.math", { role: "math", "aria-label": label || src });
  const re = /([A-Za-z][A-Za-z0-9]*)(?:_([A-Za-z0-9]+))?|(\d+)|(\s+)|(,)|(.)/gu;
  for (const m of src.matchAll(re)) {
    const [, word, sub, num, space, comma, other] = m;
    if (word) {
      const variable = word.length === 1 || word === "db";
      out.append(h(`span.${variable ? "v" : "f"}`, word, sub ? h("sub", sub) : null));
    } else if (num) out.append(h("span.f", num));
    else if (space) continue;
    else if (comma) out.append(h("span.s.sep", ","));
    else if (REL.has(other)) out.append(h("span.rel", other));
    else out.append(h(`span.s${SYM.has(other) ? "" : ".x"}`, other));
  }
  return out;
}
