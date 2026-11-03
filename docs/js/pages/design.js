// Design: three highlights (correct, fast, coverage), the overview diagram (after the paper's overview figure), and the three parts: SQLSpec,
// agentic code and proof synthesis, independent verification. Text and formulas: data/design.json
// (build/pages/design.mjs). The diagram has two hand-set layouts, wide and narrow; CSS shows one.
import { h, s, icon, math } from "../lib.js";

/** The diagram's boxes: kind (input, trusted, agent, verified), label lines, the part number it belongs to. */
const NODES = {
  input: { kind: "input", label: ["SQL · schema · workload · data · hardware"] },
  spec: { kind: "trusted", label: ["SQLSpec"], part: 1 },
  target: { kind: "trusted", label: ["Fixed target"], term: true },
  agent: { kind: "agent", label: ["AI agent"], part: 2 },
  trials: { kind: "agent", label: ["Performance trials"] },
  verus: { kind: "trusted", label: ["Verus"], part: 3 },
  engine: { kind: "verified", label: ["Verified engine"] },
};
/** Per layout: box [x, y, w, h]; text sizes (fs: boxes, efs: edge labels); the part number's circle (radius r, its
 *  centre pad + r from the box's left; the label is centred in the rest of the box); edges as point lists (target:
 *  from the fixed target; back: feedback, dashed), with an optional label [text, x, y, anchor]. */
const LAYOUTS = {
  wide: {
    w: 1112, h: 302, fs: 19, efs: 15, num: { r: 13, pad: 14 },
    box: { input: [0, 0, 470, 56], spec: [0, 100, 148, 68], target: [188, 100, 192, 68], agent: [428, 100, 192, 68], trials: [414, 222, 220, 56], verus: [744, 100, 144, 68], engine: [928, 100, 184, 68] },
    edges: [
      { pts: [[284, 56], [284, 100]] },
      { pts: [[449, 56], [449, 100]] },
      { pts: [[148, 134], [188, 134]] },
      { pts: [[380, 134], [428, 134]], target: true },
      { pts: [[490, 168], [490, 222]] },
      { pts: [[558, 222], [558, 168]] },
      { pts: [[620, 134], [744, 134]], label: ["code + proofs", 682, 119, "middle"] },
      { pts: [[284, 168], [284, 298], [816, 298], [816, 168]], target: true },
      { pts: [[816, 100], [816, 78], [580, 78], [580, 100]], back: true, label: ["errors", 698, 64, "middle"] },
      { pts: [[888, 134], [928, 134]] },
    ],
  },
  narrow: {
    w: 360, h: 478, fs: 16, efs: 14, num: { r: 11, pad: 10 },
    box: { input: [0, 0, 218, 60], spec: [238, 0, 122, 60], target: [34, 104, 300, 56], agent: [34, 204, 160, 60], trials: [222, 204, 122, 60], verus: [34, 314, 160, 60], engine: [34, 418, 160, 60] },
    label: { input: ["SQL · schema · workload", "data · hardware"], trials: ["Performance", "trials"] },
    edges: [
      { pts: [[124, 60], [124, 104]] },
      { pts: [[299, 60], [299, 104]] },
      { pts: [[119, 160], [119, 204]], target: true },
      { pts: [[12, 60], [12, 234], [34, 234]] },
      { pts: [[194, 222], [222, 222]] },
      { pts: [[222, 246], [194, 246]] },
      { pts: [[150, 264], [150, 314]], label: ["code + proofs", 142, 289, "end"] },
      { pts: [[334, 132], [356, 132], [356, 344], [194, 344]], target: true },
      { pts: [[176, 314], [176, 264]], back: true, label: ["errors", 186, 289, "start"] },
      { pts: [[114, 374], [114, 418]] },
    ],
  },
};

/** A polyline with rounded corners, ending short of its last point, and its arrow head (a filled triangle). */
function arrow(pts, r = 8) {
  const [px, py] = pts[pts.length - 1], [qx, qy] = pts[pts.length - 2];
  const len = Math.hypot(px - qx, py - qy), dx = (px - qx) / len, dy = (py - qy) / len;
  const tip = [px - dx * 2, py - dy * 2], base = [tip[0] - dx * 10, tip[1] - dy * 10];
  const line = [...pts.slice(0, -1), [base[0] + dx, base[1] + dy]];
  let d = `M${line[0][0]} ${line[0][1]}`;
  for (let i = 1; i < line.length - 1; i++) {
    const [ax, ay] = line[i - 1], [bx, by] = line[i], [cx, cy] = line[i + 1];
    const k1 = Math.min(r, Math.hypot(bx - ax, by - ay) / 2) / Math.hypot(bx - ax, by - ay);
    const k2 = Math.min(r, Math.hypot(cx - bx, cy - by) / 2) / Math.hypot(cx - bx, cy - by);
    d += `L${bx - (bx - ax) * k1} ${by - (by - ay) * k1}Q${bx} ${by} ${bx + (cx - bx) * k2} ${by + (cy - by) * k2}`;
  }
  d += `L${line[line.length - 1][0]} ${line[line.length - 1][1]}`;
  const head = `M${tip[0]} ${tip[1]}L${base[0] - dy * 5} ${base[1] + dx * 5}L${base[0] + dy * 5} ${base[1] - dx * 5}Z`;
  return [d, head];
}

function diagram(name) {
  const L = LAYOUTS[name];
  const svg = s("svg", { class: `dg dg--${name}`, viewBox: `-1 -1 ${L.w + 2} ${L.h + 2}`, role: "img", "aria-label": "SQLSpec and the SQL make a fixed target. An AI agent, using the workload, data and hardware and performance trials, writes code and proofs. Verus checks them against the target and returns errors to the agent; what it accepts is the verified engine." });
  for (const e of L.edges) {
    const [d, head] = arrow(e.pts);
    svg.append(s("g", { class: `dg-edge${e.target ? " is-target" : ""}${e.back ? " is-back" : ""}` }, s("path", { class: "dg-line", d }), s("path", { class: "dg-head", d: head })));
    if (e.label) svg.append(s("text", { class: "dg-elabel", x: e.label[1], y: e.label[2], "text-anchor": e.label[3], "font-size": L.efs }, e.label[0]));
  }
  for (const [id, n] of Object.entries(NODES)) {
    const [x, y, w, hh] = L.box[id];
    const lines = (L.label && L.label[id]) || n.label;
    const g = s("g", { class: `dg-node is-${n.kind}` }, s("rect", { x, y, width: w, height: hh, rx: 12 }));
    const { r, pad } = L.num;
    const cx = n.part ? (x + pad + 2 * r + x + w) / 2 : x + w / 2, cy = y + hh / 2;
    if (n.part) g.append(s("circle", { class: "dg-num", cx: x + pad + r, cy, r }), s("text", { class: "dg-numt", x: x + pad + r, y: cy, "font-size": Math.round(r * 1.05) }, String(n.part)));
    lines.forEach((t, i) => {
      const text = s("text", { class: "dg-label", x: cx, y: cy + (i - (lines.length - 1) / 2) * (L.fs + 4), "font-size": L.fs }, t);
      if (n.term) text.append(" ", s("tspan", { class: "dg-m" }, "⟦"), s("tspan", { class: "dg-mi" }, "Q"), s("tspan", { class: "dg-m" }, "⟧"));
      g.append(text);
    });
    svg.append(g);
  }
  return svg;
}

/** Text with {x} parts set as math. */
const withMath = (t) => t.split(/\{([^}]+)\}/).map((p, i) => (i % 2 ? math(p) : p));

function part(n, block, visual) {
  return h(`section.part.part--${block.id}`, { "aria-labelledby": `part-${block.id}` },
    h("div.part__text",
      h("span.part__n", String(n)),
      h("h2", { id: `part-${block.id}` }, block.title),
      h("p.part__line", block.line)),
    h("div.part__visual", visual));
}

export default function render({ data }) {
  const [spec, synth, verify] = data.blocks;
  return h("div.wrap",
    h("header.page-head.design-head",
      h("h1", data.title),
      h("ul.highlights", data.highlights.map((x) => h(`li.hl.hl--${x.id}`,
        h("span.hl__icon", icon(x.icon)),
        h("h2.hl__title", x.title),
        x.lines.map((t) => h("p.hl__text", t)),
        x.link ? h("a.go.hl__go", { href: `#/${x.link}` }, "Performance", icon("arrow-right")) : null)))),
    h("figure.card.overview",
      diagram("wide"), diagram("narrow"),
      h("figcaption.legend", h("span.legend__k.is-trusted", "Trusted"), h("span.legend__k.is-verified", "Verified"))),
    h("div.parts",
      part(1, spec, h("div.def",
        h("div.def__f", math(spec.formula)),
        h("p.def__t", withMath(spec.formulaText)),
        h("ul.def__covers", spec.covers.map((c) => h("li.chip", c))))),
      part(2, synth, h("div.synth",
        h("div.synth__parts", synth.parts.map((p) => h("div.synth__part", h("span.synth__icon", icon(p.icon)), h("strong", p.title), h("span", p.text)))),
        h("ol.synth__order", synth.order.map((o, i) => h("li", i ? icon("arrow-right", { cls: "synth__then" }) : null, h("span.chip", icon(o.icon), o.text)))))),
      part(3, verify, h("div.targets",
        verify.targets.map((t) => h("div.target",
          h("span.target__mode", t.mode),
          h("div.target__f", math(t.formula)),
          h("span.target__scope", withMath(t.scope)))),
        h("p.targets__fixed", icon("check"), verify.fixed)))));
}
