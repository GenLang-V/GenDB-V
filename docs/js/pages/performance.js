// Performance: two links to the two results, then engine synthesis (total time per version at 1 and 64 threads, ending
// with the latest engine and a note on it) and template synthesis (headline speedups; total
// time and the speedup per query, with a thread switch and a baseline switch). Text and numbers:
// data/performance.json (build/pages/performance.mjs). The charts are SVG drawn at the width of their box, and drawn
// again when that width changes. Address: #/performance/engine and #/performance/templates scroll to a section;
// ?threads=32&vs=umbra sets the switches.
import { h, s, icon } from "../lib.js";

const BASE_KEYS = { DuckDB: "duckdb", Umbra: "umbra" };
const threadLabel = (t) => `${t} thread${t === "1" ? "" : "s"}`;

/* ---------------------------------------------------------------- numbers */

/** A speedup: 3,334 · 23.4 · 0.19 */
const times = (x) => (x >= 100 ? Math.round(x).toLocaleString("en-US") : x >= 1 ? x.toFixed(1) : x.toFixed(2));
/** A per-query time: 20.9 s · 288 ms · 12.3 ms · 0.729 ms */
function ms(v) {
  if (v >= 1000) { const t = v / 1000; return `${t >= 100 ? t.toFixed(0) : t >= 10 ? t.toFixed(1) : t.toFixed(2)} s`; }
  return `${v >= 100 ? v.toFixed(0) : v >= 10 ? v.toFixed(1) : v >= 1 ? v.toFixed(2) : v.toFixed(3)} ms`;
}
/** y = scale(v) on a log axis from [lo, hi] to [a, b]. */
function logScale(lo, hi, a, b) {
  const l0 = Math.log10(lo), span = Math.log10(hi) - l0;
  return (v) => a + ((Math.log10(v) - l0) / span) * (b - a);
}

/** An SVG element with its classes in the tag: sv("circle.a.b", { r: 4 }, ...children). */
function sv(tag, attrs, ...children) {
  if (!attrs || typeof attrs !== "object" || attrs instanceof Node || Array.isArray(attrs)) { if (attrs !== undefined) children.unshift(attrs); attrs = {}; }
  const [name, ...cls] = tag.split(".");
  return s(name, cls.length ? { ...attrs, class: cls.join(" ") } : attrs, ...children);
}

/* ---------------------------------------------------------------- parts */

/** A row of buttons, one pressed. */
function switcher(label, options, onPick) {
  const buttons = options.map(([value, text]) => h("button.seg__b", { type: "button", "data-value": value, "aria-pressed": "false", onclick: () => onPick(value) }, text));
  const el = h("div.seg", { role: "group", "aria-label": label }, buttons);
  el.set = (value) => { for (const b of buttons) b.setAttribute("aria-pressed", String(b.dataset.value === value)); };
  return el;
}

/** Text with the names that hold a hyphen kept on one line. */
const keep = (text) => text.split(/(TPC-H|SEC-EDGAR|GenDB-V)/).map((part, i) => (i % 2 ? h("span.nw", part) : part));

/** The section heading: an icon, the title, one line. */
function head(id, iconName, title, line) {
  return h("header.sec__head",
    h("span.sec__icon", icon(iconName)),
    h("h2", { id: `perf-${id}` }, title),
    h("p.sec__line", keep(line)));
}

/** The tooltip of a chart box: rows of [key, label, value, extra]; placed inside the box at (x, y), kept inside it. */
function tooltip(box) {
  const el = h("div.tip", { hidden: true });
  el.show = (title, rows, at) => {
    el.replaceChildren(h("div.tip__t", title), h("div.tip__rows", rows.map(([key, label, value, extra, strong]) =>
      h(`div.tip__r${strong ? ".is-strong" : ""}`, h(`span.tip__k${key ? `.k-${key}` : ""}`), h("span.tip__l", label), h("span.tip__v", value), h("span.tip__x", extra || "")))));
    el.hidden = false;
    const W = box.clientWidth, w = el.offsetWidth, hh = el.offsetHeight;
    let x = at.side === "left" ? at.x - w - 14 : at.side === "right" ? at.x + 14 : at.x - w / 2;
    if (at.side === "right" && x + w > W) x = at.x - w - 14;
    if (at.side === "left" && x < 0) x = at.x + 14;
    x = Math.max(0, Math.min(W - w, x));
    const y = at.below === false ? at.y - hh - 10 : at.y;
    el.style.transform = `translate(${Math.round(x)}px, ${Math.round(Math.max(0, y))}px)`;
  };
  el.hide = () => { el.hidden = true; };
  return el;
}

/** Hide the chart's values on a tap or click outside it. */
function outside(box, hide) {
  document.addEventListener("pointerdown", (e) => { if (box.isConnected && !box.contains(e.target)) hide(); });
}

/** Call draw() now (the box is on screen) and again whenever the box's width changes. */
function onWidth(box, draw) {
  let last = box.clientWidth, frame = 0;
  if (last) draw();
  new ResizeObserver(() => {
    cancelAnimationFrame(frame);
    frame = requestAnimationFrame(() => { if (box.clientWidth && box.clientWidth !== last) { last = box.clientWidth; draw(); } });
  }).observe(box);
}

/* ---------------------------------------------------------------- template synthesis: headline */

function headline(tpl) {
  return h("figure.kpis",
    h("div.kpis__grid", tpl.workloads.map((w) => h("div.kpi",
      h("div.kpi__wl", h("span", w.name), h("span.kpi__scale", w.scale)),
      h("div.kpi__nums", w.headline.map((x) => h("div.kpi__n",
        h("span.kpi__num", x.text, h("span.kpi__x", "×")),
        h("span.kpi__vs", `vs ${x.baseline}`))))))),
    h("figcaption.kpis__cap", h("span.key.key--agent"), tpl.systems.agent, h("span.kpis__dot", " · "), tpl.caption));
}

/* ---------------------------------------------------------------- template synthesis: total time */

function totalsCard(tpl) {
  const order = [["duckdb", "DuckDB"], ["umbra", "Umbra"], ["plain", tpl.systems.plain, true], ["agent", tpl.systems.agent, true]];
  const groups = tpl.workloads.map((w) => {
    const rows = order.map(([key, label, ours]) => {
      const fill = h("span.tbar__fill"), value = h("span.tbar__val");
      const name = ours ? h("span.tbar__label", h("span.tbar__ours", "GenDB-V"), h("span", label)) : h("span.tbar__label", label);
      return { key, fill, value, el: h(`li.tbar.is-${key}`, name, h("span.tbar__track", fill, value)) };
    });
    return { w, rows, el: h("div.tot", h("h4.tot__wl", w.name, h("span.tot__scale", w.scale)), h("ul.tot__bars", rows.map((r) => r.el))) };
  });
  const el = h("section.card.totals", { "aria-labelledby": "perf-totals" },
    h("h3.card__t#perf-totals", tpl.totalsTitle),
    h("div.totals__grid", groups.map((g) => g.el)));
  el.update = ({ threads }) => {
    for (const g of groups) {
      const tot = g.w.totals[threads];
      const max = Math.max(...g.rows.map((r) => tot[r.key].s));
      for (const r of g.rows) {
        r.fill.style.setProperty("--f", (tot[r.key].s / max).toFixed(5));
        r.value.textContent = `${tot[r.key].text} s`;
      }
    }
  };
  return el;
}

/* ---------------------------------------------------------------- template synthesis: speedup per query */

const SPEEDUP_DOMAIN = [0.1, 10000];
const SPEEDUP_TICKS = [0.1, 1, 10, 100, 1000, 10000];
const speedupTick = (v, short) => (v < 1 ? "0.1×" : short && v >= 1000 ? `${v / 1000}k×` : `${v.toLocaleString("en-US")}×`);

/**
 * Per query: GenDB-V's speedup over the chosen baseline with plain arrays (ring) and agent-designed storage (dot),
 * joined by a line. Wide: one column per query, the two workloads side by side. Narrow: one row per query.
 */
function queryChart(tpl, state) {
  const box = h("div.qc");
  const tip = tooltip(box);
  const items = tpl.workloads.flatMap((w) => w.queries.map((q) => ({ w, q })));
  let geo = null, active = -1, svg = null, band = null;
  const marks = [];

  function draw() {
    const W = box.clientWidth;
    const narrow = W < 640;
    const panels = [];
    if (!narrow) {
      const m = { l: 56, r: 6, t: 34, b: 30 }, gap = 36, H = 380;
      const col = (W - m.l - m.r - gap * (tpl.workloads.length - 1)) / items.length;
      let x0 = m.l;
      for (const w of tpl.workloads) {
        panels.push({ w, x0, x1: x0 + col * w.queries.length });
        x0 += col * w.queries.length + gap;
      }
      const at = logScale(...SPEEDUP_DOMAIN, H - m.b, m.t);
      const pos = panels.flatMap((p) => p.w.queries.map((_, i) => p.x0 + (i + 0.5) * col));
      geo = { narrow, W, H, m, col, at, panels, pos };
    } else {
      const m = { l: 40, r: 16, t: 30, b: 30 }, row = 24, headH = 34, gap = 14;
      let y0 = m.t;
      for (const w of tpl.workloads) {
        panels.push({ w, y0: y0 + headH, y1: y0 + headH + row * w.queries.length, head: y0 + 22 });
        y0 += headH + row * w.queries.length + gap;
      }
      const H = y0 - gap + m.b;
      const at = logScale(...SPEEDUP_DOMAIN, m.l, W - m.r);
      const pos = panels.flatMap((p) => p.w.queries.map((_, i) => p.y0 + (i + 0.5) * row));
      geo = { narrow, W, H, m, row, at, panels, pos };
    }
    const { H, m, at } = geo;
    svg = sv("svg.qc__svg", { viewBox: `0 0 ${W} ${H}`, width: W, height: H, role: "img", tabindex: "0", "aria-label": `${tpl.queriesTitle}: ${tpl.workloads.map((w) => w.name).join(", ")}` });
    band = sv("rect.qc__band", { visibility: "hidden" });
    const grid = sv("g.qc__grid"), labels = sv("g.qc__labels"), data = sv("g.qc__data");
    for (const v of SPEEDUP_TICKS) {
      const one = v === 1 ? ".is-one" : "";
      if (!narrow) {
        const y = at(v);
        for (const p of geo.panels) grid.append(sv(`line${one}`, { x1: p.x0, x2: p.x1, y1: y, y2: y }));
        labels.append(sv(`text.qc__tick${one}`, { x: m.l - 10, y, "text-anchor": "end", "dominant-baseline": "central" }, speedupTick(v)));
      } else {
        const x = at(v);
        for (const p of geo.panels) grid.append(sv(`line${one}`, { x1: x, x2: x, y1: p.y0, y2: p.y1 }));
        for (const y of [m.t - 12, H - m.b + 18]) labels.append(sv(`text.qc__tick${one}`, { x, y, "text-anchor": v === 0.1 ? "start" : v === 10000 ? "end" : "middle" }, speedupTick(v, true)));
      }
    }
    for (const p of geo.panels) {
      if (!narrow) {
        labels.append(sv("text.qc__panel", { x: p.x0, y: m.t - 16 }, p.w.name, sv("tspan.qc__scale", { dx: 6 }, p.w.scale)));
        p.w.queries.forEach((q, i) => labels.append(sv("text.qc__q", { x: p.x0 + (i + 0.5) * geo.col, y: H - m.b + 18, "text-anchor": "middle" }, q.id.slice(1))));
      } else {
        labels.append(sv("text.qc__panel", { x: 0, y: p.head }, p.w.name, sv("tspan.qc__scale", { dx: 6 }, p.w.scale)));
        p.w.queries.forEach((q, i) => labels.append(sv("text.qc__q", { x: 0, y: p.y0 + (i + 0.5) * geo.row, "dominant-baseline": "central" }, q.id)));
      }
    }
    marks.length = 0;
    items.forEach(() => {
      const stem = sv("rect.qc__stem", narrow ? { x: 0, y: -1, width: 1, height: 2 } : { x: -1, y: 0, width: 2, height: 1 });
      const plain = sv("g.qc__m", sv("circle.qc__plain", { r: 4.5 }));
      const agent = sv("g.qc__m", sv("circle.qc__agent", { r: 5.5 }));
      data.append(stem, plain, agent);
      marks.push({ stem, plain, agent });
    });
    svg.append(band, grid, data, labels);
    svg.addEventListener("pointermove", (e) => pick(indexAt(e)));
    svg.addEventListener("pointerdown", (e) => pick(indexAt(e)));
    svg.addEventListener("pointerleave", (e) => { if (e.pointerType === "mouse") pick(-1); });
    svg.addEventListener("focus", () => pick(Math.max(0, active)));
    svg.addEventListener("blur", () => pick(-1));
    svg.addEventListener("keydown", (e) => {
      const step = { ArrowRight: 1, ArrowDown: 1, ArrowLeft: -1, ArrowUp: -1 }[e.key];
      if (step) { e.preventDefault(); pick((Math.max(0, active) + step + items.length) % items.length); }
      if (e.key === "Escape") pick(-1);
    });
    box.replaceChildren(svg, tip);
    place();
    if (active >= 0) pick(active);
  }

  /** The item under the pointer, or -1. */
  function indexAt(e) {
    const r = svg.getBoundingClientRect(), x = e.clientX - r.left, y = e.clientY - r.top;
    const along = geo.narrow ? y : x, half = (geo.narrow ? geo.row : geo.col) / 2 + (geo.narrow ? 0 : 6);
    let best = -1, dist = Infinity;
    geo.pos.forEach((p, i) => { const d = Math.abs(p - along); if (d < dist) { dist = d; best = i; } });
    return dist <= half ? best : -1;
  }

  /** Every mark at the speedups of the current threads and baseline. */
  function place() {
    const { threads, vs } = state;
    items.forEach(({ q }, i) => {
      const c = q.ms[threads], a = geo.at(c[vs] / c.agent), p = geo.at(c[vs] / c.plain), at = geo.pos[i];
      const { stem, plain, agent } = marks[i];
      const lo = Math.min(a, p), len = Math.max(Math.abs(a - p), 0.001);
      if (geo.narrow) {
        stem.style.transform = `translate(${lo}px, ${at}px) scale(${len}, 1)`;
        plain.style.transform = `translate(${p}px, ${at}px)`;
        agent.style.transform = `translate(${a}px, ${at}px)`;
      } else {
        stem.style.transform = `translate(${at}px, ${lo}px) scale(1, ${len})`;
        plain.style.transform = `translate(${at}px, ${p}px)`;
        agent.style.transform = `translate(${at}px, ${a}px)`;
      }
    });
  }

  /** Show item i's values (-1: none). */
  function pick(i) {
    active = i;
    if (i < 0) { tip.hide(); band.setAttribute("visibility", "hidden"); return; }
    const { w, q } = items[i], c = q.ms[state.threads], at = geo.pos[i];
    if (geo.narrow) {
      Object.entries({ x: 0, y: at - geo.row / 2, width: geo.W, height: geo.row }).forEach(([k, v]) => band.setAttribute(k, v));
    } else {
      Object.entries({ x: at - geo.col / 2, y: geo.m.t - 6, width: geo.col, height: geo.H - geo.m.t - geo.m.b + 12 }).forEach(([k, v]) => band.setAttribute(k, v));
    }
    band.setAttribute("visibility", "visible");
    const base = state.vs;
    tip.show(`${q.id} · ${w.name} · ${threadLabel(state.threads)}`, [
      ["agent", tpl.systems.agent, ms(c.agent), `${times(c[base] / c.agent)}×`],
      ["plain", tpl.systems.plain, ms(c.plain), `${times(c[base] / c.plain)}×`],
      ...tpl.baselines.map((b) => [null, b, ms(c[BASE_KEYS[b]]), "", BASE_KEYS[b] === base]),
    ], !geo.narrow ? { x: at, y: geo.m.t, side: at > geo.W / 2 ? "left" : "right" }
      : at < geo.H * 0.6 ? { x: geo.W / 2, y: at + geo.row / 2 + 6 } : { x: geo.W / 2, y: at - geo.row / 2, below: false });
  }

  return {
    el: box,
    start: () => { onWidth(box, draw); outside(box, () => { if (svg) pick(-1); }); },
    update: () => { if (svg) { place(); if (active >= 0) pick(active); } },
  };
}

function queriesCard(tpl, state, onVs) {
  const chart = queryChart(tpl, state);
  const vs = switcher("Baseline", tpl.baselines.map((b) => [BASE_KEYS[b], `vs ${b}`]), onVs);
  const el = h("section.card.queries", { "aria-labelledby": "perf-queries" },
    h("div.card__head",
      h("h3.card__t#perf-queries", tpl.queriesTitle),
      vs),
    h("div.legend",
      h("span.legend__k", h("span.key.key--agent"), tpl.systems.agent),
      h("span.legend__k", h("span.key.key--plain"), tpl.systems.plain)),
    chart.el);
  el.update = (st) => { vs.set(st.vs); chart.update(); };
  el.start = chart.start;
  return el;
}

/* ---------------------------------------------------------------- engine synthesis */

/** Log ticks 1, 2, 3, 5 × 10^k inside [lo, hi]. */
function ticks1235(lo, hi) {
  const out = [];
  for (let k = Math.floor(Math.log10(lo)); k <= Math.ceil(Math.log10(hi)); k++) {
    for (const d of [1, 2, 3, 5]) { const v = d * 10 ** k; if (v >= lo && v <= hi) out.push(v); }
  }
  return out;
}

/**
 * One worker count: GenDB-V's total time per version against DuckDB's and Umbra's (log axis), then, one slot apart,
 * the latest engine.
 */
function engineChart(eng, panel) {
  const t = panel.threads;
  const box = h("div.ec");
  const tip = tooltip(box);
  const versions = eng.versions, done = versions.filter((v) => v.s);
  // the points a pointer or the keyboard can pick: every version, then the latest engine
  const points = [...versions.map((v) => ({ slot: v.v, label: `v${v.v}`, s: v.s && v.s[t], text: v.text && v.text[t] })),
    { slot: versions.length + 1, label: eng.latest.label, s: eng.latest.s[t], text: eng.latest.text[t] }];
  let geo = null, svg = null, cross = null, dot = null, active = -1;

  function draw() {
    const W = box.clientWidth, narrow = W < 460;
    const m = { l: 50, r: narrow ? 56 : 64, t: 34, b: 30 }, H = narrow ? 250 : 290;
    const values = [...points.filter((p) => p.s).map((p) => p.s), ...eng.baselines.map((b) => b.s[t])];
    const lo = Math.min(...values) / 1.3, hi = Math.max(...values) * 1.25;
    const y = logScale(lo, hi, H - m.b, m.t);
    const step = (W - m.l - m.r) / (versions.length + 2);
    const x = (slot) => m.l + (slot + 0.5) * step;
    geo = { W, H, m, x, y, step };
    const id = `ec-wash-${t}`;
    svg = sv("svg.ec__svg", { viewBox: `0 0 ${W} ${H}`, width: W, height: H, role: "img", tabindex: "0", "aria-label": `${eng.title}, ${threadLabel(t)}` });
    const defs = sv("defs", sv("linearGradient", { id, x1: 0, x2: 0, y1: 0, y2: 1 },
      sv("stop.ec__stop", { offset: "0" }), sv("stop.ec__stop.is-end", { offset: "1" })));
    const grid = sv("g.ec__grid"), labels = sv("g.ec__labels");
    for (const v of ticks1235(lo, hi)) {
      grid.append(sv("line", { x1: m.l, x2: W - m.r, y1: y(v), y2: y(v) }));
      labels.append(sv("text.ec__tick", { x: m.l - 10, y: y(v), "text-anchor": "end", "dominant-baseline": "central" }, `${v} s`));
    }
    const every = [1, 2, 4].find((k) => k * step >= 28) || 4;
    const latest = points[points.length - 1], lx = x(latest.slot);
    for (const v of versions) {
      if (v.v % every === 0 && lx - x(v.v) >= 36) labels.append(sv("text.ec__x", { x: x(v.v), y: H - m.b + 18, "text-anchor": "middle" }, `v${v.v}`));
    }
    labels.append(sv("text.ec__x.is-latest", { x: lx, y: H - m.b + 18, "text-anchor": "middle" }, latest.label));
    // the baselines, named at their right end
    const bases = sv("g.ec__bases");
    eng.baselines.forEach((b) => {
      bases.append(sv(`line.ec__base.is-${BASE_KEYS[b.name]}`, { x1: m.l, x2: W - m.r + 4, y1: y(b.s[t]), y2: y(b.s[t]) }));
      labels.append(sv("text.ec__bname", { x: W - m.r + 8, y: y(b.s[t]), "dominant-baseline": "central" }, b.name));
    });
    // GenDB-V: the versions that finish every query, a wash under them; the first ones did not finish
    const pts = done.map((v) => [x(v.v), y(v.s[t])]);
    const line = pts.map(([px, py], i) => `${i ? "L" : "M"}${px.toFixed(1)} ${py.toFixed(1)}`).join("");
    const wash = sv("path.ec__wash", { d: `${line}L${pts[pts.length - 1][0].toFixed(1)} ${H - m.b}L${pts[0][0].toFixed(1)} ${H - m.b}Z`, fill: `url(#${id})` });
    const path = sv("path.ec__line", { d: line });
    const dots = sv("g.ec__dots", pts.map(([px, py]) => sv("circle", { cx: px, cy: py, r: 3 })));
    const last = pts[pts.length - 1], ly = y(latest.s);
    const end = sv("g.ec__latest",
      sv("path.ec__bridge", { d: `M${last[0].toFixed(1)} ${last[1].toFixed(1)}L${lx.toFixed(1)} ${ly.toFixed(1)}` }),
      sv("circle.ec__halo", { cx: lx, cy: ly, r: 11 }),
      sv("circle.ec__end", { cx: lx, cy: ly, r: 6 }));
    const miss = sv("g.ec__miss");
    versions.filter((v) => !v.s).forEach((v) => {
      const cx = x(v.v), cy = m.t - 16, r = 4.5;
      miss.append(sv("path", { d: `M${cx - r} ${cy - r}L${cx + r} ${cy + r}M${cx + r} ${cy - r}L${cx - r} ${cy + r}` }));
    });
    const lastMiss = versions.filter((v) => !v.s).pop();
    if (lastMiss) labels.append(sv("text.ec__misslabel", { x: x(lastMiss.v) + 12, y: m.t - 16, "dominant-baseline": "central" }, eng.incomplete));
    cross = sv("line.ec__cross", { y1: m.t - 24, y2: H - m.b, visibility: "hidden" });
    dot = sv("circle.ec__hot", { r: 5, visibility: "hidden" });
    svg.append(defs, grid, bases, wash, path, dots, end, miss, cross, dot, labels);
    const at = (e) => {
      const r = svg.getBoundingClientRect(), slot = Math.round((e.clientX - r.left - m.l) / step - 0.5);
      return points.findIndex((p) => p.slot === slot);
    };
    svg.addEventListener("pointermove", (e) => pick(at(e)));
    svg.addEventListener("pointerdown", (e) => pick(at(e)));
    svg.addEventListener("pointerleave", (e) => { if (e.pointerType === "mouse") pick(-1); });
    svg.addEventListener("focus", () => pick(points.length - 1));
    svg.addEventListener("blur", () => pick(-1));
    svg.addEventListener("keydown", (e) => {
      const d = { ArrowRight: 1, ArrowLeft: -1 }[e.key];
      if (d) { e.preventDefault(); pick(Math.min(points.length - 1, Math.max(0, (active < 0 ? points.length - 1 : active) + d))); }
      if (e.key === "Escape") pick(-1);
    });
    box.replaceChildren(svg, tip);
    if (active >= 0) pick(active);
  }

  /** Show point i's time (-1: none). */
  function pick(i) {
    active = i;
    if (i < 0) { tip.hide(); cross.setAttribute("visibility", "hidden"); dot.setAttribute("visibility", "hidden"); return; }
    const p = points[i], cx = geo.x(p.slot);
    cross.setAttribute("x1", cx); cross.setAttribute("x2", cx); cross.setAttribute("visibility", "visible");
    if (p.s) { dot.setAttribute("cx", cx); dot.setAttribute("cy", geo.y(p.s)); dot.setAttribute("visibility", "visible"); }
    else dot.setAttribute("visibility", "hidden");
    tip.show(p.label, p.s ? [["agent", "GenDB-V", `${p.text} s`]] : [[null, eng.incomplete, ""]],
      { x: cx, y: geo.m.t, side: cx > geo.W * 0.55 ? "left" : "right" });
  }

  return { el: box, start: () => { onWidth(box, draw); outside(box, () => { if (svg) pick(-1); }); } };
}

function engineCard(eng) {
  const charts = [];
  const panels = eng.panels.map((p) => {
    const chart = engineChart(eng, p);
    charts.push(chart);
    return h("div.ep",
      h("div.ep__head",
        h("div.ep__time",
          h("span.ep__threads", threadLabel(p.threads), h("span.ep__v", p.label)),
          h("span.ep__num", p.time, h("span.ep__unit", " s"))),
        h("div.ep__stats", p.speedups.map((x) => h("div.ep__stat",
          h("span.ep__x", x.text, h("span.kpi__x", "×")),
          h("span.ep__vs", `vs ${x.baseline}`))))),
      chart.el);
  });
  const el = h("section.card.engine",
    h("div.card__head",
      h("h3.card__t", eng.workload),
      h("div.legend",
        h("span.legend__k", h("span.key.key--line"), "GenDB-V"),
        eng.baselines.map((b) => h("span.legend__k", h(`span.key.key--${BASE_KEYS[b.name]}`), b.name)))),
    h("div.engine__grid", panels),
    h("p.ec-note", h("span.ec-note__key"), h("strong", eng.latest.label), h("span", eng.latest.note)));
  el.start = () => charts.forEach((c) => c.start());
  return el;
}

/* ---------------------------------------------------------------- the page */

export default function render({ data, path, params }) {
  const tpl = data.templates, eng = data.engine;
  const state = { threads: tpl.threads[0], vs: BASE_KEYS[tpl.baselines[0]] };
  const read = (p) => {
    if (tpl.threads.includes(p.get("threads"))) state.threads = p.get("threads");
    if (Object.values(BASE_KEYS).includes(p.get("vs"))) state.vs = p.get("vs");
  };
  read(params);

  const threads = switcher("Threads", tpl.threads.map((t) => [t, threadLabel(t)]), (t) => pick({ threads: t }));
  const totals = totalsCard(tpl);
  const queries = queriesCard(tpl, state, (vs) => pick({ vs }));
  const engine = engineCard(eng);

  function apply() {
    threads.set(state.threads);
    totals.update(state);
    queries.update(state);
  }
  /** A switch was pressed: update the page and its address (without a new history entry). */
  function pick(change) {
    Object.assign(state, change);
    apply();
    history.replaceState(null, "", `#/performance/templates?threads=${state.threads}&vs=${state.vs}`);
  }

  const ICONS = { engine: "cpu", templates: "file-code" };
  const sections = {
    engine: h("section.sec.sec--engine#engine", { "aria-labelledby": "perf-engine" },
      head("engine", ICONS.engine, eng.title, eng.line),
      engine),
    templates: h("section.sec.sec--templates#templates", { "aria-labelledby": "perf-templates" },
      head("templates", ICONS.templates, tpl.title, tpl.line),
      headline(tpl),
      h("div.controls", threads),
      totals,
      queries),
  };
  /** Scroll to the section an address names (#/performance/engine, #/performance/templates). */
  const scroll = (p, smooth) => { if (sections[p[0]]) sections[p[0]].scrollIntoView({ behavior: smooth ? "smooth" : "auto" }); };
  const jump = h("nav.jump", { "aria-label": "Results" }, data.jump.map((j) => h("a.jump__card", {
    href: `#/performance/${j.id}`,
    onclick: (e) => { e.preventDefault(); scroll([j.id], true); history.replaceState(null, "", `#/performance/${j.id}`); },
  }, h("span.jump__icon", icon(ICONS[j.id])), h("span.jump__text", h("strong", j.title), h("span", j.line)), icon("arrow-down", { cls: "jump__go" }))));

  const el = h("div.wrap",
    h("header.page-head", h("h1", data.title), h("p", keep(data.lead))),
    jump,
    data.jump.map((j) => sections[j.id]));
  apply();

  el.shown = () => { queries.start(); engine.start(); scroll(path); };
  el.reroute = (p, q) => { read(q); apply(); scroll(p); return true; };
  return el;
}
