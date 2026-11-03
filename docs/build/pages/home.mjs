// Home page data: the title, and the two story rows (speed, correctness), each a problem and GenDB-V's answer.
// The speedups are recomputed from this repository's results with the paper's method: per template and worker count,
// the mean time over the template's bindings; per baseline, the speedup baseline/GenDB-V of every template and
// worker count; their geometric mean. They must round to the values the paper states. With --paper, the per-template
// means must also equal the paper's figure data, and the paper's text must state the same rounded values. The
// repository README states the same speedups and story sentences; GUIDE.md states the claim.
import { csv, geomean } from "../lib.mjs";

const THREADS = ["1", "32", "64"];
const BASELINES = [{ key: "duckdb_ms", name: "DuckDB", csv: "DuckDB_ms" }, { key: "umbra_ms", name: "Umbra", csv: "Umbra_ms" }];
const WORKLOADS = [
  { name: "TPC-H", dir: "results/tpch-sf100", paperName: "TPC-H SF100", stated: ["51.6", "22.0"] },
  { name: "SEC-EDGAR", dir: "results/sec-edgar-sf3", paperName: "SEC-EDGAR SF3", stated: ["61.3", "28.3"] },
];
const ABSTRACT = "sections/00-abstract.tex", INTRO = "sections/01-introduction.tex", EVAL = "sections/06-evaluation.tex";
const README = "README.md", GUIDE = "GUIDE.md";

/** Per template and worker count: the mean over bindings of GenDB-V (agent-designed storage) and each baseline. */
function means(ctx, w) {
  const g = ctx.readJson(`${w.dir}/gendb-v-agent-designed-storage/times.json`);
  const b = ctx.readJson(`${w.dir}/duckdb-umbra-baselines/times.json`);
  const rows = [];
  ctx.check(Object.keys(g).sort().join() === Object.keys(b).sort().join(), `${w.name}: GenDB-V and baselines have the same templates`);
  for (const q of Object.keys(g).sort()) {
    const bindings = Object.keys(g[q]).sort();
    ctx.check(bindings.join() === Object.keys(b[q] || {}).sort().join(), `${w.name} ${q}: same bindings`);
    for (const t of THREADS) {
      const avg = (f) => bindings.reduce((s, v) => s + f(v), 0) / bindings.length;
      const gendb = avg((v) => g[q][v][t].gendb_ms);
      const base = BASELINES.map((x) => avg((v) => b[q][v][t][x.key]));
      ctx.check([gendb, ...base].every((x) => Number.isFinite(x) && x > 0), `${w.name} ${q} ${t}: positive times`);
      rows.push({ template: q, threads: t, bindings: bindings.length, gendb, base });
    }
  }
  return rows;
}

/** The paper's figure data (template-visible-mean.csv) must hold the same per-template means. */
function againstPaperData(ctx, w, rows) {
  const text = ctx.readPaper("figures/data/template-visible-mean.csv");
  if (!text) return;
  const paper = csv(text).filter((r) => r.workload === w.paperName);
  const same = (a, b) => Math.abs(a - b) <= 1e-6 * Math.max(1, Math.abs(b));
  ctx.quotePaper(w.paperName, "figures/data/template-visible-mean.csv");
  ctx.check(paper.length === rows.length, `${w.name}: the paper's data has ${paper.length} template-thread rows, the results ${rows.length}`);
  for (const r of rows) {
    const p = paper.find((x) => x.template === r.template && x.threads === r.threads);
    const ok = p && Number(p.bindings) === r.bindings && same(Number(p.GenDB_ms), r.gendb) && BASELINES.every((x, i) => same(Number(p[x.csv]), r.base[i]));
    ctx.check(ok, `${w.name} ${r.template} ${r.threads}: the per-template means equal the paper's figure data`);
  }
}

function speed(ctx) {
  const workloads = WORKLOADS.map((w) => {
    const rows = means(ctx, w);
    againstPaperData(ctx, w, rows);
    const speedups = BASELINES.map((x, i) => {
      const value = geomean(rows.map((r) => r.base[i] / r.gendb));
      const text = value.toFixed(1);
      ctx.check(text === w.stated[i], `${w.name} over ${x.name}: geometric-mean speedup ${text}, the paper states ${w.stated[i]}`);
      return { baseline: x.name, value: Number(value.toFixed(4)), text };
    });
    const templates = new Set(rows.map((r) => r.template)).size;
    // the README shows the same speedups
    ctx.quote(`| ${w.name}, ${templates} queries | ${speedups.map((s) => `**${s.text}×**`).join(" | ")} |`, README);
    return { name: w.name, templates, speedups };
  });
  // the paper's sentences, built from the computed values
  const [tpch, sec] = workloads.map((w) => w.speedups.map((s) => s.text));
  ctx.quotePaper(`geometric-mean speedups reach $${tpch[0]}\\times$ over DuckDB and $${tpch[1]}\\times$ over Umbra on TPC-H, and $${sec[0]}\\times$ and $${sec[1]}\\times$ on SEC-EDGAR`, EVAL);
  const all = workloads.flatMap((w) => w.speedups.map((s) => s.value));
  const lo = Math.min(...all).toFixed(1), hi = Math.max(...all).toFixed(1);
  ctx.quotePaper(`For verified template implementations, GenDB-V achieves geometric-mean speedups of ${lo}--${hi}$\\times$ over DuckDB and Umbra`, ABSTRACT);
  ctx.quotePaper("We measure query execution time at 1, 32, and 64 threads", EVAL);
  ctx.quotePaper("For each template, we average its execution time across its three parameter bindings", EVAL);
  return {
    problem: ctx.claim({ text: "Databases are rebuilt again and again for new workloads and new hardware.", paper: [ABSTRACT, "we repeatedly redesign and rebuild database systems"], repo: [README, "Databases are rebuilt again and again for new workloads and new hardware."] }),
    answer: ctx.claim({ text: "GenDB-V synthesizes a fast engine for your workload and hardware.", paper: [ABSTRACT, "enables AI agents to synthesize database engines specialized to hardware and workloads for performance"], repo: [README, "GenDB-V synthesizes a fast engine for your workload and hardware."] }),
    baselines: BASELINES.map((x) => x.name),
    workloads,
  };
}

function correctness(ctx) {
  const props = "proving SQL correctness, data preservation, memory and arithmetic safety, race-free parallel execution, and termination";
  return {
    problem: ctx.claim({ text: "Mature systems still return wrong answers, after years of engineering and testing.", paper: [ABSTRACT, "recent studies continue to uncover wrong-answer bugs even in mature database engines, despite years of development and testing"], repo: [README, "Mature systems still return wrong answers, after years of engineering and testing."] }),
    answer: ctx.claim({ text: "GenDB-V formally verifies your engine for correctness and program safety.", paper: [ABSTRACT, "proving SQL correctness and program safety"], repo: [README, "GenDB-V formally verifies your engine for correctness and program safety."] }),
    guarantees: [
      { id: "correctness", label: ctx.claim({ text: "Correctness", paper: [INTRO, props], repo: [GUIDE, "rows that are an allowed answer of the statement's SQLSpec meaning"] }) },
      { id: "memory", label: ctx.claim({ text: "Memory safety", paper: [INTRO, props] }) },
      { id: "arithmetic", label: ctx.claim({ text: "Arithmetic safety", paper: [INTRO, props] }) },
      { id: "races", label: ctx.claim({ text: "No data races", paper: [INTRO, props] }) },
      { id: "termination", label: ctx.claim({ text: "Termination", paper: [INTRO, props], repo: [GUIDE, "The termination checks of Verus prove that every loop and every recursion ends."] }) },
    ],
  };
}

export default function build(ctx) {
  return {
    title: "GenDB-V",
    tagline: ctx.claim({ text: "AI-generated, formally verified database engines", paper: ["main.tex", "AI-Generated and Formally Verified Database Systems"], repo: [README, "AI-generated, formally verified database engines"] }),
    speed: speed(ctx),
    correctness: correctness(ctx),
  };
}
