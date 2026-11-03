// Performance page data: template synthesis (TPC-H SF100, SEC-EDGAR SF3) and engine synthesis (TPC-H SF100).
//
// Templates. Per template, worker count and system, the mean time over the template's bindings, from this
// repository's results (times.json of GenDB-V with agent-designed storage, GenDB-V with plain arrays, DuckDB and
// Umbra), as the paper computes them. The totals sum these means; the headline speedups are geometric means of
// baseline/GenDB-V over every template and worker count. Checked against the results READMEs and the values the
// paper states; with --paper also against the paper's figure data, its runtime table and its sentences.
//
// Engine. The engine is not in this repository, so its version totals (the paper's figure data,
// figures/data/engine-timeline.csv) are kept below; with --paper they must equal that file and engine-progress.csv.
// Its baselines are the sums over the 22 templates at binding v0 of this repository's DuckDB and Umbra times, and
// version 16 must give the end point the paper states. The latest engine (one engine for every schema), the timeline's
// last point, is kept below too, per TPC-H template; with --engine-records DIR (its version's folder) every time must equal its
// timing records there.
import fs from "node:fs";
import path from "node:path";
import { csv, geomean } from "../lib.mjs";

const THREADS = ["1", "32", "64"];
const ENGINE_THREADS = ["1", "64"];
// Per series: its key in the page's data, its times in the results, and its names in the paper's figure data (the
// per-template means' column and the totals' system).
const SYSTEMS = [
  { key: "agent", dir: "gendb-v-agent-designed-storage", csv: "GenDB_ms", total: "GenDB" },
  { key: "plain", dir: "gendb-v-plain-array-storage", csv: "GenDBPlain_ms", total: "GenDBPlain" },
];
const BASELINES = [
  { key: "duckdb", name: "DuckDB", field: "duckdb_ms", csv: "DuckDB_ms", total: "DuckDB" },
  { key: "umbra", name: "Umbra", field: "umbra_ms", csv: "Umbra_ms", total: "Umbra" },
];
const SERIES = [...SYSTEMS, ...BASELINES];
const WORKLOADS = [
  { id: "tpch", name: "TPC-H", scale: "SF100", dir: "results/tpch-sf100", paperName: "TPC-H SF100", tableName: "TPC-H", stated: ["51.6", "22.0"] },
  { id: "sec", name: "SEC-EDGAR", scale: "SF3", dir: "results/sec-edgar-sf3", paperName: "SEC-EDGAR SF3", tableName: "SEC-EDGAR", stated: ["61.3", "28.3"] },
];
const README = "README.md", ABSTRACT = "sections/00-abstract.tex", INTRO = "sections/01-introduction.tex", EVAL = "sections/06-evaluation.tex";
const TABLE = "figures/eval-runtime-table.tex", MEANS = "figures/data/template-visible-mean.csv", TOTALS = "figures/data/template-visible-totals.csv";
const TIMELINE = "figures/data/engine-timeline.csv", PROGRESS = "figures/data/engine-progress.csv";

/**
 * The engine's versions on TPC-H SF100: total time (s) of the 22 templates at 1 and 64 workers. Versions 0 and 1 do
 * not finish every template (the paper's figure marks them incomplete).
 */
const ENGINE = [
  { v: 0 }, { v: 1 },
  { v: 2, t1: 247.2, t64: 47.1 }, { v: 3, t1: 226.2, t64: 28.2 }, { v: 4, t1: 195.4, t64: 21.6 },
  { v: 5, t1: 166.2, t64: 18.1 }, { v: 6, t1: 162.3, t64: 17.5 }, { v: 7, t1: 150.9, t64: 14.7 },
  { v: 8, t1: 151.1, t64: 12.6 }, { v: 9, t1: 148.1, t64: 12.1 }, { v: 10, t1: 143.6, t64: 11.4 },
  { v: 11, t1: 141.7, t64: 10.8 }, { v: 12, t1: 132.8, t64: 10.8 }, { v: 13, t1: 114.7, t64: 10.4 },
  { v: 14, t1: 115.8, t64: 9.18 }, { v: 15, t1: 115.7, t64: 9.25 }, { v: 16, t1: 109.26, t64: 9.16 },
];
/** Version 16 as the paper states it: time (s) and speedups over DuckDB and Umbra, at 1 and 64 workers. */
const ENGINE_STATED = { 1: { time: "109.3", DuckDB: "3.4", Umbra: "1.52" }, 64: { time: "9.16", DuckDB: "1.8", Umbra: "1.27" } };

/**
 * The latest engine: one verified engine with one storage design for every schema (version 4 of the one-engine run).
 * Per TPC-H template Q1-Q22 its time at binding v0 (ns, the median of its timed calls) at 1, 32 and 64 workers.
 */
const LATEST = {
    Q01: [10083182922, 445176509, 343191791], Q02: [342523251, 222555890, 235555382],
    Q03: [5810244894, 508368515, 483386958], Q04: [1940707112, 149378223, 155756080],
    Q05: [4426687764, 308891741, 305231280], Q06: [1609693147, 109402866, 102029782],
    Q07: [3899759950, 395556957, 339966566], Q08: [1462718110, 144328243, 145326043],
    Q09: [15460713395, 1222642230, 1036371849], Q10: [5883063305, 712615139, 654152400],
    Q11: [1413587311, 401688709, 388786356], Q12: [3410851309, 190318979, 182791833],
    Q13: [7265121553, 566506751, 538772244], Q14: [2336208854, 141397495, 129919383],
    Q15: [3063279012, 384336595, 358496695], Q16: [1760483827, 275292999, 262766203],
    Q17: [315351083, 89225969, 105619744], Q18: [6812924945, 340224980, 320318528],
    Q19: [808294072, 137373087, 135816482], Q20: [2455040177, 310175048, 263702875],
    Q21: [5883910008, 655271682, 526180739], Q22: [1320584093, 166853172, 144829147],
};
/** The latest engine's TPC-H totals (s) and speedups as stated with it, at 1, 32 and 64 workers. */
const LATEST_STATED = { time: ["87.76", "7.88", "7.16"], DuckDB: ["4.28", "2.74", "2.28"], Umbra: ["1.89", "1.27", "1.63"] };
/** The note beside the latest engine: the authors' statement of a plan, so it has no source to check. */
const LATEST_NOTE = "The engine keeps evolving. We will open-source it and update these results over time.";
/** --engine-records DIR: the latest engine's version folder (its race.json), else null. */
const ENGINE_RECORDS = (() => { const i = process.argv.indexOf("--engine-records"); return i > 0 ? path.resolve(process.argv[i + 1]) : null; })();

const decimals = (text) => (text.split(".")[1] || "").length;
/** `value` printed with as many decimals as `like`. */
const as = (value, like) => value.toFixed(decimals(like));
const same = (a, b) => Math.abs(a - b) <= 1e-6 * Math.max(1, Math.abs(b));
const qnum = (q) => Number(q.replace(/^Q0*/, ""));
const ms6 = (x) => Number(x.toFixed(6));

/** Seconds as the page prints the template totals: three significant digits, at least the milliseconds (368, 4.45). */
const seconds = (s) => (s >= 100 ? s.toFixed(0) : s >= 10 ? s.toFixed(1) : s >= 1 ? s.toFixed(2) : s.toFixed(3));
/** Seconds as the page prints the engine's totals, the paper's precision: 109.3, 47.1, 9.16. */
const engineSeconds = (s) => (s >= 10 ? s.toFixed(1) : s.toFixed(2));

/** Per template and worker count: the mean over bindings of every system, from the results' times.json. */
function workloadMeans(ctx, w) {
  const runs = Object.fromEntries(SYSTEMS.map((s) => [s.key, ctx.readJson(`${w.dir}/${s.dir}/times.json`)]));
  const base = ctx.readJson(`${w.dir}/duckdb-umbra-baselines/times.json`);
  const names = Object.keys(base).sort((a, b) => qnum(a) - qnum(b));
  for (const s of SYSTEMS) ctx.check(Object.keys(runs[s.key]).sort().join() === [...names].sort().join(), `${w.name}: ${s.dir} and the baselines have the same templates`);
  return names.map((q) => {
    const bindings = Object.keys(base[q]).sort();
    for (const s of SYSTEMS) ctx.check(Object.keys(runs[s.key][q]).sort().join() === bindings.join(), `${w.name} ${q}: ${s.dir} has the baselines' bindings`);
    const avg = (f) => bindings.reduce((sum, v) => sum + f(v), 0) / bindings.length;
    const ms = {};
    for (const t of THREADS) {
      ms[t] = {};
      for (const s of SYSTEMS) ms[t][s.key] = avg((v) => runs[s.key][q][v][t].gendb_ms);
      for (const b of BASELINES) ms[t][b.key] = avg((v) => base[q][v][t][b.field]);
      ctx.check(Object.values(ms[t]).every((x) => Number.isFinite(x) && x > 0), `${w.name} ${q} ${t}: positive times`);
    }
    return { name: q, id: `Q${qnum(q)}`, bindings: bindings.length, ms };
  });
}

/** With --paper: every per-template mean equals the paper's figure data (template-visible-mean.csv). */
function againstFigureData(ctx, w, queries) {
  const text = ctx.readPaper(MEANS);
  if (!text) return;
  const rows = csv(text).filter((r) => r.workload === w.paperName);
  ctx.check(rows.length === queries.length * THREADS.length, `${w.name}: the paper's figure data has ${rows.length} template-thread rows, the results ${queries.length * THREADS.length}`);
  for (const q of queries) for (const t of THREADS) {
    const r = rows.find((x) => x.template === q.name && x.threads === t);
    const ok = r && Number(r.bindings) === q.bindings && SERIES.every((c) => same(Number(r[c.csv]), q.ms[t][c.key]));
    ctx.check(ok, `${w.name} ${q.name} ${t}: the per-template means equal the paper's figure data`);
  }
}

/** Totals (s) per worker count and system: checked against the results README and, with --paper, Table 3 and its data. */
function totals(ctx, w, queries) {
  const sum = {};
  for (const t of THREADS) {
    sum[t] = {};
    for (const { key } of SERIES) sum[t][key] = queries.reduce((s, q) => s + q.ms[t][key], 0) / 1000;
  }
  // the results README: TPC-H states the sum of all medians (3 bindings per template), SEC-EDGAR the sum of the means
  const cols = SERIES.map(({ key }) => THREADS.map((t) => (w.id === "tpch" ? 3 * sum[t][key] : sum[t][key]).toFixed(3)).join(" / "));
  const row = w.id === "tpch" ? "Sum of medians, all 3 bindings, 1 / 32 / 64 workers (s)" : "Total, 1 / 32 / 64 workers (s)";
  if (w.id === "tpch") ctx.check(queries.every((q) => q.bindings === 3), "TPC-H: every template has 3 bindings");
  ctx.quote(`| ${row} | ${cols.join(" | ")} |`, `${w.dir}/README.md`);
  // the paper's Table 3 rows and the totals data
  THREADS.forEach((t, i) => {
    const s = sum[t];
    ctx.quotePaper(`${i ? "" : w.tableName} & ${t} & ${s.duckdb.toFixed(3)} & ${s.umbra.toFixed(3)} & ${s.plain.toFixed(3)} & \\textbf{${s.agent.toFixed(3)}} \\\\`, TABLE);
  });
  const text = ctx.readPaper(TOTALS);
  if (text) {
    const rows = csv(text).filter((r) => r.workload === w.paperName);
    for (const t of THREADS) for (const { key, total } of SERIES) {
      const r = rows.find((x) => x.threads === t && x.system === total);
      ctx.check(r && same(Number(r.total_ms) / 1000, sum[t][key]), `${w.name} ${t} ${total}: the total equals the paper's totals data`);
    }
  }
  return sum;
}

/** Speedups of every template and worker count: baseline time / GenDB-V time. */
const ratios = (queries, system, baseline) => queries.flatMap((q) => THREADS.map((t) => q.ms[t][baseline] / q.ms[t][system]));

function templates(ctx) {
  const c = ctx.claim;
  const all = WORKLOADS.map((w) => {
    const queries = workloadMeans(ctx, w);
    againstFigureData(ctx, w, queries);
    const sum = totals(ctx, w, queries);
    const headline = BASELINES.map((b, i) => {
      const text = geomean(ratios(queries, "agent", b.key)).toFixed(1);
      ctx.check(text === w.stated[i], `${w.name} over ${b.name}: geometric-mean speedup ${text}, the paper states ${w.stated[i]}`);
      return { baseline: b.name, text };
    });
    return { w, queries, sum, headline };
  });

  // the paper's statements on these results, built from the computed values
  const [tpch, sec] = all;
  const hs = all.map((x) => x.headline.map((s) => s.text));
  ctx.quotePaper(`geometric-mean speedups reach $${hs[0][0]}\\times$ over DuckDB and $${hs[0][1]}\\times$ over Umbra on TPC-H, and $${hs[1][0]}\\times$ and $${hs[1][1]}\\times$ on SEC-EDGAR`, EVAL);
  const range = (xs) => `${Math.min(...xs).toFixed(1)}--${Math.max(...xs).toFixed(1)}`;
  ctx.quotePaper(`For verified template implementations, GenDB-V achieves geometric-mean speedups of ${range(hs.flat().map(Number))}$\\times$ over DuckDB and Umbra`, ABSTRACT);
  ctx.check(all.every((x) => BASELINES.every((b) => ratios(x.queries, "agent", b.key).every((r) => r > 1))), "agent-designed storage is faster than both baselines for every template and worker count");
  ctx.quotePaper("Joint storage and query optimization outperforms both baselines on every evaluated template at all three thread counts.", EVAL);
  const wins = (x, b) => ratios(x.queries, "plain", b).filter((r) => r > 1).length;
  const n = (x) => x.queries.length * THREADS.length;
  const of = (x, b) => (wins(x, b) === n(x) ? `all ${n(x)}` : `${wins(x, b)} of ${n(x)}`);
  ctx.quotePaper(`GenDB-V outperforms DuckDB on ${of(tpch, "duckdb")} TPC-H query--thread combinations and ${of(sec, "duckdb")} SEC-EDGAR combinations, and Umbra on ${of(tpch, "umbra")} and ${of(sec, "umbra")}, respectively.`, EVAL);
  const plainGeo = all.flatMap((x) => BASELINES.map((b) => geomean(ratios(x.queries, "plain", b.key))));
  ctx.quotePaper(`verified query implementations achieve geometric-mean speedups of ${Math.min(...plainGeo).toFixed(2)}--${Math.max(...plainGeo).toFixed(2)}$\\times$ over DuckDB and Umbra`, INTRO);
  const gain = (x) => THREADS.map((t) => x.sum[t].plain / x.sum[t].agent);
  ctx.quotePaper(`further reduces total workload time by $${Math.min(...gain(tpch)).toFixed(1)}\\times$--$${Math.max(...gain(tpch)).toFixed(1)}\\times$ on TPC-H and $${Math.min(...gain(sec)).toFixed(1)}\\times$--$${Math.max(...gain(sec)).toFixed(1)}\\times$ on SEC-EDGAR`, EVAL);
  // the case studies' numbers (the page shows the same values in its per-query view)
  const cell = (x, id, t) => x.queries.find((q) => q.id === id).ms[t];
  const q21 = cell(tpch, "Q21", "32");
  ctx.quotePaper(`the implementation takes ${q21.plain.toFixed(0)}\\,ms at 32 threads, outperforming DuckDB by $${(q21.duckdb / q21.plain).toFixed(1)}\\times$ and Umbra by $${(q21.umbra / q21.plain).toFixed(1)}\\times$`, EVAL);
  const q2 = cell(tpch, "Q2", "1");
  ctx.quotePaper(`The implementation takes ${q2.agent.toFixed(2)}\\,ms on one thread, compared with ${q2.plain.toFixed(0)}\\,ms for the separately synthesized plain-array implementation.`, EVAL);
  ctx.quotePaper("We measure query execution time at 1, 32, and 64 threads", EVAL);
  ctx.quotePaper("For each template, we average its execution time across its three parameter bindings", EVAL);

  return {
    title: c({ text: "Template synthesis", paper: [EVAL, "\\subsection{Verified Template Synthesis}"] }),
    line: c({ text: "One verified package for each SQL template.", repo: [README, "One verified package answers one hot query template"], paper: [EVAL, "GenDB-V synthesizes formally verified implementations for all benchmark templates."] }),
    caption: c({ text: "Geometric-mean speedup over all queries and thread counts", paper: [EVAL, "Across templates and thread counts, geometric-mean speedups reach"] }),
    totalsTitle: c({ text: "Total time", paper: [EVAL, "reports total workload execution times"] }),
    queriesTitle: c({ text: "Speedup per query", paper: ["figures/template-perf-figure.tex", "per-query speedup of GenDB-V over DuckDB and Umbra"] }),
    systems: {
      agent: c({ text: "Agent-designed storage", repo: ["results/tpch-sf100/gendb-v-agent-designed-storage/README.md", "A workload agent designed the shared storage."], paper: [EVAL, "agents co-design physical storage layouts and query execution code"] }),
      plain: c({ text: "Plain arrays", repo: ["results/tpch-sf100/gendb-v-plain-array-storage/README.md", "Every column of every table is a plain typed array in the original row order"], paper: [EVAL, "\\emph{query optimization over plain arrays}"] }),
    },
    baselines: BASELINES.map((b) => b.name),
    threads: THREADS,
    workloads: all.map(({ w, queries, sum, headline }) => ({
      id: w.id, name: w.name, scale: w.scale, headline,
      totals: Object.fromEntries(THREADS.map((t) => [t, Object.fromEntries(Object.entries(sum[t]).map(([k, s]) => [k, { s: Number(s.toFixed(6)), text: seconds(s) }]))])),
      queries: queries.map((q) => ({ id: q.id, ms: Object.fromEntries(THREADS.map((t) => [t, Object.fromEntries(Object.entries(q.ms[t]).map(([k, v]) => [k, ms6(v)]))])) })),
    })),
  };
}

/** A workload's baselines at binding v0: per baseline and worker count, the sum over its templates (s). */
function v0Baselines(ctx, w) {
  const base = ctx.readJson(`${w.dir}/duckdb-umbra-baselines/times.json`);
  ctx.check(Object.values(base).every((q) => q.v0), `${w.name}: every template has binding v0`);
  const out = {};
  for (const b of BASELINES) {
    out[b.name] = {};
    for (const t of THREADS) out[b.name][t] = Number((Object.values(base).reduce((s, q) => s + q.v0[t][b.field], 0) / 1000).toFixed(3));
  }
  return { out, base };
}

/** The engine's baselines: the TPC-H sums at binding v0, which the results README states. */
function engineBaselines(ctx) {
  const { out, base } = v0Baselines(ctx, WORKLOADS[0]);
  ctx.check(Object.keys(base).length === 22, "TPC-H: 22 templates");
  const cols = BASELINES.map((b) => THREADS.map((t) => out[b.name][t].toFixed(3)).join(" / "));
  ctx.quote(`| ${cols.join(" | ")} |`, "results/tpch-sf100/README.md");
  return out;
}

/** With --paper: the versions above equal the paper's figure data. */
function engineAgainstPaper(ctx, base) {
  const timeline = ctx.readPaper(TIMELINE), progress = ctx.readPaper(PROGRESS);
  if (!timeline || !progress) return;
  const rows = csv(timeline);
  for (const b of BASELINES) {
    const r = rows.find((x) => x.run === b.name && x.version === "baseline");
    ctx.check(r && THREADS.every((t) => Number(r[`t${t}_s`]) === base[b.name][t]), `engine: the ${b.name} totals equal the paper's engine-timeline.csv`);
  }
  const run = rows.filter((r) => r.run === "coopt");
  const prog = csv(progress);
  for (const e of ENGINE) {
    const name = `v${String(e.v).padStart(3, "0")}`;
    const r = run.find((x) => x.version === name || x.version === `${name}-move`);
    const p = prog.find((x) => x.version === name);
    ctx.check(p, `engine v${e.v}: in the paper's engine-progress.csv`);
    if (e.t1 === undefined) {
      ctx.check(p && !p.sf100_t1_s, `engine v${e.v}: no SF100 total in engine-progress.csv (incomplete)`);
      if (r) ctx.check(ENGINE_THREADS.some((t) => Number(r[`finished${t}`]) < 22), `engine v${e.v}: unfinished templates in engine-timeline.csv`);
      continue;
    }
    ctx.check(r && ENGINE_THREADS.every((t) => Number(r[`t${t}_s`]) === e[`t${t}`] && r[`finished${t}`] === "22"), `engine v${e.v}: the totals equal the paper's engine-timeline.csv`);
    ctx.check(p && ENGINE_THREADS.every((t) => as(Number(p[`sf100_t${t}_s`]), String(e[`t${t}`])) === String(e[`t${t}`]) && p[`sf100_finished${t}`] === "22"), `engine v${e.v}: the totals agree with the paper's engine-progress.csv`);
  }
  ctx.check(run.length === ENGINE.length - 1, `engine: the paper's run has ${run.length} rows, the page ${ENGINE.length - 1} (version 0 has no SF100 row)`);
  ctx.check(prog.find((x) => x.version === "v000")?.sf1_finished1 === "2", "engine v0: 2 of 22 templates finish at SF1");
}

/** With --engine-records: every kept time equals the latest engine's TPC-H timing records (binding v0, finished), whose baselines
 * are this repository's (the faster of DuckDB and Umbra per template and worker count). */
function latestAgainstRecords(ctx, base) {
  if (!ENGINE_RECORDS) return;
  const race = JSON.parse(fs.readFileSync(path.join(ENGINE_RECORDS, "race.json"), "utf8"));
  ctx.check(race.binding === "v0" && race.candidate_score.binding === "v0", "latest: the records are at binding v0");
  const cells = race.candidate_score.cells.filter((x) => x.template in LATEST);
  ctx.check(cells.length === Object.keys(LATEST).length * THREADS.length, `latest: ${cells.length} records for the kept templates`);
  for (const [q, times] of Object.entries(LATEST)) THREADS.forEach((t, i) => {
    const r = cells.find((x) => x.template === q && String(x.workers) === t);
    const faster = Math.round(Math.min(...BASELINES.map((b) => base[q].v0[t][b.field])) * 1e6);
    ctx.check(r && r.status.status === "finished" && r.time_ns === times[i] && r.faster_baseline_ns === faster, `latest TPC-H ${q} ${t}: the time equals the records`);
  });
}

/**
 * The latest engine, the timeline's last point and the panels' headline: its TPC-H total time and its speedups over
 * DuckDB and Umbra at 1 and 64 workers, and the note beside it.
 */
function latest(ctx) {
  const { out, base } = v0Baselines(ctx, WORKLOADS[0]);
  ctx.check(Object.keys(LATEST).sort().join() === Object.keys(base).sort().join(), "latest: every TPC-H template of the results");
  latestAgainstRecords(ctx, base);
  const s = {}, text = {}, speedups = {};
  THREADS.forEach((t, i) => {
    const total = Object.values(LATEST).reduce((sum, times) => sum + times[i], 0) / 1e9;
    ctx.check(as(total, LATEST_STATED.time[i]) === LATEST_STATED.time[i], `latest at ${t} workers: ${as(total, LATEST_STATED.time[i])} s, stated ${LATEST_STATED.time[i]} s`);
    const xs = BASELINES.map((b) => {
      const x = (out[b.name][t] / total).toFixed(2);
      ctx.check(x === LATEST_STATED[b.name][i], `latest over ${b.name} at ${t} workers: ${x}, stated ${LATEST_STATED[b.name][i]}`);
      return { baseline: b.name, text: x };
    });
    if (ENGINE_THREADS.includes(t)) { s[t] = Number(total.toFixed(6)); text[t] = engineSeconds(total); speedups[t] = xs; }
  });
  return { label: "Latest", note: LATEST_NOTE, s, text, speedups };
}

/** The section's line; each part of it has a source. */
function engineLine(ctx) {
  ctx.quote("An AI agent writes Rust code and its proofs.", README);
  ctx.quote("a version is accepted only when it is faster in total on the workloads it is tuned for", "GUIDE.md");
  ctx.quotePaper("formally verified for correctness", ABSTRACT);
  return ctx.claim({ text: "One formally verified general-purpose engine in Rust, for every schema, optimized for TPC-H:",
    repo: ["GUIDE.md", "one verified engine that answers every supported query over the schema"],
    paper: [ABSTRACT, "general-purpose engines that accept any query within a supported SQL subset"] });
}

function engine(ctx) {
  const c = ctx.claim;
  const base = engineBaselines(ctx);
  engineAgainstPaper(ctx, base);
  ctx.check(ENGINE.every((e, i) => e.v === i), "engine: versions 0 to 16 in order");
  const done = ENGINE.filter((e) => e.t1 !== undefined);
  const last = ENGINE[ENGINE.length - 1];
  const first = done[0];
  ctx.check(first.v === 2 && first.t1 < base.DuckDB["1"], "engine: version 2 is the first complete one and is faster than DuckDB at 1 worker");
  ctx.quotePaper("By version~2, the engine completes the full workload at SF100 and outperforms DuckDB at one thread.", EVAL);
  ctx.quotePaper("from the reference interpreter, which completes only 2 of 22 queries within 60\\,s at SF1", EVAL);
  // version 16 against the paper's statements (its times show in the timeline)
  const v16 = ENGINE_THREADS.map((t) => {
    const stated = ENGINE_STATED[t];
    const time = engineSeconds(last[`t${t}`]);
    ctx.check(time === stated.time, `engine v16 at ${t} workers: ${time} s, the paper states ${stated.time} s`);
    const speedups = BASELINES.map((b) => {
      const text = as(base[b.name][t] / last[`t${t}`], stated[b.name]);
      ctx.check(text === stated[b.name], `engine v16 over ${b.name} at ${t} workers: ${text}, the paper states ${stated[b.name]}`);
      return { baseline: b.name, text };
    });
    return { threads: t, time, speedups };
  });
  const [p1, p64] = v16;
  ctx.quotePaper(`Version~16 reduces total execution time to ${p1.time}\\,s at one thread and ${p64.time}\\,s at 64 threads, achieving speedups of $${p1.speedups[0].text}\\times$ and $${p64.speedups[0].text}\\times$ over DuckDB, and $${p1.speedups[1].text}\\times$ and $${p64.speedups[1].text}\\times$ over Umbra, respectively.`, EVAL);
  const all = v16.flatMap((p) => p.speedups.map((s) => Number(s.text)));
  const lo = v16.flatMap((p) => p.speedups).find((s) => Number(s.text) === Math.min(...all)).text;
  const hi = v16.flatMap((p) => p.speedups).find((s) => Number(s.text) === Math.max(...all)).text;
  ctx.quotePaper(`For a verified general-purpose engine, GenDB-V also achieves speedups of ${lo}--${hi}$\\times$ on TPC-H.`, ABSTRACT);
  // the panels' headline: the latest engine
  const { speedups, ...newest } = latest(ctx);
  const panels = ENGINE_THREADS.map((t) => ({ threads: t, label: newest.label, time: newest.text[t], speedups: speedups[t] }));
  return {
    title: c({ text: "Engine synthesis", paper: ["figures/engine-timeline-figure.tex", "Verified engine synthesis on TPC-H SF100."] }),
    line: engineLine(ctx),
    workload: "TPC-H SF100",
    incomplete: c({ text: "Incomplete", paper: [EVAL, "completes only 2 of 22 queries within 60\\,s at SF1"] }),
    baselines: BASELINES.map((b) => ({ name: b.name, s: Object.fromEntries(ENGINE_THREADS.map((t) => [t, base[b.name][t]])) })),
    versions: ENGINE.map((e) => (e.t1 === undefined ? { v: e.v } : { v: e.v, s: { 1: e.t1, 64: e.t64 }, text: { 1: engineSeconds(e.t1), 64: engineSeconds(e.t64) } })),
    panels,
    latest: newest,
  };
}

export default function build(ctx) {
  const c = ctx.claim;
  const t = templates(ctx);
  const e = engine(ctx);
  // the lead's repository sources: every cell of both workloads is faster than the faster baseline
  ctx.quote("| Cells faster than the faster baseline | 48/48 |", "results/sec-edgar-sf3/README.md");
  return {
    title: "Performance",
    lead: c({ text: "Verified code, faster than DuckDB and Umbra.", paper: [INTRO, "Joint storage and query optimization achieves geometric-mean speedups of 22.0--61.3$\\times$ over DuckDB and Umbra across the two benchmarks"], repo: ["results/tpch-sf100/README.md", "| Cells faster than the faster baseline | 198/198 |"] }),
    // the two results, engine first; the page's sections follow this order
    jump: [
      { id: "engine", title: e.title, line: c({ text: "One verified engine for every supported query", repo: [README, "One verified engine answers every supported query over a schema"], paper: [ABSTRACT, "general-purpose engines that accept any query within a supported SQL subset"] }) },
      { id: "templates", title: t.title, line: c({ text: "One verified package per hot query template", repo: [README, "One verified package answers one hot query template, for every parameter value."], paper: [ABSTRACT, "GenDB-V supports specialized implementations of SQL templates"] }) },
    ],
    templates: t,
    engine: e,
  };
}
