// Planted errors the build must catch: node docs/checks/negbuild.mjs   (PAPER: the paper's folder, for the paper ones)
// Each case runs the build on a copy of its inputs with one change, into a scratch folder, and passes when the build
// fails with that change's message and writes nothing; a control run on unchanged inputs must pass. The copies are
// symbolic links except the changed file. Scratch: CHECKS_TMP, else TMPDIR, else checks/out/tmp.
import fs from "node:fs";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const here = path.dirname(fileURLToPath(import.meta.url));
const site = path.resolve(here, "..");
const repo = path.resolve(site, "..");
const paper = process.env.PAPER ? path.resolve(process.env.PAPER) : null;
const tmp = path.join(process.env.CHECKS_TMP || process.env.TMPDIR || path.join(here, "out/tmp"), "site-negbuild");
const problems = [], lines = [];

/** A copy of `from` at `to` as symbolic links, except the file `rel`, which is copied and changed by `edit`. */
function mirror(from, to, rel, edit) {
  const down = rel.split("/");
  fs.mkdirSync(to, { recursive: true });
  for (const name of fs.readdirSync(from)) {
    if (name !== down[0]) fs.symlinkSync(path.join(from, name), path.join(to, name));
    else if (down.length > 1) mirror(path.join(from, name), path.join(to, name), down.slice(1).join("/"), edit);
    else {
      const text = fs.readFileSync(path.join(from, name), "utf8"), changed = edit(text);
      if (changed === text) throw new Error(`the planted change of ${rel} changed nothing`);
      fs.writeFileSync(path.join(to, name), changed);
    }
  }
}

function run(name, { repoEdit, paperEdit, expect }) {
  const root = path.join(tmp, name);
  fs.rmSync(root, { recursive: true, force: true });
  let r = repo, p = paper;
  if (repoEdit) mirror(repo, (r = path.join(root, "repo")), ...repoEdit);
  if (paperEdit) mirror(paper, (p = path.join(root, "paper")), ...paperEdit);
  const out = path.join(root, "out");
  const res = spawnSync("node", [path.join(site, "build/build.mjs"), "--repo", r, "--out", out, ...(p ? ["--paper", p] : [])], { encoding: "utf8" });
  const wrote = fs.existsSync(path.join(out, "data"));
  const ok = expect ? res.status !== 0 && expect.test(res.stderr) && !wrote : res.status === 0 && wrote;
  const failedLine = (res.stderr.match(/FAILED .*/) || [""])[0].slice(0, 140);
  lines.push(`${ok ? "ok  " : "BAD "} ${name}: exit ${res.status}, data ${wrote ? "written" : "not written"}${failedLine ? `; ${failedLine}` : ""}`);
  if (!ok) problems.push(`${name}: ${expect ? `not caught as ${expect}` : "the control run failed"}\n${res.stderr.slice(-800)}`);
  fs.rmSync(root, { recursive: true, force: true });
}

const TIMES = "results/tpch-sf100/gendb-v-agent-designed-storage/times.json";
run("control", {});
run("a GenDB-V time changed", {
  repoEdit: [TIMES, (t) => t.replace('"gendb_ms": 632.622007', '"gendb_ms": 948.933011')],
  expect: /TPC-H over DuckDB: geometric-mean speedup 51\.\d, the paper states 51\.6/,
});
run("a baseline time changed", {
  repoEdit: ["results/sec-edgar-sf3/duckdb-umbra-baselines/times.json", (t) => t.replace('"umbra_ms": 447.843', '"umbra_ms": 4478.43')],
  expect: /SEC-EDGAR over Umbra: geometric-mean speedup/,
});
run("a README sentence changed", {
  repoEdit: ["README.md", (t) => t.replace("The agent cannot change the claim.", "The agent can change the claim.")],
  expect: /"The agent cannot change the claim\." is not in README\.md/,
});
if (paper) {
  run("the paper states another speedup", {
    paperEdit: ["sections/06-evaluation.tex", (t) => t.replace("$51.6\\times$ over DuckDB", "$51.7\\times$ over DuckDB")],
    expect: /is not in the paper's sections\/06-evaluation\.tex/,
  });
  run("the paper's figure data differ", {
    paperEdit: ["figures/data/template-visible-mean.csv", (t) => t.replace("TPC-H SF100,Q01,1,3,644.730981", "TPC-H SF100,Q01,1,3,644.830981")],
    expect: /TPC-H Q01 1: the per-template means equal the paper's figure data/,
  });
  run("the paper's abstract changed", {
    paperEdit: ["sections/00-abstract.tex", (t) => t.replace("wrong-answer bugs even in mature", "bugs even in mature")],
    expect: /is not in the paper's sections\/00-abstract\.tex/,
  });
} else lines.push("(paper cases skipped: no PAPER)");
fs.rmSync(tmp, { recursive: true, force: true });

console.log(lines.join("\n"));
if (problems.length) console.log(`${problems.length} problems:\n  ${problems.join("\n  ")}`);
console.log(`${problems.length ? "FAIL" : "PASS"} negbuild: ${lines.filter((l) => /^(ok|BAD)/.test(l)).length} runs, planted errors caught and nothing written`);
process.exitCode = problems.length ? 1 : 0;
