#!/usr/bin/env node
// The site's build: node docs/build/build.mjs [--paper PATH] [--page ID] [--repo PATH] [--out DIR]
// For every page of the registry (js/pages.js) that is not `soon` and has a builder build/pages/<id>.mjs, runs the
// builder and writes its data to data/<id>.json. Builders check every number and claim they write: against this
// repository's results, and, with --paper (the paper's source folder), against the paper's text and figure data.
// Any failed check fails the build, which then writes nothing. The same inputs give byte-identical files.
// --page builds one page only. --repo reads another copy of the repository and --out writes data/ under another
// folder (the checks use both).
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { PAGES } from "../js/pages.js";
import { LINKS } from "../js/links.js";
import { context, stableJson } from "./lib.mjs";

const here = path.dirname(fileURLToPath(import.meta.url));
const site = path.resolve(here, "..");
const arg = (name) => {
  const i = process.argv.indexOf(name);
  return i > 0 ? process.argv[i + 1] : null;
};
const repo = path.resolve(arg("--repo") || path.join(site, ".."));
const paper = arg("--paper") ? path.resolve(arg("--paper")) : null;
const dest = path.resolve(arg("--out") || site);
const only = arg("--page");
if (only && !PAGES.some((p) => p.id === only)) throw new Error(`--page: no page ${only} in js/pages.js`);
if (paper && !fs.existsSync(path.join(paper, "sections"))) throw new Error(`--paper: no sections/ in ${paper}`);

const out = [];
let failed = 0;
for (const page of PAGES) {
  const file = path.join(here, "pages", `${page.id}.mjs`);
  if (page.soon || !fs.existsSync(file) || (only && page.id !== only)) continue;
  const ctx = context({ repo, paper, page: page.id });
  const { default: build } = await import(pathToFileURL(file).href);
  const data = await build(ctx);
  const { checks, paperChecks, problems } = ctx.summary();
  console.error(`[build] ${page.id}: ${checks} checks${paper ? ` (${paperChecks} against the paper)` : ", paper checks skipped (no --paper)"}, ${problems.length} failed`);
  for (const p of problems) console.error(`  FAILED ${p}`);
  failed += problems.length;
  out.push([`data/${page.id}.json`, stableJson(data)]);
}
if (failed) {
  console.error(`[build] ${failed} failed checks: nothing written`);
  process.exit(1);
}
for (const [rel, text] of out) {
  fs.mkdirSync(path.dirname(path.join(dest, rel)), { recursive: true });
  fs.writeFileSync(path.join(dest, rel), text);
}
console.error(`[build] wrote ${out.map(([rel]) => rel).join(", ")}`);
const unset = Object.keys(LINKS).filter((k) => !LINKS[k]);
if (unset.length) console.error(`[build] warning: links not set yet in js/links.js: ${unset.join(", ")} (they show as "#")`);
