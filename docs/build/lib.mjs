// Shared by the page builders: the build context (files, checks) and stable JSON.
import fs from "node:fs";
import path from "node:path";

/** JSON with sorted object keys and a final newline, so the same data gives the same bytes. */
export function stableJson(value) {
  const sort = (v) => {
    if (Array.isArray(v)) return v.map(sort);
    if (v && typeof v === "object") return Object.fromEntries(Object.keys(v).sort().filter((k) => v[k] !== undefined).map((k) => [k, sort(v[k])]));
    return v;
  };
  return `${JSON.stringify(sort(value), null, 1)}\n`;
}

/** Text with runs of white space made one space, for comparing quotes with their source. */
const flat = (t) => t.replace(/\s+/g, " ").trim().toLowerCase();
/** LaTeX source without its comments (from an unescaped % to the end of the line). */
const uncomment = (t) => t.replace(/(^|[^\\])%.*$/gm, "$1");

/**
 * The context a builder gets:
 *  - repo, paper: the repository root and the paper's source folder (null without --paper);
 *  - read(rel), readJson(rel): a file of the repository; readPaper(rel): a file of the paper (null without --paper);
 *  - check(ok, what): record one check (a failed check fails the build);
 *  - quote(text, rel): check that `text` occurs in repository file `rel` (white space and case aside);
 *    quotePaper(text, rel): the same in a paper file (LaTeX comments aside), skipped without --paper;
 *  - claim({ text, paper: [rel, quote] | repo: [rel, quote] }): a sentence of the page with its source; checks the
 *    quote and returns the text.
 */
export function context({ repo, paper, page }) {
  let checks = 0, paperChecks = 0;
  const problems = [];
  const cache = new Map();
  const load = (abs) => {
    if (!cache.has(abs)) cache.set(abs, fs.readFileSync(abs, "utf8"));
    return cache.get(abs);
  };
  const check = (ok, what) => {
    checks++;
    if (!ok) problems.push(`${page}: ${what}`);
    return Boolean(ok);
  };
  const ctx = {
    repo, paper,
    read: (rel) => load(path.join(repo, rel)),
    readJson: (rel) => JSON.parse(load(path.join(repo, rel))),
    readPaper: (rel) => (paper ? load(path.join(paper, rel)) : null),
    check,
    quote: (text, rel) => check(flat(load(path.join(repo, rel))).includes(flat(text)), `"${text}" is not in ${rel}`),
    quotePaper: (text, rel) => {
      if (!paper) return true;
      paperChecks++;
      const source = load(path.join(paper, rel));
      return check(flat(rel.endsWith(".tex") ? uncomment(source) : source).includes(flat(text)), `"${text}" is not in the paper's ${rel}`);
    },
    claim: ({ text, paper: p, repo: r }) => {
      if (!p && !r) throw new Error(`claim without a source: ${text}`);
      if (p) ctx.quotePaper(p[1], p[0]);
      if (r) ctx.quote(r[1], r[0]);
      return text;
    },
    summary: () => ({ checks, paperChecks, problems }),
  };
  return ctx;
}

/** CSV text with a header row → array of objects (no quoted fields). */
export function csv(text) {
  const [head, ...rows] = text.trim().split("\n").map((l) => l.split(","));
  return rows.map((r) => Object.fromEntries(head.map((k, i) => [k, r[i]])));
}

/** Geometric mean. */
export const geomean = (xs) => Math.exp(xs.reduce((s, x) => s + Math.log(x), 0) / xs.length);
