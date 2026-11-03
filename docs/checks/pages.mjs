// Browser checks of the served site: node docs/checks/pages.mjs [OUT]   (SITE_URL, default http://localhost:8794/)
// Every page of the registry, and an unknown address, at 1440 and 390 px, light and dark: no page errors, no console
// errors, no failed requests, no sideways scroll, no content cut off (a box that scrolls sideways must be code or
// marked data-scroll), the top bar within its width with its 2 outside links, the footer's 4 links, the page's
// element on screen, every image loaded. The home page's numbers and words on screen must be those of data/home.json.
// Screenshots of every page go to OUT (default docs/checks/out). Ends with one
// PASS/FAIL line; the exit status is the result.
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { chromium } from "playwright-core";
import { PAGES } from "../js/pages.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const site = path.resolve(here, "..");
const URL0 = (process.env.SITE_URL || "http://localhost:8794/").replace(/\/?$/, "/");
const out = path.resolve(process.argv[2] || path.join(here, "out"));
fs.mkdirSync(out, { recursive: true });

const routes = [...PAGES.map((p) => [p.id, p.id === "home" ? "#/" : `#/${p.id}`]), ["home", "#/no-such-page"]];
const problems = [];
let shots = 0;

/** The home page's text on screen against data/home.json. */
async function homeAgainstData(p, where) {
  const data = JSON.parse(fs.readFileSync(path.join(site, "data/home.json"), "utf8"));
  const shown = await p.evaluate(() => ({
    nums: [...document.querySelectorAll(".speed__num")].map((e) => e.textContent),
    wls: [...document.querySelectorAll(".speed__wl")].map((e) => e.textContent),
    bases: [...document.querySelectorAll(".speed__base")].map((e) => e.textContent),
    guarantees: [...document.querySelectorAll(".g__label")].map((e) => e.textContent),
    text: document.querySelector("main").innerText.replace(/\s+/g, " "),
  }));
  const want = data.speed.workloads.flatMap((w) => w.speedups.map((s) => `${s.text}×`));
  if (shown.nums.join() !== want.join()) problems.push(`${where}: speedups shown ${shown.nums.join(" ")}, data ${want.join(" ")}`);
  if (shown.wls.join() !== data.speed.workloads.map((w) => w.name).join()) problems.push(`${where}: workloads shown ${shown.wls.join()}`);
  if (shown.bases.join() !== data.speed.baselines.map((b) => `vs${b}`).join()) problems.push(`${where}: baselines shown ${shown.bases.join()}`);
  if (shown.guarantees.join() !== data.correctness.guarantees.map((g) => g.label).join()) problems.push(`${where}: guarantees shown ${shown.guarantees.join()}`);
  const flat = (t) => t.replace(/\s+/g, " ");
  for (const t of [data.tagline, data.speed.problem, data.speed.answer, data.correctness.problem, data.correctness.answer]) {
    if (!shown.text.includes(flat(t))) problems.push(`${where}: "${t}" is not on the page`);
  }
  // no number on the page that is not one of the data's
  const extra = (shown.text.match(/\d+(\.\d+)?×/g) || []).filter((n) => !want.includes(n));
  if (extra.length) problems.push(`${where}: numbers not in the data: ${extra.join(" ")}`);
}

const browser = await chromium.launch();
for (const theme of ["light", "dark"]) for (const w of [1440, 390]) {
  const ctx = await browser.newContext({ viewport: { width: w, height: w < 600 ? 844 : 900 }, deviceScaleFactor: 1, colorScheme: theme });
  const p = await ctx.newPage();
  let where = "";
  p.on("pageerror", (e) => problems.push(`${where}: page error ${e.message}`));
  p.on("console", (m) => { if (m.type() === "error") problems.push(`${where}: console ${m.text()}`); });
  p.on("requestfailed", (r) => problems.push(`${where}: request failed ${r.url()}`));
  p.on("response", (r) => { if (r.status() >= 400) problems.push(`${where}: HTTP ${r.status()} ${r.url()}`); });
  for (const [id, route] of routes) {
    where = `${route} ${w}px ${theme}`;
    await p.goto(URL0 + route, { waitUntil: "networkidle" });
    await p.evaluate(() => document.fonts.ready);
    await p.waitForSelector(`main > .page-${id}`, { timeout: 10000 }).catch(() => problems.push(`${where}: .page-${id} not shown`));
    await p.waitForTimeout(900);   // the home picture's rise
    const m = await p.evaluate(() => ({
      sw: document.documentElement.scrollWidth,
      images: [...document.images].filter((i) => !i.complete || i.naturalWidth === 0).map((i) => i.src),
      titled: document.querySelectorAll("main [title]").length,
      bar: (() => { const b = document.querySelector(".bar__in"); return b.scrollWidth - b.clientWidth; })(),
      links: [document.querySelectorAll(".ext a").length, document.querySelectorAll(".foot a").length],
      // content cut off: a box narrower than its content, unless it is meant to scroll (code, or data-scroll)
      clipped: [...document.querySelectorAll("main *")].filter((e) => {
        if (e.closest("pre, .code, [data-scroll]") || e.scrollWidth <= e.clientWidth + 1) return false;
        const o = getComputedStyle(e).overflowX;
        return o === "auto" || o === "scroll" || o === "hidden" || o === "clip";
      }).map((e) => `${e.tagName.toLowerCase()}.${[...e.classList].join(".")} (${e.scrollWidth} > ${e.clientWidth})`),
    }));
    if (m.sw > w) problems.push(`${where}: sideways scroll (${m.sw} px wide)`);
    if (m.images.length) problems.push(`${where}: images not loaded: ${m.images.join(", ")}`);
    if (m.titled) problems.push(`${where}: ${m.titled} elements with a title attribute`);
    if (m.bar > 0) problems.push(`${where}: the top bar is ${m.bar} px too wide`);
    if (m.links.join() !== "2,4") problems.push(`${where}: ${m.links[0]} links in the top bar (want 2), ${m.links[1]} in the footer (want 4)`);
    if (m.clipped.length) problems.push(`${where}: content cut off in ${m.clipped.slice(0, 4).join(", ")}`);
    if (id === "home" && route === "#/") await homeAgainstData(p, where);
    if (route !== "#/no-such-page") {
      await p.screenshot({ path: path.join(out, `${id}_${w}_${theme}.png`), fullPage: true });
      shots++;
    }
  }
  await ctx.close();
}
await browser.close();

if (problems.length) console.log(`${problems.length} problems:\n  ${problems.slice(0, 60).join("\n  ")}`);
console.log(`${problems.length ? "FAIL" : "PASS"} pages: ${routes.length} addresses × 1440 / 390 px × light / dark; ${shots} screenshots in ${out}`);
process.exitCode = problems.length ? 1 : 0;
