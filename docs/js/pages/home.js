// Home: the title and the picture; two story rows, each a problem and GenDB-V's answer (speedups; the verified
// guarantees); links to the other pages; a call to get in touch (links: js/links.js). Text and numbers:
// data/home.json (build/pages/home.mjs).
import { h, icon, math } from "../lib.js";
import { PAGES } from "../pages.js";
import { LINKS, linkAttrs } from "../links.js";

/** The picture (copied by build/hero.mjs). */
const HERO = "assets/hero-s.svg";

const GUARANTEE_ICONS = { memory: "memory-stick", arithmetic: "binary", races: "split", termination: "flag" };
const PAGE_ICONS = { design: "layers", sqlspec: "square-function", example: "play", performance: "gauge" };

/** A story row: the problem, a turn arrow, GenDB-V's answer and its evidence. */
function row(id, problemIcon, problem, answerIcon, answer, evidence) {
  return h(`article.row.row--${id}`,
    h("div.row__problem", h("span.row__icon", icon(problemIcon)), h("p", problem)),
    h("div.row__turn", { "aria-hidden": "true" }, icon("arrow-right")),
    h("div.row__answer", h("span.row__icon.row__icon--yes", icon(answerIcon)), claim(answer), evidence));
}

/** "GenDB-V does x" with the name set apart. */
function claim(text) {
  const m = /^GenDB-V (.*)$/.exec(text);
  return h("p.row__claim", m ? [h("strong", "GenDB-V"), " ", m[1]] : text);
}

function speedTable(speed) {
  const grid = h("div.speed", { role: "table", "aria-label": "Speedup over DuckDB and Umbra" },
    h("div.speed__row.speed__head", { role: "row" }, h("span", { role: "columnheader" }),
      speed.baselines.map((b) => h("span.speed__base", { role: "columnheader" }, h("span.speed__vs", "vs"), b))),
    speed.workloads.map((w) => h("div.speed__row", { role: "row" },
      h("span.speed__wl", { role: "rowheader" }, w.name),
      w.speedups.map((s) => h("span.speed__num", { role: "cell" }, s.text, h("span.speed__x", "×"))))));
  return h("figure.speedfig", grid);
}

function guarantees(list) {
  return h("ul.gs", list.map((g) => h(`li.g.g--${g.id}`,
    h("span.g__icon", g.id === "correctness" ? math("∈") : icon(GUARANTEE_ICONS[g.id])),
    h("span.g__label", g.label))));
}

/** The tagline with its two key words in the title's colours: "AI-generated" as "Gen", "formally verified" as "-V". */
function tagline(text) {
  return text.split(/(AI-generated|formally verified)/).map((part) =>
    part === "AI-generated" ? h("span.hero__gen", part) : part === "formally verified" ? h("span.hero__ver", part) : part);
}

/** The closing call: contact, the paper, the repository; the address shows once it is set. */
function contact() {
  return h("section.wrap.cta", { "aria-labelledby": "cta-title" },
    h("div.cta__in",
      h("h2#cta-title", "Need a fast and correct engine for your workload?"),
      h("p.cta__line", "Let us know."),
      h("div.cta__buttons",
        h("a.btn.btn--primary", linkAttrs("email"), icon("mail"), "Contact us"),
        h("a.btn", linkAttrs("paper"), icon("file-text"), "Read the paper"),
        h("a.btn", linkAttrs("github"), icon("github"), "GitHub")),
      LINKS.email ? h("p.cta__mail", LINKS.email) : null));
}

export default function render({ data }) {
  const { speed, correctness } = data;
  return h("div",
    h("section.hero",
      h("div.wrap.hero__text",
        h("h1.hero__title", h("span.hero__gen", "Gen"), "DB", h("span.hero__v", "-V")),
        h("p.hero__line", tagline(data.tagline))),
      h("div.wrap.hero__art",
        h("img", { src: HERO, width: "1760", height: "700", alt: "The GenDB cockroach takes a bite out of a database. The mascots of other database systems lie fallen around it.", fetchpriority: "high", decoding: "async" }))),
    h("section.wrap.story", { "aria-label": "Why GenDB-V" },
      row("speed", "refresh-ccw", speed.problem, "zap", speed.answer, speedTable(speed)),
      row("correct", "bug", correctness.problem, "shield-check", correctness.answer, guarantees(correctness.guarantees))),
    h("nav.wrap.more", { "aria-label": "Pages" },
      PAGES.filter((p) => p.id !== "home").map((p) => h("a.more__card", { href: `#/${p.id}` },
        h("span.more__icon", icon(PAGE_ICONS[p.id] || "arrow-up-right")),
        h("span.more__label", p.label),
        icon("arrow-right", { cls: "more__go" })))),
    contact());
}
