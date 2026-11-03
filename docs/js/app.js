// The site shell: the top bar, the theme switch and the hash router. #/<id>/<path...>?<params> shows page <id> of the
// registry (js/pages.js; home at #/). A page module's default export render({ data, path, params, page }) returns the
// page element; the router adds the classes `page page-<id>`, loads css/pages/<id>.css and data/<id>.json first, and
// calls el.shown() once the element is on screen. When only the path or params change and the page on screen has
// el.reroute(path, params) returning true, the page updates itself and is not rendered again.
import { PAGES } from "./pages.js";
import { LINKS, linkAttrs } from "./links.js";
import { h, icon, json } from "./lib.js";

const app = document.getElementById("app");
const byId = new Map(PAGES.map((p) => [p.id, p]));
const styles = new Map();
let token = 0;

function parse() {
  const raw = location.hash.replace(/^#\/?/, "");
  const [pathPart, query = ""] = raw.split("?");
  const parts = pathPart.split("/").filter(Boolean).map(decodeURIComponent);
  const page = byId.get(parts[0]) || byId.get("home");
  return { page, path: page.id === parts[0] ? parts.slice(1) : [], params: new URLSearchParams(query) };
}

/** css/pages/<id>.css, once; resolves when the sheet has loaded (a missing sheet is no error). */
function style(id) {
  if (!styles.has(id)) {
    styles.set(id, new Promise((done) => {
      const link = h("link", { rel: "stylesheet", href: `css/pages/${id}.css` });
      link.addEventListener("load", done);
      link.addEventListener("error", done);
      document.head.append(link);
    }));
  }
  return styles.get(id);
}

function soon(page) {
  return h("div.wrap.page-soon", h("div.page-head", h("h1", page.label)), h("span.chip", icon("timer"), "Coming soon"));
}

async function render() {
  const { page, path, params } = parse();
  for (const a of document.querySelectorAll(".nav a")) {
    if (a.dataset.page === page.id) a.setAttribute("aria-current", "page");
    else a.removeAttribute("aria-current");
  }
  const onScreen = app.firstElementChild;
  if (onScreen && onScreen.dataset.page === page.id && onScreen.reroute && onScreen.reroute(path, params)) return;
  const my = ++token;
  try {
    let el;
    if (page.soon) el = soon(page);
    else {
      const [mod, data] = await Promise.all([import(`./pages/${page.id}.js`), json(`data/${page.id}.json`), style(page.id)]);
      el = await mod.default({ data, path, params, page });
    }
    if (my !== token) return;
    el.classList.add("page", `page-${page.id}`);
    el.dataset.page = page.id;
    app.replaceChildren(el);
    document.body.dataset.page = page.id;
    document.title = page.id === "home" ? "GenDB-V" : `${page.label} · GenDB-V`;
    window.scrollTo(0, 0);
    app.focus({ preventScroll: true });
    if (el.shown) el.shown();
  } catch (e) {
    console.error(e);
    if (my === token) app.replaceChildren(h("div.wrap.failed", h("p", "This page could not be shown."), h("p", h("a.go", { href: "#/" }, "Home", icon("arrow-right")))));
  }
}

function bar() {
  const nav = document.querySelector(".nav");
  for (const p of PAGES) {
    if (p.id === "home") { nav.append(h("a", { href: "#/", "data-page": p.id }, "Home")); continue; }
    nav.append(h("a", { href: `#/${p.id}`, "data-page": p.id }, p.short ? [h("span.full", p.label), h("span.short", p.short)] : p.label));
  }
  // the paper and the repository, before the theme switch (icons only on phones)
  document.querySelector(".ext").append(
    h("a.ext__link", { ...linkAttrs("paper"), "aria-label": "Paper" }, icon("file-text"), h("span.ext__label", "Paper")),
    h("a.ext__link", { ...linkAttrs("github"), "aria-label": "GitHub" }, icon("github")));
  // the footer of every page
  document.querySelector(".foot").append(h("div.wrap.foot__in",
    h("span.foot__name", "GenDB-V"),
    h("nav.foot__links", { "aria-label": "Links" },
      h("a", linkAttrs("paper"), "Paper"),
      h("a", linkAttrs("github"), "GitHub"),
      h("a", linkAttrs("email"), LINKS.email || "Contact"),
      h("a", linkAttrs("license"), "License"))));
  // links not set yet do nothing
  document.addEventListener("click", (e) => { if (e.target.closest?.("a[data-unset]")) e.preventDefault(); });
  document.querySelector(".theme").addEventListener("click", () => {
    const root = document.documentElement;
    const dark = root.dataset.theme ? root.dataset.theme === "dark" : matchMedia("(prefers-color-scheme: dark)").matches;
    root.dataset.theme = dark ? "light" : "dark";
    try { localStorage.setItem("gendbv-theme", root.dataset.theme); } catch { /* no storage */ }
  });
}

bar();
window.addEventListener("hashchange", render);
render();
