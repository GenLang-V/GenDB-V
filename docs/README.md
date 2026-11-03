# GenDB-V website

A static site (HTML, CSS, JavaScript modules; no framework, fonts and icons included). GitHub Pages serves it from `docs/`. The build writes the data the pages load and checks every number and sentence against this repository's results, README and guide and, when given, the paper's sources.

```sh
node docs/build/build.mjs [--paper PATH]   # writes docs/data/ (--page ID: one page); fails, writing nothing, on any failed check
node docs/serve.mjs --port 8794            # serves docs/ at http://localhost:8794/
PAPER=PATH docs/checks/run.sh              # the build twice, planted errors, browser checks with screenshots
```

The browser checks need `playwright-core` (`npm install` in `docs/`) and a Chromium for it (`npx playwright-core install chromium`). `node docs/build/hero.mjs --from DIR` copies the mascot picture into `assets/`.

## Pages

Each page has one line in `js/pages.js` and four files of its own:

| File | Role |
|---|---|
| `js/pages/<id>.js` | `export default function render({ data, path, params, page })` returns the page element (may be async). `path`: the address parts after `#/<id>/`; `params`: its `?` query. Optional: `el.shown()` runs once the page is on screen; `el.reroute(path, params)` returning `true` updates the page in place. |
| `css/pages/<id>.css` | The page's styles, every rule under `.page-<id>`. |
| `build/pages/<id>.mjs` | `export default function build(ctx)` returns the page's data; `ctx.claim`, `ctx.quote`, `ctx.check` check it (`build/lib.mjs`). |
| `data/<id>.json` | Written by the build. |

Shared, used by every page and changed by none: `index.html`, `js/app.js` (top bar, footer, router, theme), `js/lib.js` (`h`, `s`, `icon`, `math`, `json`), `js/links.js` (the paper, repository and contact links, in one place; an empty one shows as `#` and the build warns), `css/tokens.css`, `css/base.css`, `assets/`.

## Files

| Path | Content |
|---|---|
| `assets/` | The mascot picture, the icon sprite (Lucide and the GitHub mark), the fonts (Inter, Geist Mono, STIX Two), with their licenses |
| `build/` | The build (`build.mjs`, `lib.mjs`, one builder per page) and `hero.mjs` |
| `checks/` | `run.sh`, `negbuild.mjs` (planted errors), `pages.mjs` (browser) |
| `serve.mjs` | A static server for `docs/` |
