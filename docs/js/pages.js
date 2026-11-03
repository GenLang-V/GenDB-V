// The page registry: one line per page. The router, the build and the checks read it.
// Page `id` is served at #/id (home at #/) from js/pages/<id>.js, css/pages/<id>.css and data/<id>.json, the data
// written by build/pages/<id>.mjs (README.md: "Pages"). `short`: the top-bar label on phones. `soon`: not built yet,
// the router shows a placeholder and the build skips it; remove the flag when the page's files are in place.
export const PAGES = [
  { id: "home", label: "GenDB-V" },
  { id: "design", label: "Design" },
  { id: "sqlspec", label: "SQLSpec" },
  { id: "example", label: "Example" },
  { id: "performance", label: "Performance", short: "Perf" },
];
