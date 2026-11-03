#!/bin/sh
# All checks of the site: docs/checks/run.sh [OUT]
#  1. the build, twice: it passes and gives byte-identical data (PAPER=<the paper's source folder> adds its checks);
#  2. negbuild.mjs: planted errors the build must catch;
#  3. pages.mjs: the served site in a browser (SITE_URL, default http://localhost:8794/; node docs/serve.mjs),
#     with screenshots in OUT (default docs/checks/out).
# Prints one line per step; the exit status is 0 when all passed.
HERE=$(cd "$(dirname "$0")" && pwd)
SITE=$(dirname "$HERE")
OUT=${1:-$HERE/out}
PAPER_ARG=""
[ -n "${PAPER:-}" ] && PAPER_ARG="--paper $PAPER"
failed=0

datasum() { cat "$SITE"/data/*.json | sha1sum | cut -c1-12; }
if node "$SITE/build/build.mjs" $PAPER_ARG && a=$(datasum) && node "$SITE/build/build.mjs" $PAPER_ARG && [ "$a" = "$(datasum)" ]; then
  echo "PASS build: two builds, byte-identical data ($a)"
else
  echo "FAIL build"; failed=1
fi
node "$HERE/negbuild.mjs" | tail -1 | grep -q '^PASS' && echo "PASS negbuild" || { echo "FAIL negbuild (run node docs/checks/negbuild.mjs)"; failed=1; }
node "$HERE/pages.mjs" "$OUT" | tail -1 | grep -q '^PASS' && echo "PASS pages (screenshots in $OUT)" || { echo "FAIL pages (run node docs/checks/pages.mjs)"; failed=1; }
exit $failed
