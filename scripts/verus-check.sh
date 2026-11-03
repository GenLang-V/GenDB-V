#!/usr/bin/env bash
# Re-check one published GenDB-V crate with the pinned Verus release: the whole crate, --no-cheating (verification
# only, no code generation).
#
# usage: GENDB_VERUS_HOME=<toolchain directory> scripts/verus-check.sh CRATE_DIR
#   CRATE_DIR: any published query or storage crate under results/**/crates/, e.g.
#   results/example-readings-count/crates/example-readings-count or results/tpch-sf100/<run>/crates/queries/q06
# The toolchain directory layout is pinned in src/gendb/verification/verus/toolchain.json.
set -euo pipefail
crate=$(cd "${1:?usage: scripts/verus-check.sh CRATE_DIR}" && pwd)
home=${GENDB_VERUS_HOME:?set GENDB_VERUS_HOME to the pinned toolchain directory}
rust_verify=$home/verus/0.2026.09.13.671956e/verus-x86-linux/rust_verify
rust_lib=$home/rustup/toolchains/1.98.1-x86_64-unknown-linux-gnu/lib
z3=$home/z3/4.16.0-manylinux_2_27/z3_solver-4.16.0.0.data/data/bin/z3
if [ -d "$crate/src/agent" ]; then name=gendb_query; else name=gendb_store; fi
exec env -i PATH=/usr/local/bin:/usr/bin:/bin LD_LIBRARY_PATH="$rust_lib" VSTD_KIND=Imported VERUS_Z3_PATH="$z3" \
  TMPDIR="${TMPDIR:-/tmp}" "$rust_verify" "$crate/src/lib.rs" --edition=2021 --crate-type=cdylib --crate-name="$name" \
  --no-cheating --num-threads 8
