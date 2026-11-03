#!/bin/bash
# GenDB direct Verus run: a diagnostic, never a submission or the official check.
#
# Usage: direct-verus.sh query|storage CRATE_DIR [rust_verify options]
#   e.g. direct-verus.sh query verus --verify-only-module agent::sort --verify-function lemma_sorted
#
# Runs the pinned rust_verify on CRATE_DIR/src/lib.rs with the framework's environment and arguments for that crate
# kind (human-readable diagnostics instead of JSON), from the directory holding this script. It stays in the
# foreground until rust_verify exits, passes through everything rust_verify prints, then prints one line
# `direct-verus: rust_verify exit status N` and exits with N. Every failure (refused options, a parse or type error,
# a verification error, a crash) returns as soon as rust_verify exits.
#
# rust_verify runs in its own process group, recorded in direct-verus-<group>.pgid next to this script while it
# runs: `kill -TERM -- -<group>` stops it with its solver children. A TERM, INT or HUP sent to this script (for
# example by `timeout`) stops that group too before the script exits.
set -u
run_dir=@RUN_DIR@

usage() {
    echo "usage: $0 query|storage CRATE_DIR [rust_verify options]" >&2
    exit 2
}
[ $# -ge 2 ] || usage
case $1 in
    query) options=(@QUERY_OPTIONS@) ;;
    storage) options=(@STORAGE_OPTIONS@) ;;
    *) usage ;;
esac
crate_dir=$(cd -- "$2" 2>/dev/null && pwd) || { echo "direct-verus: no crate directory $2" >&2; exit 2; }
crate_root=$crate_dir/src/lib.rs
[ -f "$crate_root" ] || { echo "direct-verus: $crate_root does not exist" >&2; exit 2; }
shift 2
cd -- "$run_dir" || exit 2

# The trap is set before rust_verify starts, so a stop request is never lost; it signals the group and, in case
# setsid has not run yet, the process itself.
group='' stop=''
stop_verifier() { [ -n "$group" ] && kill -TERM -- "-$group" "$group" 2>/dev/null; }
trap 'stop=1; stop_verifier' TERM INT HUP
setsid env -i @ENVIRONMENT@ @RUST_VERIFY@ "$crate_root" "${options[@]}" "$@" &
group=$!
[ -z "$stop" ] || stop_verifier
record=$run_dir/direct-verus-$group.pgid
echo "$group" > "$record"
# `wait` also returns when a trapped signal arrives; wait again until rust_verify itself has exited.
while :; do
    wait "$group"
    status=$?
    kill -0 "$group" 2>/dev/null || break
done
rm -f -- "$record"
echo "direct-verus: rust_verify exit status $status"
exit "$status"
