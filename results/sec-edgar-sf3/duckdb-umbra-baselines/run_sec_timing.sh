#!/usr/bin/env bash
# SEC-EDGAR SF3 baseline timing in the TPC-H baseline protocol: sec_baselines_runner.py (run_sec_baselines.py = the
# TPC-H SF100 run_baselines.py with the SEC-EDGAR parameter types, plus a fresh DuckDB PREPARE before every execution,
# outside the timed interval), then the TPC-H aggregate.py, which writes times.json. Every template x binding, threads
# 1/32/64, DuckDB then Umbra per block, 1 warm + 3 hot, median hot. Existing blocks are skipped. Needs the read-only
# Umbra server gendb-umbra-sec (load/umbra_server.sh) running.
# Usage: run_sec_timing.sh <benchmarks/sec-edgar> <bindings.json> <out_dir> [run_baselines options, e.g. --queries Q1,Q2]
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
templates=$(readlink -f "$1"); bindings=$(readlink -f "$2"); out=$3; shift 3
sf100=$here/../../tpch-sf100/duckdb-umbra-baselines
[[ $(docker inspect -f '{{.State.Running}}' gendb-umbra-sec 2>/dev/null) == true ]] || { echo "Umbra server gendb-umbra-sec is not running (load/umbra_server.sh)"; exit 1; }
export DUCKDB_STORE=/path/to/baseline-store/sec-edgar-sf3/duckdb/sec_edgar_sf3.duckdb
export PYTHONPATH=/path/to/pydeps   # the DuckDB Python package and psycopg2
export UMBRA_DSN="host=127.0.0.1 port=5575 dbname=postgres user=postgres password=postgres"
export TIMING_LOCKS=/path/to/locks/activity.lock:/path/to/locks/build.lock:/path/to/locks/race.lock
mkdir -p "$out"
python3 "$here/sec_baselines_runner.py" "$bindings" "$templates" "$out/runs/visible" "$@"
python3 "$sf100/aggregate.py" "$out/runs/visible" "$bindings" "$out/times.json"
