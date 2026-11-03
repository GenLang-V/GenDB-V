#!/usr/bin/env bash
# Load the canonical SEC-EDGAR SF3 data into a fresh Umbra database with the TPC-H baseline route (the TPC-H baselines' load/umbra_run.sh):
# same image, umbra-sql -createdb, the load script umbra-create-load.sql (make_umbra_sql.py:
# primary keys in CREATE TABLE, COPY, then the foreign keys), reading the CSV export of the canonical Parquet
# (export_for_umbra.py) from a read-only /data, COMPILATIONMODE=o. Load-only resources: PARALLEL=8, --cpus=8, 48g
# memory, BUFFERSIZE=24G; the environment variables UMBRA_LOAD_PARALLEL, UMBRA_LOAD_CPUS, UMBRA_LOAD_MEMORY and UMBRA_LOAD_BUFFERSIZE
# override them. The server for queries uses the TPC-H baselines' server settings (umbra_server.sh).
# Usage: umbra_load.sh <export_dir>. Database: $BASE/db/umbra.db.
set -euo pipefail
IMAGE=sha256:4ef513ffa6018bd9e48adf48d681ac37af9bc266af9879b707d8018f5d760425
BASE=/path/to/baseline-store/sec-edgar-sf3/umbra
data=$1
db=$BASE/db task=$BASE/load-task
[[ -e $db/umbra.db ]] && { echo "refused: $db/umbra.db exists"; exit 1; }
mkdir -p "$db" "$task/scratch"
cp "$(dirname "$0")/umbra-create-load.sql" "$task/"
parallel=${UMBRA_LOAD_PARALLEL:-8} cpus=${UMBRA_LOAD_CPUS:-8} memory=${UMBRA_LOAD_MEMORY:-48g} buffer=${UMBRA_LOAD_BUFFERSIZE:-24G}
exec docker run --rm --name gendb-umbra-load-sec --pull=never --network=none --cpuset-cpus=0-63 --cpus=$cpus \
  --memory=$memory --memory-swap=$memory --env BUFFERSIZE=$buffer --security-opt=seccomp=unconfined --ulimit=memlock=-1:-1 \
  --user "$(id -u):$(id -g)" --mount type=bind,source="$db",target=/var/db \
  --mount type=bind,source="$task",target=/task --mount type=bind,source="$data",target=/data,readonly \
  --workdir=/task --env TMPDIR=/task/scratch --env PARALLEL=$parallel --env COMPILATIONMODE=o \
  "$IMAGE" /usr/local/bin/umbra-sql -createdb /var/db/umbra.db /task/umbra-create-load.sql
