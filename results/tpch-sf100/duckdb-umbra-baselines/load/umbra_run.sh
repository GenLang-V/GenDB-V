#!/usr/bin/env bash
# Run umbra-sql (pinned image) on a SQL file against a db dir. Usage: umbra_run.sh <name> <dbdir> <datadir> <sqlfile> [createdb]
# The SQL file's directory is mounted at /task; data dir read-only at /data; db dir at /var/db.
set -euo pipefail
IMAGE=sha256:4ef513ffa6018bd9e48adf48d681ac37af9bc266af9879b707d8018f5d760425
name=$1 dbdir=$2 data=$3 sql=$4 create=${5:-}
task=$(dirname "$(readlink -f "$sql")")
mkdir -p "$task/scratch"
args=(); [[ "$create" == createdb ]] && args=(-createdb)
exec docker run --rm --name "$name" --pull=never --network=host --cpuset-cpus=0-63 \
  --memory=${UMBRA_MEM:-144g} --memory-swap=${UMBRA_MEM:-144g} ${UMBRA_BUFFERSIZE:+--env BUFFERSIZE=$UMBRA_BUFFERSIZE} --security-opt=seccomp=unconfined --ulimit=memlock=-1:-1 \
  --user "$(id -u):$(id -g)" --mount type=bind,source="$dbdir",target=/var/db \
  --mount type=bind,source="$task",target=/task --mount type=bind,source="$data",target=/data,readonly \
  --workdir=/task --env TMPDIR=/task/scratch --env PARALLEL=64 --env COMPILATIONMODE=o \
  "$IMAGE" /usr/local/bin/umbra-sql "${args[@]}" /var/db/umbra.db "/task/$(basename "$sql")"
