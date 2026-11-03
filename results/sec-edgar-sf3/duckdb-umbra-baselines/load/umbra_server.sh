#!/usr/bin/env bash
# Start the read-only Umbra server of the canonical SEC-EDGAR SF3 store with the TPC-H baseline server settings
# (results/tpch-sf100/duckdb-umbra-baselines/load/umbra_server.sh): same image, 144g memory, cpuset 0-63,
# COMPILATIONMODE=o, host network bound to 127.0.0.1, -readonly. Container gendb-umbra-sec on port 5575.
# Usage: umbra_server.sh   (prints the container id; stop with: docker stop gendb-umbra-sec && docker rm gendb-umbra-sec)
set -euo pipefail
IMAGE=sha256:4ef513ffa6018bd9e48adf48d681ac37af9bc266af9879b707d8018f5d760425
PORT=5575
D=/path/to/baseline-store/sec-edgar-sf3/umbra
mkdir -p "$D/task/scratch" "$D/task/sockets"
docker run --detach --name gendb-umbra-sec --pull=never --network=host --cpuset-cpus=0-63 \
  --memory=144g --memory-swap=144g --read-only --security-opt=seccomp=unconfined --ulimit=memlock=-1:-1 \
  --user "$(id -u):$(id -g)" --log-driver=json-file \
  --mount type=bind,source="$D/db",target=/var/db --mount type=bind,source="$D/task",target=/task \
  --workdir=/task --env TMPDIR=/task/scratch --env COMPILATIONMODE=o "$IMAGE" \
  /usr/local/bin/umbra-server -readonly -createSSLFiles -address=127.0.0.1 -port=$PORT -pgSocketDir=/task/sockets \
  -certFile=/task/umbra.cert -keyFile=/task/umbra.pem /var/db/umbra.db
