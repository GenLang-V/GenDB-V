#!/usr/bin/env bash
# Start the read-only Umbra baseline server: 144g, cpuset 0-63, COMPILATIONMODE=o, host network bound to 127.0.0.1,
# -readonly. Prints the container id.
set -euo pipefail
IMAGE=sha256:4ef513ffa6018bd9e48adf48d681ac37af9bc266af9879b707d8018f5d760425
D=/path/to/baseline-store/umbra
PORT=5552
mkdir -p "$D/task/scratch" "$D/task/sockets"
docker run --detach --name gendb-b-umbra-o --pull=never --network=host --cpuset-cpus=0-63 \
  --memory=144g --memory-swap=144g --read-only --security-opt=seccomp=unconfined --ulimit=memlock=-1:-1 \
  --user "$(id -u):$(id -g)" --log-driver=json-file \
  --mount type=bind,source="$D/db",target=/var/db --mount type=bind,source="$D/task",target=/task \
  --workdir=/task --env TMPDIR=/task/scratch --env COMPILATIONMODE=o "$IMAGE" \
  /usr/local/bin/umbra-server -readonly -createSSLFiles -address=127.0.0.1 -port=$PORT -pgSocketDir=/task/sockets \
  -certFile=/task/umbra.cert -keyFile=/task/umbra.pem /var/db/umbra.db
