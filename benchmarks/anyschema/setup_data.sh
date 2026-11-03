#!/usr/bin/env bash
#
# Make the data of the workload anyschema: data/tiny/<table>.parquet and data/tiny/MANIFEST.json (generate.py).
#
# Usage:
#   bash benchmarks/anyschema/setup_data.sh [tiny]      (the one scale; `gendb run` runs it when data/tiny/ is missing)
#
# Needs Python 3 with pyarrow.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[ "${1:-tiny}" = "tiny" ] || { echo "the one scale is tiny" >&2; exit 1; }
python3 "${SCRIPT_DIR}/generate.py" "${SCRIPT_DIR}/data/tiny"
