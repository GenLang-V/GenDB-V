#!/usr/bin/env bash
#
# Make the data of the example readings-count: data/tiny/readings.parquet (4 rows).
#
# Usage:
#   bash benchmarks/readings-count/setup_data.sh [tiny]      (the one scale; `gendb run` runs it when data/tiny/ is missing)
#
# Needs Python 3 with pyarrow.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[ "${1:-tiny}" = "tiny" ] || { echo "the one scale is tiny" >&2; exit 1; }
python3 "${SCRIPT_DIR}/make_data.py" "${SCRIPT_DIR}/data/tiny"
