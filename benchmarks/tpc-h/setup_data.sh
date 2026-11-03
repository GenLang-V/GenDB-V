#!/usr/bin/env bash
#
# Make the TPC-H data of one scale: dbgen .tbl text, then one Parquet file per table (the input GenDB reads).
#
# Usage:
#   bash benchmarks/tpc-h/setup_data.sh SCALE      (SCALE: sf1, sf10, sf100, ...; a bare number N means sfN)
#
# `gendb run benchmarks/tpc-h --scale SCALE` runs it when data/SCALE/ is missing.
# Needs git, make, a C compiler, cargo (Rust 1.88 or later) and python3.
# Writes raw/SCALE/<table>.tbl (the dbgen text) and data/SCALE/ (<table>.parquet and MANIFEST.json, with
# `original_data_bytes`: the size of the text, which GenDB takes as the default storage budget).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SCALE="${1:-sf1}"
[[ "${SCALE}" =~ ^[0-9]+$ ]] && SCALE="sf${SCALE}"
SCALE_FACTOR="${SCALE#sf}"
[[ "${SCALE}" =~ ^sf[0-9]+$ ]] || { echo "SCALE must be sf<N>, for example sf1" >&2; exit 1; }
RAW_DIR="${SCRIPT_DIR}/raw/${SCALE}"
DATA_DIR="${SCRIPT_DIR}/data/${SCALE}"
DBGEN_DIR="${SCRIPT_DIR}/tpch-dbgen"

echo "=== TPC-H Data Setup ==="
echo "Scale factor: ${SCALE_FACTOR}"
echo "Text: ${RAW_DIR}"
echo "Parquet: ${DATA_DIR}"

# Step 1: Clone dbgen if not already present
if [ ! -d "${DBGEN_DIR}" ]; then
    echo "Cloning tpch-dbgen..."
    git clone https://github.com/electrum/tpch-dbgen.git "${DBGEN_DIR}"
else
    echo "tpch-dbgen already cloned."
fi

# Step 2: Build dbgen
echo "Building dbgen..."
cd "${DBGEN_DIR}"
make clean || true
make
echo "dbgen built successfully."

# Step 3: Generate the text
echo "Generating TPC-H data at scale factor ${SCALE_FACTOR}..."
./dbgen -s "${SCALE_FACTOR}" -f
mkdir -p "${RAW_DIR}"
chmod 644 *.tbl 2>/dev/null || true
mv -f *.tbl "${RAW_DIR}/"
echo "Data generated."

# Step 4: Convert to Parquet with tbl-to-parquet, which checks every value back against the text and stops on any
# mismatch
echo "Converting to Parquet..."
cargo run --release --manifest-path "${SCRIPT_DIR}/tbl-to-parquet/Cargo.toml" --bin materialize -- \
    --scale "${SCALE}" --input "${RAW_DIR}" --output "${DATA_DIR}"

# Step 5: Record the original data size (the sum of the tables' text bytes) in MANIFEST.json
python3 - "${DATA_DIR}/MANIFEST.json" <<'EOF'
import json, sys

path = sys.argv[1]
manifest = json.load(open(path))
manifest["original_data_bytes"] = sum(table["source_bytes"] for table in manifest["tables"])
with open(path, "w") as f:
    json.dump(manifest, f, indent=2)
    f.write("\n")
print("original_data_bytes", manifest["original_data_bytes"])
EOF

echo ""
echo "=== TPC-H data ready ==="
echo "Files in ${DATA_DIR} (rows per table in MANIFEST.json):"
ls -lh "${DATA_DIR}"
