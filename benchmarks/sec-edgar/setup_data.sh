#!/usr/bin/env bash
#
# Setup SEC-EDGAR benchmark data: download the SEC Financial Statement Data Sets 2022q1-2024q4 (12 quarters) and
# write the canonical Parquet files with make_canonical.py.
#
# Usage:
#   bash benchmarks/sec-edgar/setup_data.sh [sf3]      (the one scale; `gendb run` runs it when data/sf3/ is missing)
#
# Needs curl, unzip and Python 3 with pyarrow (the published data was written with pyarrow 20.0.0).
# Raw text is written to benchmarks/sec-edgar/raw/<quarter>/ (about 7.1 GB),
# the canonical data to benchmarks/sec-edgar/data/sf3/ (about 1.05 GB: one Parquet file per table, MANIFEST.json with
# `original_data_bytes`, and the cleaning record generation.json).
# Environment: PYTHON (default python3); SEC_USER_AGENT, the User-Agent header sent to sec.gov.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[ "${1:-sf3}" = "sf3" ] || { echo "the one scale is sf3" >&2; exit 1; }
DATA_DIR="${SCRIPT_DIR}/raw"
OUT_DIR="${SCRIPT_DIR}/data/sf3"
PYTHON="${PYTHON:-python3}"
USER_AGENT="${SEC_USER_AGENT:-Mozilla/5.0 (X11; Linux x86_64)}"
BASE_URL="https://www.sec.gov/files/dera/data/financial-statement-data-sets"

echo "=== SEC-EDGAR Data Setup ==="
echo "Quarters: 2022q1-2024q4"
echo "Raw text: ${DATA_DIR}"

mkdir -p "${DATA_DIR}"

# Step 1: Download and extract the 12 quarters (each needs sub, num, tag and pre)
for year in 2022 2023 2024; do
    for quarter in 1 2 3 4; do
        tag="${year}q${quarter}"
        zip_file="${DATA_DIR}/${tag}.zip"
        extract_dir="${DATA_DIR}/${tag}"

        if [ -f "${extract_dir}/sub.txt" ] && [ -f "${extract_dir}/num.txt" ] \
           && [ -f "${extract_dir}/tag.txt" ] && [ -f "${extract_dir}/pre.txt" ]; then
            echo "  ${tag}: already extracted, skipping download."
            continue
        fi

        url="${BASE_URL}/${tag}.zip"
        echo "  Downloading ${tag}.zip..."
        if ! curl -fSL --retry 3 --retry-delay 5 \
             -H "User-Agent: ${USER_AGENT}" \
             -H "Accept-Encoding: gzip" \
             -o "${zip_file}" "${url}"; then
            rm -f "${zip_file}"
            echo "ERROR: failed to download ${url}; all 12 quarters are needed." >&2
            echo "sec.gov may refuse a request without a declared User-Agent: set SEC_USER_AGENT to 'Name email'." >&2
            exit 1
        fi

        echo "  Extracting ${tag}.zip..."
        mkdir -p "${extract_dir}"
        unzip -o -q "${zip_file}" -d "${extract_dir}"
        rm -f "${zip_file}"
    done
done

# Step 2: Write the canonical Parquet files (make_canonical.py refuses existing outputs)
if [ -f "${OUT_DIR}/MANIFEST.json" ]; then
    echo "Canonical data already written (remove ${OUT_DIR} to write it again)."
else
    "${PYTHON}" -c 'import pyarrow; print("pyarrow", pyarrow.__version__)'
    "${PYTHON}" "${SCRIPT_DIR}/make_canonical.py" "${DATA_DIR}" "${OUT_DIR}" "${OUT_DIR}/generation.json"
fi

# Step 3: Compare with the published manifest: rows and schema must be equal; bytes depend on the pyarrow version
echo ""
echo "=== SEC-EDGAR data ready ==="
echo "Files in ${OUT_DIR}:"
ls -lh "${OUT_DIR}"
echo ""
echo "Compared with ${SCRIPT_DIR}/MANIFEST.json:"
"${PYTHON}" - "${SCRIPT_DIR}/MANIFEST.json" "${OUT_DIR}/MANIFEST.json" <<'EOF'
import json, sys

published, written = (json.load(open(path))['tables'] for path in sys.argv[1:3])
differ = sorted(set(published) ^ set(written))
for table, want in published.items():
    got = written.get(table)
    if got is None:
        continue
    if (got['rows'], got['arrow_schema']) != (want['rows'], want['arrow_schema']):
        differ.append(table)
        print(f"  {table}: {got['rows']:,} rows, published {want['rows']:,}; schema equal: "
              f"{got['arrow_schema'] == want['arrow_schema']}")
        continue
    writer = [k for k in ('row_groups', 'bytes', 'created_by') if got[k] != want[k]]
    print(f"  {table}: {got['rows']:,} rows and schema equal; "
          + (f"differ: {', '.join(f'{k} {got[k]} (published {want[k]})' for k in writer)}" if writer
             else 'row groups, bytes and writer equal'))
if differ:
    sys.exit(f"Differs from the published data: {', '.join(differ)}")
# Equal rows and schema: the data is the published data, so its size as '|' text is the published one
manifest = json.load(open(sys.argv[2]))
manifest['original_data_bytes'] = json.load(open(sys.argv[1]))['original_data_bytes']
with open(sys.argv[2], 'w') as f:
    json.dump(manifest, f, indent=1)
    f.write('\n')
print(f"  original_data_bytes {manifest['original_data_bytes']:,}")
EOF
