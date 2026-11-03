#!/usr/bin/env python3
"""Write the data of the example query (results/example-readings-count/README.md).

Usage: python3 make_data.py OUT_DIR

Writes OUT_DIR/readings.parquet (refuses an existing file): one table `readings` with one column
`value BIGINT NOT NULL` (Arrow int64, nullable=False), holding the rows [[5],[5],[9],[0]] in that order.
The declared constraint CHECK (value >= 0) holds (checked before writing). Writer options are fixed (as
benchmarks/anyschema/generate.py), so the same pyarrow version writes the same bytes.
"""
import os
import sys

import pyarrow as pa
import pyarrow.parquet as pq

ROWS = [5, 5, 9, 0]  # the rows of `readings`, in row order


def main():
    (out_dir,) = sys.argv[1:]
    assert all(v >= 0 for v in ROWS), "CHECK (value >= 0) must hold on the data"
    schema = pa.schema([pa.field("value", pa.int64(), nullable=False)])
    table = pa.Table.from_arrays([pa.array(ROWS, type=pa.int64())], schema=schema)
    path = os.path.join(out_dir, "readings.parquet")
    if os.path.exists(path):
        sys.exit(f"{path} exists")
    pq.write_table(table, path, compression="zstd", version="2.6", write_statistics=True, use_dictionary=True)
    back = pq.read_table(path)
    print(path, back.schema.field("value"), back.column("value").to_pylist(), f"pyarrow {pa.__version__}", os.path.getsize(path), "B")


if __name__ == "__main__":
    main()
