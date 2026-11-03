#!/usr/bin/env python3
"""Write the data of the example `readings-count` (README.md beside this script).

Usage: python3 make_data.py DIR      (setup_data.sh runs it with DIR = data/tiny)

Writes DIR/readings.parquet (an existing file is refused): one table `readings` with one column
`value bigint NOT NULL` (Arrow int64, nullable=False), holding the rows 5, 5, 9, 0 in this order. GenDB imports a
Parquet file only when its Arrow schema is exactly the declared one, so the column is declared non-null here too. The
declared constraint CHECK (value >= 0) holds on these rows (checked before writing). The writer options are fixed, so
the same pyarrow version always writes the same bytes.
"""
import os
import sys

import pyarrow as pa
import pyarrow.parquet as pq

ROWS = [5, 5, 9, 0]  # the rows of `readings`, in row order


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    data_dir = sys.argv[1]
    path = os.path.join(data_dir, "readings.parquet")
    if os.path.exists(path):
        sys.exit(f"{path} exists")
    assert all(v >= 0 for v in ROWS), "CHECK (value >= 0) must hold on the data"
    schema = pa.schema([pa.field("value", pa.int64(), nullable=False)])
    table = pa.Table.from_arrays([pa.array(ROWS, type=pa.int64())], schema=schema)
    os.makedirs(data_dir, exist_ok=True)
    pq.write_table(table, path, compression="zstd", version="2.6", write_statistics=True, use_dictionary=True)
    back = pq.read_table(path)
    print(path, back.schema.field("value"), back.column("value").to_pylist(), f"pyarrow {pa.__version__}", os.path.getsize(path), "B")


if __name__ == "__main__":
    main()
