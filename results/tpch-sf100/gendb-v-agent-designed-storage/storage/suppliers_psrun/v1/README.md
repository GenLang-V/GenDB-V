# Storage `suppliers_psrun`

Storage suppliers with its parts unchanged (linked), extended by one layout part: the uniform run length of partsupp's ps_partkey runs and the first key, so the partsupp rows of a key are found by arithmetic (rows (key - first) * ratio .. + ratio) without reading the key column.

Units: ratio: rows per ps_partkey run; first: bigint ps_partkey of row 0

## Tables and columns

- `partsupp`: ps_partkey, ps_suppkey, ps_availqty, ps_supplycost, ps_comment
- `supplier`: s_suppkey, s_name, s_address, s_nationkey, s_phone, s_acctbal, s_comment
- `nation`: n_nationkey, n_name, n_regionkey, n_comment
- `region`: r_regionkey, r_name, r_comment

## Parts

- part: I64 [ratio, first]: when ratio >= 1, the stored partsupp rows (sorted by ps_partkey) form runs of exactly ratio rows per key, starting at ps_partkey first: row k has ps_partkey first + k / ratio; [0, 0] when the layout has no such uniform runs

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
