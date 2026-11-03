# Storage `psrun`

storage suppliers (partsupp, supplier, nation, region; its 48 parts linked unchanged) followed by part 48: I64 runs = [ratio, one entry per 65536-row block of partsupp]

Units: ratio: partsupp rows per key; entries: ps_partkey values (bigint) or i64::MIN for no run

## Tables and columns

- `partsupp`: ps_partkey, ps_suppkey, ps_availqty, ps_supplycost, ps_comment
- `supplier`: s_suppkey, s_name, s_address, s_nationkey, s_phone, s_acctbal, s_comment
- `nation`: n_nationkey, n_name, n_regionkey, n_comment
- `region`: r_regionkey, r_name, r_comment

## Parts

- partsupp ps_partkey key runs: I64 [ratio r >= 1, then per block b of 65536 stored partsupp rows: NO_RUN (i64::MIN) or the key k with ps_partkey(i) == k + (i - 65536 b) / r for every row i of the block]

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
