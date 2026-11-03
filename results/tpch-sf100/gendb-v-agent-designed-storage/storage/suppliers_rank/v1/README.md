# Storage `suppliers_rank`

storage suppliers unchanged (48 inherited parts), then a permutation of the supplier rows by s_acctbal descending and a dense ps_suppkey directory of partsupp (I64 [mode, kmin], U32 offsets, U32 permutation of the partsupp rows grouped by ps_suppkey)

Units: row positions of suppliers' stored (canonical) supplier and partsupp rows; directory entry e is ps_suppkey kmin + e; offsets are permutation positions

## Tables and columns

- `partsupp`: ps_partkey, ps_suppkey, ps_availqty, ps_supplycost, ps_comment
- `supplier`: s_suppkey, s_name, s_address, s_nationkey, s_phone, s_acctbal, s_comment
- `nation`: n_nationkey, n_name, n_regionkey, n_comment
- `region`: r_regionkey, r_name, r_comment

## Parts

- SBAL (U32): supplier rows in descending s_acctbal order (row positions only), or empty
- PSMETA (I64 [mode, kmin]): mode 1 = dense directory over ps_suppkey values kmin .. kmin + nk
- PSOFFS (U32, nk + 1): positions offs[e] .. offs[e + 1] of PSPERM hold the partsupp rows of ps_suppkey kmin + e
- PSPERM (U32): partsupp row positions grouped by ps_suppkey (rows ascending within a key)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
