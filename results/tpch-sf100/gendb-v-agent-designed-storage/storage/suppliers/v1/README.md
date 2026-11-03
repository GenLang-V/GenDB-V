# Storage `suppliers`

partsupp, supplier, nation and region in canonical row order: uniform 65536-row groups, frame-of-reference coded numeric/integer columns, text as offsets + bytes; key flags: partsupp rows sorted by ps_partkey and supplier rows by s_suppkey (kind 1).

Units: Integers exact: bigint as integers, numeric(15,2) as coefficients of scale 2 (value = coefficient / 100), dates as days since 2000-01-01 (Val::Date); frame-of-reference value = group base (I64, or U64 for dictionary indices and row positions) + unsigned code (U8/U16/U32) of the row; text offsets are byte offsets (U64, from 0) into the U8 byte part; group starts and row positions are stored-row indices; block size 65536 rows.

## Tables and columns

- `partsupp`: ps_partkey, ps_suppkey, ps_availqty, ps_supplycost, ps_comment
- `supplier`: s_suppkey, s_name, s_address, s_nationkey, s_phone, s_acctbal, s_comment
- `nation`: n_nationkey, n_name, n_regionkey, n_comment
- `region`: r_regionkey, r_name, r_comment

## Parts

- partsupp.layout: U64 [rows, block rows]
- partsupp.groups: U64 group starts
- partsupp.ps_partkey: U32 codes
- partsupp.ps_partkey: I64 group bases
- partsupp.ps_suppkey: U32 codes
- partsupp.ps_suppkey: I64 group bases
- partsupp.ps_availqty: U16 codes
- partsupp.ps_availqty: I64 group bases
- partsupp.ps_supplycost: U32 codes
- partsupp.ps_supplycost: I64 group bases
- partsupp.ps_comment: U64 offsets
- partsupp.ps_comment: U8 bytes
- partsupp.key_index_kind(ps_partkey): U64 [key index kind: 0 none, 1 stored rows sorted by key, 2 key index]
- supplier.layout: U64 [rows, block rows]
- supplier.groups: U64 group starts
- supplier.s_suppkey: U32 codes
- supplier.s_suppkey: I64 group bases
- supplier.s_name: U64 offsets
- supplier.s_name: U8 bytes
- supplier.s_address: U64 offsets
- supplier.s_address: U8 bytes
- supplier.s_nationkey: U8 codes
- supplier.s_nationkey: I64 group bases
- supplier.s_phone: U64 offsets
- supplier.s_phone: U8 bytes
- supplier.s_acctbal: U32 codes
- supplier.s_acctbal: I64 group bases
- supplier.s_comment: U64 offsets
- supplier.s_comment: U8 bytes
- supplier.key_index_kind(s_suppkey): U64 [key index kind: 0 none, 1 stored rows sorted by key, 2 key index]
- nation.layout: U64 [rows, block rows]
- nation.groups: U64 group starts
- nation.n_nationkey: U8 codes
- nation.n_nationkey: I64 group bases
- nation.n_name: U64 offsets
- nation.n_name: U8 bytes
- nation.n_regionkey: U8 codes
- nation.n_regionkey: I64 group bases
- nation.n_comment: U64 offsets
- nation.n_comment: U8 bytes
- region.layout: U64 [rows, block rows]
- region.groups: U64 group starts
- region.r_regionkey: U8 codes
- region.r_regionkey: I64 group bases
- region.r_name: U64 offsets
- region.r_name: U8 bytes
- region.r_comment: U64 offsets
- region.r_comment: U8 bytes

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
