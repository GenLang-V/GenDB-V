# Storage `custpart`

customer and part in canonical row order (stored row j = source row j): uniform 65536-row groups, every numeric/integer column frame-of-reference coded, low-cardinality text (c_mktsegment, p_mfgr, p_brand, p_type, p_container) as sorted dictionaries with U8 codes, other text as offsets + bytes; key flags: stored rows sorted by c_custkey / p_partkey (kind 1), so key lookups binary-search or probe the dense position.

Units: Integers exact: bigint as integers, numeric(15,2) as coefficients of scale 2 (value = coefficient / 100), dates as days since 2000-01-01 (Val::Date); frame-of-reference value = group base (I64, or U64 for dictionary indices and row positions) + unsigned code (U8/U16/U32) of the row; text offsets are byte offsets (U64, from 0) into the U8 byte part; group starts and row positions are stored-row indices; block size 65536 rows.

## Tables and columns

- `customer`: c_custkey, c_name, c_address, c_nationkey, c_phone, c_acctbal, c_mktsegment, c_comment
- `part`: p_partkey, p_name, p_mfgr, p_brand, p_type, p_size, p_container, p_retailprice, p_comment

## Parts

- customer.layout: U64 [rows, block rows]
- customer.groups: U64 group starts
- customer.c_custkey: U32 codes
- customer.c_custkey: I64 group bases
- customer.c_name: U64 offsets
- customer.c_name: U8 bytes
- customer.c_address: U64 offsets
- customer.c_address: U8 bytes
- customer.c_nationkey: U8 codes
- customer.c_nationkey: I64 group bases
- customer.c_phone: U64 offsets
- customer.c_phone: U8 bytes
- customer.c_acctbal: U32 codes
- customer.c_acctbal: I64 group bases
- customer.c_mktsegment: U8 codes of dictionary indices
- customer.c_mktsegment: U64 group bases of dictionary indices
- customer.c_mktsegment: U64 dictionary offsets
- customer.c_mktsegment: U8 dictionary bytes
- customer.c_comment: U64 offsets
- customer.c_comment: U8 bytes
- customer.key_index_kind(c_custkey): U64 [key index kind: 0 none, 1 stored rows sorted by key, 2 key index]
- part.layout: U64 [rows, block rows]
- part.groups: U64 group starts
- part.p_partkey: U32 codes
- part.p_partkey: I64 group bases
- part.p_name: U64 offsets
- part.p_name: U8 bytes
- part.p_mfgr: U8 codes of dictionary indices
- part.p_mfgr: U64 group bases of dictionary indices
- part.p_mfgr: U64 dictionary offsets
- part.p_mfgr: U8 dictionary bytes
- part.p_brand: U8 codes of dictionary indices
- part.p_brand: U64 group bases of dictionary indices
- part.p_brand: U64 dictionary offsets
- part.p_brand: U8 dictionary bytes
- part.p_type: U8 codes of dictionary indices
- part.p_type: U64 group bases of dictionary indices
- part.p_type: U64 dictionary offsets
- part.p_type: U8 dictionary bytes
- part.p_size: U8 codes
- part.p_size: I64 group bases
- part.p_container: U8 codes of dictionary indices
- part.p_container: U64 group bases of dictionary indices
- part.p_container: U64 dictionary offsets
- part.p_container: U8 dictionary bytes
- part.p_retailprice: U32 codes
- part.p_retailprice: I64 group bases
- part.p_comment: U64 offsets
- part.p_comment: U8 bytes
- part.key_index_kind(p_partkey): U64 [key index kind: 0 none, 1 stored rows sorted by key, 2 key index]

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
