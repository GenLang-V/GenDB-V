# Storage `facts`

lineitem (all columns but l_comment) and orders (all columns but o_clerk, o_comment). orders stored sorted by o_orderdate; lineitem stored grouped by the stored position of its order (co-clustered), each table with a row map column (stored row -> canonical row). Per table: uniform 65536-row groups; every column frame-of-reference coded (U8/U16/U32 codes, per-group base); low-cardinality text as a sorted dictionary + codes; zone maps (group maxima) on l_shipdate, l_commitdate, l_receiptdate, o_orderdate; key indexes: orders by o_orderkey (index = inverse row map, kind 2), lineitem by l_partkey (sorted permutation, kind 2); a checked co-clustering flag.

Units: Integers exact: bigint as integers, numeric(15,2) as coefficients of scale 2 (value = coefficient / 100), dates as days since 2000-01-01 (Val::Date); frame-of-reference value = group base (I64, or U64 for dictionary indices and row positions) + unsigned code (U8/U16/U32) of the row; text offsets are byte offsets (U64, from 0) into the U8 byte part; group starts and row positions are stored-row indices; block size 65536 rows.

## Tables and columns

- `lineitem`: l_orderkey, l_partkey, l_suppkey, l_linenumber, l_quantity, l_extendedprice, l_discount, l_tax, l_returnflag, l_linestatus, l_shipdate, l_commitdate, l_receiptdate, l_shipinstruct, l_shipmode
- `orders`: o_orderkey, o_custkey, o_orderstatus, o_totalprice, o_orderdate, o_orderpriority, o_shippriority

## Parts

- lineitem.layout: U64 [rows, block rows]
- lineitem.groups: U64 group starts
- lineitem.row_map: U32 codes of the canonical row of each stored row
- lineitem.row_map: U64 group bases of canonical rows
- lineitem.l_orderkey: U32 codes
- lineitem.l_orderkey: I64 group bases
- lineitem.l_partkey: U32 codes
- lineitem.l_partkey: I64 group bases
- lineitem.l_suppkey: U32 codes
- lineitem.l_suppkey: I64 group bases
- lineitem.l_linenumber: U8 codes
- lineitem.l_linenumber: I64 group bases
- lineitem.l_quantity: U16 codes
- lineitem.l_quantity: I64 group bases
- lineitem.l_extendedprice: U32 codes
- lineitem.l_extendedprice: I64 group bases
- lineitem.l_discount: U8 codes
- lineitem.l_discount: I64 group bases
- lineitem.l_tax: U8 codes
- lineitem.l_tax: I64 group bases
- lineitem.l_returnflag: U8 codes of dictionary indices
- lineitem.l_returnflag: U64 group bases of dictionary indices
- lineitem.l_returnflag: U64 dictionary offsets
- lineitem.l_returnflag: U8 dictionary bytes
- lineitem.l_linestatus: U8 codes of dictionary indices
- lineitem.l_linestatus: U64 group bases of dictionary indices
- lineitem.l_linestatus: U64 dictionary offsets
- lineitem.l_linestatus: U8 dictionary bytes
- lineitem.l_shipdate: U16 codes
- lineitem.l_shipdate: I64 group bases
- lineitem.l_shipdate: I64 group maxima (zone map)
- lineitem.l_commitdate: U16 codes
- lineitem.l_commitdate: I64 group bases
- lineitem.l_commitdate: I64 group maxima (zone map)
- lineitem.l_receiptdate: U16 codes
- lineitem.l_receiptdate: I64 group bases
- lineitem.l_receiptdate: I64 group maxima (zone map)
- lineitem.l_shipinstruct: U8 codes of dictionary indices
- lineitem.l_shipinstruct: U64 group bases of dictionary indices
- lineitem.l_shipinstruct: U64 dictionary offsets
- lineitem.l_shipinstruct: U8 dictionary bytes
- lineitem.l_shipmode: U8 codes of dictionary indices
- lineitem.l_shipmode: U64 group bases of dictionary indices
- lineitem.l_shipmode: U64 dictionary offsets
- lineitem.l_shipmode: U8 dictionary bytes
- lineitem.key_index(l_partkey): U32 codes of the stored row at each key-order position (key index)
- lineitem.key_index(l_partkey): U64 group bases of the key index
- lineitem.key_index_kind(l_partkey): U64 [key index kind: 0 none, 1 stored rows sorted by key, 2 key index]
- orders.layout: U64 [rows, block rows]
- orders.groups: U64 group starts
- orders.row_map: U32 codes of the canonical row of each stored row
- orders.row_map: U64 group bases of canonical rows
- orders.o_orderkey: U32 codes
- orders.o_orderkey: I64 group bases
- orders.o_custkey: U32 codes
- orders.o_custkey: I64 group bases
- orders.o_orderstatus: U8 codes of dictionary indices
- orders.o_orderstatus: U64 group bases of dictionary indices
- orders.o_orderstatus: U64 dictionary offsets
- orders.o_orderstatus: U8 dictionary bytes
- orders.o_totalprice: U32 codes
- orders.o_totalprice: I64 group bases
- orders.o_orderdate: U16 codes
- orders.o_orderdate: I64 group bases
- orders.o_orderdate: I64 group maxima (zone map)
- orders.o_orderpriority: U8 codes of dictionary indices
- orders.o_orderpriority: U64 group bases of dictionary indices
- orders.o_orderpriority: U64 dictionary offsets
- orders.o_orderpriority: U8 dictionary bytes
- orders.o_shippriority: U8 codes
- orders.o_shippriority: I64 group bases
- orders.key_index(o_orderkey): U32 codes of the stored row at each key-order position (key index)
- orders.key_index(o_orderkey): U64 group bases of the key index
- orders.key_index_kind(o_orderkey): U64 [key index kind: 0 none, 1 stored rows sorted by key, 2 key index]
- lineitem.cluster_flag: U64 [1 when the stored lineitem rows follow the stored order of their orders]

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
