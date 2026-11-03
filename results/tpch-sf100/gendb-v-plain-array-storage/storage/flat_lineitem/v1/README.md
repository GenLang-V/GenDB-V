# Storage `flat_lineitem`

fixed flat storage of lineitem: every column as a plain typed array in source row order, one part per column, two (offsets, bytes) per text column

Units: bigint I64, integer I32, date I32 days since 1970-01-01, numeric I128 coefficient at the declared scale, text I64 offsets into U8 UTF-8 bytes

## Tables and columns

- `lineitem`: l_orderkey, l_partkey, l_suppkey, l_linenumber, l_quantity, l_extendedprice, l_discount, l_tax, l_returnflag, l_linestatus, l_shipdate, l_commitdate, l_receiptdate, l_shipinstruct, l_shipmode, l_comment

## Parts

- L_ORDERKEY I64 of l_orderkey
- L_PARTKEY I64 of l_partkey
- L_SUPPKEY I64 of l_suppkey
- L_LINENUMBER I64 of l_linenumber
- L_QUANTITY I128 of l_quantity
- L_EXTENDEDPRICE I128 of l_extendedprice
- L_DISCOUNT I128 of l_discount
- L_TAX I128 of l_tax
- L_RETURNFLAG_OFFSETS I64 of l_returnflag
- L_RETURNFLAG_BYTES U8 of l_returnflag
- L_LINESTATUS_OFFSETS I64 of l_linestatus
- L_LINESTATUS_BYTES U8 of l_linestatus
- L_SHIPDATE I32 of l_shipdate
- L_COMMITDATE I32 of l_commitdate
- L_RECEIPTDATE I32 of l_receiptdate
- L_SHIPINSTRUCT_OFFSETS I64 of l_shipinstruct
- L_SHIPINSTRUCT_BYTES U8 of l_shipinstruct
- L_SHIPMODE_OFFSETS I64 of l_shipmode
- L_SHIPMODE_BYTES U8 of l_shipmode
- L_COMMENT_OFFSETS I64 of l_comment
- L_COMMENT_BYTES U8 of l_comment

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
