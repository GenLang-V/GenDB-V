# Storage `factext`

The long, rarely used text columns of lineitem (l_comment) and orders (o_clerk as a sorted dictionary of 100000 entries with U32 codes, o_comment as text), in canonical row order (stored row j = source row j), with uniform 65536-row groups.

Units: Integers exact: bigint as integers, numeric(15,2) as coefficients of scale 2 (value = coefficient / 100), dates as days since 2000-01-01 (Val::Date); frame-of-reference value = group base (I64, or U64 for dictionary indices and row positions) + unsigned code (U8/U16/U32) of the row; text offsets are byte offsets (U64, from 0) into the U8 byte part; group starts and row positions are stored-row indices; block size 65536 rows.

## Tables and columns

- `lineitem`: l_comment
- `orders`: o_clerk, o_comment

## Parts

- lineitem.layout: U64 [rows, block rows]
- lineitem.groups: U64 group starts
- lineitem.l_comment: U64 offsets
- lineitem.l_comment: U8 bytes
- orders.layout: U64 [rows, block rows]
- orders.groups: U64 group starts
- orders.o_clerk: U32 codes of dictionary indices
- orders.o_clerk: U64 group bases of dictionary indices
- orders.o_clerk: U64 dictionary offsets
- orders.o_clerk: U8 dictionary bytes
- orders.o_comment: U64 offsets
- orders.o_comment: U8 bytes

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
