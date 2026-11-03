# Storage `li_bits`

facts unchanged (75 inherited parts), then bitmap indexes over facts' stored lineitem rows: equality bitmaps of l_discount (keys 0.00..0.10), range bitmaps of l_quantity (l_quantity < 2 .. < 51) and per-row-group range bitmaps of l_shipdate at month starts; one bit per stored row, 64 rows per U64 word, bitmap-major

Units: bits per stored lineitem row (stored order of facts); keys in coefficient units (scale 2) and days since 2000-01-01

## Tables and columns

- `lineitem`: l_orderkey, l_partkey, l_suppkey, l_linenumber, l_quantity, l_extendedprice, l_discount, l_tax, l_returnflag, l_linestatus, l_shipdate, l_commitdate, l_receiptdate, l_shipinstruct, l_shipmode
- `orders`: o_orderkey, o_custkey, o_orderstatus, o_totalprice, o_orderdate, o_orderpriority, o_shippriority

## Parts

- lineitem: U64 layout [nw words per bitmap, nd discount keys, nq quantity keys, ns shipdate keys per row group]
- lineitem: I64 l_discount keys of the equality bitmaps (coefficients at scale 2: 0..10)
- lineitem: U64 equality bitmap index of l_discount: nd bitmaps of nw words; bit i of word w of bitmap k is set iff stored row 64w+i has l_discount == key k
- lineitem: I64 l_quantity keys of the range bitmaps (coefficients at scale 2: 200..5100)
- lineitem: U64 range bitmap index of l_quantity: nq bitmaps of nw words; bit of row j in bitmap t is set iff l_quantity of row j < key t
- lineitem: I64 l_shipdate keys per row group of facts (ns per group: the month starts after the group's base shipdate, days since 2000-01-01)
- lineitem: U64 range bitmap index of l_shipdate per row group: ns bitmaps of nw words; bit of row j in bitmap t is set iff l_shipdate of row j < key t of row j's group

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
