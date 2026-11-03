# Storage `li_okruns`

storage facts unchanged (its 75 parts, inherited), then one U32 part: the start row of every maximal run of equal l_orderkey in facts' stored lineitem order, then the row count (runs + 1 entries; [0] when the table is empty or has more than u32::MAX - 1 rows)

Units: stored lineitem row positions of facts (0 .. rows), U32

## Tables and columns

- `lineitem`: l_orderkey, l_partkey, l_suppkey, l_linenumber, l_quantity, l_extendedprice, l_discount, l_tax, l_returnflag, l_linestatus, l_shipdate, l_commitdate, l_receiptdate, l_shipinstruct, l_shipmode
- `orders`: o_orderkey, o_custkey, o_orderstatus, o_totalprice, o_orderdate, o_orderpriority, o_shippriority

## Parts

- U32 run starts: the first stored lineitem row of each maximal run of equal l_orderkey, in stored row order, followed by the row count

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
