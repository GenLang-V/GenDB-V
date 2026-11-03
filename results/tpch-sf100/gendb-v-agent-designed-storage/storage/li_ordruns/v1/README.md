# Storage `li_ordruns`

facts unchanged (75 inherited parts), then one U8 part: the run-length encoding of l_orderkey along facts' stored lineitem rows (lineitem is stored grouped by order, so one run per order). Empty when a run exceeds 255 rows.

Units: run lengths in lineitem rows (1..255)

## Tables and columns

- `lineitem`: l_orderkey, l_partkey, l_suppkey, l_linenumber, l_quantity, l_extendedprice, l_discount, l_tax, l_returnflag, l_linestatus, l_shipdate, l_commitdate, l_receiptdate, l_shipinstruct, l_shipmode
- `orders`: o_orderkey, o_custkey, o_orderstatus, o_totalprice, o_orderdate, o_orderpriority, o_shippriority

## Parts

- lineitem: U8 run lengths of l_orderkey along the stored lineitem rows: entry r is the number of rows of the r-th maximal run of equal l_orderkey (empty when a run exceeds 255 rows)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
