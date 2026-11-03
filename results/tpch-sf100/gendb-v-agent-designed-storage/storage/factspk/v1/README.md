# Storage `factspk`

storage facts (lineitem, orders; its 75 parts linked unchanged) followed by a directory over facts' l_partkey key index: part 75 I64 [kb], part 76 U32 dir of (max key - kb + 2) entries; the rows of l_partkey kb + i are the key-index positions [dir[i], dir[i+1]) because the index is sorted by key

Units: kb: l_partkey value; dir: positions in facts' l_partkey key index (0 .. row count)

## Tables and columns

- `lineitem`: l_orderkey, l_partkey, l_suppkey, l_linenumber, l_quantity, l_extendedprice, l_discount, l_tax, l_returnflag, l_linestatus, l_shipdate, l_commitdate, l_receiptdate, l_shipinstruct, l_shipmode
- `orders`: o_orderkey, o_custkey, o_orderstatus, o_totalprice, o_orderdate, o_orderpriority, o_shippriority

## Parts

- lineitem l_partkey directory: I64 [kb], the key of directory entry 0
- lineitem l_partkey directory: U32 dir, dir[i] = the first position of facts' l_partkey key index (part 45/46) whose l_partkey is at least kb + i (the row count when none)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
