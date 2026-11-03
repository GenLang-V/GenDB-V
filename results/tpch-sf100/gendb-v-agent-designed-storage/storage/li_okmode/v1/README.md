# Storage `li_okmode`

storage li_okruns unchanged (76 inherited parts: facts' 75 parts and the l_orderkey run starts), then one U64 layout part and two bitmap parts over facts' stored lineitem rows: the l_orderkey run-start bitmap and one equality bitmap per l_shipmode dictionary entry; one bit per stored row, 64 rows per U64 word

Units: bits per stored lineitem row (stored order of facts); bitmap words of 64 rows

## Tables and columns

- `lineitem`: l_orderkey, l_partkey, l_suppkey, l_linenumber, l_quantity, l_extendedprice, l_discount, l_tax, l_returnflag, l_linestatus, l_shipdate, l_commitdate, l_receiptdate, l_shipinstruct, l_shipmode
- `orders`: o_orderkey, o_custkey, o_orderstatus, o_totalprice, o_orderdate, o_orderpriority, o_shippriority

## Parts

- OKM_LAYOUT (U64, 2): words per bitmap nw (ceil(rows / 64), 0 for the fallback without bitmaps) and the number nm of l_shipmode bitmaps
- RUN_BITS (U64, nw): bit j % 64 of word j / 64 is set exactly when stored lineitem row j of facts starts a maximal run of equal l_orderkey (j == 0 or its key differs from row j - 1's); bits past the row count are 0
- MODE_BITS (U64, nm * nw, bitmap-major): bit j of bitmap k is set exactly when stored lineitem row j of facts has l_shipmode dictionary index k (group base + code); bits past the row count are 0

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
