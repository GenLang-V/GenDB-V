# Storage `li_pairmask`

facts unchanged (75 inherited parts), then one U64 part: per chunk of 2048 stored lineitem rows, the set of (l_returnflag, l_linestatus) code pairs present, as a 64-bit mask (bit rf_code * 8 + ls_code)

Units: bits indexed by rf_code * 8 + ls_code, codes being facts' sorted-dictionary indices; mask c covers stored lineitem rows [2048 c, 2048 c + 2048)

## Tables and columns

- `lineitem`: l_orderkey, l_partkey, l_suppkey, l_linenumber, l_quantity, l_extendedprice, l_discount, l_tax, l_returnflag, l_linestatus, l_shipdate, l_commitdate, l_receiptdate, l_shipinstruct, l_shipmode
- `orders`: o_orderkey, o_custkey, o_orderstatus, o_totalprice, o_orderdate, o_orderpriority, o_shippriority

## Parts

- lineitem: U64 pair masks, one per chunk of 2048 stored lineitem rows of facts: bit rf * 8 + ls is set for every (l_returnflag, l_linestatus) dictionary-code pair (rf, ls) occurring in the chunk (empty when a code is 8 or more)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
