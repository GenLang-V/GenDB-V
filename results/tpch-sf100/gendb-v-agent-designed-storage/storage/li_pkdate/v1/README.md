# Storage `li_pkdate`

facts unchanged (75 inherited parts), then a composite index of lineitem on (l_partkey, l_shipdate): a dense directory over l_partkey, the stored rows in key order, and the l_shipdate key of each index position

Units: keys are bigint l_partkey values and days since 2000-01-01 (date key = dbase + U16 code); offsets are index positions (U32); index rows are stored lineitem rows of facts (U32)

## Tables and columns

- `lineitem`: l_partkey, l_suppkey, l_quantity, l_shipdate

## Parts

- IDX_META (I64 [mode, kmin, dbase]): mode 1 when the index is present, the first l_partkey of the directory and the base day of the date keys
- IDX_OFFS (U32, nkeys + 1): directory over l_partkey kmin .. kmin + nkeys; entry e is the index positions offs[e] .. offs[e + 1]
- IDX_ROWS (U32, one per lineitem row): the stored lineitem rows of facts in (l_partkey, l_shipdate) order
- IDX_DATES (U16, one per lineitem row): l_shipdate - dbase of the row at the same index position (the index's second key)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
