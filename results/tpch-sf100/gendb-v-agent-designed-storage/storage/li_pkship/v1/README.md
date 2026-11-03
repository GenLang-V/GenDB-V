# Storage `li_pkship`

facts unchanged (75 inherited parts), then a composite index of lineitem on (l_partkey, l_shipinstruct, l_shipmode): a dense directory over l_partkey, the stored rows in key order, and the (l_shipinstruct, l_shipmode) key byte of each index position

Units: keys are bigint l_partkey values; offsets are index positions (U32); index rows are stored lineitem rows of facts (U32); ship keys are 16 * si + sm with si, sm the dictionary indices of facts' l_shipinstruct and l_shipmode dictionaries

## Tables and columns

- `lineitem`: l_partkey, l_quantity, l_extendedprice, l_discount, l_shipinstruct, l_shipmode

## Parts

- IDX_META (I64 [mode, kmin]): mode 1 when the index is present, and the first l_partkey of the directory
- IDX_OFFS (U32, nkeys + 1): directory over l_partkey kmin .. kmin + nkeys; entry e is the index positions offs[e] .. offs[e + 1]
- IDX_ROWS (U32, one per lineitem row): the stored lineitem rows of facts in (l_partkey, l_shipinstruct, l_shipmode) order
- IDX_SHIP (U8, one per lineitem row): the second key 16 * si + sm (l_shipinstruct and l_shipmode dictionary indices) of the row at the same index position

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
