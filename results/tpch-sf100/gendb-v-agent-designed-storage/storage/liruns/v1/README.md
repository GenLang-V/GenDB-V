# Storage `liruns`

storage facts unchanged (75 inherited parts), then U64 [mode, stride], U8 run lengths of equal l_orderkey along the stored lineitem rows, U64 starts of every stride-th run, I64 l_quantity maxima per lineitem group, then the permutation of the runs by length (U64 [mode, lmax, nlong], U32 run indices, U32 start rows)

Units: run lengths and starts are lineitem row counts / stored row positions of facts; zone maxima are l_quantity coefficients at scale 2

## Tables and columns

- `lineitem`: l_orderkey, l_quantity
- `orders`: o_orderkey, o_custkey, o_totalprice, o_orderdate

## Parts

- lineitem runs: U64 [mode, stride] (mode 1: runs and zone map present)
- lineitem runs: U8 length of each maximal run of equal l_orderkey in the stored row order of facts
- lineitem runs: U64 start row of every stride-th run
- lineitem l_quantity zone map: I64 maximum coefficient of each 65536-row group
- lineitem runs by length: U64 [mode, longest run length, number of runs of that length]
- lineitem runs by length: U32 run indices of all runs ordered by run length (longest first), then by run index
- lineitem runs by length: U32 start rows of the same runs in the same order

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
