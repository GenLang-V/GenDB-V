# Storage `lisupp`

facts (inherited unchanged, parts 0..74) plus a key index of lineitem by l_suppkey in the facts keyidx format: a permutation of the stored lineitem rows sorted by l_suppkey (FOR-coded positions), checked at build time to be a bijection and sorted

Units: index entries are stored lineitem row positions of facts (U32 codes + U64 group bases over the lineitem block size); kind flag 0 or 2

## Tables and columns

- `lineitem`: l_suppkey, l_extendedprice, l_discount, l_shipdate

## Parts

- lineitem.l_suppkey key index: U32 codes of the stored rows in key order (index position r -> stored row bases[r / block] + codes[r])
- lineitem.l_suppkey key index: U64 group bases of the index column (one per block of the lineitem layout)
- lineitem.l_suppkey key index kind: U64 [0 none, 2 index]

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
