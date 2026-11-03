# Storage `tag`

tag in canonical row order; every text column dictionary-coded (U64 code per row into a strictly sorted dictionary, U8 validity for nullable columns); custom and abstract as I32; tv_order: the row positions sorted by (tag, version).

Units: rows: canonical tag rows; offsets: bytes; codes: dictionary positions; tv_order: row positions

## Tables and columns

- `tag`: tag, version, custom, abstract, datatype, iord, crdr, tlabel, doc

## Parts

- tag code per row (U64)
- tag dictionary offsets (U64)
- tag dictionary bytes (U8)
- version code per row (U64)
- version dictionary offsets (U64)
- version dictionary bytes (U8)
- tv_order: row positions sorted by (tag, version) (U64 permutation)
- custom (I32)
- abstract (I32)
- datatype code per row (U64)
- datatype validity per row (U8, 0 = NULL)
- datatype dictionary offsets (U64)
- datatype dictionary bytes (U8)
- iord code per row (U64)
- iord dictionary offsets (U64)
- iord dictionary bytes (U8)
- crdr code per row (U64)
- crdr validity per row (U8, 0 = NULL)
- crdr dictionary offsets (U64)
- crdr dictionary bytes (U8)
- tlabel code per row (U64)
- tlabel validity per row (U8, 0 = NULL)
- tlabel dictionary offsets (U64)
- tlabel dictionary bytes (U8)
- doc code per row (U64)
- doc validity per row (U8, 0 = NULL)
- doc dictionary offsets (U64)
- doc dictionary bytes (U8)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
