# Storage `tag_tv`

the 28 parts of storage tag unchanged, then tag_first (per tag code, its first tv_order position) and tv_version (the version code at each tv_order position): a (tag, version) -> row index over tag's own keys.

Units: positions: tv_order positions; codes: tag's own tag / version dictionary positions; rows: canonical tag rows

## Tables and columns

- `tag`: tag, version, custom, abstract, datatype, iord, crdr, tlabel, doc

## Parts

- tag_first: U64, tag count + 1 entries: per tag code c the number of tv_order positions whose row's tag code is below c
- tv_version: U64, one per tv_order position: the version code of the row at that position

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
