# Storage `num_tvg`

the 27 parts of storage num unchanged, then a group index over num's stored order: per run its group range (run_groups), per group its first row (group_start) and its pair code (group_key). A group is a maximal range of rows of one run with one pair code.

Units: run_groups: group indices; group_start: stored row positions of num; group_key: num pair codes (positions in num's pair list)

## Tables and columns

- `num`: adsh, tag, version, ddate, qtrs, uom, coreg, value, footnote

## Parts

- run_groups: U64, R + 1 entries; the groups of run r are [run_groups[r], run_groups[r + 1]) (layout offsets)
- group_start: U32, G + 1 entries; group g is stored rows [group_start[g], group_start[g + 1]) (row positions)
- group_key: U32, G entries; the pair code (tag, version) shared by every row of group g (index key)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
