# Storage `num_vord`

the 27 parts of storage num unchanged, then vorder: per unit (uom code), the unit's stored row positions sorted by value descending (ties by row), at the unit's own positions.

Units: vorder: stored row positions of num

## Tables and columns

- `num`: adsh, tag, version, ddate, qtrs, uom, coreg, value, footnote

## Parts

- vorder: U64, n entries; for every uom code u, positions [unit_row(u), unit_row(u + 1)) hold the stored rows of that same range ordered by value descending, ties by stored row (row positions only)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
