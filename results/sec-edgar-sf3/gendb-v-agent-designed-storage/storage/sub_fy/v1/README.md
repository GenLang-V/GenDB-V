# Storage `sub_fy`

the 44 parts of storage sub unchanged (sub in canonical row order, adsh_order), then fy_order: the row positions sorted by (fy with NULL first, cik, name code, row), then adsh_rank: the inverse of adsh_order.

Units: rows: canonical sub rows; fy_order: row positions; offsets: bytes; codes: dictionary positions

## Tables and columns

- `sub`: adsh, cik, name, sic, countryba, stprba, cityba, countryinc, form, period, fy, fp, filed, accepted, prevrpt, nciks, afs, wksi, fye, instance

## Parts

- fy_order: U64 row positions, a permutation of 0..n sorted by (fy (NULL first), cik, name code, row)
- adsh_rank: U64, the position of each row in adsh_order (inverse permutation)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
