# Storage `sub_sic`

the 46 parts of storage sub_fy unchanged, then sic_order: the row positions sorted by (sic with NULL first, cik, row).

Units: rows: canonical sub rows; sic_order: row positions

## Tables and columns

- `sub`: adsh, cik, name, sic, countryba, stprba, cityba, countryinc, form, period, fy, fp, filed, accepted, prevrpt, nciks, afs, wksi, fye, instance

## Parts

- sic_order: U64 row positions, a permutation of 0..n sorted by (sic (NULL first), cik, row)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
