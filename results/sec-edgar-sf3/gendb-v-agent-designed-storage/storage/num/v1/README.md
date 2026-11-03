# Storage `num`

num clustered by (uom, adsh, tag, version): orig permutation to canonical rows; (uom, adsh) run-length encoded with a uom directory; sorted dictionaries for uom, adsh, tag, version; per-row (tag, version) pair code; ddate and value per stored row; per-run ddate min/max; qtrs, coreg, footnote in canonical order (coreg and footnote sparse).

Units: rows: stored positions unless noted canonical; offsets: bytes; codes: dictionary positions; value: numeric(28,4) coefficient (scale 4); ddate: yyyymmdd integer

## Tables and columns

- `num`: adsh, tag, version, ddate, qtrs, uom, coreg, value, footnote

## Parts

- orig: canonical row of each stored row (U64 permutation of 0..n)
- run_start: first stored row of each (uom, adsh) run, plus n (U64, R+1)
- run_uom: uom code of each run (U64, R)
- run_adsh: adsh code of each run (U64, R)
- uom_runs: first run of each uom code, plus R (U64, U+1)
- uom dictionary offsets (U64)
- uom dictionary bytes (U8)
- adsh dictionary offsets (U64)
- adsh dictionary bytes (U8)
- tv: (tag, version) pair code per stored row (U64)
- pair_tag: tag code of each pair (U64)
- pair_version: version code of each pair (U64)
- tag dictionary offsets (U64)
- tag dictionary bytes (U8)
- version dictionary offsets (U64)
- version dictionary bytes (U8)
- ddate per stored row (I32)
- value per stored row (I128, numeric(28,4) coefficients)
- run_ddate_min: minimum ddate of each run (I32, R)
- run_ddate_max: maximum ddate of each run (I32, R)
- qtrs in canonical row order (I32)
- coreg: canonical rows that are not NULL, increasing (U64)
- coreg values of those rows: offsets (U64)
- coreg values of those rows: bytes (U8)
- footnote: canonical rows that are not NULL, increasing (U64)
- footnote values of those rows: offsets (U64)
- footnote values of those rows: bytes (U8)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
