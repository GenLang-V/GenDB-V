# Storage `pre`

pre clustered by (adsh, (stmt, rfile), tag, version): orig permutation to canonical rows; (adsh, stmt/rfile group) run-length encoded into sub-runs with an adsh directory; a dictionary of distinct (stmt, rfile) groups; sorted dictionaries for adsh, stmt, rfile, tag, version, plabel; per-row (tag, version) pair code, line and plabel code/validity in stored order; report, inpth, negating in canonical order.

Units: rows: stored positions unless noted canonical; offsets: bytes; codes: dictionary positions

## Tables and columns

- `pre`: adsh, report, line, stmt, inpth, rfile, tag, version, plabel, negating

## Parts

- orig: canonical row of each stored row (U64 permutation of 0..n)
- sub_start: first stored row of each (adsh, stmt, rfile) sub-run, plus n (U64, S+1)
- sub_adsh: adsh code of each sub-run (U64, S)
- sub_group: (stmt, rfile) group code of each sub-run (U64, S)
- adsh_subs: first sub-run of each adsh code, plus S (U64, A+1)
- adsh dictionary offsets (U64)
- adsh dictionary bytes (U8)
- group_stmt: stmt key of each group, 0 = NULL, else stmt code + 1 (U64)
- group_rfile: rfile code of each group (U64)
- stmt dictionary offsets (U64)
- stmt dictionary bytes (U8)
- rfile dictionary offsets (U64)
- rfile dictionary bytes (U8)
- tv: (tag, version) pair code per stored row (U64)
- pair_tag: tag code of each pair (U64)
- pair_version: version code of each pair (U64)
- tag dictionary offsets (U64)
- tag dictionary bytes (U8)
- version dictionary offsets (U64)
- version dictionary bytes (U8)
- line per stored row (I32)
- plabel code per stored row (U64)
- plabel validity per stored row (U8, 0 = NULL)
- plabel dictionary offsets (U64)
- plabel dictionary bytes (U8)
- report in canonical row order (I32)
- inpth in canonical row order (I32)
- negating in canonical row order (I32)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
