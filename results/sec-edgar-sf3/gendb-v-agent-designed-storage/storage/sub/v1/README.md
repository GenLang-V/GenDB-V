# Storage `sub`

sub (one row per filing) in canonical row order, one part per int4 column, a U8 validity part per nullable column, flat text (U64 offsets + U8 bytes) per text column; name dictionary-encoded (U64 codes into a strictly sorted dictionary); adsh_order: the row positions sorted by adsh.

Units: rows: canonical sub rows; offsets: bytes; codes: dictionary positions; adsh_order: row positions

## Tables and columns

- `sub`: adsh, cik, name, sic, countryba, stprba, cityba, countryinc, form, period, fy, fp, filed, accepted, prevrpt, nciks, afs, wksi, fye, instance

## Parts

- adsh text offsets (U64, n+1)
- adsh text bytes (U8)
- adsh_order: row positions sorted by adsh (U64 permutation)
- cik (I32)
- name codes per row (U64) into the name dictionary
- name dictionary offsets (U64)
- name dictionary bytes (U8)
- sic (I32)
- sic validity (U8, 0 = NULL)
- countryba text offsets (U64, n+1)
- countryba text bytes (U8)
- countryba validity (U8, 0 = NULL)
- stprba text offsets (U64, n+1)
- stprba text bytes (U8)
- stprba validity (U8, 0 = NULL)
- cityba text offsets (U64, n+1)
- cityba text bytes (U8)
- cityba validity (U8, 0 = NULL)
- countryinc text offsets (U64, n+1)
- countryinc text bytes (U8)
- countryinc validity (U8, 0 = NULL)
- form text offsets (U64, n+1)
- form text bytes (U8)
- period (I32)
- period validity (U8, 0 = NULL)
- fy (I32)
- fy validity (U8, 0 = NULL)
- fp text offsets (U64, n+1)
- fp text bytes (U8)
- fp validity (U8, 0 = NULL)
- filed (I32)
- accepted text offsets (U64, n+1)
- accepted text bytes (U8)
- prevrpt (I32)
- nciks (I32)
- afs text offsets (U64, n+1)
- afs text bytes (U8)
- afs validity (U8, 0 = NULL)
- wksi (I32)
- fye text offsets (U64, n+1)
- fye text bytes (U8)
- fye validity (U8, 0 = NULL)
- instance text offsets (U64, n+1)
- instance text bytes (U8)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
