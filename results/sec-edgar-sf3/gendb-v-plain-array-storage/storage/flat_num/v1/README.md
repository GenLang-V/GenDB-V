# Storage `flat_num`

fixed flat storage of num: every column as a plain typed array in source row order, one part per column, two (offsets, bytes) per text column

Units: bigint I64, integer I32, date I32 days since 1970-01-01, numeric I128 coefficient at the declared scale, text I64 offsets into U8 UTF-8 bytes

## Tables and columns

- `num`: adsh, tag, version, ddate, qtrs, uom, coreg, value, footnote

## Parts

- ADSH_OFFSETS I64 of adsh
- ADSH_BYTES U8 of adsh
- TAG_OFFSETS I64 of tag
- TAG_BYTES U8 of tag
- VERSION_OFFSETS I64 of version
- VERSION_BYTES U8 of version
- DDATE I32 of ddate
- QTRS I32 of qtrs
- UOM_OFFSETS I64 of uom
- UOM_BYTES U8 of uom
- COREG_OFFSETS I64 of coreg
- COREG_BYTES U8 of coreg
- COREG_VALIDITY U8 of coreg
- VALUE I128 of value
- FOOTNOTE_OFFSETS I64 of footnote
- FOOTNOTE_BYTES U8 of footnote
- FOOTNOTE_VALIDITY U8 of footnote

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
