# Storage `flat_pre`

fixed flat storage of pre: every column as a plain typed array in source row order, one part per column, two (offsets, bytes) per text column

Units: bigint I64, integer I32, date I32 days since 1970-01-01, numeric I128 coefficient at the declared scale, text I64 offsets into U8 UTF-8 bytes

## Tables and columns

- `pre`: adsh, report, line, stmt, inpth, rfile, tag, version, plabel, negating

## Parts

- ADSH_OFFSETS I64 of adsh
- ADSH_BYTES U8 of adsh
- REPORT I32 of report
- LINE I32 of line
- STMT_OFFSETS I64 of stmt
- STMT_BYTES U8 of stmt
- STMT_VALIDITY U8 of stmt
- INPTH I32 of inpth
- RFILE_OFFSETS I64 of rfile
- RFILE_BYTES U8 of rfile
- TAG_OFFSETS I64 of tag
- TAG_BYTES U8 of tag
- VERSION_OFFSETS I64 of version
- VERSION_BYTES U8 of version
- PLABEL_OFFSETS I64 of plabel
- PLABEL_BYTES U8 of plabel
- PLABEL_VALIDITY U8 of plabel
- NEGATING I32 of negating

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
