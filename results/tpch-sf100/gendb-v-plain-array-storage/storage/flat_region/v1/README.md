# Storage `flat_region`

fixed flat storage of region: every column as a plain typed array in source row order, one part per column, two (offsets, bytes) per text column

Units: bigint I64, integer I32, date I32 days since 1970-01-01, numeric I128 coefficient at the declared scale, text I64 offsets into U8 UTF-8 bytes

## Tables and columns

- `region`: r_regionkey, r_name, r_comment

## Parts

- R_REGIONKEY I64 of r_regionkey
- R_NAME_OFFSETS I64 of r_name
- R_NAME_BYTES U8 of r_name
- R_COMMENT_OFFSETS I64 of r_comment
- R_COMMENT_BYTES U8 of r_comment

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
