# Storage `flat_partsupp`

fixed flat storage of partsupp: every column as a plain typed array in source row order, one part per column, two (offsets, bytes) per text column

Units: bigint I64, integer I32, date I32 days since 1970-01-01, numeric I128 coefficient at the declared scale, text I64 offsets into U8 UTF-8 bytes

## Tables and columns

- `partsupp`: ps_partkey, ps_suppkey, ps_availqty, ps_supplycost, ps_comment

## Parts

- PS_PARTKEY I64 of ps_partkey
- PS_SUPPKEY I64 of ps_suppkey
- PS_AVAILQTY I64 of ps_availqty
- PS_SUPPLYCOST I128 of ps_supplycost
- PS_COMMENT_OFFSETS I64 of ps_comment
- PS_COMMENT_BYTES U8 of ps_comment

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
