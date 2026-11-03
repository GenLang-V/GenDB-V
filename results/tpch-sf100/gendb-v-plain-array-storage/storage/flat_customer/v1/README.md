# Storage `flat_customer`

fixed flat storage of customer: every column as a plain typed array in source row order, one part per column, two (offsets, bytes) per text column

Units: bigint I64, integer I32, date I32 days since 1970-01-01, numeric I128 coefficient at the declared scale, text I64 offsets into U8 UTF-8 bytes

## Tables and columns

- `customer`: c_custkey, c_name, c_address, c_nationkey, c_phone, c_acctbal, c_mktsegment, c_comment

## Parts

- C_CUSTKEY I64 of c_custkey
- C_NAME_OFFSETS I64 of c_name
- C_NAME_BYTES U8 of c_name
- C_ADDRESS_OFFSETS I64 of c_address
- C_ADDRESS_BYTES U8 of c_address
- C_NATIONKEY I64 of c_nationkey
- C_PHONE_OFFSETS I64 of c_phone
- C_PHONE_BYTES U8 of c_phone
- C_ACCTBAL I128 of c_acctbal
- C_MKTSEGMENT_OFFSETS I64 of c_mktsegment
- C_MKTSEGMENT_BYTES U8 of c_mktsegment
- C_COMMENT_OFFSETS I64 of c_comment
- C_COMMENT_BYTES U8 of c_comment

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
