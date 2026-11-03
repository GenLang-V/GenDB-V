# Storage `flat_tag`

fixed flat storage of tag: every column as a plain typed array in source row order, one part per column, two (offsets, bytes) per text column

Units: bigint I64, integer I32, date I32 days since 1970-01-01, numeric I128 coefficient at the declared scale, text I64 offsets into U8 UTF-8 bytes

## Tables and columns

- `tag`: tag, version, custom, abstract, datatype, iord, crdr, tlabel, doc

## Parts

- TAG_OFFSETS I64 of tag
- TAG_BYTES U8 of tag
- VERSION_OFFSETS I64 of version
- VERSION_BYTES U8 of version
- CUSTOM I32 of custom
- ABSTRACT I32 of abstract
- DATATYPE_OFFSETS I64 of datatype
- DATATYPE_BYTES U8 of datatype
- DATATYPE_VALIDITY U8 of datatype
- IORD_OFFSETS I64 of iord
- IORD_BYTES U8 of iord
- CRDR_OFFSETS I64 of crdr
- CRDR_BYTES U8 of crdr
- CRDR_VALIDITY U8 of crdr
- TLABEL_OFFSETS I64 of tlabel
- TLABEL_BYTES U8 of tlabel
- TLABEL_VALIDITY U8 of tlabel
- DOC_OFFSETS I64 of doc
- DOC_BYTES U8 of doc
- DOC_VALIDITY U8 of doc

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
