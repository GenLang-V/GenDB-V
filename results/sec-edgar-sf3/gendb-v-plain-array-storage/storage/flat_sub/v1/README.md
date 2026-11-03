# Storage `flat_sub`

fixed flat storage of sub: every column as a plain typed array in source row order, one part per column, two (offsets, bytes) per text column

Units: bigint I64, integer I32, date I32 days since 1970-01-01, numeric I128 coefficient at the declared scale, text I64 offsets into U8 UTF-8 bytes

## Tables and columns

- `sub`: adsh, cik, name, sic, countryba, stprba, cityba, countryinc, form, period, fy, fp, filed, accepted, prevrpt, nciks, afs, wksi, fye, instance

## Parts

- ADSH_OFFSETS I64 of adsh
- ADSH_BYTES U8 of adsh
- CIK I32 of cik
- NAME_OFFSETS I64 of name
- NAME_BYTES U8 of name
- SIC I32 of sic
- SIC_VALIDITY U8 of sic
- COUNTRYBA_OFFSETS I64 of countryba
- COUNTRYBA_BYTES U8 of countryba
- COUNTRYBA_VALIDITY U8 of countryba
- STPRBA_OFFSETS I64 of stprba
- STPRBA_BYTES U8 of stprba
- STPRBA_VALIDITY U8 of stprba
- CITYBA_OFFSETS I64 of cityba
- CITYBA_BYTES U8 of cityba
- CITYBA_VALIDITY U8 of cityba
- COUNTRYINC_OFFSETS I64 of countryinc
- COUNTRYINC_BYTES U8 of countryinc
- COUNTRYINC_VALIDITY U8 of countryinc
- FORM_OFFSETS I64 of form
- FORM_BYTES U8 of form
- PERIOD I32 of period
- PERIOD_VALIDITY U8 of period
- FY I32 of fy
- FY_VALIDITY U8 of fy
- FP_OFFSETS I64 of fp
- FP_BYTES U8 of fp
- FP_VALIDITY U8 of fp
- FILED I32 of filed
- ACCEPTED_OFFSETS I64 of accepted
- ACCEPTED_BYTES U8 of accepted
- PREVRPT I32 of prevrpt
- NCIKS I32 of nciks
- AFS_OFFSETS I64 of afs
- AFS_BYTES U8 of afs
- AFS_VALIDITY U8 of afs
- WKSI I32 of wksi
- FYE_OFFSETS I64 of fye
- FYE_BYTES U8 of fye
- FYE_VALIDITY U8 of fye
- INSTANCE_OFFSETS I64 of instance
- INSTANCE_BYTES U8 of instance

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
