# Storage `cust_phoneidx`

custpart unchanged (50 inherited parts), then a U32 permutation of the customer rows grouped by country code (first two characters of c_phone; rows ascending within a code) and the U64 starts of its runs

Units: permutation entries are stored (= canonical) customer row positions of custpart; run starts are positions in the permutation

## Tables and columns

- `customer`: c_phone

## Parts

- PHONE_PERM (U32, one per customer row or empty): the customer rows ordered by SUBSTRING(c_phone, 1, 2) (stable: ascending row within a code)
- PHONE_RUNS (U64, m + 1 run starts from 0 to n, or empty): every run of PHONE_PERM holds rows of one country code

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
