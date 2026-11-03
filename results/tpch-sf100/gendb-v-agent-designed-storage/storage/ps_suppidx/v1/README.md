# Storage `ps_suppidx`

A secondary index of partsupp on ps_suppkey: a dense directory over the key range [kmin, kmin + nkeys) whose entry e is a range of a permutation of the canonical partsupp rows; the range holds exactly the rows whose ps_suppkey is kmin + e (ascending rows).

Units: keys are bigint ps_suppkey values; offsets are positions in the permutation (U32); permutation entries are canonical partsupp row numbers (U32)

## Tables and columns

- `partsupp`: ps_suppkey

## Parts

- partsupp: I64 [mode, kmin]: index mode (1: dense directory) and smallest ps_suppkey
- partsupp: U32 directory offsets into the permutation, one per key kmin + e (mode 1), nkeys + 1 entries
- partsupp: U32 permutation of canonical partsupp rows grouped by ps_suppkey (ascending row within a key; mode 1)
- partsupp: I64 per-row keys (mode 0 fallback only; empty in mode 1)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
