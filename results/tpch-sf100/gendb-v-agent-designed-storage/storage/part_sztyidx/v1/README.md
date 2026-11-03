# Storage `part_sztyidx`

A secondary composite index of part on (p_size, p_type): a dense directory over the keys (kmin + e / T, key text e % T), e < nkeys, whose entry e is a range of a permutation of the canonical part rows holding exactly the rows with that key, in increasing row order; the T key texts of p_type are stored once as the index's key dictionary.

Units: p_size keys are bigint values; offsets are positions in the permutation (U32); permutation entries are canonical part row numbers (U32); key texts are bytes

## Tables and columns

- `part`: p_size, p_type

## Parts

- part: I64 [mode, kmin]: index mode (1: dense composite directory) and smallest p_size
- part: U32 directory offsets into the permutation, one per composite key (p_size = kmin + e / T, p_type = key text e % T), nkeys + 1 entries (mode 1)
- part: U32 permutation of canonical part rows ordered by (p_size, p_type key, row) (mode 1)
- part: U64 offsets of the T p_type key texts of the index (T + 1 entries)
- part: U8 bytes of the p_type key texts of the index
- part: I64 per-row p_size keys (fallback mode only; empty in mode 1)
- part: U64 per-row p_type key numbers (fallback mode only; empty in mode 1)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
