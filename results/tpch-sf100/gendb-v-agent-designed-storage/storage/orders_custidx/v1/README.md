# Storage `orders_custidx`

A secondary index of orders on o_custkey: a dense directory over the key range [kmin, kmin + nkeys) whose entry e is a range of a permutation of the canonical orders rows; the range holds exactly the rows whose o_custkey is kmin + e (so its length is their number).

Units: keys are bigint o_custkey values; offsets are positions in the permutation (U32); permutation entries are canonical orders row numbers (U32)

## Tables and columns

- `orders`: o_custkey

## Parts

- orders: I64 [mode, kmin]: index mode (1: dense directory) and smallest key
- orders: U32 directory offsets into the permutation, one per key kmin + e (mode 1), nkeys + 1 entries
- orders: U32 permutation of canonical orders rows grouped by o_custkey (mode 1)
- orders: I64 per-row keys (mode 0 fallback only; empty in mode 1)

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
