# Storage `part_nameidx`

custpart unchanged (50 inherited parts), then one U32 part: a permutation of the part rows sorted by p_name (bytewise, ties in any order)

Units: permutation entries are stored (= canonical) part row positions of custpart

## Tables and columns

- `part`: p_partkey, p_name

## Parts

- NAME_PERM (U32, one per part row or empty): the stored part rows in nondecreasing bytewise p_name order

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
