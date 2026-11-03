# Storage `part_btsidx`

custpart unchanged (50 inherited parts), then a composite index of part on (p_brand, p_type, p_size): a dense directory over the key space of custpart's brand and type dictionaries and the p_size range, and the part rows in key order

Units: composite key e = (brand dictionary index * nt + type dictionary index) * ns + (p_size - smin), nt the type dictionary size; offsets are index positions (U32); permutation entries are part rows of custpart (U32)

## Tables and columns

- `part`: p_partkey, p_brand, p_size, p_type

## Parts

- IDX_META (I64 [mode, smin, ns]): mode 1 when the index is present, the smallest p_size and the number of p_size values of the key range
- IDX_OFFS (U32, nb * nt * ns + 1): dense directory over the composite key (brand index * nt + type index) * ns + (p_size - smin); entry e is the index positions offs[e] .. offs[e + 1]
- IDX_PERM (U32, one per part row): the part rows of custpart in (p_brand, p_type, p_size, row) order

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
