# Storage `supp_trisig`

suppliers unchanged (48 inherited parts), plus one U64 part: the 128-bit trigram signature of s_comment of every canonical supplier row, two words per row

Units: bit h(a,b,c) (0..128, word h/64, position h%64) of a row's signature is set iff some three consecutive bytes a,b,c of its s_comment hash to h (Knuth multiplicative hash, as factext_trisig)

## Tables and columns

- `partsupp`: ps_partkey, ps_suppkey, ps_availqty, ps_supplycost, ps_comment
- `supplier`: s_suppkey, s_name, s_address, s_nationkey, s_phone, s_acctbal, s_comment
- `nation`: n_nationkey, n_name, n_regionkey, n_comment
- `region`: r_regionkey, r_name, r_comment

## Parts

- SUPP_SIG (U64, 2 per supplier row): the 128-bit byte-trigram Bloom signature of s_comment of every canonical supplier row, words of row r at 2r and 2r+1

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
