# Storage `factext_trislice`

factext_trisig unchanged (13 inherited parts: factext's 12 and the per-row signatures), plus two U64 parts: signature words 0 and 1 of every orders row bit-sliced into 64 row bitmaps (planes) each, ceil(rows / 64) words per plane, plane-major

Units: plane q (0..64) of part h (0, 1) = bit q of signature word h (ORDERS_SIG word 2 r + h); word w of a plane holds rows 64 w .. 64 w + 63, row r at bit r % 64; padding bits past the last row are 0

## Tables and columns

- `lineitem`: l_comment
- `orders`: o_clerk, o_comment

## Parts

- orders: U64 bit-sliced word 0 of the 128-bit trigram signatures of o_comment: 64 planes (signature bits 0..64) of ceil(rows / 64) words; bit r % 64 of word q * ceil(rows / 64) + r / 64 is bit q of signature word 0 of canonical row r
- orders: U64 bit-sliced word 1 of the signatures: 64 planes (signature bits 64..128), the same layout

## Code

- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.
- [`builder/`](builder/): the verified builder.
