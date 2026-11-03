//! General modules of the query (no query constants): selection lists and range sums, rows kept by filters and
//! `= ANY`, `LIKE 'prefix%'` as a byte test, word bitmaps, even range splits, `trailing_zeros` for worker bodies, zeroed worker buffers, and row triples kept in key-range buckets.
pub mod selection;
pub mod rows;
pub mod like_prefix;
pub mod bitset;
pub mod split;
pub mod tz;
pub mod bigzero;
pub mod buckets;
