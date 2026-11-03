//! General pieces of the query (no query constants, no storage layout): `LIKE` with the backslash escape on plain
//! patterns and the two-segment pattern `'%a%b%'` as a byte test; GROUP BY with `COUNT(DISTINCT e)` over integer and
//! text keys.
pub mod like_two;
pub mod group_distinct;
pub mod text_dict;
pub mod bitset;
pub mod slot_buffer;
pub mod split;
pub mod key_group;
pub mod sort_u64;
pub mod ranks;
pub mod word_cache;
pub mod byte_scan;
