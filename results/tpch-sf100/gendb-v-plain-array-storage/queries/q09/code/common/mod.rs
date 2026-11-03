//! General pieces of the query (no query constants, no storage layout): sums over products with a unique partner
//! (single- and two-column keys), bit counts of 64-bit masks, `LIKE '%<lit>%'` as a byte-substring test, and a one-pass substring bitmap over a run of text values.
pub mod sum_pick;
pub mod like_contains;
pub mod bits;
pub mod popc;
pub mod split;
pub mod zeroed;
pub mod text_scan;
