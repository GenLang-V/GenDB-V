//! General pieces of the query (no query constants): sums over products with a unique partner, merge sort of
//! (value, key) pairs, bitmaps of `u64` words, kept rows.
pub mod sum_pick;
pub mod msort;
pub mod bitmap;
pub mod keep;
