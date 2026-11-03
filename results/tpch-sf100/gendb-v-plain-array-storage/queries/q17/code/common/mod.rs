//! General pieces of the query (no query constants, no storage layout): selection lists and range sums, sums over
//! products with a unique partner, 64-bit mask bits, and a key set with two
//! filters and a prefix-directory slot lookup.
pub mod selection;
pub mod sum_pick;
pub mod bits;
pub mod keyset;
