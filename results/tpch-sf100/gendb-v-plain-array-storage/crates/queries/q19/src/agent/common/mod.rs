//! General pieces of the query (no query constants, no storage layout): selection lists and range sums, sums over
//! products with a unique partner, 64-bit mask bits and trailing zeros, text equality with a byte string, and a table
//! from keys to small tags with open addressing.
pub mod selection;
pub mod sum_pick;
pub mod bits;
pub mod tz;
pub mod text_eq;
pub mod key_tags;
