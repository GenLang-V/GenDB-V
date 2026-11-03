//! General pieces of the query (no query constants, no storage layout): selection lists and range sums, sums over
//! products with a unique partner, `LIKE '<lit>%'` as a byte-prefix test, and 64-bit mask bits and trailing zeros.
pub mod selection;
pub mod sum_pick;
pub mod like_prefix;
pub mod bits;
pub mod tz;
