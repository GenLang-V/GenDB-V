//! General builder modules (no query constants, no single layout): parallel merge sort, sorted text
//! dictionaries, pair dictionaries and clustering keys, column copies, gathers and sort permutations.
pub use crate::stores::tag::interface::common as icommon;
pub mod columns;
pub mod dict;
pub mod gather;
pub mod keys;
pub mod sort;
