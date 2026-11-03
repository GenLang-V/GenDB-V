//! General verified building blocks of this query (no query constants): relation facts (kept rows, products),
//! key lookup in a key column (dense, sorted, linear), an exact `i128` SUM accumulator with mass tracking and a
//! bitmap of flags, a vectorizable skip over keys inside an interval, and range masks with set-bit iteration.
pub mod relations;
pub mod key_lookup;
pub mod lookup;
pub mod exact_sum;
pub mod bitmap;
pub mod key_skip;
pub mod bitscan;
