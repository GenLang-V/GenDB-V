//! General verified helpers of this query (no query constants): byte strings and hashing, a saturating SUM/COUNT
//! accumulator, chained hash indexes with bitmap filters, bucketing by partition, and lazily zeroed buffers.
pub mod bytes;
pub mod satacc;
pub mod chain;
pub mod bits;
pub mod lazy;
