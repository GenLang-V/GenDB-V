//! General pieces of the query (no query constants, no storage layout): index sums over relation rows, zero-filled
//! vectors, ORDER BY .. LIMIT as a top-n selection, and bit facts of `u64` masks.
pub mod rowsum;
pub mod zeroed;
pub mod topk_spec;
pub mod bits64;
pub mod segmask;
