//! General modules (no query constants): per-key sums, the run scan with its parallel driver, and ORDER BY ..
//! LIMIT as a top-n selection.
pub mod keysum;
pub mod runscan;
pub mod runplan;
pub mod topk_spec;
