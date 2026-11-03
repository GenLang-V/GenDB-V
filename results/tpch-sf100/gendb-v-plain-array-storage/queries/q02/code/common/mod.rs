//! General verified building blocks of this query (no query constants): preallocated worker output buffers,
//! key lookup in a key column, and a read-only key set for membership probes.
pub mod slot_buffer;
pub mod key_lookup;
pub mod key_set;
pub mod collect;
pub mod relations;
pub mod like_suffix;
pub mod least_per_key;
