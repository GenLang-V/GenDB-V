//! General helpers (no query constants): bit sets, even range splits, zero-filled buffers, range sums, the
//! two-character text prefix and the integer form of a comparison with AVG, and
//! cache-friendly marking of the keys of a slice range in a bit set.
pub mod bitset;
pub mod split;
pub mod zeroed;
pub mod rsum;
pub mod prefix2;
pub mod avg_threshold;
pub mod slice_marks;
