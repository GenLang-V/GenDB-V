//! The code convention of the lookups: `NONE` (absent) as -1.
use vstd::prelude::*;
use crate::agent::common::dictmap::NONE;

verus! {

/// A code, or -1 for `NONE`.
pub open spec fn tvi(m: u64) -> int { if m == NONE { -1 } else { m as int } }

} // verus!
