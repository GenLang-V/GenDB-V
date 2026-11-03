//! General modules of this crate (no query constants, no storage layout): WHERE / GROUP BY links under an outer
//! context, MAX over same-scale numerics, selection vectors over row ranges and from 64-row bitmasks, an exact SUM accumulator with saturating mass.
pub mod group_ctx;
pub mod max_num;
pub mod selection;
pub mod accum;
pub mod bitsel;
