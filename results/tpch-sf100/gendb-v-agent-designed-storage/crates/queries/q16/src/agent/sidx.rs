//! Supplier row numbers in the pair buffers: `u32` when every supplier row number fits (half the memory traffic
//! of `u64`), else `u64`.
use vstd::prelude::*;

verus! {

pub trait SIdx: Copy + Send + Sync + 'static {
    /// The row number.
    spec fn sx(&self) -> int;

    /// Row numbers below `lim()` are representable.
    spec fn lim() -> int;

    fn zero() -> (r: Self)
        ensures r.sx() == 0,
        no_unwind;

    fn of_usize(x: usize) -> (r: Self)
        requires (x as int) < Self::lim(),
        ensures r.sx() == x as int,
        no_unwind;

    fn to_usize(&self) -> (r: usize)
        requires self.sx() <= usize::MAX,
        ensures r as int == self.sx(),
        no_unwind;
}

impl SIdx for u32 {
    open spec fn sx(&self) -> int {
        *self as int
    }

    open spec fn lim() -> int {
        0x1_0000_0000
    }

    fn zero() -> (r: u32) {
        0
    }

    fn of_usize(x: usize) -> (r: u32) {
        x as u32
    }

    fn to_usize(&self) -> (r: usize) {
        *self as usize
    }
}

impl SIdx for u64 {
    open spec fn sx(&self) -> int {
        *self as int
    }

    open spec fn lim() -> int {
        0x1_0000_0000_0000_0000
    }

    fn zero() -> (r: u64) {
        0
    }

    fn of_usize(x: usize) -> (r: u64) {
        x as u64
    }

    fn to_usize(&self) -> (r: usize) {
        *self as usize
    }
}

} // verus!
