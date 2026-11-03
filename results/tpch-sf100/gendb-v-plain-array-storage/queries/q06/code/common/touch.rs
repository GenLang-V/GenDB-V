//! Cache warming for selection vectors: read the `i128` column values of the rows of a list (offsets from a block
//! start in a `u32` buffer) and fold their low 64 bits into a wrapping checksum that has no meaning.
//!
//! The loop is short (a few instructions per row) with independent loads, so many cache misses are in flight at
//! once; the stage that then needs the values finds their lines in the cache. The checksum must reach a later
//! decision of the caller (any decision that is correct for every value), or the compiler drops the reads.
use vstd::prelude::*;

verus! {

/// The wrapping sum of the low 64 bits of `col[base + sel[j]]` over `j < k` (`col` holds `n` values).
pub fn touch_i128(col: &[i128], n: usize, base: usize, k: usize, sel: &Vec<u32>) -> (t: u64)
    requires
        col@.len() == n,
        k <= sel@.len(),
        forall|j: int| 0 <= j < k ==> (base + (#[trigger] sel@[j]) as int) < n,
    no_unwind
{
    let mut t: u64 = 0;
    let mut j: usize = 0;
    while j < k
        invariant
            col@.len() == n,
            k <= sel@.len(),
            forall|j: int| 0 <= j < k ==> (base + (#[trigger] sel@[j]) as int) < n,
            j <= k,
        decreases k - j,
    {
        let r = base + sel[j] as usize;
        t = t.wrapping_add(col[r] as u64);
        j = j + 1;
    }
    t
}

} // verus!
