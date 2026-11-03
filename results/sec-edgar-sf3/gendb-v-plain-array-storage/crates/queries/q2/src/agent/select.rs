//! Heuristic selection of a threshold: the `k`-th largest of a list of coefficients (three-way quickselect on a
//! copy). Only its safety is proved; the callers' results are exact for every threshold they are given.
use vstd::prelude::*;

verus! {

/// About the `k`-th largest value of `v` (`1 <= k <= v.len()`): quickselect on a copy.
pub fn kth_largest(v: &Vec<i128>, k: usize) -> (r: i128)
    requires 1 <= k <= v@.len(),
{
    let mut a = v.clone();
    let n = a.len();
    let target = k - 1;
    let mut lo: usize = 0;
    let mut hi: usize = n;
    while hi - lo > 1
        invariant
            a@.len() == n,
            lo <= target < hi <= n,
        decreases hi - lo,
    {
        let pivot = a[lo + (hi - lo) / 2];
        // Three-way partition of a[lo..hi] in descending order: [lo, gt) above the pivot, [gt, i) equal to it,
        // [lt, hi) below it.
        let mut gt: usize = lo;
        let mut i: usize = lo;
        let mut lt: usize = hi;
        while i < lt
            invariant
                a@.len() == n,
                lo <= gt <= i <= lt <= hi <= n,
            decreases lt - i,
        {
            let x = a[i];
            if x > pivot {
                let y = a[gt];
                a.set(gt, x);
                a.set(i, y);
                gt = gt + 1;
                i = i + 1;
            } else if x < pivot {
                lt = lt - 1;
                let y = a[lt];
                a.set(lt, x);
                a.set(i, y);
            } else {
                i = i + 1;
            }
        }
        if target < gt {
            if gt >= hi {
                return pivot;
            }
            hi = gt;
        } else if target < i {
            return pivot;
        } else {
            if i <= lo {
                return pivot;
            }
            lo = i;
        }
    }
    a[lo]
}

} // verus!
