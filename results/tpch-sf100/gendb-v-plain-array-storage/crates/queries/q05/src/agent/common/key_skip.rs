//! Skipping a run of `i64` keys that lie in a half-open interval `[lo, hi)`: `skip_run` advances over blocks of
//! `SKIP_BLK` keys whose keys all lie in the interval, testing each block without branches (one conjunction over the
//! block, which the compiler turns into vector compares). It stops at the first block holding a key outside the
//! interval (or when fewer than `SKIP_BLK` keys are left); the caller handles the rest key by key. `no_unwind`.
use vstd::prelude::*;

verus! {

/// Keys per tested block.
pub const SKIP_BLK: usize = 16;

/// Whether all keys of `keys[row..row + SKIP_BLK)` lie in `[lo, hi)` (a conjunction without early exit, which
/// the compiler turns into vector compares).
fn block_in(keys: &[i64], row: usize, lo: i64, hi: i64) -> (ok: bool)
    requires row + SKIP_BLK <= keys@.len(), row + SKIP_BLK <= usize::MAX,
    ensures ok ==> forall|y: int| row <= y < row + SKIP_BLK ==> lo <= #[trigger] keys@[y] < hi,
    no_unwind
{
    let mut ok = true;
    let mut p: usize = 0;
    while p < SKIP_BLK
        invariant
            p <= SKIP_BLK, row + SKIP_BLK <= keys@.len(), row + SKIP_BLK <= usize::MAX,
            ok ==> forall|y: int| row <= y < row + p ==> lo <= #[trigger] keys@[y] < hi,
        decreases SKIP_BLK - p,
    {
        let k = keys[row + p];
        ok = ok && lo <= k && k < hi;
        p = p + 1;
    }
    ok
}

/// The end `row` of the longest run of whole blocks from `row0` (below `end`) whose keys all lie in `[lo, hi)`.
pub fn skip_run(keys: &[i64], row0: usize, end: usize, lo: i64, hi: i64) -> (row: usize)
    requires row0 <= end <= keys@.len(),
    ensures row0 <= row <= end, forall|y: int| row0 <= y < row ==> lo <= #[trigger] keys@[y] < hi,
    no_unwind
{
    let mut row = row0;
    let mut stop = false;
    while !stop && end - row >= SKIP_BLK
        invariant
            row0 <= row <= end <= keys@.len(),
            forall|y: int| row0 <= y < row ==> lo <= #[trigger] keys@[y] < hi,
        decreases end - row, if stop { 0int } else { 1int },
    {
        if block_in(keys, row, lo, hi) {
            row = row + SKIP_BLK;
        } else {
            stop = true;
        }
    }
    row
}

/// The first row `row >= row0` (below `end`) whose key lies outside `[lo, hi)`, or `end`: whole blocks first
/// (`skip_run`), then key by key.
pub fn skip_to(keys: &[i64], row0: usize, end: usize, lo: i64, hi: i64) -> (row: usize)
    requires row0 <= end <= keys@.len(),
    ensures
        row0 <= row <= end,
        forall|y: int| row0 <= y < row ==> lo <= #[trigger] keys@[y] < hi,
        row < end ==> !(lo <= keys@[row as int] < hi),
    no_unwind
{
    let mut row = skip_run(keys, row0, end, lo, hi);
    while row < end && lo <= keys[row] && keys[row] < hi
        invariant
            row0 <= row <= end <= keys@.len(),
            forall|y: int| row0 <= y < row ==> lo <= #[trigger] keys@[y] < hi,
        decreases end - row,
    {
        row = row + 1;
    }
    row
}

} // verus!
