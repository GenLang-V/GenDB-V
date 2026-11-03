//! Position of a key in an `i64` key column: first the dense guess `k - keys[0]` (exact when the keys are
//! consecutive from `keys[0]`, as dbgen writes them), verified by reading that one position, otherwise a linear
//! scan. The result never depends on the guess being right; it is only fast when it is.
use vstd::prelude::*;

verus! {

/// Some position of `k` in `keys`, or `None` exactly when `k` does not occur. `n` is `keys.len()` (passed in
/// because slice `len` is not `no_unwind`).
pub fn find_key(keys: &[i64], n: usize, k: i64) -> (r: Option<usize>)
    requires n == keys@.len(),
    ensures
        r matches Some(i) ==> i < keys@.len() && keys@[i as int] == k,
        r is None ==> forall|i: int| 0 <= i < keys@.len() ==> keys@[i] != k,
    no_unwind
{
    if n == 0 {
        return None;
    }
    let guess: i128 = k as i128 - keys[0] as i128;
    if 0 <= guess && guess < n as i128 {
        let g = guess as usize;
        if keys[g] == k {
            return Some(g);
        }
    }
    let mut i: usize = 0;
    while i < n
        invariant
            n == keys@.len(),
            i <= n,
            forall|j: int| 0 <= j < i ==> keys@[j] != k,
        decreases n - i,
    {
        if keys[i] == k {
            return Some(i);
        }
        i = i + 1;
    }
    None
}

} // verus!
