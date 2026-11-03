//! Vectors of one repeated value through `vec![x; n]` (the standard library's fill, which uses a zeroed allocation
//! or a memset instead of a push per element), and a copy of a vector.
use vstd::prelude::*;

verus! {

/// `n` copies of `x`.
pub fn fill_usize(n: usize, x: usize) -> (v: Vec<usize>)
    ensures v@ == Seq::new(n as nat, |_i: int| x),
{
    let v = vec![x; n];
    proof {
        assert forall|i: int| 0 <= i < n implies #[trigger] v@[i] == x by {
            assert(vstd::pervasive::cloned(x, v@[i]));
        }
        assert(v@ =~= Seq::new(n as nat, |_i: int| x));
    }
    v
}

/// `n` copies of `x`.
pub fn fill_u32(n: usize, x: u32) -> (v: Vec<u32>)
    ensures v@ == Seq::new(n as nat, |_i: int| x),
{
    let v = vec![x; n];
    proof {
        assert forall|i: int| 0 <= i < n implies #[trigger] v@[i] == x by {
            assert(vstd::pervasive::cloned(x, v@[i]));
        }
        assert(v@ =~= Seq::new(n as nat, |_i: int| x));
    }
    v
}

/// `n` copies of `x`.
pub fn fill_u64(n: usize, x: u64) -> (v: Vec<u64>)
    ensures v@ == Seq::new(n as nat, |_i: int| x),
{
    let v = vec![x; n];
    proof {
        assert forall|i: int| 0 <= i < n implies #[trigger] v@[i] == x by {
            assert(vstd::pervasive::cloned(x, v@[i]));
        }
        assert(v@ =~= Seq::new(n as nat, |_i: int| x));
    }
    v
}

/// A copy of `v`.
pub fn copy_usize(v: &Vec<usize>) -> (r: Vec<usize>)
    ensures r@ == v@,
{
    let n = v.len();
    let mut r: Vec<usize> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            n == v@.len(),
            i <= n,
            r@ == v@.subrange(0, i as int),
        decreases n - i,
    {
        r.push(v[i]);
        proof { assert(r@ =~= v@.subrange(0, i + 1)); }
        i = i + 1;
    }
    proof { assert(v@.subrange(0, n as int) =~= v@); }
    r
}

} // verus!
