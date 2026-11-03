//! Least value per key: the positions `i` whose value is at most the value of every position with the same key
//! (all ties kept), in increasing order. When the keys are non-decreasing (as when entries arrive grouped by key)
//! each key's positions form one run and a single pass suffices; otherwise every position is compared with every
//! other one.
use vstd::prelude::*;

verus! {

/// Position `i`'s value is least among the positions with its key.
pub open spec fn least_at(keys: Seq<i64>, vals: Seq<i128>, i: int) -> bool {
    forall|j: int| 0 <= j < keys.len() && #[trigger] keys[j] == keys[i] ==> vals[i] <= vals[j]
}

/// `out` lists, in increasing order, exactly the positions whose value is least for their key.
pub open spec fn least_list(keys: Seq<i64>, vals: Seq<i128>, out: Seq<usize>) -> bool {
    &&& forall|q: int| 0 <= q < out.len() ==> (#[trigger] out[q]) < keys.len() && least_at(keys, vals, out[q] as int)
    &&& forall|q: int, r: int| 0 <= q < r < out.len() ==> out[q] < out[r]
    &&& forall|i: int| 0 <= i < keys.len() && #[trigger] least_at(keys, vals, i) ==> exists|q: int| 0 <= q < out.len() && out[q] == i
}

/// Keys are non-decreasing.
pub open spec fn nondecreasing(keys: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < keys.len() ==> keys[i] <= keys[j]
}

fn is_nondecreasing(keys: &Vec<i64>) -> (r: bool)
    ensures r == nondecreasing(keys@),
{
    let n = keys.len();
    if n == 0 {
        return true;
    }
    let mut i: usize = 1;
    while i < n
        invariant
            n == keys@.len(),
            1 <= i <= n,
            forall|a: int, b: int| 0 <= a <= b < i ==> keys@[a] <= keys@[b],
        decreases n - i,
    {
        if keys[i - 1] > keys[i] {
            return false;
        }
        proof {
            assert forall|a: int, b: int| 0 <= a <= b < i + 1 implies keys@[a] <= keys@[b] by {
                if b == i && a < i {
                    assert(keys@[a] <= keys@[i - 1]);
                }
            }
        }
        i = i + 1;
    }
    true
}

/// Appending position `i` (above every listed one) keeps the list increasing.
proof fn lemma_push_increasing(out: Seq<usize>, i: usize)
    requires
        forall|q: int, r: int| 0 <= q < r < out.len() ==> out[q] < out[r],
        forall|q: int| 0 <= q < out.len() ==> out[q] < i,
    ensures forall|q: int, r: int| 0 <= q < r < out.push(i).len() ==> out.push(i)[q] < out.push(i)[r],
{
}

/// The positions whose value is least for their key (see the module comment).
pub fn least_per_key(keys: &Vec<i64>, vals: &Vec<i128>) -> (out: Vec<usize>)
    requires keys@.len() == vals@.len(),
    ensures least_list(keys@, vals@, out@),
{
    let n = keys.len();
    let mut out: Vec<usize> = Vec::with_capacity(n);
    if is_nondecreasing(keys) {
        let mut s0: usize = 0;
        while s0 < n
            invariant
                n == keys@.len(), n == vals@.len(),
                nondecreasing(keys@),
                s0 <= n,
                0 < s0 < n ==> keys@[s0 - 1] < keys@[s0 as int],
                forall|q: int| 0 <= q < out@.len() ==> (#[trigger] out@[q]) < s0 && least_at(keys@, vals@, out@[q] as int),
                forall|q: int, r: int| 0 <= q < r < out@.len() ==> out@[q] < out@[r],
                forall|i: int| 0 <= i < s0 && #[trigger] least_at(keys@, vals@, i) ==> exists|q: int| 0 <= q < out@.len() && out@[q] == i,
            decreases n - s0,
        {
            // The run of key `k` is [s0, s1); `mn` is its least value.
            let k = keys[s0];
            let mut mn = vals[s0];
            let mut s1 = s0 + 1;
            while s1 < n && keys[s1] == k
                invariant
                    n == keys@.len(), n == vals@.len(),
                    s0 < s1 <= n,
                    k == keys@[s0 as int],
                    forall|j: int| #![trigger keys@[j]] #![trigger vals@[j]] s0 <= j < s1 ==> keys@[j] == k && mn <= vals@[j],
                    exists|j: int| s0 <= j < s1 && vals@[j] == mn,
                decreases n - s1,
            {
                let ghost old_mn = mn;
                assert(keys@[s1 as int] == k);
                if vals[s1] < mn {
                    mn = vals[s1];
                }
                proof {
                    assert forall|j: int| s0 <= j < s1 + 1 implies keys@[j] == k && mn <= vals@[j] by {
                        if j < s1 { assert(old_mn <= vals@[j]); }
                    }
                    if mn == old_mn {
                        let x = choose|x: int| s0 <= x < s1 && vals@[x] == old_mn;
                        assert(s0 <= x < s1 + 1 && vals@[x] == mn);
                    } else {
                        assert(vals@[s1 as int] == mn);
                    }
                }
                s1 = s1 + 1;
            }
            proof {
                // Every position with key `k` lies in the run.
                assert forall|j: int| 0 <= j < n && keys@[j] == k implies s0 <= j < s1 by {
                    if j < s0 {
                        assert(keys@[j] <= keys@[s0 - 1]);
                    }
                    if j >= s1 {
                        assert(keys@[s1 as int] <= keys@[j]);
                        assert(keys@[s1 as int] != k);
                        assert(k <= keys@[s1 as int]);
                    }
                }
            }
            let mut j = s0;
            while j < s1
                invariant
                    n == keys@.len(), n == vals@.len(),
                    s0 <= j <= s1 <= n,
                    k == keys@[s0 as int],
                    forall|x: int| #![trigger keys@[x]] #![trigger vals@[x]] s0 <= x < s1 ==> keys@[x] == k && mn <= vals@[x],
                    exists|x: int| s0 <= x < s1 && vals@[x] == mn,
                    forall|x: int| 0 <= x < n && keys@[x] == k ==> s0 <= x < s1,
                    forall|q: int| 0 <= q < out@.len() ==> (#[trigger] out@[q]) < j && least_at(keys@, vals@, out@[q] as int),
                    forall|q: int, r: int| 0 <= q < r < out@.len() ==> out@[q] < out@[r],
                    forall|i: int| 0 <= i < j && #[trigger] least_at(keys@, vals@, i) ==> exists|q: int| 0 <= q < out@.len() && out@[q] == i,
                decreases s1 - j,
            {
                let ghost before = out@;
                proof {
                    // Least for its key exactly when equal to the run's minimum.
                    let x0 = choose|x: int| s0 <= x < s1 && vals@[x] == mn;
                    if least_at(keys@, vals@, j as int) {
                        assert(keys@[x0] == keys@[j as int]);
                    }
                    if vals@[j as int] == mn {
                        assert forall|x: int| 0 <= x < keys@.len() && #[trigger] keys@[x] == keys@[j as int] implies vals@[j as int] <= vals@[x] by {}
                    }
                }
                if vals[j] == mn {
                    proof { lemma_push_increasing(out@, j); }
                    out.push(j);
                    proof {
                        assert forall|i: int| 0 <= i < j + 1 && #[trigger] least_at(keys@, vals@, i) implies exists|q: int| 0 <= q < out@.len() && out@[q] == i by {
                            if i < j {
                                let q = choose|q: int| 0 <= q < before.len() && before[q] == i;
                                assert(out@[q] == i);
                            } else {
                                assert(out@[before.len() as int] == i);
                            }
                        }
                    }
                }
                j = j + 1;
            }
            s0 = s1;
        }
    } else {
        // Unsorted keys: compare every position with every other one.
        let mut i: usize = 0;
        while i < n
            invariant
                n == keys@.len(), n == vals@.len(),
                i <= n,
                forall|q: int| 0 <= q < out@.len() ==> (#[trigger] out@[q]) < i && least_at(keys@, vals@, out@[q] as int),
                forall|q: int, r: int| 0 <= q < r < out@.len() ==> out@[q] < out@[r],
                forall|x: int| 0 <= x < i && #[trigger] least_at(keys@, vals@, x) ==> exists|q: int| 0 <= q < out@.len() && out@[q] == x,
            decreases n - i,
        {
            let mut least = true;
            let mut j: usize = 0;
            while j < n
                invariant
                    n == keys@.len(), n == vals@.len(),
                    i < n,
                    j <= n,
                    least == forall|x: int| 0 <= x < j && #[trigger] keys@[x] == keys@[i as int] ==> vals@[i as int] <= vals@[x],
                decreases n - j,
            {
                if keys[j] == keys[i] && vals[j] < vals[i] {
                    least = false;
                }
                j = j + 1;
            }
            let ghost before = out@;
            if least {
                proof { lemma_push_increasing(out@, i); }
                out.push(i);
            }
            proof {
                assert forall|x: int| 0 <= x < i + 1 && #[trigger] least_at(keys@, vals@, x) implies exists|q: int| 0 <= q < out@.len() && out@[q] == x by {
                    if x < i {
                        let q = choose|q: int| 0 <= q < before.len() && before[q] == x;
                        assert(out@[q] == x);
                    } else {
                        assert(out@[before.len() as int] == x);
                    }
                }
            }
            i = i + 1;
        }
    }
    out
}

} // verus!
