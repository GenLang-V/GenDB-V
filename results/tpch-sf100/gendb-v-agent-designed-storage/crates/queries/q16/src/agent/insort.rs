//! The fallback order of the groups (`order_slow`): group indices inserted one by one at their place by
//! descending count, ties by index. Quadratic; used only when the counts are too large for the counting sort of
//! `output::order_groups`.
use vstd::prelude::*;
use super::output::{Grp, perm_ok};

verus! {

/// Group `a` comes before group `b`.
pub open spec fn before(gs: Seq<Grp>, a: usize, b: usize) -> bool {
    gs[a as int].cnt > gs[b as int].cnt || (gs[a as int].cnt == gs[b as int].cnt && a < b)
}

pub fn order_slow(gs: &Vec<Grp>) -> (perm: Vec<usize>)
    ensures perm_ok(gs@, perm@),
{
    let n = gs.len();
    let mut perm: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == gs@.len(), i <= n, perm@.len() == i,
            forall|p: int| 0 <= p < perm@.len() ==> #[trigger] perm@[p] < i,
            forall|k: int| 0 <= k < i ==> #[trigger] perm@.contains(k as usize),
            forall|p: int, q: int| 0 <= p < q < perm@.len() ==> before(gs@, #[trigger] perm@[p], #[trigger] perm@[q]),
        decreases n - i,
    {
        let ci = gs[i].cnt;
        let mut pos: usize = 0;
        while pos < perm.len() && gs[perm[pos]].cnt >= ci
            invariant
                n == gs@.len(), i < n, perm@.len() == i, pos <= perm@.len(), ci == gs@[i as int].cnt,
                forall|p: int| 0 <= p < perm@.len() ==> #[trigger] perm@[p] < i,
                forall|p: int| 0 <= p < pos ==> before(gs@, #[trigger] perm@[p], i),
            decreases perm@.len() - pos,
        {
            pos = pos + 1;
        }
        let ghost old_perm = perm@;
        proof {
            old_perm.insert_ensures(pos as int, i);
            if pos < old_perm.len() {
                assert forall|q: int| pos <= q < old_perm.len() implies before(gs@, i, #[trigger] old_perm[q]) by {
                    if q > pos {
                        assert(before(gs@, old_perm[pos as int], old_perm[q]));
                    }
                }
            }
        }
        perm.insert(pos, i);
        proof {
            assert forall|p: int| 0 <= p < perm@.len() implies #[trigger] perm@[p] < i + 1 by {
                if p < pos {
                } else if p > pos {
                    assert(perm@[p] == old_perm[p - 1]);
                }
            }
            assert forall|k: int| 0 <= k < i + 1 implies #[trigger] perm@.contains(k as usize) by {
                if k < i {
                    assert(old_perm.contains(k as usize));
                    let p = choose|p: int| 0 <= p < old_perm.len() && old_perm[p] == k as usize;
                    if p < pos {
                        assert(perm@[p] == k as usize);
                    } else {
                        assert(perm@[p + 1] == k as usize);
                    }
                } else {
                    assert(perm@[pos as int] == k as usize);
                }
            }
            assert forall|p: int, q: int| 0 <= p < q < perm@.len() implies before(gs@, #[trigger] perm@[p], #[trigger] perm@[q]) by {
                if q < pos {
                } else if q == pos {
                } else if p < pos {
                    assert(perm@[q] == old_perm[q - 1]);
                    assert(before(gs@, old_perm[p], i));
                } else if p == pos {
                    assert(perm@[q] == old_perm[q - 1]);
                } else {
                    assert(perm@[p] == old_perm[p - 1] && perm@[q] == old_perm[q - 1]);
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert forall|p: int, q: int| 0 <= p < q < perm@.len() implies gs@[#[trigger] perm@[p] as int].cnt > gs@[#[trigger] perm@[q] as int].cnt
            || (gs@[perm@[p] as int].cnt == gs@[perm@[q] as int].cnt && perm@[p] < perm@[q]) by {
            assert(before(gs@, perm@[p], perm@[q]));
        }
    }
    perm
}

} // verus!
