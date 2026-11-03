//! Ordering indices by descending `i128` keys (insertion sort; for short lists such as result groups): the result
//! is a permutation of `0..n` along which the keys never increase.
use vstd::prelude::*;

verus! {

/// `ord` lists every index of `0..n` exactly once.
pub open spec fn is_index_perm(ord: Seq<usize>, n: int) -> bool {
    &&& ord.len() == n
    &&& forall|a: int| 0 <= a < n ==> #[trigger] ord[a] < n
    &&& forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] ord[a] != #[trigger] ord[b]
    &&& forall|i: int| 0 <= i < n ==> #[trigger] covers(ord, i)
}

/// Index `i` appears in `ord`.
pub open spec fn covers(ord: Seq<usize>, i: int) -> bool {
    exists|a: int| 0 <= a < ord.len() && ord[a] == i
}

/// The keys never increase along `ord`.
pub open spec fn desc_along(keys: Seq<i128>, ord: Seq<usize>) -> bool {
    forall|a: int, b: int| 0 <= a < b < ord.len() ==> keys[#[trigger] ord[a] as int] >= keys[#[trigger] ord[b] as int]
}

/// The indices `0..keys.len()` in descending key order.
pub fn order_desc(keys: &Vec<i128>) -> (ord: Vec<usize>)
    ensures is_index_perm(ord@, keys@.len() as int), desc_along(keys@, ord@),
{
    let n = keys.len();
    let mut ord: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == keys@.len(), i <= n,
            is_index_perm(ord@, i as int),
            desc_along(keys@, ord@),
        decreases n - i,
    {
        // the first position whose key is smaller than key i
        let mut p: usize = 0;
        while p < ord.len() && keys[ord[p]] >= keys[i]
            invariant
                n == keys@.len(), i < n,
                is_index_perm(ord@, i as int),
                p <= ord@.len(),
                forall|a: int| 0 <= a < p ==> keys@[#[trigger] ord@[a] as int] >= keys@[i as int],
            decreases ord@.len() - p,
        {
            p = p + 1;
        }
        let ghost old_ord = ord@;
        ord.insert(p, i);
        proof {
            let o = ord@;
            assert(o == old_ord.insert(p as int, i));
            assert(o.len() == i + 1);
            assert forall|a: int| 0 <= a < i + 1 implies #[trigger] o[a] < i + 1 by {
                if a < p {
                    assert(o[a] == old_ord[a]);
                } else if a > p {
                    assert(o[a] == old_ord[a - 1]);
                }
            }
            assert forall|a: int, b: int| 0 <= a < i + 1 && 0 <= b < i + 1 && a != b implies #[trigger] o[a] != #[trigger] o[b] by {
                let oa = if a < p { a } else { a - 1 };
                let ob = if b < p { b } else { b - 1 };
                if a != p && b != p {
                    assert(o[a] == old_ord[oa] && o[b] == old_ord[ob]);
                    assert(oa != ob);
                } else if a == p {
                    assert(o[b] == old_ord[ob]);
                    assert(old_ord[ob] < i);
                } else {
                    assert(o[a] == old_ord[oa]);
                    assert(old_ord[oa] < i);
                }
            }
            assert forall|x: int| 0 <= x < i + 1 implies #[trigger] covers(o, x) by {
                if x == i {
                    assert(o[p as int] == x);
                } else {
                    assert(covers(old_ord, x));
                    let a = choose|a: int| 0 <= a < old_ord.len() && old_ord[a] == x;
                    if a < p {
                        assert(o[a] == x);
                    } else {
                        assert(o[a + 1] == x);
                    }
                }
            }
            assert forall|a: int, b: int| 0 <= a < b < o.len() implies keys@[#[trigger] o[a] as int] >= keys@[#[trigger] o[b] as int] by {
                if b < p {
                    assert(o[a] == old_ord[a] && o[b] == old_ord[b]);
                } else if a > p {
                    assert(o[a] == old_ord[a - 1] && o[b] == old_ord[b - 1]);
                } else if a == p {
                    // key i is larger than the key at old position p, hence than every later key
                    assert(o[b] == old_ord[b - 1]);
                    if p < old_ord.len() {
                        assert(keys@[old_ord[p as int] as int] < keys@[i as int]);
                        if b - 1 > p {
                            assert(keys@[old_ord[p as int] as int] >= keys@[old_ord[b - 1] as int]);
                        }
                    }
                } else if b == p {
                    assert(o[a] == old_ord[a]);
                } else {
                    // a < p < b
                    assert(o[a] == old_ord[a] && o[b] == old_ord[b - 1]);
                    assert(a < b - 1);
                }
            }
        }
        i = i + 1;
    }
    ord
}

} // verus!
