//! Top `TOPK` candidates by `o_totalprice DESC, o_orderdate` (`answer::row_cmp` on price and stored date):
//! insertion into a sorted list of at most `TOPK` candidate indices.
//!
//! Invariant after candidates `0..i` (`top_inv`): `sel` holds `min(i, TOPK)` distinct indices below `i`, sorted by
//! `row_cmp`; while fewer than `TOPK` were seen every index is selected; and every selected candidate sorts no
//! later than every unselected one. A new candidate enters at the position after every selected candidate that
//! does not sort after it; when the list is full, the last one leaves.
use vstd::prelude::*;
use crate::agent::answer::row_cmp;

verus! {

/// Rows the statement returns at most (`LIMIT 100`).
pub const TOPK: usize = 100;

/// One output candidate: an orders row `o`, its customer row `c`, its quantity sum (scale 2), and the ORDER BY
/// values (total price coefficient, stored date).
#[derive(Clone, Copy)]
pub struct Cand {
    pub o: usize,
    pub c: usize,
    pub sum: i128,
    pub price: i128,
    pub date: i32,
}

/// The ORDER BY comparison of two candidates.
pub open spec fn ccmp(x: Cand, y: Cand) -> int {
    row_cmp(x.price as int, x.date as int, y.price as int, y.date as int)
}

/// `x` sorts strictly before `y`.
fn before(x: &Cand, y: &Cand) -> (b: bool)
    ensures b == (ccmp(*x, *y) < 0),
{
    x.price > y.price || (x.price == y.price && x.date < y.date)
}

/// `row_cmp` is antisymmetric and transitive.
pub proof fn lemma_ccmp(x: Cand, y: Cand, z: Cand)
    ensures
        ccmp(x, y) == -ccmp(y, x),
        ccmp(x, y) <= 0 && ccmp(y, z) <= 0 ==> ccmp(x, z) <= 0,
        ccmp(x, y) < 0 && ccmp(y, z) <= 0 ==> ccmp(x, z) < 0,
        ccmp(x, y) <= 0 && ccmp(y, z) < 0 ==> ccmp(x, z) < 0,
{
}

/// The selection invariant after candidates `0..i` (see the module header).
pub open spec fn top_inv(cs: Seq<Cand>, i: int, sel: Seq<usize>) -> bool {
    &&& 0 <= i <= cs.len() <= usize::MAX
    &&& sel.len() == if i <= TOPK { i } else { TOPK as int }
    &&& sel.no_duplicates()
    &&& forall|t: int| 0 <= t < sel.len() ==> (#[trigger] sel[t] as int) < i
    &&& forall|a: int, b: int| 0 <= a < b < sel.len() ==> ccmp(cs[sel[a] as int], cs[sel[b] as int]) <= 0
    &&& i <= TOPK ==> forall|x: int| 0 <= x < i ==> #[trigger] sel.contains(x as usize)
    &&& forall|x: int, a: int| 0 <= x < i && !sel.contains(x as usize) && 0 <= a < sel.len()
            ==> #[trigger] ccmp(cs[sel[a] as int], cs[x]) <= 0
}

/// Inserting candidate `i` at position `p` keeps the list sorted and duplicate-free, and its entries are the old
/// ones and `i`.
proof fn lemma_insert(cs: Seq<Cand>, i: int, sel: Seq<usize>, p: int)
    requires
        top_inv(cs, i, sel), i < cs.len(),
        0 <= p <= sel.len(),
        forall|a: int| p <= a < sel.len() ==> ccmp(cs[i], cs[#[trigger] sel[a] as int]) < 0,
        p > 0 ==> ccmp(cs[sel[p - 1] as int], cs[i]) <= 0,
    ensures ({
        let ins = sel.insert(p, i as usize);
        &&& forall|a: int, b: int| 0 <= a < b < ins.len() ==> ccmp(cs[ins[a] as int], cs[ins[b] as int]) <= 0
        &&& ins.no_duplicates()
        &&& forall|y: usize| #[trigger] ins.contains(y) <==> (sel.contains(y) || y == i as usize)
        &&& forall|t: int| 0 <= t < ins.len() ==> (#[trigger] ins[t] as int) < i + 1
    }),
{
    let x = i as usize;
    let ins = sel.insert(p, x);
    assert(!sel.contains(x)) by {
        if sel.contains(x) {
            let t = choose|t: int| 0 <= t < sel.len() && sel[t] == x;
            assert((sel[t] as int) < i);
        }
    }
    assert(forall|a: int| 0 <= a < p ==> ins[a] == sel[a]);
    assert(ins[p] == x);
    assert(forall|a: int| p < a < ins.len() ==> ins[a] == sel[a - 1]);
    // every selected candidate before p sorts no later than i
    assert forall|a: int| 0 <= a < p implies ccmp(cs[sel[a] as int], cs[i]) <= 0 by {
        if a < p - 1 {
            lemma_ccmp(cs[sel[a] as int], cs[sel[p - 1] as int], cs[i]);
        }
    }
    assert forall|a: int, b: int| 0 <= a < b < ins.len() implies ccmp(cs[ins[a] as int], cs[ins[b] as int]) <= 0 by {
        if b < p {
        } else if b == p {
        } else if a < p {
            lemma_ccmp(cs[sel[a] as int], cs[i], cs[sel[b - 1] as int]);
        } else if a == p {
            lemma_ccmp(cs[i], cs[sel[b - 1] as int], cs[i]);
        } else {
        }
    }
    assert forall|a: int, b: int| 0 <= a < ins.len() && 0 <= b < ins.len() && a != b implies ins[a] != ins[b] by {
        if a == p || b == p {
            if a != p { assert(sel.contains(ins[a])); }
            if b != p { assert(sel.contains(ins[b])); }
        }
    }
    assert forall|y: usize| #[trigger] ins.contains(y) <==> (sel.contains(y) || y == x) by {
        if ins.contains(y) {
            let t = choose|t: int| 0 <= t < ins.len() && ins[t] == y;
            if t < p { assert(sel[t] == y); } else if t > p { assert(sel[t - 1] == y); }
        }
        if sel.contains(y) {
            let t = choose|t: int| 0 <= t < sel.len() && sel[t] == y;
            if t < p { assert(ins[t] == y); } else { assert(ins[t + 1] == y); }
        }
        if y == x { assert(ins[p] == y); }
    }
    assert forall|t: int| 0 <= t < ins.len() implies (#[trigger] ins[t] as int) < i + 1 by {
        if t != p {
            assert(sel.contains(ins[t]));
            let u = choose|u: int| 0 <= u < sel.len() && sel[u] == ins[t];
        }
    }
}

/// When the full list loses its last candidate `last` to `i`: every kept candidate sorts no later than every
/// unselected one (`last` included).
proof fn lemma_full_unselected(cs: Seq<Cand>, i: int, sel: Seq<usize>, ins: Seq<usize>)
    requires
        0 <= i < cs.len() <= usize::MAX,
        sel.len() > 0, ins.len() == sel.len() + 1,
        ins[ins.len() - 1] == sel[sel.len() - 1],
        ccmp(cs[i], cs[sel[sel.len() - 1] as int]) < 0,
        forall|a: int, b: int| 0 <= a < b < ins.len() ==> ccmp(cs[ins[a] as int], cs[ins[b] as int]) <= 0,
        forall|y: usize| #[trigger] ins.contains(y) <==> (sel.contains(y) || y == i as usize),
        forall|t: int| 0 <= t < sel.len() ==> ccmp(cs[#[trigger] sel[t] as int], cs[sel[sel.len() - 1] as int]) <= 0,
        forall|x: int, a: int| 0 <= x < i && !sel.contains(x as usize) && 0 <= a < sel.len()
            ==> #[trigger] ccmp(cs[sel[a] as int], cs[x]) <= 0,
    ensures ({
        let out = ins.drop_last();
        forall|z: int, a: int| 0 <= z < i + 1 && !out.contains(z as usize) && 0 <= a < out.len()
            ==> #[trigger] ccmp(cs[out[a] as int], cs[z]) <= 0
    }),
{
    let out = ins.drop_last();
    let last = sel[sel.len() - 1];
    assert forall|z: int, a: int| 0 <= z < i + 1 && !out.contains(z as usize) && 0 <= a < out.len()
        implies #[trigger] ccmp(cs[out[a] as int], cs[z]) <= 0 by {
        let w = out[a];
        assert(w == ins[a]);
        assert(ins.contains(w));
        if z as usize == last {
            // the dropped last candidate: everything kept sorts no later
            assert(ccmp(cs[ins[a] as int], cs[ins[ins.len() - 1] as int]) <= 0);
        } else {
            assert(!ins.contains(z as usize)) by {
                if ins.contains(z as usize) {
                    let t = choose|t: int| 0 <= t < ins.len() && ins[t] == z as usize;
                    if t < out.len() { assert(out[t] == z as usize); }
                }
            }
            assert(z != i);
            assert(!sel.contains(z as usize));
            // z was unselected: every old selected candidate, the last among them, sorts no later
            assert(ccmp(cs[sel[sel.len() - 1] as int], cs[z]) <= 0);
            if w == i as usize {
                lemma_ccmp(cs[i], cs[last as int], cs[z]);
            } else {
                assert(sel.contains(w));
                let u = choose|u: int| 0 <= u < sel.len() && sel[u] == w;
                assert(ccmp(cs[sel[u] as int], cs[z]) <= 0);
            }
        }
    }
}

/// Inserting candidate `i` at position `p` (after every selected candidate that does not sort after it), then
/// dropping the last one when the list held `TOPK`.
proof fn lemma_enter(cs: Seq<Cand>, i: int, sel: Seq<usize>, p: int)
    requires
        top_inv(cs, i, sel), i < cs.len(),
        0 <= p <= sel.len(),
        sel.len() == TOPK ==> p < TOPK,
        forall|a: int| p <= a < sel.len() ==> ccmp(cs[i], cs[#[trigger] sel[a] as int]) < 0,
        p > 0 ==> ccmp(cs[sel[p - 1] as int], cs[i]) <= 0,
    ensures ({
        let ins = sel.insert(p, i as usize);
        top_inv(cs, i + 1, if sel.len() == TOPK { ins.drop_last() } else { ins })
    }),
{
    let x = i as usize;
    let ins = sel.insert(p, x);
    lemma_insert(cs, i, sel, p);
    if sel.len() < TOPK {
        assert(i < TOPK);
        assert forall|z: int| 0 <= z < i + 1 implies #[trigger] ins.contains(z as usize) by {
            if z < i {
                assert(sel.contains(z as usize));
            }
        }
    } else {
        let out = ins.drop_last();
        assert(ins[ins.len() - 1] == sel[sel.len() - 1]);
        assert(ccmp(cs[i], cs[sel[sel.len() - 1] as int]) < 0);
        assert forall|t: int| 0 <= t < sel.len() implies ccmp(cs[#[trigger] sel[t] as int], cs[sel[sel.len() - 1] as int]) <= 0 by {
            if t < sel.len() - 1 {
                assert(ccmp(cs[sel[t] as int], cs[sel[sel.len() - 1] as int]) <= 0);
            } else {
                lemma_ccmp(cs[sel[t] as int], cs[sel[t] as int], cs[sel[t] as int]);
            }
        }
        lemma_full_unselected(cs, i, sel, ins);
        assert forall|t: int| 0 <= t < out.len() implies (#[trigger] out[t] as int) < i + 1 by {
            assert(out[t] == ins[t]);
        }
        assert forall|a: int, b: int| 0 <= a < b < out.len() implies ccmp(cs[out[a] as int], cs[out[b] as int]) <= 0 by {
            assert(out[a] == ins[a] && out[b] == ins[b]);
        }
        assert(out.no_duplicates()) by {
            assert forall|a: int, b: int| 0 <= a < out.len() && 0 <= b < out.len() && a != b implies out[a] != out[b] by {
                assert(out[a] == ins[a] && out[b] == ins[b]);
            }
        }
    }
}

/// Skipping candidate `i` when the list is full and its last one sorts no later than `i`.
proof fn lemma_skip(cs: Seq<Cand>, i: int, sel: Seq<usize>)
    requires
        top_inv(cs, i, sel), i < cs.len(),
        sel.len() == TOPK,
        ccmp(cs[sel[sel.len() - 1] as int], cs[i]) <= 0,
    ensures top_inv(cs, i + 1, sel),
{
    assert forall|z: int, a: int| 0 <= z < i + 1 && !sel.contains(z as usize) && 0 <= a < sel.len()
        implies #[trigger] ccmp(cs[sel[a] as int], cs[z]) <= 0 by {
        if z == i {
            if a < sel.len() - 1 {
                lemma_ccmp(cs[sel[a] as int], cs[sel[sel.len() - 1] as int], cs[i]);
            }
        }
    }
}

/// The first `min(TOPK, |cands|)` candidates in ORDER BY order (indices into `cands`).
pub fn top(cands: &Vec<Cand>) -> (sel: Vec<usize>)
    ensures top_inv(cands@, cands@.len() as int, sel@),
{
    let mut sel: Vec<usize> = Vec::new();
    let n = cands.len();
    let ghost cs = cands@;
    let mut i: usize = 0;
    while i < n
        invariant n == cs.len(), cs == cands@, i <= n, top_inv(cs, i as int, sel@),
        decreases n - i,
    {
        let x = cands[i];
        let m = sel.len();
        // the position after every selected candidate that does not sort after x
        let mut p: usize = m;
        while p > 0 && before(&x, &cands[sel[p - 1]])
            invariant
                p <= m, m == sel@.len(), cs == cands@, i < n, x == cs[i as int], top_inv(cs, i as int, sel@),
                forall|a: int| p <= a < m ==> ccmp(cs[i as int], cs[#[trigger] sel@[a] as int]) < 0,
            decreases p,
        {
            p = p - 1;
        }
        proof {
            if p > 0 {
                lemma_ccmp(cs[sel@[p - 1] as int], cs[i as int], cs[i as int]);
            }
        }
        if p < TOPK {
            proof { lemma_enter(cs, i as int, sel@, p as int); }
            let full = m == TOPK;
            sel.insert(p, i);
            if full {
                let _ = sel.pop();
            }
        } else {
            proof {
                lemma_ccmp(cs[sel@[m - 1] as int], cs[i as int], cs[i as int]);
                lemma_skip(cs, i as int, sel@);
            }
        }
        i = i + 1;
    }
    sel
}

} // verus!
