//! Merge of the `num` items of one partition `p` into one accumulator per join key: the task reads the items of
//! all `num` scan outputs in task order and adds each item of its partition to its key's accumulator.
//!
//! `msum(sel, g, rows)`: accumulator `sel` of key `g` over the rows `rows` (items of other partitions or keys count
//! 0). After all tasks the rows are `ilist(0, n)`, and for an entry `k` whose key is `g`, `msum` over them is
//! `ctx::acc(sel, k, n)` (`lemma_acc_msum`).
use vstd::prelude::*;
use crate::agent::common::satacc::*;
use crate::agent::ctx::*;
use crate::agent::keys::*;
use crate::agent::kg::*;
use crate::agent::numscan::*;

verus! {

/// The task bounds cover `0..n` in order, and each task's output lists its items.
#[verifier::opaque]
pub open spec fn nouts_ok(nouts: Seq<NumOut>, c: Ctx, pbits: u64, kgs: Seq<KgPart>, bounds: Seq<int>) -> bool {
    &&& bounds.len() == nouts.len() + 1
    &&& bounds[0] == 0
    &&& bounds[nouts.len() as int] == c.n
    &&& forall|t: int| 0 <= t < nouts.len() ==> #[trigger] bounds[t] <= bounds[t + 1]
    &&& forall|t: int| 0 <= t < nouts.len() ==> num_out_ok(#[trigger] nouts[t], c, pbits, kgs, bounds[t], bounds[t + 1])
}

pub proof fn lemma_nouts(nouts: Seq<NumOut>, c: Ctx, pbits: u64, kgs: Seq<KgPart>, bounds: Seq<int>)
    requires nouts_ok(nouts, c, pbits, kgs, bounds),
    ensures
        bounds.len() == nouts.len() + 1,
        bounds[0] == 0,
        bounds[nouts.len() as int] == c.n,
        forall|t: int| 0 <= t < nouts.len() ==> #[trigger] bounds[t] <= bounds[t + 1],
        forall|t: int| 0 <= t < nouts.len() ==> num_out_ok(#[trigger] nouts[t], c, pbits, kgs, bounds[t], bounds[t + 1]),
{
    reveal(nouts_ok);
}

/// Accumulator `sel` of key `g` of partition `p` over the rows `rows`.
pub open spec fn msum(c: Ctx, pbits: u64, kgs: Seq<KgPart>, sel: int, p: int, g: int, rows: Seq<int>) -> int
    decreases rows.len(),
{
    if rows.len() == 0 {
        0
    } else {
        let i = rows.last();
        msum(c, pbits, kgs, sel, p, g, rows.drop_last())
            + if rpart(c, pbits, i) == p && rowg(c, pbits, kgs, i) == g { wt(c, sel, i) } else { 0 }
    }
}

/// The three accumulators of key `g` over `rows`.
pub open spec fn macc_ok(a: Acc, c: Ctx, pbits: u64, kgs: Seq<KgPart>, p: int, g: int, rows: Seq<int>) -> bool {
    &&& acc_ok(a, msum(c, pbits, kgs, 0, p, g, rows), msum(c, pbits, kgs, 1, p, g, rows), msum(c, pbits, kgs, 2, p, g, rows))
    &&& acc_sane(msum(c, pbits, kgs, 0, p, g, rows), msum(c, pbits, kgs, 1, p, g, rows), msum(c, pbits, kgs, 2, p, g, rows))
}

pub proof fn lemma_msum_push(c: Ctx, pbits: u64, kgs: Seq<KgPart>, sel: int, p: int, g: int, rows: Seq<int>, i: int)
    ensures msum(c, pbits, kgs, sel, p, g, rows.push(i)) == msum(c, pbits, kgs, sel, p, g, rows)
        + if rpart(c, pbits, i) == p && rowg(c, pbits, kgs, i) == g { wt(c, sel, i) } else { 0 },
{
    assert(rows.push(i).drop_last() =~= rows);
}

pub proof fn lemma_msum_empty(c: Ctx, pbits: u64, kgs: Seq<KgPart>, p: int, g: int)
    ensures macc_ok(acc_zero_spec(), c, pbits, kgs, p, g, Seq::empty()),
{
}

pub open spec fn acc_zero_spec() -> Acc {
    (0u64, 0i128, 0u128)
}

/// The rows of a range with an item, appended to those of the earlier range.
pub proof fn lemma_ilist_append(c: Ctx, pbits: u64, kgs: Seq<KgPart>, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures ilist(c, pbits, kgs, lo, mid) + ilist(c, pbits, kgs, mid, hi) == ilist(c, pbits, kgs, lo, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_ilist_append(c, pbits, kgs, lo, mid, hi - 1);
        let a = ilist(c, pbits, kgs, lo, mid);
        let b = ilist(c, pbits, kgs, mid, hi - 1);
        assert((a + b).push(hi - 1) =~= a + b.push(hi - 1));
    } else {
        assert(ilist(c, pbits, kgs, lo, mid) + Seq::<int>::empty() =~= ilist(c, pbits, kgs, lo, mid));
    }
}

/// The rows of a range with an item lie in it and have an item.
pub proof fn lemma_ilist_range(c: Ctx, pbits: u64, kgs: Seq<KgPart>, lo: int, hi: int, j: int)
    requires 0 <= j < ilist(c, pbits, kgs, lo, hi).len(),
    ensures lo <= ilist(c, pbits, kgs, lo, hi)[j] < hi, has_item(c, pbits, kgs, ilist(c, pbits, kgs, lo, hi)[j]),
    decreases hi - lo,
{
    if hi > lo {
        let d = ilist(c, pbits, kgs, lo, hi - 1);
        if j < d.len() {
            lemma_ilist_range(c, pbits, kgs, lo, hi - 1, j);
        }
    }
}

/// For an entry `k` whose key is `g`: its accumulator over `num` rows `0..hi` is `msum` over their items.
pub proof fn lemma_acc_msum(c: Ctx, pbits: u64, kgs: Seq<KgPart>, sel: int, p: int, g: int, k: int, hi: int)
    requires
        kgs_ok(kgs, c, pbits), 0 <= p < kgs.len(),
        pre_ok(c, k), epart(c, pbits, k) == p,
        0 <= g < kgs[p].nkg, kg_key(kgs[p], c, g) == ekey(c, k),
        0 <= hi,
    ensures acc(c, sel, k, hi) == msum(c, pbits, kgs, sel, p, g, ilist(c, pbits, kgs, 0, hi)),
    decreases hi,
{
    if hi > 0 {
        lemma_acc_msum(c, pbits, kgs, sel, p, g, k, hi - 1);
        lemma_nmatch_item(c, pbits, kgs, p, g, k, hi - 1);
        let d = ilist(c, pbits, kgs, 0, hi - 1);
        if has_item(c, pbits, kgs, hi - 1) {
            lemma_msum_push(c, pbits, kgs, sel, p, g, d, hi - 1);
        }
    }
}

/// The items of all tasks read so far: the rows of the earlier tasks, then the first `j` of task `t`.
pub open spec fn mrows(c: Ctx, pbits: u64, kgs: Seq<KgPart>, bounds: Seq<int>, t: int, j: int) -> Seq<int> {
    ilist(c, pbits, kgs, 0, bounds[t]) + ilist(c, pbits, kgs, bounds[t], bounds[t + 1]).subrange(0, j)
}

pub proof fn lemma_mrows_start(c: Ctx, pbits: u64, kgs: Seq<KgPart>, bounds: Seq<int>, t: int)
    ensures mrows(c, pbits, kgs, bounds, t, 0) == ilist(c, pbits, kgs, 0, bounds[t]),
{
    assert(ilist(c, pbits, kgs, 0, bounds[t]) + ilist(c, pbits, kgs, bounds[t], bounds[t + 1]).subrange(0, 0)
        =~= ilist(c, pbits, kgs, 0, bounds[t]));
}

pub proof fn lemma_mrows_step(c: Ctx, pbits: u64, kgs: Seq<KgPart>, bounds: Seq<int>, t: int, j: int)
    requires 0 <= j < ilist(c, pbits, kgs, bounds[t], bounds[t + 1]).len(),
    ensures mrows(c, pbits, kgs, bounds, t, j + 1)
        == mrows(c, pbits, kgs, bounds, t, j).push(ilist(c, pbits, kgs, bounds[t], bounds[t + 1])[j]),
{
    let a = ilist(c, pbits, kgs, 0, bounds[t]);
    let b = ilist(c, pbits, kgs, bounds[t], bounds[t + 1]);
    assert(a + b.subrange(0, j + 1) =~= (a + b.subrange(0, j)).push(b[j]));
}

pub proof fn lemma_mrows_next(c: Ctx, pbits: u64, kgs: Seq<KgPart>, bounds: Seq<int>, t: int)
    requires 0 <= bounds[t] <= bounds[t + 1],
    ensures mrows(c, pbits, kgs, bounds, t, ilist(c, pbits, kgs, bounds[t], bounds[t + 1]).len() as int)
        == ilist(c, pbits, kgs, 0, bounds[t + 1]),
{
    let b = ilist(c, pbits, kgs, bounds[t], bounds[t + 1]);
    assert(b.subrange(0, b.len() as int) =~= b);
    lemma_ilist_append(c, pbits, kgs, 0, bounds[t], bounds[t + 1]);
}

/// The task bounds are monotone.
pub proof fn lemma_nb_mono(bounds: Seq<int>, nt: int, a: int, b: int)
    requires
        bounds.len() == nt + 1, 0 <= a <= b <= nt,
        forall|u: int| 0 <= u < nt ==> #[trigger] bounds[u] <= bounds[u + 1],
    ensures bounds[a] <= bounds[b],
    decreases b - a,
{
    if b > a {
        lemma_nb_mono(bounds, nt, a, b - 1);
        assert(bounds[b - 1] <= bounds[b]);
    }
}

/// Add the items of partition `p` of all `num` scan outputs to the accumulators of their keys.
pub fn merge_items(accs: &mut Vec<Acc>, nouts: &Vec<NumOut>, p: usize,
    Ghost(c): Ghost<Ctx>, Ghost(pbits): Ghost<u64>, Ghost(kgs): Ghost<Seq<KgPart>>, Ghost(bounds): Ghost<Seq<int>>)
    requires
        kgs_ok(kgs, c, pbits), (p as int) < kgs.len(),
        nouts_ok(nouts@, c, pbits, kgs, bounds),
        old(accs)@.len() == kgs[p as int].nkg,
        forall|g: int| 0 <= g < old(accs)@.len() ==> #[trigger] old(accs)@[g] == acc_zero_spec(),
    ensures
        final(accs)@.len() == old(accs)@.len(),
        forall|g: int| 0 <= g < final(accs)@.len() ==>
            macc_ok(#[trigger] final(accs)@[g], c, pbits, kgs, p as int, g, ilist(c, pbits, kgs, 0, c.n)),
    no_unwind
{
    let ghost nk = accs@.len();
    let nt = nouts.len();
    proof {
        lemma_nouts(nouts@, c, pbits, kgs, bounds);
        assert forall|g: int| 0 <= g < nk implies macc_ok(#[trigger] accs@[g], c, pbits, kgs, p as int, g, ilist(c, pbits, kgs, 0, bounds[0])) by {
            lemma_msum_empty(c, pbits, kgs, p as int, g);
        }
    }
    let mut t: usize = 0;
    while t < nt
        invariant
            kgs_ok(kgs, c, pbits), (p as int) < kgs.len(), nouts_ok(nouts@, c, pbits, kgs, bounds), nt == nouts@.len(),
            t <= nt, accs@.len() == nk, nk == kgs[p as int].nkg,
            forall|g: int| 0 <= g < nk ==>
                macc_ok(#[trigger] accs@[g], c, pbits, kgs, p as int, g, ilist(c, pbits, kgs, 0, bounds[t as int])),
        decreases nt - t,
    {
        proof {
            lemma_nouts(nouts@, c, pbits, kgs, bounds);
            lemma_nb_mono(bounds, nt as int, 0, t as int);
            lemma_mrows_start(c, pbits, kgs, bounds, t as int);
        }
        let o = &nouts[t];
        let ol = o.len;
        let ghost il = ilist(c, pbits, kgs, bounds[t as int], bounds[t + 1]);
        let mut j: usize = 0;
        while j < ol
            invariant
                kgs_ok(kgs, c, pbits), (p as int) < kgs.len(), nouts_ok(nouts@, c, pbits, kgs, bounds), nt == nouts@.len(),
                t < nt, accs@.len() == nk, nk == kgs[p as int].nkg,
                o == &nouts@[t as int], ol == o.len, il == ilist(c, pbits, kgs, bounds[t as int], bounds[t + 1]),
                num_out_ok(*o, c, pbits, kgs, bounds[t as int], bounds[t + 1]),
                0 <= bounds[t as int] <= bounds[t + 1],
                j <= ol,
                forall|g: int| 0 <= g < nk ==>
                    macc_ok(#[trigger] accs@[g], c, pbits, kgs, p as int, g, mrows(c, pbits, kgs, bounds, t as int, j as int)),
            decreases ol - j,
        {
            let ghost rows = mrows(c, pbits, kgs, bounds, t as int, j as int);
            let ghost i = il[j as int];
            proof {
                lemma_mrows_step(c, pbits, kgs, bounds, t as int, j as int);
                lemma_ilist_range(c, pbits, kgs, bounds[t as int], bounds[t + 1], j as int);
            }
            if o.ip[j] as usize == p {
                let g = o.ig[j];
                let v = o.iv[j];
                proof {
                    let g2 = choose|g2: int| #[trigger] hits(c, pbits, kgs, i, rpart(c, pbits, i), g2);
                    lemma_hits_unique(c, pbits, kgs, i, g2);
                    assert(g < nk);
                }
                let a = accs[g];
                let ghost c0 = msum(c, pbits, kgs, 0, p as int, g as int, rows);
                let ghost s0 = msum(c, pbits, kgs, 1, p as int, g as int, rows);
                let ghost m0 = msum(c, pbits, kgs, 2, p as int, g as int, rows);
                let a2 = acc_add(a, v, Ghost(c0), Ghost(s0), Ghost(m0));
                let ghost before = accs@;
                accs[g] = a2;
                proof {
                    assert forall|g3: int| 0 <= g3 < nk implies
                        macc_ok(#[trigger] accs@[g3], c, pbits, kgs, p as int, g3, rows.push(i)) by {
                        lemma_msum_push(c, pbits, kgs, 0, p as int, g3, rows, i);
                        lemma_msum_push(c, pbits, kgs, 1, p as int, g3, rows, i);
                        lemma_msum_push(c, pbits, kgs, 2, p as int, g3, rows, i);
                        if g3 != g as int {
                            assert(accs@[g3] == before[g3]);
                        }
                    }
                }
            } else {
                proof {
                    assert forall|g3: int| 0 <= g3 < nk implies
                        macc_ok(#[trigger] accs@[g3], c, pbits, kgs, p as int, g3, rows.push(i)) by {
                        lemma_msum_push(c, pbits, kgs, 0, p as int, g3, rows, i);
                        lemma_msum_push(c, pbits, kgs, 1, p as int, g3, rows, i);
                        lemma_msum_push(c, pbits, kgs, 2, p as int, g3, rows, i);
                    }
                }
            }
            j = j + 1;
        }
        proof {
            lemma_mrows_next(c, pbits, kgs, bounds, t as int);
        }
        t = t + 1;
    }
}

} // verus!
