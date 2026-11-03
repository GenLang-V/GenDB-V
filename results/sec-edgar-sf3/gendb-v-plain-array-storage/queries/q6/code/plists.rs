//! Reading the pre-scan outputs of all tasks in task order, keeping the entries of one partition.
//!
//! Task `t` scanned `pre` rows `bounds[t]..bounds[t + 1]` (`pres_ok`); after its first `j` entries the entries of
//! partition `p` read so far are `pl(.., p, t, j)`: those of the earlier tasks (`plist(p, 0, bounds[t])`) and of the
//! first `j` entries of task `t`. At the end of the last task they are `plist(p, 0, q)`.
use vstd::prelude::*;
use crate::agent::ctx::*;
use crate::agent::keys::*;
use crate::agent::prescan::*;
use crate::agent::keys::MAX_PBITS;

verus! {

/// The task bounds cover `0..q` in order, and each task's output lists its entries.
#[verifier::opaque]
pub open spec fn pres_ok(pres: Seq<PreOut>, c: Ctx, pbits: u64, bounds: Seq<int>) -> bool {
    &&& bounds.len() == pres.len() + 1
    &&& bounds[0] == 0
    &&& bounds[pres.len() as int] == c.q
    &&& forall|t: int| 0 <= t < pres.len() ==> #[trigger] bounds[t] <= bounds[t + 1]
    &&& forall|t: int| 0 <= t < pres.len() ==> pre_out_ok(#[trigger] pres[t], c, pbits, bounds[t], bounds[t + 1])
}

/// The entries of partition `p` among the first `j` entries of `el`.
pub open spec fn filt(c: Ctx, pbits: u64, p: int, el: Seq<int>, j: int) -> Seq<int>
    decreases j,
{
    if j <= 0 {
        Seq::empty()
    } else {
        let d = filt(c, pbits, p, el, j - 1);
        if epart(c, pbits, el[j - 1]) == p { d.push(el[j - 1]) } else { d }
    }
}

/// The entries of partition `p` read after `j` entries of task `t`.
pub open spec fn pl(c: Ctx, pbits: u64, p: int, bounds: Seq<int>, t: int, j: int) -> Seq<int> {
    plist(c, pbits, p, 0, bounds[t]) + filt(c, pbits, p, elist(c, bounds[t], bounds[t + 1]), j)
}

/// The entries of a range, filtered by partition, are the range's entries of the partition.
pub proof fn lemma_filt_plist(c: Ctx, pbits: u64, p: int, lo: int, hi: int)
    requires lo <= hi,
    ensures filt(c, pbits, p, elist(c, lo, hi), elist(c, lo, hi).len() as int) == plist(c, pbits, p, lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_filt_plist(c, pbits, p, lo, hi - 1);
        let d = elist(c, lo, hi - 1);
        if pre_ok(c, hi - 1) {
            lemma_filt_prefix(c, pbits, p, d.push(hi - 1), d, d.len() as int);
        }
    }
}

/// `filt` reads only the first `j` entries.
pub proof fn lemma_filt_prefix(c: Ctx, pbits: u64, p: int, a: Seq<int>, b: Seq<int>, j: int)
    requires 0 <= j <= a.len(), j <= b.len(), forall|i: int| 0 <= i < j ==> #[trigger] a[i] == b[i],
    ensures filt(c, pbits, p, a, j) == filt(c, pbits, p, b, j),
    decreases j,
{
    if j > 0 {
        lemma_filt_prefix(c, pbits, p, a, b, j - 1);
    }
}

/// Adjacent ranges concatenate.
pub proof fn lemma_plist_append(c: Ctx, pbits: u64, p: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures plist(c, pbits, p, lo, mid) + plist(c, pbits, p, mid, hi) == plist(c, pbits, p, lo, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_plist_append(c, pbits, p, lo, mid, hi - 1);
        let a = plist(c, pbits, p, lo, mid);
        let b = plist(c, pbits, p, mid, hi - 1);
        assert((a + b).push(hi - 1) =~= a + b.push(hi - 1));
    } else {
        assert(plist(c, pbits, p, lo, mid) + Seq::<int>::empty() =~= plist(c, pbits, p, lo, mid));
    }
}

/// One more entry of task `t`.
pub proof fn lemma_pl_step(c: Ctx, pbits: u64, p: int, bounds: Seq<int>, t: int, j: int)
    requires 0 <= j < elist(c, bounds[t], bounds[t + 1]).len(),
    ensures ({
        let e = elist(c, bounds[t], bounds[t + 1])[j];
        pl(c, pbits, p, bounds, t, j + 1) == if epart(c, pbits, e) == p { pl(c, pbits, p, bounds, t, j).push(e) } else { pl(c, pbits, p, bounds, t, j) }
    }),
{
    let a = plist(c, pbits, p, 0, bounds[t]);
    let f = filt(c, pbits, p, elist(c, bounds[t], bounds[t + 1]), j);
    assert((a + f).push(elist(c, bounds[t], bounds[t + 1])[j]) =~= a + f.push(elist(c, bounds[t], bounds[t + 1])[j]));
}

/// The end of task `t` is the start of task `t + 1`.
pub proof fn lemma_pl_next(c: Ctx, pbits: u64, p: int, bounds: Seq<int>, t: int)
    requires 0 <= bounds[t], bounds[t] <= bounds[t + 1], t + 1 < bounds.len(),
    ensures
        pl(c, pbits, p, bounds, t, elist(c, bounds[t], bounds[t + 1]).len() as int) == plist(c, pbits, p, 0, bounds[t + 1]),
{
    lemma_filt_plist(c, pbits, p, bounds[t], bounds[t + 1]);
    lemma_plist_append(c, pbits, p, 0, bounds[t], bounds[t + 1]);
}

/// The start of task `t`.
pub proof fn lemma_pl_start(c: Ctx, pbits: u64, p: int, bounds: Seq<int>, t: int)
    ensures pl(c, pbits, p, bounds, t, 0) == plist(c, pbits, p, 0, bounds[t]),
{
    assert(plist(c, pbits, p, 0, bounds[t]) + Seq::<int>::empty() =~= plist(c, pbits, p, 0, bounds[t]));
}

/// `filt` of a prefix is at most the whole filtered list.
pub proof fn lemma_filt_len(c: Ctx, pbits: u64, p: int, el: Seq<int>, j: int, j2: int)
    requires 0 <= j <= j2,
    ensures filt(c, pbits, p, el, j).len() <= filt(c, pbits, p, el, j2).len(),
    decreases j2 - j,
{
    if j2 > j {
        lemma_filt_len(c, pbits, p, el, j, j2 - 1);
    }
}

/// `plist` grows with its end.
pub proof fn lemma_plist_mono(c: Ctx, pbits: u64, p: int, lo: int, hi: int, hi2: int)
    requires lo <= hi <= hi2,
    ensures plist(c, pbits, p, lo, hi).len() <= plist(c, pbits, p, lo, hi2).len(),
    decreases hi2 - hi,
{
    if hi2 > hi {
        lemma_plist_mono(c, pbits, p, lo, hi, hi2 - 1);
    }
}

/// While task `t` reads its entry `j` of partition `p`, the entries read so far plus this one fit in `plist(p, 0, q)`.
pub proof fn lemma_pl_room(c: Ctx, pbits: u64, p: int, bounds: Seq<int>, t: int, j: int, nt: int)
    requires
        0 <= t < nt, bounds.len() == nt + 1, bounds[0] == 0, bounds[nt] == c.q,
        forall|u: int| 0 <= u < nt ==> #[trigger] bounds[u] <= bounds[u + 1],
        0 <= j < elist(c, bounds[t], bounds[t + 1]).len(),
        epart(c, pbits, elist(c, bounds[t], bounds[t + 1])[j]) == p,
    ensures pl(c, pbits, p, bounds, t, j).len() < plist(c, pbits, p, 0, c.q).len(),
{
    let el = elist(c, bounds[t], bounds[t + 1]);
    lemma_bounds_mono(bounds, nt, 0, t);
    lemma_pl_step(c, pbits, p, bounds, t, j);
    lemma_filt_len(c, pbits, p, el, j + 1, el.len() as int);
    lemma_pl_next(c, pbits, p, bounds, t);
    lemma_bounds_mono(bounds, nt, t + 1, nt);
    lemma_plist_mono(c, pbits, p, 0, bounds[t + 1], c.q);
}

/// The task bounds are monotone.
pub proof fn lemma_bounds_mono(bounds: Seq<int>, nt: int, a: int, b: int)
    requires
        bounds.len() == nt + 1, 0 <= a <= b <= nt,
        forall|u: int| 0 <= u < nt ==> #[trigger] bounds[u] <= bounds[u + 1],
    ensures bounds[a] <= bounds[b],
    decreases b - a,
{
    if b > a {
        lemma_bounds_mono(bounds, nt, a, b - 1);
        assert(bounds[b - 1] <= bounds[b]);
    }
}

/// The facts of `pres_ok`.
pub proof fn lemma_pres(pres: Seq<PreOut>, c: Ctx, pbits: u64, bounds: Seq<int>)
    requires pres_ok(pres, c, pbits, bounds),
    ensures
        bounds.len() == pres.len() + 1,
        bounds[0] == 0,
        bounds[pres.len() as int] == c.q,
        forall|t: int| 0 <= t < pres.len() ==> #[trigger] bounds[t] <= bounds[t + 1],
        forall|t: int| 0 <= t < pres.len() ==> pre_out_ok(#[trigger] pres[t], c, pbits, bounds[t], bounds[t + 1]),
{
    reveal(pres_ok);
}

/// `filt` of a prefix is a prefix of `filt` of a longer prefix.
pub proof fn lemma_filt_prefix_of(c: Ctx, pbits: u64, p: int, el: Seq<int>, j: int, j2: int)
    requires 0 <= j <= j2,
    ensures
        filt(c, pbits, p, el, j).len() <= filt(c, pbits, p, el, j2).len(),
        forall|i: int| 0 <= i < filt(c, pbits, p, el, j).len() ==> #[trigger] filt(c, pbits, p, el, j)[i] == filt(c, pbits, p, el, j2)[i],
    decreases j2 - j,
{
    if j2 > j {
        lemma_filt_prefix_of(c, pbits, p, el, j, j2 - 1);
    }
}

/// The entries of partition `p` read so far are a prefix of all its entries.
pub proof fn lemma_pl_prefix(c: Ctx, pbits: u64, p: int, bounds: Seq<int>, t: int, j: int, nt: int)
    requires
        0 <= t < nt, bounds.len() == nt + 1, bounds[0] == 0, bounds[nt] == c.q,
        forall|u: int| 0 <= u < nt ==> #[trigger] bounds[u] <= bounds[u + 1],
        0 <= j <= elist(c, bounds[t], bounds[t + 1]).len(),
    ensures
        pl(c, pbits, p, bounds, t, j).len() <= plist(c, pbits, p, 0, c.q).len(),
        forall|i: int| 0 <= i < pl(c, pbits, p, bounds, t, j).len() ==>
            #[trigger] pl(c, pbits, p, bounds, t, j)[i] == plist(c, pbits, p, 0, c.q)[i],
{
    let el = elist(c, bounds[t], bounds[t + 1]);
    lemma_bounds_mono(bounds, nt, 0, t);
    lemma_bounds_mono(bounds, nt, t + 1, nt);
    lemma_filt_prefix_of(c, pbits, p, el, j, el.len() as int);
    lemma_pl_next(c, pbits, p, bounds, t);
    lemma_plist_append(c, pbits, p, 0, bounds[t + 1], c.q);
    let a = plist(c, pbits, p, 0, bounds[t]);
    let full = pl(c, pbits, p, bounds, t, el.len() as int);
    assert forall|i: int| 0 <= i < pl(c, pbits, p, bounds, t, j).len() implies
        #[trigger] pl(c, pbits, p, bounds, t, j)[i] == plist(c, pbits, p, 0, c.q)[i] by {
        if i < a.len() {
            assert(pl(c, pbits, p, bounds, t, j)[i] == a[i]);
            assert(full[i] == a[i]);
        } else {
            assert(pl(c, pbits, p, bounds, t, j)[i] == filt(c, pbits, p, el, j)[i - a.len()]);
            assert(full[i] == filt(c, pbits, p, el, el.len() as int)[i - a.len()]);
        }
        assert(plist(c, pbits, p, 0, c.q)[i] == full[i]);
    }
}

/// At most one entry per row.
pub proof fn lemma_plist_len(c: Ctx, pbits: u64, p: int, lo: int, hi: int)
    requires lo <= hi,
    ensures plist(c, pbits, p, lo, hi).len() <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_plist_len(c, pbits, p, lo, hi - 1);
    }
}

/// The number of entries of each partition (`np = 2^pbits` partitions).
pub fn count_parts(pres: &Vec<PreOut>, np: usize, Ghost(c): Ghost<Ctx>, Ghost(pbits): Ghost<u64>, Ghost(bounds): Ghost<Seq<int>>) -> (cnt: Vec<usize>)
    requires pres_ok(pres@, c, pbits, bounds), np as int == pow2u(pbits), pbits <= MAX_PBITS, 0 <= c.q <= usize::MAX,
    ensures
        cnt@.len() == np,
        forall|p: int| 0 <= p < np ==> #[trigger] cnt@[p] as int == plist(c, pbits, p, 0, c.q).len(),
{
    let mut cnt: Vec<usize> = vec![0usize; np];
    proof {
        lemma_pres(pres@, c, pbits, bounds);
        assert forall|p: int| 0 <= p < np implies #[trigger] cnt@[p] as int == plist(c, pbits, p, 0, bounds[0]).len() by {
            assert(cloned(0usize, cnt@[p]));
        }
    }
    let nt = pres.len();
    let mut t: usize = 0;
    while t < nt
        invariant
            pres_ok(pres@, c, pbits, bounds), np as int == pow2u(pbits), pbits <= MAX_PBITS, 0 <= c.q <= usize::MAX,
            nt == pres@.len(), t <= nt, cnt@.len() == np,
            forall|p: int| 0 <= p < np ==> #[trigger] cnt@[p] as int == plist(c, pbits, p, 0, bounds[t as int]).len(),
        decreases nt - t,
    {
        proof {
            lemma_pres(pres@, c, pbits, bounds);
            lemma_bounds_mono(bounds, nt as int, 0, t as int);
            assert forall|p: int| 0 <= p < np implies #[trigger] cnt@[p] as int == pl(c, pbits, p, bounds, t as int, 0).len() by {
                lemma_pl_start(c, pbits, p, bounds, t as int);
            }
        }
        let o = &pres[t];
        let ol = o.len;
        let mut j: usize = 0;
        while j < ol
            invariant
                pres_ok(pres@, c, pbits, bounds), np as int == pow2u(pbits), pbits <= MAX_PBITS, 0 <= c.q <= usize::MAX,
                nt == pres@.len(), t < nt, cnt@.len() == np,
                o == &pres@[t as int], ol == o.len,
                pre_out_ok(*o, c, pbits, bounds[t as int], bounds[t + 1]),
                0 <= bounds[t as int] <= bounds[t + 1],
                j <= ol,
                forall|p: int| 0 <= p < np ==> #[trigger] cnt@[p] as int == pl(c, pbits, p, bounds, t as int, j as int).len(),
            decreases ol - j,
        {
            let ghost el = elist(c, bounds[t as int], bounds[t + 1]);
            let p0 = o.ep[j] as usize;
            proof {
                lemma_pres(pres@, c, pbits, bounds);
                lemma_elist_range(c, bounds[t as int], bounds[t + 1], j as int);
                crate::agent::collect::lemma_tpart_range(p_tag(c, el[j as int]), pbits);
                assert(p0 < np);
                assert forall|p: int| 0 <= p < np implies #[trigger] pl(c, pbits, p, bounds, t as int, j as int + 1)
                    == if epart(c, pbits, el[j as int]) == p { pl(c, pbits, p, bounds, t as int, j as int).push(el[j as int]) }
                       else { pl(c, pbits, p, bounds, t as int, j as int) } by {
                    lemma_pl_step(c, pbits, p, bounds, t as int, j as int);
                }
                lemma_pl_room(c, pbits, p0 as int, bounds, t as int, j as int, nt as int);
                lemma_plist_len(c, pbits, p0 as int, 0, c.q);
            }
            let v = cnt[p0];
            cnt[p0] = v + 1;
            j = j + 1;
        }
        proof {
            assert forall|p: int| 0 <= p < np implies #[trigger] cnt@[p] as int == plist(c, pbits, p, 0, bounds[t + 1]).len() by {
                lemma_pl_next(c, pbits, p, bounds, t as int);
            }
        }
        t = t + 1;
    }
    cnt
}

} // verus!
