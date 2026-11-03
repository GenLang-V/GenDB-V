//! The customer task (`CTask`): the buckets `[b0, b1)` of every scan task's output (`agent::scan`), i.e. the
//! customer rows `[min(b0 * CPB, nc), min(b1 * CPB, nc))`.
//!
//! Per bucket `b` (customer rows `base = b * CPB` onwards): every scan task's bucket-`b` entries add their encoded
//! order revenue (`agent::enc`) to the accumulator `acc[row - base]`; then each customer row of the bucket is checked
//! positional (`c_custkey[a] == cbase + a`), its accumulator read and reset to zero, and the customer offered to a
//! top-`TOPN` buffer (`common::topn`) when it can enter it and its nation exists. A customer's accumulator ends as
//! its total over the scan tasks' lists (`osum`); on sorted keys that is its revenue `ctot` (`lemma_bucket_total`,
//! by the filter law of `common::filter_sum` per scan task).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::cols::*;
use crate::agent::normal::*;
use crate::agent::xcols::*;
use crate::agent::enc::*;
use crate::agent::runs::*;
use crate::agent::scan::*;
use crate::agent::answer::*;
use crate::agent::common::topn::*;
use crate::agent::common::filter_sum::*;

verus! {

/// Capacity of the top lists (the statement's LIMIT).
pub const TOPN: usize = 20;

// ------------------------------------------------------------------------------------------------ specifications

/// The value of a customer's group in the answer's terms.
pub open spec fn cval(sv: StoresView, dlo: int, dhi: int) -> spec_fn(int) -> int { |a: int| ctot(sv, dlo, dhi, a) }

/// The customer keys `[ca, cb)` are positional: `c_custkey[r] == cbase + r`.
pub open spec fn cust_pos(sv: StoresView, cbase: int, ca: int, cb: int) -> bool {
    forall|r: int| ca <= r < cb ==> #[trigger] ck(sv)[r] as int == cbase + r
}

/// Customer row `a`'s term of orders row `j` (by the order's customer row): the order's revenue when it is in the
/// window with customer row `a`.
pub open spec fn tsum_of(sv: StoresView, dlo: int, dhi: int, cbase: int, a: int) -> spec_fn(int) -> int {
    |j: int| if win(sv, dlo, dhi, j) && crow(sv, cbase, j) == a { ksum(sv, okey(sv, j), 0, n_l(sv)) } else { 0 }
}

pub open spec fn tcnt_of(sv: StoresView, dlo: int, dhi: int, cbase: int, a: int) -> spec_fn(int) -> int {
    |j: int| if win(sv, dlo, dhi, j) && crow(sv, cbase, j) == a { kcnt(sv, okey(sv, j), 0, n_l(sv)) as int } else { 0 }
}

/// The same terms by the customer key (`cmatch`).
pub open spec fn fsum(sv: StoresView, dlo: int, dhi: int, a: int) -> spec_fn(int) -> int {
    |j: int| if cmatch(sv, dlo, dhi, a, j) { ksum(sv, ok(sv)[j] as int, 0, n_l(sv)) } else { 0 }
}

pub open spec fn fcnt(sv: StoresView, dlo: int, dhi: int, a: int) -> spec_fn(int) -> int {
    |j: int| if cmatch(sv, dlo, dhi, a, j) { kcnt(sv, ok(sv)[j] as int, 0, n_l(sv)) as int } else { 0 }
}

/// Customer `a`'s sums over the bucket-`b` lists of the first `t` scan outputs.
pub open spec fn osum(c: Cols, sv: StoresView, outs: Seq<SOut>, b: int, a: int, t: int) -> int
    decreases t,
{
    if t <= 0 { 0 } else {
        osum(c, sv, outs, b, a, t - 1)
            + lsum_of(tsum_of(sv, c.dlo as int, c.dhi as int, c.cbase as int, a), outs[t - 1].lists@[b], outs[t - 1].cnt@[b] as int)
    }
}

pub open spec fn ocnt(c: Cols, sv: StoresView, outs: Seq<SOut>, b: int, a: int, t: int) -> int
    decreases t,
{
    if t <= 0 { 0 } else {
        ocnt(c, sv, outs, b, a, t - 1)
            + lsum_of(tcnt_of(sv, c.dlo as int, c.dhi as int, c.cbase as int, a), outs[t - 1].lists@[b], outs[t - 1].cnt@[b] as int)
    }
}

/// The scan outputs are complete for bucket `b`: their order ranges `os` partition the orders and each output's
/// bucket `b` is `bucket_ok` over its range.
#[verifier::opaque]
pub open spec fn outs_ok(c: Cols, sv: StoresView, outs: Seq<SOut>, os: Seq<int>, nb: int, b: int) -> bool {
    &&& outs.len() >= 1 && os.len() == outs.len() + 1 && os[0] == 0 && os[outs.len() as int] == n_o(sv)
    &&& forall|t: int| 0 <= t < outs.len() ==> #[trigger] os[t] <= os[t + 1]
    &&& forall|t: int| 0 <= t < outs.len() ==> #[trigger] out_wf(outs[t], nb)
    &&& forall|t: int| 0 <= t < outs.len() ==> #[trigger] bucket_ok(c, sv, outs[t].rv@, outs[t].cnt@,
            outs[t].lists@, outs[t].rcap as int, os[t], os[t + 1], b)
}

/// The shape of a scan output with `nb` buckets.
pub open spec fn out_wf(o: SOut, nb: int) -> bool {
    &&& o.nb == nb && o.rv@.len() == nb * o.rcap && o.cnt@.len() == nb && o.lists@.len() == nb
    &&& nb * o.rcap <= usize::MAX
}

/// The groups among the customers `lo..x`, ascending.
pub open spec fn grange(sv: StoresView, dlo: int, dhi: int, lo: int, x: int) -> Seq<int>
    decreases x - lo,
{
    if x <= lo { Seq::empty() } else {
        let d = grange(sv, dlo, dhi, lo, x - 1);
        if is_group(sv, dlo, dhi, x - 1) { d.push(x - 1) } else { d }
    }
}

// ------------------------------------------------------------------------------------------------ lemmas

pub proof fn lemma_grange(sv: StoresView, dlo: int, dhi: int, lo: int, x: int)
    requires lo <= x,
    ensures
        grange(sv, dlo, dhi, lo, x).no_duplicates(),
        forall|y: int| #[trigger] grange(sv, dlo, dhi, lo, x).contains(y) <==> lo <= y < x && is_group(sv, dlo, dhi, y),
    decreases x - lo,
{
    if x > lo {
        lemma_grange(sv, dlo, dhi, lo, x - 1);
        let d = grange(sv, dlo, dhi, lo, x - 1);
        if is_group(sv, dlo, dhi, x - 1) {
            let e = d.push(x - 1);
            assert forall|y: int| #[trigger] e.contains(y) <==> lo <= y < x && is_group(sv, dlo, dhi, y) by {
                if e.contains(y) {
                    let q = choose|q: int| 0 <= q < e.len() && e[q] == y;
                    if q < d.len() { assert(d[q] == y); assert(d.contains(y)); }
                }
                if lo <= y < x && is_group(sv, dlo, dhi, y) {
                    if y < x - 1 {
                        assert(d.contains(y));
                        let q = choose|q: int| 0 <= q < d.len() && d[q] == y;
                        assert(e[q] == y);
                    } else {
                        assert(e[d.len() as int] == y);
                    }
                }
            }
            assert forall|a: int, b: int| 0 <= a < b < e.len() implies e[a] != e[b] by {
                if a < d.len() && b < d.len() {
                    assert(d[a] != d[b]);
                } else if a < d.len() {
                    assert(d.contains(d[a]));
                } else if b < d.len() {
                    assert(d.contains(d[b]));
                }
            }
        }
    }
}

/// The customer sums as range sums.
pub proof fn lemma_c_rsum(sv: StoresView, dlo: int, dhi: int, a: int, lo: int, hi: int)
    ensures
        csum(sv, dlo, dhi, a, lo, hi) == rsum(fsum(sv, dlo, dhi, a), lo, hi),
        ccnt(sv, dlo, dhi, a, lo, hi) as int == rsum(fcnt(sv, dlo, dhi, a), lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_c_rsum(sv, dlo, dhi, a, lo, hi - 1);
    }
}

/// Range sums of pointwise equal terms are equal.
proof fn lemma_rsum_ext(f: spec_fn(int) -> int, g: spec_fn(int) -> int, lo: int, hi: int)
    requires forall|j: int| lo <= j < hi ==> #[trigger] f(j) == g(j),
    ensures rsum(f, lo, hi) == rsum(g, lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_rsum_ext(f, g, lo, hi - 1);
    }
}

/// A scan output's bucket-`b` list sum of customer `a` (of bucket `b`) is its range sum over the output's orders.
proof fn lemma_list_range(c: Cols, sv: StoresView, o: SOut, olo: int, ohi: int, b: int, a: int)
    requires
        cols_ok(c, sv), lk_sorted(sv), olo <= ohi,
        bucket_ok(c, sv, o.rv@, o.cnt@, o.lists@, o.rcap as int, olo, ohi, b),
        0 <= a < n_c(sv), a / (CPB as int) == b,
    ensures
        lsum_of(tsum_of(sv, c.dlo as int, c.dhi as int, c.cbase as int, a), o.lists@[b], o.cnt@[b] as int)
            == rsum(tsum_of(sv, c.dlo as int, c.dhi as int, c.cbase as int, a), olo, ohi),
        lsum_of(tcnt_of(sv, c.dlo as int, c.dhi as int, c.cbase as int, a), o.lists@[b], o.cnt@[b] as int)
            == rsum(tcnt_of(sv, c.dlo as int, c.dhi as int, c.cbase as int, a), olo, ohi),
{
    let (dlo, dhi, cbase) = (c.dlo as int, c.dhi as int, c.cbase as int);
    let l = o.lists@[b];
    let q = |j: int| ohit(sv, dlo, dhi, cbase, j) && obk(sv, cbase, j) == b;
    let fs = tsum_of(sv, dlo, dhi, cbase, a);
    let fc = tcnt_of(sv, dlo, dhi, cbase, a);
    assert forall|j: int| olo <= j < ohi && q(j) implies #[trigger] l.contains(j) by {}
    assert forall|j: int| olo <= j < ohi && !q(j) implies #[trigger] fs(j) == 0 && fc(j) == 0 by {
        if win(sv, dlo, dhi, j) && crow(sv, cbase, j) == a {
            assert(qualifies(sv, dlo, dhi, cbase, j));
            assert(obk(sv, cbase, j) == b);
            assert(kcnt(sv, okey(sv, j), 0, n_l(sv)) == 0);
            lemma_k_bounds(sv, okey(sv, j), 0, n_l(sv));
        }
    }
    assert forall|j: int| olo <= j < ohi && !q(j) implies #[trigger] fs(j) == 0 by {}
    assert forall|j: int| olo <= j < ohi && !q(j) implies #[trigger] fc(j) == 0 by {}
    lemma_filter_sum(fs, q, l, olo, ohi);
    lemma_filter_sum(fc, q, l, olo, ohi);
}

/// Over the first `t` scan outputs, customer `a`'s list sums are its range sums over their orders.
proof fn lemma_osum_range(c: Cols, sv: StoresView, outs: Seq<SOut>, os: Seq<int>, nb: int, b: int, a: int, t: int)
    requires
        cols_ok(c, sv), lk_sorted(sv), outs_ok(c, sv, outs, os, nb, b), 0 <= t <= outs.len(),
        0 <= a < n_c(sv), a / (CPB as int) == b,
    ensures
        osum(c, sv, outs, b, a, t) == rsum(tsum_of(sv, c.dlo as int, c.dhi as int, c.cbase as int, a), 0, os[t]),
        ocnt(c, sv, outs, b, a, t) == rsum(tcnt_of(sv, c.dlo as int, c.dhi as int, c.cbase as int, a), 0, os[t]),
        0 <= os[t],
    decreases t,
{
    reveal(outs_ok);
    if t > 0 {
        lemma_osum_range(c, sv, outs, os, nb, b, a, t - 1);
        assert(os[t - 1] <= os[t]);
        assert(bucket_ok(c, sv, outs[t - 1].rv@, outs[t - 1].cnt@, outs[t - 1].lists@,
            outs[t - 1].rcap as int, os[t - 1], os[t], b));
        lemma_list_range(c, sv, outs[t - 1], os[t - 1], os[t], b, a);
        lemma_rsum_split(tsum_of(sv, c.dlo as int, c.dhi as int, c.cbase as int, a), 0, os[t - 1], os[t]);
        lemma_rsum_split(tcnt_of(sv, c.dlo as int, c.dhi as int, c.cbase as int, a), 0, os[t - 1], os[t]);
    }
}

/// On sorted keys, a positional customer's total over all scan outputs' bucket lists is its revenue.
pub proof fn lemma_bucket_total(c: Cols, sv: StoresView, outs: Seq<SOut>, os: Seq<int>, nb: int, b: int, a: int)
    requires
        cols_ok(c, sv), lk_sorted(sv), outs_ok(c, sv, outs, os, nb, b),
        0 <= a < n_c(sv), a / (CPB as int) == b, ck(sv)[a] as int == c.cbase + a,
    ensures
        osum(c, sv, outs, b, a, outs.len() as int) == ctot(sv, c.dlo as int, c.dhi as int, a),
        ocnt(c, sv, outs, b, a, outs.len() as int) == ctcnt(sv, c.dlo as int, c.dhi as int, a) as int,
{
    let (dlo, dhi, cbase) = (c.dlo as int, c.dhi as int, c.cbase as int);
    reveal(outs_ok);
    lemma_osum_range(c, sv, outs, os, nb, b, a, outs.len() as int);
    let no = n_o(sv);
    assert forall|j: int| 0 <= j < no implies #[trigger] tsum_of(sv, dlo, dhi, cbase, a)(j) == fsum(sv, dlo, dhi, a)(j) by {
        assert(cmatch(sv, dlo, dhi, a, j) == (win(sv, dlo, dhi, j) && crow(sv, cbase, j) == a));
    }
    assert forall|j: int| 0 <= j < no implies #[trigger] tcnt_of(sv, dlo, dhi, cbase, a)(j) == fcnt(sv, dlo, dhi, a)(j) by {
        assert(cmatch(sv, dlo, dhi, a, j) == (win(sv, dlo, dhi, j) && crow(sv, cbase, j) == a));
    }
    lemma_rsum_ext(tsum_of(sv, dlo, dhi, cbase, a), fsum(sv, dlo, dhi, a), 0, no);
    lemma_rsum_ext(tcnt_of(sv, dlo, dhi, cbase, a), fcnt(sv, dlo, dhi, a), 0, no);
    lemma_c_rsum(sv, dlo, dhi, a, 0, no);
}

/// A customer row beyond the table has no terms in any list (every listed order's customer row is in the table).
proof fn lemma_osum_beyond(c: Cols, sv: StoresView, outs: Seq<SOut>, os: Seq<int>, nb: int, b: int, a: int, t: int)
    requires outs_ok(c, sv, outs, os, nb, b), 0 <= t <= outs.len(), a >= n_c(sv),
    ensures osum(c, sv, outs, b, a, t) == 0, ocnt(c, sv, outs, b, a, t) == 0,
    decreases t,
{
    reveal(outs_ok);
    if t > 0 {
        lemma_osum_beyond(c, sv, outs, os, nb, b, a, t - 1);
        let o = outs[t - 1];
        assert(bucket_ok(c, sv, o.rv@, o.cnt@, o.lists@, o.rcap as int, os[t - 1], os[t], b));
        lemma_lsum_zero(c, sv, o.lists@[b], o.cnt@[b] as int, a);
    }
}

/// List sums of a customer row beyond the table over listed (qualifying) orders vanish.
proof fn lemma_lsum_zero(c: Cols, sv: StoresView, l: Seq<int>, n: int, a: int)
    requires
        0 <= n <= l.len(), a >= n_c(sv),
        forall|p: int| 0 <= p < n ==> ohit(sv, c.dlo as int, c.dhi as int, c.cbase as int, #[trigger] l[p]),
    ensures
        lsum_of(tsum_of(sv, c.dlo as int, c.dhi as int, c.cbase as int, a), l, n) == 0,
        lsum_of(tcnt_of(sv, c.dlo as int, c.dhi as int, c.cbase as int, a), l, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_lsum_zero(c, sv, l, n - 1, a);
        assert(ohit(sv, c.dlo as int, c.dhi as int, c.cbase as int, l[n - 1]));
    }
}

// ------------------------------------------------------------------------------------------------ nations

/// Whether customer row `a` has a nation row (a scan of the nation keys).
pub fn nation_of(c: &Cols, a: usize, Ghost(sv): Ghost<StoresView>) -> (r: Option<usize>)
    requires cols_ok(*c, sv), a < c.nc,
    ensures
        r is Some <==> natok(sv, a as int),
        r matches Some(n) ==> n < c.nn && nk(sv)[n as int] == cnk(sv)[a as int],
    no_unwind
{
    let k = c.cnk[a];
    let mut i: usize = 0;
    while i < c.nn
        invariant cols_ok(*c, sv), a < c.nc, k == cnk(sv)[a as int], i <= c.nn,
            forall|j: int| 0 <= j < i ==> #[trigger] nk(sv)[j] != k,
        decreases c.nn - i,
    {
        if c.nk[i] == k {
            return Some(i);
        }
        i = i + 1;
    }
    None
}

// ------------------------------------------------------------------------------------------------ selection

/// The selection invariant over the customers `lo..xe`: the buffer holds a top list of the offered groups `s`
/// (a subset of the range's groups); a group not offered was below the full buffer's last revenue.
pub open spec fn sel_inv(t: Top, s: Seq<int>, sv: StoresView, dlo: int, dhi: int, lo: int, xe: int) -> bool {
    &&& top_inv(t, s, cval(sv, dlo, dhi))
    &&& t.cap == TOPN
    &&& forall|y: int| #[trigger] s.contains(y) ==> grange(sv, dlo, dhi, lo, xe).contains(y)
    &&& forall|y: int| #[trigger] grange(sv, dlo, dhi, lo, xe).contains(y) && !s.contains(y)
            ==> t.k == t.cap && cval(sv, dlo, dhi)(y) <= t.vals@[t.cap - 1]
}

/// At the end of the range, the buffer is a top list of the range's groups.
proof fn lemma_part_top(t: Top, s: Seq<int>, sv: StoresView, dlo: int, dhi: int, lo: int, hi: int)
    requires sel_inv(t, s, sv, dlo, dhi, lo, hi), lo <= hi,
    ensures top_of(tsel(t), grange(sv, dlo, dhi, lo, hi), cval(sv, dlo, dhi), TOPN as int),
{
    let g = grange(sv, dlo, dhi, lo, hi);
    let sel = tsel(t);
    let vf = cval(sv, dlo, dhi);
    lemma_grange(sv, dlo, dhi, lo, hi);
    assert forall|i: int| 0 <= i < s.len() implies g.contains(#[trigger] s[i]) by {
        assert(s.contains(s[i]));
    }
    lemma_sub_len(s, g);
    assert forall|i: int| 0 <= i < sel.len() implies g.contains(#[trigger] sel[i]) by {
        assert(s.contains(sel[i]));
    }
    if exists|y: int| #[trigger] g.contains(y) && !s.contains(y) {
        let y = choose|y: int| #[trigger] g.contains(y) && !s.contains(y);
        assert(t.k == t.cap);
    } else {
        assert forall|i: int| 0 <= i < g.len() implies s.contains(#[trigger] g[i]) by {
            assert(g.contains(g[i]));
        }
        lemma_sub_len(g, s);
    }
    if sel.len() > 0 {
        assert(t.vals@[t.k - 1] as int == vf(t.rows@[t.k - 1] as int));
        assert forall|y: int| #[trigger] g.contains(y) && !sel.contains(y) implies vf(y) <= vf(sel.last()) by {
            if s.contains(y) {
            } else {
                assert(t.k == t.cap);
            }
        }
    }
}

/// One customer of the scan: offered when its accumulator `e` (its encoded revenue) can enter the buffer and its
/// nation exists.
#[inline(always)]
fn offer_one(c: &Cols, a: usize, e: i64, top: &mut Top, Ghost(s): Ghost<Seq<int>>, Ghost(sv): Ghost<StoresView>,
    Ghost(lo): Ghost<int>) -> (r: Ghost<Seq<int>>)
    requires
        cols_ok(*c, sv), lo <= a < c.nc,
        enc_ok(e, ctot(sv, c.dlo as int, c.dhi as int, a as int), ctcnt(sv, c.dlo as int, c.dhi as int, a as int) as int),
        forall|y: int| lo <= y < a ==> 0 <= #[trigger] ctot(sv, c.dlo as int, c.dhi as int, y) < CAP,
        sel_inv(*old(top), s, sv, c.dlo as int, c.dhi as int, lo, a as int),
    ensures sel_inv(*final(top), r@, sv, c.dlo as int, c.dhi as int, lo, a + 1),
    no_unwind
{
    let ghost (dlo, dhi) = (c.dlo as int, c.dhi as int);
    let ghost vf = cval(sv, dlo, dhi);
    let ghost s0 = s;
    let ghost t0 = *top;
    let ghost mut s1 = s;
    proof {
        lemma_enc_dec(e, ctot(sv, dlo, dhi, a as int), ctcnt(sv, dlo, dhi, a as int) as int);
        lemma_grange(sv, dlo, dhi, lo, a as int);
        lemma_grange(sv, dlo, dhi, lo, a + 1);
    }
    proof {
        if top.k == top.cap {
            let r = top.rows@[top.cap - 1] as int;
            assert(tsel(*top)[top.cap - 1] == r);
            assert(s.contains(r));
            assert(grange(sv, dlo, dhi, lo, a as int).contains(r));
            assert(top.vals@[top.cap - 1] as int == ctot(sv, dlo, dhi, r));
        }
    }
    let gate: i64 = if top.k < top.cap { 0 } else { (top.vals[top.cap - 1] + 1) as i64 };
    if e > gate {
        if nation_of(c, a, Ghost(sv)).is_some() {
            proof {
                assert(is_group(sv, dlo, dhi, a as int));
                assert(!s.contains(a as int)) by {
                    if s.contains(a as int) { assert(grange(sv, dlo, dhi, lo, a as int).contains(a as int)); }
                }
            }
            top_offer(top, a, (e - 1) as i128, Ghost(s), Ghost(vf));
            proof { s1 = s.push(a as int); }
        }
    }
    proof {
        let g0 = grange(sv, dlo, dhi, lo, a as int);
        let g1 = grange(sv, dlo, dhi, lo, a + 1);
        assert forall|y: int| #[trigger] s1.contains(y) implies g1.contains(y) by {
            if s1 != s0 { vstd::seq_lib::lemma_seq_contains_after_push(s0, a as int, y); }
            if y != a as int { assert(s0.contains(y)); assert(g0.contains(y)); }
        }
        assert forall|y: int| #[trigger] g1.contains(y) && !s1.contains(y)
            implies top.k == top.cap && vf(y) <= top.vals@[top.cap - 1] by {
            if s1 != s0 { vstd::seq_lib::lemma_seq_contains_after_push(s0, a as int, y); }
            if y == a as int {
                assert(is_group(sv, dlo, dhi, y));
                assert(s1 == s0);
                assert(t0.k == t0.cap);
            } else {
                assert(g0.contains(y));
                assert(!s0.contains(y));
                assert(t0.k == t0.cap && vf(y) <= t0.vals@[t0.cap - 1]);
            }
        }
    }
    Ghost(s1)
}

// ------------------------------------------------------------------------------------------------ the task

pub struct CTask {
    pub c: Cols,
    pub outs: Arc<Vec<SOut>>,
    pub os: Ghost<Seq<int>>,
    pub nb: usize,
    pub b0: usize,
    pub b1: usize,
    pub acc: Vec<i64>,
    pub top: Top,
    pub sv: Ghost<StoresView>,
}

pub struct COut {
    pub ok: bool,
    pub top: Top,
    pub acc: Vec<i64>,
}

/// The customer rows of the buckets from `b`: `min(b * CPB, nc)`.
pub open spec fn bstart(b: int, nc: int) -> int { if b * (CPB as int) < nc { b * (CPB as int) } else { nc } }

pub open spec fn cust_pre(t: CTask) -> bool {
    &&& cols_ok(t.c, t.sv@) && lk_sorted(t.sv@)
    &&& t.c.nc < 0x8000_0000
    &&& t.b0 <= t.b1 <= t.nb && t.nb * CPB < 0x1_0000_0000_0000 && t.nb * CPB < t.c.nc + CPB
    &&& forall|b: int| t.b0 <= b < t.b1 ==> #[trigger] outs_ok(t.c, t.sv@, (*t.outs)@, t.os@, t.nb as int, b)
    &&& (*t.outs)@.len() >= 1
    &&& t.acc@.len() == CPB && forall|x: int| 0 <= x < CPB ==> #[trigger] t.acc@[x] == 0
    &&& top_inv(t.top, Seq::empty(), cval(t.sv@, t.c.dlo as int, t.c.dhi as int)) && t.top.cap == TOPN
}

pub open spec fn cust_post(c: Cols, sv: StoresView, lo: int, hi: int, out: COut) -> bool {
    &&& out.top.cap == TOPN
    &&& out.ok ==> {
        &&& cust_pos(sv, c.cbase as int, lo, hi)
        &&& exists|s: Seq<int>| top_inv(out.top, s, cval(sv, c.dlo as int, c.dhi as int))
        &&& top_of(tsel(out.top), grange(sv, c.dlo as int, c.dhi as int, lo, hi), cval(sv, c.dlo as int, c.dhi as int), TOPN as int)
        &&& forall|a: int| lo <= a < hi ==> 0 <= #[trigger] ctot(sv, c.dlo as int, c.dhi as int, a) < CAP
    }
}

/// The accumulators of bucket `b` after the lists of the first `t` scan outputs and `p` entries of output `t`.
#[verifier::opaque]
pub open spec fn acc_rel(c: Cols, sv: StoresView, outs: Seq<SOut>, b: int, acc: Seq<i64>, t: int, p: int) -> bool {
    let (dlo, dhi, cbase) = (c.dlo as int, c.dhi as int, c.cbase as int);
    &&& acc.len() == CPB
    &&& forall|x: int| 0 <= x < CPB ==> enc_ok(#[trigger] acc[x],
            osum(c, sv, outs, b, b * (CPB as int) + x, t)
                + if t < outs.len() { lsum_of(tsum_of(sv, dlo, dhi, cbase, b * (CPB as int) + x), outs[t].lists@[b], p) } else { 0 },
            ocnt(c, sv, outs, b, b * (CPB as int) + x, t)
                + if t < outs.len() { lsum_of(tcnt_of(sv, dlo, dhi, cbase, b * (CPB as int) + x), outs[t].lists@[b], p) } else { 0 })
}

/// The facts of entry `p` of scan output `t`'s bucket `b`: its order `j`, the position inside the buffers, the
/// customer row (inside bucket `b`) and the encoded revenue.
proof fn lemma_entry(c: Cols, sv: StoresView, outs: Seq<SOut>, os: Seq<int>, nb: int, b: int, t: int, p: int)
    requires lk_sorted(sv), outs_ok(c, sv, outs, os, nb, b), 0 <= b < nb, 0 <= t < outs.len(), 0 <= p < outs[t].cnt@[b],
    ensures ({
        let o = outs[t];
        let j = o.lists@[b][p];
        let pos = b * o.rcap + p;
        &&& out_wf(o, nb) && 0 <= pos < nb * o.rcap && o.cnt@.len() == nb && o.lists@[b].len() == o.cnt@[b]
        &&& win(sv, c.dlo as int, c.dhi as int, j)
        &&& 0 <= o.rv@[pos] && pk_lo(o.rv@[pos]) == crow(sv, c.cbase as int, j) - b * (CPB as int)
        &&& b * (CPB as int) <= crow(sv, c.cbase as int, j) < b * (CPB as int) + CPB
        &&& pk_rev_ok(pk_hi(o.rv@[pos]), ksum(sv, okey(sv, j), 0, n_l(sv)), kcnt(sv, okey(sv, j), 0, n_l(sv)) as int)
    }),
{
    reveal(outs_ok);
    let o = outs[t];
    let j = o.lists@[b][p];
    assert(out_wf(o, nb));
    assert(bucket_ok(c, sv, o.rv@, o.cnt@, o.lists@, o.rcap as int, os[t], os[t + 1], b));
    assert(entry_ok(c, sv, o.rv@, o.rcap as int, b, p, j));
    lemma_pos_bound(b, p, nb, o.rcap as int);
    let cr = crow(sv, c.cbase as int, j);
    assert(b * 131072 <= cr < b * 131072 + 131072) by (nonlinear_arith) requires cr / 131072 == b, cr >= 0;
}

/// The shape facts of scan output `t`.
proof fn lemma_out_wf(c: Cols, sv: StoresView, outs: Seq<SOut>, os: Seq<int>, nb: int, b: int, t: int)
    requires outs_ok(c, sv, outs, os, nb, b), 0 <= t < outs.len(),
    ensures out_wf(outs[t], nb), outs.len() >= 1,
{
    reveal(outs_ok);
}

/// Adding entry `p` (order `j`, customer row `base + x`) to accumulator `x` steps the accumulators to `p + 1`.
proof fn lemma_acc_step(c: Cols, sv: StoresView, outs: Seq<SOut>, b: int, acc0: Seq<i64>, acc1: Seq<i64>, t: int, p: int,
    x: int, v: i64)
    requires
        acc_rel(c, sv, outs, b, acc0, t, p), 0 <= t < outs.len(), 0 <= p < outs[t].lists@[b].len(), 0 <= x < CPB,
        ({
            let j = outs[t].lists@[b][p];
            let a = b * (CPB as int) + x;
            let (dlo, dhi, cbase) = (c.dlo as int, c.dhi as int, c.cbase as int);
            &&& win(sv, dlo, dhi, j) && crow(sv, cbase, j) == a
            &&& acc1 == acc0.update(x, v)
            &&& enc_ok(v,
                osum(c, sv, outs, b, a, t) + lsum_of(tsum_of(sv, dlo, dhi, cbase, a), outs[t].lists@[b], p)
                    + ksum(sv, okey(sv, j), 0, n_l(sv)),
                ocnt(c, sv, outs, b, a, t) + lsum_of(tcnt_of(sv, dlo, dhi, cbase, a), outs[t].lists@[b], p)
                    + kcnt(sv, okey(sv, j), 0, n_l(sv)) as int)
        }),
    ensures acc_rel(c, sv, outs, b, acc1, t, p + 1),
{
    reveal(acc_rel);
    let (dlo, dhi, cbase) = (c.dlo as int, c.dhi as int, c.cbase as int);
    let l = outs[t].lists@[b];
    let j = l[p];
    assert forall|y: int| 0 <= y < CPB implies enc_ok(#[trigger] acc1[y],
        osum(c, sv, outs, b, b * (CPB as int) + y, t)
            + if t < outs.len() { lsum_of(tsum_of(sv, dlo, dhi, cbase, b * (CPB as int) + y), outs[t].lists@[b], p + 1) } else { 0 },
        ocnt(c, sv, outs, b, b * (CPB as int) + y, t)
            + if t < outs.len() { lsum_of(tcnt_of(sv, dlo, dhi, cbase, b * (CPB as int) + y), outs[t].lists@[b], p + 1) } else { 0 }) by {
        if y != x {
            assert(acc1[y] == acc0[y]);
            assert(crow(sv, cbase, j) != b * (CPB as int) + y);
        }
    }
}

/// The accumulators at the start of a bucket (all zero) and after a whole list (next output, no entry).
proof fn lemma_acc_start(c: Cols, sv: StoresView, outs: Seq<SOut>, b: int, acc: Seq<i64>)
    requires acc.len() == CPB, forall|x: int| 0 <= x < CPB ==> #[trigger] acc[x] == 0,
    ensures acc_rel(c, sv, outs, b, acc, 0, 0),
{
    reveal(acc_rel);
    assert forall|x: int| 0 <= x < CPB implies enc_ok(#[trigger] acc[x],
        osum(c, sv, outs, b, b * (CPB as int) + x, 0)
            + if 0 < outs.len() { lsum_of(tsum_of(sv, c.dlo as int, c.dhi as int, c.cbase as int, b * (CPB as int) + x), outs[0].lists@[b], 0) } else { 0 },
        ocnt(c, sv, outs, b, b * (CPB as int) + x, 0)
            + if 0 < outs.len() { lsum_of(tcnt_of(sv, c.dlo as int, c.dhi as int, c.cbase as int, b * (CPB as int) + x), outs[0].lists@[b], 0) } else { 0 }) by {
    }
}

proof fn lemma_acc_next(c: Cols, sv: StoresView, outs: Seq<SOut>, b: int, acc: Seq<i64>, t: int)
    requires acc_rel(c, sv, outs, b, acc, t, outs[t].cnt@[b] as int), 0 <= t < outs.len(),
    ensures acc_rel(c, sv, outs, b, acc, t + 1, 0),
{
    reveal(acc_rel);
    let (dlo, dhi, cbase) = (c.dlo as int, c.dhi as int, c.cbase as int);
    assert forall|x: int| 0 <= x < CPB implies enc_ok(#[trigger] acc[x],
        osum(c, sv, outs, b, b * (CPB as int) + x, t + 1)
            + if t + 1 < outs.len() { lsum_of(tsum_of(sv, dlo, dhi, cbase, b * (CPB as int) + x), outs[t + 1].lists@[b], 0) } else { 0 },
        ocnt(c, sv, outs, b, b * (CPB as int) + x, t + 1)
            + if t + 1 < outs.len() { lsum_of(tcnt_of(sv, dlo, dhi, cbase, b * (CPB as int) + x), outs[t + 1].lists@[b], 0) } else { 0 }) by {
    }
}

/// At the end of a bucket, accumulator `x` encodes customer `base + x`'s totals.
proof fn lemma_acc_end(c: Cols, sv: StoresView, outs: Seq<SOut>, b: int, acc: Seq<i64>, x: int)
    requires acc_rel(c, sv, outs, b, acc, outs.len() as int, 0), 0 <= x < CPB,
    ensures enc_ok(acc[x], osum(c, sv, outs, b, b * (CPB as int) + x, outs.len() as int),
        ocnt(c, sv, outs, b, b * (CPB as int) + x, outs.len() as int)),
{
    reveal(acc_rel);
}

/// Adds entry `p` of scan output `t`'s bucket `b` to the accumulators.
#[inline(always)]
fn add_entry(c: &Cols, o: &SOut, acc: &mut Vec<i64>, b: usize, p: usize, Ghost(sv): Ghost<StoresView>,
    Ghost(outs): Ghost<Seq<SOut>>, Ghost(os): Ghost<Seq<int>>, Ghost(nb): Ghost<int>, Ghost(t): Ghost<int>) -> (okc: bool)
    requires
        lk_sorted(sv), outs_ok(*c, sv, outs, os, nb, b as int), 0 <= t < outs.len(), outs[t] == *o, b < nb,
        p < o.cnt@[b as int], b * CPB < 0x1_0000_0000_0000,
        acc_rel(*c, sv, outs, b as int, old(acc)@, t, p as int), old(acc)@.len() == CPB,
    ensures
        final(acc)@.len() == old(acc)@.len(),
        okc ==> acc_rel(*c, sv, outs, b as int, final(acc)@, t, p + 1),
    no_unwind
{
    let ghost (dlo, dhi, cbase) = (c.dlo as int, c.dhi as int, c.cbase as int);
    let ghost l = o.lists@[b as int];
    let ghost j = l[p as int];
    proof {
        lemma_entry(*c, sv, outs, os, nb, b as int, t, p as int);
        assert(out_wf(*o, nb));
    }
    let pos = b * o.rcap + p;
    // the packed entry: encoded revenue and the customer row's offset in bucket `b`
    let pk = o.rv[pos] as u64;
    let x = (pk % 131072) as usize;
    let e = (pk / 131072) as i64;
    let ghost a = b * (CPB as int) + x;
    let ghost (s2, c2) = (ksum(sv, okey(sv, j), 0, n_l(sv)), kcnt(sv, okey(sv, j), 0, n_l(sv)) as int);
    let ghost (s1, c1) = (osum(*c, sv, outs, b as int, a, t) + lsum_of(tsum_of(sv, dlo, dhi, cbase, a), l, p as int),
        ocnt(*c, sv, outs, b as int, a, t) + lsum_of(tcnt_of(sv, dlo, dhi, cbase, a), l, p as int));
    proof {
        reveal(acc_rel);
        assert(a == b * (CPB as int) + x);
        assert(enc_ok(acc@[x as int], s1, c1));
    }
    match enc_combine(acc[x], e, Ghost(s1), Ghost(c1), Ghost(s2), Ghost(c2)) {
        Some(v) => {
            let ghost a0 = acc@;
            acc[x] = v;
            proof {
                lemma_acc_step(*c, sv, outs, b as int, a0, acc@, t, p as int, x as int, v);
            }
            true
        },
        None => false,
    }
}

impl WorkerTask for CTask {
    type Output = COut;

    open spec fn pre(&self) -> bool { cust_pre(*self) }

    open spec fn post(&self, out: COut) -> bool {
        cust_post(self.c, self.sv@, bstart(self.b0 as int, self.c.nc as int), bstart(self.b1 as int, self.c.nc as int), out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.b0 as u64, self.b1 as u64)
    }

    #[verifier::loop_isolation(false)]
    fn run(self) -> (out: COut) {
        let CTask { c, outs, os, nb, b0, b1, acc, top, sv } = self;
        let ghost sv = sv@;
        let ghost os = os@;
        let ghost (dlo, dhi, cbase) = (c.dlo as int, c.dhi as int, c.cbase as int);
        let ghost vf = cval(sv, dlo, dhi);
        let mut acc = acc;
        let mut top = top;
        let ov: &Vec<SOut> = &*outs;
        let ghost outv = ov@;
        let nt = ov.len();
        let nc = c.nc;
        let ghost lo = bstart(b0 as int, nc as int);
        let ghost mut s: Seq<int> = Seq::empty();
        proof {
            assert(grange(sv, dlo, dhi, lo, lo) =~= Seq::<int>::empty());
            assert(b0 * CPB <= nb * CPB) by (nonlinear_arith) requires b0 <= nb;
        }
        let mut b = b0;
        while b < b1
            invariant
                cols_ok(c, sv), lk_sorted(sv), nc == c.nc, nc < 0x8000_0000, b0 <= b <= b1 <= nb, nb * CPB < 0x1_0000_0000_0000,
                nb * CPB < nc + CPB, nt == outv.len(), outv == ov@, nt >= 1,
                forall|bb: int| b0 <= bb < b1 ==> #[trigger] outs_ok(c, sv, outv, os, nb as int, bb),
                acc@.len() == CPB, forall|x: int| 0 <= x < CPB ==> #[trigger] acc@[x] == 0,
                sel_inv(top, s, sv, dlo, dhi, lo, bstart(b as int, nc as int)),
                lo <= bstart(b as int, nc as int),
                cust_pos(sv, cbase, lo, bstart(b as int, nc as int)),
                forall|a: int| lo <= a < bstart(b as int, nc as int) ==> 0 <= #[trigger] ctot(sv, dlo, dhi, a) < CAP,
            decreases b1 - b,
        {
            proof {
                assert(b * CPB < nb * CPB) by (nonlinear_arith) requires b < nb;
                assert(b * CPB + CPB <= nb * CPB) by (nonlinear_arith) requires b < nb;
                assert(b * CPB < nc);
                assert(outs_ok(c, sv, outv, os, nb as int, b as int));
            }
            let base = b * CPB;
            // aggregation
            proof { lemma_acc_start(c, sv, outv, b as int, acc@); }
            let mut t: usize = 0;
            while t < nt
                invariant
                    cols_ok(c, sv), lk_sorted(sv), b0 <= b < b1 <= nb, nb * CPB < 0x1_0000_0000_0000, base == b * CPB,
                    b * CPB < 0x1_0000_0000_0000,
                    nt == outv.len(), outv == ov@, t <= nt, outs_ok(c, sv, outv, os, nb as int, b as int),
                    acc_rel(c, sv, outv, b as int, acc@, t as int, 0), acc@.len() == CPB,
                decreases nt - t,
            {
                let o = &ov[t];
                proof { lemma_out_wf(c, sv, outv, os, nb as int, b as int, t as int); }
                let n = o.cnt[b];
                let mut p: usize = 0;
                while p < n
                    invariant
                        cols_ok(c, sv), lk_sorted(sv), b0 <= b < b1 <= nb, base == b * CPB, b * CPB < 0x1_0000_0000_0000,
                        nt == outv.len(), outv == ov@, t < nt, *o == outv[t as int], n == o.cnt@[b as int], p <= n,
                        outs_ok(c, sv, outv, os, nb as int, b as int),
                        acc_rel(c, sv, outv, b as int, acc@, t as int, p as int), acc@.len() == CPB,
                    decreases n - p,
                {
                    if !add_entry(&c, o, &mut acc, b, p, Ghost(sv), Ghost(outv), Ghost(os), Ghost(nb as int), Ghost(t as int)) {
                        return COut { ok: false, top, acc };
                    }
                    p = p + 1;
                }
                proof { lemma_acc_next(c, sv, outv, b as int, acc@, t as int); }
                t = t + 1;
            }
            // selection over the bucket's customers
            let ghost acc0 = acc@;
            let w = if nc - base < CPB { nc - base } else { CPB };
            proof {
                assert(bstart(b as int, nc as int) == base);
                assert(bstart(b + 1, nc as int) == base + w);
            }
            let mut x: usize = 0;
            while x < w
                invariant
                    cols_ok(c, sv), lk_sorted(sv), nc == c.nc, nc < 0x8000_0000, b0 <= b < b1 <= nb, base == b * CPB,
                    base < nc, w <= CPB, base + w <= nc, x <= w, vf == cval(sv, dlo, dhi),
                    nt == outv.len(), outs_ok(c, sv, outv, os, nb as int, b as int),
                    acc@.len() == CPB,
                    forall|y: int| 0 <= y < x ==> #[trigger] acc@[y] == 0,
                    acc_rel(c, sv, outv, b as int, acc0, nt as int, 0),
                    forall|y: int| x <= y < CPB ==> #[trigger] acc@[y] == acc0[y],
                    sel_inv(top, s, sv, dlo, dhi, lo, base + x),
                    lo <= base,
                    cust_pos(sv, cbase, lo, base + x),
                    forall|a: int| lo <= a < base + x ==> 0 <= #[trigger] ctot(sv, dlo, dhi, a) < CAP,
                decreases w - x,
            {
                let a = base + x;
                proof {
                    lemma_acc_end(c, sv, outv, b as int, acc0, x as int);
                    assert(acc@[x as int] == acc0[x as int]);
                }
                if c.ck[a] as i128 != c.cbase as i128 + a as i128 {
                    return COut { ok: false, top, acc };
                }
                let e = acc[x];
                proof {
                    assert(a / CPB == b) by (nonlinear_arith) requires a == b * 131072 + x, x < 131072;
                    lemma_bucket_total(c, sv, outv, os, nb as int, b as int, a as int);
                    assert(enc_ok(e, ctot(sv, dlo, dhi, a as int), ctcnt(sv, dlo, dhi, a as int) as int));
                    lemma_enc_dec(e, ctot(sv, dlo, dhi, a as int), ctcnt(sv, dlo, dhi, a as int) as int);
                }
                acc[x] = 0;
                let gs = offer_one(&c, a, e, &mut top, Ghost(s), Ghost(sv), Ghost(lo));
                proof { s = gs@; }
                x = x + 1;
            }
            proof {
                // the accumulators beyond the table's rows were never written
                assert forall|y: int| 0 <= y < CPB implies #[trigger] acc@[y] == 0 by {
                    if y >= w {
                        lemma_osum_beyond(c, sv, outv, os, nb as int, b as int, b * (CPB as int) + y, nt as int);
                        lemma_acc_end(c, sv, outv, b as int, acc0, y);
                        assert(acc@[y] == acc0[y]);
                    }
                }
            }
            b = b + 1;
        }
        proof {
            lemma_part_top(top, s, sv, dlo, dhi, lo, bstart(b1 as int, nc as int));
        }
        COut { ok: true, top, acc }
    }
}

} // verus!
