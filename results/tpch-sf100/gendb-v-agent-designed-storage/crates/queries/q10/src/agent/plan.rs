//! Planning of the clustered (fast) path on the calling thread. Orders blocks carry a minimum (the base) and a
//! zone maximum of o_orderdate, so the orders before the first block whose maximum reaches `lo`, and from the
//! first of the trailing blocks whose minimum is beyond `hi`, are outside the window (`orders_window`). The
//! lineitem rows of the orders before a position `o` are a prefix `[0, l)` (`lb_search`, binary search with the
//! orders key index). Chunk boundaries are order positions with their first lineitem row (`boundary`: the order
//! of a lineitem row and the start of its run; `plan_bounds`: about equal lineitem rows per chunk).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::parallel::MAX_WORKERS;
use crate::stores::facts::interface::common::keyidx as fk;
use super::model::*;
use super::qspec::*;
use super::kernel::*;

verus! {

/// No order outside `[qs, qe)` is dated in the window.
pub open spec fn window_ok(m: M, p: QP, qs: int, qe: int) -> bool {
    &&& 0 <= qs <= qe <= m.o_n
    &&& forall|q: int| 0 <= q < m.o_n && (q < qs || q >= qe) ==> !#[trigger] odok(m, p, q)
}

/// Rows below `g * bs` lie in groups below `g`; rows from `g * bs` in groups from `g` on.
proof fn lemma_group_side(j: int, bs: int, g: int)
    requires j >= 0, bs >= 1, g >= 0,
    ensures
        j < g * bs ==> j / bs < g,
        j >= g * bs ==> j / bs >= g,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, bs);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, bs);
    let h = j / bs;
    assert(bs * h == h * bs) by (nonlinear_arith);
    if j < g * bs && h >= g {
        assert(h * bs >= g * bs) by (nonlinear_arith) requires h >= g, bs >= 1;
    }
    if j >= g * bs && h < g {
        assert(h * bs + bs <= g * bs) by (nonlinear_arith) requires h + 1 <= g, bs >= 1;
    }
}

/// The orders window `[qs, qe)` from the date zone maps.
pub fn orders_window(c: &Cols, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: (usize, usize))
    requires cols_ok(*c, m, p), model_ok(m),
    ensures window_ok(m, p, r.0 as int, r.1 as int),
{
    // leading blocks whose maximum is before lo
    let mut gs: usize = 0;
    while gs < c.o_nb && c.o_date_z[gs] < c.lo
        invariant
            cols_ok(*c, m, p), model_ok(m),
            gs <= m.o_nb,
            forall|h: int| 0 <= h < gs ==> #[trigger] m.o_date_z[h] < p.lo,
        decreases m.o_nb - gs,
    {
        gs = gs + 1;
    }
    // trailing blocks whose minimum is after hi
    let mut ge: usize = c.o_nb;
    while ge > gs && c.o_date_b[ge - 1] > c.hi
        invariant
            cols_ok(*c, m, p), model_ok(m),
            gs <= ge <= m.o_nb,
            forall|h: int| ge <= h < m.o_nb ==> #[trigger] m.o_date_b[h] > p.hi,
        decreases ge,
    {
        ge = ge - 1;
    }
    proof {
        assert(gs * m.o_bs <= ge * m.o_bs) by (nonlinear_arith) requires gs <= ge, m.o_bs >= 1;
        assert(ge * m.o_bs <= m.o_nb * m.o_bs) by (nonlinear_arith) requires ge <= m.o_nb, m.o_bs >= 1;
        assert(m.o_nb * m.o_bs < m.o_n + m.o_bs) by (nonlinear_arith)
            requires m.o_nb > 0 ==> (m.o_nb - 1) * m.o_bs < m.o_n, m.o_bs >= 1, m.o_n >= 0, m.o_nb >= 0;
    }
    let s64 = (gs as u64) * c.o_bs;
    let e64 = (ge as u64) * c.o_bs;
    let qs: usize = if s64 < c.o_n as u64 { s64 as usize } else { c.o_n };
    let qe: usize = if e64 < c.o_n as u64 { e64 as usize } else { c.o_n };
    proof {
        assert forall|q: int| 0 <= q < m.o_n && (q < qs || q >= qe) implies !#[trigger] odok(m, p, q) by {
            lemma_block_bound(q, m.o_bs, m.o_n, m.o_nb);
            assert(in_i64(okey(m, q)));
            if q < qs {
                lemma_group_side(q, m.o_bs, gs as int);
                assert(odate(m, q) <= m.o_date_z[q / m.o_bs]);
            } else {
                lemma_group_side(q, m.o_bs, ge as int);
                assert(odate(m, q) >= m.o_date_b[q / m.o_bs]);
            }
        }
    }
    (qs, qe)
}

/// The stored orders position whose key is `k`, if any.
pub fn find_order(c: &Cols, k: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: Option<usize>)
    requires cols_ok(*c, m, p), model_ok(m), c.idx_ok,
    ensures
        r matches Some(q) ==> q < m.o_n && okey(m, q as int) == k as int && opos(m, k as int) == q as int,
        r is None ==> opos(m, k as int) == m.o_n,
{
    let r = fk::key_find(c.o_key_c, c.o_key_b, c.o_ic, c.o_ib, c.o_bsz, c.o_kind, c.o_n, k as i128);
    proof {
        crate::agent::facts::lemma_opos(m, k as int);
        match r {
            Some(q) => {
                assert(fk::fkey(m.o_key_c, m.o_key_b, m.o_bs, q as int) == okey(m, q as int));
            },
            None => {
                if opos(m, k as int) < m.o_n {
                    assert(fk::fkey(m.o_key_c, m.o_key_b, m.o_bs, opos(m, k as int)) == okey(m, opos(m, k as int)));
                }
            },
        }
    }
    r
}

/// `l_orderkey` of lineitem row `j`.
pub fn lkey_at(c: &Cols, j: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (k: i64)
    requires cols_ok(*c, m, p), model_ok(m), j < m.l_n,
    ensures k as int == lkey(m, j as int),
{
    proof {
        lemma_block_bound(j as int, m.l_bs, m.l_n, m.l_nb);
        assert(in_i64(lkey(m, j as int)));
    }
    c.l_key_b[((j as u64) / c.l_bs) as usize] + c.l_key_c[j] as i64
}

/// The order position of lineitem row `j`.
pub fn lpos_at(c: &Cols, j: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: usize)
    requires cols_ok(*c, m, p), model_ok(m), c.idx_ok, j < m.l_n,
    ensures r as int == lpos(m, j as int),
{
    let k = lkey_at(c, j, Ghost(m), Ghost(p));
    match find_order(c, k, Ghost(m), Ghost(p)) {
        Some(q) => q,
        None => c.o_n,
    }
}

/// The first lineitem row whose order position is at least `o` (binary search; the positions never decrease).
pub fn lb_search(c: &Cols, o: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (l: usize)
    requires cols_ok(*c, m, p), model_ok(m), c.idx_ok, m.cluster == 1,
    ensures lb_ok(m, o as int, l as int),
{
    let mut lo: usize = 0;
    let mut hi: usize = c.l_n;
    while lo < hi
        invariant
            cols_ok(*c, m, p), model_ok(m), m.cluster == 1, c.idx_ok,
            lo <= hi <= m.l_n,
            forall|t: int| 0 <= t < lo ==> #[trigger] lpos(m, t) < o,
            forall|t: int| hi <= t < m.l_n ==> #[trigger] lpos(m, t) >= o,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let pm = lpos_at(c, mid, Ghost(m), Ghost(p));
        if pm >= o {
            proof {
                assert forall|t: int| mid <= t < m.l_n implies #[trigger] lpos(m, t) >= o by {
                    lemma_lpos_mono(m, mid as int, t);
                }
            }
            hi = mid;
        } else {
            proof {
                assert forall|t: int| 0 <= t < mid + 1 implies #[trigger] lpos(m, t) < o by {
                    lemma_lpos_mono(m, t, mid as int);
                }
            }
            lo = mid + 1;
        }
    }
    lo
}

/// The first row of the run of lineitem row `t`'s order, when that order exists (position `o < o_n`).
pub fn run_start(c: &Cols, t: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(o): Ghost<int>) -> (l: usize)
    requires cols_ok(*c, m, p), model_ok(m), m.cluster == 1, t < m.l_n, o == lpos(m, t as int), o < m.o_n,
    ensures l <= t, lb_ok(m, o, l as int),
{
    let k = lkey_at(c, t, Ghost(m), Ghost(p));
    let mut l = t;
    let mut stop = false;
    while l > 0 && !stop
        invariant
            cols_ok(*c, m, p), model_ok(m), m.cluster == 1,
            t < m.l_n, o == lpos(m, t as int), o < m.o_n, k as int == lkey(m, t as int),
            l <= t,
            forall|j: int| l <= j <= t ==> #[trigger] lkey(m, j) == k as int,
            stop ==> l > 0 && lkey(m, l - 1) != k as int,
        decreases l + if stop { 0int } else { 1int },
    {
        let kp = lkey_at(c, l - 1, Ghost(m), Ghost(p));
        if kp == k {
            l = l - 1;
        } else {
            stop = true;
        }
    }
    proof {
        crate::agent::facts::lemma_opos(m, k as int);
        assert(okey(m, o) == k as int);
        assert forall|j: int| l <= j < m.l_n implies #[trigger] lpos(m, j) >= o by {
            if j <= t {
                assert(lkey(m, j) == k as int);
            } else {
                lemma_lpos_mono(m, t as int, j);
            }
        }
        if l > 0 {
            lemma_lpos_key(m, o, l as int - 1);
            lemma_lpos_mono(m, l as int - 1, t as int);
            assert(lpos(m, l as int - 1) < o);
        }
        assert forall|j: int| 0 <= j < l implies #[trigger] lpos(m, j) < o by {
            lemma_lpos_mono(m, j, l as int - 1);
        }
    }
    l
}

/// A chunk boundary from lineitem row `t` of the window: its order position and the start of its run, when they
/// continue the previous boundary `(po, pl)` monotonically below the cut `(pe, lp)`; otherwise the previous one.
pub fn boundary(c: &Cols, t: usize, po: usize, pl: usize, pe: usize, lp: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>)
    -> (r: (usize, usize))
    requires
        cols_ok(*c, m, p), model_ok(m), m.cluster == 1, c.idx_ok,
        t < m.l_n,
        lb_ok(m, po as int, pl as int),
        lb_ok(m, pe as int, lp as int),
        po <= pe <= m.o_n,
        pl <= lp,
    ensures
        lb_ok(m, r.0 as int, r.1 as int),
        po <= r.0 <= pe,
        pl <= r.1 <= lp,
{
    let k = lkey_at(c, t, Ghost(m), Ghost(p));
    match find_order(c, k, Ghost(m), Ghost(p)) {
        Some(o) => {
            if o >= po && o <= pe {
                let l = run_start(c, t, Ghost(m), Ghost(p), Ghost(o as int));
                proof {
                    // run starts are ordered like their order positions
                    if (l as int) < pl as int {
                        assert(lpos(m, l as int) >= o as int);
                        assert(lpos(m, l as int) < po as int);
                    }
                    if (l as int) > lp as int {
                        assert(lpos(m, lp as int) < o as int);
                        assert(lpos(m, lp as int) >= pe as int);
                    }
                }
                (o, l)
            } else {
                (po, pl)
            }
        },
        None => (po, pl),
    }
}

/// The chunk boundaries of the window `[o0, pe)` (orders) and `[l0, lp)` (lineitems): `bo[k]`, `bl[k]`.
#[verifier::opaque]
pub open spec fn bounds_ok(m: M, bo: Seq<usize>, bl: Seq<usize>, n: int, o0: int, l0: int, pe: int, lp: int) -> bool {
    &&& bo.len() == n && bl.len() == n
    &&& n >= 1 && bo[0] == o0 && bl[0] == l0
    &&& forall|k: int| 0 <= k < n ==> lb_ok(m, #[trigger] bo[k] as int, bl[k] as int) && bo[k] <= pe && bl[k] <= lp
    &&& forall|k: int| 0 <= k < n - 1 ==> #[trigger] bo[k] <= bo[k + 1] && bl[k] <= bl[k + 1]
}

/// Boundary `k`, and its order with the next one.
pub proof fn lemma_bounds_get(m: M, bo: Seq<usize>, bl: Seq<usize>, n: int, o0: int, l0: int, pe: int, lp: int, k: int)
    requires bounds_ok(m, bo, bl, n, o0, l0, pe, lp), 0 <= k < n,
    ensures
        bo.len() == n && bl.len() == n,
        bo[0] == o0 && bl[0] == l0,
        lb_ok(m, bo[k] as int, bl[k] as int), bo[k] <= pe, bl[k] <= lp,
        k < n - 1 ==> bo[k] <= bo[k + 1] && bl[k] <= bl[k + 1],
{
    reveal(bounds_ok);
}

/// One boundary.
pub proof fn lemma_bounds_one(m: M, o0: int, l0: int, pe: int, lp: int, bo: Seq<usize>, bl: Seq<usize>)
    requires
        bo.len() == 1 && bl.len() == 1 && bo[0] == o0 && bl[0] == l0,
        lb_ok(m, o0, l0), o0 <= pe, l0 <= lp,
    ensures bounds_ok(m, bo, bl, 1, o0, l0, pe, lp),
{
    reveal(bounds_ok);
}

/// One more boundary after the last.
pub proof fn lemma_bounds_push(m: M, bo: Seq<usize>, bl: Seq<usize>, n: int, o0: int, l0: int, pe: int, lp: int, o: usize, l: usize)
    requires
        bounds_ok(m, bo, bl, n, o0, l0, pe, lp),
        lb_ok(m, o as int, l as int), o <= pe, l <= lp,
        bo[n - 1] <= o, bl[n - 1] <= l,
    ensures bounds_ok(m, bo.push(o), bl.push(l), n + 1, o0, l0, pe, lp),
{
    reveal(bounds_ok);
    let (bo2, bl2) = (bo.push(o), bl.push(l));
    assert forall|k: int| 0 <= k < n + 1 implies lb_ok(m, #[trigger] bo2[k] as int, bl2[k] as int) && bo2[k] <= pe && bl2[k] <= lp by {
        if k < n {
            assert(bo2[k] == bo[k] && bl2[k] == bl[k]);
        }
    }
    assert forall|k: int| 0 <= k < n + 1 - 1 implies #[trigger] bo2[k] <= bo2[k + 1] && bl2[k] <= bl2[k + 1] by {
        if k < n - 1 {
            assert(bo2[k] == bo[k] && bl2[k] == bl[k] && bo2[k + 1] == bo[k + 1] && bl2[k + 1] == bl[k + 1]);
        } else {
            assert(bo2[k] == bo[k] && bl2[k] == bl[k]);
        }
    }
}

/// Chunk boundaries: `ntasks` ranges of about equal lineitem rows, cut at order runs.
pub fn plan_bounds(c: &Cols, ntasks: usize, o0: usize, l0: usize, pe: usize, lp: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>)
    -> (r: (Vec<usize>, Vec<usize>))
    requires
        cols_ok(*c, m, p), model_ok(m), m.cluster == 1, c.idx_ok,
        1 <= ntasks <= MAX_WORKERS,
        lb_ok(m, o0 as int, l0 as int), lb_ok(m, pe as int, lp as int),
        o0 <= pe <= m.o_n, l0 <= lp <= m.l_n,
    ensures
        bounds_ok(m, r.0@, r.1@, ntasks + 1, o0 as int, l0 as int, pe as int, lp as int),
        r.0@[ntasks as int] == pe, r.1@[ntasks as int] == lp,
{
    let mut bo: Vec<usize> = Vec::new();
    let mut bl: Vec<usize> = Vec::new();
    bo.push(o0);
    bl.push(l0);
    proof {
        lemma_bounds_one(m, o0 as int, l0 as int, pe as int, lp as int, bo@, bl@);
    }
    let span = lp - l0;
    let step = span / ntasks;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(span as int, ntasks as int);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(span as int, ntasks as int);
        assert(ntasks * step == step * ntasks) by (nonlinear_arith);
    }
    let mut i: usize = 1;
    while i < ntasks
        invariant
            cols_ok(*c, m, p), model_ok(m), m.cluster == 1, c.idx_ok,
            1 <= i <= ntasks <= MAX_WORKERS,
            lb_ok(m, pe as int, lp as int),
            o0 <= pe <= m.o_n, l0 <= lp <= m.l_n,
            span == lp - l0,
            step * ntasks <= span,
            bounds_ok(m, bo@, bl@, i as int, o0 as int, l0 as int, pe as int, lp as int),
        decreases ntasks - i,
    {
        proof {
            assert(step * i <= step * ntasks) by (nonlinear_arith) requires i <= ntasks, step >= 0;
            lemma_bounds_get(m, bo@, bl@, i as int, o0 as int, l0 as int, pe as int, lp as int, i - 1);
        }
        let row = l0 + step * i;
        let prev_o = bo[i - 1];
        let prev_l = bl[i - 1];
        let (o, l) = if row < lp {
            boundary(c, row, prev_o, prev_l, pe, lp, Ghost(m), Ghost(p))
        } else {
            (prev_o, prev_l)
        };
        proof {
            lemma_bounds_push(m, bo@, bl@, i as int, o0 as int, l0 as int, pe as int, lp as int, o, l);
        }
        bo.push(o);
        bl.push(l);
        i = i + 1;
    }
    proof {
        lemma_bounds_get(m, bo@, bl@, ntasks as int, o0 as int, l0 as int, pe as int, lp as int, ntasks - 1);
        lemma_bounds_push(m, bo@, bl@, ntasks as int, o0 as int, l0 as int, pe as int, lp as int, pe, lp);
    }
    bo.push(pe);
    bl.push(lp);
    (bo, bl)
}

/// Consecutive boundaries are ordered below the cut.
pub proof fn lemma_bounds_at(m: M, bo: Seq<usize>, bl: Seq<usize>, n: int, o0: int, l0: int, pe: int, lp: int, t: int)
    requires bounds_ok(m, bo, bl, n, o0, l0, pe, lp), 0 <= t < n - 1,
    ensures o0 <= bo[t] <= bo[t + 1] <= pe,
    decreases t,
{
    lemma_bounds_get(m, bo, bl, n, o0, l0, pe, lp, t);
    lemma_bounds_get(m, bo, bl, n, o0, l0, pe, lp, t + 1);
    if t > 0 {
        lemma_bounds_at(m, bo, bl, n, o0, l0, pe, lp, t - 1);
    }
}

} // verus!
