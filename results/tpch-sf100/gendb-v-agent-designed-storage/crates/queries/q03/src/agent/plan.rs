//! Planning of the clustered (fast) path on the calling thread. Orders are stored by order date at block
//! granularity, so the orders from `orders_cut` on are dated on or after `$2` (no group). The lineitem rows of the
//! orders before the cut are a prefix `[0, LP)` (`lb_search`, binary search with the orders key index); the first
//! lineitem block whose shipdate zone maximum is after `$2` starts the window (`window_start`; earlier rows ship on
//! or before `$2`, so earlier orders have no group). Chunk boundaries are order positions with their first lineitem
//! row (`boundary`: the order of a lineitem row and the start of its run).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::stores::facts::interface::common::keyidx as fk;
use super::common::isum::*;
use super::model::*;
use super::qspec::*;
use super::kernel::*;

verus! {

/// Every order from position `pe` on is dated on or after `$2`.
pub open spec fn cut_ok(m: M, p: QP, pe: int) -> bool {
    &&& 0 <= pe <= m.o_n
    &&& forall|q: int| pe <= q < m.o_n ==> #[trigger] odate(m, q) >= p.day
}

/// The orders cut: the start of the last run of order blocks whose base date is on or after `$2`.
pub fn orders_cut(c: &Cols, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (pe: usize)
    requires cols_ok(*c, m, p), model_ok(m),
    ensures cut_ok(m, p, pe as int),
{
    let mut g = c.o_nb;
    while g > 0 && c.o_date_b[g - 1] >= c.day
        invariant
            cols_ok(*c, m, p), model_ok(m),
            g <= m.o_nb,
            forall|h: int| g <= h < m.o_nb ==> #[trigger] m.o_date_b[h] >= p.day,
        decreases g,
    {
        g = g - 1;
    }
    proof {
        assert(g * m.o_bs <= m.o_nb * m.o_bs) by (nonlinear_arith) requires g <= m.o_nb, m.o_bs >= 1;
    }
    proof {
        assert(m.o_nb * m.o_bs < m.o_n + m.o_bs) by (nonlinear_arith)
            requires m.o_nb > 0 ==> (m.o_nb - 1) * m.o_bs < m.o_n, m.o_bs >= 1, m.o_n >= 0, m.o_nb >= 0;
    }
    let start = (g as u64) * c.o_bs;
    let pe = if start < c.o_n as u64 { start as usize } else { c.o_n };
    proof {
        assert forall|q: int| pe <= q < m.o_n implies #[trigger] odate(m, q) >= p.day by {
            lemma_block_bound(q, m.o_bs, m.o_n, m.o_nb);
            let h = q / m.o_bs;
            assert(h >= g) by {
                if h < g {
                    assert(q < (h + 1) * m.o_bs) by {
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q, m.o_bs);
                        vstd::arithmetic::div_mod::lemma_mod_pos_bound(q, m.o_bs);
                        assert(m.o_bs * h == h * m.o_bs) by (nonlinear_arith);
                        assert((h + 1) * m.o_bs == h * m.o_bs + m.o_bs) by (nonlinear_arith);
                    }
                    assert((h + 1) * m.o_bs <= g * m.o_bs) by (nonlinear_arith) requires h + 1 <= g, m.o_bs >= 1;
                }
            }
        }
    }
    pe
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

/// Lineitem rows before `l` ship on or before `$2`.
pub open spec fn shipped_by(m: M, p: QP, l: int) -> bool {
    forall|j: int| 0 <= j < l && j < m.l_n ==> #[trigger] lship(m, j) <= p.day
}

/// The window start: the first lineitem block (before the lineitem cut `lp`) whose shipdate zone maximum is after
/// `$2`; all earlier rows ship on or before `$2`. Returns its first row, or `lp` when there is none.
pub fn window_start(c: &Cols, lp: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (t0: usize)
    requires cols_ok(*c, m, p), model_ok(m), lp <= m.l_n,
    ensures t0 <= lp, shipped_by(m, p, t0 as int),
{
    let mut g: usize = 0;
    let mut start: u64 = 0;
    while g < c.l_nb && start < lp as u64 && c.l_ship_z[g] <= c.day
        invariant
            cols_ok(*c, m, p), model_ok(m), lp <= m.l_n,
            g <= m.l_nb,
            start == g * m.l_bs,
            forall|h: int| 0 <= h < g ==> #[trigger] m.l_ship_z[h] <= p.day,
        decreases m.l_nb - g,
    {
        proof {
            assert((g + 1) * m.l_bs == g * m.l_bs + m.l_bs) by (nonlinear_arith);
            assert((g + 1) * m.l_bs <= m.l_nb * m.l_bs) by (nonlinear_arith) requires g + 1 <= m.l_nb, m.l_bs >= 1;
            assert(m.l_nb * m.l_bs < m.l_n + m.l_bs) by (nonlinear_arith)
                requires m.l_nb > 0, (m.l_nb - 1) * m.l_bs < m.l_n, m.l_bs >= 1;
        }
        g = g + 1;
        start = start + c.l_bs;
    }
    let t0 = if start < lp as u64 { start as usize } else { lp };
    proof {
        assert forall|j: int| 0 <= j < t0 && j < m.l_n implies #[trigger] lship(m, j) <= p.day by {
            assert(in_i64(lkey(m, j)));
            lemma_block_bound(j, m.l_bs, m.l_n, m.l_nb);
            let h = j / m.l_bs;
            assert(h < g) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, m.l_bs);
                vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, m.l_bs);
                assert(m.l_bs * h == h * m.l_bs) by (nonlinear_arith);
                if h >= g {
                    assert(h * m.l_bs >= g * m.l_bs) by (nonlinear_arith) requires h >= g, m.l_bs >= 1;
                }
            }
        }
    }
    t0
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

} // verus!
