//! Planning of the clustered (fast) path on the calling thread. The lineitem rows of the orders are a prefix
//! `[0, LP)` of the stored lineitem rows (`lb_search` of `o_n`: binary search with the orders key index; later rows
//! name no order). Chunk boundaries are order positions with their first lineitem row (`boundary`: the order of a
//! lineitem row and the start of its run), so every order's lineitem run lies inside one chunk.
use vstd::prelude::*;
use crate::stores::liruns::interface::common::keyidx as fk;
use super::common::isum::*;
use super::model::*;
use super::qspec::*;
use super::kernel::*;

verus! {

/// The stored orders position whose key is `k`, if any.
pub fn find_order(c: &Cols, k: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: Option<usize>)
    requires cols_ok(*c, m, p), model_ok(m), c.idx_ok,
    ensures
        r matches Some(q) ==> q < m.o_n && okey(m, q as int) == k as int && opos(m, k as int) == q as int,
        r is None ==> opos(m, k as int) == m.o_n,
    no_unwind
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

/// The stored orders position whose key is `k`, if any: one probe at position `guess` first (on the co-clustered
/// layout the run index of a lineitem run is usually its order's position), else `find_order`.
pub fn find_order_guess(c: &Cols, k: i64, guess: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: Option<usize>)
    requires cols_ok(*c, m, p), model_ok(m), c.idx_ok,
    ensures
        r matches Some(q) ==> q < m.o_n && okey(m, q as int) == k as int && opos(m, k as int) == q as int,
        r is None ==> opos(m, k as int) == m.o_n,
    no_unwind
{
    let r = fk::key_find_guess(c.o_key_c, c.o_key_b, c.o_ic, c.o_ib, c.o_bsz, c.o_kind, c.o_n, k as i128, guess);
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

} // verus!
