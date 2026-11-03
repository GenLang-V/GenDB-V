//! Key lookups of the kernel, each proved against the model's key positions (`model::*pos`, unique under the
//! declared primary keys): the part row of a key (by position when part keys are dense, else by key index), the
//! supplier row of a key (likewise), the nation row of a supplier (a table of nation keys in `[0, 256)`, else a scan),
//! the partsupp row of a `(part key, supplier key)` pair (the key range of the part key in the sorted partsupp rows,
//! its start guessed at four rows per part and checked; a scan when partsupp is not sorted) and the orders position
//! of a key (probing the positions after a cursor, then the orders key index).
use vstd::prelude::*;
use crate::stores::facts::interface::common::keyidx as fk;
use crate::stores::suppliers::interface::common::keyidx as sk;
use crate::stores::custpart::interface::common::keyidx as ck;
use crate::stores::custpart::interface::common::read::lemma_div_lt;
use super::model::*;
use super::cols::*;
use super::common::grp::*;

verus! {

/// No nation row.
pub const NO_NATION: u64 = 0xffff_ffff_ffff_ffffu64;

/// The block divisors of the tables.
#[derive(Clone, Copy)]
pub struct Divs {
    pub l: Div,
    pub o: Div,
    pub p: Div,
    pub t: Div,
    pub s: Div,
    pub n: Div,
}

pub open spec fn divs_ok(d: Divs, m: M) -> bool {
    &&& div_ok(d.l, m.l_bs)
    &&& div_ok(d.o, m.o_bs)
    &&& div_ok(d.p, m.p_bs)
    &&& div_ok(d.t, m.t_bs)
    &&& div_ok(d.s, m.s_bs)
    &&& div_ok(d.n, m.n_bs)
}

/// The facts every lookup needs.
pub open spec fn look_ok(c: Cols, d: Divs, m: M) -> bool {
    &&& cols_ok(c, m)
    &&& model_ok(m)
    &&& divs_ok(d, m)
}

/// Part keys are dense: part row `c` has key `c + 1`.
pub open spec fn p_dense_ok(m: M) -> bool {
    forall|c: int| 0 <= c < m.p_n ==> #[trigger] pkey(m, c) == c + 1
}

/// Supplier keys are dense.
pub open spec fn s_dense_ok(m: M) -> bool {
    forall|s: int| 0 <= s < m.s_n ==> #[trigger] skey(m, s) == s + 1
}

/// The nation table: entry `k` is the nation row of key `k`, or `NO_NATION`; with `small`, every nation key is in
/// `[0, 256)`.
pub open spec fn ntab_ok(ntab: Seq<u64>, small: bool, m: M) -> bool {
    &&& ntab.len() == 256
    &&& m.n_n < NO_NATION
    &&& forall|k: int| 0 <= k < 256 ==> (#[trigger] ntab[k] == NO_NATION && npos(m, k) == m.n_n
            || ntab[k] < m.n_n && ntab[k] as int == npos(m, k))
    &&& small ==> forall|n: int| 0 <= n < m.n_n ==> 0 <= #[trigger] nkey(m, n) < 256
}

// ------------------------------------------------------------------------------------------------ key positions

/// A part row holding key `k` is `ppos(k)`; without one `ppos(k)` is `p_n`.
pub proof fn lemma_ppos(m: M, k: int, x: int)
    requires model_ok(m),
    ensures
        0 <= x < m.p_n && pkey(m, x) == k ==> ppos(m, k) == x,
        (forall|c: int| 0 <= c < m.p_n ==> #[trigger] pkey(m, c) != k) ==> ppos(m, k) == m.p_n,
        0 <= ppos(m, k) <= m.p_n,
        ppos(m, k) < m.p_n ==> pkey(m, ppos(m, k)) == k,
{
    if exists|c: int| 0 <= c < m.p_n && #[trigger] pkey(m, c) == k {
        let c0 = choose|c: int| 0 <= c < m.p_n && #[trigger] pkey(m, c) == k;
        if 0 <= x < m.p_n && pkey(m, x) == k && x != c0 {
            assert(pkey(m, x) != pkey(m, c0));
        }
    }
}

pub proof fn lemma_spos(m: M, k: int, x: int)
    requires model_ok(m),
    ensures
        0 <= x < m.s_n && skey(m, x) == k ==> spos(m, k) == x,
        (forall|s: int| 0 <= s < m.s_n ==> #[trigger] skey(m, s) != k) ==> spos(m, k) == m.s_n,
        0 <= spos(m, k) <= m.s_n,
        spos(m, k) < m.s_n ==> skey(m, spos(m, k)) == k,
{
    if exists|s: int| 0 <= s < m.s_n && #[trigger] skey(m, s) == k {
        let s0 = choose|s: int| 0 <= s < m.s_n && #[trigger] skey(m, s) == k;
        if 0 <= x < m.s_n && skey(m, x) == k && x != s0 {
            assert(skey(m, x) != skey(m, s0));
        }
    }
}

pub proof fn lemma_npos(m: M, k: int, x: int)
    requires model_ok(m),
    ensures
        0 <= x < m.n_n && nkey(m, x) == k ==> npos(m, k) == x,
        (forall|n: int| 0 <= n < m.n_n ==> #[trigger] nkey(m, n) != k) ==> npos(m, k) == m.n_n,
        0 <= npos(m, k) <= m.n_n,
        npos(m, k) < m.n_n ==> nkey(m, npos(m, k)) == k,
{
    if exists|n: int| 0 <= n < m.n_n && #[trigger] nkey(m, n) == k {
        let n0 = choose|n: int| 0 <= n < m.n_n && #[trigger] nkey(m, n) == k;
        if 0 <= x < m.n_n && nkey(m, x) == k && x != n0 {
            assert(nkey(m, x) != nkey(m, n0));
        }
    }
}

pub proof fn lemma_opos(m: M, k: int, x: int)
    requires model_ok(m),
    ensures
        0 <= x < m.o_n && okey(m, x) == k ==> opos(m, k) == x,
        (forall|q: int| 0 <= q < m.o_n ==> #[trigger] okey(m, q) != k) ==> opos(m, k) == m.o_n,
        0 <= opos(m, k) <= m.o_n,
        opos(m, k) < m.o_n ==> okey(m, opos(m, k)) == k,
{
    if exists|q: int| 0 <= q < m.o_n && #[trigger] okey(m, q) == k {
        let q0 = choose|q: int| 0 <= q < m.o_n && #[trigger] okey(m, q) == k;
        if 0 <= x < m.o_n && okey(m, x) == k && x != q0 {
            assert(okey(m, x) != okey(m, q0));
        }
    }
}

pub proof fn lemma_tpos(m: M, pk: int, skv: int, x: int)
    requires model_ok(m),
    ensures
        0 <= x < m.t_n && tpk(m, x) == pk && tsk(m, x) == skv ==> tpos(m, pk, skv) == x,
        (forall|t: int| 0 <= t < m.t_n ==> !(#[trigger] tpk(m, t) == pk && tsk(m, t) == skv)) ==> tpos(m, pk, skv) == m.t_n,
        0 <= tpos(m, pk, skv) <= m.t_n,
        tpos(m, pk, skv) < m.t_n ==> tpk(m, tpos(m, pk, skv)) == pk && tsk(m, tpos(m, pk, skv)) == skv,
{
    if exists|t: int| 0 <= t < m.t_n && #[trigger] tpk(m, t) == pk && tsk(m, t) == skv {
        let t0 = choose|t: int| 0 <= t < m.t_n && #[trigger] tpk(m, t) == pk && tsk(m, t) == skv;
        if 0 <= x < m.t_n && tpk(m, x) == pk && tsk(m, x) == skv && x != t0 {
            assert(tpk(m, x) != tpk(m, t0) || tsk(m, x) != tsk(m, t0));
        }
    }
}

// ------------------------------------------------------------------------------------------------ decoding

/// Block of row `j` of a table with `n` rows in `nb` groups of `bs`.
pub proof fn lemma_block(j: int, bs: int, n: int, nb: int)
    requires 0 <= j < n, frame_ok(n, bs, nb),
    ensures 0 <= j / bs < nb,
{
    lemma_div_lt(j, bs, nb);
}

/// The decoded values of lineitem row `j` are in range.
pub proof fn lemma_lvals(m: M, j: int)
    requires model_ok(m), 0 <= j < m.l_n,
    ensures
        in_i64(lok(m, j)) && in_i64(lpk(m, j)) && in_i64(lsk(m, j)),
        num15(lqty(m, j)) && num15(lprice(m, j)) && num15(ldisc(m, j)),
{
    assert(in_i64(lok(m, j)));
}

pub proof fn lemma_ovals(m: M, q: int)
    requires model_ok(m), 0 <= q < m.o_n,
    ensures in_i64(okey(m, q)) && crate::spec::datetime::date_valid(odate(m, q)) && in_i64(odate(m, q)),
{
    assert(in_i64(okey(m, q)));
}

pub proof fn lemma_tvals(m: M, t: int)
    requires model_ok(m), 0 <= t < m.t_n,
    ensures in_i64(tpk(m, t)) && in_i64(tsk(m, t)) && num15(tcost(m, t)),
{
    assert(in_i64(tpk(m, t)));
}

pub proof fn lemma_pvals(m: M, r: int)
    requires model_ok(m), 0 <= r < m.p_n,
    ensures in_i64(pkey(m, r)),
{
    assert(in_i64(pkey(m, r)));
}

pub proof fn lemma_svals(m: M, s: int)
    requires model_ok(m), 0 <= s < m.s_n,
    ensures in_i64(skey(m, s)) && in_i64(snk(m, s)),
{
    assert(in_i64(skey(m, s)));
}

pub proof fn lemma_nvals(m: M, n: int)
    requires model_ok(m), 0 <= n < m.n_n,
    ensures in_i64(nkey(m, n)),
{
    assert(in_i64(nkey(m, n)));
}

/// `l_partkey` of lineitem row `j`.
pub fn get_lpk(c: &Cols, d: &Divs, j: usize, Ghost(m): Ghost<M>) -> (v: i64)
    requires look_ok(*c, *d, m), j < m.l_n,
    ensures v as int == lpk(m, j as int),
    no_unwind
{
    proof { lemma_block(j as int, m.l_bs, m.l_n, m.l_nb); lemma_lvals(m, j as int); }
    let g = grp(j, d.l);
    c.l_pk_b[g] + c.l_pk_c[j] as i64
}

/// `l_suppkey` of lineitem row `j`.
pub fn get_lsk(c: &Cols, d: &Divs, j: usize, Ghost(m): Ghost<M>) -> (v: i64)
    requires look_ok(*c, *d, m), j < m.l_n,
    ensures v as int == lsk(m, j as int),
    no_unwind
{
    proof { lemma_block(j as int, m.l_bs, m.l_n, m.l_nb); lemma_lvals(m, j as int); }
    let g = grp(j, d.l);
    c.l_sk_b[g] + c.l_sk_c[j] as i64
}

/// `l_orderkey` of lineitem row `j`.
pub fn get_lok(c: &Cols, d: &Divs, j: usize, Ghost(m): Ghost<M>) -> (v: i64)
    requires look_ok(*c, *d, m), j < m.l_n,
    ensures v as int == lok(m, j as int),
    no_unwind
{
    proof { lemma_block(j as int, m.l_bs, m.l_n, m.l_nb); lemma_lvals(m, j as int); }
    let g = grp(j, d.l);
    c.l_ok_b[g] + c.l_ok_c[j] as i64
}

/// `l_quantity`, `l_extendedprice`, `l_discount` of lineitem row `j`.
pub fn get_lnums(c: &Cols, d: &Divs, j: usize, Ghost(m): Ghost<M>) -> (v: (i64, i64, i64))
    requires look_ok(*c, *d, m), j < m.l_n,
    ensures
        v.0 as int == lqty(m, j as int),
        v.1 as int == lprice(m, j as int),
        v.2 as int == ldisc(m, j as int),
    no_unwind
{
    proof {
        lemma_block(j as int, m.l_bs, m.l_n, m.l_nb);
        lemma_lvals(m, j as int);
        assert(crate::spec::numeric::pow10(15) == 1000000000000000) by (compute);
    }
    let g = grp(j, d.l);
    (c.l_qty_b[g] + c.l_qty_c[j] as i64, c.l_price_b[g] + c.l_price_c[j] as i64, c.l_disc_b[g] + c.l_disc_c[j] as i64)
}

/// `o_orderkey` of orders position `q`.
pub fn get_okey(c: &Cols, d: &Divs, q: usize, Ghost(m): Ghost<M>) -> (v: i64)
    requires look_ok(*c, *d, m), q < m.o_n,
    ensures v as int == okey(m, q as int),
    no_unwind
{
    proof { lemma_block(q as int, m.o_bs, m.o_n, m.o_nb); lemma_ovals(m, q as int); }
    let g = grp(q, d.o);
    c.o_key_b[g] + c.o_key_c[q] as i64
}

/// `o_orderdate` of orders position `q`.
pub fn get_odate(c: &Cols, d: &Divs, q: usize, Ghost(m): Ghost<M>) -> (v: i64)
    requires look_ok(*c, *d, m), q < m.o_n,
    ensures v as int == odate(m, q as int),
    no_unwind
{
    proof { lemma_block(q as int, m.o_bs, m.o_n, m.o_nb); lemma_ovals(m, q as int); }
    let g = grp(q, d.o);
    c.o_date_b[g] + c.o_date_c[q] as i64
}

/// `ps_partkey`, `ps_suppkey`, `ps_supplycost` of partsupp row `t`.
pub fn get_t(c: &Cols, d: &Divs, t: usize, Ghost(m): Ghost<M>) -> (v: (i64, i64, i64))
    requires look_ok(*c, *d, m), t < m.t_n,
    ensures
        v.0 as int == tpk(m, t as int),
        v.1 as int == tsk(m, t as int),
        v.2 as int == tcost(m, t as int),
    no_unwind
{
    proof {
        lemma_block(t as int, m.t_bs, m.t_n, m.t_nb);
        lemma_tvals(m, t as int);
        assert(crate::spec::numeric::pow10(15) == 1000000000000000) by (compute);
    }
    let g = grp(t, d.t);
    (c.t_pk_b[g] + c.t_pk_c[t] as i64, c.t_sk_b[g] + c.t_sk_c[t] as i64, c.t_cost_b[g] + c.t_cost_c[t] as i64)
}

/// `ps_partkey` of partsupp row `t`.
pub fn get_tpk(c: &Cols, d: &Divs, t: usize, Ghost(m): Ghost<M>) -> (v: i64)
    requires look_ok(*c, *d, m), t < m.t_n,
    ensures v as int == tpk(m, t as int),
    no_unwind
{
    proof { lemma_block(t as int, m.t_bs, m.t_n, m.t_nb); lemma_tvals(m, t as int); }
    let g = grp(t, d.t);
    c.t_pk_b[g] + c.t_pk_c[t] as i64
}

/// `p_partkey` of part row `r`.
pub fn get_pkey(c: &Cols, d: &Divs, r: usize, Ghost(m): Ghost<M>) -> (v: i64)
    requires look_ok(*c, *d, m), r < m.p_n,
    ensures v as int == pkey(m, r as int),
    no_unwind
{
    proof { lemma_block(r as int, m.p_bs, m.p_n, m.p_nb); lemma_pvals(m, r as int); }
    let g = grp(r, d.p);
    c.p_key_b[g] + c.p_key_c[r] as i64
}

/// `s_suppkey` of supplier row `s`.
pub fn get_skey(c: &Cols, d: &Divs, s: usize, Ghost(m): Ghost<M>) -> (v: i64)
    requires look_ok(*c, *d, m), s < m.s_n,
    ensures v as int == skey(m, s as int),
    no_unwind
{
    proof { lemma_block(s as int, m.s_bs, m.s_n, m.s_nb); lemma_svals(m, s as int); }
    let g = grp(s, d.s);
    c.s_key_b[g] + c.s_key_c[s] as i64
}

/// `n_nationkey` of nation row `n`.
pub fn get_nkey(c: &Cols, d: &Divs, n: usize, Ghost(m): Ghost<M>) -> (v: i64)
    requires look_ok(*c, *d, m), n < m.n_n,
    ensures v as int == nkey(m, n as int),
    no_unwind
{
    proof { lemma_block(n as int, m.n_bs, m.n_n, m.n_nb); lemma_nvals(m, n as int); }
    let g = grp(n, d.n);
    c.n_key_b[g] + c.n_key_c[n] as i64
}

// ------------------------------------------------------------------------------------------------ lookups

/// Part, supplier and partsupp rows sorted by key (key index kind 1): keys never decrease.
pub proof fn lemma_p_sorted(m: M, a: int, b: int)
    requires model_ok(m), m.p_kind == 1, 0 <= a <= b < m.p_n,
    ensures pkey(m, a) <= pkey(m, b),
{
    ck::lemma_sorted_le(m.p_key_c, m.p_key_b, Seq::<u32>::empty(), Seq::<u64>::empty(), m.p_bs, m.p_kind, m.p_n, a, b);
}

pub proof fn lemma_s_sorted(m: M, a: int, b: int)
    requires model_ok(m), m.s_kind == 1, 0 <= a <= b < m.s_n,
    ensures skey(m, a) <= skey(m, b),
{
    sk::lemma_sorted_le(m.s_key_c, m.s_key_b, Seq::<u32>::empty(), Seq::<u64>::empty(), m.s_bs, m.s_kind, m.s_n, a, b);
}

pub proof fn lemma_t_sorted(m: M, a: int, b: int)
    requires model_ok(m), m.t_kind == 1, 0 <= a <= b < m.t_n,
    ensures tpk(m, a) <= tpk(m, b),
{
    sk::lemma_sorted_le(m.t_pk_c, m.t_pk_b, Seq::<u32>::empty(), Seq::<u64>::empty(), m.t_bs, m.t_kind, m.t_n, a, b);
}

/// The first part row whose key is at least `k` (sorted part rows).
fn lb_p(c: &Cols, d: &Divs, k: i64, Ghost(m): Ghost<M>) -> (r: usize)
    requires look_ok(*c, *d, m), m.p_kind == 1,
    ensures
        r <= m.p_n,
        forall|x: int| 0 <= x < r ==> #[trigger] pkey(m, x) < k as int,
        forall|x: int| r <= x < m.p_n ==> #[trigger] pkey(m, x) >= k as int,
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = c.p_n;
    while lo < hi
        invariant
            look_ok(*c, *d, m), m.p_kind == 1,
            lo <= hi <= m.p_n,
            forall|x: int| 0 <= x < lo ==> #[trigger] pkey(m, x) < k as int,
            forall|x: int| hi <= x < m.p_n ==> #[trigger] pkey(m, x) >= k as int,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if get_pkey(c, d, mid, Ghost(m)) < k {
            proof {
                assert forall|x: int| 0 <= x < mid + 1 implies #[trigger] pkey(m, x) < k as int by {
                    lemma_p_sorted(m, x, mid as int);
                }
            }
            lo = mid + 1;
        } else {
            proof {
                assert forall|x: int| mid <= x < m.p_n implies #[trigger] pkey(m, x) >= k as int by {
                    lemma_p_sorted(m, mid as int, x);
                }
            }
            hi = mid;
        }
    }
    lo
}

/// The first supplier row whose key is at least `k` (sorted supplier rows).
fn lb_s(c: &Cols, d: &Divs, k: i64, Ghost(m): Ghost<M>) -> (r: usize)
    requires look_ok(*c, *d, m), m.s_kind == 1,
    ensures
        r <= m.s_n,
        forall|x: int| 0 <= x < r ==> #[trigger] skey(m, x) < k as int,
        forall|x: int| r <= x < m.s_n ==> #[trigger] skey(m, x) >= k as int,
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = c.s_n;
    while lo < hi
        invariant
            look_ok(*c, *d, m), m.s_kind == 1,
            lo <= hi <= m.s_n,
            forall|x: int| 0 <= x < lo ==> #[trigger] skey(m, x) < k as int,
            forall|x: int| hi <= x < m.s_n ==> #[trigger] skey(m, x) >= k as int,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if get_skey(c, d, mid, Ghost(m)) < k {
            proof {
                assert forall|x: int| 0 <= x < mid + 1 implies #[trigger] skey(m, x) < k as int by {
                    lemma_s_sorted(m, x, mid as int);
                }
            }
            lo = mid + 1;
        } else {
            proof {
                assert forall|x: int| mid <= x < m.s_n implies #[trigger] skey(m, x) >= k as int by {
                    lemma_s_sorted(m, mid as int, x);
                }
            }
            hi = mid;
        }
    }
    lo
}

/// The first partsupp row whose part key is at least `k` (sorted partsupp rows).
fn lb_t(c: &Cols, d: &Divs, k: i64, Ghost(m): Ghost<M>) -> (r: usize)
    requires look_ok(*c, *d, m), m.t_kind == 1,
    ensures
        r <= m.t_n,
        forall|x: int| 0 <= x < r ==> #[trigger] tpk(m, x) < k as int,
        forall|x: int| r <= x < m.t_n ==> #[trigger] tpk(m, x) >= k as int,
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = c.t_n;
    while lo < hi
        invariant
            look_ok(*c, *d, m), m.t_kind == 1,
            lo <= hi <= m.t_n,
            forall|x: int| 0 <= x < lo ==> #[trigger] tpk(m, x) < k as int,
            forall|x: int| hi <= x < m.t_n ==> #[trigger] tpk(m, x) >= k as int,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if get_tpk(c, d, mid, Ghost(m)) < k {
            proof {
                assert forall|x: int| 0 <= x < mid + 1 implies #[trigger] tpk(m, x) < k as int by {
                    lemma_t_sorted(m, x, mid as int);
                }
            }
            lo = mid + 1;
        } else {
            proof {
                assert forall|x: int| mid <= x < m.t_n implies #[trigger] tpk(m, x) >= k as int by {
                    lemma_t_sorted(m, mid as int, x);
                }
            }
            hi = mid;
        }
    }
    lo
}

/// The part row of key `pk` (`ppos`), or `None` when no part has it.
pub fn part_row(c: &Cols, d: &Divs, p_dense: bool, pk: i64, Ghost(m): Ghost<M>) -> (r: Option<usize>)
    requires look_ok(*c, *d, m), p_dense ==> p_dense_ok(m),
    ensures
        r matches Some(x) ==> x < m.p_n && x as int == ppos(m, pk as int),
        r is None ==> ppos(m, pk as int) == m.p_n,
    no_unwind
{
    if p_dense {
        if 1 <= pk as i128 && pk as i128 <= c.p_n as i128 {
            let x = (pk - 1) as usize;
            proof {
                assert(pkey(m, x as int) == x + 1);
                lemma_ppos(m, pk as int, x as int);
            }
            Some(x)
        } else {
            proof {
                assert forall|r: int| 0 <= r < m.p_n implies #[trigger] pkey(m, r) != pk as int by {
                    assert(pkey(m, r) == r + 1);
                }
                lemma_ppos(m, pk as int, 0);
            }
            None
        }
    } else if c.p_kind == 1 {
        let x = lb_p(c, d, pk, Ghost(m));
        if x < c.p_n && get_pkey(c, d, x, Ghost(m)) == pk {
            proof { lemma_ppos(m, pk as int, x as int); }
            Some(x)
        } else {
            proof {
                assert forall|r: int| 0 <= r < m.p_n implies #[trigger] pkey(m, r) != pk as int by {
                    if r > x {
                        lemma_p_sorted(m, x as int, r);
                    }
                }
                lemma_ppos(m, pk as int, 0);
            }
            None
        }
    } else {
        let mut x: usize = 0;
        while x < c.p_n
            invariant
                look_ok(*c, *d, m),
                x <= m.p_n,
                forall|r: int| 0 <= r < x ==> #[trigger] pkey(m, r) != pk as int,
            decreases m.p_n - x,
        {
            if get_pkey(c, d, x, Ghost(m)) == pk {
                proof { lemma_ppos(m, pk as int, x as int); }
                return Some(x);
            }
            x = x + 1;
        }
        proof { lemma_ppos(m, pk as int, 0); }
        None
    }
}

/// The supplier row of key `skv` (`spos`), or `None`.
pub fn supp_row(c: &Cols, d: &Divs, s_dense: bool, skv: i64, Ghost(m): Ghost<M>) -> (r: Option<usize>)
    requires look_ok(*c, *d, m), s_dense ==> s_dense_ok(m),
    ensures
        r matches Some(x) ==> x < m.s_n && x as int == spos(m, skv as int),
        r is None ==> spos(m, skv as int) == m.s_n,
    no_unwind
{
    if s_dense {
        if 1 <= skv as i128 && skv as i128 <= c.s_n as i128 {
            let x = (skv - 1) as usize;
            proof {
                assert(skey(m, x as int) == x + 1);
                lemma_spos(m, skv as int, x as int);
            }
            Some(x)
        } else {
            proof {
                assert forall|r: int| 0 <= r < m.s_n implies #[trigger] skey(m, r) != skv as int by {
                    assert(skey(m, r) == r + 1);
                }
                lemma_spos(m, skv as int, 0);
            }
            None
        }
    } else if c.s_kind == 1 {
        let x = lb_s(c, d, skv, Ghost(m));
        if x < c.s_n && get_skey(c, d, x, Ghost(m)) == skv {
            proof { lemma_spos(m, skv as int, x as int); }
            Some(x)
        } else {
            proof {
                assert forall|r: int| 0 <= r < m.s_n implies #[trigger] skey(m, r) != skv as int by {
                    if r > x {
                        lemma_s_sorted(m, x as int, r);
                    }
                }
                lemma_spos(m, skv as int, 0);
            }
            None
        }
    } else {
        let mut x: usize = 0;
        while x < c.s_n
            invariant
                look_ok(*c, *d, m),
                x <= m.s_n,
                forall|r: int| 0 <= r < x ==> #[trigger] skey(m, r) != skv as int,
            decreases m.s_n - x,
        {
            if get_skey(c, d, x, Ghost(m)) == skv {
                proof { lemma_spos(m, skv as int, x as int); }
                return Some(x);
            }
            x = x + 1;
        }
        proof { lemma_spos(m, skv as int, 0); }
        None
    }
}

/// The nation row of supplier row `s` (`npos(snk(s))`), or `NO_NATION`.
pub fn nation_of(c: &Cols, d: &Divs, ntab: &Vec<u64>, small: bool, s: usize, Ghost(m): Ghost<M>) -> (r: u64)
    requires look_ok(*c, *d, m), ntab_ok(ntab@, small, m), s < m.s_n,
    ensures
        r == NO_NATION ==> npos(m, snk(m, s as int)) == m.n_n,
        r != NO_NATION ==> r < m.n_n && r as int == npos(m, snk(m, s as int)),
    no_unwind
{
    proof { lemma_block(s as int, m.s_bs, m.s_n, m.s_nb); lemma_svals(m, s as int); }
    let g = grp(s, d.s);
    let nk = c.s_nk_b[g] + c.s_nk_c[s] as i64;
    if 0 <= nk && nk < 256 {
        ntab[nk as usize]
    } else if small {
        proof {
            assert forall|n: int| 0 <= n < m.n_n implies #[trigger] nkey(m, n) != nk as int by {}
            lemma_npos(m, nk as int, 0);
        }
        NO_NATION
    } else {
        let mut n: usize = 0;
        while n < c.n_n
            invariant
                look_ok(*c, *d, m),
                n <= m.n_n,
                nk as int == snk(m, s as int),
                m.n_n < NO_NATION,
                forall|x: int| 0 <= x < n ==> #[trigger] nkey(m, x) != nk as int,
            decreases m.n_n - n,
        {
            if get_nkey(c, d, n, Ghost(m)) == nk {
                proof { lemma_npos(m, nk as int, n as int); }
                return n as u64;
            }
            n = n + 1;
        }
        proof { lemma_npos(m, nk as int, 0); }
        NO_NATION
    }
}

/// The first partsupp row of key `pk` in sorted partsupp: every earlier row has a smaller key and the row has `pk`.
pub open spec fn tstart_ok(m: M, pk: int, lo: int) -> bool {
    &&& 0 <= lo < m.t_n
    &&& tpk(m, lo) == pk
    &&& forall|t: int| 0 <= t < lo ==> #[trigger] tpk(m, t) < pk
}

/// The first partsupp row of key `pk` (sorted partsupp): the guess `4 * (pk - 1)` (four suppliers per part) when it
/// holds the key and its predecessor does not, else a binary search; `None` when no row has the key.
pub fn ps_start(c: &Cols, d: &Divs, pk: i64, Ghost(m): Ghost<M>) -> (r: Option<usize>)
    requires look_ok(*c, *d, m), m.t_kind == 1,
    ensures
        r matches Some(lo) ==> tstart_ok(m, pk as int, lo as int),
        r is None ==> forall|t: int| 0 <= t < m.t_n ==> #[trigger] tpk(m, t) != pk as int,
    no_unwind
{
    if 1 <= pk && pk <= 0x1000_0000_0000 {
        let g64 = ((pk - 1) as u64) * 4;
        if g64 < c.t_n as u64 {
            let guess = g64 as usize;
            if get_tpk(c, d, guess, Ghost(m)) == pk {
                if guess == 0 {
                    return Some(0);
                }
                if get_tpk(c, d, guess - 1, Ghost(m)) < pk {
                    proof {
                        assert forall|t: int| 0 <= t < guess implies #[trigger] tpk(m, t) < pk as int by {
                            lemma_t_sorted(m, t, guess - 1);
                        }
                    }
                    return Some(guess);
                }
            }
        }
    }
    let x = lb_t(c, d, pk, Ghost(m));
    if x < c.t_n && get_tpk(c, d, x, Ghost(m)) == pk {
        Some(x)
    } else {
        proof {
            assert forall|t: int| 0 <= t < m.t_n implies #[trigger] tpk(m, t) != pk as int by {
                if t > x {
                    lemma_t_sorted(m, x as int, t);
                }
            }
        }
        None
    }
}

/// One more partsupp row of key `pk` without supplier key `skv`.
proof fn lemma_ps_step(m: M, pk: int, skv: int, lo: int, t: int)
    requires
        forall|x: int| lo <= x < t ==> #[trigger] tpk(m, x) == pk && tsk(m, x) != skv,
        tpk(m, t) == pk, tsk(m, t) != skv,
    ensures
        forall|x: int| lo <= x < t + 1 ==> #[trigger] tpk(m, x) == pk && tsk(m, x) != skv,
{
    assert forall|x: int| lo <= x < t + 1 implies #[trigger] tpk(m, x) == pk && tsk(m, x) != skv by {
        if x < t {
            assert(tpk(m, x) == pk && tsk(m, x) != skv);
        } else {
            assert(x == t);
        }
    }
    assert(forall|x: int| lo <= x < t + 1 ==> #[trigger] tpk(m, x) == pk && tsk(m, x) != skv);
}

/// The partsupp row of `(pk, skv)` (`tpos`), or `None`.
pub fn ps_row(c: &Cols, d: &Divs, pk: i64, skv: i64, Ghost(m): Ghost<M>) -> (r: Option<usize>)
    requires look_ok(*c, *d, m),
    ensures
        r matches Some(t) ==> t < m.t_n && t as int == tpos(m, pk as int, skv as int),
        r is None ==> tpos(m, pk as int, skv as int) == m.t_n,
    no_unwind
{
    if c.t_kind != 1 {
        // not sorted: scan every row
        let mut t: usize = 0;
        while t < c.t_n
            invariant
                look_ok(*c, *d, m),
                t <= m.t_n,
                forall|x: int| 0 <= x < t ==> !(#[trigger] tpk(m, x) == pk as int && tsk(m, x) == skv as int),
            decreases m.t_n - t,
        {
            let (a, b, _) = get_t(c, d, t, Ghost(m));
            if a == pk && b == skv {
                proof { lemma_tpos(m, pk as int, skv as int, t as int); }
                return Some(t);
            }
            t = t + 1;
        }
        proof { lemma_tpos(m, pk as int, skv as int, 0); }
        return None;
    }
    match ps_start(c, d, pk, Ghost(m)) {
        None => {
            proof { lemma_tpos(m, pk as int, skv as int, 0); }
            None
        },
        Some(lo) => {
            let mut t = lo;
            while t < c.t_n
                invariant
                    look_ok(*c, *d, m), m.t_kind == 1,
                    tstart_ok(m, pk as int, lo as int),
                    lo <= t <= m.t_n,
                    forall|x: int| lo <= x < t ==> #[trigger] tpk(m, x) == pk as int && tsk(m, x) != skv as int,
                decreases m.t_n - t,
            {
                let (a, b, _) = get_t(c, d, t, Ghost(m));
                if a != pk {
                    proof {
                        assert forall|x: int| 0 <= x < m.t_n implies !(#[trigger] tpk(m, x) == pk as int && tsk(m, x) == skv as int) by {
                            if x >= t {
                                lemma_t_sorted(m, lo as int, t as int);
                                lemma_t_sorted(m, t as int, x);
                            }
                        }
                        lemma_tpos(m, pk as int, skv as int, 0);
                    }
                    return None;
                }
                if b == skv {
                    proof { lemma_tpos(m, pk as int, skv as int, t as int); }
                    return Some(t);
                }
                proof {
                    assert(tpk(m, t as int) == pk as int && tsk(m, t as int) != skv as int);
                    lemma_ps_step(m, pk as int, skv as int, lo as int, t as int);
                }
                t = t + 1;
            }
            proof {
                assert forall|x: int| 0 <= x < m.t_n implies !(#[trigger] tpk(m, x) == pk as int && tsk(m, x) == skv as int) by {}
                lemma_tpos(m, pk as int, skv as int, 0);
            }
            None
        },
    }
}

/// The orders position of key `k` (`opos`): positions `cq ..` first (at most 64 probes), then the key index when its
/// block size fits `usize`, else a scan.
pub fn order_row(c: &Cols, d: &Divs, cq: usize, k: i64, Ghost(m): Ghost<M>) -> (r: Option<usize>)
    requires look_ok(*c, *d, m),
    ensures
        r matches Some(q) ==> q < m.o_n && q as int == opos(m, k as int),
        r is None ==> opos(m, k as int) == m.o_n,
    no_unwind
{
    let mut q = cq;
    let mut step: usize = 0;
    while step < 64 && q < c.o_n
        invariant look_ok(*c, *d, m),
        decreases 64 - step,
    {
        if get_okey(c, d, q, Ghost(m)) == k {
            proof { lemma_opos(m, k as int, q as int); }
            return Some(q);
        }
        q = q + 1;
        step = step + 1;
    }
    if c.o_bsz_ok {
        let r = fk::key_find(c.o_key_c, c.o_key_b, c.o_ic, c.o_ib, c.o_bsz, c.o_kind, c.o_n, k as i128);
        proof {
            match r {
                Some(x) => {
                    assert(fk::fkey(m.o_key_c, m.o_key_b, m.o_bs, x as int) == okey(m, x as int));
                    lemma_opos(m, k as int, x as int);
                },
                None => {
                    assert forall|x: int| 0 <= x < m.o_n implies #[trigger] okey(m, x) != k as int by {
                        assert(fk::fkey(m.o_key_c, m.o_key_b, m.o_bs, x) == okey(m, x));
                    }
                    lemma_opos(m, k as int, 0);
                },
            }
        }
        r
    } else {
        let mut x: usize = 0;
        while x < c.o_n
            invariant
                look_ok(*c, *d, m),
                x <= m.o_n,
                forall|r: int| 0 <= r < x ==> #[trigger] okey(m, r) != k as int,
            decreases m.o_n - x,
        {
            if get_okey(c, d, x, Ghost(m)) == k {
                proof { lemma_opos(m, k as int, x as int); }
                return Some(x);
            }
            x = x + 1;
        }
        proof { lemma_opos(m, k as int, 0); }
        None
    }
}

} // verus!
