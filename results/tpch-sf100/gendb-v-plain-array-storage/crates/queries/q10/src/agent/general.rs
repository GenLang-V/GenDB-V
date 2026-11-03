//! The general path, for data the fast path's checks refuse (keys out of order, negative values, sums beyond the
//! fast accumulators, non-positional customer keys): a serial computation that assumes nothing about row order or
//! key layout, straight from the definitions of `agent::normal`.
//!
//! For every customer whose nation exists, its revenue is the sum, over the orders it collects (`cmatch`), of the
//! values of the lineitem rows that hit the order's key, with the absolute mass tracked in `i128`: a mass beyond
//! `i128::MAX` is the statement's capacity limit (`Over`). Every group is offered to a top-`TOPN` buffer in row order.
//! The cost is the product of the table sizes; the fast path covers the benchmark data.
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::spec::numeric::abs;
use crate::link::expr::i128_max;
use crate::agent::cols::*;
use crate::agent::normal::*;
use crate::agent::xcols::*;
use crate::agent::scan::is_r_exec;
use crate::agent::cagg::{nation_of, TOPN, cval};
use crate::agent::answer::*;
use crate::agent::common::topn::*;

verus! {

/// The general path's result.
pub enum GenOut {
    /// A top-`TOPN` buffer of all groups.
    Top(Top),
    /// A customer whose nation exists and whose absolute SUM mass exceeds `i128::MAX`.
    Over(usize),
}

/// The `i128` value of lineitem row `i` (`|price|, |discount| < 10^15`).
fn line_value(c: &Cols, i: usize, Ghost(sv): Ghost<StoresView>) -> (v: i128)
    requires cols_ok(*c, sv), i < c.nl,
    ensures v as int == lval(sv, i as int), -2_000_000_000_000_000_000_000_000_000_000 <= v <= 2_000_000_000_000_000_000_000_000_000_000,
{
    let p = c.lp[i];
    let d = c.ld[i];
    proof {
        assert(num15(lp(sv)[i as int]) && num15(ld(sv)[i as int]));
        assert(-1_000_000_000_000_000 < p < 1_000_000_000_000_000);
        assert(-1_000_000_000_000_000 < d < 1_000_000_000_000_000);
        let q = 100 - d;
        assert(-1_000_000_000_000_000 + 100 < q < 1_000_000_000_000_000 + 100);
        assert(-2_000_000_000_000_000_000_000_000_000_000 <= p * q <= 2_000_000_000_000_000_000_000_000_000_000) by (nonlinear_arith)
            requires -1_000_000_000_000_000 < p < 1_000_000_000_000_000, -1_000_000_000_000_000 + 100 < q < 1_000_000_000_000_000 + 100;
    }
    p * (100 - d)
}

/// Monotonicity of the absolute masses.
proof fn lemma_mass_mono(sv: StoresView, dlo: int, dhi: int, a: int, j: int, k: int, i: int)
    requires 0 <= j < n_o(sv), 0 <= i <= n_l(sv), cmatch(sv, dlo, dhi, a, j), k == ok(sv)[j] as int,
    ensures cabs(sv, dlo, dhi, a, 0, j) + kabs(sv, k, 0, i) <= ctabs(sv, dlo, dhi, a),
{
    lemma_k_split(sv, k, 0, i, n_l(sv));
    lemma_k_bounds(sv, k, i, n_l(sv));
    lemma_c_split(sv, dlo, dhi, a, 0, j + 1, n_o(sv));
    lemma_c_bounds(sv, dlo, dhi, a, j + 1, n_o(sv));
}

/// Customer `a`'s revenue and whether a lineitem row reaches it; `None` when its absolute mass exceeds `i128::MAX`.
fn cust_total(c: &Cols, a: usize, Ghost(sv): Ghost<StoresView>) -> (r: Option<(i128, bool)>)
    requires cols_ok(*c, sv), a < c.nc,
    ensures
        r matches Some((s, any)) ==> s as int == ctot(sv, c.dlo as int, c.dhi as int, a as int)
            && any == (ctcnt(sv, c.dlo as int, c.dhi as int, a as int) > 0)
            && ctabs(sv, c.dlo as int, c.dhi as int, a as int) <= i128_max(),
        r is None ==> ctabs(sv, c.dlo as int, c.dhi as int, a as int) > i128_max(),
{
    let ghost (dlo, dhi, ai) = (c.dlo as int, c.dhi as int, a as int);
    let mut s: i128 = 0;
    let mut m: i128 = 0;
    let mut any = false;
    let mut j: usize = 0;
    while j < c.no
        invariant
            cols_ok(*c, sv), a < c.nc, dlo == c.dlo, dhi == c.dhi, ai == a, j <= c.no,
            s as int == csum(sv, dlo, dhi, ai, 0, j as int),
            m as int == cabs(sv, dlo, dhi, ai, 0, j as int),
            any == (ccnt(sv, dlo, dhi, ai, 0, j as int) > 0),
        decreases c.no - j,
    {
        let d = c.od[j] as i64;
        proof { lemma_c_bounds(sv, dlo, dhi, ai, 0, j as int); }
        if c.oc[j] == c.ck[a] && d >= c.dlo && d < c.dhi {
            proof { assert(cmatch(sv, dlo, dhi, ai, j as int)); }
            let k = c.ok[j];
            let ghost (s0, m0, any0) = (s, m, any);
            let mut i: usize = 0;
            while i < c.nl
                invariant
                    cols_ok(*c, sv), a < c.nc, dlo == c.dlo, dhi == c.dhi, ai == a, j < c.no, i <= c.nl,
                    cmatch(sv, dlo, dhi, ai, j as int), k == ok(sv)[j as int],
                    s0 as int == csum(sv, dlo, dhi, ai, 0, j as int),
                    m0 as int == cabs(sv, dlo, dhi, ai, 0, j as int),
                    any0 == (ccnt(sv, dlo, dhi, ai, 0, j as int) > 0),
                    s as int == s0 + ksum(sv, k as int, 0, i as int),
                    m as int == m0 + kabs(sv, k as int, 0, i as int),
                    any == (any0 || kcnt(sv, k as int, 0, i as int) > 0),
                    -(m as int) <= s as int <= m as int,
                decreases c.nl - i,
            {
                proof {
                    lemma_c_bounds(sv, dlo, dhi, ai, 0, j as int);
                    lemma_k_bounds(sv, k as int, 0, i as int);
                }
                if c.lk[i] == k && is_r_exec(c, i, Ghost(sv)) {
                    let v = line_value(c, i, Ghost(sv));
                    let av: i128 = if v < 0 { -v } else { v };
                    if m > i128::MAX - av {
                        proof {
                            assert(lhit(sv, k as int, i as int));
                            lemma_mass_mono(sv, dlo, dhi, ai, j as int, k as int, i + 1);
                        }
                        return None;
                    }
                    m = m + av;
                    s = s + v;
                    any = true;
                }
                proof {
                    assert(lhit(sv, k as int, i as int) == (lk(sv)[i as int] == k && is_r(sv, i as int)));
                }
                i = i + 1;
            }
        } else {
            proof { assert(!cmatch(sv, dlo, dhi, ai, j as int)); }
        }
        j = j + 1;
    }
    proof { lemma_c_bounds(sv, dlo, dhi, ai, 0, c.no as int); }
    Some((s, any))
}

/// The general path: a top-`TOPN` buffer of all groups (every group's mass within `i128`), or a group beyond it.
pub fn general(c: &Cols, top: Top, Ghost(sv): Ghost<StoresView>) -> (r: GenOut)
    requires
        cols_ok(*c, sv),
        top_inv(top, Seq::empty(), cval(sv, c.dlo as int, c.dhi as int)), top.cap == TOPN,
    ensures
        r matches GenOut::Top(t) ==> t.cap == TOPN && t.k <= t.cap && t.rows@.len() == t.cap && t.vals@.len() == t.cap
            && top_of(tsel(t), all_groups(sv, c.dlo as int, c.dhi as int), cval(sv, c.dlo as int, c.dhi as int), TOPN as int)
            && (forall|k: int| 0 <= k < t.k ==> #[trigger] t.vals@[k] as int == ctot(sv, c.dlo as int, c.dhi as int, t.rows@[k] as int))
            && groups_capped(sv, c.dlo as int, c.dhi as int),
        r matches GenOut::Over(a) ==> a < c.nc && natok(sv, a as int)
            && ctabs(sv, c.dlo as int, c.dhi as int, a as int) > i128_max(),
{
    let ghost (dlo, dhi) = (c.dlo as int, c.dhi as int);
    let ghost vf = cval(sv, dlo, dhi);
    let mut top = top;
    let mut a: usize = 0;
    proof { assert(glist(sv, dlo, dhi, 0) =~= Seq::<int>::empty()); }
    while a < c.nc
        invariant
            cols_ok(*c, sv), dlo == c.dlo, dhi == c.dhi, vf == cval(sv, dlo, dhi), a <= c.nc,
            top_inv(top, glist(sv, dlo, dhi, a as int), vf), top.cap == TOPN,
            forall|b: int| 0 <= b < a && #[trigger] is_group(sv, dlo, dhi, b) ==> ctabs(sv, dlo, dhi, b) <= i128_max(),
        decreases c.nc - a,
    {
        proof { lemma_glist(sv, dlo, dhi, a as int); }
        if nation_of(c, a, Ghost(sv)).is_some() {
            match cust_total(c, a, Ghost(sv)) {
                None => {
                    return GenOut::Over(a);
                },
                Some((s, any)) => {
                    if any {
                        proof {
                            assert(is_group(sv, dlo, dhi, a as int));
                            assert(!glist(sv, dlo, dhi, a as int).contains(a as int));
                        }
                        top_offer(&mut top, a, s, Ghost(glist(sv, dlo, dhi, a as int)), Ghost(vf));
                        proof {
                            assert(glist(sv, dlo, dhi, a + 1) == glist(sv, dlo, dhi, a as int).push(a as int));
                        }
                    } else {
                        proof { assert(!is_group(sv, dlo, dhi, a as int)); }
                    }
                },
            }
        } else {
            proof { assert(!is_group(sv, dlo, dhi, a as int)); }
        }
        a = a + 1;
    }
    proof {
        assert forall|k: int| 0 <= k < top.k implies #[trigger] top.vals@[k] as int == ctot(sv, dlo, dhi, top.rows@[k] as int) by {}
    }
    GenOut::Top(top)
}

} // verus!
