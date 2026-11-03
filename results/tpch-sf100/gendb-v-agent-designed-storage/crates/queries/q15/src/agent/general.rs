//! The general path: exact for any stored data the storage contracts admit, serial and quadratic (each group's
//! totals by a pass over every stored lineitem row). It runs only when the fast path's guards fail.
//!
//! `general` finds the largest group sum `M` (the totals of every qualifying row's group; `is_max`, or no group)
//! with every group's absolute mass inside `i128` (`group_caps`), then decides per supplier row whether its key is a
//! group of sum `M`; or it returns a group whose absolute mass exceeds `i128` (the statement is then outside its
//! capacity domain).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::query::*;
use crate::link::expr::{ival, i128_max};
use super::group::*;
use super::model::*;
use super::answer::*;
use super::emit::*;

verus! {

/// The group key of supplier key `k`.
pub open spec fn kr(k: int) -> Row {
    seq![Val::Int(k)]
}

/// The decoded columns are in the numeric(15, 2) domain.
pub open spec fn li_vals_ok(c: Li) -> bool {
    &&& li_shape(c)
    &&& forall|j: int| 0 <= j < c.n ==> -p15() < #[trigger] price_v(c, j) < p15() && -p15() < disc_v(c, j) < p15()
}

/// Row `j`'s decoded columns `(l_suppkey, l_extendedprice, l_discount, l_shipdate)`.
pub fn row_vals(c: &Li, j: usize) -> (r: (i128, i128, i128, i128))
    requires li_shape(*c), j < c.n,
    ensures
        r.0 == supp_v(*c, j as int),
        r.1 == price_v(*c, j as int),
        r.2 == disc_v(*c, j as int),
        r.3 == ship_v(*c, j as int),
    no_unwind
{
    proof {
        crate::stores::lisupp::interface::common::read::lemma_div_lt(j as int, c.bs as int, c.nb as int);
    }
    let b = (j as u64 / c.bs) as usize;
    (c.supp_base[b] as i128 + c.supp[j] as i128, c.price_base[b] as i128 + c.price[j] as i128,
        c.disc_base[b] as i128 + c.disc[j] as i128, c.ship_base[b] as i128 + c.ship[j] as i128)
}

/// Row `j` of the stored rows hits group `kr(k)` exactly when it qualifies and has key `k`.
pub proof fn lemma_hit_row(c: Li, lo: int, hi: int, j: int, k: int)
    requires 0 <= j < c.n,
    ensures
        hit(qg(lo, hi), xs_of(c)[j], kr(k)) == (lo <= ship_v(c, j) <= hi && supp_v(c, j) == k),
        (qg(lo, hi).qual)(xs_of(c)[j]) == (lo <= ship_v(c, j) <= hi),
        (qg(lo, hi).key)(xs_of(c)[j]) == kr(supp_v(c, j)),
        (qg(lo, hi).arg)(0, xs_of(c)[j]) == price_v(c, j) * (100 - disc_v(c, j)),
{
    let x = xs_of(c)[j];
    assert(key_of(x) =~= kr(supp_v(c, j)));
    if key_of(x) == kr(k) {
        assert(key_of(x)[0] == kr(k)[0]);
    }
}

/// A product of two numeric(15, 2)-sized factors fits far inside `i128`.
proof fn lemma_rev_bound(p: int, d: int)
    requires -p15() < p < p15(), -p15() < d < p15(),
    ensures abs(p * (100 - d)) < 4 * p15() * p15(), 4 * p15() * p15() < i128_max(),
{
    assert(-2 * p15() < 100 - d < 2 * p15());
    assert(abs(p * (100 - d)) < p15() * (2 * p15())) by (nonlinear_arith)
        requires -p15() < p < p15(), -2 * p15() < 100 - d < 2 * p15(), p15() > 0;
}

/// A row that hits group `k` makes the group non-empty.
pub proof fn lemma_hit_count(g: QuerySpec, xs: Seq<Row>, i: int, k: Row)
    requires 0 <= i < xs.len(), hit(g, xs[i], k),
    ensures gcount(g, xs, k) > 0,
{
    lemma_range_step(g, xs, 0, i, k, 0);
    lemma_split(g, xs, 0, i + 1, xs.len() as int, k, 0);
    assert(xs.subrange(0, xs.len() as int) =~= xs);
}

/// The exact `(sum, absolute mass, count)` of group `kr(key)` over the stored rows, or `None` when its absolute
/// mass exceeds `i128` (the group is then non-empty).
pub fn key_totals(c: &Li, lo: i64, hi: i64, key: i128) -> (r: Option<(i128, i128, u64)>)
    requires li_vals_ok(*c),
    ensures ({
        let g = qg(lo as int, hi as int);
        let xs = xs_of(*c);
        &&& r matches Some(t) ==> t.0 == gsum(g, xs, kr(key as int), 0) && t.1 == gabs(g, xs, kr(key as int), 0)
                && t.2 == gcount(g, xs, kr(key as int))
        &&& r is None ==> gabs(g, xs, kr(key as int), 0) > i128_max() && gcount(g, xs, kr(key as int)) > 0
    }),
{
    let ghost g = qg(lo as int, hi as int);
    let ghost xs = xs_of(*c);
    let ghost k = kr(key as int);
    let mut sum: i128 = 0;
    let mut mass: i128 = 0;
    let mut cnt: u64 = 0;
    let mut j: usize = 0;
    proof {
        lemma_empty(g, xs, 0, k, 0);
    }
    while j < c.n
        invariant
            li_vals_ok(*c),
            g == qg(lo as int, hi as int),
            xs == xs_of(*c),
            k == kr(key as int),
            j <= c.n,
            sum == gsum(g, xs.subrange(0, j as int), k, 0),
            mass == gabs(g, xs.subrange(0, j as int), k, 0),
            cnt == gcount(g, xs.subrange(0, j as int), k),
            cnt <= j,
        decreases c.n - j,
    {
        let (sk, pr, ds, sd) = row_vals(c, j);
        proof {
            lemma_hit_row(*c, lo as int, hi as int, j as int, key as int);
            lemma_range_step(g, xs, 0, j as int, k, 0);
            lemma_abs_bound(g, xs.subrange(0, j as int), k, 0);
        }
        if lo as i128 <= sd && sd <= hi as i128 && sk == key {
            proof {
                lemma_rev_bound(pr as int, ds as int);
            }
            let v = pr * (100 - ds);
            let a = if v < 0 { -v } else { v };
            if mass > i128::MAX - a {
                proof {
                    lemma_split(g, xs, 0, j + 1, xs.len() as int, k, 0);
                    assert(xs.subrange(0, xs.len() as int) =~= xs);
                    lemma_abs_bound(g, xs.subrange(j + 1, xs.len() as int), k, 0);
                    lemma_hit_count(g, xs, j as int, k);
                }
                return None;
            }
            sum = sum + v;
            mass = mass + a;
            cnt = cnt + 1;
        }
        j = j + 1;
    }
    proof {
        assert(xs.subrange(0, c.n as int) =~= xs);
    }
    Some((sum, mass, cnt))
}

/// The general plan: the largest group sum `M` (or no group) with every group inside `i128`, and per supplier row
/// whether its key is a group of sum `M`; or a group whose absolute mass exceeds `i128`.
pub fn general(c: &Li, s: &Su, lo: i64, hi: i64) -> (r: Result<(i128, Vec<bool>), Ghost<Row>>)
    requires
        li_vals_ok(*c),
        su_shape(*s),
    ensures ({
        let g = qg(lo as int, hi as int);
        let xs = xs_of(*c);
        &&& r matches Ok(t) ==> {
            &&& group_caps(g, xs)
            &&& is_max(g, xs, t.0 as int) || no_groups(g, xs)
            &&& t.1@.len() == s.ns
            &&& forall|j: int| 0 <= j < s.ns ==> #[trigger] t.1@[j] == hit_m(g, xs, t.0 as int, mrow(*s, j))
        }
        &&& r matches Err(k) ==> gcount(g, xs, k@) > 0 && gabs(g, xs, k@, 0) > i128_max()
    }),
{
    let ghost g = qg(lo as int, hi as int);
    let ghost xs = xs_of(*c);
    let mut m: i128 = 0;
    let mut found = false;
    let ghost mut wk: Row = kr(0);
    let mut i: usize = 0;
    while i < c.n
        invariant
            li_vals_ok(*c),
            g == qg(lo as int, hi as int),
            xs == xs_of(*c),
            i <= c.n,
            found ==> gcount(g, xs, wk) > 0 && gsum(g, xs, wk, 0) == m,
            forall|i2: int| 0 <= i2 < i && #[trigger] (g.qual)(xs[i2]) ==>
                found && gabs(g, xs, (g.key)(xs[i2]), 0) <= i128_max() && gsum(g, xs, (g.key)(xs[i2]), 0) <= m,
        decreases c.n - i,
    {
        let (sk, _pr, _ds, sd) = row_vals(c, i);
        proof {
            lemma_hit_row(*c, lo as int, hi as int, i as int, sk as int);
        }
        if lo as i128 <= sd && sd <= hi as i128 {
            match key_totals(c, lo, hi, sk) {
                None => {
                    return Err(Ghost(kr(sk as int)));
                },
                Some((sm, _ms, _cn)) => {
                    proof {
                        lemma_hit_count(g, xs, i as int, kr(sk as int));
                    }
                    if !found || sm > m {
                        m = sm;
                        found = true;
                        proof {
                            wk = kr(sk as int);
                        }
                    }
                },
            }
        }
        i = i + 1;
    }
    proof {
        if found {
            assert forall|k: Row| #[trigger] gcount(g, xs, k) > 0 implies gsum(g, xs, k, 0) <= m by {
                lemma_count_witness(g, xs, k);
                let i2 = choose|i2: int| 0 <= i2 < xs.len() && #[trigger] hit(g, xs[i2], k);
                assert((g.qual)(xs[i2]));
            }
            assert(gsum(g, xs, wk, 0) == m);
        } else {
            assert forall|k: Row| #[trigger] gcount(g, xs, k) == 0 by {
                if gcount(g, xs, k) > 0 {
                    lemma_count_witness(g, xs, k);
                    let i2 = choose|i2: int| 0 <= i2 < xs.len() && #[trigger] hit(g, xs[i2], k);
                    assert((g.qual)(xs[i2]));
                }
            }
        }
        assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
            assert(j == 0);
            if gcount(g, xs, k) > 0 {
                lemma_count_witness(g, xs, k);
                let i2 = choose|i2: int| 0 <= i2 < xs.len() && #[trigger] hit(g, xs[i2], k);
                assert((g.qual)(xs[i2]));
            } else {
                lemma_zero_count(g, xs, k, j);
            }
        }
    }
    // per supplier row
    let mut hits: Vec<bool> = Vec::new();
    let mut j: usize = 0;
    while j < s.ns
        invariant
            li_vals_ok(*c),
            su_shape(*s),
            g == qg(lo as int, hi as int),
            xs == xs_of(*c),
            group_caps(g, xs),
            found ==> is_max(g, xs, m as int),
            !found ==> no_groups(g, xs),
            j <= s.ns,
            hits@.len() == j,
            forall|j2: int| 0 <= j2 < j ==> #[trigger] hits@[j2] == hit_m(g, xs, m as int, mrow(*s, j2)),
        decreases s.ns - j,
    {
        let ghost kj = kr(skey_v(*s, j as int));
        proof {
            assert(seq![mrow(*s, j as int)[0]] =~= kj);
        }
        if found {
            let k = skey_at(s, j);
            match key_totals(c, lo, hi, k) {
                None => {
                    return Err(Ghost(kr(k as int)));
                },
                Some((sm, _ms, cn)) => {
                    hits.push(cn > 0 && sm == m);
                },
            }
        } else {
            hits.push(false);
        }
        proof {
            assert(hits@[j as int] == hit_m(g, xs, m as int, mrow(*s, j as int)));
        }
        j = j + 1;
    }
    proof {
        if found {
            assert(is_max(g, xs, m as int));
        }
    }
    Ok((m, hits))
}

} // verus!
