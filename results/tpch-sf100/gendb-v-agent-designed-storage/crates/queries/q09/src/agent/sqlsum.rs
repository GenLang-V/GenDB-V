//! The relational link of Q9, part 2: the six-fold index sum of a group term over the joined model rows collapses,
//! under the declared primary keys, to one sum over the stored lineitem rows (`lemma_collapse`). A term `gterm(k, w)`
//! is `w(x)` on a projected FROM row `x` that satisfies the WHERE condition and has the group key `k`, else 0. For a
//! lineitem row `j` only the matching rows contribute: the nation of its supplier (`sn`), its order (`lq`), its
//! partsupp row (`lt`), its supplier (`ls`) and its part (`lc`), in that order of collapse; the part and supplier
//! sums are first exchanged with the lineitem sum.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::expr::ival;
use super::common::isum::*;
use super::model::*;
use super::qspec::*;
use super::sqlrow::*;
use super::sqllink::*;
use super::lookups::{lemma_ppos, lemma_spos, lemma_tpos, lemma_opos, lemma_npos};
use super::year::year_of;

verus! {

/// The group key of a projected FROM row: n_name, the order year.
pub open spec fn keyx(x: Row) -> Row {
    seq![x[16], Val::Num { coeff: year_of(ival(x[14])), scale: 0 }]
}

/// The group term of key `k` and weight `w`.
pub open spec fn gterm(p: QP, k: Row, w: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| if qual_x(p, x) && keyx(x) == k { w(x) } else { 0int }
}

/// The group key of lineitem row `j`.
pub open spec fn jkey(m: M, j: int) -> Row {
    seq![Val::Text(nname(m, jn(m, j))), Val::Num { coeff: jyear(m, j), scale: 0 }]
}

/// The joined row of lineitem row `j` with its part, supplier, partsupp row, order and nation.
pub open spec fn jfull(m: M, j: int) -> Row {
    jrow(m, lc(m, j), ls(m, j), j, lt(m, j), lq(m, j), jn(m, j))
}

/// The collapsed term of lineitem row `j`.
pub open spec fn jterm(m: M, p: QP, k: Row, w: spec_fn(Row) -> int) -> spec_fn(int) -> int {
    |j: int| if jok(m, p, j) && jkey(m, j) == k { w(jfull(m, j)) } else { 0int }
}

/// A term vanishes off the join: every key equality must hold.
proof fn lemma_term_join(m: M, p: QP, k: Row, w: spec_fn(Row) -> int, c: int, s: int, j: int, t: int, q: int, n: int)
    requires
        model_ok(m),
        0 <= c < m.p_n && 0 <= s < m.s_n && 0 <= j < m.l_n && 0 <= t < m.t_n && 0 <= q < m.o_n && 0 <= n < m.n_n,
        gterm(p, k, w)(jrow(m, c, s, j, t, q, n)) != 0,
    ensures
        skey(m, s) == lsk(m, j), tsk(m, t) == lsk(m, j), tpk(m, t) == lpk(m, j), pkey(m, c) == lpk(m, j),
        okey(m, q) == lok(m, j), snk(m, s) == nkey(m, n),
{
    lemma_jrow_typed(m, c, s, j, t, q, n);
}

/// Nation: only the nation row of the supplier's key contributes.
proof fn lemma_c6(m: M, p: QP, k: Row, w: spec_fn(Row) -> int, c: int, s: int, j: int, t: int, q: int)
    requires
        model_ok(m),
        0 <= c < m.p_n && 0 <= s < m.s_n && 0 <= j < m.l_n && 0 <= t < m.t_n && 0 <= q < m.o_n,
    ensures
        s6(m, gterm(p, k, w), prow(m, c) + srow(m, s) + lrow(m, j) + trow(m, t) + orow(m, q))
            == if sn(m, s) < m.n_n { gterm(p, k, w)(jrow(m, c, s, j, t, q, sn(m, s))) } else { 0int },
{
    let f = gterm(p, k, w);
    let x = prow(m, c) + srow(m, s) + lrow(m, j) + trow(m, t) + orow(m, q);
    let g = |n: int| f(x + nrow(m, n));
    let n0 = sn(m, s);
    lemma_npos(m, snk(m, s), 0);
    assert forall|n: int| 0 <= n < m.n_n && n != n0 implies #[trigger] g(n) == 0 by {
        assert(x + nrow(m, n) == jrow(m, c, s, j, t, q, n));
        if f(jrow(m, c, s, j, t, q, n)) != 0 {
            lemma_term_join(m, p, k, w, c, s, j, t, q, n);
            lemma_npos(m, snk(m, s), n);
        }
    }
    lemma_isum_single(m.n_n, g, n0);
    if 0 <= n0 < m.n_n {
        assert(x + nrow(m, n0) == jrow(m, c, s, j, t, q, n0));
    }
}

/// Orders: only the order of the lineitem's key contributes.
proof fn lemma_c5(m: M, p: QP, k: Row, w: spec_fn(Row) -> int, c: int, s: int, j: int, t: int)
    requires
        model_ok(m),
        0 <= c < m.p_n && 0 <= s < m.s_n && 0 <= j < m.l_n && 0 <= t < m.t_n,
    ensures
        s5(m, gterm(p, k, w), prow(m, c) + srow(m, s) + lrow(m, j) + trow(m, t))
            == if lq(m, j) < m.o_n && sn(m, s) < m.n_n { gterm(p, k, w)(jrow(m, c, s, j, t, lq(m, j), sn(m, s))) } else { 0int },
{
    let f = gterm(p, k, w);
    let x = prow(m, c) + srow(m, s) + lrow(m, j) + trow(m, t);
    let g = |q: int| s6(m, f, x + orow(m, q));
    let q0 = lq(m, j);
    lemma_opos(m, lok(m, j), 0);
    lemma_npos(m, snk(m, s), 0);
    assert forall|q: int| 0 <= q < m.o_n implies #[trigger] g(q)
        == if sn(m, s) < m.n_n { f(jrow(m, c, s, j, t, q, sn(m, s))) } else { 0int } by {
        lemma_c6(m, p, k, w, c, s, j, t, q);
    }
    assert forall|q: int| 0 <= q < m.o_n && q != q0 implies #[trigger] g(q) == 0 by {
        if sn(m, s) < m.n_n && f(jrow(m, c, s, j, t, q, sn(m, s))) != 0 {
            lemma_term_join(m, p, k, w, c, s, j, t, q, sn(m, s));
            lemma_opos(m, lok(m, j), q);
        }
    }
    lemma_isum_single(m.o_n, g, q0);
}

/// Partsupp: only the partsupp row of the lineitem's (part, supplier) keys contributes.
proof fn lemma_c4(m: M, p: QP, k: Row, w: spec_fn(Row) -> int, c: int, s: int, j: int)
    requires
        model_ok(m),
        0 <= c < m.p_n && 0 <= s < m.s_n && 0 <= j < m.l_n,
    ensures
        s4(m, gterm(p, k, w), prow(m, c) + srow(m, s) + lrow(m, j)) == gc(m, p, k, w, c, s, j),
{
    let f = gterm(p, k, w);
    let x = prow(m, c) + srow(m, s) + lrow(m, j);
    let g = |t: int| s5(m, f, x + trow(m, t));
    let t0 = lt(m, j);
    lemma_tpos(m, lpk(m, j), lsk(m, j), 0);
    assert forall|t: int| 0 <= t < m.t_n implies #[trigger] g(t)
        == if lq(m, j) < m.o_n && sn(m, s) < m.n_n { f(jrow(m, c, s, j, t, lq(m, j), sn(m, s))) } else { 0int } by {
        lemma_c5(m, p, k, w, c, s, j, t);
    }
    assert forall|t: int| 0 <= t < m.t_n && t != t0 implies #[trigger] g(t) == 0 by {
        if lq(m, j) < m.o_n && sn(m, s) < m.n_n && f(jrow(m, c, s, j, t, lq(m, j), sn(m, s))) != 0 {
            lemma_opos(m, lok(m, j), 0);
            lemma_npos(m, snk(m, s), 0);
            lemma_term_join(m, p, k, w, c, s, j, t, lq(m, j), sn(m, s));
            lemma_tpos(m, lpk(m, j), lsk(m, j), t);
        }
    }
    lemma_isum_single(m.t_n, g, t0);
}

/// The term of part row `c`, supplier row `s` and lineitem row `j` after the inner collapses.
pub open spec fn gc(m: M, p: QP, k: Row, w: spec_fn(Row) -> int, c: int, s: int, j: int) -> int {
    if lt(m, j) < m.t_n && lq(m, j) < m.o_n && sn(m, s) < m.n_n {
        gterm(p, k, w)(jrow(m, c, s, j, lt(m, j), lq(m, j), sn(m, s)))
    } else {
        0int
    }
}

/// Supplier: only the supplier of the lineitem's key contributes.
proof fn lemma_cs(m: M, p: QP, k: Row, w: spec_fn(Row) -> int, c: int, j: int)
    requires model_ok(m), 0 <= c < m.p_n, 0 <= j < m.l_n,
    ensures isum(m.s_n, |s: int| gc(m, p, k, w, c, s, j)) == if ls(m, j) < m.s_n { gc(m, p, k, w, c, ls(m, j), j) } else { 0int },
{
    let g = |s: int| gc(m, p, k, w, c, s, j);
    let s0 = ls(m, j);
    lemma_spos(m, lsk(m, j), 0);
    assert forall|s: int| 0 <= s < m.s_n && s != s0 implies #[trigger] g(s) == 0 by {
        if g(s) != 0 {
            lemma_tpos(m, lpk(m, j), lsk(m, j), 0);
            lemma_opos(m, lok(m, j), 0);
            lemma_npos(m, snk(m, s), 0);
            lemma_term_join(m, p, k, w, c, s, j, lt(m, j), lq(m, j), sn(m, s));
            lemma_spos(m, lsk(m, j), s);
        }
    }
    lemma_isum_single(m.s_n, g, s0);
}

/// Part: only the part of the lineitem's key contributes.
proof fn lemma_cc(m: M, p: QP, k: Row, w: spec_fn(Row) -> int, j: int)
    requires model_ok(m), 0 <= j < m.l_n,
    ensures
        isum(m.p_n, |c: int| if ls(m, j) < m.s_n { gc(m, p, k, w, c, ls(m, j), j) } else { 0int })
            == if lc(m, j) < m.p_n && ls(m, j) < m.s_n { gc(m, p, k, w, lc(m, j), ls(m, j), j) } else { 0int },
{
    let g = |c: int| if ls(m, j) < m.s_n { gc(m, p, k, w, c, ls(m, j), j) } else { 0int };
    let c0 = lc(m, j);
    lemma_ppos(m, lpk(m, j), 0);
    lemma_spos(m, lsk(m, j), 0);
    assert forall|c: int| 0 <= c < m.p_n && c != c0 implies #[trigger] g(c) == 0 by {
        if g(c) != 0 {
            let s = ls(m, j);
            lemma_tpos(m, lpk(m, j), lsk(m, j), 0);
            lemma_opos(m, lok(m, j), 0);
            lemma_npos(m, snk(m, s), 0);
            lemma_term_join(m, p, k, w, c, s, j, lt(m, j), lq(m, j), sn(m, s));
            lemma_ppos(m, lpk(m, j), c);
        }
    }
    lemma_isum_single(m.p_n, g, c0);
}

/// At the joined row of a lineitem row the term is its collapsed term.
proof fn lemma_jterm_at(m: M, p: QP, k: Row, w: spec_fn(Row) -> int, j: int)
    requires model_ok(m), 0 <= j < m.l_n,
    ensures
        (if lc(m, j) < m.p_n && ls(m, j) < m.s_n { gc(m, p, k, w, lc(m, j), ls(m, j), j) } else { 0int })
            == jterm(m, p, k, w)(j),
{
    let (c, s, t, q) = (lc(m, j), ls(m, j), lt(m, j), lq(m, j));
    lemma_ppos(m, lpk(m, j), 0);
    lemma_spos(m, lsk(m, j), 0);
    lemma_tpos(m, lpk(m, j), lsk(m, j), 0);
    lemma_opos(m, lok(m, j), 0);
    if c < m.p_n && s < m.s_n && t < m.t_n && q < m.o_n {
        let n = sn(m, s);
        lemma_npos(m, snk(m, s), 0);
        if n < m.n_n {
            let x = jrow(m, c, s, j, t, q, n);
            lemma_jrow_typed(m, c, s, j, t, q, n);
            assert(joins_x(x));
            assert(like_x(p, x) == plike(m, p, c));
            assert(keyx(x) =~= jkey(m, j));
            assert(jfull(m, j) == x);
        }
    }
}

/// Named inner sums (quantifier triggers): over lineitem rows for (part, supplier), over suppliers for (part,
/// lineitem), and their outer sums.
pub open spec fn sum_j(m: M, p: QP, k: Row, w: spec_fn(Row) -> int, c: int, s: int) -> int {
    isum(m.l_n, |j: int| gc(m, p, k, w, c, s, j))
}

pub open spec fn sum_s(m: M, p: QP, k: Row, w: spec_fn(Row) -> int, c: int, j: int) -> int {
    isum(m.s_n, |s: int| gc(m, p, k, w, c, s, j))
}

pub open spec fn sum_sj(m: M, p: QP, k: Row, w: spec_fn(Row) -> int, c: int) -> int {
    isum(m.s_n, |s: int| sum_j(m, p, k, w, c, s))
}

pub open spec fn sum_js(m: M, p: QP, k: Row, w: spec_fn(Row) -> int, c: int) -> int {
    isum(m.l_n, |j: int| sum_s(m, p, k, w, c, j))
}

pub open spec fn sum_cs(m: M, p: QP, k: Row, w: spec_fn(Row) -> int, j: int) -> int {
    isum(m.p_n, |c: int| sum_s(m, p, k, w, c, j))
}

/// The inner collapses under the part and supplier sums.
proof fn lemma_collapse_inner(m: M, p: QP, k: Row, w: spec_fn(Row) -> int)
    requires model_ok(m),
    ensures isum(m.p_n, |c: int| s2(m, gterm(p, k, w), prow(m, c))) == isum(m.p_n, |c: int| sum_sj(m, p, k, w, c)),
{
    hide(gc);
    let f = gterm(p, k, w);
    assert forall|c: int| 0 <= c < m.p_n implies #[trigger] s2(m, f, prow(m, c)) == sum_sj(m, p, k, w, c) by {
        assert forall|s: int| 0 <= s < m.s_n implies #[trigger] s3(m, f, prow(m, c) + srow(m, s)) == sum_j(m, p, k, w, c, s) by {
            assert forall|j: int| 0 <= j < m.l_n implies #[trigger] s4(m, f, prow(m, c) + srow(m, s) + lrow(m, j))
                == gc(m, p, k, w, c, s, j) by {
                lemma_c4(m, p, k, w, c, s, j);
            }
            lemma_isum_ext(m.l_n, |j: int| s4(m, f, prow(m, c) + srow(m, s) + lrow(m, j)), |j: int| gc(m, p, k, w, c, s, j));
        }
        lemma_isum_ext(m.s_n, |s: int| s3(m, f, prow(m, c) + srow(m, s)), |s: int| sum_j(m, p, k, w, c, s));
    }
    lemma_isum_ext(m.p_n, |c: int| s2(m, f, prow(m, c)), |c: int| sum_sj(m, p, k, w, c));
}

/// Exchange: the lineitem sum outermost.
proof fn lemma_collapse_swap(m: M, p: QP, k: Row, w: spec_fn(Row) -> int)
    ensures isum(m.p_n, |c: int| sum_sj(m, p, k, w, c)) == isum(m.l_n, |j: int| sum_cs(m, p, k, w, j)),
{
    hide(gc);
    assert forall|c: int| 0 <= c < m.p_n implies #[trigger] sum_sj(m, p, k, w, c) == sum_js(m, p, k, w, c) by {
        let h = |s: int, j: int| gc(m, p, k, w, c, s, j);
        lemma_isum_swap(m.s_n, m.l_n, h);
        assert forall|s: int| 0 <= s < m.s_n implies #[trigger] sum_j(m, p, k, w, c, s) == isum(m.l_n, |j: int| h(s, j)) by {
            lemma_isum_ext(m.l_n, |j: int| gc(m, p, k, w, c, s, j), |j: int| h(s, j));
        }
        lemma_isum_ext(m.s_n, |s: int| sum_j(m, p, k, w, c, s), |s: int| isum(m.l_n, |j: int| h(s, j)));
        assert forall|j: int| 0 <= j < m.l_n implies #[trigger] sum_s(m, p, k, w, c, j) == isum(m.s_n, |s: int| h(s, j)) by {
            lemma_isum_ext(m.s_n, |s: int| gc(m, p, k, w, c, s, j), |s: int| h(s, j));
        }
        lemma_isum_ext(m.l_n, |j: int| isum(m.s_n, |s: int| h(s, j)), |j: int| sum_s(m, p, k, w, c, j));
    }
    lemma_isum_ext(m.p_n, |c: int| sum_sj(m, p, k, w, c), |c: int| sum_js(m, p, k, w, c));
    let h2 = |c: int, j: int| sum_s(m, p, k, w, c, j);
    lemma_isum_swap(m.p_n, m.l_n, h2);
    assert forall|c: int| 0 <= c < m.p_n implies #[trigger] sum_js(m, p, k, w, c) == isum(m.l_n, |j: int| h2(c, j)) by {
        lemma_isum_ext(m.l_n, |j: int| sum_s(m, p, k, w, c, j), |j: int| h2(c, j));
    }
    lemma_isum_ext(m.p_n, |c: int| sum_js(m, p, k, w, c), |c: int| isum(m.l_n, |j: int| h2(c, j)));
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] sum_cs(m, p, k, w, j) == isum(m.p_n, |c: int| h2(c, j)) by {
        lemma_isum_ext(m.p_n, |c: int| sum_s(m, p, k, w, c, j), |c: int| h2(c, j));
    }
    lemma_isum_ext(m.l_n, |j: int| isum(m.p_n, |c: int| h2(c, j)), |j: int| sum_cs(m, p, k, w, j));
}

/// The supplier and part collapses under the lineitem sum.
proof fn lemma_collapse_outer(m: M, p: QP, k: Row, w: spec_fn(Row) -> int)
    requires model_ok(m),
    ensures isum(m.l_n, |j: int| sum_cs(m, p, k, w, j)) == isum(m.l_n, jterm(m, p, k, w)),
{
    hide(gc);
    hide(jterm);
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] sum_cs(m, p, k, w, j) == jterm(m, p, k, w)(j) by {
        assert forall|c: int| 0 <= c < m.p_n implies #[trigger] sum_s(m, p, k, w, c, j)
            == (if ls(m, j) < m.s_n { gc(m, p, k, w, c, ls(m, j), j) } else { 0int }) by {
            lemma_cs(m, p, k, w, c, j);
        }
        lemma_isum_ext(m.p_n, |c: int| sum_s(m, p, k, w, c, j),
            |c: int| if ls(m, j) < m.s_n { gc(m, p, k, w, c, ls(m, j), j) } else { 0int });
        lemma_cc(m, p, k, w, j);
        lemma_jterm_at(m, p, k, w, j);
    }
    lemma_isum_ext(m.l_n, |j: int| sum_cs(m, p, k, w, j), jterm(m, p, k, w));
}

/// The six-fold index sum of a group term collapses to the lineitem sum of its collapsed terms.
pub proof fn lemma_collapse(m: M, p: QP, k: Row, w: spec_fn(Row) -> int)
    requires model_ok(m),
    ensures isum(m.p_n, |c: int| s2(m, gterm(p, k, w), prow(m, c))) == isum(m.l_n, jterm(m, p, k, w)),
{
    lemma_collapse_inner(m, p, k, w);
    lemma_collapse_swap(m, p, k, w);
    lemma_collapse_outer(m, p, k, w);
}

} // verus!
