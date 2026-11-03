//! The statement's body over `supplier x nation`: `lemma_body` proves `eval_query(db, [], body_q(ps))` is
//! `nf::nf_outcome`. The outer WHERE on `s ++ n` is the partsupp subquery's error, else two-valued
//! `sk_ok(s_suppkey) && s_nationkey = n_nationkey && n_name = $3` (`lemma_outer_pred`); with distinct nation keys at
//! most one nation row joins each supplier row, so the kept product rows projected to `[s_name, s_address]` are
//! `nf_rows` (`lemma_kept_product`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::link::join::*;
use crate::link::expr::*;
use crate::bridge::collect::lemma_collect_all;
use crate::link::capacity::lemma_collect_uniform_err;
use crate::exec::relational::domain::{filter_results, project_results};
use super::typed::*;
use super::nf::*;
use super::ast::*;
use super::sem_ps::*;
use super::sem_li::lemma_int_eq;

verus! {

/// A row of `supplier ++ nation` as the outer WHERE reads it.
pub open spec fn xrow_ok(x: Row) -> bool {
    &&& x.len() == 11
    &&& is_int(x[0])
    &&& is_int(x[3])
    &&& is_int(x[7])
    &&& is_text(x[8])
}

/// The outer WHERE's truth when the subquery succeeds.
pub open spec fn outer_sel(db: Database, ps: Seq<Literal>, d1: int) -> spec_fn(Row) -> bool {
    |x: Row| sk_ok(db, pat_of(ps), d0_of(ps), d1, ival(x[0])) && x[3] == x[7] && tval(x[8]) == nname_of(ps)
}

/// `$3` is the text literal of the nation name.
pub proof fn lemma_name_lit(ps: Seq<Literal>)
    requires crate::query::param_domain(ps),
    ensures ps[2] == Literal::Text(nname_of(ps)),
{
    assert(crate::query::param_typed(ps));
}

/// `n_name = $3` on `x`.
proof fn lemma_name_pred(db: Database, x: Row, l2: Literal, name: Seq<u8>)
    requires x.len() == 11, is_text(x[8]), l2 == Literal::Text(name),
    ensures
        eval_pred(db, x, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(8), b: Expr::Lit(l2) })
            == Ok::<Truth, SqlError>(truth_of(tval(x[8]) == name)),
{
    lemma_expr_col(db, x, 8);
    lemma_expr_text(db, x, name);
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(8), Expr::Lit(l2), tval(x[8]), name);
}

/// The outer WHERE on one row.
pub proof fn lemma_outer_pred(db: Database, x: Row, ps: Seq<Literal>, d1: int)
    requires sem_ok(db, ps, d1), xrow_ok(x),
    ensures
        eval_pred(db, x, outer_pred(ps)) == if ps_err(db, ps) {
            Err::<Truth, SqlError>(SqlError::InvalidEscapeSequence)
        } else {
            Ok::<Truth, SqlError>(truth_of(outer_sel(db, ps, d1)(x)))
        },
{
    hide(eval_pred);
    lemma_in_ps(db, x, ps, d1);
    lemma_int_eq(db, x, 3, 7);
    lemma_name_lit(ps);
    lemma_name_pred(db, x, ps[2], nname_of(ps));
    let a = cand(in_ps(ps), ccmp(CmpOp::Eq, 3, 7));
    if ps_err(db, ps) {
        assert(eval_pred(db, x, a) == Err::<Truth, SqlError>(SqlError::InvalidEscapeSequence)) by {
            reveal(eval_pred);
        }
        assert(eval_pred(db, x, outer_pred(ps)) == Err::<Truth, SqlError>(SqlError::InvalidEscapeSequence)) by {
            reveal(eval_pred);
        }
    } else {
        let sk = sk_ok(db, pat_of(ps), d0_of(ps), d1, ival(x[0]));
        assert(eval_pred(db, x, a) == Ok::<Truth, SqlError>(truth_of(sk && x[3] == x[7]))) by {
            lemma_pred_and(db, x, in_ps(ps), ccmp(CmpOp::Eq, 3, 7), sk, x[3] == x[7]);
        }
        lemma_pred_and(db, x, a, name_pred(ps), sk && x[3] == x[7], tval(x[8]) == nname_of(ps));
    }
}

/// Every product row of typed supplier and nation rows is a typed outer row.
pub proof fn lemma_product_rows_ok(s: Seq<Row>, n: Seq<Row>)
    requires
        forall|i: int| 0 <= i < s.len() ==> srow_ok(#[trigger] s[i]),
        forall|j: int| 0 <= j < n.len() ==> nrow_ok(#[trigger] n[j]),
    ensures
        forall|i: int| 0 <= i < product_rows(s, n).len() ==> xrow_ok(#[trigger] product_rows(s, n)[i]),
        product_rows(s, n).len() == s.len() * n.len(),
    decreases s.len(),
{
    crate::link::join::lemma_product_index(s, n);
    if s.len() > 0 {
        let si = s.drop_last();
        assert forall|i: int| 0 <= i < si.len() implies srow_ok(#[trigger] si[i]) by {
            assert(si[i] == s[i]);
        }
        lemma_product_rows_ok(si, n);
        let p = product_rows(s, n);
        let pi = product_rows(si, n);
        let t = s.last();
        assert(srow_ok(s[s.len() - 1]));
        let m = |r: Row| t + r;
        assert(p == pi + n.map_values(m));
        assert forall|i: int| 0 <= i < p.len() implies xrow_ok(#[trigger] p[i]) by {
            if i < pi.len() {
                assert(p[i] == pi[i]);
            } else {
                let j = i - pi.len();
                assert(p[i] == t + n[j]);
                assert(nrow_ok(n[j]));
            }
        }
    }
}

/// At most one row of distinct keys has key `v`; one is kept exactly when some row satisfies the condition.
pub proof fn lemma_keep_unique(rows: Seq<Row>, h: spec_fn(Row) -> bool, v: Val)
    requires
        forall|a: int, b: int| 0 <= a < rows.len() && 0 <= b < rows.len() && a != b
            ==> #[trigger] rows[a][0] != #[trigger] rows[b][0],
        forall|i: int| 0 <= i < rows.len() && h(#[trigger] rows[i]) ==> rows[i][0] == v,
    ensures
        keep(rows, h).len() <= 1,
        (keep(rows, h).len() == 1) == (exists|j: int| 0 <= j < rows.len() && h(#[trigger] rows[j])),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let d = rows.drop_last();
        let last = rows.len() - 1;
        assert forall|a: int, b: int| 0 <= a < d.len() && 0 <= b < d.len() && a != b
            implies #[trigger] d[a][0] != #[trigger] d[b][0] by {
            assert(d[a] == rows[a] && d[b] == rows[b]);
        }
        assert forall|i: int| 0 <= i < d.len() && h(#[trigger] d[i]) implies d[i][0] == v by {
            assert(d[i] == rows[i]);
        }
        lemma_keep_unique(d, h, v);
        let e = exists|j: int| 0 <= j < d.len() && h(#[trigger] d[j]);
        if e {
            let j = choose|j: int| 0 <= j < d.len() && h(#[trigger] d[j]);
            assert(rows[j] == d[j]);
            if h(rows[last]) {
                assert(rows[j][0] == v && rows[last][0] == v);
                assert(false);
            }
        }
        if h(rows[last]) {
            assert(keep(rows, h) == keep(d, h).push(rows[last]));
        }
        if exists|j: int| 0 <= j < rows.len() && h(#[trigger] rows[j]) {
            let j = choose|j: int| 0 <= j < rows.len() && h(#[trigger] rows[j]);
            if j < last {
                assert(d[j] == rows[j]);
            }
        }
    }
}

/// `[s_name, s_address]` of an outer row.
pub open spec fn proj_row(x: Row) -> Row {
    seq![x[1], x[2]]
}

/// The output rows one supplier row contributes: one when it qualifies.
pub proof fn lemma_one_supplier(db: Database, ps: Seq<Literal>, d1: int, t: Row)
    requires sem_ok(db, ps, d1), srow_ok(t),
    ensures ({
        let g = outer_sel(db, ps, d1);
        keep(nt(db).map_values(|r: Row| t + r), g).map_values(|x: Row| proj_row(x))
            == if s_qual(db, ps, d1, t) { seq![out_row(t)] } else { Seq::<Row>::empty() }
    }),
{
    let g = outer_sel(db, ps, d1);
    let m = |r: Row| t + r;
    let n = nt(db);
    let name = nname_of(ps);
    let sk = sk_ok(db, pat_of(ps), d0_of(ps), d1, ival(t[0]));
    let h = |y: Row| g(m(y));
    lemma_keep_map(n, m, g);
    let k = keep(n, h);
    assert forall|i: int| 0 <= i < n.len() && h(#[trigger] n[i]) implies n[i][0] == t[3] by {
        assert((t + n[i])[3] == t[3] && (t + n[i])[7] == n[i][0]);
    }
    lemma_keep_unique(n, h, t[3]);
    lemma_keep_members(n, h);
    let out = k.map_values(m).map_values(|x: Row| proj_row(x));
    assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i] == out_row(t) by {
        assert(out[i] == proj_row(t + k[i]));
        assert(proj_row(t + k[i]) =~= out_row(t));
    }
    let e = exists|j: int| 0 <= j < n.len() && h(#[trigger] n[j]);
    if e {
        let j = choose|j: int| 0 <= j < n.len() && h(#[trigger] n[j]);
        assert((t + n[j])[0] == t[0] && (t + n[j])[3] == t[3] && (t + n[j])[7] == n[j][0] && (t + n[j])[8] == n[j][1]);
        assert(nrow_ok(n[j]));
        assert(n[j][0] == Val::Int(ival(t[3])) && n[j][1] == Val::Text(name));
        assert(nat_ok(db, name, ival(t[3])));
        assert(out =~= seq![out_row(t)]);
    }
    if s_qual(db, ps, d1, t) {
        let j = choose|j: int| 0 <= j < n.len() && #[trigger] n[j][0] == Val::Int(ival(t[3])) && n[j][1] == Val::Text(name);
        assert((t + n[j])[0] == t[0] && (t + n[j])[3] == t[3] && (t + n[j])[7] == n[j][0] && (t + n[j])[8] == n[j][1]);
        assert(h(n[j]));
    }
    if !e {
        assert(out =~= Seq::<Row>::empty());
    }
}

/// The kept product rows, projected, are the result rows of `nf` (supplier rows `s`, a prefix of the table).
pub proof fn lemma_kept_product(db: Database, ps: Seq<Literal>, d1: int, s: Seq<Row>)
    requires sem_ok(db, ps, d1), forall|i: int| 0 <= i < s.len() ==> srow_ok(#[trigger] s[i]),
    ensures
        keep(product_rows(s, nt(db)), outer_sel(db, ps, d1)).map_values(|x: Row| proj_row(x))
            == keep(s, s_qual_f(db, ps, d1)).map_values(|r: Row| out_row(r)),
    decreases s.len(),
{
    let g = outer_sel(db, ps, d1);
    let q = s_qual_f(db, ps, d1);
    if s.len() == 0 {
        assert(keep(product_rows(s, nt(db)), g).map_values(|x: Row| proj_row(x)) =~= Seq::<Row>::empty());
        assert(keep(s, q).map_values(|r: Row| out_row(r)) =~= Seq::<Row>::empty());
    } else {
        let si = s.drop_last();
        let t = s.last();
        assert forall|i: int| 0 <= i < si.len() implies srow_ok(#[trigger] si[i]) by {
            assert(si[i] == s[i]);
        }
        assert(srow_ok(s[s.len() - 1]));
        lemma_kept_product(db, ps, d1, si);
        let m = |r: Row| t + r;
        let a = product_rows(si, nt(db));
        let b = nt(db).map_values(m);
        assert(product_rows(s, nt(db)) == a + b);
        lemma_keep_append(a, b, g);
        lemma_one_supplier(db, ps, d1, t);
        let ka = keep(a, g);
        let kb = keep(b, g);
        assert((ka + kb).map_values(|x: Row| proj_row(x))
            =~= ka.map_values(|x: Row| proj_row(x)) + kb.map_values(|x: Row| proj_row(x)));
        let ks = keep(si, q);
        if q(t) {
            assert(keep(s, q) == ks.push(t));
            assert(ks.push(t).map_values(|r: Row| out_row(r)) =~= ks.map_values(|r: Row| out_row(r)) + seq![out_row(t)]);
        } else {
            assert(keep(s, q) == ks);
            assert(ks.map_values(|r: Row| out_row(r)) + Seq::<Row>::empty() =~= ks.map_values(|r: Row| out_row(r)));
        }
    }
}

/// The outer filter over `supplier x nation`.
pub proof fn lemma_outer_filter(db: Database, ps: Seq<Literal>, d1: int)
    requires sem_ok(db, ps, d1),
    ensures
        eval_query(db, Seq::empty(), outer_filter(ps)) == if ps_err(db, ps) && st(db).len() > 0 && nt(db).len() > 0 {
            Err::<Relation, SqlError>(SqlError::InvalidEscapeSequence)
        } else {
            Ok::<Relation, SqlError>(keep(product_rows(st(db), nt(db)), outer_sel(db, ps, d1)))
        },
{
    hide(eval_pred);
    hide(eval_query);
    let ctx = Seq::<Val>::empty();
    let (s, n) = (st(db), nt(db));
    assert forall|i: int| 0 <= i < s.len() implies srow_ok(#[trigger] s[i]) by {}
    assert forall|j: int| 0 <= j < n.len() implies nrow_ok(#[trigger] n[j]) by {}
    lemma_product_rows_ok(s, n);
    let p = product_rows(s, n);
    assert(eval_query(db, ctx, outer_from()) == Ok::<Relation, SqlError>(p)) by {
        reveal_with_fuel(eval_query, 2);
    }
    let pred = outer_pred(ps);
    crate::exec::relational::domain::lemma_eval_filter(db, ctx, pred, Box::new(outer_from()));
    let rs = filter_results(db, ctx, p, pred);
    assert forall|i: int| 0 <= i < p.len() implies #[trigger] rs[i] == eval_pred(db, p[i], pred) by {
        assert(ctx + p[i] =~= p[i]);
    }
    let g = outer_sel(db, ps, d1);
    if ps_err(db, ps) && s.len() > 0 && n.len() > 0 {
        assert(p.len() > 0) by (nonlinear_arith) requires p.len() == s.len() * n.len(), s.len() > 0, n.len() > 0;
        assert forall|i: int| 0 <= i < rs.len()
            implies #[trigger] rs[i] is Ok || rs[i] == Err::<Truth, SqlError>(SqlError::InvalidEscapeSequence) by {
            lemma_outer_pred(db, p[i], ps, d1);
        }
        lemma_outer_pred(db, p[0], ps, d1);
        lemma_collect_uniform_err(rs, SqlError::InvalidEscapeSequence, 0);
    } else if ps_err(db, ps) {
        assert(p.len() == 0) by (nonlinear_arith) requires p.len() == s.len() * n.len(), s.len() == 0 || n.len() == 0;
        lemma_collect_all(rs, Seq::<Truth>::empty());
        assert(keep_true(p, Seq::<Truth>::empty()) == Seq::<Row>::empty());
        assert(keep(p, g) == Seq::<Row>::empty());
    } else {
        let truths = Seq::new(p.len(), |i: int| truth_of(g(p[i])));
        assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(truths[i]) by {
            lemma_outer_pred(db, p[i], ps, d1);
        }
        lemma_collect_all(rs, truths);
        lemma_keep_true_keep(p, truths, g);
    }
}

/// `[Col(1), Col(2)]` on an outer row.
proof fn lemma_proj_exprs(db: Database, x: Row)
    requires x.len() == 11,
    ensures eval_exprs(db, x, seq![Expr::Col(1), Expr::Col(2)]) == Ok::<Row, SqlError>(proj_row(x)),
{
    hide(eval_expr);
    let (e0, e1) = (Expr::Col(1), Expr::Col(2));
    lemma_expr_col(db, x, 1);
    lemma_expr_col(db, x, 2);
    let a2 = seq![e0, e1];
    let a1 = seq![e0];
    assert(a2.drop_last() =~= a1 && a2.last() == e1);
    assert(a1.drop_last() =~= Seq::<Expr>::empty() && a1.last() == e0);
    lemma_eval_exprs_empty(db, x);
    lemma_eval_exprs_step(db, x, a1);
    lemma_eval_exprs_step(db, x, a2);
    assert(Seq::<Val>::empty().push(x[1]).push(x[2]) =~= proj_row(x));
}

/// The statement's body is the normal form's outcome.
pub proof fn lemma_body(db: Database, ps: Seq<Literal>, d1: int)
    requires sem_ok(db, ps, d1),
    ensures eval_query(db, Seq::empty(), body_q(ps)) == nf_outcome(db, ps, d1),
{
    let ctx = Seq::<Val>::empty();
    let (s, n) = (st(db), nt(db));
    lemma_outer_filter(db, ps, d1);
    let exprs = seq![Expr::Col(1), Expr::Col(2)];
    crate::exec::relational::domain::lemma_eval_project(db, ctx, exprs, Box::new(outer_filter(ps)));
    assert(ps_err(db, ps) == (pst(db).len() > 0 && part_err(db, pat_of(ps))));
    if !(ps_err(db, ps) && s.len() > 0 && n.len() > 0) {
        let g = outer_sel(db, ps, d1);
        let p = product_rows(s, n);
        let k = keep(p, g);
        assert forall|i: int| 0 <= i < s.len() implies srow_ok(#[trigger] s[i]) by {}
        assert forall|j: int| 0 <= j < n.len() implies nrow_ok(#[trigger] n[j]) by {}
        lemma_product_rows_ok(s, n);
        lemma_keep_members(p, g);
        let out = k.map_values(|x: Row| proj_row(x));
        let prs = project_results(db, ctx, k, exprs);
        assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Row, SqlError>(out[i]) by {
            let j = choose|j: int| 0 <= j < p.len() && p[j] == k[i];
            assert(xrow_ok(p[j]));
            assert(ctx + k[i] =~= k[i]);
            lemma_proj_exprs(db, k[i]);
        }
        lemma_collect_all(prs, out);
        lemma_kept_product(db, ps, d1, s);
    }
}

} // verus!
