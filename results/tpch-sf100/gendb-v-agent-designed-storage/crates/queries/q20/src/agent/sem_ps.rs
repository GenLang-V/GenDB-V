//! The partsupp subquery `SELECT ps_suppkey FROM partsupp WHERE ps_partkey IN (..) AND ps_availqty > (..)` under an
//! outer row `x` (`supplier ++ nation`, 11 values), and `s_suppkey IN (subquery)`:
//! - `lemma_ps_pred`: on one partsupp row the WHERE is 22025 when the part LIKE fails, else true exactly for
//!   `nf::ps_qual`;
//! - `lemma_ps_q`: the subquery fails when the LIKE fails and partsupp has rows, else it lists `[ps_suppkey]` of the
//!   qualifying rows;
//! - `lemma_in_ps`: the IN condition is then the error, or two-valued `nf::sk_ok(s_suppkey)`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::link::join::*;
use crate::link::expr::*;
use crate::bridge::collect::lemma_collect_all;
use crate::link::capacity::lemma_collect_uniform_err;
use crate::exec::relational::domain::{filter_results, project_results};
use crate::query::param_domain;
use super::typed::*;
use super::nf::*;
use super::ast::*;
use super::sem_li::lemma_avail_pred;
use super::sem_part::{lemma_in_part, lemma_any_int, lemma_keep_has};

verus! {

/// The facts the subquery lemmas share.
pub open spec fn sem_ok(db: Database, ps: Seq<Literal>, d1: int) -> bool {
    &&& tables_ok(db)
    &&& lt(db).len() <= 0xffff_ffff_ffff_ffff
    &&& param_domain(ps)
    &&& d1_ok(ps, d1)
}

/// The qualifying partsupp rows.
pub open spec fn ps_sel(db: Database, ps: Seq<Literal>, d1: int) -> spec_fn(Row) -> bool {
    |r: Row| ps_qual(db, pat_of(ps), d0_of(ps), d1, r)
}

/// The WHERE on `x ++ r` for partsupp row `r`.
pub proof fn lemma_ps_pred(db: Database, x: Row, r: Row, ps: Seq<Literal>, d1: int)
    requires sem_ok(db, ps, d1), x.len() == 11, psrow_ok(r),
    ensures
        part_err(db, pat_of(ps)) ==> eval_pred(db, x + r, ps_pred(ps)) == Err::<Truth, SqlError>(SqlError::InvalidEscapeSequence),
        !part_err(db, pat_of(ps)) ==> eval_pred(db, x + r, ps_pred(ps)) is Ok
            && (eval_pred(db, x + r, ps_pred(ps))->Ok_0 is True) == ps_sel(db, ps, d1)(r),
{
    let env = x + r;
    assert(env.len() == 16 && env[11] == r[0] && env[12] == r[1] && env[13] == r[2]);
    lemma_in_part(db, env, ps);
    if !part_err(db, pat_of(ps)) {
        lemma_avail_pred(db, env, ps, d1);
    }
}

/// `keep_true` keeps the rows whose truth is `True`, whatever the other truths are.
pub proof fn lemma_keep_true_iff(rows: Seq<Row>, truths: Seq<Truth>, f: spec_fn(Row) -> bool)
    requires
        truths.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] truths[i] is True) == f(rows[i]),
    ensures keep_true(rows, truths) == keep(rows, f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < ri.len() implies (#[trigger] ti[i] is True) == f(ri[i]) by {
            assert(ti[i] == truths[i] && ri[i] == rows[i]);
        }
        lemma_keep_true_iff(ri, ti, f);
        assert(truths[rows.len() - 1] is True == f(rows[rows.len() - 1]));
    }
}

/// The subquery's WHERE over partsupp.
pub proof fn lemma_ps_filter(db: Database, x: Row, ps: Seq<Literal>, d1: int)
    requires sem_ok(db, ps, d1), x.len() == 11,
    ensures
        eval_query(db, x, ps_filter(ps)) == if pst(db).len() > 0 && part_err(db, pat_of(ps)) {
            Err::<Relation, SqlError>(SqlError::InvalidEscapeSequence)
        } else {
            Ok::<Relation, SqlError>(keep(pst(db), ps_sel(db, ps, d1)))
        },
{
    let p = pst(db);
    let pred = ps_pred(ps);
    let f = ps_sel(db, ps, d1);
    crate::exec::relational::domain::lemma_eval_filter(db, x, pred, Box::new(Query::Table(4)));
    assert(eval_query(db, x, Query::Table(4)) == Ok::<Relation, SqlError>(p));
    let rs = filter_results(db, x, p, pred);
    if part_err(db, pat_of(ps)) {
        if p.len() > 0 {
            assert forall|i: int| 0 <= i < rs.len()
                implies #[trigger] rs[i] is Ok || rs[i] == Err::<Truth, SqlError>(SqlError::InvalidEscapeSequence) by {
                assert(psrow_ok(p[i]));
                lemma_ps_pred(db, x, p[i], ps, d1);
            }
            assert(psrow_ok(p[0]));
            lemma_ps_pred(db, x, p[0], ps, d1);
            lemma_collect_uniform_err(rs, SqlError::InvalidEscapeSequence, 0);
        } else {
            lemma_collect_all(rs, Seq::<Truth>::empty());
            assert(keep_true(p, Seq::<Truth>::empty()) == Seq::<Row>::empty());
        }
    } else {
        let truths = Seq::new(p.len(), |i: int| eval_pred(db, x + p[i], pred)->Ok_0);
        assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(truths[i]) by {
            assert(psrow_ok(p[i]));
            lemma_ps_pred(db, x, p[i], ps, d1);
        }
        lemma_collect_all(rs, truths);
        assert forall|i: int| 0 <= i < p.len() implies (#[trigger] truths[i] is True) == f(p[i]) by {
            assert(psrow_ok(p[i]));
            lemma_ps_pred(db, x, p[i], ps, d1);
        }
        lemma_keep_true_iff(p, truths, f);
    }
}

/// `[ps_suppkey]` of a partsupp row.
pub open spec fn supp_row(r: Row) -> Row {
    seq![r[1]]
}

/// The subquery's rows when it succeeds.
pub open spec fn ps_rows(db: Database, ps: Seq<Literal>, d1: int) -> Seq<Row> {
    keep(pst(db), ps_sel(db, ps, d1)).map_values(|r: Row| supp_row(r))
}

/// The partsupp subquery.
pub proof fn lemma_ps_q(db: Database, x: Row, ps: Seq<Literal>, d1: int)
    requires sem_ok(db, ps, d1), x.len() == 11,
    ensures
        eval_query(db, x, ps_q(ps)) == if pst(db).len() > 0 && part_err(db, pat_of(ps)) {
            Err::<Relation, SqlError>(SqlError::InvalidEscapeSequence)
        } else {
            Ok::<Relation, SqlError>(ps_rows(db, ps, d1))
        },
{
    lemma_ps_filter(db, x, ps, d1);
    crate::exec::relational::domain::lemma_eval_project(db, x, seq![Expr::Col(12)], Box::new(ps_filter(ps)));
    if !(pst(db).len() > 0 && part_err(db, pat_of(ps))) {
        let ks = keep(pst(db), ps_sel(db, ps, d1));
        lemma_keep_members(pst(db), ps_sel(db, ps, d1));
        let out = ps_rows(db, ps, d1);
        let prs = project_results(db, x, ks, seq![Expr::Col(12)]);
        assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Row, SqlError>(out[i]) by {
            let m = choose|m: int| 0 <= m < pst(db).len() && pst(db)[m] == ks[i];
            assert(psrow_ok(pst(db)[m]));
            let env = x + ks[i];
            assert(env[12] == ks[i][1]);
            lemma_expr_col(db, env, 12);
            super::sem_li::lemma_one_expr(db, env, Expr::Col(12));
        }
        lemma_collect_all(prs, out);
    }
}

/// The subquery fails.
pub open spec fn ps_err(db: Database, ps: Seq<Literal>) -> bool {
    pst(db).len() > 0 && part_err(db, pat_of(ps))
}

/// `s_suppkey IN (subquery)` with `s_suppkey == x[0]`.
pub proof fn lemma_in_ps(db: Database, x: Row, ps: Seq<Literal>, d1: int)
    requires sem_ok(db, ps, d1), x.len() == 11, is_int(x[0]),
    ensures
        eval_pred(db, x, in_ps(ps)) == if ps_err(db, ps) {
            Err::<Truth, SqlError>(SqlError::InvalidEscapeSequence)
        } else {
            Ok::<Truth, SqlError>(truth_of(sk_ok(db, pat_of(ps), d0_of(ps), d1, ival(x[0]))))
        },
{
    let s = ival(x[0]);
    let (pat, d0) = (pat_of(ps), d0_of(ps));
    lemma_expr_col(db, x, 0);
    lemma_ps_q(db, x, ps, d1);
    if !ps_err(db, ps) {
        let f = ps_sel(db, ps, d1);
        let ks = keep(pst(db), f);
        let rows = ps_rows(db, ps, d1);
        lemma_keep_members(pst(db), f);
        assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] rows[i]).len() == 1 && is_int(rows[i][0]) by {
            let m = choose|m: int| 0 <= m < pst(db).len() && pst(db)[m] == ks[i];
            assert(psrow_ok(pst(db)[m]));
        }
        lemma_any_int(s, rows);
        let a = exists|i: int| 0 <= i < rows.len() && #[trigger] rows[i][0] == Val::Int(s);
        if a {
            let i = choose|i: int| 0 <= i < rows.len() && #[trigger] rows[i][0] == Val::Int(s);
            let m = choose|m: int| 0 <= m < pst(db).len() && pst(db)[m] == ks[i];
            assert(f(ks[i]));
            assert(ps_qual(db, pat, d0, d1, pst(db)[m]));
            assert(sk_ok(db, pat, d0, d1, s));
        }
        if sk_ok(db, pat, d0, d1, s) {
            let j = choose|j: int| 0 <= j < pst(db).len() && #[trigger] ps_qual(db, pat, d0, d1, pst(db)[j])
                && pst(db)[j][1] == Val::Int(s);
            assert(f(pst(db)[j]));
            lemma_keep_has(pst(db), f, j);
            let i = choose|i: int| 0 <= i < ks.len() && ks[i] == pst(db)[j];
            assert(rows[i][0] == Val::Int(s));
        }
    }
}

} // verus!
