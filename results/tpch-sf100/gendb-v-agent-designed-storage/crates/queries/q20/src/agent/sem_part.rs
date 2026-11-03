//! The part subquery `ps_partkey IN (SELECT p_partkey FROM part WHERE p_name LIKE $1)` under a context `c` of 16
//! values (`supplier ++ nation ++ partsupp`):
//! - `lemma_part_q`: the subquery fails with 22025 when some part name makes the LIKE fail (`nf::part_err`), else
//!   it lists `[p_partkey]` of the matching part rows;
//! - `lemma_in_part`: the IN condition is then the error, or two-valued `nf::part_hit(ps_partkey)`.
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
use crate::query::param_domain;
use super::typed::*;
use super::nf::*;
use super::ast::*;
use super::common::likeprefix::lemma_like_value_err;

verus! {

/// `$1` is the text literal of the pattern.
pub proof fn lemma_pat_lit(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures ps[0] == Literal::Text(pat_of(ps)), lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Text(pat_of(ps))),
{
    assert(crate::query::param_typed(ps));
}

/// The LIKE's arguments on `c ++ p`.
proof fn lemma_like_args(db: Database, env: Row, l0: Literal, pat: Seq<u8>)
    requires env.len() == 25, l0 == Literal::Text(pat),
    ensures
        eval_exprs(db, env, seq![Expr::Col(17), Expr::Lit(l0), Expr::Lit(Literal::Text(seq![92u8]))])
            == Ok::<Row, SqlError>(seq![env[17], Val::Text(pat), Val::Text(seq![92u8])]),
{
    hide(eval_expr);
    let (e0, e1, e2) = (Expr::Col(17), Expr::Lit(l0), Expr::Lit(Literal::Text(seq![92u8])));
    let (v0, v1, v2) = (env[17], Val::Text(pat), Val::Text(seq![92u8]));
    lemma_expr_col(db, env, 17);
    lemma_expr_text(db, env, seq![92u8]);
    lemma_expr_text(db, env, pat);
    let a3 = seq![e0, e1, e2];
    let a2 = seq![e0, e1];
    let a1 = seq![e0];
    assert(a3.drop_last() =~= a2 && a3.last() == e2);
    assert(a2.drop_last() =~= a1 && a2.last() == e1);
    assert(a1.drop_last() =~= Seq::<Expr>::empty() && a1.last() == e0);
    lemma_eval_exprs_empty(db, env);
    lemma_eval_exprs_step(db, env, a1);
    lemma_eval_exprs_step(db, env, a2);
    lemma_eval_exprs_step(db, env, a3);
    assert(Seq::<Val>::empty().push(v0).push(v1).push(v2) =~= seq![v0, v1, v2]);
}

/// `p_name LIKE $1` on `c ++ p`.
pub proof fn lemma_like_expr(db: Database, c: Row, p: Row, ps: Seq<Literal>)
    requires c.len() == 16, prow_ok(p), param_domain(ps),
    ensures eval_expr(db, c + p, like_expr(ps)) == like_of(tval(p[1]), pat_of(ps)),
{
    hide(crate::spec::fns::like::like_value);
    let env = c + p;
    assert(env[17] == p[1]);
    lemma_pat_lit(ps);
    lemma_like_args(db, env, ps[0], pat_of(ps));
}

/// The WHERE of the part subquery on part row `p`: the LIKE's error, or its truth.
pub open spec fn like_truth(t: Seq<u8>, pat: Seq<u8>) -> Result<Truth, SqlError> {
    match like_of(t, pat) {
        Err(e) => Err(e),
        Ok(v) => Ok(truth_of(v == Val::Bool(true))),
    }
}

pub proof fn lemma_part_pred(db: Database, c: Row, p: Row, ps: Seq<Literal>)
    requires c.len() == 16, prow_ok(p), param_domain(ps),
    ensures
        eval_pred(db, c + p, Pred::OfBool(like_expr(ps))) == like_truth(tval(p[1]), pat_of(ps)),
        like_truth(tval(p[1]), pat_of(ps)) is Err
            ==> like_truth(tval(p[1]), pat_of(ps)) == Err::<Truth, SqlError>(SqlError::InvalidEscapeSequence),
{
    lemma_like_expr(db, c, p, ps);
    lemma_like_value_err(tval(p[1]), pat_of(ps));
}

/// The matching part rows.
pub open spec fn part_sel(pat: Seq<u8>) -> spec_fn(Row) -> bool {
    |r: Row| like_hit(tval(r[1]), pat)
}

/// `[p_partkey]` of a part row.
pub open spec fn key_row(r: Row) -> Row {
    seq![r[0]]
}

/// The subquery's rows when no LIKE fails.
pub open spec fn part_rows(db: Database, pat: Seq<u8>) -> Seq<Row> {
    keep(pt(db), part_sel(pat)).map_values(|r: Row| key_row(r))
}

/// The WHERE: the first error (always 22025), else the matching rows.
pub proof fn lemma_part_filter(db: Database, c: Row, ps: Seq<Literal>)
    requires tables_ok(db), c.len() == 16, param_domain(ps),
    ensures
        eval_query(db, c, part_filter(ps)) == if part_err(db, pat_of(ps)) {
            Err::<Relation, SqlError>(SqlError::InvalidEscapeSequence)
        } else {
            Ok::<Relation, SqlError>(keep(pt(db), part_sel(pat_of(ps))))
        },
{
    let p = pt(db);
    let pat = pat_of(ps);
    let pred = Pred::OfBool(like_expr(ps));
    crate::exec::relational::domain::lemma_eval_filter(db, c, pred, Box::new(Query::Table(3)));
    assert(eval_query(db, c, Query::Table(3)) == Ok::<Relation, SqlError>(p));
    let rs = filter_results(db, c, p, pred);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == like_truth(tval(p[i][1]), pat)
        && (rs[i] is Ok || rs[i] == Err::<Truth, SqlError>(SqlError::InvalidEscapeSequence)) by {
        assert(prow_ok(p[i]));
        lemma_part_pred(db, c, p[i], ps);
    }
    if part_err(db, pat) {
        let i = choose|i: int| 0 <= i < p.len() && #[trigger] like_of(tval(p[i][1]), pat) is Err;
        assert(rs[i] == like_truth(tval(p[i][1]), pat));
        lemma_collect_uniform_err(rs, SqlError::InvalidEscapeSequence, i);
    } else {
        let f = part_sel(pat);
        let truths = Seq::new(p.len(), |i: int| truth_of(f(p[i])));
        assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(truths[i]) by {
            assert(rs[i] == like_truth(tval(p[i][1]), pat));
            assert(!(like_of(tval(p[i][1]), pat) is Err));
        }
        lemma_collect_all(rs, truths);
        lemma_keep_true_keep(p, truths, f);
    }
}

/// The subquery: the error, or `[p_partkey]` of the matching rows.
pub proof fn lemma_part_q(db: Database, c: Row, ps: Seq<Literal>)
    requires tables_ok(db), c.len() == 16, param_domain(ps),
    ensures
        eval_query(db, c, part_q(ps)) == if part_err(db, pat_of(ps)) {
            Err::<Relation, SqlError>(SqlError::InvalidEscapeSequence)
        } else {
            Ok::<Relation, SqlError>(part_rows(db, pat_of(ps)))
        },
{
    lemma_part_filter(db, c, ps);
    crate::exec::relational::domain::lemma_eval_project(db, c, seq![Expr::Col(16)], Box::new(part_filter(ps)));
    if !part_err(db, pat_of(ps)) {
        let ks = keep(pt(db), part_sel(pat_of(ps)));
        lemma_keep_members(pt(db), part_sel(pat_of(ps)));
        let out = part_rows(db, pat_of(ps));
        let prs = project_results(db, c, ks, seq![Expr::Col(16)]);
        assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Row, SqlError>(out[i]) by {
            let m = choose|m: int| 0 <= m < pt(db).len() && pt(db)[m] == ks[i];
            assert(prow_ok(pt(db)[m]));
            let env = c + ks[i];
            assert(env[16] == ks[i][0]);
            lemma_expr_col(db, env, 16);
            super::sem_li::lemma_one_expr(db, env, Expr::Col(16));
        }
        lemma_collect_all(prs, out);
    }
}

/// `Int(k) = ANY (rows)` over one-column bigint rows: two-valued membership.
pub proof fn lemma_any_int(k: int, rows: Seq<Row>)
    requires forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() == 1 && is_int(rows[i][0]),
    ensures
        any_cmp_truth(CmpOp::Eq, Val::Int(k), rows)
            == Ok::<Truth, SqlError>(truth_of(exists|i: int| 0 <= i < rows.len() && #[trigger] rows[i][0] == Val::Int(k))),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let d = rows.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]).len() == 1 && is_int(d[i][0]) by {
            assert(d[i] == rows[i]);
        }
        lemma_any_int(k, d);
        let x = rows.last()[0];
        assert(is_int(rows[rows.len() - 1][0]));
        assert(first_col(rows.last()) == Ok::<Val, SqlError>(x));
        lemma_compare_int(k, ival(x));
        lemma_cmp_holds_sign(CmpOp::Eq, k, ival(x));
        assert(cmp_truth(CmpOp::Eq, Val::Int(k), x) == Ok::<Truth, SqlError>(truth_of(x == Val::Int(k))));
        let a = exists|i: int| 0 <= i < d.len() && #[trigger] d[i][0] == Val::Int(k);
        let b = exists|i: int| 0 <= i < rows.len() && #[trigger] rows[i][0] == Val::Int(k);
        if a {
            let i = choose|i: int| 0 <= i < d.len() && #[trigger] d[i][0] == Val::Int(k);
            assert(rows[i] == d[i]);
        }
        if b && !(x == Val::Int(k)) {
            let i = choose|i: int| 0 <= i < rows.len() && #[trigger] rows[i][0] == Val::Int(k);
            assert(i < d.len());
            assert(d[i] == rows[i]);
        }
        if x == Val::Int(k) {
            assert(rows[rows.len() - 1][0] == Val::Int(k));
        }
    }
}

/// A row satisfying the condition is kept.
pub proof fn lemma_keep_has(rows: Seq<Row>, f: spec_fn(Row) -> bool, j: int)
    requires 0 <= j < rows.len(), f(rows[j]),
    ensures keep(rows, f).contains(rows[j]),
    decreases rows.len(),
{
    let d = rows.drop_last();
    if j == rows.len() - 1 {
        assert(keep(rows, f) == keep(d, f).push(rows[j]));
        assert(keep(rows, f)[keep(d, f).len() as int] == rows[j]);
    } else {
        assert(d[j] == rows[j]);
        lemma_keep_has(d, f, j);
        let m = choose|m: int| 0 <= m < keep(d, f).len() && keep(d, f)[m] == rows[j];
        if f(rows.last()) {
            assert(keep(rows, f)[m] == rows[j]);
        }
    }
}

/// `ps_partkey IN (subquery)` with `ps_partkey == c[11]`: the error, or two-valued `part_hit`.
pub proof fn lemma_in_part(db: Database, c: Row, ps: Seq<Literal>)
    requires tables_ok(db), c.len() == 16, is_int(c[11]), param_domain(ps),
    ensures
        eval_pred(db, c, in_part(ps)) == if part_err(db, pat_of(ps)) {
            Err::<Truth, SqlError>(SqlError::InvalidEscapeSequence)
        } else {
            Ok::<Truth, SqlError>(truth_of(part_hit(db, pat_of(ps), ival(c[11]))))
        },
{
    let pat = pat_of(ps);
    let k = ival(c[11]);
    lemma_expr_col(db, c, 11);
    lemma_part_q(db, c, ps);
    if !part_err(db, pat) {
        let f = part_sel(pat);
        let ks = keep(pt(db), f);
        let rows = part_rows(db, pat);
        lemma_keep_members(pt(db), f);
        assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] rows[i]).len() == 1 && is_int(rows[i][0]) by {
            let m = choose|m: int| 0 <= m < pt(db).len() && pt(db)[m] == ks[i];
            assert(prow_ok(pt(db)[m]));
        }
        lemma_any_int(k, rows);
        let a = exists|i: int| 0 <= i < rows.len() && #[trigger] rows[i][0] == Val::Int(k);
        if a {
            let i = choose|i: int| 0 <= i < rows.len() && #[trigger] rows[i][0] == Val::Int(k);
            let m = choose|m: int| 0 <= m < pt(db).len() && pt(db)[m] == ks[i];
            assert(f(ks[i]));
            assert(like_hit(tval(pt(db)[m][1]), pat));
            assert(part_hit(db, pat, k));
        }
        if part_hit(db, pat, k) {
            let j = choose|j: int| 0 <= j < pt(db).len() && pt(db)[j][0] == Val::Int(k)
                && #[trigger] like_hit(tval(pt(db)[j][1]), pat);
            lemma_keep_has(pt(db), f, j);
            let i = choose|i: int| 0 <= i < ks.len() && ks[i] == pt(db)[j];
            assert(rows[i][0] == Val::Int(k));
        }
    }
}

} // verus!
