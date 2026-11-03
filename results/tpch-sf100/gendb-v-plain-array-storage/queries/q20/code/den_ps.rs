//! `s_suppkey IN (SELECT ps_suppkey FROM partsupp WHERE ps_partkey IN (..) AND ps_availqty > (..))`, evaluated with
//! an 11-value outer row whose `s_suppkey` (position 0) is `v`:
//!
//! - on partsupp row `q` (context: the outer row and the partsupp row, 16 values) `ps_availqty > (li_sub)` compares
//!   `ps_availqty` (scale 0) with `5 * lsum` (scale 3): `Unknown` without lineitem hits, else whether
//!   `200 * ps_availqty > lsum` (`lemma_gt_pred`); with the IN condition the WHERE is `True` exactly when the row
//!   qualifies (`lemma_ps_pred`), so it keeps the rows of `ps_f` (`lemma_ps_filter`);
//! - the subquery's rows are `[ps_suppkey]` of those rows (`lemma_ps_sub`) and the outer IN condition is
//!   `in_supp(v)` (`lemma_in_supp_pred`), when no `LIKE` raises or partsupp is empty;
//! - otherwise (some `LIKE` raises, partsupp non-empty) the IN condition is the error 22025 (`lemma_in_supp_pred_err`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::gendb_entry::stores::StoresView;
use crate::query::param_domain;
use crate::exec::relational::domain::*;
use crate::link::join::{keep, lemma_keep_members};
use crate::link::expr::{ival, lemma_compare_num, lemma_align_same, lemma_align_by};
use crate::link::capacity::{lemma_filter_err, lemma_first_input};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_ok};
use crate::stores::flat_partsupp::interface as psi;
use crate::agent::tables::*;
use crate::agent::ast::*;
use crate::agent::params::*;
use crate::agent::normal::*;
use crate::agent::den_li::*;
use crate::agent::den_part::*;
use crate::agent::common::rows::*;

verus! {

/// Partsupp row `q` as the evaluator sees it: arity and the three integer columns.
pub proof fn lemma_ps_row(sv: StoresView, q: int)
    requires stores_wf(sv), 0 <= q < n_ps(sv),
    ensures ({
        let r = ps_rows(sv)[q];
        &&& r == psi::row_at(sv.flat_partsupp, q)
        &&& r.len() == 5
        &&& r[0] == Val::Int(pspk(sv)[q] as int)
        &&& r[1] == Val::Int(pssk(sv)[q] as int)
        &&& r[2] == Val::Int(psaq(sv)[q] as int)
    }),
{
}

/// The truth of `ps_availqty > (li_sub)` for the key pair `(a, b)` and availability `aq`.
pub open spec fn gt_truth(sv: StoresView, lo: int, hi: int, a: int, b: int, aq: int) -> Truth {
    if lcnt(sv, lo, hi, a, b) == 0 { Truth::Unknown } else { truth_of(200 * aq > lsum(sv, lo, hi, a, b)) }
}

/// `aq` at scale 0 against `5 * s` at scale 3: the order of `1000 * aq` and `5 * s`.
proof fn lemma_compare_gt(aq: int, s: int)
    ensures compare(Val::Num { coeff: aq, scale: 0 }, Val::Num { coeff: 5 * s, scale: 3 }) == Some(sign(1000 * aq - 5 * s)),
{
    lemma_compare_num(aq, 0, 5 * s, 3);
    assert(max_nat(0, 3) == 3);
    assert(pow10(3) == 1000) by (compute);
    lemma_align_by(aq, 0, 3, 1000);
    lemma_align_same(5 * s, 3);
}

/// `ps_availqty > (li_sub)` on the context of a partsupp row.
pub proof fn lemma_gt_pred(db: Database, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, env: Row, a: int, b: int, aq: int)
    requires
        tables_of(sv, db), model_ok(sv), sizes_ok(sv), win_ok(ps, lo, hi),
        env.len() == 16, env[11] == Val::Int(a), env[12] == Val::Int(b), env[13] == Val::Int(aq),
    ensures eval_pred(db, env, ps_gt_pred(ps[1])) == Ok::<Truth, SqlError>(gt_truth(sv, lo, hi, a, b, aq)),
{
    hide(eval_query);
    let sub = Expr::Subquery(Box::new(li_sub(ps[1])));
    assert(eval_expr(db, env, Expr::Col(13)) == Ok::<Val, SqlError>(Val::Int(aq)));
    assert(eval_expr(db, env, aq_cast()) == Ok::<Val, SqlError>(Val::Num { coeff: aq, scale: 0 }));
    lemma_li_value(db, sv, ps, lo, hi, env, a, b);
    let v = li_val(sv, lo, hi, a, b);
    assert(eval_expr(db, env, sub) == Ok::<Val, SqlError>(v));
    if lcnt(sv, lo, hi, a, b) == 0 {
        assert(v == Val::Null);
        assert(cmp_truth(CmpOp::Gt, Val::Num { coeff: aq, scale: 0 }, v) == Ok::<Truth, SqlError>(Truth::Unknown));
    } else {
        let s = lsum(sv, lo, hi, a, b);
        assert(v == Val::Num { coeff: 5 * s, scale: 3 });
        lemma_compare_gt(aq, s);
        assert((sign(1000 * aq - 5 * s) > 0) == (200 * aq > s));
        assert(cmp_truth(CmpOp::Gt, Val::Num { coeff: aq, scale: 0 }, v) == Ok::<Truth, SqlError>(truth_of(200 * aq > s)));
    }
}

/// The partsupp WHERE on row `q` (context: the outer row `x` and the row), when no `LIKE` raises: `True` exactly
/// when the row qualifies.
pub proof fn lemma_ps_pred(db: Database, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, x: Row, q: int)
    requires
        tables_of(sv, db), model_ok(sv), sizes_ok(sv), param_domain(ps), win_ok(ps, lo, hi), likes_ok(sv, ps),
        x.len() == 11, 0 <= q < n_ps(sv),
    ensures ({
        let r = eval_pred(db, x + ps_rows(sv)[q], ps_pred(ps));
        &&& r is Ok
        &&& (r->Ok_0 is True) == ps_f(sv, ps, lo, hi)(ps_rows(sv)[q])
    }),
{
    hide(eval_query);
    let row = ps_rows(sv)[q];
    lemma_ps_row(sv, q);
    let env = x + row;
    let (a, b, aq) = (pspk(sv)[q] as int, pssk(sv)[q] as int, psaq(sv)[q] as int);
    assert(env[11] == row[0] && env[12] == row[1] && env[13] == row[2]);
    lemma_in_part_pred(db, sv, ps, env, a);
    lemma_gt_pred(db, sv, ps, lo, hi, env, a, b, aq);
    let t1 = truth_of(in_part(sv, ps, a));
    let t2 = gt_truth(sv, lo, hi, a, b, aq);
    assert(eval_pred(db, env, ps_pred(ps)) == Ok::<Truth, SqlError>(truth_and(t1, t2)));
    assert(ival(row[0]) == a && ival(row[1]) == b && ival(row[2]) == aq);
    lemma_ltotals_bounds(sv, lo, hi, a, b);
    assert(ps_f(sv, ps, lo, hi)(row) == ps_cond(sv, ps, lo, hi, a, b, aq));
    assert((truth_and(t1, t2) is True) == ps_cond(sv, ps, lo, hi, a, b, aq));
}

/// The partsupp WHERE on row `q` when some `LIKE` raises: the error 22025.
proof fn lemma_ps_pred_err(db: Database, sv: StoresView, ps: Seq<Literal>, x: Row, q: int)
    requires tables_of(sv, db), stores_wf(sv), param_domain(ps), !likes_ok(sv, ps), x.len() == 11, 0 <= q < n_ps(sv),
    ensures eval_pred(db, x + ps_rows(sv)[q], ps_pred(ps)) == Err::<Truth, SqlError>(SqlError::InvalidEscapeSequence),
{
    hide(eval_query);
    lemma_ps_row(sv, q);
    lemma_in_part_pred_err(db, sv, ps, x + ps_rows(sv)[q]);
}

/// The partsupp WHERE under an outer row: the qualifying rows (when no `LIKE` raises or partsupp is empty).
pub proof fn lemma_ps_filter(db: Database, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, x: Row)
    requires
        tables_of(sv, db), model_ok(sv), sizes_ok(sv), param_domain(ps), win_ok(ps, lo, hi),
        likes_ok(sv, ps) || n_ps(sv) == 0, x.len() == 11,
    ensures eval_query(db, x, ps_filter(ps)) == Ok::<Relation, SqlError>(keep(ps_rows(sv), ps_f(sv, ps, lo, hi))),
{
    let rows = ps_rows(sv);
    let f = ps_f(sv, ps, lo, hi);
    let pred = ps_pred(ps);
    assert(eval_query(db, x, Query::Table(4)) == Ok::<Relation, SqlError>(rows));
    lemma_eval_filter(db, x, pred, Box::new(Query::Table(4)));
    let prs = filter_results(db, x, rows, pred);
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] is Ok by {
        lemma_ps_pred(db, sv, ps, lo, hi, x, i);
    }
    lemma_collect_ok(prs);
    let truths = collect(prs)->Ok_0;
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] truths[i] is True) == f(rows[i]) by {
        lemma_ps_pred(db, sv, ps, lo, hi, x, i);
        assert(prs[i] == Ok::<Truth, SqlError>(truths[i]));
    }
    lemma_keep_true_is(rows, truths, f);
}

/// The subquery's rows: `[ps_suppkey]` of every qualifying partsupp row.
pub open spec fn ps_out(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int) -> Seq<Row> {
    keep(ps_rows(sv), ps_f(sv, ps, lo, hi)).map_values(|r: Row| seq![r[1]])
}

/// The partsupp subquery under an outer row (when no `LIKE` raises or partsupp is empty).
pub proof fn lemma_ps_sub(db: Database, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, x: Row)
    requires
        tables_of(sv, db), model_ok(sv), sizes_ok(sv), param_domain(ps), win_ok(ps, lo, hi),
        likes_ok(sv, ps) || n_ps(sv) == 0, x.len() == 11,
    ensures eval_query(db, x, ps_sub(ps)) == Ok::<Relation, SqlError>(ps_out(sv, ps, lo, hi)),
{
    let rows = ps_rows(sv);
    let f = ps_f(sv, ps, lo, hi);
    let kept = keep(rows, f);
    lemma_ps_filter(db, sv, ps, lo, hi, x);
    let es = seq![Expr::Col(12)];
    lemma_eval_project(db, x, es, Box::new(ps_filter(ps)));
    let pr = project_results(db, x, kept, es);
    let out = ps_out(sv, ps, lo, hi);
    lemma_keep_members(rows, f);
    assert forall|t: int| 0 <= t < pr.len() implies #[trigger] pr[t] == Ok::<Row, SqlError>(out[t]) by {
        assert(rows.contains(kept[t]));
        let q = choose|q: int| 0 <= q < rows.len() && rows[q] == kept[t];
        lemma_ps_row(sv, q);
        let e = x + kept[t];
        assert(e[12] == kept[t][1]);
        let er = expr_results(db, e, es);
        lemma_expr_results_index(db, e, es);
        lemma_collect_all(er, seq![kept[t][1]]);
    }
    lemma_collect_all(pr, out);
}

/// `s_suppkey IN (ps_sub)` on an outer row whose `s_suppkey` is `v` (when no `LIKE` raises or partsupp is empty):
/// `in_supp(v)`.
pub proof fn lemma_in_supp_pred(db: Database, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, x: Row, v: int)
    requires
        tables_of(sv, db), model_ok(sv), sizes_ok(sv), param_domain(ps), win_ok(ps, lo, hi),
        likes_ok(sv, ps) || n_ps(sv) == 0, x.len() == 11, x[0] == Val::Int(v),
    ensures eval_pred(db, x, out_in_pred(ps)) == Ok::<Truth, SqlError>(truth_of(in_supp(sv, ps, lo, hi, v))),
{
    let rows = ps_rows(sv);
    let f = ps_f(sv, ps, lo, hi);
    let kept = keep(rows, f);
    let out = ps_out(sv, ps, lo, hi);
    lemma_ps_sub(db, sv, ps, lo, hi, x);
    assert(eval_expr(db, x, Expr::Col(0)) == Ok::<Val, SqlError>(Val::Int(v)));
    lemma_keep_members(rows, f);
    assert forall|t: int| 0 <= t < out.len() implies exists|w: int| #[trigger] out[t] == seq![Val::Int(w)] by {
        assert(rows.contains(kept[t]));
        let q = choose|q: int| 0 <= q < rows.len() && rows[q] == kept[t];
        lemma_ps_row(sv, q);
        assert(out[t] == seq![Val::Int(pssk(sv)[q] as int)]);
    }
    lemma_any_eq(v, out);
    let ex = exists|t: int| 0 <= t < out.len() && #[trigger] out[t] == seq![Val::Int(v)];
    if ex {
        let t = choose|t: int| 0 <= t < out.len() && #[trigger] out[t] == seq![Val::Int(v)];
        assert(rows.contains(kept[t]));
        let q = choose|q: int| 0 <= q < rows.len() && rows[q] == kept[t];
        lemma_ps_row(sv, q);
        assert(out[t] == seq![kept[t][1]]);
        assert(seq![kept[t][1]][0] == seq![Val::Int(v)][0]);
        assert(pssk(sv)[q] as int == v);
        assert(f(kept[t]));
        assert(ps_ok(sv, ps, lo, hi, q));
        assert(in_supp(sv, ps, lo, hi, v));
    }
    if in_supp(sv, ps, lo, hi, v) {
        let q = choose|q: int| 0 <= q < n_ps(sv) && #[trigger] ps_ok(sv, ps, lo, hi, q) && pssk(sv)[q] as int == v;
        lemma_ps_row(sv, q);
        assert(f(rows[q]));
        lemma_keep_has(rows, f, q);
        let t = choose|t: int| 0 <= t < kept.len() && kept[t] == rows[q];
        assert(out[t] == seq![kept[t][1]]);
        assert(out[t] =~= seq![Val::Int(v)]);
    }
}

/// `s_suppkey IN (ps_sub)` when some `LIKE` raises and partsupp is non-empty: the error 22025.
pub proof fn lemma_in_supp_pred_err(db: Database, sv: StoresView, ps: Seq<Literal>, x: Row)
    requires tables_of(sv, db), stores_wf(sv), param_domain(ps), !likes_ok(sv, ps), n_ps(sv) > 0, x.len() == 11,
    ensures eval_pred(db, x, out_in_pred(ps)) == Err::<Truth, SqlError>(SqlError::InvalidEscapeSequence),
{
    let e = SqlError::InvalidEscapeSequence;
    let rows = ps_rows(sv);
    let pred = ps_pred(ps);
    assert(eval_query(db, x, Query::Table(4)) == Ok::<Relation, SqlError>(rows));
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, x + rows[k], pred) is Ok
        || eval_pred(db, x + rows[k], pred) == Err::<Truth, SqlError>(e) by {
        lemma_ps_pred_err(db, sv, ps, x, k);
    }
    lemma_ps_pred_err(db, sv, ps, x, 0);
    lemma_filter_err(db, x, pred, Box::new(Query::Table(4)), rows, e, 0);
    lemma_first_input(db, x, ps_sub(ps));
    assert(eval_query(db, x, ps_sub(ps)) == Err::<Relation, SqlError>(e));
    assert(eval_expr(db, x, Expr::Col(0)) == Ok::<Val, SqlError>(x[0]));
}

} // verus!
