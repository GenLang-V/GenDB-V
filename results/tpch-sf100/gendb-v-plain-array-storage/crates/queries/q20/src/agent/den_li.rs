//! The correlated subquery `SELECT 0.5 * SUM(l_quantity) FROM lineitem WHERE l_partkey = ps_partkey AND l_suppkey =
//! ps_suppkey AND l_shipdate >= $2 AND l_shipdate < $2 + INTERVAL '1' YEAR`, evaluated with a 16-value context whose
//! `ps_partkey` (position 11) is `a` and `ps_suppkey` (12) is `b`:
//!
//! - its WHERE keeps the lineitem rows with keys `(a, b)` and shipdate in the window (`lemma_li_filter`);
//! - their quantities are numeric(15,2) values: `lcnt` of them, summing to the coefficient `lsum` at scale 2
//!   (`lemma_li_kept`), far inside PostgreSQL's numeric range;
//! - SUM is NULL without rows, else `lsum` at scale 2; `0.5 * SUM` is `5 * lsum` at scale 3 (`li_val`). No step
//!   fails, so the subquery's value is `li_val` (`lemma_li_value`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::source_check::date32_val;
use crate::exec::relational::domain::*;
use crate::link::join::{keep, sum_of, lemma_keep_true_keep, lemma_keep_members, lemma_sum_of_keep, lemma_sum_of_ext};
use crate::link::expr::{ival, lemma_pred_cmp, lemma_compare_int, lemma_align_same, lemma_pred_and};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::stores::flat_lineitem::interface as li;
use crate::agent::tables::*;
use crate::agent::ast::*;
use crate::agent::params::*;
use crate::agent::normal::*;
use crate::agent::common::selection::*;

verus! {

/// The row count fits a machine word (the stored parts are machine arrays).
pub open spec fn sizes_ok(sv: StoresView) -> bool { n_l(sv) <= usize::MAX as int }

/// `10^15 * 2^64`, a bound of every quantity sum.
pub open spec fn sum_bound() -> int { 18_446_744_073_709_551_616_000_000_000_000_000 }

/// The subquery's value for the key pair `(a, b)`: `0.5 * SUM`, or NULL without rows.
pub open spec fn li_val(sv: StoresView, lo: int, hi: int, a: int, b: int) -> Val {
    if lcnt(sv, lo, hi, a, b) == 0 { Val::Null } else { Val::Num { coeff: 5 * lsum(sv, lo, hi, a, b), scale: 3 } }
}

/// SUM over the pair's rows: NULL without rows.
pub open spec fn sum_val(sv: StoresView, lo: int, hi: int, a: int, b: int) -> Val {
    if lcnt(sv, lo, hi, a, b) == 0 { Val::Null } else { Val::Num { coeff: lsum(sv, lo, hi, a, b), scale: 2 } }
}

// ------------------------------------------------------------------------------------------------ bounds

/// Range sums of the pair's terms: the count is in `[0, hi - lo]` and the quantity sum is bounded by the count.
pub proof fn lemma_lterm_bounds(sv: StoresView, lo: int, hi: int, a: int, b: int, x: int, y: int)
    requires x <= y, 0 <= x, y <= n_l(sv), domains_ok(sv),
    ensures
        0 <= range_sum(x, y, lcnt_term(sv, lo, hi, a, b)) <= y - x,
        -999_999_999_999_999 * range_sum(x, y, lcnt_term(sv, lo, hi, a, b)) <= range_sum(x, y, lsum_term(sv, lo, hi, a, b))
            <= 999_999_999_999_999 * range_sum(x, y, lcnt_term(sv, lo, hi, a, b)),
    decreases y - x,
{
    if y > x {
        lemma_lterm_bounds(sv, lo, hi, a, b, x, y - 1);
        assert(num15(lqt(sv)[y - 1]));
    }
}

/// The totals of every pair are bounded: at most `n_l` rows, `|lsum| <= lcnt * (10^15 - 1)`, inside `i128`.
pub proof fn lemma_ltotals_bounds(sv: StoresView, lo: int, hi: int, a: int, b: int)
    requires domains_ok(sv), sizes_ok(sv),
    ensures
        0 <= lcnt(sv, lo, hi, a, b) <= n_l(sv),
        -999_999_999_999_999 * lcnt(sv, lo, hi, a, b) <= lsum(sv, lo, hi, a, b) <= 999_999_999_999_999 * lcnt(sv, lo, hi, a, b),
        -sum_bound() < lsum(sv, lo, hi, a, b) < sum_bound(),
{
    lemma_lterm_bounds(sv, lo, hi, a, b, 0, n_l(sv) as int);
    let c = lcnt(sv, lo, hi, a, b);
    assert(999_999_999_999_999 * c < sum_bound()) by (nonlinear_arith)
        requires 0 <= c <= 0xffff_ffff_ffff_ffff;
}

// ------------------------------------------------------------------------------------------------ the inner rows

/// The inner condition on a lineitem row: keys `(a, b)`, shipdate (position 10) in the window.
pub open spec fn lf(lo: int, hi: int, a: int, b: int) -> spec_fn(Row) -> bool {
    |r: Row| r[1] == Val::Int(a) && r[2] == Val::Int(b) && lo <= ival(r[10]) + 10957 && ival(r[10]) + 10957 < hi
}

/// Lineitem row `l` as the evaluator sees it: arity, keys, quantity, shipdate.
pub proof fn lemma_line_row(sv: StoresView, l: int)
    requires stores_wf(sv), 0 <= l < n_l(sv),
    ensures ({
        let r = line_rows(sv)[l];
        &&& r == li::row_at(sv.flat_lineitem, l)
        &&& r.len() == 16
        &&& r[1] == Val::Int(lpk(sv)[l] as int)
        &&& r[2] == Val::Int(lsk(sv)[l] as int)
        &&& r[4] == Val::Num { coeff: lqt(sv)[l] as int, scale: 2 }
        &&& r[10] == Val::Date(lsd(sv)[l] as int - 10957)
    }),
{
    assert(date32_val(lsd(sv)[l]) == Val::Date(lsd(sv)[l] as int - 10957));
}

/// The inner condition holds on lineitem row `l` exactly when it is a hit of the pair.
pub proof fn lemma_lf_row(sv: StoresView, lo: int, hi: int, a: int, b: int, l: int)
    requires stores_wf(sv), 0 <= l < n_l(sv),
    ensures lf(lo, hi, a, b)(line_rows(sv)[l]) == lhit(sv, lo, hi, a, b, l),
{
    lemma_line_row(sv, l);
}

/// The inner WHERE on one row.
proof fn lemma_li_pred_row(db: Database, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, ctx: Row, a: int, b: int, l: int)
    requires
        stores_wf(sv), win_ok(ps, lo, hi), 0 <= l < n_l(sv),
        ctx.len() == 16, ctx[11] == Val::Int(a), ctx[12] == Val::Int(b),
    ensures eval_pred(db, ctx + line_rows(sv)[l], li_pred(ps[1])) == Ok::<Truth, SqlError>(truth_of(lf(lo, hi, a, b)(line_rows(sv)[l]))),
{
    let r = line_rows(sv)[l];
    lemma_line_row(sv, l);
    let e = ctx + r;
    let (k, s, d) = (lpk(sv)[l] as int, lsk(sv)[l] as int, lsd(sv)[l] as int);
    assert(e[17] == r[1] && e[18] == r[2] && e[26] == r[10] && e[11] == ctx[11] && e[12] == ctx[12]);
    assert(eval_expr(db, e, Expr::Col(17)) == Ok::<Val, SqlError>(Val::Int(k)));
    assert(eval_expr(db, e, Expr::Col(11)) == Ok::<Val, SqlError>(Val::Int(a)));
    assert(eval_expr(db, e, Expr::Col(18)) == Ok::<Val, SqlError>(Val::Int(s)));
    assert(eval_expr(db, e, Expr::Col(12)) == Ok::<Val, SqlError>(Val::Int(b)));
    lemma_compare_int(k, a);
    lemma_compare_int(s, b);
    let p1 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(17), b: Expr::Col(11) };
    let p2 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(18), b: Expr::Col(12) };
    lemma_pred_cmp(db, e, CmpOp::Eq, Expr::Col(17), Expr::Col(11), Val::Int(k), Val::Int(a), k, a);
    lemma_pred_cmp(db, e, CmpOp::Eq, Expr::Col(18), Expr::Col(12), Val::Int(s), Val::Int(b), s, b);
    lemma_pred_and(db, e, p1, p2, k == a, s == b);
    lemma_li_date_preds(db, e, ps, lo, hi, d);
    lemma_pred_and(db, e, li_key_pred(), li_ge_pred(ps[1]), k == a && s == b, lo <= d);
    lemma_pred_and(db, e, and(li_key_pred(), li_ge_pred(ps[1])), li_lt_pred(ps[1]), (k == a && s == b) && lo <= d, d < hi);
    assert(ival(r[10]) == d - 10957);
    assert(lf(lo, hi, a, b)(r) == (((k == a && s == b) && lo <= d) && d < hi));
}

/// The inner WHERE keeps the hits of the pair.
pub proof fn lemma_li_filter(db: Database, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, ctx: Row, a: int, b: int)
    requires
        tables_of(sv, db), stores_wf(sv), win_ok(ps, lo, hi),
        ctx.len() == 16, ctx[11] == Val::Int(a), ctx[12] == Val::Int(b),
    ensures eval_query(db, ctx, li_filter(ps[1])) == Ok::<Relation, SqlError>(keep(line_rows(sv), lf(lo, hi, a, b))),
{
    let rows = line_rows(sv);
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(rows));
    let pred = li_pred(ps[1]);
    let f = lf(lo, hi, a, b);
    let truths = Seq::new(rows.len(), |i: int| truth_of(f(rows[i])));
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        lemma_li_pred_row(db, sv, ps, lo, hi, ctx, a, b, i);
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    lemma_keep_true_keep(rows, truths, f);
}

/// The quantity values of rows (position 4).
pub open spec fn qty_col(ks: Seq<Row>) -> Seq<Val> { ks.map_values(|r: Row| r[4]) }

/// Every row holds a numeric value of scale 2 at position 4.
pub open spec fn qty_shaped(ks: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < ks.len() ==> (#[trigger] ks[i])[4] is Num && ks[i][4]->Num_scale == 2
}

/// The coefficient at position 4.
pub open spec fn qcoef() -> spec_fn(Row) -> int { |r: Row| ival(r[4]) }

/// Values of one scale 2: the count, kind and exact sum of the quantity column.
pub proof fn lemma_qty_col(ks: Seq<Row>)
    requires qty_shaped(ks),
    ensures
        count_non_null(qty_col(ks)) == ks.len(),
        all_of_kind(NumKind::Numeric, qty_col(ks)),
        num_sum(qty_col(ks)) == if ks.len() == 0 { (0int, 0nat) } else { (sum_of(ks, qcoef()), 2nat) },
    decreases ks.len(),
{
    if ks.len() > 0 {
        let ki = ks.drop_last();
        assert forall|i: int| 0 <= i < ki.len() implies (#[trigger] ki[i])[4] is Num && ki[i][4]->Num_scale == 2 by {
            assert(ki[i] == ks[i]);
        }
        lemma_qty_col(ki);
        let vs = qty_col(ks);
        assert(vs.drop_last() =~= qty_col(ki));
        let v = ks.last()[4];
        assert(ks.last() == ks[ks.len() - 1]);
        assert(vs.last() == v);
        let c = v->Num_coeff;
        assert(v == Val::Num { coeff: c, scale: 2 });
        assert(pow10(0) == 1);
        let acc = num_sum(qty_col(ki));
        lemma_align_same(c, 2);
        assert(sum_of(ks, qcoef()) == sum_of(ki, qcoef()) + ival(v));
        if ki.len() == 0 {
            assert(align(0, 0, 2) == 0);
        } else {
            lemma_align_same(acc.0, 2);
        }
    } else {
        assert(qty_col(ks) =~= Seq::<Val>::empty());
    }
}

/// The sum over a sequence built by `Seq::new` is the range sum of the terms of its elements.
pub proof fn lemma_sum_of_new(n: nat, g: spec_fn(int) -> Row, h: spec_fn(Row) -> int)
    ensures sum_of(Seq::new(n, g), h) == range_sum(0, n as int, |i: int| h(g(i))),
    decreases n,
{
    if n > 0 {
        let s = Seq::new(n, g);
        lemma_sum_of_new((n - 1) as nat, g, h);
        assert(s.drop_last() =~= Seq::new((n - 1) as nat, g));
    } else {
        assert(Seq::new(n, g) =~= Seq::<Row>::empty());
    }
}

/// The sum of 1 over rows is their number.
pub proof fn lemma_sum_of_one(ks: Seq<Row>)
    ensures sum_of(ks, |r: Row| 1int) == ks.len(),
    decreases ks.len(),
{
    if ks.len() > 0 {
        lemma_sum_of_one(ks.drop_last());
    }
}

/// The kept inner rows: `lcnt` of them, their quantity coefficients summing to `lsum`, all of scale 2.
pub proof fn lemma_li_kept(sv: StoresView, lo: int, hi: int, a: int, b: int)
    requires stores_wf(sv),
    ensures ({
        let ks = keep(line_rows(sv), lf(lo, hi, a, b));
        &&& ks.len() == lcnt(sv, lo, hi, a, b)
        &&& sum_of(ks, qcoef()) == lsum(sv, lo, hi, a, b)
        &&& qty_shaped(ks)
        &&& forall|i: int| 0 <= i < ks.len() ==> (#[trigger] ks[i]).len() == 16
    }),
{
    let rows = line_rows(sv);
    let f = lf(lo, hi, a, b);
    let ks = keep(rows, f);
    lemma_keep_members(rows, f);
    let g = |i: int| li::row_at(sv.flat_lineitem, i);
    assert(rows == Seq::new(n_l(sv), g));
    // the count: 1 on kept rows, 0 elsewhere
    let one_k = |r: Row| if f(r) { 1int } else { 0int };
    assert forall|i: int| 0 <= i < rows.len() && !f(#[trigger] rows[i]) implies one_k(rows[i]) == 0 by {}
    lemma_sum_of_keep(rows, f, one_k);
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] one_k(ks[i]) == (|r: Row| 1int)(ks[i]) by {
        assert(rows.contains(ks[i]));
    }
    lemma_sum_of_ext(ks, one_k, |r: Row| 1int);
    lemma_sum_of_one(ks);
    lemma_sum_of_new(n_l(sv), g, one_k);
    let gc = |i: int| one_k(g(i));
    assert forall|l: int| 0 <= l < n_l(sv) implies #[trigger] gc(l) == lcnt_term(sv, lo, hi, a, b)(l) by {
        lemma_lf_row(sv, lo, hi, a, b, l);
    }
    lemma_range_sum_ext(0, n_l(sv) as int, gc, lcnt_term(sv, lo, hi, a, b));
    // the quantity sum: the coefficient on kept rows, 0 elsewhere
    let q_k = |r: Row| if f(r) { ival(r[4]) } else { 0int };
    assert forall|i: int| 0 <= i < rows.len() && !f(#[trigger] rows[i]) implies q_k(rows[i]) == 0 by {}
    lemma_sum_of_keep(rows, f, q_k);
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] q_k(ks[i]) == qcoef()(ks[i]) by {
        assert(rows.contains(ks[i]));
    }
    lemma_sum_of_ext(ks, q_k, qcoef());
    lemma_sum_of_new(n_l(sv), g, q_k);
    let gq = |i: int| q_k(g(i));
    assert forall|l: int| 0 <= l < n_l(sv) implies #[trigger] gq(l) == lsum_term(sv, lo, hi, a, b)(l) by {
        lemma_lf_row(sv, lo, hi, a, b, l);
        lemma_line_row(sv, l);
    }
    lemma_range_sum_ext(0, n_l(sv) as int, gq, lsum_term(sv, lo, hi, a, b));
    // every row has 16 columns and a scale-2 quantity
    assert forall|i: int| 0 <= i < ks.len() implies (#[trigger] ks[i])[4] is Num && ks[i][4]->Num_scale == 2 && ks[i].len() == 16 by {
        assert(rows.contains(ks[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == ks[i];
        lemma_line_row(sv, m);
    }
}

// ------------------------------------------------------------------------------------------------ the subquery

/// The aggregate arguments of the kept inner rows (each the one-value row of its quantity).
pub open spec fn li_args(ks: Seq<Row>) -> Seq<Row> { ks.map_values(|r: Row| seq![r[4]]) }

/// The SUM argument of one inner row `r` in context `x`: its quantity.
proof fn lemma_li_arg_row(db: Database, x: Row, r: Row)
    requires x.len() == 16, r.len() == 16,
    ensures agg_args(db, x + r, li_aggs()) == Ok::<Row, SqlError>(seq![r[4]]),
{
    let e = x + r;
    let aggs = li_aggs();
    assert(e[20] == r[4]);
    let ar = agg_arg_results(db, e, aggs);
    lemma_agg_arg_results_index(db, e, aggs);
    assert(ar[0] == agg_arg(db, e, aggs[0]));
    assert(agg_arg(db, e, aggs[0]) == eval_expr(db, e, Expr::Col(20)));
    assert(ar[0] == Ok::<Val, SqlError>(r[4]));
    lemma_collect_all(ar, seq![r[4]]);
    lemma_agg_args(db, e, aggs);
}

/// The SUM arguments of the kept inner rows, in context `x`.
proof fn lemma_li_args(db: Database, x: Row, ks: Seq<Row>)
    requires x.len() == 16, forall|i: int| 0 <= i < ks.len() ==> (#[trigger] ks[i]).len() == 16,
    ensures collect(agg_args_results(db, x, ks, li_aggs())) == Ok::<Seq<Row>, SqlError>(li_args(ks)),
{
    hide(agg_args);
    let rs = agg_args_results(db, x, ks, li_aggs());
    let args = li_args(ks);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(args[i]) by {
        lemma_li_arg_row(db, x, ks[i]);
    }
    lemma_collect_all(rs, args);
}

/// SUM over the argument rows of the kept inner rows of the pair.
proof fn lemma_li_sum(sv: StoresView, lo: int, hi: int, a: int, b: int)
    requires model_ok(sv), sizes_ok(sv),
    ensures agg_row(li_aggs(), li_args(keep(line_rows(sv), lf(lo, hi, a, b))))
        == Ok::<Row, SqlError>(seq![sum_val(sv, lo, hi, a, b)]),
{
    let ks = keep(line_rows(sv), lf(lo, hi, a, b));
    lemma_li_kept(sv, lo, hi, a, b);
    let aggs = li_aggs();
    let args = li_args(ks);
    lemma_agg_row(aggs, args);
    let col = column(args, 0);
    assert(col =~= qty_col(ks));
    lemma_qty_col(ks);
    let vr = agg_value_results(aggs, args);
    assert(vr.len() == 1);
    assert(vr[0] == agg_value(aggs[0], col));
    lemma_ltotals_bounds(sv, lo, hi, a, b);
    if lcnt(sv, lo, hi, a, b) > 0 {
        let s = lsum(sv, lo, hi, a, b);
        lemma_num_in_range_small(s, 2);
        assert(num_result(s, 2) == Ok::<Val, SqlError>(Val::Num { coeff: s, scale: 2 }));
    }
    assert(vr[0] == Ok::<Val, SqlError>(sum_val(sv, lo, hi, a, b)));
    lemma_collect_all(vr, seq![sum_val(sv, lo, hi, a, b)]);
}

/// `SUM(l_quantity)` over the kept inner rows, in context `ctx`.
pub proof fn lemma_li_agg(db: Database, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, ctx: Row, a: int, b: int)
    requires
        tables_of(sv, db), model_ok(sv), sizes_ok(sv), win_ok(ps, lo, hi),
        ctx.len() == 16, ctx[11] == Val::Int(a), ctx[12] == Val::Int(b),
    ensures eval_query(db, ctx, li_agg(ps[1])) == Ok::<Relation, SqlError>(seq![seq![sum_val(sv, lo, hi, a, b)]]),
{
    lemma_li_filter(db, sv, ps, lo, hi, ctx, a, b);
    let ks = keep(line_rows(sv), lf(lo, hi, a, b));
    lemma_li_kept(sv, lo, hi, a, b);
    lemma_li_args(db, ctx, ks);
    lemma_li_sum(sv, lo, hi, a, b);
    lemma_eval_aggregate(db, ctx, li_aggs(), Box::new(li_filter(ps[1])));
}

/// `0.5 * SUM` as values: the subquery's value.
proof fn lemma_half_mul_val(sv: StoresView, lo: int, hi: int, a: int, b: int)
    requires model_ok(sv), sizes_ok(sv),
    ensures arith(ArithOp::Mul, NumKind::Numeric, Val::Num { coeff: 5, scale: 1 }, sum_val(sv, lo, hi, a, b))
        == Ok::<Val, SqlError>(li_val(sv, lo, hi, a, b)),
{
    lemma_ltotals_bounds(sv, lo, hi, a, b);
    if lcnt(sv, lo, hi, a, b) > 0 {
        let s = lsum(sv, lo, hi, a, b);
        assert(num_arith(ArithOp::Mul, 5, 1, s, 2) == (5 * s, 3nat));
        lemma_num_in_range_small(5 * s, 3);
        assert(num_result(5 * s, 3) == Ok::<Val, SqlError>(Val::Num { coeff: 5 * s, scale: 3 }));
    }
}

/// `0.5 * SUM` on the aggregate row, as a one-value projection list.
proof fn lemma_half_mul(db: Database, sv: StoresView, lo: int, hi: int, x: Row, a: int, b: int)
    requires model_ok(sv), sizes_ok(sv), x.len() == 16,
    ensures eval_exprs(db, x + seq![sum_val(sv, lo, hi, a, b)], seq![half_mul()])
        == Ok::<Row, SqlError>(seq![li_val(sv, lo, hi, a, b)]),
{
    let s = sum_val(sv, lo, hi, a, b);
    let e = x + seq![s];
    assert(e[16] == s);
    assert(eval_expr(db, e, Expr::Col(16)) == Ok::<Val, SqlError>(s));
    lemma_num_in_range_small(5, 1);
    assert(crate::spec::limits::numeric_dscale_max() == 16383);
    assert(eval_expr(db, e, Expr::Lit(half_lit())) == Ok::<Val, SqlError>(Val::Num { coeff: 5, scale: 1 }));
    lemma_half_mul_val(sv, lo, hi, a, b);
    assert(eval_expr(db, e, half_mul()) == Ok::<Val, SqlError>(li_val(sv, lo, hi, a, b)));
    let es = seq![half_mul()];
    let er = expr_results(db, e, es);
    lemma_expr_results_index(db, e, es);
    lemma_collect_all(er, seq![li_val(sv, lo, hi, a, b)]);
}

/// The subquery in context `ctx`: the one row `[li_val]`.
pub proof fn lemma_li_query(db: Database, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, ctx: Row, a: int, b: int)
    requires
        tables_of(sv, db), model_ok(sv), sizes_ok(sv), win_ok(ps, lo, hi),
        ctx.len() == 16, ctx[11] == Val::Int(a), ctx[12] == Val::Int(b),
    ensures eval_query(db, ctx, li_sub(ps[1])) == Ok::<Relation, SqlError>(seq![seq![li_val(sv, lo, hi, a, b)]]),
{
    lemma_li_agg(db, sv, ps, lo, hi, ctx, a, b);
    let s = sum_val(sv, lo, hi, a, b);
    let es = seq![half_mul()];
    lemma_eval_project(db, ctx, es, Box::new(li_agg(ps[1])));
    lemma_half_mul(db, sv, lo, hi, ctx, a, b);
    let rows = seq![seq![s]];
    let pr = project_results(db, ctx, rows, es);
    assert(pr.len() == 1);
    assert(pr[0] == eval_exprs(db, ctx + rows[0], es));
    lemma_collect_all(pr, seq![seq![li_val(sv, lo, hi, a, b)]]);
}

/// The scalar subquery expression in context `ctx` is `li_val`.
pub proof fn lemma_li_value(db: Database, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, ctx: Row, a: int, b: int)
    requires
        tables_of(sv, db), model_ok(sv), sizes_ok(sv), win_ok(ps, lo, hi),
        ctx.len() == 16, ctx[11] == Val::Int(a), ctx[12] == Val::Int(b),
    ensures eval_expr(db, ctx, Expr::Subquery(Box::new(li_sub(ps[1])))) == Ok::<Val, SqlError>(li_val(sv, lo, hi, a, b)),
{
    lemma_li_query(db, sv, ps, lo, hi, ctx, a, b);
}

} // verus!
