//! The aggregate `SUM(l_extendedprice)` over the kept joined rows and the body `SELECT sum / 7.0`, stated with the
//! per-lineitem totals `t = tot(sv, ps)` (the number of qualifying rows and their price coefficient sum, scale 2):
//! - the aggregate row is `grow(t)`: NULL without qualifying rows, else the sum at scale 2 (`lemma_eval_agg`);
//! - the output value is `out_val(t)`: NULL, or PostgreSQL's numeric division of the sum by `7.0`, or its SQL
//!   error (`lemma_body_rows`);
//! - outside `out_fits(t)` (the division leaves its executable domain) the body is outside the capacity domain.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::fns::*;
use crate::spec::fns::div::*;
use crate::exec::domain::*;
use crate::exec::relational::domain::*;
use crate::gendb_entry::stores::StoresView;
use crate::link::join::{keep, sum_of, lemma_sum_of_ext};
use crate::link::expr::{ival, lemma_align_same};
use crate::link::query::lemma_agg_arg_sum;
use crate::bridge::collect::lemma_collect_all;
use crate::agent::tables::*;
use crate::agent::ast::*;
use crate::agent::sub::*;
use crate::agent::joined::*;
use crate::agent::common::selection::*;

verus! {

// ------------------------------------------------------------------------------------------------ totals

/// The totals of the qualifying lineitem rows: their number and their price coefficient sum (scale 2).
pub struct Tot {
    pub cnt: int,
    pub sum: int,
}

pub open spec fn tot(sv: StoresView, ps: Seq<Literal>) -> Tot {
    Tot { cnt: range_sum(0, n_l(sv) as int, f_cnt(sv, ps)), sum: range_sum(0, n_l(sv) as int, f_price(sv, ps)) }
}

/// Range sums of the per-row terms: the count is in `[0, hi - lo]` and the price sum is bounded by the count.
pub proof fn lemma_fterm_bounds(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int)
    requires lo <= hi, 0 <= lo, hi <= n_l(sv), domains_ok(sv),
    ensures
        0 <= range_sum(lo, hi, f_cnt(sv, ps)) <= hi - lo,
        -999_999_999_999_999 * range_sum(lo, hi, f_cnt(sv, ps)) <= range_sum(lo, hi, f_price(sv, ps))
            <= 999_999_999_999_999 * range_sum(lo, hi, f_cnt(sv, ps)),
    decreases hi - lo,
{
    if hi > lo {
        lemma_fterm_bounds(sv, ps, lo, hi - 1);
        assert(num15(l_qty(sv)[hi - 1]) && num15(l_price(sv)[hi - 1]));
    }
}

/// The totals are bounded: `0 <= cnt <= n_l` and `|sum| < sum_bound()`.
pub proof fn lemma_tot_bounds(sv: StoresView, ps: Seq<Literal>)
    requires domains_ok(sv), sizes_ok(sv),
    ensures
        0 <= tot(sv, ps).cnt <= n_l(sv),
        -sum_bound() < tot(sv, ps).sum < sum_bound(),
        tot(sv, ps).cnt == 0 ==> tot(sv, ps).sum == 0,
{
    lemma_fterm_bounds(sv, ps, 0, n_l(sv) as int);
    let c = tot(sv, ps).cnt;
    assert(999_999_999_999_999 * c < sum_bound()) by (nonlinear_arith)
        requires 0 <= c <= 0xffff_ffff_ffff_ffff;
}

// ------------------------------------------------------------------------------------------------ the aggregate

/// The price values of rows (position 5).
pub open spec fn price_col(ks: Seq<Row>) -> Seq<Val> { ks.map_values(|r: Row| r[5]) }

/// Every row holds a numeric value of scale 2 at position 5.
pub open spec fn price_shaped(ks: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < ks.len() ==> (#[trigger] ks[i]).len() == 25 && ks[i][5] is Num && ks[i][5]->Num_scale == 2
}

/// The coefficient at position 5.
pub open spec fn pcoef() -> spec_fn(Row) -> int { |r: Row| ival(r[5]) }

/// Values of one scale 2: the count, kind and exact sum of the price column.
pub proof fn lemma_price_col(ks: Seq<Row>)
    requires price_shaped(ks),
    ensures
        count_non_null(price_col(ks)) == ks.len(),
        all_of_kind(NumKind::Numeric, price_col(ks)),
        num_sum(price_col(ks)) == if ks.len() == 0 { (0int, 0nat) } else { (sum_of(ks, pcoef()), 2nat) },
    decreases ks.len(),
{
    if ks.len() > 0 {
        let ki = ks.drop_last();
        assert forall|i: int| 0 <= i < ki.len() implies (#[trigger] ki[i]).len() == 25 && ki[i][5] is Num && ki[i][5]->Num_scale == 2 by {
            assert(ki[i] == ks[i]);
        }
        lemma_price_col(ki);
        let vs = price_col(ks);
        assert(vs.drop_last() =~= price_col(ki));
        let v = ks.last()[5];
        assert(ks.last() == ks[ks.len() - 1]);
        assert(vs.last() == v);
        let c = v->Num_coeff;
        assert(v == Val::Num { coeff: c, scale: 2 });
        let acc = num_sum(price_col(ki));
        lemma_align_same(c, 2);
        assert(sum_of(ks, pcoef()) == sum_of(ki, pcoef()) + ival(v));
        if ki.len() == 0 {
            assert(align(0, 0, 2) == 0);
        } else {
            lemma_align_same(acc.0, 2);
        }
    } else {
        assert(price_col(ks) =~= Seq::<Val>::empty());
    }
}

/// The aggregate row of the totals `t`: NULL without rows, else the price sum at scale 2.
pub open spec fn grow(t: Tot) -> Row {
    if t.cnt == 0 { seq![Val::Null] } else { seq![Val::Num { coeff: t.sum, scale: 2 }] }
}

/// The SUM argument of one kept row: its price.
proof fn lemma_arg_row(db: Database, x: Row)
    requires x.len() == 25,
    ensures agg_args(db, x, q_aggs()) == Ok::<Row, SqlError>(seq![x[5]]),
{
    hide(eval_expr);
    hide(agg_arg);
    hide(collect);
    hide(agg_arg_results);
    let aggs = q_aggs();
    lemma_col_5(db, x);
    lemma_agg_arg_sum(db, x, NumKind::Numeric, Expr::Col(5));
    let ar = agg_arg_results(db, x, aggs);
    lemma_agg_arg_results_index(db, x, aggs);
    assert(aggs[0] == Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(5) });
    assert(ar[0] == Ok::<Val, SqlError>(x[5]));
    lemma_collect_all(ar, seq![x[5]]);
    reveal(collect);
    lemma_agg_args(db, x, aggs);
}

proof fn lemma_col_5(db: Database, x: Row)
    requires x.len() == 25,
    ensures eval_expr(db, x, Expr::Col(5)) == Ok::<Val, SqlError>(x[5]),
{
}

/// The argument rows of rows `ks`.
pub open spec fn sum_args(ks: Seq<Row>) -> Seq<Row> { ks.map_values(|r: Row| seq![r[5]]) }

/// The SUM arguments of the kept rows.
proof fn lemma_args(db: Database, ks: Seq<Row>)
    requires price_shaped(ks),
    ensures collect(agg_args_results(db, Seq::empty(), ks, q_aggs())) == Ok::<Seq<Row>, SqlError>(sum_args(ks)),
{
    hide(agg_args);
    hide(collect);
    let ctx = Seq::<Val>::empty();
    let rs = agg_args_results(db, ctx, ks, q_aggs());
    let args = sum_args(ks);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(args[i]) by {
        assert(ctx + ks[i] =~= ks[i]);
        lemma_arg_row(db, ks[i]);
    }
    lemma_collect_all(rs, args);
}

/// The SUM over the argument rows of rows of one scale whose count and sum are `t` (and in range).
proof fn lemma_sum_row(ks: Seq<Row>, t: Tot)
    requires
        price_shaped(ks),
        ks.len() == t.cnt,
        sum_of(ks, pcoef()) == t.sum,
        -sum_bound() < t.sum < sum_bound(),
    ensures agg_row(q_aggs(), sum_args(ks)) == Ok::<Row, SqlError>(grow(t)),
{
    let aggs = q_aggs();
    let args = sum_args(ks);
    crate::exec::relational::domain::lemma_agg_row(aggs, args);
    assert(column(args, 0) =~= price_col(ks));
    lemma_price_col(ks);
    let vr = agg_value_results(aggs, args);
    assert(vr.len() == 1);
    assert(vr[0] == agg_value(aggs[0], price_col(ks)));
    if t.cnt > 0 {
        lemma_sum_bound_small();
        lemma_num_in_range_small(t.sum, 2);
    }
    assert(vr[0] == Ok::<Val, SqlError>(grow(t)[0]));
    lemma_collect_all(vr, grow(t));
}

/// The aggregate node over the filtered rows `ks` with totals `t`: the one row `grow(t)`.
pub proof fn lemma_eval_agg(db: Database, ps: Seq<Literal>, ks: Seq<Row>, t: Tot)
    requires
        eval_query(db, Seq::empty(), q_filter(ps)) == Ok::<Relation, SqlError>(ks),
        price_shaped(ks),
        ks.len() == t.cnt,
        sum_of(ks, pcoef()) == t.sum,
        -sum_bound() < t.sum < sum_bound(),
    ensures eval_query(db, Seq::empty(), q_agg(ps)) == Ok::<Relation, SqlError>(seq![grow(t)]),
{
    hide(eval_query);
    hide(agg_row);
    hide(collect);
    let ctx = Seq::<Val>::empty();
    lemma_args(db, ks);
    lemma_sum_row(ks, t);
    lemma_eval_aggregate(db, ctx, q_aggs(), Box::new(q_filter(ps)));
}

// ------------------------------------------------------------------------------------------------ the output

/// The output value of the totals `t`.
pub open spec fn out_val(t: Tot) -> Result<Val, SqlError> {
    if t.cnt == 0 { Ok(Val::Null) } else { num_div(t.sum, 2, 70, 1) }
}

/// The output's division is inside its executable domain.
pub open spec fn out_fits(t: Tot) -> bool {
    t.cnt == 0 || num_div_fits(t.sum, 2, 70, 1)
}

/// The literal `7.0`.
proof fn lemma_seven(db: Database, g: Row)
    ensures eval_expr(db, g, Expr::Lit(seven_lit())) == Ok::<Val, SqlError>(Val::Num { coeff: 70, scale: 1 }),
{
    lemma_num_in_range_small(70, 1);
    assert(crate::spec::limits::numeric_dscale_max() == 16383);
}

/// A two-element list of expressions.
proof fn lemma_list2(db: Database, g: Row, a: Expr, b: Expr, va: Val, vb: Val)
    requires eval_expr(db, g, a) == Ok::<Val, SqlError>(va), eval_expr(db, g, b) == Ok::<Val, SqlError>(vb),
    ensures eval_exprs(db, g, seq![a, b]) == Ok::<Row, SqlError>(seq![va, vb]),
{
    hide(eval_expr);
    hide(collect);
    let es = seq![a, b];
    let vs = seq![va, vb];
    let rs = expr_results(db, g, es);
    lemma_expr_results_index(db, g, es);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        if i == 0 {} else { assert(i == 1); }
    }
    lemma_collect_all(rs, vs);
    assert(eval_exprs(db, g, es) == collect(rs));
}

/// The domain of a two-element list of columns and literals: always inside.
proof fn lemma_fits_list2(db: Database, g: Row, a: Expr, b: Expr)
    requires eval_expr(db, g, a) is Ok, fits_expr(db, g, a), fits_expr(db, g, b),
    ensures fits_exprs(db, g, seq![a, b]),
{
    hide(eval_expr);
    hide(fits_expr);
    hide(eval_exprs);
    let es = seq![a, b];
    let first = seq![a];
    assert(es.drop_last() =~= first);
    assert(es.last() == b);
    assert(first.drop_last() =~= Seq::<Expr>::empty());
    assert(first.last() == a);
    lemma_fits_exprs_unfold(db, g, es);
    lemma_fits_exprs_unfold(db, g, first);
    assert(fits_exprs(db, g, Seq::<Expr>::empty()));
    reveal(eval_exprs);
    lemma_eval_exprs_empty(db, g);
    lemma_eval_exprs_step(db, g, first);
}

/// One evaluation and domain step of a call over evaluated arguments.
proof fn lemma_call_node(db: Database, g: Row, f: ScalarFn, args: Seq<Expr>, vs: Seq<Val>)
    requires eval_exprs(db, g, args) == Ok::<Row, SqlError>(vs),
    ensures
        eval_expr(db, g, Expr::Call { f, args }) == apply_fn(f, vs),
        fits_expr(db, g, Expr::Call { f, args }) == (fits_exprs(db, g, args) && fits_fn(f, vs)),
{
}

/// The numeric division on two operands: NULL with a NULL dividend, else `num_div`; and its domain.
proof fn lemma_apply_div(x: Val, y: Val)
    requires y is Num,
    ensures
        x is Null ==> apply_fn(ScalarFn::DivNumeric, seq![x, y]) == Ok::<Val, SqlError>(Val::Null)
            && fits_fn(ScalarFn::DivNumeric, seq![x, y]),
        x is Num ==> apply_fn(ScalarFn::DivNumeric, seq![x, y])
            == num_div(x->Num_coeff, x->Num_scale, y->Num_coeff, y->Num_scale)
            && fits_fn(ScalarFn::DivNumeric, seq![x, y]) == num_div_fits(x->Num_coeff, x->Num_scale, y->Num_coeff, y->Num_scale),
{
    let vs = seq![x, y];
    assert(vs[0] == x && vs[1] == y);
}

/// `sum / 7.0` on the aggregate row, and its domain.
proof fn lemma_div(db: Database, t: Tot)
    ensures
        eval_expr(db, grow(t), div_expr()) == out_val(t),
        fits_expr(db, grow(t), div_expr()) == out_fits(t),
{
    hide(apply_fn);
    hide(fits_fn);
    hide(num_div);
    hide(num_div_fits);
    let g = grow(t);
    let seven = Val::Num { coeff: 70, scale: 1 };
    assert(eval_expr(db, g, Expr::Col(0)) == Ok::<Val, SqlError>(g[0]));
    lemma_seven(db, g);
    lemma_list2(db, g, Expr::Col(0), Expr::Lit(seven_lit()), g[0], seven);
    lemma_fits_list2(db, g, Expr::Col(0), Expr::Lit(seven_lit()));
    lemma_call_node(db, g, ScalarFn::DivNumeric, seq![Expr::Col(0), Expr::Lit(seven_lit())], seq![g[0], seven]);
    lemma_apply_div(g[0], seven);
}

/// The output expressions on the aggregate row: one value, or its error; their domain.
proof fn lemma_outs(db: Database, t: Tot)
    ensures
        eval_exprs(db, grow(t), seq![div_expr()]) == match out_val(t) {
            Ok(v) => Ok::<Row, SqlError>(seq![v]),
            Err(e) => Err(e),
        },
        fits_exprs(db, grow(t), seq![div_expr()]) == out_fits(t),
{
    hide(eval_expr);
    hide(fits_expr);
    let g = grow(t);
    let es = seq![div_expr()];
    lemma_div(db, t);
    assert(es.drop_last() =~= Seq::<Expr>::empty());
    assert(es.last() == div_expr());
    lemma_eval_exprs_empty(db, g);
    lemma_eval_exprs_step(db, g, es);
    lemma_fits_exprs_unfold(db, g, es);
    assert(fits_exprs(db, g, Seq::<Expr>::empty()));
    if let Ok(v) = out_val(t) {
        assert(Seq::<Val>::empty().push(v) =~= seq![v]);
    }
}

/// The body over the aggregate row `grow(t)`: the output row, or its error; outside its domain, `!fits_query`.
pub proof fn lemma_project(db: Database, ps: Seq<Literal>, t: Tot)
    requires eval_query(db, Seq::empty(), q_agg(ps)) == Ok::<Relation, SqlError>(seq![grow(t)]),
    ensures
        eval_query(db, Seq::empty(), q_body(ps)) == match out_val(t) {
            Ok(v) => Ok::<Relation, SqlError>(seq![seq![v]]),
            Err(e) => Err::<Relation, SqlError>(e),
        },
        !out_fits(t) ==> !fits_query(db, Seq::empty(), q_body(ps)),
{
    hide(eval_exprs);
    hide(fits_exprs);
    let ctx = Seq::<Val>::empty();
    let g = grow(t);
    let rows = seq![g];
    let exprs = seq![div_expr()];
    lemma_outs(db, t);
    assert(ctx + g =~= g);
    lemma_eval_project(db, ctx, exprs, Box::new(q_agg(ps)));
    let rs = project_results(db, ctx, rows, exprs);
    assert(rs.len() == 1 && rs[0] == eval_exprs(db, g, exprs));
    assert(rs.drop_last() =~= Seq::<Result<Row, SqlError>>::empty());
    assert(collect(rs.drop_last()) == Ok::<Seq<Row>, SqlError>(Seq::empty()));
    if let Ok(v) = out_val(t) {
        assert(Seq::<Row>::empty().push(seq![v]) =~= seq![seq![v]]);
    }
    if !out_fits(t) {
        let fs = project_fs(db, ctx, rows, exprs);
        lemma_project_fs_index(db, ctx, rows, exprs);
        assert(fs[0] == fits_exprs(db, ctx + rows[0], exprs));
        assert(ok_before(rs, 0));
        assert(!fits_each(rs, fs));
    }
}

// ------------------------------------------------------------------------------------------------ the body

/// Every kept row has the shape the aggregate reads, and the kept rows' count and price sum are the totals.
pub proof fn lemma_kept_tot(sv: StoresView, ps: Seq<Literal>)
    requires model_ok(sv),
    ensures ({
        let k = keep(jrows(sv), jq(sv, ps));
        &&& price_shaped(k)
        &&& k.len() == tot(sv, ps).cnt
        &&& sum_of(k, pcoef()) == tot(sv, ps).sum
    }),
{
    let k = keep(jrows(sv), jq(sv, ps));
    lemma_kept_rows(sv, ps);
    lemma_kept_sums(sv, ps);
    assert forall|i: int| 0 <= i < k.len() implies (#[trigger] k[i]).len() == 25 && k[i][5] is Num && k[i][5]->Num_scale == 2 by {
        assert(kept_ok(sv, ps, k[i]));
        let (l, a) = choose|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && k[i] == #[trigger] row2(sv, l, a);
        lemma_row2(sv, l, a);
    }
    assert forall|i: int| 0 <= i < k.len() implies (jt_cnt(sv, ps))(#[trigger] k[i]) == 1 by {
        assert(kept_ok(sv, ps, k[i]));
    }
    lemma_sum_one(k, jt_cnt(sv, ps));
    assert forall|i: int| 0 <= i < k.len() implies (pcoef())(#[trigger] k[i]) == (jt_price(sv, ps))(k[i]) by {
        assert(kept_ok(sv, ps, k[i]));
    }
    lemma_sum_of_ext(k, pcoef(), jt_price(sv, ps));
}

/// The number of rows is the sum of 1 over them.
proof fn lemma_sum_one(ks: Seq<Row>, f: spec_fn(Row) -> int)
    requires forall|i: int| 0 <= i < ks.len() ==> f(#[trigger] ks[i]) == 1,
    ensures sum_of(ks, f) == ks.len(),
    decreases ks.len(),
{
    if ks.len() > 0 {
        let ki = ks.drop_last();
        assert forall|i: int| 0 <= i < ki.len() implies f(#[trigger] ki[i]) == 1 by { assert(ki[i] == ks[i]); }
        lemma_sum_one(ki, f);
        assert(f(ks[ks.len() - 1]) == 1);
    }
}

/// The body over a bound database: the output row or its error, and `!fits_query` outside `out_fits`.
pub proof fn lemma_body_rows(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), model_ok(sv), sizes_ok(sv), params_text(ps),
    ensures ({
        let t = tot(sv, ps);
        &&& eval_query(db, Seq::empty(), q_body(ps)) == match out_val(t) {
                Ok(v) => Ok::<Relation, SqlError>(seq![seq![v]]),
                Err(e) => Err::<Relation, SqlError>(e),
            }
        &&& !out_fits(t) ==> !fits_query(db, Seq::empty(), q_body(ps))
    }),
{
    let t = tot(sv, ps);
    crate::agent::joined::lemma_eval_filter(db, sv, ps);
    lemma_kept_tot(sv, ps);
    lemma_tot_bounds(sv, ps);
    lemma_eval_agg(db, ps, keep(jrows(sv), jq(sv, ps)), t);
    lemma_project(db, ps, t);
}

} // verus!
