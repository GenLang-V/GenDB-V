//! The correlated lineitem subquery `(SELECT 0.5 * SUM(l_quantity) FROM lineitem WHERE l_partkey = ps_partkey AND
//! l_suppkey = ps_suppkey AND l_shipdate >= $2 AND l_shipdate < $2 + INTERVAL '1' YEAR)` under a context `c` of 16
//! values (`supplier ++ nation ++ partsupp`), and the condition `ps_availqty > (subquery)`:
//! - `lemma_hi_expr`: `$2 + 1 year` is the midnight of day `d1` (`nf::d1_ok`);
//! - `lemma_li_filter`: the WHERE keeps the rows `nf::lsel` selects;
//! - `lemma_li_q`: the subquery's single row is NULL without such rows, else `5 * lsum` at scale 3;
//! - `lemma_avail_pred`: the condition is true exactly when `lcnt > 0` and `200 * ps_availqty > lsum`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::datetime::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::link::join::*;
use crate::link::expr::*;
use crate::bridge::collect::lemma_collect_all;
use crate::exec::relational::domain::{filter_results, agg_args_results, project_results};
use crate::query::param_domain;
use super::typed::*;
use super::nf::*;
use super::ast::*;

verus! {

/// The literal `$2` is the date `d0`.
pub proof fn lemma_lit_d0(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures lit_val(ps[1]) == Ok::<Val, SqlError>(Val::Date(d0_of(ps))),
{
    assert(crate::query::param_typed(ps));
}

/// `$2 + INTERVAL '1' YEAR` is the timestamp `d1 * usecs_per_day()`.
pub proof fn lemma_hi_expr(db: Database, env: Row, ps: Seq<Literal>, d1: int)
    requires param_domain(ps), d1_ok(ps, d1),
    ensures eval_expr(db, env, hi_expr(ps)) == Ok::<Val, SqlError>(Val::Ts(d1 * usecs_per_day())),
{
    lemma_lit_d0(ps);
    let lit = Expr::Lit(ps[1]);
    let c = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(lit) };
    assert(eval_expr(db, env, lit) == Ok::<Val, SqlError>(Val::Date(d0_of(ps))));
    assert(eval_expr(db, env, c) == cast(CastOp::DateToTimestamp, Val::Date(d0_of(ps))));
    assert(date_to_ts(d0_of(ps)) is Ok);
}

/// `Col(a) = Col(b)` on two bigints.
pub proof fn lemma_int_eq(db: Database, env: Row, a: nat, b: nat)
    requires a < env.len(), b < env.len(), is_int(env[a as int]), is_int(env[b as int]),
    ensures eval_pred(db, env, ccmp(CmpOp::Eq, a, b)) == Ok::<Truth, SqlError>(truth_of(env[a as int] == env[b as int])),
{
    let (x, y) = (ival(env[a as int]), ival(env[b as int]));
    lemma_expr_col(db, env, a);
    lemma_expr_col(db, env, b);
    lemma_compare_int(x, y);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(a), Expr::Col(b), Val::Int(x), Val::Int(y), x, y);
}

/// The WHERE of the lineitem subquery on one lineitem row `l` (context `c`): `lsel`.
pub proof fn lemma_li_pred(db: Database, c: Row, l: Row, ps: Seq<Literal>, d1: int)
    requires
        c.len() == 16, is_int(c[11]), is_int(c[12]),
        lrow_ok(l),
        param_domain(ps), d1_ok(ps, d1),
    ensures
        eval_pred(db, c + l, li_pred(ps))
            == Ok::<Truth, SqlError>(truth_of(lsel(ival(c[11]), ival(c[12]), d0_of(ps), d1, l))),
{
    hide(eval_pred);
    hide(eval_expr);
    let env = c + l;
    let (k, s, d0) = (ival(c[11]), ival(c[12]), d0_of(ps));
    assert(env[17] == l[1] && env[18] == l[2] && env[26] == l[10] && env[11] == c[11] && env[12] == c[12]);
    lemma_int_eq(db, env, 17, 11);
    lemma_int_eq(db, env, 18, 12);
    let p12 = cand(ccmp(CmpOp::Eq, 17, 11), ccmp(CmpOp::Eq, 18, 12));
    lemma_pred_and(db, env, ccmp(CmpOp::Eq, 17, 11), ccmp(CmpOp::Eq, 18, 12), env[17] == env[11], env[18] == env[12]);
    let dl = ival(l[10]);
    lemma_expr_col(db, env, 26);
    lemma_lit_d0(ps);
    assert(eval_expr(db, env, Expr::Lit(ps[1])) == Ok::<Val, SqlError>(Val::Date(d0))) by {
        reveal(eval_expr);
    }
    lemma_compare_date(dl, d0);
    let pge = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(26), b: Expr::Lit(ps[1]) };
    lemma_pred_cmp(db, env, CmpOp::Ge, Expr::Col(26), Expr::Lit(ps[1]), Val::Date(dl), Val::Date(d0), dl, d0);
    lemma_hi_expr(db, env, ps, d1);
    lemma_compare_date_midnight(dl, d1);
    let plt = Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(26), b: hi_expr(ps) };
    lemma_pred_cmp(db, env, CmpOp::Lt, Expr::Col(26), hi_expr(ps), Val::Date(dl), Val::Ts(d1 * usecs_per_day()), dl, d1);
    lemma_pred_and(db, env, p12, pge, env[17] == env[11] && env[18] == env[12], dl >= d0);
    lemma_pred_and(db, env, cand(p12, pge), plt, (env[17] == env[11] && env[18] == env[12]) && dl >= d0, dl < d1);
    assert((l[1] == c[11]) == (l[1] == Val::Int(k)));
    assert((l[2] == c[12]) == (l[2] == Val::Int(s)));
}

/// The lineitem rows `lsel` keeps for the context's partsupp row.
pub open spec fn li_sel(c: Row, d0: int, d1: int) -> spec_fn(Row) -> bool {
    |r: Row| lsel(ival(c[11]), ival(c[12]), d0, d1, r)
}

/// The WHERE keeps the rows `lsel` selects.
pub proof fn lemma_li_filter(db: Database, c: Row, ps: Seq<Literal>, d1: int)
    requires
        tables_ok(db),
        c.len() == 16, is_int(c[11]), is_int(c[12]),
        param_domain(ps), d1_ok(ps, d1),
    ensures
        eval_query(db, c, li_filter(ps)) == Ok::<Relation, SqlError>(keep(lt(db), li_sel(c, d0_of(ps), d1))),
{
    let l = lt(db);
    let pred = li_pred(ps);
    let f = li_sel(c, d0_of(ps), d1);
    crate::exec::relational::domain::lemma_eval_filter(db, c, pred, Box::new(Query::Table(0)));
    assert(eval_query(db, c, Query::Table(0)) == Ok::<Relation, SqlError>(l));
    let rs = filter_results(db, c, l, pred);
    let truths = Seq::new(l.len(), |i: int| truth_of(f(l[i])));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(lrow_ok(l[i]));
        lemma_li_pred(db, c, l[i], ps, d1);
    }
    lemma_collect_all(rs, truths);
    lemma_keep_true_keep(l, truths, f);
}

/// The quantities of lineitem rows.
pub open spec fn qty_vals(ks: Seq<Row>) -> Seq<Val> {
    ks.map_values(|l: Row| l[4])
}

/// The argument rows `[l_quantity]` of lineitem rows.
pub open spec fn qty_args(ks: Seq<Row>) -> Seq<Row> {
    Seq::new(ks.len(), |i: int| seq![ks[i][4]])
}

/// Numeric(15, 2) quantities: all numeric, none NULL, exact sum at scale 2 (scale 0 when empty).
pub proof fn lemma_qty_sum(ks: Seq<Row>)
    requires forall|i: int| 0 <= i < ks.len() ==> num2(#[trigger] ks[i][4]),
    ensures
        all_of_kind(NumKind::Numeric, qty_vals(ks)),
        count_non_null(qty_vals(ks)) == ks.len(),
        num_sum(qty_vals(ks)) == (sum_of(ks, |l: Row| ival(l[4])), if ks.len() > 0 { 2nat } else { 0nat }),
        -ks.len() * p15() <= sum_of(ks, |l: Row| ival(l[4])) <= ks.len() * p15(),
    decreases ks.len(),
{
    let vs = qty_vals(ks);
    if ks.len() > 0 {
        let d = ks.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies num2(#[trigger] d[i][4]) by {
            assert(d[i] == ks[i]);
        }
        lemma_qty_sum(d);
        assert(vs.drop_last() =~= qty_vals(d));
        assert(num2(ks[ks.len() - 1][4]));
        let c = ival(ks.last()[4]);
        assert(vs.last() == Val::Num { coeff: c, scale: 2 });
        assert(pow10(0) == 1);
        let s = num_sum(qty_vals(d));
        if d.len() == 0 {
            assert(s == (0int, 0nat));
            assert(pow10(2) == 100) by (compute);
            assert(align(0, 0, 2) == 0);
            assert(align(c, 2, 2) == c);
        } else {
            assert(align(s.0, 2, 2) == s.0);
            assert(align(c, 2, 2) == c);
        }
    }
}

/// The argument rows of the kept rows, collected (context `c` of 16 values, l_quantity at 20).
pub proof fn lemma_li_args(db: Database, c: Row, ks: Seq<Row>)
    requires
        c.len() == 16,
        forall|i: int| 0 <= i < ks.len() ==> (#[trigger] ks[i]).len() == 16,
    ensures
        collect(agg_args_results(db, c, ks, seq![sum_agg()])) == Ok::<Seq<Row>, SqlError>(qty_args(ks)),
        column(qty_args(ks), 0) == qty_vals(ks),
{
    let rs = agg_args_results(db, c, ks, seq![sum_agg()]);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(qty_args(ks)[i]) by {
        let env = c + ks[i];
        assert(env[20] == ks[i][4]);
        let ars = agg_arg_results(db, env, seq![sum_agg()]);
        assert(ars[0] == agg_arg(db, env, sum_agg()));
        assert(agg_arg(db, env, sum_agg()) == eval_expr(db, env, Expr::Col(20)));
        lemma_collect_all(ars, seq![ks[i][4]]);
    }
    lemma_collect_all(rs, qty_args(ks));
    assert(column(qty_args(ks), 0) =~= qty_vals(ks));
}

/// The SUM over the kept rows: NULL without rows, else the coefficient sum at scale 2.
pub open spec fn sum_val(n: int, s: int) -> Val {
    if n == 0 { Val::Null } else { Val::Num { coeff: s, scale: 2 } }
}

/// The subquery's value: NULL without rows, else `5 * sum` at scale 3.
pub open spec fn half_val(n: int, s: int) -> Val {
    if n == 0 { Val::Null } else { Val::Num { coeff: 5 * s, scale: 3 } }
}

/// The kept rows' sum and number are `lsum` and `lcnt`.
pub proof fn lemma_kept_sums(db: Database, k: int, s: int, d0: int, d1: int)
    requires tables_ok(db),
    ensures ({
        let ks = keep(lt(db), |r: Row| lsel(k, s, d0, d1, r));
        &&& ks.len() == lcnt(db, k, s, d0, d1)
        &&& sum_of(ks, |l: Row| ival(l[4])) == lsum(db, k, s, d0, d1)
        &&& forall|i: int| 0 <= i < ks.len() ==> lrow_ok(#[trigger] ks[i])
    }),
{
    let l = lt(db);
    let c = |r: Row| lsel(k, s, d0, d1, r);
    let ks = keep(l, c);
    lemma_keep_members(l, c);
    assert forall|i: int| 0 <= i < ks.len() implies lrow_ok(#[trigger] ks[i]) by {
        assert(l.contains(ks[i]));
        let m = choose|m: int| 0 <= m < l.len() && l[m] == ks[i];
        assert(lrow_ok(l[m]));
    }
    lemma_sum_of_keep(l, c, lq_term(k, s, d0, d1));
    lemma_sum_of_keep(l, c, lc_term(k, s, d0, d1));
    assert forall|i: int| 0 <= i < ks.len() implies (#[trigger] lq_term(k, s, d0, d1)(ks[i])) == (|l: Row| ival(l[4]))(ks[i])
        && lc_term(k, s, d0, d1)(ks[i]) == 1 by {
        assert(l.contains(ks[i]));
        assert(c(ks[i]));
    }
    lemma_sum_of_ext(ks, lq_term(k, s, d0, d1), |l: Row| ival(l[4]));
    crate::agent::common::sums::lemma_sum_of_const(ks, lc_term(k, s, d0, d1), 1);
}

/// The SUM aggregate over the kept rows.
pub proof fn lemma_li_agg(db: Database, c: Row, ps: Seq<Literal>, d1: int)
    requires
        tables_ok(db), lt(db).len() <= 0xffff_ffff_ffff_ffff,
        c.len() == 16, is_int(c[11]), is_int(c[12]),
        param_domain(ps), d1_ok(ps, d1),
    ensures ({
        let (k, s, d0) = (ival(c[11]), ival(c[12]), d0_of(ps));
        eval_query(db, c, li_agg(ps)) == Ok::<Relation, SqlError>(seq![seq![sum_val(lcnt(db, k, s, d0, d1), lsum(db, k, s, d0, d1))]])
    }),
{
    let (k, s, d0) = (ival(c[11]), ival(c[12]), d0_of(ps));
    lemma_li_filter(db, c, ps, d1);
    let ks = keep(lt(db), li_sel(c, d0, d1));
    assert(ks == keep(lt(db), |r: Row| lsel(k, s, d0, d1, r)));
    lemma_kept_sums(db, k, s, d0, d1);
    assert forall|i: int| 0 <= i < ks.len() implies (#[trigger] ks[i]).len() == 16 by {
        assert(lrow_ok(ks[i]));
    }
    lemma_li_args(db, c, ks);
    crate::exec::relational::domain::lemma_eval_aggregate(db, c, seq![sum_agg()], Box::new(li_filter(ps)));
    assert forall|i: int| 0 <= i < ks.len() implies num2(#[trigger] ks[i][4]) by {
        assert(lrow_ok(ks[i]));
    }
    lemma_qty_sum(ks);
    let vs = qty_vals(ks);
    let n = ks.len() as int;
    let sum = sum_of(ks, |l: Row| ival(l[4]));
    let v = sum_val(n, sum);
    let args = qty_args(ks);
    let rs = Seq::new(1, |j: int| agg_value(seq![sum_agg()][j], column(args, j)));
    assert(rs[0] == agg_value(sum_agg(), vs));
    if n > 0 {
        assert(n <= lt(db).len()) by {
            crate::agent::common::sums::lemma_keep_len(lt(db), li_sel(c, d0, d1));
        }
        assert(-0x8000_0000_0000_0000_0000_0000_0000_0000 <= sum <= 0x8000_0000_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
            requires -n * p15() <= sum <= n * p15(), 1 <= n <= 0xffff_ffff_ffff_ffff, p15() == 1_000_000_000_000_000;
        lemma_num_in_range_small(sum, 2);
        assert(agg_value(sum_agg(), vs) == Ok::<Val, SqlError>(v));
    } else {
        assert(agg_value(sum_agg(), vs) == Ok::<Val, SqlError>(v));
    }
    lemma_collect_all(rs, seq![v]);
}

/// One expression on one row: its value as a one-value row.
pub proof fn lemma_one_expr(db: Database, row: Row, e: Expr)
    ensures
        eval_exprs(db, row, seq![e]) == match eval_expr(db, row, e) {
            Ok(v) => Ok::<Row, SqlError>(seq![v]),
            Err(err) => Err::<Row, SqlError>(err),
        },
{
    let exprs = seq![e];
    assert(exprs.drop_last() =~= Seq::<Expr>::empty());
    lemma_eval_exprs_step(db, row, exprs);
    lemma_eval_exprs_empty(db, row);
    if let Ok(v) = eval_expr(db, row, e) {
        assert(Seq::<Val>::empty().push(v) =~= seq![v]);
    }
}

/// `0.5 * sum` on the aggregate row.
pub proof fn lemma_half(db: Database, env: Row, n: int, s: int)
    requires
        env.len() == 17, env[16] == sum_val(n, s),
        -0x1000_0000_0000_0000_0000_0000_0000_0000 <= s <= 0x1000_0000_0000_0000_0000_0000_0000_0000,
    ensures eval_expr(db, env, half_expr()) == Ok::<Val, SqlError>(half_val(n, s)),
{
    assert(num_in_range(5, 1)) by (compute);
    assert(1 <= crate::spec::limits::numeric_dscale_max()) by (compute);
    assert(eval_expr(db, env, Expr::Lit(Literal::Num { coeff: 5, scale: 1 })) == Ok::<Val, SqlError>(Val::Num { coeff: 5, scale: 1 }));
    assert(eval_expr(db, env, Expr::Col(16)) == Ok::<Val, SqlError>(sum_val(n, s)));
    if n != 0 {
        assert(num_arith(ArithOp::Mul, 5, 1, s, 2) == (5 * s, 3nat));
        lemma_num_in_range_small(5 * s, 3);
    }
}

/// The subquery's single row.
pub proof fn lemma_li_q(db: Database, c: Row, ps: Seq<Literal>, d1: int)
    requires
        tables_ok(db), lt(db).len() <= 0xffff_ffff_ffff_ffff,
        c.len() == 16, is_int(c[11]), is_int(c[12]),
        param_domain(ps), d1_ok(ps, d1),
    ensures ({
        let (k, s, d0) = (ival(c[11]), ival(c[12]), d0_of(ps));
        &&& eval_query(db, c, li_q(ps)) == Ok::<Relation, SqlError>(seq![seq![half_val(lcnt(db, k, s, d0, d1), lsum(db, k, s, d0, d1))]])
        &&& lcnt(db, k, s, d0, d1) >= 0
    }),
{
    let (k, s, d0) = (ival(c[11]), ival(c[12]), d0_of(ps));
    let (n, sum) = (lcnt(db, k, s, d0, d1), lsum(db, k, s, d0, d1));
    lemma_li_agg(db, c, ps, d1);
    lemma_kept_sums(db, k, s, d0, d1);
    let ks = keep(lt(db), |r: Row| lsel(k, s, d0, d1, r));
    assert forall|i: int| 0 <= i < ks.len() implies num2(#[trigger] ks[i][4]) by {
        assert(lrow_ok(ks[i]));
    }
    lemma_qty_sum(ks);
    crate::agent::common::sums::lemma_keep_len(lt(db), |r: Row| lsel(k, s, d0, d1, r));
    assert(-0x1000_0000_0000_0000_0000_0000_0000_0000 <= sum <= 0x1000_0000_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
        requires -n * p15() <= sum <= n * p15(), 0 <= n <= 0xffff_ffff_ffff_ffff, p15() == 1_000_000_000_000_000;
    crate::exec::relational::domain::lemma_eval_project(db, c, seq![half_expr()], Box::new(li_agg(ps)));
    let arows = seq![seq![sum_val(n, sum)]];
    let prs = project_results(db, c, arows, seq![half_expr()]);
    let env = c + arows[0];
    assert(env[16] == sum_val(n, sum));
    lemma_half(db, env, n, sum);
    lemma_one_expr(db, env, half_expr());
    assert(prs[0] == Ok::<Row, SqlError>(seq![half_val(n, sum)]));
    lemma_collect_all(prs, seq![seq![half_val(n, sum)]]);
}

/// `ps_availqty > (subquery)`: true exactly when the lineitem rows exist and `200 * ps_availqty > lsum`; never an
/// error.
pub proof fn lemma_avail_pred(db: Database, c: Row, ps: Seq<Literal>, d1: int)
    requires
        tables_ok(db), lt(db).len() <= 0xffff_ffff_ffff_ffff,
        c.len() == 16, is_int(c[11]), is_int(c[12]), is_int(c[13]),
        param_domain(ps), d1_ok(ps, d1),
    ensures ({
        let (k, s, a, d0) = (ival(c[11]), ival(c[12]), ival(c[13]), d0_of(ps));
        &&& eval_pred(db, c, avail_pred(ps)) is Ok
        &&& (eval_pred(db, c, avail_pred(ps))->Ok_0 is True)
            == (lcnt(db, k, s, d0, d1) > 0 && 200 * a > lsum(db, k, s, d0, d1))
    }),
{
    let (k, s, a, d0) = (ival(c[11]), ival(c[12]), ival(c[13]), d0_of(ps));
    let (n, sum) = (lcnt(db, k, s, d0, d1), lsum(db, k, s, d0, d1));
    lemma_li_q(db, c, ps, d1);
    let w = half_val(n, sum);
    let lhs = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Col(13)) };
    assert(eval_expr(db, c, Expr::Col(13)) == Ok::<Val, SqlError>(Val::Int(a)));
    assert(eval_expr(db, c, lhs) == Ok::<Val, SqlError>(Val::Num { coeff: a, scale: 0 }));
    assert(subquery_value(seq![seq![w]]) == Ok::<Val, SqlError>(w));
    assert(eval_expr(db, c, Expr::Subquery(Box::new(li_q(ps)))) == Ok::<Val, SqlError>(w));
    if n != 0 {
        lemma_compare_num(a, 0, 5 * sum, 3);
        assert(pow10(3) == 1000) by (compute);
        assert(pow10(0) == 1);
        assert(align(a, 0, 3) == a * 1000);
        assert(align(5 * sum, 3, 3) == 5 * sum);
        assert((a * 1000 - 5 * sum > 0) == (200 * a > sum));
        lemma_cmp_holds_sign(CmpOp::Gt, a * 1000, 5 * sum);
    }
}

} // verus!
