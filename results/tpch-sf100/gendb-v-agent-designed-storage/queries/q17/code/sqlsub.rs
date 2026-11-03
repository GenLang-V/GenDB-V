//! The correlated subquery `(SELECT 0.2 * AVG(l_quantity) FROM lineitem WHERE l_partkey = p_partkey)` evaluated
//! under a row `x` of `lineitem x part` (25 columns, p_partkey at 16): its value is `vals::sub_val` of the lineitem
//! value rows at the part's key (`lemma_eval_sub`). On typed tables it never raises: the average of quantities
//! below `10^15` is a numeric far inside PostgreSQL's format (`lemma_avg_range`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::fns::div::*;
use crate::spec::aggs::avg::*;
use crate::link::join::*;
use crate::link::query::{proj, proj_all};
use crate::link::expr::ival;
use crate::link::source::lemma_proj_all_index;
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::fns::div::{lemma_div_round_bounds, lemma_div_scale_range};
use crate::exec::relational::domain::{filter_results, agg_args_results, project_results};
use super::vals::*;
use super::typed::*;

verus! {

// ------------------------------------------------------------------------------------------------ the AST

/// `l_partkey = p_partkey` inside the subquery (n28: inner l_partkey at 26, outer p_partkey at 16).
pub open spec fn key_pred() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(26), b: Expr::Col(16) }
}

/// `FROM lineitem WHERE l_partkey = p_partkey` (n30).
pub open spec fn sub_filter() -> Query {
    Query::Filter { pred: key_pred(), input: Box::new(Query::Table(0)) }
}

/// `AVG(l_quantity)` (n25).
pub open spec fn avg_agg() -> Agg {
    Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(29) }
}

/// The aggregate (n31).
pub open spec fn sub_agg() -> Query {
    Query::Aggregate { aggs: seq![avg_agg()], input: Box::new(sub_filter()) }
}

/// `0.2 * AVG(..)` (n23).
pub open spec fn fifth_expr() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Lit(Literal::Num { coeff: 2, scale: 1 })), b: Box::new(Expr::Col(25)) }
}

/// The subquery (n32).
pub open spec fn sub_q() -> Query {
    Query::Project { exprs: seq![fifth_expr()], input: Box::new(sub_agg()) }
}

/// The scalar subquery expression (n33).
pub open spec fn sub_expr() -> Expr {
    Expr::Subquery(Box::new(sub_q()))
}

/// Lineitem rows of key `k`.
pub open spec fn lkey(k: int) -> spec_fn(Row) -> bool {
    |l: Row| l[1] == Val::Int(k)
}

// ------------------------------------------------------------------------------------------------ the filter

/// `WHERE l_partkey = p_partkey` keeps the lineitem rows of the outer part's key `k`.
pub proof fn lemma_sub_filter(db: Database, x: Row, k: int)
    requires tables_ok(db), x.len() == 25, x[16] == Val::Int(k),
    ensures eval_query(db, x, sub_filter()) == Ok::<Relation, SqlError>(keep(db.tables[0], lkey(k))),
{
    let l = db.tables[0];
    crate::exec::relational::domain::lemma_eval_filter(db, x, key_pred(), Box::new(Query::Table(0)));
    let rs = filter_results(db, x, l, key_pred());
    let truths = Seq::new(l.len(), |i: int| truth_of(lkey(k)(l[i])));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        let env = x + l[i];
        assert(lrow_ok(l[i]));
        assert(env[26] == l[i][1]);
        assert(env[16] == x[16]);
        let a = ival(l[i][1]);
        assert(eval_expr(db, env, Expr::Col(26)) == Ok::<Val, SqlError>(Val::Int(a)));
        assert(eval_expr(db, env, Expr::Col(16)) == Ok::<Val, SqlError>(Val::Int(k)));
        assert(cmp_truth(CmpOp::Eq, Val::Int(a), Val::Int(k)) == Ok::<Truth, SqlError>(truth_of(a == k)));
    }
    lemma_collect_all(rs, truths);
    lemma_keep_true_keep(l, truths, lkey(k));
}

// ------------------------------------------------------------------------------------------------ the aggregate

/// The quantities of lineitem rows.
pub open spec fn qty_vals(ks: Seq<Row>) -> Seq<Val> {
    ks.map_values(|l: Row| l[4])
}

/// The argument rows `[l_quantity]` of lineitem rows.
pub open spec fn qty_args(ks: Seq<Row>) -> Seq<Row> {
    Seq::new(ks.len(), |i: int| seq![ks[i][4]])
}

/// Every quantity is a numeric of scale 2: all numeric, all non-NULL, exact sum at scale 2 (scale 0 when empty).
pub proof fn lemma_qty_sum(ks: Seq<Row>)
    requires forall|i: int| 0 <= i < ks.len() ==> num2(#[trigger] ks[i][4]),
    ensures
        all_of_kind(NumKind::Numeric, qty_vals(ks)),
        count_non_null(qty_vals(ks)) == ks.len(),
        num_sum(qty_vals(ks)) == (sum_of(ks, |l: Row| ival(l[4])), if ks.len() > 0 { 2nat } else { 0nat }),
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

/// The argument rows of the kept rows, collected (`env = x + row`, l_quantity at 29).
pub proof fn lemma_sub_args(db: Database, x: Row, ks: Seq<Row>)
    requires
        x.len() == 25,
        forall|i: int| 0 <= i < ks.len() ==> (#[trigger] ks[i]).len() == 16,
    ensures
        collect(agg_args_results(db, x, ks, seq![avg_agg()])) == Ok::<Seq<Row>, SqlError>(qty_args(ks)),
        column(qty_args(ks), 0) == qty_vals(ks),
{
    let rs = agg_args_results(db, x, ks, seq![avg_agg()]);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(qty_args(ks)[i]) by {
        let env = x + ks[i];
        assert(env[29] == ks[i][4]);
        let ars = agg_arg_results(db, env, seq![avg_agg()]);
        assert(ars[0] == agg_arg(db, env, avg_agg()));
        assert(agg_arg(db, env, avg_agg()) == eval_expr(db, env, Expr::Col(29)));
        lemma_collect_all(ars, seq![ks[i][4]]);
    }
    lemma_collect_all(rs, qty_args(ks));
    assert(column(qty_args(ks), 0) =~= qty_vals(ks));
}

/// The argument row of one kept row.
pub proof fn lemma_sub_arg_row(db: Database, x: Row, ks: Seq<Row>, i: int)
    requires x.len() == 25, 0 <= i < ks.len(), ks[i].len() == 16,
    ensures agg_args(db, x + ks[i], seq![avg_agg()]) == Ok::<Row, SqlError>(qty_args(ks)[i]),
{
    let env = x + ks[i];
    assert(env[29] == ks[i][4]);
    let ars = agg_arg_results(db, env, seq![avg_agg()]);
    assert(ars[0] == agg_arg(db, env, avg_agg()));
    assert(agg_arg(db, env, avg_agg()) == eval_expr(db, env, Expr::Col(29)));
    lemma_collect_all(ars, seq![ks[i][4]]);
}

/// `10^(a + b) = 10^a * 10^b`.
pub proof fn lemma_pow10_add(a: nat, b: nat)
    ensures pow10(a + b) == pow10(a) * pow10(b),
    decreases a,
{
    if a > 0 {
        lemma_pow10_add((a - 1) as nat, b);
        assert(pow10(a + b) == 10 * pow10((a - 1 + b) as nat));
        assert(10 * (pow10((a - 1) as nat) * pow10(b)) == (10 * pow10((a - 1) as nat)) * pow10(b)) by (nonlinear_arith);
    }
}

/// The average of `c >= 1` quantities summing to `s` with `|s| <= c * 10^15`: a numeric `q` at scale `r >= 2`
/// with `|q| <= 10^13 * 10^r`, and `0.2 * avg` (`2 q` at scale `r + 1`) is inside PostgreSQL's format.
pub proof fn lemma_avg_range(s: int, c: int)
    requires c >= 1, -c * p15() <= s <= c * p15(),
    ensures ({
        let r = div_scale(s, 2, c, 0);
        let q = num_div_coeff(s, 2, c, 0);
        &&& r >= 2
        &&& num_in_range(q, r)
        &&& num_div(s, 2, c, 0) == Ok::<Val, SqlError>(Val::Num { coeff: q, scale: r })
        &&& num_in_range(2 * q, r + 1)
        &&& abs(q) <= 10_000_000_000_000 * pow10(r)
    }),
{
    let r = div_scale(s, 2, c, 0);
    lemma_div_scale_range(s, 2, c, 0);
    let p = pow10(r);
    lemma_pow10_positive(r);
    assert(pow10(2) == 100) by (compute);
    assert(pow10((r + 0) as nat) == p);
    let n = abs(s) * p;
    let d = abs(c) * 100;
    assert(abs(s) <= c * p15());
    assert(n <= c * p15() * p) by (nonlinear_arith) requires n == abs(s) * p, abs(s) <= c * p15(), p >= 1;
    assert(n >= 0) by (nonlinear_arith) requires n == abs(s) * p, p >= 1;
    lemma_div_round_bounds(n, d);
    let u = div_round(n, d);
    let m = 10_000_000_000_000 * p;
    // 2 d u <= 2 n + d <= 2 d m + d, so u <= m.
    assert(2 * d * m == 2 * n + 2 * (c * p15() * p - n)) by (nonlinear_arith)
        requires d == c * 100, m == 10_000_000_000_000 * p, p15() == 1_000_000_000_000_000;
    assert(u <= m) by (nonlinear_arith)
        requires 2 * d * u <= 2 * n + d, n <= c * p15() * p, d == c * 100, m == 10_000_000_000_000 * p,
            p15() == 1_000_000_000_000_000, d >= 100, u >= 0, 2 * d * m == 2 * n + 2 * (c * p15() * p - n);
    let q = num_div_coeff(s, 2, c, 0);
    assert(q == sign(s) * sign(c) * u);
    assert(abs(q) <= u) by (nonlinear_arith) requires q == sign(s) * sign(c) * u, u >= 0, -1 <= sign(s) <= 1, sign(c) == 1;
    // |q| <= 10^13 p < 10^131072 p, and |2 q| < 10^14 p <= 10^131073 p
    lemma_pow10_add(131072, r);
    lemma_pow10_add(131073, r);
    lemma_pow10_monotone(14, 131072);
    assert(pow10(14) == 100_000_000_000_000) by (compute);
    assert(pow10(131073) == 10 * pow10(131072));
    assert(abs(q) < pow10(131072 + r)) by (nonlinear_arith)
        requires abs(q) <= 10_000_000_000_000 * p, pow10(131072 + r) == pow10(131072) * p,
            pow10(131072) >= 100_000_000_000_000, p >= 1;
    assert(abs(2 * q) < pow10(131073 + r)) by (nonlinear_arith)
        requires abs(q) <= 10_000_000_000_000 * p, pow10(131073 + r) == pow10(131073) * p,
            pow10(131073) == 10 * pow10(131072), pow10(131072) >= 100_000_000_000_000, p >= 1;
    lemma_decimal_digits_bound(abs(q), (131072 + r) as nat);
    lemma_decimal_digits_bound(abs(2 * q), (131073 + r) as nat);
    assert(crate::spec::limits::numeric_int_digits_max() == 131072) by (compute);
}

/// The quantity sum and count of key `k` over the value rows are those of the lineitem rows the subquery keeps.
pub proof fn lemma_sub_sums(db: Database, k: int)
    requires tables_ok(db),
    ensures ({
        let ks = keep(db.tables[0], lkey(k));
        &&& qcnt(ys_of(db), k) == ks.len()
        &&& qsum(ys_of(db), k) == sum_of(ks, |r: Row| ival(r[4]))
        &&& forall|i: int| 0 <= i < ks.len() ==> num2(#[trigger] ks[i][4]) && ks[i].len() == 16
    }),
{
    let l = db.tables[0];
    let ks = keep(l, lkey(k));
    let ys = ys_of(db);
    lemma_value_rows(db);
    lemma_keep_members(l, lkey(k));
    assert forall|i: int| 0 <= i < ks.len() implies num2(#[trigger] ks[i][4]) && ks[i].len() == 16 by {
        assert(l.contains(ks[i]));
        let m = choose|m: int| 0 <= m < l.len() && l[m] == ks[i];
        assert(lrow_ok(l[m]));
    }
    let pm = |r: Row| proj(r, lcols());
    lemma_proj_all_index(l, lcols());
    assert(ys == l.map_values(pm));
    lemma_sum_of_map(l, pm, tq(k));
    lemma_sum_of_map(l, pm, t1(k));
    let fq = |r: Row| if lkey(k)(r) { ival(r[4]) } else { 0int };
    let fc = |r: Row| if lkey(k)(r) { 1int } else { 0int };
    assert forall|i: int| 0 <= i < l.len() implies (|r: Row| tq(k)(pm(r)))(#[trigger] l[i]) == fq(l[i])
        && (|r: Row| t1(k)(pm(r)))(l[i]) == fc(l[i]) by {
        assert(pm(l[i])[0] == l[i][1] && pm(l[i])[1] == l[i][4]);
    }
    lemma_sum_of_ext(l, |r: Row| tq(k)(pm(r)), fq);
    lemma_sum_of_ext(l, |r: Row| t1(k)(pm(r)), fc);
    lemma_sum_of_keep(l, lkey(k), fq);
    lemma_sum_of_keep(l, lkey(k), fc);
    assert forall|i: int| 0 <= i < ks.len() implies fq(#[trigger] ks[i]) == (|r: Row| ival(r[4]))(ks[i])
        && fc(ks[i]) == 1 by {
        assert(lkey(k)(ks[i]));
    }
    lemma_sum_of_ext(ks, fq, |r: Row| ival(r[4]));
    lemma_sum_of_const(ks, fc, 1);
}

/// The AVG over the quantities of the lineitem rows of key `k`, and `0.2 *` it: `sub_val`.
pub proof fn lemma_sub_avg(db: Database, k: int)
    requires tables_ok(db), db.tables[0].len() <= 0xffff_ffff_ffff_ffff,
    ensures ({
        let ks = keep(db.tables[0], lkey(k));
        let ys = ys_of(db);
        let a = avg_value(NumKind::Numeric, qty_vals(ks));
        &&& qcnt(ys, k) == ks.len()
        &&& a is Ok
        &&& arith(ArithOp::Mul, NumKind::Numeric, Val::Num { coeff: 2, scale: 1 }, a->Ok_0) == Ok::<Val, SqlError>(sub_val(ys, k))
    }),
{
    let l = db.tables[0];
    let ks = keep(l, lkey(k));
    let ys = ys_of(db);
    lemma_value_rows(db);
    lemma_keep_members(l, lkey(k));
    assert forall|i: int| 0 <= i < ks.len() implies num2(#[trigger] ks[i][4]) by {
        assert(l.contains(ks[i]));
        let m = choose|m: int| 0 <= m < l.len() && l[m] == ks[i];
        assert(lrow_ok(l[m]));
    }
    lemma_qty_sum(ks);
    // the sums over the value rows are the sums over the kept lineitem rows
    let pm = |r: Row| proj(r, lcols());
    lemma_proj_all_index(l, lcols());
    assert(ys == l.map_values(pm));
    lemma_sum_of_map(l, pm, tq(k));
    lemma_sum_of_map(l, pm, t1(k));
    let fq = |r: Row| if lkey(k)(r) { ival(r[4]) } else { 0int };
    let fc = |r: Row| if lkey(k)(r) { 1int } else { 0int };
    assert forall|i: int| 0 <= i < l.len() implies (|r: Row| tq(k)(pm(r)))(#[trigger] l[i]) == fq(l[i])
        && (|r: Row| t1(k)(pm(r)))(l[i]) == fc(l[i]) by {
        assert(pm(l[i])[0] == l[i][1] && pm(l[i])[1] == l[i][4]);
    }
    lemma_sum_of_ext(l, |r: Row| tq(k)(pm(r)), fq);
    lemma_sum_of_ext(l, |r: Row| t1(k)(pm(r)), fc);
    lemma_sum_of_keep(l, lkey(k), fq);
    lemma_sum_of_keep(l, lkey(k), fc);
    assert forall|i: int| 0 <= i < ks.len() implies fq(#[trigger] ks[i]) == (|r: Row| ival(r[4]))(ks[i])
        && fc(ks[i]) == 1 by {
        assert(lkey(k)(ks[i]));
    }
    lemma_sum_of_ext(ks, fq, |r: Row| ival(r[4]));
    lemma_sum_of_const(ks, fc, 1);
    assert(qcnt(ys, k) == ks.len());
    let s = qsum(ys, k);
    assert(s == sum_of(ks, |r: Row| ival(r[4])));
    let vs = qty_vals(ks);
    if ks.len() > 0 {
        let c = ks.len() as int;
        lemma_qsum_bound(ys, k);
        lemma_avg_range(s, c);
        assert(c <= l.len());
        assert(abs(s) <= 0x8000_0000_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
            requires -c * p15() <= s <= c * p15(), 1 <= c <= 0xffff_ffff_ffff_ffff, p15() == 1_000_000_000_000_000;
        lemma_num_in_range_small(s, 2);
        assert(num_sum(vs) == (s, 2nat));
        assert(avg_value(NumKind::Numeric, vs) == num_div(s, 2, c, 0));
        let r = div_scale(s, 2, c, 0);
        let q = num_div_coeff(s, 2, c, 0);
        assert(num_arith(ArithOp::Mul, 2, 1, q, r) == (2 * q, (1 + r) as nat));
        assert((1 + r) as nat == r + 1);
    } else {
        assert(sub_val(ys, k) == Val::Null);
    }
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

/// The literal `0.2`.
pub proof fn lemma_lit_fifth(db: Database, env: Row)
    ensures eval_expr(db, env, Expr::Lit(Literal::Num { coeff: 2, scale: 1 })) == Ok::<Val, SqlError>(Val::Num { coeff: 2, scale: 1 }),
{
    assert(num_in_range(2, 1)) by (compute);
    assert(1 <= crate::spec::limits::numeric_dscale_max()) by (compute);
}

/// The scalar subquery under a row `x` of `lineitem x part` whose p_partkey is `k`: `sub_val` at `k`.
pub proof fn lemma_eval_sub(db: Database, x: Row, k: int)
    requires
        tables_ok(db),
        db.tables[0].len() <= 0xffff_ffff_ffff_ffff,
        x.len() == 25,
        x[16] == Val::Int(k),
    ensures eval_expr(db, x, sub_expr()) == Ok::<Val, SqlError>(sub_val(ys_of(db), k)),
{
    let l = db.tables[0];
    let ks = keep(l, lkey(k));
    lemma_sub_filter(db, x, k);
    lemma_keep_members(l, lkey(k));
    assert forall|i: int| 0 <= i < ks.len() implies (#[trigger] ks[i]).len() == 16 by {
        assert(l.contains(ks[i]));
        let m = choose|m: int| 0 <= m < l.len() && l[m] == ks[i];
        assert(lrow_ok(l[m]));
    }
    lemma_sub_args(db, x, ks);
    crate::exec::relational::domain::lemma_eval_aggregate(db, x, seq![avg_agg()], Box::new(sub_filter()));
    lemma_sub_avg(db, k);
    let a = avg_value(NumKind::Numeric, qty_vals(ks))->Ok_0;
    let args = qty_args(ks);
    let rs = Seq::new(1, |j: int| agg_value(seq![avg_agg()][j], column(args, j)));
    assert(rs[0] == agg_value(avg_agg(), column(args, 0)));
    lemma_collect_all(rs, seq![a]);
    assert(eval_query(db, x, sub_agg()) == Ok::<Relation, SqlError>(seq![seq![a]]));
    crate::exec::relational::domain::lemma_eval_project(db, x, seq![fifth_expr()], Box::new(sub_agg()));
    let arows = seq![seq![a]];
    let prs = project_results(db, x, arows, seq![fifth_expr()]);
    let env = x + seq![a];
    assert(env[25] == a);
    lemma_lit_fifth(db, env);
    assert(eval_expr(db, env, Expr::Col(25)) == Ok::<Val, SqlError>(a));
    let v = sub_val(ys_of(db), k);
    assert(eval_expr(db, env, fifth_expr()) == Ok::<Val, SqlError>(v));
    lemma_one_expr(db, env, fifth_expr());
    assert(x + arows[0] == env);
    assert(prs[0] == Ok::<Row, SqlError>(seq![v]));
    lemma_collect_all(prs, seq![seq![v]]);
    assert(eval_query(db, x, sub_q()) == Ok::<Relation, SqlError>(seq![seq![v]]));
}

} // verus!
