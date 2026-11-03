//! The uncorrelated scalar subquery `SELECT AVG(c_acctbal) FROM customer WHERE c_acctbal > 0.00 AND
//! SUBSTRING(c_phone, 1, 2) IN (..)`, evaluated in the context of any outer customer row `x` (8 positions; the
//! inner row follows them, so `c_phone` is position 12 and `c_acctbal` 13).
//!
//! - Its WHERE keeps the customer rows of the AVG population (`lemma_sub_filter`).
//! - Their balances are numeric(15,2) values: `avg_n` of them summing to the coefficient `avg_s` (scale 2,
//!   `lemma_kept_totals`), far inside PostgreSQL's numeric range.
//! - AVG is `num_div(avg_s, 2, avg_n, 0)`, NULL without rows (`avg_val`); the subquery never fails
//!   (`lemma_sub_value`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::fns::div::*;
use crate::spec::aggs::avg::*;
use crate::exec::relational::domain::*;
use crate::gendb_entry::stores::StoresView;
use crate::link::join::{keep, sum_of, lemma_keep_true_keep, lemma_keep_members, lemma_sum_of_keep, lemma_sum_of_ext};
use crate::link::expr::{ival, tval, lemma_pred_cmp, lemma_pred_and, lemma_expr_col, lemma_compare_num, lemma_align_same};
use crate::link::query::{lemma_agg_arg_avg, lemma_digits_in_range};
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::fns::div::{lemma_div_scale_range, lemma_div_round_bounds, lemma_num_div_coeff_scaled};
use crate::bridge::order::lemma_pow10_add;
use crate::agent::common::rsum::*;
use crate::agent::common::prefix2::prefix2;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::ast::*;
use crate::agent::rowsem::*;
use crate::stores::flat_customer::interface as ci;

verus! {

// ------------------------------------------------------------------------------------------------ the inner rows

/// The inner condition on a customer row value: positive balance and a hitting code.
pub open spec fn fsub(ps: Seq<Literal>) -> spec_fn(Row) -> bool {
    |r: Row| ival(r[5]) > 0 && code_hit(ps, prefix2(tval(r[4])))
}

/// The inner WHERE on one customer row, after the outer row `x`.
#[verifier::spinoff_prover]
proof fn lemma_sub_pred_row(db: Database, sv: StoresView, ps: Seq<Literal>, x: Row, i: int)
    requires ps_ok(ps), x.len() == 8, 0 <= i < n_c(sv),
    ensures eval_pred(db, x + cust_rows(sv)[i], sub_pred(ps)) == Ok::<Truth, SqlError>(truth_of(fsub(ps)(cust_rows(sv)[i]))),
{
    hide(eval_pred);
    hide(eval_expr);
    let r = cust_rows(sv)[i];
    lemma_cust_row(sv, i);
    let e = x + r;
    let c = bal(sv)[i] as int;
    assert(e[13] == r[5] && e[12] == r[4]);
    lemma_expr_col(db, e, 13);
    let zero = Literal::Num { coeff: 0, scale: 2 };
    assert(num_in_range(0, 2));
    assert(eval_expr(db, e, Expr::Lit(zero)) == Ok::<Val, SqlError>(Val::Num { coeff: 0, scale: 2 })) by {
        reveal(eval_expr);
        assert(crate::spec::limits::numeric_dscale_max() == 16383);
    }
    lemma_compare_num(c, 2, 0, 2);
    lemma_align_same(c, 2);
    lemma_align_same(0, 2);
    lemma_pred_cmp(db, e, CmpOp::Gt, Expr::Col(13), Expr::Lit(zero), Val::Num { coeff: c, scale: 2 },
        Val::Num { coeff: 0, scale: 2 }, c, 0);
    lemma_in7_eval(db, e, 12, phone(sv, i), ps);
    lemma_pred_and(db, e, Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(13), b: Expr::Lit(zero) }, in7(12, ps), c > 0,
        code_hit(ps, prefix2(phone(sv, i))));
}

/// The inner WHERE keeps the customer rows of the AVG population.
#[verifier::spinoff_prover]
pub proof fn lemma_sub_filter(db: Database, sv: StoresView, ps: Seq<Literal>, x: Row)
    requires tables_of(sv, db), ps_ok(ps), x.len() == 8,
    ensures eval_query(db, x, sub_filter(ps)) == Ok::<Relation, SqlError>(keep(cust_rows(sv), fsub(ps))),
{
    let rows = cust_rows(sv);
    let pred = sub_pred(ps);
    let f = fsub(ps);
    lemma_eval_filter(db, x, pred, Box::new(Query::Table(2)));
    assert(eval_query(db, x, Query::Table(2)) == Ok::<Relation, SqlError>(rows));
    let truths = Seq::new(rows.len(), |i: int| truth_of(f(rows[i])));
    let prs = filter_results(db, x, rows, pred);
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        lemma_sub_pred_row(db, sv, ps, x, i);
    }
    lemma_collect_all(prs, truths);
    lemma_keep_true_keep(rows, truths, f);
}

// ------------------------------------------------------------------------------------------------ totals

/// The balance values of rows (position 5).
pub open spec fn bal_col(ks: Seq<Row>) -> Seq<Val> { ks.map_values(|r: Row| r[5]) }

/// Every row holds a numeric value of scale 2 at position 5.
pub open spec fn bal_shaped(ks: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < ks.len() ==> (#[trigger] ks[i])[5] is Num && ks[i][5]->Num_scale == 2
}

/// The coefficient at position 5.
pub open spec fn bcoef() -> spec_fn(Row) -> int { |r: Row| ival(r[5]) }

/// Values of one scale 2: the count, kind and exact sum of the balance column.
#[verifier::spinoff_prover]
pub proof fn lemma_bal_col(ks: Seq<Row>)
    requires bal_shaped(ks),
    ensures
        count_non_null(bal_col(ks)) == ks.len(),
        all_of_kind(NumKind::Numeric, bal_col(ks)),
        num_sum(bal_col(ks)) == if ks.len() == 0 { (0int, 0nat) } else { (sum_of(ks, bcoef()), 2nat) },
    decreases ks.len(),
{
    if ks.len() > 0 {
        let ki = ks.drop_last();
        assert forall|i: int| 0 <= i < ki.len() implies (#[trigger] ki[i])[5] is Num && ki[i][5]->Num_scale == 2 by {
            assert(ki[i] == ks[i]);
        }
        lemma_bal_col(ki);
        let vs = bal_col(ks);
        assert(vs.drop_last() =~= bal_col(ki));
        let v = ks.last()[5];
        assert(ks.last() == ks[ks.len() - 1]);
        assert(vs.last() == v);
        let c = v->Num_coeff;
        assert(v == Val::Num { coeff: c, scale: 2 });
        assert(pow10(0) == 1);
        let acc = num_sum(bal_col(ki));
        lemma_align_same(c, 2);
        assert(sum_of(ks, bcoef()) == sum_of(ki, bcoef()) + ival(v));
        if ki.len() == 0 {
            assert(align(0, 0, 2) == 0);
        } else {
            lemma_align_same(acc.0, 2);
        }
    } else {
        assert(bal_col(ks) =~= Seq::<Val>::empty());
    }
}

/// The sum over a sequence built by `Seq::new` is the range sum of the terms of its elements.
#[verifier::spinoff_prover]
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
#[verifier::spinoff_prover]
pub proof fn lemma_sum_of_one(ks: Seq<Row>)
    ensures sum_of(ks, |r: Row| 1int) == ks.len(),
    decreases ks.len(),
{
    if ks.len() > 0 {
        lemma_sum_of_one(ks.drop_last());
    }
}

/// The kept inner rows: `avg_n` of them, their balance coefficients summing to `avg_s`, all of scale 2.
#[verifier::spinoff_prover]
pub proof fn lemma_kept_totals(sv: StoresView, ps: Seq<Literal>)
    ensures ({
        let ks = keep(cust_rows(sv), fsub(ps));
        &&& ks.len() == avg_n(sv, ps)
        &&& sum_of(ks, bcoef()) == avg_s(sv, ps)
        &&& bal_shaped(ks)
    }),
{
    let rows = cust_rows(sv);
    let f = fsub(ps);
    let ks = keep(rows, f);
    lemma_keep_members(rows, f);
    let g = |i: int| ci::row_at(sv.flat_customer, i);
    assert(rows == Seq::new(n_c(sv), g));
    // the count: 1 on kept rows, 0 elsewhere
    let one_k = |r: Row| if f(r) { 1int } else { 0int };
    assert forall|i: int| 0 <= i < rows.len() && !f(#[trigger] rows[i]) implies one_k(rows[i]) == 0 by {}
    lemma_sum_of_keep(rows, f, one_k);
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] one_k(ks[i]) == (|r: Row| 1int)(ks[i]) by {
        assert(rows.contains(ks[i]));
    }
    lemma_sum_of_ext(ks, one_k, |r: Row| 1int);
    lemma_sum_of_one(ks);
    lemma_sum_of_new(n_c(sv), g, one_k);
    let gc = |i: int| one_k(g(i));
    assert forall|l: int| 0 <= l < n_c(sv) implies #[trigger] gc(l) == avg_cnt_term(sv, ps)(l) by {
        lemma_cust_row(sv, l);
        assert(g(l) == rows[l]);
    }
    lemma_range_sum_ext(0, n_c(sv) as int, gc, avg_cnt_term(sv, ps));
    // the balance sum: the coefficient on kept rows, 0 elsewhere
    let q_k = |r: Row| if f(r) { ival(r[5]) } else { 0int };
    assert forall|i: int| 0 <= i < rows.len() && !f(#[trigger] rows[i]) implies q_k(rows[i]) == 0 by {}
    lemma_sum_of_keep(rows, f, q_k);
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] q_k(ks[i]) == bcoef()(ks[i]) by {
        assert(rows.contains(ks[i]));
    }
    lemma_sum_of_ext(ks, q_k, bcoef());
    lemma_sum_of_new(n_c(sv), g, q_k);
    let gq = |i: int| q_k(g(i));
    assert forall|l: int| 0 <= l < n_c(sv) implies #[trigger] gq(l) == avg_sum_term(sv, ps)(l) by {
        lemma_cust_row(sv, l);
        assert(g(l) == rows[l]);
    }
    lemma_range_sum_ext(0, n_c(sv) as int, gq, avg_sum_term(sv, ps));
    // every kept row has a scale-2 balance
    assert forall|i: int| 0 <= i < ks.len() implies (#[trigger] ks[i])[5] is Num && ks[i][5]->Num_scale == 2 by {
        assert(rows.contains(ks[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == ks[i];
        lemma_cust_row(sv, m);
    }
}

/// `10^15 * 2^61`, a bound of every balance sum.
pub open spec fn sum_bound() -> int { 2_305_843_009_213_693_952_000_000_000_000_000 }

/// The AVG population's totals: `0 <= avg_n <= n_c`, `0 <= avg_s < 10^15 * avg_n`, far inside `i128`.
#[verifier::spinoff_prover]
pub proof fn lemma_avg_totals(sv: StoresView, ps: Seq<Literal>)
    requires model_ok(sv), sizes_ok(sv),
    ensures
        0 <= avg_n(sv, ps) <= n_c(sv),
        0 <= avg_s(sv, ps) <= 999_999_999_999_999 * avg_n(sv, ps),
        avg_s(sv, ps) < sum_bound(),
{
    let n = n_c(sv) as int;
    lemma_range_sum_bounds(0, n, avg_cnt_term(sv, ps), 0, 1);
    lemma_avg_pair(sv, ps, n);
    let a = avg_n(sv, ps);
    assert(999_999_999_999_999 * a < sum_bound()) by (nonlinear_arith)
        requires 0 <= a <= 0x1fff_ffff_ffff_ffff;
}

/// Prefix form of the AVG bounds: the balance sum of rows `[0, m)` is in `[0, (10^15 - 1) * count]`.
#[verifier::spinoff_prover]
proof fn lemma_avg_pair(sv: StoresView, ps: Seq<Literal>, m: int)
    requires model_ok(sv), 0 <= m <= n_c(sv),
    ensures
        0 <= range_sum(0, m, avg_sum_term(sv, ps)),
        range_sum(0, m, avg_sum_term(sv, ps)) <= 999_999_999_999_999 * range_sum(0, m, avg_cnt_term(sv, ps)),
    decreases m,
{
    if m > 0 {
        lemma_avg_pair(sv, ps, m - 1);
        assert(num15(bal(sv)[m - 1]));
    }
}

/// `10^35` bounds the balance sums.
#[verifier::spinoff_prover]
pub proof fn lemma_sum_bound_small()
    ensures sum_bound() < 0x8000_0000_0000_0000_0000_0000_0000_0000, sum_bound() < pow10(35),
{
    assert(pow10(35) == 100_000_000_000_000_000_000_000_000_000_000_000) by (compute);
}

/// A quotient of a dividend at scale 2 by a positive count: `|coeff| <= |c1| * 10^(r - 2)` with `r >= 2`.
#[verifier::spinoff_prover]
pub proof fn lemma_div_coeff_bound(c1: int, c2: int)
    requires c2 >= 1,
    ensures
        2 <= div_scale(c1, 2, c2, 0) <= 1000,
        abs(num_div_coeff(c1, 2, c2, 0)) <= abs(c1) * pow10((div_scale(c1, 2, c2, 0) - 2) as nat),
{
    lemma_div_scale_range(c1, 2, c2, 0);
    lemma_num_div_coeff_scaled(c1, 2, c2, 0);
    let r = div_scale(c1, 2, c2, 0);
    let kk = (r - 2) as nat;
    assert(r + 0 - 2 == kk);
    let p = pow10(kk);
    lemma_pow10_positive(kk);
    let n = abs(c1) * p;
    assert(n >= 0) by (nonlinear_arith) requires abs(c1) >= 0, p >= 1, n == abs(c1) * p;
    let q = div_round(n, c2);
    assert(abs(c2) == c2);
    lemma_div_round_bounds(n, c2);
    assert(q <= n) by (nonlinear_arith) requires 2 * c2 * q <= 2 * n + c2, c2 >= 1, n >= 0, q >= 0;
    let s = sign(c1) * sign(c2) * q;
    assert(num_div_coeff(c1, 2, c2, 0) == s);
    assert(sign(c2) == 1);
    let sg = sign(c1);
    assert(-1 <= sg <= 1);
    assert(s == sg * q) by (nonlinear_arith) requires s == sg * sign(c2) * q, sign(c2) == 1;
    assert(abs(s) <= q) by (nonlinear_arith) requires s == sg * q, -1 <= sg <= 1, q >= 0;
}

/// With a non-empty population, the sum is in range and the division succeeds.
#[verifier::spinoff_prover]
pub proof fn lemma_avg_in_range(sv: StoresView, ps: Seq<Literal>)
    requires model_ok(sv), sizes_ok(sv), avg_n(sv, ps) > 0,
    ensures
        num_in_range(avg_s(sv, ps), 2),
        num_div(avg_s(sv, ps), 2, avg_n(sv, ps), 0) == Ok::<Val, SqlError>(avg_val(sv, ps)),
{
    let s = avg_s(sv, ps);
    let c = avg_n(sv, ps);
    lemma_avg_totals(sv, ps);
    lemma_sum_bound_small();
    lemma_num_in_range_small(s, 2);
    lemma_div_coeff_bound(s, c);
    let r = div_scale(s, 2, c, 0);
    let kk = (r - 2) as nat;
    let a = num_div_coeff(s, 2, c, 0);
    lemma_pow10_positive(kk);
    lemma_pow10_add(35, kk);
    let p = pow10(kk);
    assert(abs(s) < pow10(35));
    assert(abs(a) < pow10(35) * p) by (nonlinear_arith)
        requires abs(a) <= abs(s) * p, abs(s) < pow10(35), p >= 1;
    assert(35 + kk == r + 33);
    assert(crate::spec::limits::numeric_int_digits_max() == 131072);
    lemma_digits_in_range(a, r, (r + 33) as nat);
}

// ------------------------------------------------------------------------------------------------ the subquery

/// The aggregate arguments of the kept inner rows (each the one-value row of its balance).
pub open spec fn sub_args(ks: Seq<Row>) -> Seq<Row> { ks.map_values(|r: Row| seq![r[5]]) }

/// The AVG argument of one inner row `r` in context `x`: its balance.
#[verifier::spinoff_prover]
pub proof fn lemma_sub_arg_row(db: Database, x: Row, r: Row)
    requires x.len() == 8, r.len() == 8,
    ensures agg_args(db, x + r, sub_aggs()) == Ok::<Row, SqlError>(seq![r[5]]),
{
    hide(eval_expr);
    hide(agg_arg);
    hide(collect);
    hide(agg_arg_results);
    let e = x + r;
    let aggs = sub_aggs();
    assert(e[13] == r[5]);
    lemma_expr_col(db, e, 13);
    lemma_agg_arg_avg(db, e, NumKind::Numeric, Expr::Col(13));
    let ar = agg_arg_results(db, e, aggs);
    lemma_agg_arg_results_index(db, e, aggs);
    assert(aggs[0] == Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(13) });
    assert(ar[0] == Ok::<Val, SqlError>(r[5]));
    lemma_collect_all(ar, seq![r[5]]);
    reveal(collect);
    lemma_agg_args(db, e, aggs);
}

/// The AVG arguments of the kept inner rows, in context `x`.
#[verifier::spinoff_prover]
proof fn lemma_sub_args(db: Database, x: Row, ks: Seq<Row>)
    requires x.len() == 8, forall|i: int| 0 <= i < ks.len() ==> (#[trigger] ks[i]).len() == 8,
    ensures collect(agg_args_results(db, x, ks, sub_aggs())) == Ok::<Seq<Row>, SqlError>(sub_args(ks)),
{
    hide(agg_args);
    hide(collect);
    let rs = agg_args_results(db, x, ks, sub_aggs());
    let args = sub_args(ks);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(args[i]) by {
        lemma_sub_arg_row(db, x, ks[i]);
    }
    lemma_collect_all(rs, args);
}

/// AVG over the argument rows of the kept inner rows.
#[verifier::spinoff_prover]
proof fn lemma_sub_avg(sv: StoresView, ps: Seq<Literal>)
    requires model_ok(sv), sizes_ok(sv),
    ensures agg_row(sub_aggs(), sub_args(keep(cust_rows(sv), fsub(ps)))) == Ok::<Row, SqlError>(seq![avg_val(sv, ps)]),
{
    let ks = keep(cust_rows(sv), fsub(ps));
    lemma_kept_totals(sv, ps);
    let aggs = sub_aggs();
    let args = sub_args(ks);
    lemma_agg_row(aggs, args);
    let col = column(args, 0);
    assert(col =~= bal_col(ks));
    lemma_bal_col(ks);
    let vr = agg_value_results(aggs, args);
    assert(vr.len() == 1);
    assert(vr[0] == avg_value(NumKind::Numeric, bal_col(ks)));
    if avg_n(sv, ps) > 0 {
        lemma_avg_in_range(sv, ps);
    }
    assert(vr[0] == Ok::<Val, SqlError>(avg_val(sv, ps)));
    lemma_collect_all(vr, seq![avg_val(sv, ps)]);
}

/// `AVG(c_acctbal)` over the kept inner rows, in context `x`.
#[verifier::spinoff_prover]
pub proof fn lemma_sub_agg(db: Database, sv: StoresView, ps: Seq<Literal>, x: Row)
    requires tables_of(sv, db), model_ok(sv), sizes_ok(sv), ps_ok(ps), x.len() == 8,
    ensures eval_query(db, x, sub_agg(ps)) == Ok::<Relation, SqlError>(seq![seq![avg_val(sv, ps)]]),
{
    hide(eval_query);
    hide(agg_row);
    hide(collect);
    lemma_sub_filter(db, sv, ps, x);
    let rows = cust_rows(sv);
    let ks = keep(rows, fsub(ps));
    lemma_keep_members(rows, fsub(ps));
    assert forall|i: int| 0 <= i < ks.len() implies (#[trigger] ks[i]).len() == 8 by {
        assert(rows.contains(ks[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == ks[i];
        lemma_cust_row(sv, m);
    }
    lemma_sub_args(db, x, ks);
    lemma_sub_avg(sv, ps);
    lemma_eval_aggregate(db, x, sub_aggs(), Box::new(sub_filter(ps)));
}

/// One evaluation step of a scalar subquery over its evaluated rows.
#[verifier::spinoff_prover]
proof fn lemma_subquery_node(db: Database, env: Row, q: Query, rows: Relation)
    requires eval_query(db, env, q) == Ok::<Relation, SqlError>(rows),
    ensures eval_expr(db, env, Expr::Subquery(Box::new(q))) == subquery_value(rows),
{
}

/// The scalar subquery expression in context `x` is `avg_val`.
#[verifier::spinoff_prover]
pub proof fn lemma_sub_value(db: Database, sv: StoresView, ps: Seq<Literal>, x: Row)
    requires tables_of(sv, db), model_ok(sv), sizes_ok(sv), ps_ok(ps), x.len() == 8,
    ensures eval_expr(db, x, Expr::Subquery(Box::new(sub_agg(ps)))) == Ok::<Val, SqlError>(avg_val(sv, ps)),
{
    hide(eval_query);
    hide(eval_expr);
    lemma_sub_agg(db, sv, ps, x);
    lemma_subquery_node(db, x, sub_agg(ps), seq![seq![avg_val(sv, ps)]]);
}

} // verus!
