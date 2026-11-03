//! The correlated subquery `SELECT 0.2 * AVG(l_quantity) FROM lineitem WHERE l_partkey = p_partkey`, evaluated
//! with an outer joined row `x` whose `p_partkey` (position 16) is `k`.
//!
//! - Its inner WHERE keeps the lineitem rows with part key `k` (`lemma_sub_filter`).
//! - Their quantities are numeric(15,2) values: `kcnt(k)` of them, summing to the coefficient `ksum(k)` at scale 2
//!   (`lemma_qty_col`); the sum is far inside PostgreSQL's numeric range.
//! - AVG is PostgreSQL's numeric division `num_div(ksum, 2, kcnt, 0)`: the coefficient `avg_coeff(k)` at scale
//!   `avg_scale(k)` (NULL without rows); `0.2 * AVG` is `2 * avg_coeff(k)` at scale `avg_scale(k) + 1`
//!   (`sub_val`). Every step is in range, so the subquery never fails (`lemma_sub_value`).
//! - Outside the executable domain of that division the subquery is outside the capacity domain
//!   (`lemma_sub_capacity`).
//!
//! Counts and sums are range sums over the lineitem rows (`common::selection::range_sum`), so the scan can
//! compute them per row range.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::fns::div::*;
use crate::spec::aggs::avg::*;
use crate::exec::domain::*;
use crate::exec::relational::domain::*;
use crate::gendb_entry::stores::StoresView;
use crate::link::join::{keep, sum_of, lemma_keep_true_keep, lemma_keep_members, lemma_sum_of_keep, lemma_sum_of_ext};
use crate::link::expr::{ival, lemma_pred_cmp, lemma_compare_int, lemma_align_same};
use crate::link::query::lemma_agg_arg_avg;
use crate::link::query::lemma_digits_in_range;
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::bridge::fns::div::{lemma_div_scale_range, lemma_div_round_bounds, lemma_num_div_coeff_scaled};
use crate::bridge::order::lemma_pow10_add;
use crate::agent::tables::*;
use crate::agent::ast::*;
use crate::agent::common::selection::*;
use crate::stores::flat_lineitem::interface as li;

verus! {

// ------------------------------------------------------------------------------------------------ per-key totals

/// Per-row terms: the row has part key `k` (1 or 0), and its quantity coefficient when it does.
pub open spec fn kcnt_term(sv: StoresView, k: int) -> spec_fn(int) -> int {
    |l: int| if l_pkey(sv)[l] as int == k { 1int } else { 0int }
}
pub open spec fn kqty_term(sv: StoresView, k: int) -> spec_fn(int) -> int {
    |l: int| if l_pkey(sv)[l] as int == k { l_qty(sv)[l] as int } else { 0int }
}

/// The number of lineitem rows with part key `k`, and the sum of their quantity coefficients (scale 2).
pub open spec fn kcnt(sv: StoresView, k: int) -> int { range_sum(0, n_l(sv) as int, kcnt_term(sv, k)) }
pub open spec fn ksum(sv: StoresView, k: int) -> int { range_sum(0, n_l(sv) as int, kqty_term(sv, k)) }

/// `AVG(l_quantity)` of key `k` (when `kcnt(k) > 0`): coefficient and scale of `num_div(ksum, 2, kcnt, 0)`.
pub open spec fn avg_scale(sv: StoresView, k: int) -> nat { div_scale(ksum(sv, k), 2, kcnt(sv, k), 0) }
pub open spec fn avg_coeff(sv: StoresView, k: int) -> int { num_div_coeff(ksum(sv, k), 2, kcnt(sv, k), 0) }

/// The subquery's value for the outer part key `k`: `0.2 * AVG`, or NULL without rows.
pub open spec fn sub_val(sv: StoresView, k: int) -> Val {
    if kcnt(sv, k) == 0 {
        Val::Null
    } else {
        Val::Num { coeff: 2 * avg_coeff(sv, k), scale: avg_scale(sv, k) + 1 }
    }
}

/// The row count fits a machine word (the stored parts are machine arrays).
pub open spec fn sizes_ok(sv: StoresView) -> bool {
    n_l(sv) <= usize::MAX as int
}

/// `10^15 * 2^64`, a bound of every quantity or price sum.
pub open spec fn sum_bound() -> int { 18_446_744_073_709_551_616_000_000_000_000_000 }

// ------------------------------------------------------------------------------------------------ bounds

/// Range sums of the per-key terms: the count is in `[0, hi - lo]` and the quantity sum is bounded by the count.
pub proof fn lemma_kterm_bounds(sv: StoresView, k: int, lo: int, hi: int)
    requires lo <= hi, 0 <= lo, hi <= n_l(sv), domains_ok(sv),
    ensures
        0 <= range_sum(lo, hi, kcnt_term(sv, k)) <= hi - lo,
        -999_999_999_999_999 * range_sum(lo, hi, kcnt_term(sv, k)) <= range_sum(lo, hi, kqty_term(sv, k))
            <= 999_999_999_999_999 * range_sum(lo, hi, kcnt_term(sv, k)),
    decreases hi - lo,
{
    if hi > lo {
        lemma_kterm_bounds(sv, k, lo, hi - 1);
        assert(num15(l_qty(sv)[hi - 1]));
    }
}

/// The totals of every key are bounded: at most `n_l` rows, `|ksum| <= kcnt * (10^15 - 1)`, both far inside
/// `i128`.
pub proof fn lemma_ktotals_bounds(sv: StoresView, k: int)
    requires domains_ok(sv), sizes_ok(sv),
    ensures
        0 <= kcnt(sv, k) <= n_l(sv),
        -999_999_999_999_999 * kcnt(sv, k) <= ksum(sv, k) <= 999_999_999_999_999 * kcnt(sv, k),
        -sum_bound() < ksum(sv, k) < sum_bound(),
{
    lemma_kterm_bounds(sv, k, 0, n_l(sv) as int);
    let c = kcnt(sv, k);
    assert(999_999_999_999_999 * c < sum_bound()) by (nonlinear_arith)
        requires 0 <= c <= 0xffff_ffff_ffff_ffff;
}

/// `sum_bound() < 2^127`.
pub proof fn lemma_sum_bound_small()
    ensures sum_bound() < 0x8000_0000_0000_0000_0000_0000_0000_0000, sum_bound() < pow10(35),
{
    assert(pow10(35) == 100_000_000_000_000_000_000_000_000_000_000_000) by (compute);
}

/// A numeric quotient of a dividend at scale 2 by a positive count: `|coeff| <= |c1| * 10^(r - 2)` with the
/// result scale `r >= 2`.
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
    // 2 * c2 * q <= 2 * n + c2 with c2 >= 1 gives q <= n
    assert(q <= n) by (nonlinear_arith) requires 2 * c2 * q <= 2 * n + c2, c2 >= 1, n >= 0, q >= 0;
    let s = sign(c1) * sign(c2) * q;
    assert(num_div_coeff(c1, 2, c2, 0) == s);
    assert(sign(c2) == 1);
    assert((r + 0 - 2) as nat == kk);
    assert(abs(c2) == c2);
    let sg = sign(c1);
    assert(-1 <= sg <= 1);
    assert(s == sg * q) by (nonlinear_arith) requires s == sg * sign(c2) * q, sign(c2) == 1;
    assert(abs(s) <= q) by (nonlinear_arith) requires s == sg * q, -1 <= sg <= 1, q >= 0;
}

/// With a non-empty key, AVG and `0.2 * AVG` are in range and the division succeeds.
pub proof fn lemma_avg_in_range(sv: StoresView, k: int)
    requires domains_ok(sv), sizes_ok(sv), kcnt(sv, k) > 0,
    ensures
        num_in_range(ksum(sv, k), 2),
        num_div(ksum(sv, k), 2, kcnt(sv, k), 0) == Ok::<Val, SqlError>(Val::Num { coeff: avg_coeff(sv, k), scale: avg_scale(sv, k) }),
        num_in_range(2 * avg_coeff(sv, k), avg_scale(sv, k) + 1),
        2 <= avg_scale(sv, k) <= 1000,
{
    let s = ksum(sv, k);
    let c = kcnt(sv, k);
    lemma_ktotals_bounds(sv, k);
    lemma_sum_bound_small();
    lemma_num_in_range_small(s, 2);
    lemma_div_coeff_bound(s, c);
    let r = avg_scale(sv, k);
    let kk = (r - 2) as nat;
    let a = avg_coeff(sv, k);
    // |a| <= |s| * 10^(r-2) < 10^35 * 10^(r-2) = 10^(r+33)
    lemma_pow10_positive(kk);
    lemma_pow10_add(35, kk);
    let p = pow10(kk);
    assert(abs(a) < pow10(35) * p) by (nonlinear_arith)
        requires abs(a) <= abs(s) * p, abs(s) < pow10(35), p >= 1;
    assert(35 + kk == r + 33);
    assert(crate::spec::limits::numeric_int_digits_max() == 131072);
    lemma_digits_in_range(a, r, (r + 33) as nat);
    // 0.2 * AVG: |2a| < 2 * 10^(r+33) <= 10^(r+34)
    lemma_pow10_add(1, (r + 33) as nat);
    assert(pow10(1) == 10) by (compute);
    assert(abs(2 * a) < pow10((r + 34) as nat)) by (nonlinear_arith)
        requires abs(a) < pow10((r + 33) as nat), pow10((r + 34) as nat) == 10 * pow10((r + 33) as nat);
    lemma_digits_in_range(2 * a, r + 1, (r + 34) as nat);
}

// ------------------------------------------------------------------------------------------------ the inner rows

/// The inner condition: the lineitem row has part key `k`.
pub open spec fn kf(k: int) -> spec_fn(Row) -> bool { |r: Row| r[1] == Val::Int(k) }

/// The inner WHERE keeps the lineitem rows with part key `k`.
pub proof fn lemma_sub_filter(db: Database, sv: StoresView, x: Row, k: int)
    requires tables_of(sv, db), x.len() == 25, x[16] == Val::Int(k),
    ensures eval_query(db, x, sub_filter()) == Ok::<Relation, SqlError>(keep(line_rows(sv), kf(k))),
{
    let rows = line_rows(sv);
    assert(eval_query(db, x, Query::Table(0)) == Ok::<Relation, SqlError>(rows));
    let pred = sub_key_pred();
    let f = kf(k);
    let truths = Seq::new(rows.len(), |i: int| truth_of(f(rows[i])));
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, x + rows[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        let r = rows[i];
        assert(r == li::row_at(sv.flat_lineitem, i));
        let e = x + r;
        let pk = l_pkey(sv)[i] as int;
        assert(r[1] == Val::Int(pk));
        assert(e[26] == r[1]);
        assert(e[16] == x[16]);
        assert(eval_expr(db, e, Expr::Col(26)) == Ok::<Val, SqlError>(Val::Int(pk)));
        assert(eval_expr(db, e, Expr::Col(16)) == Ok::<Val, SqlError>(Val::Int(k)));
        lemma_compare_int(pk, k);
        lemma_pred_cmp(db, e, CmpOp::Eq, Expr::Col(26), Expr::Col(16), Val::Int(pk), Val::Int(k), pk, k);
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

/// The kept inner rows: `kcnt(k)` of them, their quantity coefficients summing to `ksum(k)`, all of scale 2.
pub proof fn lemma_kept_totals(sv: StoresView, k: int)
    requires stores_wf(sv),
    ensures ({
        let ks = keep(line_rows(sv), kf(k));
        &&& ks.len() == kcnt(sv, k)
        &&& sum_of(ks, qcoef()) == ksum(sv, k)
        &&& qty_shaped(ks)
    }),
{
    let rows = line_rows(sv);
    let f = kf(k);
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
    assert forall|l: int| 0 <= l < n_l(sv) implies #[trigger] gc(l) == kcnt_term(sv, k)(l) by {
        assert(g(l)[1] == Val::Int(l_pkey(sv)[l] as int));
    }
    lemma_range_sum_ext(0, n_l(sv) as int, gc, kcnt_term(sv, k));
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
    assert forall|l: int| 0 <= l < n_l(sv) implies #[trigger] gq(l) == kqty_term(sv, k)(l) by {
        assert(g(l)[1] == Val::Int(l_pkey(sv)[l] as int));
        assert(g(l)[4] == Val::Num { coeff: l_qty(sv)[l] as int, scale: 2 });
    }
    lemma_range_sum_ext(0, n_l(sv) as int, gq, kqty_term(sv, k));
    // every row has a scale-2 quantity
    assert forall|i: int| 0 <= i < ks.len() implies (#[trigger] ks[i])[4] is Num && ks[i][4]->Num_scale == 2 by {
        assert(rows.contains(ks[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == ks[i];
        assert(rows[m] == li::row_at(sv.flat_lineitem, m));
    }
}

// ------------------------------------------------------------------------------------------------ the subquery

/// AVG over the key's rows: NULL without rows, else the quotient.
pub open spec fn avg_val(sv: StoresView, k: int) -> Val {
    if kcnt(sv, k) == 0 { Val::Null } else { Val::Num { coeff: avg_coeff(sv, k), scale: avg_scale(sv, k) } }
}

/// The aggregate arguments of the kept inner rows (each the one-value row of its quantity).
pub open spec fn sub_args(ks: Seq<Row>) -> Seq<Row> { ks.map_values(|r: Row| seq![r[4]]) }

/// Position 29 of the context followed by an inner row is the inner row's quantity.
proof fn lemma_col_29(db: Database, x: Row, r: Row)
    requires x.len() == 25, r.len() == 16,
    ensures eval_expr(db, x + r, Expr::Col(29)) == Ok::<Val, SqlError>(r[4]),
{
    assert((x + r)[29] == r[4]);
}

/// The AVG argument of one inner row `r` in context `x`: its quantity.
pub proof fn lemma_sub_arg_row(db: Database, x: Row, r: Row)
    requires x.len() == 25, r.len() == 16,
    ensures agg_args(db, x + r, sub_aggs()) == Ok::<Row, SqlError>(seq![r[4]]),
{
    hide(eval_expr);
    hide(agg_arg);
    hide(collect);
    hide(agg_arg_results);
    let e = x + r;
    let aggs = sub_aggs();
    lemma_col_29(db, x, r);
    lemma_agg_arg_avg(db, e, NumKind::Numeric, Expr::Col(29));
    let ar = agg_arg_results(db, e, aggs);
    lemma_agg_arg_results_index(db, e, aggs);
    assert(aggs[0] == Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(29) });
    assert(ar[0] == Ok::<Val, SqlError>(r[4]));
    lemma_collect_all(ar, seq![r[4]]);
    reveal(collect);
    lemma_agg_args(db, e, aggs);
}

/// The AVG arguments of the kept inner rows, in context `x`.
proof fn lemma_sub_args(db: Database, sv: StoresView, x: Row, ks: Seq<Row>)
    requires x.len() == 25, forall|i: int| 0 <= i < ks.len() ==> (#[trigger] ks[i]).len() == 16,
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

/// AVG over the argument rows of the kept inner rows of key `k`.
proof fn lemma_sub_avg(sv: StoresView, k: int)
    requires model_ok(sv), sizes_ok(sv),
    ensures agg_row(sub_aggs(), sub_args(keep(line_rows(sv), kf(k)))) == Ok::<Row, SqlError>(seq![avg_val(sv, k)]),
{
    let ks = keep(line_rows(sv), kf(k));
    lemma_kept_totals(sv, k);
    let aggs = sub_aggs();
    let args = sub_args(ks);
    crate::exec::relational::domain::lemma_agg_row(aggs, args);
    let col = column(args, 0);
    assert(col =~= qty_col(ks));
    lemma_qty_col(ks);
    let vr = agg_value_results(aggs, args);
    assert(vr.len() == 1);
    assert(vr[0] == avg_value(NumKind::Numeric, qty_col(ks)));
    if kcnt(sv, k) > 0 {
        lemma_avg_in_range(sv, k);
    }
    assert(vr[0] == Ok::<Val, SqlError>(avg_val(sv, k)));
    lemma_collect_all(vr, seq![avg_val(sv, k)]);
}

/// `AVG(l_quantity)` over the kept inner rows, in context `x`.
pub proof fn lemma_sub_agg(db: Database, sv: StoresView, x: Row, k: int)
    requires tables_of(sv, db), model_ok(sv), sizes_ok(sv), x.len() == 25, x[16] == Val::Int(k),
    ensures eval_query(db, x, sub_agg()) == Ok::<Relation, SqlError>(seq![seq![avg_val(sv, k)]]),
{
    hide(eval_query);
    hide(agg_row);
    hide(collect);
    lemma_sub_filter(db, sv, x, k);
    let rows = line_rows(sv);
    let ks = keep(rows, kf(k));
    lemma_keep_members(rows, kf(k));
    assert forall|i: int| 0 <= i < ks.len() implies (#[trigger] ks[i]).len() == 16 by {
        assert(rows.contains(ks[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == ks[i];
        assert(rows[m] == li::row_at(sv.flat_lineitem, m));
    }
    lemma_sub_args(db, sv, x, ks);
    lemma_sub_avg(sv, k);
    lemma_eval_aggregate(db, x, sub_aggs(), Box::new(sub_filter()));
}

/// The literal `0.2`.
proof fn lemma_fifth_lit(db: Database, e: Row)
    ensures eval_expr(db, e, Expr::Lit(fifth_lit())) == Ok::<Val, SqlError>(Val::Num { coeff: 2, scale: 1 }),
{
    lemma_num_in_range_small(2, 1);
    assert(crate::spec::limits::numeric_dscale_max() == 16383);
}

/// `0.2 * AVG` as values: the subquery's value.
proof fn lemma_sub_mul_val(sv: StoresView, k: int)
    requires model_ok(sv), sizes_ok(sv),
    ensures arith(ArithOp::Mul, NumKind::Numeric, Val::Num { coeff: 2, scale: 1 }, avg_val(sv, k)) == Ok::<Val, SqlError>(sub_val(sv, k)),
{
    lemma_ktotals_bounds(sv, k);
    if kcnt(sv, k) > 0 {
        lemma_avg_in_range(sv, k);
        let c = avg_coeff(sv, k);
        let sc = avg_scale(sv, k);
        assert(num_arith(ArithOp::Mul, 2, 1, c, sc) == (2 * c, 1 + sc));
        assert(1 + sc == sc + 1);
        assert(num_in_range(2 * c, 1 + sc));
        assert(num_result(2 * c, 1 + sc) == Ok::<Val, SqlError>(Val::Num { coeff: 2 * c, scale: 1 + sc }));
        assert(sub_val(sv, k) == Val::Num { coeff: 2 * c, scale: 1 + sc });
        assert(avg_val(sv, k) == Val::Num { coeff: c, scale: sc });
        assert(arith(ArithOp::Mul, NumKind::Numeric, Val::Num { coeff: 2, scale: 1 }, Val::Num { coeff: c, scale: sc })
            == num_result(2 * c, 1 + sc));
    } else {
        assert(avg_val(sv, k) == Val::Null);
        assert(sub_val(sv, k) == Val::Null);
    }
}

/// `0.2 * AVG` on the aggregate row: the subquery's value.
proof fn lemma_sub_mul_expr(db: Database, sv: StoresView, x: Row, k: int)
    requires model_ok(sv), sizes_ok(sv), x.len() == 25,
    ensures eval_expr(db, x + seq![avg_val(sv, k)], sub_mul()) == Ok::<Val, SqlError>(sub_val(sv, k)),
{
    hide(arith);
    hide(lit_val);
    let a = avg_val(sv, k);
    let e = x + seq![a];
    assert(e[25] == a);
    assert(eval_expr(db, e, Expr::Col(25)) == Ok::<Val, SqlError>(a));
    lemma_fifth_lit(db, e);
    lemma_sub_mul_val(sv, k);
}

/// The projection list `[0.2 * AVG]` on the aggregate row.
proof fn lemma_sub_mul(db: Database, sv: StoresView, x: Row, k: int)
    requires model_ok(sv), sizes_ok(sv), x.len() == 25,
    ensures eval_exprs(db, x + seq![avg_val(sv, k)], seq![sub_mul()]) == Ok::<Row, SqlError>(seq![sub_val(sv, k)]),
{
    hide(eval_expr);
    let e = x + seq![avg_val(sv, k)];
    lemma_sub_mul_expr(db, sv, x, k);
    let es = seq![sub_mul()];
    let er = expr_results(db, e, es);
    lemma_expr_results_index(db, e, es);
    lemma_collect_all(er, seq![sub_val(sv, k)]);
}

/// The subquery in context `x`: the one row `[sub_val(k)]`.
pub proof fn lemma_sub_query(db: Database, sv: StoresView, x: Row, k: int)
    requires tables_of(sv, db), model_ok(sv), sizes_ok(sv), x.len() == 25, x[16] == Val::Int(k),
    ensures eval_query(db, x, sub_q()) == Ok::<Relation, SqlError>(seq![seq![sub_val(sv, k)]]),
{
    hide(eval_query);
    hide(eval_exprs);
    hide(collect);
    lemma_sub_agg(db, sv, x, k);
    let a = avg_val(sv, k);
    let es = seq![sub_mul()];
    lemma_eval_project(db, x, es, Box::new(sub_agg()));
    lemma_sub_mul(db, sv, x, k);
    let rows = seq![seq![a]];
    let pr = project_results(db, x, rows, es);
    assert(pr.len() == 1);
    assert(pr[0] == eval_exprs(db, x + rows[0], es));
    lemma_collect_all(pr, seq![seq![sub_val(sv, k)]]);
}

/// The scalar subquery expression in context `x` is `sub_val(k)`.
pub proof fn lemma_sub_value(db: Database, sv: StoresView, x: Row, k: int)
    requires tables_of(sv, db), model_ok(sv), sizes_ok(sv), x.len() == 25, x[16] == Val::Int(k),
    ensures eval_expr(db, x, Expr::Subquery(Box::new(sub_q()))) == Ok::<Val, SqlError>(sub_val(sv, k)),
{
    lemma_sub_query(db, sv, x, k);
}

} // verus!
