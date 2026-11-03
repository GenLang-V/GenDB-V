//! SQL meaning of TPC-H Q8, part 4: the statement's outcome from the per-year group sums.
//!
//! With `zs = inner_rows(db, ps)` and the year groups `ykey(1995)`, `ykey(1996)` (`norm::lemma_group_keys`: the only
//! ones), the outcome is decided by each present group's counts, sums and absolute volume mass (`gmass`):
//! - a mass above `i128::MAX` puts SUM(volume) outside its capacity condition (`lemma_cap_mass`);
//! - otherwise every sum is exact, and a present group whose volume sum is 0 makes the division fail with
//!   22012 (`lemma_ans_zero`; every other group's quotient is a value, `lemma_share_ok`, so the error is the outcome
//!   whatever the group order);
//! - otherwise a group whose division leaves the executable domain (`num_div_fits`) puts the outer SELECT outside
//!   the capacity domain (`lemma_ans_cap_div`);
//! - otherwise the result is the sorted rows `(year, share)` of the present groups (`lemma_ans_rows`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::fns::div::{num_div, num_div_fits, num_div_coeff, div_scale, div_round};
use crate::exec::domain::{fits_expr, fits_exprs};
use crate::exec::relational::domain::*;
use crate::query::{query_spec_at, param_domain};
use super::sql::*;
use super::group::*;
use super::norm::*;

verus! {

// ------------------------------------------------------------------------------------------------ group facts

/// Both year groups' absolute volume masses are `i128`-representable.
pub open spec fn masses_fit(db: Database, ps: Seq<Literal>) -> bool {
    &&& gmass(inner_rows(db, ps), ykey(1995)) <= i128::MAX
    &&& gmass(inner_rows(db, ps), ykey(1996)) <= i128::MAX
}

/// The mass bounds the sums; an empty group has mass 0.
pub proof fn lemma_gsum_bounds(b0: Seq<u8>, zs: Seq<Row>, k: Row)
    ensures
        gmass(zs, k) >= 0,
        abs(gsum1(zs, k)) <= gmass(zs, k),
        abs(gsum0(b0, zs, k)) <= gmass(zs, k),
        gcnt(zs, k) == 0 ==> gmass(zs, k) == 0,
    decreases zs.len(),
{
    if zs.len() > 0 {
        lemma_gsum_bounds(b0, zs.drop_last(), k);
    }
}

/// The groups that have rows are the two year groups.
pub proof fn lemma_keys_cover(db: Database, ps: Seq<Literal>, k: Row)
    requires db_ok(db), gcnt(inner_rows(db, ps), k) > 0,
    ensures k == ykey(1995) || k == ykey(1996),
{
    lemma_group_keys(db, ps);
    let ds = distinct_rows(gkeys(inner_rows(db, ps)));
    assert(ds.contains(k));
    let i = choose|i: int| 0 <= i < ds.len() && ds[i] == k;
    assert(ds[i] == ykey(1995) || ds[i] == ykey(1996));
}

/// Inside the masses every group's sums are inside PostgreSQL's numeric format.
pub proof fn lemma_in_range(db: Database, ps: Seq<Literal>)
    requires db_ok(db), masses_fit(db, ps),
    ensures sums_in_range(txt(ps[0]), inner_rows(db, ps)),
{
    let zs = inner_rows(db, ps);
    let b0 = txt(ps[0]);
    assert forall|k: Row| #[trigger] gcnt(zs, k) > 0 implies num_in_range(gsum0(b0, zs, k), sc0(b0, zs, k))
        && num_in_range(gsum1(zs, k), 4) by {
        lemma_keys_cover(db, ps, k);
        lemma_gsum_bounds(b0, zs, k);
        lemma_num_in_range_small(gsum0(b0, zs, k), sc0(b0, zs, k));
        lemma_num_in_range_small(gsum1(zs, k), 4);
    }
}

// ------------------------------------------------------------------------------------------------ the division

/// A quotient of a dividend inside `i128` (scale at most 4) by a nonzero divisor of scale 4 is a value: its
/// coefficient has at most `43 + rscale` digits, far inside PostgreSQL's numeric format.
pub proof fn lemma_share_ok(c1: int, s1: nat, c2: int)
    requires abs(c1) <= i128::MAX, s1 <= 4, c2 != 0,
    ensures num_div(c1, s1, c2, 4) is Ok,
{
    let r = div_scale(c1, s1, c2, 4);
    crate::bridge::fns::div::lemma_div_scale_range(c1, s1, c2, 4);
    crate::bridge::fns::div::lemma_num_div_coeff_scaled(c1, s1, c2, 4);
    let k = r + 4 - s1;
    assert(k >= 0);
    let kn = k as nat;
    let n = abs(c1) * pow10(kn);
    let d = abs(c2);
    let q = div_round(n, d);
    lemma_pow10_positive(kn);
    lemma_pow10_i128_boundary();
    assert(pow10(39) == pow10(38) * 10) by {
        crate::bridge::order::lemma_pow10_add(38, 1);
        assert(pow10(1) == 10) by (compute_only);
    }
    assert(abs(c1) + 1 <= pow10(39));
    assert(n >= 0) by (nonlinear_arith) requires n == abs(c1) * pow10(kn), abs(c1) >= 0, pow10(kn) >= 1;
    assert(q <= n + 1) by (nonlinear_arith)
        requires q == (2 * n + d) / (2 * d), d >= 1, n >= 0;
    assert(q >= 0) by (nonlinear_arith)
        requires q == (2 * n + d) / (2 * d), d >= 1, n >= 0;
    crate::bridge::order::lemma_pow10_add(39, kn);
    assert(n + 1 <= pow10(39) * pow10(kn)) by (nonlinear_arith)
        requires n == abs(c1) * pow10(kn), abs(c1) + 1 <= pow10(39), pow10(kn) >= 1;
    let coeff = num_div_coeff(c1, s1, c2, 4);
    assert(abs(coeff) <= q) by {
        assert(coeff == sign(c1) * sign(c2) * q);
        assert(sign(c1) == 0 || sign(c1) == 1 || sign(c1) == -1);
        assert(sign(c2) == 0 || sign(c2) == 1 || sign(c2) == -1);
        assert(abs(sign(c1) * sign(c2) * q) <= q) by (nonlinear_arith)
            requires -1 <= sign(c1) <= 1, -1 <= sign(c2) <= 1, q >= 0;
    }
    let lim = numeric_int_digits_max_nat() + r;
    assert(39 + kn + 1 <= lim);
    crate::bridge::order::lemma_pow10_add(39 + kn, 1);
    assert(pow10(1) == 10) by (compute_only);
    lemma_pow10_positive(39 + kn);
    lemma_pow10_monotone(39 + kn + 1, lim);
    assert(abs(coeff) < pow10(lim));
    lemma_decimal_digits_bound(abs(coeff), lim);
    assert(num_in_range(coeff, r));
}

pub open spec fn numeric_int_digits_max_nat() -> nat {
    crate::spec::limits::numeric_int_digits_max()
}

/// The outer SELECT list on a group row is inside its domain exactly when the division is.
pub proof fn lemma_outer_fits(db: Database, b0: Seq<u8>, zs: Seq<Row>, k: Row)
    requires is_ykey(k),
    ensures fits_exprs(db, grow(b0, zs, k), outer_exprs())
        == num_div_fits(gsum0(b0, zs, k), sc0(b0, zs, k), gsum1(zs, k), 4),
{
    let r = grow(b0, zs, k);
    let (a0, a1) = (agg0_val(b0, zs, k), agg1_val(zs, k));
    assert(r.len() == 3 && r[0] == k[0] && r[1] == a0 && r[2] == a1);
    let args = seq![Expr::Col(1), Expr::Col(2)];
    let div = Expr::Call { f: ScalarFn::DivNumeric, args };
    let es = outer_exprs();
    assert(es =~= seq![Expr::Col(0), div]);
    crate::link::expr::lemma_expr_col(db, r, 1);
    crate::link::expr::lemma_expr_col(db, r, 2);
    crate::link::expr::lemma_expr_col(db, r, 0);
    lemma_exprs2(db, r, Expr::Col(1), Expr::Col(2), a0, a1);
    lemma_exprs1(db, r, Expr::Col(0), k[0]);
    crate::exec::domain::lemma_fits_exprs_unfold(db, r, args);
    crate::exec::domain::lemma_fits_exprs_unfold(db, r, args.drop_last());
    assert(args.drop_last().drop_last() =~= Seq::<Expr>::empty());
    assert(args.drop_last() =~= seq![Expr::Col(1)]);
    assert(fits_exprs(db, r, args));
    assert(fits_expr(db, r, div) == crate::spec::fns::fits_fn(ScalarFn::DivNumeric, seq![a0, a1]));
    crate::exec::domain::lemma_fits_exprs_unfold(db, r, es);
    crate::exec::domain::lemma_fits_exprs_unfold(db, r, es.drop_last());
    assert(es.drop_last() =~= seq![Expr::Col(0)]);
    assert(es.drop_last().drop_last() =~= Seq::<Expr>::empty());
}

// ------------------------------------------------------------------------------------------------ outcomes

/// A year group whose absolute volume mass passes `i128::MAX` puts SUM(volume) outside its capacity condition.
pub proof fn lemma_cap_mass(db: Database, ps: Seq<Literal>, y: int)
    requires
        db_ok(db), param_domain(ps), y == 1995 || y == 1996,
        gmass(inner_rows(db, ps), ykey(y)) > i128::MAX,
    ensures !fits_query(db, Seq::empty(), query_spec_at(ps).body),
{
    hide(eval_query);
    let zs = inner_rows(db, ps);
    let b0 = txt(ps[0]);
    let ctx = Seq::<Val>::empty();
    let (keys, aggs) = (group_keys(), group_aggs(ps));
    let (ks, gs) = (gkeys(zs), gargs_all(b0, zs));
    lemma_statement(ps);
    lemma_params(ps);
    lemma_inner(db, ps);
    lemma_inner_rows(db, ps);
    lemma_group_keys(db, ps);
    let k = ykey(y);
    lemma_gsum_bounds(b0, zs, k);
    assert forall|i: int| 0 <= i < zs.len() implies #[trigger] group_input(db, ctx + zs[i], keys, aggs)
        == Ok::<(Row, Row), SqlError>((ks[i], gs[i])) by {
        assert(ctx + zs[i] =~= zs[i]);
        lemma_group_input(db, ps, zs[i]);
    }
    let ds = distinct_rows(ks);
    assert(ds.contains(k));
    let g = choose|g: int| 0 <= g < ds.len() && ds[g] == k;
    let m = group_members(ks, gs, k);
    lemma_members(b0, zs, k);
    lemma_members_mass(b0, zs, k);
    assert(aggs[1] == Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(1) });
    assert(!fits_agg_value(aggs[1], column(m, 1)));
    assert forall|h: int| 0 <= h < ds.len() implies #[trigger] crate::link::capacity::aggs_ok_inside(aggs,
        group_members(ks, gs, ds[h])) by {
        let kh = ds[h];
        assert(kh == ykey(1995) || kh == ykey(1996));
        let mh = group_members(ks, gs, kh);
        lemma_members(b0, zs, kh);
        assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(mh, j))
            implies agg_value(aggs[j], column(mh, j)) is Ok by {
            if j == 0 {
                crate::link::capacity::lemma_sum_inside_ok(NumKind::Numeric, case_e(ps), column(mh, 0));
            } else {
                crate::link::capacity::lemma_sum_inside_ok(NumKind::Numeric, Expr::Col(1), column(mh, 1));
            }
        }
    }
    crate::link::capacity::lemma_group_by_capacity(db, ctx, keys, aggs, Box::new(inner_q(ps)), zs, ks, gs, g, 1);
    assert(!fits_query(db, ctx, group_q(ps)));
}

/// The present groups in first-occurrence order, their GROUP BY rows and outcomes of the outer SELECT.
pub open spec fn gds(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    distinct_rows(gkeys(inner_rows(db, ps)))
}

pub open spec fn grows(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    gds(db, ps).map_values(|k: Row| grow(txt(ps[0]), inner_rows(db, ps), k))
}

pub open spec fn gouts(db: Database, ps: Seq<Literal>) -> Seq<Result<Row, SqlError>> {
    gds(db, ps).map_values(|k: Row| out_res(txt(ps[0]), inner_rows(db, ps), k))
}

/// Inside the masses: the body is the collected group outcomes, and its domain is the GROUP BY's and the outer
/// SELECT's per-group domains.
pub proof fn lemma_body_parts(db: Database, ps: Seq<Literal>)
    requires db_ok(db), param_domain(ps), masses_fit(db, ps),
    ensures
        denote_body(db, query_spec_at(ps)) == collect(gouts(db, ps)),
        project_results(db, Seq::empty(), grows(db, ps), outer_exprs()) == gouts(db, ps),
        fits_query(db, Seq::empty(), query_spec_at(ps).body) ==> fits_each(gouts(db, ps),
            project_fs(db, Seq::empty(), grows(db, ps), outer_exprs())),
        forall|i: int| 0 <= i < gds(db, ps).len() ==> #[trigger] project_fs(db, Seq::empty(), grows(db, ps), outer_exprs())[i]
            == num_div_fits(gsum0(txt(ps[0]), inner_rows(db, ps), gds(db, ps)[i]),
                sc0(txt(ps[0]), inner_rows(db, ps), gds(db, ps)[i]), gsum1(inner_rows(db, ps), gds(db, ps)[i]), 4),
        forall|i: int| 0 <= i < gds(db, ps).len() ==> #[trigger] gds(db, ps)[i] == ykey(1995) || gds(db, ps)[i] == ykey(1996),
{
    hide(eval_query);
    hide(eval_exprs);
    let zs = inner_rows(db, ps);
    let b0 = txt(ps[0]);
    let ctx = Seq::<Val>::empty();
    lemma_statement(ps);
    lemma_params(ps);
    lemma_in_range(db, ps);
    lemma_body(db, ps);
    lemma_inner(db, ps);
    lemma_inner_rows(db, ps);
    lemma_group_keys(db, ps);
    lemma_groupby(db, ps, inner_q(ps), zs);
    let ds = gds(db, ps);
    let gr = grows(db, ps);
    let rs = project_results(db, ctx, gr, outer_exprs());
    let os = gouts(db, ps);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == os[i] by {
        assert(ctx + gr[i] =~= gr[i]);
        lemma_outer_row(db, b0, zs, ds[i]);
    }
    assert(rs =~= os);
    let fs = project_fs(db, ctx, gr, outer_exprs());
    assert forall|i: int| 0 <= i < ds.len() implies #[trigger] fs[i]
        == num_div_fits(gsum0(b0, zs, ds[i]), sc0(b0, zs, ds[i]), gsum1(zs, ds[i]), 4) by {
        assert(ctx + gr[i] =~= gr[i]);
        lemma_outer_fits(db, b0, zs, ds[i]);
    }
    assert(eval_query(db, ctx, group_q(ps)) == Ok::<Relation, SqlError>(gr));
}

/// A present group with volume sum 0: the division by zero is the outcome.
pub proof fn lemma_ans_zero(db: Database, ps: Seq<Literal>, y: int)
    requires
        db_ok(db), param_domain(ps), masses_fit(db, ps), y == 1995 || y == 1996,
        gcnt(inner_rows(db, ps), ykey(y)) > 0, gsum1(inner_rows(db, ps), ykey(y)) == 0,
    ensures denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(SqlError::DivisionByZero),
{
    let zs = inner_rows(db, ps);
    let b0 = txt(ps[0]);
    lemma_body_parts(db, ps);
    lemma_group_keys(db, ps);
    let ds = gds(db, ps);
    let os = gouts(db, ps);
    let e = SqlError::DivisionByZero;
    assert(ds.contains(ykey(y)));
    let i = choose|i: int| 0 <= i < ds.len() && ds[i] == ykey(y);
    assert forall|h: int| 0 <= h < os.len() implies #[trigger] os[h] is Ok || os[h] == Err::<Row, SqlError>(e) by {
        let kh = ds[h];
        lemma_gsum_bounds(b0, zs, kh);
        if gsum1(zs, kh) != 0 {
            lemma_share_ok(gsum0(b0, zs, kh), sc0(b0, zs, kh), gsum1(zs, kh));
        }
    }
    crate::link::capacity::lemma_collect_uniform_err(os, e, i);
}

/// No present group has volume sum 0.
pub open spec fn no_zero(db: Database, ps: Seq<Literal>) -> bool {
    &&& gcnt(inner_rows(db, ps), ykey(1995)) > 0 ==> gsum1(inner_rows(db, ps), ykey(1995)) != 0
    &&& gcnt(inner_rows(db, ps), ykey(1996)) > 0 ==> gsum1(inner_rows(db, ps), ykey(1996)) != 0
}

/// Every group's quotient is a value.
proof fn lemma_outs_ok(db: Database, ps: Seq<Literal>)
    requires db_ok(db), param_domain(ps), masses_fit(db, ps), no_zero(db, ps),
    ensures forall|h: int| 0 <= h < gouts(db, ps).len() ==> (#[trigger] gouts(db, ps)[h]) is Ok,
{
    let zs = inner_rows(db, ps);
    let b0 = txt(ps[0]);
    lemma_body_parts(db, ps);
    lemma_group_keys(db, ps);
    let ds = gds(db, ps);
    assert forall|h: int| 0 <= h < gouts(db, ps).len() implies (#[trigger] gouts(db, ps)[h]) is Ok by {
        let kh = ds[h];
        assert(ds.contains(kh));
        lemma_gsum_bounds(b0, zs, kh);
        lemma_share_ok(gsum0(b0, zs, kh), sc0(b0, zs, kh), gsum1(zs, kh));
    }
}

/// A present group whose division leaves the executable domain (no group dividing by zero).
pub proof fn lemma_ans_cap_div(db: Database, ps: Seq<Literal>, y: int)
    requires
        db_ok(db), param_domain(ps), masses_fit(db, ps), no_zero(db, ps), y == 1995 || y == 1996,
        gcnt(inner_rows(db, ps), ykey(y)) > 0,
        !num_div_fits(gsum0(txt(ps[0]), inner_rows(db, ps), ykey(y)), sc0(txt(ps[0]), inner_rows(db, ps), ykey(y)),
            gsum1(inner_rows(db, ps), ykey(y)), 4),
    ensures !fits_query(db, Seq::empty(), query_spec_at(ps).body),
{
    lemma_body_parts(db, ps);
    lemma_outs_ok(db, ps);
    lemma_group_keys(db, ps);
    let ds = gds(db, ps);
    let fs = project_fs(db, Seq::empty(), grows(db, ps), outer_exprs());
    assert(ds.contains(ykey(y)));
    let i = choose|i: int| 0 <= i < ds.len() && ds[i] == ykey(y);
    assert(!fs[i]);
    crate::link::capacity::lemma_fits_each_violation(gouts(db, ps), fs, i);
}

/// The output row of year `y` with share `v`.
pub open spec fn yrow(y: int, v: Val) -> Row {
    seq![Val::Num { coeff: y, scale: 0 }, v]
}

/// The share of year `y` (when it is a value).
pub open spec fn yshare(db: Database, ps: Seq<Literal>, y: int) -> Val {
    share(txt(ps[0]), inner_rows(db, ps), ykey(y))->Ok_0
}

/// The sorted result rows: the present years in increasing order.
pub open spec fn out_rows(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    let zs = inner_rows(db, ps);
    let a: Seq<Row> = if gcnt(zs, ykey(1995)) > 0 { seq![yrow(1995, yshare(db, ps, 1995))] } else { Seq::empty() };
    let b: Seq<Row> = if gcnt(zs, ykey(1996)) > 0 { seq![yrow(1996, yshare(db, ps, 1996))] } else { Seq::empty() };
    a + b
}

/// The present groups are the two year groups in some order (each once).
proof fn lemma_ds_shape(db: Database, ps: Seq<Literal>)
    requires db_ok(db),
    ensures ({
        let ds = gds(db, ps);
        let zs = inner_rows(db, ps);
        let p95 = gcnt(zs, ykey(1995)) > 0;
        let p96 = gcnt(zs, ykey(1996)) > 0;
        ||| ds.len() == 0 && !p95 && !p96
        ||| ds == seq![ykey(1995)] && p95 && !p96
        ||| ds == seq![ykey(1996)] && !p95 && p96
        ||| ds == seq![ykey(1995), ykey(1996)] && p95 && p96
        ||| ds == seq![ykey(1996), ykey(1995)] && p95 && p96
    }),
{
    lemma_group_keys(db, ps);
    let ds = gds(db, ps);
    let (k5, k6) = (ykey(1995), ykey(1996));
    assert(k5 != k6) by {
        assert(k5[0] != k6[0]);
    }
    if ds.len() >= 3 {
        assert(ds[0] == k5 || ds[0] == k6);
        assert(ds[1] == k5 || ds[1] == k6);
        assert(ds[2] == k5 || ds[2] == k6);
        assert(false);
    }
    if ds.len() == 0 {
        assert(!ds.contains(k5) && !ds.contains(k6));
    } else if ds.len() == 1 {
        assert(ds[0] == k5 || ds[0] == k6);
        if ds[0] == k5 {
            assert(ds.contains(k5));
            assert(!ds.contains(k6));
            assert(ds =~= seq![k5]);
        } else {
            assert(ds.contains(k6));
            assert(!ds.contains(k5));
            assert(ds =~= seq![k6]);
        }
    } else {
        assert(ds[0] == k5 || ds[0] == k6);
        assert(ds[1] == k5 || ds[1] == k6);
        assert(ds[0] != ds[1]);
        assert(ds.contains(ds[0]) && ds.contains(ds[1]));
        if ds[0] == k5 {
            assert(ds =~= seq![k5, k6]);
        } else {
            assert(ds =~= seq![k6, k5]);
        }
    }
}

/// Year rows are sorted by year.
proof fn lemma_yrows_sorted(v5: Val, v6: Val)
    ensures
        sorted_by(order_keys(), seq![yrow(1995, v5), yrow(1996, v6)]),
        sorted_by(order_keys(), seq![yrow(1995, v5)]),
        sorted_by(order_keys(), seq![yrow(1996, v6)]),
        sorted_by(order_keys(), Seq::<Row>::empty()),
{
    let s = seq![yrow(1995, v5), yrow(1996, v6)];
    let ok = order_keys()[0];
    assert(pow10(0) == 1);
    assert(num_sub_coeff(1995, 0, 1996, 0) == -1);
    assert(key_cmp(ok, s[0], s[1]) == -1);
    assert(order_keys().drop_first() =~= Seq::<OrderKey>::empty());
    assert(keys_cmp(order_keys(), s[0], s[1]) == -1);
    assert forall|i: int, j: int| 0 <= i < j < s.len() implies keys_cmp(order_keys(), #[trigger] s[i], #[trigger] s[j]) <= 0 by {
        assert(i == 0 && j == 1);
    }
}

/// The group values in first-occurrence order.
pub open spec fn gvals(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    gds(db, ps).map_values(|k: Row| yrow(k[0]->Num_coeff, share(txt(ps[0]), inner_rows(db, ps), k)->Ok_0))
}

/// The sorted year rows are a sorted permutation of the group values.
proof fn lemma_out_perm(db: Database, ps: Seq<Literal>)
    requires db_ok(db),
    ensures
        out_rows(db, ps).to_multiset() == gvals(db, ps).to_multiset(),
        sorted_by(order_keys(), out_rows(db, ps)),
        slice_rows(out_rows(db, ps), 0, None) == out_rows(db, ps),
{
    lemma_ds_shape(db, ps);
    let ds = gds(db, ps);
    let vs = gvals(db, ps);
    let out = out_rows(db, ps);
    let v5 = yshare(db, ps, 1995);
    let v6 = yshare(db, ps, 1996);
    let (r5, r6) = (yrow(1995, v5), yrow(1996, v6));
    lemma_yrows_sorted(v5, v6);
    let (k5, k6) = (ykey(1995), ykey(1996));
    assert(k5[0]->Num_coeff == 1995 && k6[0]->Num_coeff == 1996);
    if ds.len() == 0 {
        assert(vs =~= Seq::<Row>::empty());
        assert(out =~= Seq::<Row>::empty());
    } else if ds.len() == 1 {
        if ds[0] == k5 {
            assert(vs =~= seq![r5]);
            assert(out =~= seq![r5]);
        } else {
            assert(vs =~= seq![r6]);
            assert(out =~= seq![r6]);
        }
    } else {
        assert(out =~= seq![r5, r6]);
        if ds[0] == k5 {
            assert(vs =~= out);
        } else {
            assert(vs =~= seq![r6, r5]);
            broadcast use vstd::multiset::group_multiset_axioms, vstd::seq_lib::group_to_multiset_ensures;
            let e = Seq::<Row>::empty();
            assert(vs =~= e.push(r6).push(r5));
            assert(out =~= e.push(r5).push(r6));
            assert(vs.to_multiset() =~= out.to_multiset());
        }
    }
    assert(slice_rows(out, 0, None) =~= out);
}

/// No division by zero and every division inside its domain: the sorted year rows are the result.
pub proof fn lemma_ans_rows(db: Database, ps: Seq<Literal>)
    requires
        db_ok(db), param_domain(ps), masses_fit(db, ps), no_zero(db, ps),
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out_rows(db, ps))),
{
    hide(eval_query);
    hide(out_rows);
    let zs = inner_rows(db, ps);
    let b0 = txt(ps[0]);
    lemma_statement(ps);
    lemma_body_parts(db, ps);
    lemma_outs_ok(db, ps);
    lemma_group_keys(db, ps);
    let ds = gds(db, ps);
    let os = gouts(db, ps);
    let vs = gvals(db, ps);
    assert forall|h: int| 0 <= h < os.len() implies #[trigger] os[h] == Ok::<Row, SqlError>(vs[h]) by {
        let kh = ds[h];
        assert(os[h] is Ok);
        assert(out_res(b0, zs, kh) == Ok::<Row, SqlError>(seq![kh[0], share(b0, zs, kh)->Ok_0]));
        assert(kh[0] is Num && kh[0]->Num_scale == 0);
        assert(seq![kh[0], share(b0, zs, kh)->Ok_0] =~= yrow(kh[0]->Num_coeff, share(b0, zs, kh)->Ok_0));
    }
    crate::bridge::collect::lemma_collect_all(os, vs);
    lemma_out_perm(db, ps);
    let out = out_rows(db, ps);
    assert(query_spec_at(ps).keys == order_keys());
    assert(out.to_multiset() == vs.to_multiset() && sorted_by(order_keys(), out)
        && Ok::<Relation, SqlError>(out) == Ok::<Relation, SqlError>(slice_rows(out, 0, None)));
}

} // verus!
