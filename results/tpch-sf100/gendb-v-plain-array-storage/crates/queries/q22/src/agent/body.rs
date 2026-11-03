//! The statement's body over the stored tables: the outer WHERE keeps the qualifying customer rows
//! (`lemma_filtered`), the projection gives each its country code and balance (`grows`, `lemma_projected`), and the
//! GROUP BY is the accumulator normal form `qspec` of `link::query` over those rows (`lemma_body`): one row
//! `code, COUNT(*), SUM(c_acctbal)` per code. The group accumulators are the index sums of `normal`
//! (`lemma_group_totals`), and every group is the code of a qualifying row (`lemma_group_witness`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::limits::*;
use crate::spec::equality::row_not_distinct;
use crate::spec::fns::div::num_div_fits;
use crate::exec::relational::domain::*;
use crate::gendb_entry::stores::StoresView;
use crate::link::join::{keep, sum_of, count_term, sum_term, lemma_keep_members, lemma_sum_of_keep, lemma_sum_of_ext,
    lemma_sum_of_map, lemma_acc_sum_of};
use crate::link::expr::{ival, tval, lemma_expr_col, i128_max};
use crate::link::query::*;
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::equality::*;
use crate::agent::common::rsum::*;
use crate::agent::common::prefix2::prefix2;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::ast::*;
use crate::agent::rowsem::*;
use crate::agent::subq::*;
use crate::stores::flat_customer::interface as ci;

verus! {

// ------------------------------------------------------------------------------------------------ WHERE

/// Keeping the rows whose truth value is `True` is keeping the rows satisfying `f`, when the two agree.
#[verifier::spinoff_prover]
pub proof fn lemma_keep_true_iff(rows: Seq<Row>, truths: Seq<Truth>, f: spec_fn(Row) -> bool)
    requires
        truths.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] truths[i] is True) == f(rows[i]),
    ensures keep_true(rows, truths) == keep(rows, f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (r0, t0) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < r0.len() implies (#[trigger] t0[i] is True) == f(r0[i]) by {
            assert(t0[i] == truths[i]);
            assert(r0[i] == rows[i]);
        }
        lemma_keep_true_iff(r0, t0, f);
        assert(truths.last() == truths[truths.len() - 1]);
        assert(rows.last() == rows[rows.len() - 1]);
    }
}

/// The qualifying customer rows (as row values).
pub open spec fn kept(sv: StoresView, ps: Seq<Literal>) -> Seq<Row> { keep(cust_rows(sv), qrow(sv, ps)) }

/// The outer WHERE keeps exactly the qualifying customer rows.
#[verifier::spinoff_prover]
pub proof fn lemma_filtered(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), model_ok(sv), sizes_ok(sv), ps_ok(ps),
    ensures eval_query(db, Seq::empty(), filtered(ps)) == Ok::<Relation, SqlError>(kept(sv, ps)),
{
    let rows = cust_rows(sv);
    let pred = where_pred(ps);
    let ctx = Seq::<Val>::empty();
    lemma_eval_filter(db, ctx, pred, Box::new(Query::Table(2)));
    assert(eval_query(db, ctx, Query::Table(2)) == Ok::<Relation, SqlError>(rows));
    lemma_avg_totals(sv, ps);
    let prs = filter_results(db, ctx, rows, pred);
    assert forall|i: int| 0 <= i < prs.len() implies (#[trigger] prs[i]) is Ok
        && ((prs[i]->Ok_0 is True) == qrow(sv, ps)(rows[i])) by {
        assert(ctx + rows[i] =~= rows[i]);
        lemma_cust_row(sv, i);
        lemma_sub_value(db, sv, ps, rows[i]);
        lemma_where_eval(db, sv, ps, i);
        lemma_qrow(sv, ps, i);
    }
    let truths = Seq::new(rows.len(), |i: int| prs[i]->Ok_0);
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {}
    lemma_collect_all(prs, truths);
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] truths[i] is True) == qrow(sv, ps)(rows[i]) by {
        assert(prs[i] is Ok);
    }
    lemma_keep_true_iff(rows, truths, qrow(sv, ps));
}

// ------------------------------------------------------------------------------------------------ projection

/// The projected row of a customer row value: its country code and balance.
pub open spec fn prow(r: Row) -> Row { seq![Val::Text(prefix2(tval(r[4]))), r[5]] }

/// The rows entering the GROUP BY.
pub open spec fn grows(sv: StoresView, ps: Seq<Literal>) -> Seq<Row> { kept(sv, ps).map_values(|r: Row| prow(r)) }

/// The kept rows are customer rows: row `m` of them is the qualifying customer row `i`.
#[verifier::spinoff_prover]
pub proof fn lemma_kept_rows(sv: StoresView, ps: Seq<Literal>, m: int) -> (i: int)
    requires 0 <= m < kept(sv, ps).len(),
    ensures 0 <= i < n_c(sv), cust_rows(sv)[i] == kept(sv, ps)[m], qual(sv, ps, i),
{
    let rows = cust_rows(sv);
    lemma_keep_members(rows, qrow(sv, ps));
    assert(rows.contains(kept(sv, ps)[m]));
    let i = choose|i: int| 0 <= i < rows.len() && rows[i] == kept(sv, ps)[m];
    lemma_qrow(sv, ps, i);
    i
}

/// A two-expression list over evaluated expressions.
#[verifier::spinoff_prover]
proof fn lemma_eval_pair(db: Database, env: Row, a: Expr, b: Expr, va: Val, vb: Val)
    requires eval_expr(db, env, a) == Ok::<Val, SqlError>(va), eval_expr(db, env, b) == Ok::<Val, SqlError>(vb),
    ensures eval_exprs(db, env, seq![a, b]) == Ok::<Row, SqlError>(seq![va, vb]),
{
    hide(eval_expr);
    hide(collect);
    hide(eval_exprs);
    let es = seq![a, b];
    let vs = seq![va, vb];
    let rs = expr_results(db, env, es);
    lemma_expr_results_index(db, env, es);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        if i == 0 {} else {}
    }
    lemma_collect_all(rs, vs);
    assert(eval_exprs(db, env, es) == collect(expr_results(db, env, es))) by { reveal(eval_exprs); }
}

/// `SELECT SUBSTRING(c_phone, 1, 2), c_acctbal` of one customer row value.
#[verifier::spinoff_prover]
proof fn lemma_proj_row(db: Database, r: Row, b: Seq<u8>)
    requires r.len() == 8, r[4] == Val::Text(b),
    ensures eval_exprs(db, r, proj_exprs()) == Ok::<Row, SqlError>(prow(r)),
{
    hide(eval_expr);
    hide(eval_exprs);
    hide(sub2);
    lemma_sub2_eval(db, r, 4, b);
    lemma_expr_col(db, r, 5);
    lemma_eval_pair(db, r, sub2(4), Expr::Col(5), Val::Text(prefix2(b)), r[5]);
    assert(prow(r) == seq![Val::Text(prefix2(b)), r[5]]);
}

/// The projection gives the GROUP BY rows.
#[verifier::spinoff_prover]
pub proof fn lemma_projected(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), model_ok(sv), sizes_ok(sv), ps_ok(ps),
    ensures eval_query(db, Seq::empty(), projected(ps)) == Ok::<Relation, SqlError>(grows(sv, ps)),
{
    let ctx = Seq::<Val>::empty();
    let ks = kept(sv, ps);
    lemma_filtered(db, sv, ps);
    lemma_eval_project(db, ctx, proj_exprs(), Box::new(filtered(ps)));
    let prs = project_results(db, ctx, ks, proj_exprs());
    let out = grows(sv, ps);
    assert forall|m: int| 0 <= m < prs.len() implies #[trigger] prs[m] == Ok::<Row, SqlError>(out[m]) by {
        assert(ctx + ks[m] =~= ks[m]);
        let i = lemma_kept_rows(sv, ps, m);
        lemma_cust_row(sv, i);
        lemma_proj_row(db, ks[m], phone(sv, i));
    }
    lemma_collect_all(prs, out);
}

/// Every GROUP BY row is the code (text) and balance (numeric(15,2), scale 2) of a qualifying customer row `i`.
#[verifier::spinoff_prover]
pub proof fn lemma_grows_row(sv: StoresView, ps: Seq<Literal>, m: int) -> (i: int)
    requires 0 <= m < grows(sv, ps).len(),
    ensures
        0 <= i < n_c(sv),
        qual(sv, ps, i),
        grows(sv, ps)[m] == seq![Val::Text(code_of(sv, i)), Val::Num { coeff: bal(sv)[i] as int, scale: 2 }],
{
    let i = lemma_kept_rows(sv, ps, m);
    lemma_cust_row(sv, i);
    assert(grows(sv, ps)[m] =~= seq![Val::Text(code_of(sv, i)), Val::Num { coeff: bal(sv)[i] as int, scale: 2 }]);
    i
}

// ------------------------------------------------------------------------------------------------ GROUP BY

/// The normal form of the GROUP BY over `grows`: every row qualifies, the key is the code, the SUM argument the
/// balance coefficient; output `code, COUNT(*), SUM`.
pub open spec fn qspec() -> QuerySpec {
    QuerySpec {
        qual: |x: Row| true,
        key: |x: Row| seq![x[0]],
        arg: |j: int, x: Row| ival(x[1]),
        aggs: seq![AggKind::Count, AggKind::Sum { scale: 2 }],
        outs: seq![0nat, 1, 2],
        grouped: true,
    }
}

pub open spec fn gcols() -> Seq<nat> { seq![0nat, 1] }

/// A group count never exceeds the row count.
#[verifier::spinoff_prover]
proof fn lemma_gcount_le(g: QuerySpec, rows: Seq<Row>, k: Row)
    ensures gcount(g, rows, k) <= rows.len(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_gcount_le(g, rows.drop_last(), k);
    }
}

/// Argument coefficients below `10^15` in absolute value bound the absolute sums.
#[verifier::spinoff_prover]
proof fn lemma_gabs_le(g: QuerySpec, rows: Seq<Row>, k: Row, j: int)
    requires forall|m: int| 0 <= m < rows.len() ==> abs((g.arg)(j, #[trigger] rows[m])) < 1_000_000_000_000_000,
    ensures 0 <= gabs(g, rows, k, j) <= 1_000_000_000_000_000 * rows.len(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let r0 = rows.drop_last();
        assert forall|m: int| 0 <= m < r0.len() implies abs((g.arg)(j, #[trigger] r0[m])) < 1_000_000_000_000_000 by {
            assert(r0[m] == rows[m]);
        }
        lemma_gabs_le(g, r0, k, j);
        assert(rows.last() == rows[rows.len() - 1]);
    }
}

/// The GROUP BY rows are their own projection on `0, 1`.
#[verifier::spinoff_prover]
proof fn lemma_gcols(sv: StoresView, ps: Seq<Literal>)
    requires model_ok(sv),
    ensures proj_all(grows(sv, ps), gcols()) == grows(sv, ps),
{
    let xs = grows(sv, ps);
    assert forall|m: int| 0 <= m < xs.len() implies #[trigger] proj_all(xs, gcols())[m] == xs[m] by {
        let _i = lemma_grows_row(sv, ps, m);
        assert(proj(xs[m], gcols()) =~= xs[m]);
    }
    assert(proj_all(xs, gcols()) =~= xs);
}

/// Grouping keys: `Col(0)` is the code.
#[verifier::spinoff_prover]
proof fn lemma_keys_agree(db: Database, sv: StoresView, ps: Seq<Literal>)
    ensures keys_agree(db, grows(sv, ps), gcols(), group_keys(), qspec()),
{
    let xs = grows(sv, ps);
    let g = qspec();
    let cols = gcols();
    assert forall|m: int| 0 <= m < xs.len() && (g.qual)(proj(#[trigger] xs[m], cols)) implies
        eval_exprs(db, xs[m], group_keys()) == Ok::<Row, SqlError>((g.key)(proj(xs[m], cols))) by {
        let _i = lemma_grows_row(sv, ps, m);
        assert(proj(xs[m], cols) =~= xs[m]);
        lemma_eval_cols(db, xs[m], seq![0nat]);
        assert(col_exprs(seq![0nat]) =~= group_keys());
        assert(select(xs[m], seq![0nat]) =~= seq![xs[m][0]]);
    }
}

/// Two aggregates' arguments over evaluated arguments.
#[verifier::spinoff_prover]
proof fn lemma_agg_args_pair(db: Database, env: Row, a: Agg, b: Agg, va: Val, vb: Val)
    requires agg_arg(db, env, a) == Ok::<Val, SqlError>(va), agg_arg(db, env, b) == Ok::<Val, SqlError>(vb),
    ensures agg_args(db, env, seq![a, b]) == Ok::<Row, SqlError>(seq![va, vb]),
{
    hide(agg_arg);
    hide(collect);
    hide(agg_args);
    let aggs = seq![a, b];
    let vs = seq![va, vb];
    let ar = agg_arg_results(db, env, aggs);
    lemma_agg_arg_results_index(db, env, aggs);
    assert forall|i: int| 0 <= i < ar.len() implies #[trigger] ar[i] == Ok::<Val, SqlError>(vs[i]) by {
        if i == 0 {} else {}
    }
    lemma_collect_all(ar, vs);
    lemma_agg_args(db, env, aggs);
}

/// The aggregate arguments of one GROUP BY row: NULL for COUNT(*), the balance for SUM.
#[verifier::spinoff_prover]
proof fn lemma_args_row(db: Database, x: Row)
    requires x.len() == 2,
    ensures agg_args(db, x, group_aggs()) == Ok::<Row, SqlError>(seq![Val::Null, x[1]]),
{
    hide(eval_expr);
    hide(agg_arg);
    hide(agg_args);
    lemma_agg_arg_count(db, x);
    lemma_agg_arg_sum(db, x, NumKind::Numeric, Expr::Col(1));
    lemma_expr_col(db, x, 1);
    lemma_agg_args_pair(db, x, Agg::CountStar, Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(1) }, Val::Null, x[1]);
}

/// Aggregate arguments agree with the normal form.
#[verifier::spinoff_prover]
proof fn lemma_args_agree(db: Database, sv: StoresView, ps: Seq<Literal>)
    ensures args_agree(db, grows(sv, ps), gcols(), group_aggs(), qspec()),
{
    hide(agg_args);
    let xs = grows(sv, ps);
    let g = qspec();
    let cols = gcols();
    assert forall|m: int| 0 <= m < xs.len() && (g.qual)(proj(#[trigger] xs[m], cols)) implies
        agg_args(db, xs[m], group_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(xs[m], cols))) by {
        let i = lemma_grows_row(sv, ps, m);
        let x = xs[m];
        assert(proj(x, cols) =~= x);
        lemma_args_row(db, x);
        lemma_arg_vals(x, bal(sv)[i] as int);
    }
}

/// The normal form's argument values of a GROUP BY row.
#[verifier::spinoff_prover]
proof fn lemma_arg_vals(x: Row, c: int)
    requires x.len() == 2, x[1] == (Val::Num { coeff: c, scale: 2 }),
    ensures arg_vals(qspec(), x) == seq![Val::Null, x[1]],
{
    let g = qspec();
    assert((g.arg)(1, x) == c);
    assert(arg_vals(g, x) =~= seq![Val::Null, x[1]]);
}

/// The aggregate ASTs match the normal form's kinds; the keys are exact (texts).
#[verifier::spinoff_prover]
proof fn lemma_aggs_keys(sv: StoresView, ps: Seq<Literal>)
    ensures aggs_match(group_aggs(), qspec()), keys_exact(qspec(), grows(sv, ps)),
{
    let xs = grows(sv, ps);
    let g = qspec();
    assert forall|j: int| 0 <= j < group_aggs().len() implies agg_matches(#[trigger] group_aggs()[j], g.aggs[j]) by {
        if j == 0 {} else {}
    }
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        let _ia = lemma_grows_row(sv, ps, a);
        let _ib = lemma_grows_row(sv, ps, b);
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert forall|t: int| 0 <= t < ka.len() implies same_exact_type(#[trigger] ka[t], kb[t]) by {}
        lemma_row_exact(ka, kb);
    }
}

/// The arithmetic domain: counts below `2^61`, absolute sums below `10^15 * 2^61`.
#[verifier::spinoff_prover]
proof fn lemma_caps(sv: StoresView, ps: Seq<Literal>)
    requires model_ok(sv), sizes_ok(sv),
    ensures group_caps(qspec(), grows(sv, ps)),
{
    let xs = grows(sv, ps);
    let g = qspec();
    let n = xs.len();
    lemma_keep_members(cust_rows(sv), qrow(sv, ps));
    assert(n <= n_c(sv));
    assert forall|m: int| 0 <= m < xs.len() implies abs((g.arg)(1, #[trigger] xs[m])) < 1_000_000_000_000_000 by {
        let i = lemma_grows_row(sv, ps, m);
        assert(num15(bal(sv)[i]));
    }
    assert forall|k: Row, j: int| #![trigger gcount(g, xs, k), g.aggs[j]] 0 <= j < g.aggs.len() && g.aggs[j] is Count implies
        gcount(g, xs, k) <= int8_max() by {
        lemma_gcount_le(g, xs, k);
    }
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
        assert(j == 1);
        lemma_gabs_le(g, xs, k, 1);
        assert(1_000_000_000_000_000 * n <= i128_max()) by (nonlinear_arith) requires n <= 0x1fff_ffff_ffff_ffff;
    }
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && g.aggs[j] is Avg implies
        num_div_fits(#[trigger] gsum(g, xs, k, j), g.aggs[j]->Avg_scale, gcount(g, xs, k) as int, 0) by {
        assert(!(g.aggs[j] is Avg)) by { if j == 0 {} else {} }
    }
}

/// The output rows of the groups are their full rows (outputs `0, 1, 2` of 3 positions).
#[verifier::spinoff_prover]
proof fn lemma_out_full(sv: StoresView, ps: Seq<Literal>)
    ensures ({
        let xs = grows(sv, ps);
        let g = qspec();
        result_rows(g, xs) == gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k))
    }),
{
    let xs = grows(sv, ps);
    let g = qspec();
    let ks = gkeys(g, xs);
    assert forall|t: int| 0 <= t < ks.len() implies #[trigger] out_row(g, xs, ks[t]) == full_row(g, xs, ks[t]) by {
        let k = ks[t];
        assert(ks.contains(k));
        lemma_gkeys_witness(g, xs, k);
        let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
        let _i = lemma_grows_row(sv, ps, m);
        let r = full_row(g, xs, k);
        assert(k == seq![xs[m][0]]);
        assert(r.len() == 3);
        lemma_select_identity(r, g.outs);
    }
    assert(ks.map_values(|k: Row| out_row(g, xs, k)) =~= ks.map_values(|k: Row| full_row(g, xs, k)));
}

/// The statement's body is the normal form's result rows over `grows`.
#[verifier::spinoff_prover]
pub proof fn lemma_body(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), model_ok(sv), sizes_ok(sv), ps_ok(ps),
    ensures eval_query(db, Seq::empty(), body(ps)) == Ok::<Relation, SqlError>(result_rows(qspec(), grows(sv, ps))),
{
    hide(eval_query);
    let xs = grows(sv, ps);
    let g = qspec();
    lemma_projected(db, sv, ps);
    lemma_gcols(sv, ps);
    lemma_keep_all(xs, qual_truths(g, proj_all(xs, gcols())));
    lemma_keys_agree(db, sv, ps);
    lemma_args_agree(db, sv, ps);
    lemma_aggs_keys(sv, ps);
    lemma_caps(sv, ps);
    lemma_group_query(db, xs, gcols(), projected(ps), group_keys(), group_aggs(), g);
    lemma_out_full(sv, ps);
}

// ------------------------------------------------------------------------------------------------ group totals

/// A per-row term of the GROUP BY rows, as a range sum over customer rows.
#[verifier::spinoff_prover]
proof fn lemma_grows_sum(sv: StoresView, ps: Seq<Literal>, h: spec_fn(Row) -> int)
    ensures sum_of(grows(sv, ps), h)
        == range_sum(0, n_c(sv) as int, |i: int| if qrow(sv, ps)(cust_rows(sv)[i]) { h(prow(cust_rows(sv)[i])) } else { 0int }),
{
    let rows = cust_rows(sv);
    let f = qrow(sv, ps);
    let ks = keep(rows, f);
    lemma_sum_of_map(ks, |r: Row| prow(r), h);
    let hp = |r: Row| h(prow(r));
    let hk = |r: Row| if f(r) { hp(r) } else { 0int };
    lemma_keep_members(rows, f);
    assert forall|i: int| 0 <= i < rows.len() && !f(#[trigger] rows[i]) implies hk(rows[i]) == 0 by {}
    lemma_sum_of_keep(rows, f, hk);
    assert forall|m: int| 0 <= m < ks.len() implies #[trigger] hk(ks[m]) == (|r: Row| h((|r: Row| prow(r))(r)))(ks[m]) by {
        assert(rows.contains(ks[m]));
    }
    lemma_sum_of_ext(ks, hk, |r: Row| h((|r: Row| prow(r))(r)));
    let gen = |i: int| ci::row_at(sv.flat_customer, i);
    assert(rows == Seq::new(n_c(sv), gen));
    lemma_sum_of_new(n_c(sv), gen, hk);
    let t1 = |i: int| hk(gen(i));
    let t2 = |i: int| if qrow(sv, ps)(cust_rows(sv)[i]) { h(prow(cust_rows(sv)[i])) } else { 0int };
    assert forall|i: int| 0 <= i < n_c(sv) implies #[trigger] t1(i) == t2(i) by {
        assert(gen(i) == rows[i]);
    }
    lemma_range_sum_ext(0, n_c(sv) as int, t1, t2);
}

/// The count and balance sum of the group of a representative slot `gi` (the first slot holding its text).
#[verifier::spinoff_prover]
pub proof fn lemma_group_totals(sv: StoresView, ps: Seq<Literal>, gi: int)
    requires model_ok(sv), 0 <= gi < 7, grp(ps, pt(ps, gi)) == gi,
    ensures
        gcount(qspec(), grows(sv, ps), seq![Val::Text(pt(ps, gi))]) == gcnt(sv, ps, gi),
        gsum(qspec(), grows(sv, ps), seq![Val::Text(pt(ps, gi))], 1) == gsm(sv, ps, gi),
{
    let g = qspec();
    let k = seq![Val::Text(pt(ps, gi))];
    let xs = grows(sv, ps);
    let rows = cust_rows(sv);
    lemma_acc_sum_of(g, xs, k, 1);
    lemma_grows_sum(sv, ps, count_term(g, k));
    lemma_grows_sum(sv, ps, sum_term(g, k, 1));
    let c1 = |i: int| if qrow(sv, ps)(rows[i]) { count_term(g, k)(prow(rows[i])) } else { 0int };
    let s1 = |i: int| if qrow(sv, ps)(rows[i]) { sum_term(g, k, 1)(prow(rows[i])) } else { 0int };
    lemma_grp(ps, pt(ps, gi));
    assert forall|i: int| 0 <= i < n_c(sv) implies #[trigger] s1(i) == gsum_term(sv, ps, gi)(i) by {
        lemma_qrow(sv, ps, i);
        lemma_cust_row(sv, i);
        let p = prow(rows[i]);
        assert(p[0] == Val::Text(code_of(sv, i)));
        assert(p[1] == rows[i][5]);
        assert((g.arg)(1, p) == bal(sv)[i] as int);
        if qual(sv, ps, i) {
            lemma_grp_eq(ps, code_of(sv, i), pt(ps, gi));
            if code_of(sv, i) == pt(ps, gi) {
                assert((g.key)(p) =~= k);
                assert(hit(g, p, k));
            } else {
                assert((g.key)(p)[0] != k[0]);
                assert(!hit(g, p, k));
            }
        }
    }
    assert forall|i: int| 0 <= i < n_c(sv) implies #[trigger] c1(i) == gcnt_term(sv, ps, gi)(i) by {
        lemma_qrow(sv, ps, i);
        lemma_cust_row(sv, i);
        let p = prow(rows[i]);
        assert(p[0] == Val::Text(code_of(sv, i)));
        assert(p[1] == rows[i][5]);
        assert(ival(p[1]) == bal(sv)[i] as int);
        if qual(sv, ps, i) {
            lemma_grp_eq(ps, code_of(sv, i), pt(ps, gi));
            assert(((g.key)(p) == k) == (code_of(sv, i) == pt(ps, gi))) by {
                if code_of(sv, i) == pt(ps, gi) {
                    assert((g.key)(p) =~= k);
                } else {
                    assert((g.key)(p)[0] != k[0]);
                }
            }
        }
    }
    lemma_range_sum_ext(0, n_c(sv) as int, c1, gcnt_term(sv, ps, gi));
    lemma_range_sum_ext(0, n_c(sv) as int, s1, gsum_term(sv, ps, gi));
}

/// A non-empty group is the code of a qualifying row: its text is the parameter at its group id.
#[verifier::spinoff_prover]
pub proof fn lemma_group_witness(sv: StoresView, ps: Seq<Literal>, k: Row)
    requires model_ok(sv), gcount(qspec(), grows(sv, ps), k) > 0,
    ensures exists|i: int| 0 <= i < n_c(sv) && qual(sv, ps, i) && k == seq![Val::Text(#[trigger] code_of(sv, i))],
{
    let g = qspec();
    let xs = grows(sv, ps);
    lemma_count_witness(g, xs, k);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
    let i = lemma_grows_row(sv, ps, m);
    assert((g.key)(xs[m]) =~= seq![Val::Text(code_of(sv, i))]);
}

/// A qualifying row's group has positive count (with a representative group id).
#[verifier::spinoff_prover]
pub proof fn lemma_group_nonempty(sv: StoresView, ps: Seq<Literal>, i: int)
    requires model_ok(sv), 0 <= i < n_c(sv), qual(sv, ps, i),
    ensures
        grp(ps, code_of(sv, i)) < 7,
        code_of(sv, i) == pt(ps, grp(ps, code_of(sv, i))),
        grp(ps, pt(ps, grp(ps, code_of(sv, i)))) == grp(ps, code_of(sv, i)),
        gcnt(sv, ps, grp(ps, code_of(sv, i))) > 0,
{
    let gi = grp(ps, code_of(sv, i));
    lemma_grp(ps, code_of(sv, i));
    let n = n_c(sv) as int;
    let f = gcnt_term(sv, ps, gi);
    lemma_range_sum_split(0, i, n, f);
    lemma_range_sum_split(i, i + 1, n, f);
    lemma_range_sum_bounds(0, i, f, 0, 1);
    lemma_range_sum_bounds(i + 1, n, f, 0, 1);
    lemma_range_sum_step(i, i, f);
}

} // verus!
