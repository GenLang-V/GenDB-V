//! The IN subquery `SELECT l_orderkey FROM lineitem GROUP BY l_orderkey HAVING SUM(l_quantity) > $1`, evaluated
//! under an outer row `ctx` of the FROM product (33 values, so the subquery's lineitem columns are `ctx` positions
//! 33.. of its rows).
//!
//! Path: the GROUP BY is the normal form `sub_spec` over the lineitem rows projected to `(l_orderkey,
//! l_quantity)` (`sub_xs`): one group per order key with the exact quantity sum, which is the stored per-key sum
//! `ksum` of `common::keysum` (`lemma_sub_acc`). Inside the SUM capacity (every group's absolute mass is at most
//! `n_l * 10^15`, below `i128::MAX` for any table a `usize` can count) the groups are `gkeys` with their sums
//! (`lemma_sub_group`), the HAVING condition keeps the groups whose sum exceeds `100 * $1` (`lemma_sub_filter`),
//! and the projection gives their keys (`lemma_sub_rows`). `o_orderkey IN (..)` is then two-valued: true exactly
//! when the order key has a lineitem row and its quantity sum exceeds `$1` (`in_sub`, `lemma_in_pred`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::query::param_domain;
use crate::link::query::*;
use crate::link::expr::{i128_max, lemma_compare_num, lemma_pred_cmp};
use crate::link::join::{keep, lemma_keep_true_keep, lemma_keep_members};
use crate::link::source::lemma_proj_all_index;
use crate::link::capacity::lemma_group_prepared;
use crate::bridge::equality::same_exact_type;
use crate::bridge::collect::lemma_collect_all;
use crate::exec::relational::domain::{lemma_eval_group_by, lemma_eval_filter, lemma_eval_project, group_results,
    filter_results, project_results};
use crate::agent::tables::*;
use crate::agent::common::keysum::*;

verus! {

// ------------------------------------------------------------------------------------------------ parameter

/// `$1`.
pub open spec fn p_of(ps: Seq<Literal>) -> int {
    match ps[0] { Literal::Int { v, .. } => v, _ => 0 }
}

/// The HAVING threshold in quantity coefficients (scale 2): `SUM(l_quantity) > $1` is `sum > 100 * $1`.
pub open spec fn thr_of(ps: Seq<Literal>) -> int { 100 * p_of(ps) }

/// Order key `v` is in the subquery's result: some lineitem row has key `v` and the key's quantity sum exceeds
/// `$1`.
pub open spec fn in_sub(sv: StoresView, ps: Seq<Literal>, v: int) -> bool {
    &&& i64::MIN <= v <= i64::MAX
    &&& kcount(lk(sv), v as i64, 0, n_l(sv)) > 0
    &&& ksum(lk(sv), lq(sv), v as i64, 0, n_l(sv)) > thr_of(ps)
}

// ------------------------------------------------------------------------------------------------ the AST

/// GROUP BY l_orderkey with SUM(l_quantity), under a 33-value outer row.
pub open spec fn sub_group() -> Query {
    Query::GroupBy {
        keys: seq![Expr::Col(33)],
        aggs: seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(37) }],
        input: Box::new(Query::Table(0)),
    }
}

/// HAVING SUM(l_quantity) > $1.
pub open spec fn sub_having(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(34), b: Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(ps[0])) } }
}

pub open spec fn sub_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: sub_having(ps), input: Box::new(sub_group()) }
}

/// SELECT l_orderkey .. (the whole subquery).
pub open spec fn sub_query(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: seq![Expr::Col(33)], input: Box::new(sub_filter(ps)) }
}

/// o_orderkey IN (subquery).
pub open spec fn in_pred(ps: Seq<Literal>) -> Pred {
    Pred::AnyCmp { op: CmpOp::Eq, e: Expr::Col(8), q: Box::new(sub_query(ps)) }
}

// ------------------------------------------------------------------------------------------------ normal form

/// The lineitem columns the subquery reads: `l_orderkey`, `l_quantity`.
pub open spec fn sub_cols() -> Seq<nat> { seq![0nat, 4] }

pub open spec fn sub_xs(db: Database) -> Seq<Row> { proj_all(db.tables[0], sub_cols()) }

pub open spec fn coeff_of(v: Val) -> int { match v { Val::Num { coeff, .. } => coeff, _ => 0 } }

/// Every row qualifies; the key is `l_orderkey`; the SUM argument is the `l_quantity` coefficient (scale 2).
pub open spec fn sub_spec() -> QuerySpec {
    QuerySpec {
        qual: |x: Row| true,
        key: |x: Row| seq![x[0]],
        arg: |j: int, x: Row| coeff_of(x[1]),
        aggs: seq![AggKind::Sum { scale: 2 }],
        outs: seq![0nat, 1],
        grouped: true,
    }
}

/// The group key of order key `v`.
pub open spec fn okey_row(v: int) -> Row { seq![Val::Int(v)] }

/// The table is small enough for the SUM capacity: its row count fits `usize`.
pub open spec fn small(sv: StoresView) -> bool { n_l(sv) <= usize::MAX }

/// Projected lineitem row `i`.
pub proof fn lemma_sub_xs_row(sv: StoresView, db: Database, i: int)
    requires bound_db(sv, db), 0 <= i < n_l(sv),
    ensures
        sub_xs(db).len() == n_l(sv),
        sub_xs(db)[i] == seq![Val::Int(lk(sv)[i] as int), Val::Num { coeff: lq(sv)[i] as int, scale: 2 }],
        num15(lq(sv)[i]),
{
    lemma_parts_shape(sv, db);
    lemma_lineitem_row(sv, db, i);
    lemma_proj_all_index(db.tables[0], sub_cols());
    assert(sub_xs(db)[i] =~= seq![Val::Int(lk(sv)[i] as int), Val::Num { coeff: lq(sv)[i] as int, scale: 2 }]);
}

/// With an always-true condition the qualifying rows are all rows.
pub proof fn lemma_qrows_all(g: QuerySpec, xs: Seq<Row>)
    requires forall|x: Row| #[trigger] (g.qual)(x),
    ensures qrows(g, xs) == xs,
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_qrows_all(g, xs.drop_last());
        assert(xs.drop_last().push(xs.last()) =~= xs);
    }
}

/// The accumulators of the prefix `0..m`: group `[Int(v)]` counts and sums the rows of key `v`; the absolute
/// mass is at most `10^15` per counted row, and at most `m` rows count.
pub proof fn lemma_sub_acc(sv: StoresView, db: Database, m: int, k: Row)
    requires bound_db(sv, db), 0 <= m <= n_l(sv),
    ensures ({
        let xs = sub_xs(db).subrange(0, m);
        let g = sub_spec();
        &&& gcount(g, xs, k) <= m
        &&& gabs(g, xs, k, 0) <= gcount(g, xs, k) * 1_000_000_000_000_000
        &&& forall|v: i64| k == okey_row(v as int) ==> gcount(g, xs, k) == kcount(lk(sv), v, 0, m)
                && gsum(g, xs, k, 0) == ksum(lk(sv), lq(sv), v, 0, m)
    }),
    decreases m,
{
    let g = sub_spec();
    let all = sub_xs(db);
    lemma_parts_shape(sv, db);
    lemma_proj_all_index(db.tables[0], sub_cols());
    if m == 0 {
        lemma_empty(g, all, 0, k, 0);
        assert forall|v: i64| k == okey_row(v as int) implies gcount(g, all.subrange(0, 0), k) == kcount(lk(sv), v, 0, 0)
            && gsum(g, all.subrange(0, 0), k, 0) == ksum(lk(sv), lq(sv), v, 0, 0) by {
            lemma_k_empty(lk(sv), lq(sv), v, 0);
        }
    } else {
        lemma_sub_acc(sv, db, m - 1, k);
        lemma_range_step(g, all, 0, m - 1, k, 0);
        lemma_sub_xs_row(sv, db, m - 1);
        let x = all[m - 1];
        assert((g.key)(x) == seq![x[0]]);
        assert((g.arg)(0, x) == lq(sv)[m - 1] as int);
        let c0 = gcount(g, all.subrange(0, m - 1), k) as int;
        let a0 = gabs(g, all.subrange(0, m - 1), k, 0);
        if hit(g, x, k) {
            assert(abs(lq(sv)[m - 1] as int) <= 1_000_000_000_000_000);
            assert((c0 + 1) * 1_000_000_000_000_000 == c0 * 1_000_000_000_000_000 + 1_000_000_000_000_000);
        }
        assert forall|v: i64| k == okey_row(v as int) implies gcount(g, all.subrange(0, m), k) == kcount(lk(sv), v, 0, m)
            && gsum(g, all.subrange(0, m), k, 0) == ksum(lk(sv), lq(sv), v, 0, m) by {
            lemma_k_step(lk(sv), lq(sv), v, 0, m - 1);
            assert(hit(g, x, k) == (lk(sv)[m - 1] == v)) by {
                if hit(g, x, k) {
                    assert(seq![x[0]][0] == k[0]);
                }
                if lk(sv)[m - 1] == v {
                    assert(seq![x[0]] =~= okey_row(v as int));
                }
            }
        }
    }
}

/// The whole table: counts and sums per order key, and the SUM capacity of every group.
pub proof fn lemma_sub_totals(sv: StoresView, db: Database)
    requires bound_db(sv, db), small(sv),
    ensures
        forall|v: i64| #[trigger] gcount(sub_spec(), sub_xs(db), okey_row(v as int)) == kcount(lk(sv), v, 0, n_l(sv))
            && gsum(sub_spec(), sub_xs(db), okey_row(v as int), 0) == ksum(lk(sv), lq(sv), v, 0, n_l(sv)),
        group_caps(sub_spec(), sub_xs(db)),
{
    let g = sub_spec();
    let xs = sub_xs(db);
    lemma_parts_shape(sv, db);
    lemma_proj_all_index(db.tables[0], sub_cols());
    let n = n_l(sv);
    assert(xs.subrange(0, n) =~= xs);
    assert forall|v: i64| #[trigger] gcount(g, xs, okey_row(v as int)) == kcount(lk(sv), v, 0, n)
        && gsum(g, xs, okey_row(v as int), 0) == ksum(lk(sv), lq(sv), v, 0, n) by {
        lemma_sub_acc(sv, db, n, okey_row(v as int));
    }
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
        assert(j == 0);
        lemma_sub_acc(sv, db, n, k);
        let c = gcount(g, xs, k) as int;
        assert(c * 1_000_000_000_000_000 <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff) by (nonlinear_arith)
            requires 0 <= c <= n, n <= usize::MAX;
    }
}

/// A group with a row is the key of a lineitem row.
pub proof fn lemma_sub_key(sv: StoresView, db: Database, k: Row) -> (i: int)
    requires bound_db(sv, db), gcount(sub_spec(), sub_xs(db), k) > 0,
    ensures 0 <= i < n_l(sv), k == okey_row(lk(sv)[i] as int),
{
    let g = sub_spec();
    let xs = sub_xs(db);
    lemma_parts_shape(sv, db);
    lemma_proj_all_index(db.tables[0], sub_cols());
    lemma_count_witness(g, xs, k);
    let i = choose|i: int| 0 <= i < xs.len() && #[trigger] hit(g, xs[i], k);
    lemma_sub_xs_row(sv, db, i);
    assert(k =~= okey_row(lk(sv)[i] as int));
    i
}

// ------------------------------------------------------------------------------------------------ evaluation

/// The subquery's GROUP BY rows: every order key with its quantity sum.
pub open spec fn sub_group_rows(db: Database) -> Seq<Row> {
    gkeys(sub_spec(), sub_xs(db)).map_values(|k: Row| full_row(sub_spec(), sub_xs(db), k))
}

/// The GROUP BY under any 33-value outer row.
pub proof fn lemma_sub_group(sv: StoresView, db: Database, ctx: Row)
    requires bound_db(sv, db), small(sv), ctx.len() == 33,
    ensures eval_query(db, ctx, sub_group()) == Ok::<Relation, SqlError>(sub_group_rows(db)),
{
    let g = sub_spec();
    let xs = sub_xs(db);
    let rows = db.tables[0];
    let keys = seq![Expr::Col(33)];
    let aggs = seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(37) }];
    lemma_parts_shape(sv, db);
    lemma_proj_all_index(rows, sub_cols());
    lemma_qrows_all(g, xs);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    assert(ks.len() == rows.len() && args.len() == rows.len());
    // per row: the key and the SUM argument
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] group_input(db, ctx + rows[i], keys, aggs)
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        lemma_lineitem_row(sv, db, i);
        lemma_sub_xs_row(sv, db, i);
        let env = ctx + rows[i];
        assert(env[33] == rows[i][0] && env[37] == rows[i][4]);
        assert(col_exprs(seq![33nat]) =~= keys);
        lemma_eval_cols(db, env, seq![33nat]);
        assert(select(env, seq![33nat]) =~= seq![rows[i][0]]);
        assert(ks[i] == (g.key)(xs[i]));
        assert(ks[i] =~= seq![rows[i][0]]);
        let rs = agg_arg_results(db, env, aggs);
        lemma_agg_arg_results_index(db, env, aggs);
        assert(rs[0] == eval_expr(db, env, Expr::Col(37)));
        assert(args[i] == arg_vals(g, xs[i]));
        assert(args[i] =~= seq![rows[i][4]]);
        lemma_collect_all(rs, args[i]);
    }
    lemma_group_prepared(db, ctx, keys, aggs, rows, ks, args);
    lemma_eval_group_by(db, ctx, keys, aggs, Box::new(Query::Table(0)));
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(rows));
    assert(group_results(aggs, ks, args) =~= Seq::new(distinct_rows(ks).len(), |gi: int|
        match agg_row(aggs, group_members(ks, args, distinct_rows(ks)[gi])) {
            Ok(a) => Ok(distinct_rows(ks)[gi] + a),
            Err(e) => Err(e),
        }));
    // the groups
    lemma_sub_totals(sv, db);
    assert(aggs_match(aggs, g)) by {
        assert(agg_matches(aggs[0], g.aggs[0]));
    }
    assert(keys_exact(g, xs)) by {
        assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
            (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
            lemma_sub_xs_row(sv, db, a);
            lemma_sub_xs_row(sv, db, b);
            let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
            assert forall|t: int| 0 <= t < ka.len() implies same_exact_type(#[trigger] ka[t], kb[t]) by {}
            lemma_row_exact(ka, kb);
        }
    }
    lemma_groups(g, aggs, xs);
}

/// Every GROUP BY row: its key `[Int(v)]` of a lineitem row `i` and the key's sum.
pub proof fn lemma_sub_group_row(sv: StoresView, db: Database, t: int) -> (i: int)
    requires bound_db(sv, db), small(sv), 0 <= t < sub_group_rows(db).len(),
    ensures
        0 <= i < n_l(sv),
        gkeys(sub_spec(), sub_xs(db))[t] == okey_row(lk(sv)[i] as int),
        sub_group_rows(db)[t] == seq![Val::Int(lk(sv)[i] as int), Val::Num { coeff: ksum(lk(sv), lq(sv), lk(sv)[i], 0, n_l(sv)), scale: 2 }],
        kcount(lk(sv), lk(sv)[i], 0, n_l(sv)) > 0,
{
    let g = sub_spec();
    let xs = sub_xs(db);
    let gk = gkeys(g, xs);
    let k = gk[t];
    lemma_gkeys(g, xs);
    assert(gk.contains(k));
    lemma_gkeys_witness(g, xs, k);
    let i = lemma_sub_key(sv, db, k);
    let v = lk(sv)[i];
    lemma_sub_totals(sv, db);
    assert(gcount(g, xs, okey_row(v as int)) == kcount(lk(sv), v, 0, n_l(sv)));
    let r = sub_group_rows(db)[t];
    assert(r == full_row(g, xs, k));
    assert(agg_outs(g, xs, k) =~= seq![Val::Num { coeff: gsum(g, xs, k, 0), scale: 2 }]);
    assert(r =~= seq![Val::Int(v as int), Val::Num { coeff: ksum(lk(sv), lq(sv), v, 0, n_l(sv)), scale: 2 }]);
    i
}

/// The cast parameter `$1::numeric`.
proof fn lemma_cast_param(db: Database, ps: Seq<Literal>, env: Row)
    requires param_domain(ps),
    ensures eval_expr(db, env, Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(ps[0])) })
        == Ok::<Val, SqlError>(Val::Num { coeff: p_of(ps), scale: 0 }),
{
    assert(lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Int(p_of(ps))));
    assert(eval_expr(db, env, Expr::Lit(ps[0])) == Ok::<Val, SqlError>(Val::Int(p_of(ps))));
}

/// `sum (scale 2)` against `$1 (scale 0)`: the order of `sum` and `100 * $1`.
proof fn lemma_compare_having(s: int, p: int)
    ensures compare(Val::Num { coeff: s, scale: 2 }, Val::Num { coeff: p, scale: 0 }) == Some(sign(s - 100 * p)),
{
    lemma_compare_num(s, 2, p, 0);
    assert(pow10(0) == 1 && pow10(2) == 100) by (compute);
    assert(max_nat(2, 0) == 2);
    assert(align(s, 2, 2) == s);
    assert(align(p, 0, 2) == p * 100);
}

/// HAVING on one GROUP BY row: two-valued, true when its sum exceeds `100 * $1`.
pub proof fn lemma_having_row(db: Database, ps: Seq<Literal>, ctx: Row, r: Row, v: int, s: int)
    requires param_domain(ps), ctx.len() == 33, r == seq![Val::Int(v), Val::Num { coeff: s, scale: 2 }],
    ensures eval_pred(db, ctx + r, sub_having(ps)) == Ok::<Truth, SqlError>(truth_of(s > thr_of(ps))),
{
    let env = ctx + r;
    let p = p_of(ps);
    assert(env[34] == r[1]);
    let a = Expr::Col(34);
    let c = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(ps[0])) };
    assert(eval_expr(db, env, a) == Ok::<Val, SqlError>(Val::Num { coeff: s, scale: 2 }));
    lemma_cast_param(db, ps, env);
    lemma_compare_having(s, p);
    lemma_pred_cmp(db, env, CmpOp::Gt, a, c, Val::Num { coeff: s, scale: 2 }, Val::Num { coeff: p, scale: 0 }, s, 100 * p);
}

/// The rows the HAVING condition keeps.
pub open spec fn sub_kept(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    keep(sub_group_rows(db), |r: Row| coeff_of(r[1]) > thr_of(ps))
}

/// The HAVING filter under any 33-value outer row.
pub proof fn lemma_sub_filter(sv: StoresView, db: Database, ps: Seq<Literal>, ctx: Row)
    requires bound_db(sv, db), small(sv), param_domain(ps), ctx.len() == 33,
    ensures eval_query(db, ctx, sub_filter(ps)) == Ok::<Relation, SqlError>(sub_kept(db, ps)),
{
    let rows = sub_group_rows(db);
    let f = |r: Row| coeff_of(r[1]) > thr_of(ps);
    lemma_sub_group(sv, db, ctx);
    lemma_eval_filter(db, ctx, sub_having(ps), Box::new(sub_group()));
    let rs = filter_results(db, ctx, rows, sub_having(ps));
    let truths = Seq::new(rows.len(), |t: int| truth_of(f(rows[t])));
    assert forall|t: int| 0 <= t < rs.len() implies #[trigger] rs[t] == Ok::<Truth, SqlError>(truths[t]) by {
        let i = lemma_sub_group_row(sv, db, t);
        let v = lk(sv)[i];
        let s = ksum(lk(sv), lq(sv), v, 0, n_l(sv));
        lemma_having_row(db, ps, ctx, rows[t], v as int, s);
    }
    lemma_collect_all(rs, truths);
    lemma_keep_true_keep(rows, truths, f);
}

/// The subquery's rows: `[Int(v)]` for every kept group.
pub open spec fn sub_rows(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    sub_kept(db, ps).map_values(|r: Row| seq![r[0]])
}

/// The whole subquery under any 33-value outer row.
pub proof fn lemma_sub_rows(sv: StoresView, db: Database, ps: Seq<Literal>, ctx: Row)
    requires bound_db(sv, db), small(sv), param_domain(ps), ctx.len() == 33,
    ensures eval_query(db, ctx, sub_query(ps)) == Ok::<Relation, SqlError>(sub_rows(db, ps)),
{
    let kept = sub_kept(db, ps);
    let f = |r: Row| coeff_of(r[1]) > thr_of(ps);
    lemma_sub_filter(sv, db, ps, ctx);
    lemma_eval_project(db, ctx, seq![Expr::Col(33)], Box::new(sub_filter(ps)));
    let rs = project_results(db, ctx, kept, seq![Expr::Col(33)]);
    let out = sub_rows(db, ps);
    lemma_keep_members(sub_group_rows(db), f);
    assert forall|t: int| 0 <= t < rs.len() implies #[trigger] rs[t] == Ok::<Row, SqlError>(out[t]) by {
        assert(sub_group_rows(db).contains(kept[t]));
        let u = choose|u: int| 0 <= u < sub_group_rows(db).len() && sub_group_rows(db)[u] == kept[t];
        lemma_sub_group_row(sv, db, u);
        let env = ctx + kept[t];
        assert(kept[t].len() == 2);
        assert(env[33] == kept[t][0]);
        assert(col_exprs(seq![33nat]) =~= seq![Expr::Col(33)]);
        lemma_eval_cols(db, env, seq![33nat]);
        assert(select(env, seq![33nat]) =~= seq![kept[t][0]]);
    }
    lemma_collect_all(rs, out);
}

/// `v = ANY (rows)` over one-column integer rows is two-valued: some row is `[Int(v)]`.
pub proof fn lemma_any_eq(v: int, rows: Seq<Row>)
    requires forall|t: int| 0 <= t < rows.len() ==> exists|w: int| #[trigger] rows[t] == seq![Val::Int(w)],
    ensures any_cmp_truth(CmpOp::Eq, Val::Int(v), rows)
        == Ok::<Truth, SqlError>(truth_of(exists|t: int| 0 <= t < rows.len() && #[trigger] rows[t] == seq![Val::Int(v)])),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let init = rows.drop_last();
        assert forall|t: int| 0 <= t < init.len() implies exists|w: int| #[trigger] init[t] == seq![Val::Int(w)] by {
            assert(init[t] == rows[t]);
        }
        lemma_any_eq(v, init);
        let last = rows.last();
        assert(rows[rows.len() - 1] == last);
        let w = choose|w: int| rows[rows.len() - 1] == seq![Val::Int(w)];
        assert(first_col(last) == Ok::<Val, SqlError>(Val::Int(w)));
        assert(cmp_truth(CmpOp::Eq, Val::Int(v), Val::Int(w)) == Ok::<Truth, SqlError>(truth_of(v == w)));
        let a = exists|t: int| 0 <= t < init.len() && #[trigger] init[t] == seq![Val::Int(v)];
        let b = exists|t: int| 0 <= t < rows.len() && #[trigger] rows[t] == seq![Val::Int(v)];
        if a {
            let t = choose|t: int| 0 <= t < init.len() && #[trigger] init[t] == seq![Val::Int(v)];
            assert(rows[t] == init[t]);
        }
        if v == w {
            assert(rows[rows.len() - 1] == seq![Val::Int(v)]);
        }
        if b {
            let t = choose|t: int| 0 <= t < rows.len() && #[trigger] rows[t] == seq![Val::Int(v)];
            if t < rows.len() - 1 {
                assert(init[t] == rows[t]);
            } else {
                assert(seq![Val::Int(v)][0] == seq![Val::Int(w)][0]);
            }
        }
        assert(b == (a || v == w));
    }
}

/// A row satisfying the condition is kept.
pub proof fn lemma_keep_has(rows: Seq<Row>, f: spec_fn(Row) -> bool, u: int)
    requires 0 <= u < rows.len(), f(rows[u]),
    ensures keep(rows, f).contains(rows[u]),
    decreases rows.len(),
{
    let init = rows.drop_last();
    if u == rows.len() - 1 {
        assert(keep(rows, f) == keep(init, f).push(rows.last()));
        assert(keep(rows, f)[keep(init, f).len() as int] == rows[u]);
    } else {
        assert(init[u] == rows[u]);
        lemma_keep_has(init, f, u);
        let w = choose|w: int| 0 <= w < keep(init, f).len() && keep(init, f)[w] == rows[u];
        if f(rows.last()) {
            assert(keep(rows, f)[w] == rows[u]);
        } else {
            assert(keep(rows, f) == keep(init, f));
        }
    }
}

/// The IN condition on a 33-value outer row whose `o_orderkey` is `Int(v)`: two-valued, `in_sub(v)`.
pub proof fn lemma_in_pred(sv: StoresView, db: Database, ps: Seq<Literal>, ctx: Row, v: int)
    requires bound_db(sv, db), small(sv), param_domain(ps), ctx.len() == 33, ctx[8] == Val::Int(v),
    ensures eval_pred(db, ctx, in_pred(ps)) == Ok::<Truth, SqlError>(truth_of(in_sub(sv, ps, v))),
{
    let grows = sub_group_rows(db);
    let f = |r: Row| coeff_of(r[1]) > thr_of(ps);
    let kept = sub_kept(db, ps);
    let rows = sub_rows(db, ps);
    lemma_sub_rows(sv, db, ps, ctx);
    assert(eval_expr(db, ctx, Expr::Col(8)) == Ok::<Val, SqlError>(Val::Int(v)));
    lemma_keep_members(grows, f);
    // every row is [Int(w)] of a group whose sum exceeds the threshold
    assert forall|t: int| 0 <= t < rows.len() implies exists|w: int| #[trigger] rows[t] == seq![Val::Int(w)] by {
        assert(grows.contains(kept[t]));
        let u = choose|u: int| 0 <= u < grows.len() && grows[u] == kept[t];
        lemma_sub_group_row(sv, db, u);
        assert(rows[t] == seq![kept[t][0]]);
    }
    lemma_any_eq(v, rows);
    let e = exists|t: int| 0 <= t < rows.len() && #[trigger] rows[t] == seq![Val::Int(v)];
    lemma_sub_totals(sv, db);
    if e {
        let t = choose|t: int| 0 <= t < rows.len() && #[trigger] rows[t] == seq![Val::Int(v)];
        assert(grows.contains(kept[t]));
        let u = choose|u: int| 0 <= u < grows.len() && grows[u] == kept[t];
        let i = lemma_sub_group_row(sv, db, u);
        let w = lk(sv)[i];
        assert(rows[t] == seq![kept[t][0]]);
        assert(seq![kept[t][0]][0] == seq![Val::Int(v)][0]);
        assert(w as int == v);
        assert(f(kept[t]));
        assert(in_sub(sv, ps, v));
    }
    if in_sub(sv, ps, v) {
        let vv = v as i64;
        let k = okey_row(v);
        assert(okey_row(vv as int) == k);
        assert(gcount(sub_spec(), sub_xs(db), k) > 0);
        lemma_gkeys(sub_spec(), sub_xs(db));
        let gk = gkeys(sub_spec(), sub_xs(db));
        assert(gk.contains(k));
        let u = choose|u: int| 0 <= u < gk.len() && gk[u] == k;
        let i = lemma_sub_group_row(sv, db, u);
        let w = lk(sv)[i];
        assert(okey_row(w as int)[0] == k[0]);
        assert(w == vv);
        assert(f(grows[u]));
        lemma_keep_has(grows, f, u);
        let t = choose|t: int| 0 <= t < kept.len() && kept[t] == grows[u];
        assert(rows[t] == seq![kept[t][0]]);
        assert(rows[t] =~= seq![Val::Int(v)]);
    }
}

} // verus!
