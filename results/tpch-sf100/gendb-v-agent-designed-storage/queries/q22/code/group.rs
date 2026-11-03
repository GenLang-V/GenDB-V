//! The statement's meaning, part 2: the body in the accumulator normal form of `link::query`.
//! - `gc` describes the outer query over the customer rows (qualifying rows `mq`, key `[code]`, COUNT(*) and SUM
//!   of the balance); `gp` describes the GROUP BY over the derived table's rows `[code, c_acctbal]`;
//! - the WHERE keeps the `mq` rows (`lemma_filter`), the projection maps them to `hrow` (`lemma_project`), and the
//!   GROUP BY of `gp` over those rows has the accumulators of `gc` over the customer rows (`lemma_transfer`), so
//!   the body is `result_rows(gc, ctab(db))` whenever every group count fits int8 (`lemma_body`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::limits::*;
use crate::spec::fns::div::num_div_fits;
use crate::spec::equality::*;
use crate::query::query_spec_at;
use crate::link::expr::{ival, i128_max};
use crate::link::query::*;
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::equality::same_exact_type;
use crate::exec::relational::domain::lemma_collect_pointwise;
use super::common::sub2::*;
use super::model::*;
use super::sql::*;

verus! {

// ------------------------------------------------------------------------------------------------ normal forms

/// The outer query over the customer rows.
pub open spec fn gc(db: Database, ps: Seq<Literal>, avg: Val) -> QuerySpec {
    QuerySpec {
        qual: |r: Row| mq(db, ps, avg, r),
        key: |r: Row| seq![Val::Text(code(r))],
        arg: |j: int, r: Row| cacct(r),
        aggs: seq![AggKind::Count, AggKind::Sum { scale: 2 }],
        outs: seq![0nat, 1, 2],
        grouped: true,
    }
}

/// The GROUP BY over the derived table's rows `[cntrycode, c_acctbal]`.
pub open spec fn gp() -> QuerySpec {
    QuerySpec {
        qual: |x: Row| true,
        key: |x: Row| seq![x[0]],
        arg: |j: int, x: Row| ival(x[1]),
        aggs: seq![AggKind::Count, AggKind::Sum { scale: 2 }],
        outs: seq![0nat, 1, 2],
        grouped: true,
    }
}

/// The derived table's row of a customer row.
pub open spec fn hrow(r: Row) -> Row {
    seq![Val::Text(code(r)), r[5]]
}

/// The derived table: the `mq` rows mapped by `hrow`, in order.
pub open spec fn prows(db: Database, ps: Seq<Literal>, avg: Val, rows: Seq<Row>) -> Seq<Row> {
    keep_true(rows, qual_truths(gc(db, ps, avg), rows)).map_values(|r: Row| hrow(r))
}

pub open spec fn cols2() -> Seq<nat> {
    seq![0nat, 1]
}

// ------------------------------------------------------------------------------------------------ WHERE

/// `keep_true` only reads whether each truth is `True`.
pub proof fn lemma_keep_true_same(rows: Seq<Row>, a: Seq<Truth>, b: Seq<Truth>)
    requires
        a.len() == rows.len(), b.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] a[i] is True) == (b[i] is True),
    ensures keep_true(rows, a) == keep_true(rows, b),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ai, bi) = (a.drop_last(), b.drop_last());
        assert forall|i: int| 0 <= i < rows.len() - 1 implies (#[trigger] ai[i] is True) == (bi[i] is True) by {
            assert(ai[i] == a[i] && bi[i] == b[i]);
        }
        lemma_keep_true_same(rows.drop_last(), ai, bi);
        assert(a.last() == a[rows.len() - 1] && b.last() == b[rows.len() - 1]);
    }
}

/// The WHERE keeps the `mq` rows of the customer table.
pub proof fn lemma_filter(db: Database, ps: Seq<Literal>)
    requires
        db_ok(db), ps_ok(ps), group_caps(g2(ps), ctab(db)), avg_val(db, ps) is Null || avg_val(db, ps) is Num,
    ensures ({
        let rows = ctab(db);
        eval_query(db, Seq::empty(), filter_q(ps))
            == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(gc(db, ps, avg_val(db, ps)), rows)))
    }),
{
    let rows = ctab(db);
    let ctx = Seq::<Val>::empty();
    let g = gc(db, ps, avg_val(db, ps));
    let tw = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], where_pred(ps))->Ok_0);
    assert forall|i: int| 0 <= i < tw.len() implies #[trigger] eval_pred(db, ctx + rows[i], where_pred(ps))
        == Ok::<Truth, SqlError>(tw[i]) && (tw[i] is True) == (g.qual)(rows[i]) by {
        assert(ctx + rows[i] =~= rows[i]);
        assert(crow_ok(rows[i]));
        lemma_eval_where(db, rows[i], ps);
    }
    lemma_filter_table(db, ctx, where_pred(ps), 2, tw);
    let qt = qual_truths(g, rows);
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] tw[i] is True) == (qt[i] is True) by {
        assert((tw[i] is True) == (g.qual)(rows[i]));
    }
    lemma_keep_true_same(rows, tw, qt);
}

// ------------------------------------------------------------------------------------------------ projection

/// The derived table's columns of one customer row.
pub proof fn lemma_eval_hrow(db: Database, r: Row)
    requires crow_ok(r),
    ensures eval_exprs(db, r, proj_exprs()) == Ok::<Row, SqlError>(hrow(r)),
{
    let es = proj_exprs();
    lemma_eval_sub2(db, r, 4, cphone(r));
    lemma_expr_results_index(db, r, es);
    let rs = expr_results(db, r, es);
    let vs = hrow(r);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        assert(rs[i] == eval_expr(db, r, es[i]));
    }
    lemma_collect_all(rs, vs);
}

/// The projection maps the kept rows by `hrow`.
pub proof fn lemma_project(db: Database, ps: Seq<Literal>)
    requires
        db_ok(db), ps_ok(ps), group_caps(g2(ps), ctab(db)), avg_val(db, ps) is Null || avg_val(db, ps) is Num,
    ensures
        eval_query(db, Seq::empty(), project_q(ps)) == Ok::<Relation, SqlError>(prows(db, ps, avg_val(db, ps), ctab(db))),
{
    let rows = ctab(db);
    let ctx = Seq::<Val>::empty();
    let g = gc(db, ps, avg_val(db, ps));
    let kept = keep_true(rows, qual_truths(g, rows));
    lemma_filter(db, ps);
    let vs = kept.map_values(|r: Row| hrow(r));
    let rs = Seq::new(kept.len(), |i: int| eval_exprs(db, ctx + kept[i], proj_exprs()));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(vs[i]) by {
        lemma_keep_true_member(rows, qual_truths(g, rows), i);
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(crow_ok(rows[m]));
        assert(ctx + kept[i] =~= kept[i]);
        lemma_eval_hrow(db, kept[i]);
    }
    lemma_collect_all(rs, vs);
    lemma_collect_pointwise::<Row>();
    assert(eval_query(db, ctx, filter_q(ps)) == Ok::<Relation, SqlError>(kept));
}

// ------------------------------------------------------------------------------------------------ transfer

/// The GROUP BY accumulators over the derived table are those of `gc` over the customer rows.
pub proof fn lemma_transfer(db: Database, ps: Seq<Literal>, avg: Val, rows: Seq<Row>, k: Row, j: int)
    ensures
        gcount(gp(), prows(db, ps, avg, rows), k) == gcount(gc(db, ps, avg), rows, k),
        gsum(gp(), prows(db, ps, avg, rows), k, j) == gsum(gc(db, ps, avg), rows, k, j),
        gabs(gp(), prows(db, ps, avg, rows), k, j) == gabs(gc(db, ps, avg), rows, k, j),
        gkeys(gp(), prows(db, ps, avg, rows)) == gkeys(gc(db, ps, avg), rows),
    decreases rows.len(),
{
    let g = gc(db, ps, avg);
    let x = prows(db, ps, avg, rows);
    if rows.len() == 0 {
        assert(x =~= Seq::<Row>::empty());
    } else {
        let ri = rows.drop_last();
        let r = rows.last();
        lemma_transfer(db, ps, avg, ri, k, j);
        let xi = prows(db, ps, avg, ri);
        let qt = qual_truths(g, rows);
        assert(qt.drop_last() =~= qual_truths(g, ri));
        assert(qt.last() == truth_of(mq(db, ps, avg, r)));
        let ki = keep_true(ri, qual_truths(g, ri));
        if mq(db, ps, avg, r) {
            assert(keep_true(rows, qt) == ki.push(r));
            assert(x =~= xi.push(hrow(r)));
            assert(x.drop_last() =~= xi);
            assert(x.last() == hrow(r));
            assert(seq![hrow(r)[0]] =~= seq![Val::Text(code(r))]);
            assert(ival(hrow(r)[1]) == cacct(r));
        } else {
            assert(keep_true(rows, qt) == ki);
            assert(x =~= xi);
        }
    }
}

// ------------------------------------------------------------------------------------------------ GROUP BY

/// The derived table's rows: two columns, a text code and the customer row's balance.
pub proof fn lemma_prows_shape(db: Database, ps: Seq<Literal>, avg: Val)
    requires db_ok(db),
    ensures ({
        let x = prows(db, ps, avg, ctab(db));
        &&& x.len() <= ctab(db).len()
        &&& forall|i: int| 0 <= i < x.len() ==> #[trigger] xrow_ok(x[i])
    }),
{
    let rows = ctab(db);
    let g = gc(db, ps, avg);
    let kept = keep_true(rows, qual_truths(g, rows));
    crate::bridge::relation::lemma_keep_true_sub(rows, qual_truths(g, rows));
    let x = prows(db, ps, avg, rows);
    assert forall|i: int| 0 <= i < x.len() implies #[trigger] xrow_ok(x[i]) by {
        lemma_keep_true_member(rows, qual_truths(g, rows), i);
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(crow_ok(rows[m]));
        assert(x[i] == hrow(kept[i]));
    }
}

/// The derived table projected on its two columns is itself.
pub proof fn lemma_proj2(x: Seq<Row>)
    requires forall|i: int| 0 <= i < x.len() ==> (#[trigger] x[i]).len() == 2,
    ensures proj_all(x, cols2()) == x,
{
    assert forall|i: int| 0 <= i < x.len() implies #[trigger] proj_all(x, cols2())[i] == x[i] by {
        assert(proj(x[i], cols2()) =~= x[i]);
    }
    assert(proj_all(x, cols2()) =~= x);
}

/// `|gabs| <= rows * acct_bound` over the customer rows.
pub proof fn lemma_gabs_bound(g: QuerySpec, rows: Seq<Row>, k: Row, j: int)
    requires
        forall|i: int| 0 <= i < rows.len() ==> -acct_bound() < #[trigger] (g.arg)(j, rows[i]) < acct_bound(),
    ensures gabs(g, rows, k, j) <= rows.len() * acct_bound(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert forall|i: int| 0 <= i < ri.len() implies -acct_bound() < #[trigger] (g.arg)(j, ri[i]) < acct_bound() by {
            assert(ri[i] == rows[i]);
        }
        lemma_gabs_bound(g, ri, k, j);
        assert((g.arg)(j, rows[rows.len() - 1]) == (g.arg)(j, rows.last()));
    }
}

/// A derived-table row: a text code and a balance of scale 2.
pub open spec fn xrow_ok(r: Row) -> bool {
    r.len() == 2 && r[0] is Text && r[1] is Num && r[1]->Num_scale == 2
}

/// The group key of a derived-table row.
proof fn lemma_key_row(db: Database, r: Row)
    requires xrow_ok(r),
    ensures eval_exprs(db, r, group_keys()) == Ok::<Row, SqlError>(seq![r[0]]),
{
    assert(group_keys() =~= col_exprs(seq![0nat]));
    lemma_eval_cols(db, r, seq![0nat]);
    assert(select(r, seq![0nat]) =~= seq![r[0]]);
}

/// The aggregate argument outcomes of a derived-table row.
proof fn lemma_arg_results_row(db: Database, r: Row)
    requires xrow_ok(r),
    ensures
        agg_arg_results(db, r, group_aggs()) == seq![Ok::<Val, SqlError>(Val::Null), Ok::<Val, SqlError>(r[1])],
{
    hide(eval_expr);
    hide(agg_arg);
    let aggs = group_aggs();
    lemma_agg_arg_count(db, r);
    lemma_agg_arg_sum(db, r, NumKind::Numeric, Expr::Col(1));
    crate::link::expr::lemma_expr_col(db, r, 1);
    lemma_agg_arg_results_index(db, r, aggs);
    assert(agg_arg_results(db, r, aggs) =~= seq![Ok::<Val, SqlError>(Val::Null), Ok::<Val, SqlError>(r[1])]);
}

/// `collect` of two successes.
proof fn lemma_collect_two(x: Val, y: Val)
    ensures collect(seq![Ok::<Val, SqlError>(x), Ok::<Val, SqlError>(y)]) == Ok::<Seq<Val>, SqlError>(seq![x, y]),
{
    let s = seq![Ok::<Val, SqlError>(x), Ok::<Val, SqlError>(y)];
    let s1 = seq![Ok::<Val, SqlError>(x)];
    let e = Seq::<Result<Val, SqlError>>::empty();
    assert(s.drop_last() =~= s1);
    assert(s1.drop_last() =~= e);
    assert(collect(e) == Ok::<Seq<Val>, SqlError>(Seq::empty()));
    assert(Seq::<Val>::empty().push(x) =~= seq![x]);
    assert(collect(s1) == Ok::<Seq<Val>, SqlError>(seq![x]));
    assert(seq![x].push(y) =~= seq![x, y]);
}

/// The aggregate arguments of a derived-table row.
proof fn lemma_args_row(db: Database, r: Row)
    requires xrow_ok(r),
    ensures agg_args(db, r, group_aggs()) == Ok::<Row, SqlError>(arg_vals(gp(), r)),
{
    lemma_arg_results_row(db, r);
    lemma_collect_two(Val::Null, r[1]);
    lemma_arg_vals_gp(r);
    assert(r[1] == Val::Num { coeff: ival(r[1]), scale: 2 });
    lemma_agg_args_unfold(db, r, group_aggs());
}

/// One unfolding of `agg_args`.
proof fn lemma_agg_args_unfold(db: Database, env: Row, aggs: Seq<Agg>)
    ensures agg_args(db, env, aggs) == collect(agg_arg_results(db, env, aggs)),
{
}

/// The normal-form argument values of a derived-table row.
proof fn lemma_arg_vals_gp(r: Row)
    ensures arg_vals(gp(), r) == seq![Val::Null, Val::Num { coeff: ival(r[1]), scale: 2 }],
{
    let a = arg_vals(gp(), r);
    assert(a.len() == 2);
    assert(a[0] == Val::Null);
    assert(a[1] == Val::Num { coeff: ival(r[1]), scale: 2 });
    assert(a =~= seq![Val::Null, Val::Num { coeff: ival(r[1]), scale: 2 }]);
}

/// The agreement premises of the GROUP BY link over the derived table.
pub proof fn lemma_group_premises(db: Database, x: Seq<Row>)
    requires
        forall|i: int| 0 <= i < x.len() ==> #[trigger] xrow_ok(x[i]),
    ensures
        keys_agree(db, x, cols2(), group_keys(), gp()),
        args_agree(db, x, cols2(), group_aggs(), gp()),
        aggs_match(group_aggs(), gp()),
        keys_exact(gp(), proj_all(x, cols2())),
{
    let g = gp();
    assert forall|i: int| 0 <= i < x.len() implies (#[trigger] x[i]).len() == 2 by {
        assert(xrow_ok(x[i]));
    }
    lemma_proj2(x);
    assert forall|i: int| 0 <= i < x.len() && (g.qual)(proj(#[trigger] x[i], cols2())) implies
        eval_exprs(db, x[i], group_keys()) == Ok::<Row, SqlError>((g.key)(proj(x[i], cols2()))) by {
        assert(xrow_ok(x[i]));
        assert(proj(x[i], cols2()) =~= x[i]);
        lemma_key_row(db, x[i]);
    }
    assert forall|i: int| 0 <= i < x.len() && (g.qual)(proj(#[trigger] x[i], cols2())) implies
        agg_args(db, x[i], group_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(x[i], cols2()))) by {
        assert(xrow_ok(x[i]));
        assert(proj(x[i], cols2()) =~= x[i]);
        lemma_args_row(db, x[i]);
    }
    assert(aggs_match(group_aggs(), g)) by {
        assert(agg_matches(group_aggs()[0], g.aggs[0]));
        assert(agg_matches(group_aggs()[1], g.aggs[1]));
    }
    assert forall|a: int, b: int| 0 <= a < x.len() && 0 <= b < x.len() && (g.qual)(x[a]) && (g.qual)(x[b]) implies
        (row_not_distinct(#[trigger] (g.key)(x[a]), #[trigger] (g.key)(x[b])) <==> (g.key)(x[a]) == (g.key)(x[b])) by {
        assert(xrow_ok(x[a]) && xrow_ok(x[b]));
        let (ka, kb) = ((g.key)(x[a]), (g.key)(x[b]));
        assert(ka.len() == kb.len());
        assert forall|m: int| 0 <= m < ka.len() implies same_exact_type(#[trigger] ka[m], kb[m]) by {
            assert(ka[m] == x[a][0] && kb[m] == x[b][0]);
        }
        lemma_row_exact(ka, kb);
    }
}

/// Every group key of `gc` is the one-column key of a qualifying row.
proof fn lemma_gkeys_len(db: Database, ps: Seq<Literal>, avg: Val, rows: Seq<Row>, k: Row)
    requires gkeys(gc(db, ps, avg), rows).contains(k),
    ensures k.len() == 1, gcount(gc(db, ps, avg), rows, k) > 0,
{
    let g = gc(db, ps, avg);
    lemma_gkeys_witness(g, rows, k);
    let m = choose|m: int| 0 <= m < rows.len() && #[trigger] hit(g, rows[m], k);
    assert((g.key)(rows[m]) == k);
    lemma_gkeys(g, rows);
}

/// `group_caps` of `gp` over the derived table, from the counts of `gc` and the balance bound.
proof fn lemma_gp_caps(db: Database, ps: Seq<Literal>, avg: Val)
    requires
        db_ok(db),
        ctab(db).len() < 0x1_0000_0000_0000_0000,
        forall|k: Row| #[trigger] gcount(gc(db, ps, avg), ctab(db), k) <= int8_max(),
    ensures group_caps(gp(), prows(db, ps, avg, ctab(db))),
{
    let rows = ctab(db);
    let g = gc(db, ps, avg);
    let x = prows(db, ps, avg, rows);
    assert forall|k: Row, j: int| #![trigger gcount(gp(), x, k), gp().aggs[j]]
        0 <= j < gp().aggs.len() && gp().aggs[j] is Count implies gcount(gp(), x, k) <= int8_max() by {
        lemma_transfer(db, ps, avg, rows, k, j);
    }
    assert forall|k: Row, j: int| 0 <= j < gp().aggs.len() && !(gp().aggs[j] is Count) implies
        #[trigger] gabs(gp(), x, k, j) <= i128_max() by {
        lemma_transfer(db, ps, avg, rows, k, j);
        assert forall|i: int| 0 <= i < rows.len() implies -acct_bound() < #[trigger] (g.arg)(j, rows[i]) < acct_bound() by {
            assert(crow_ok(rows[i]));
        }
        lemma_gabs_bound(g, rows, k, j);
        let n = rows.len() as int;
        assert(n * acct_bound() <= 0x1_0000_0000_0000_0000 * acct_bound()) by (nonlinear_arith)
            requires 0 <= n <= 0x1_0000_0000_0000_0000;
    }
    assert forall|k: Row, j: int| 0 <= j < gp().aggs.len() && gp().aggs[j] is Avg implies
        num_div_fits(#[trigger] gsum(gp(), x, k, j), gp().aggs[j]->Avg_scale, gcount(gp(), x, k) as int, 0) by {}
}

/// The GROUP BY rows over the derived table are the normal form's rows over the customer rows.
proof fn lemma_rows_transfer(db: Database, ps: Seq<Literal>, avg: Val)
    ensures ({
        let x = prows(db, ps, avg, ctab(db));
        gkeys(gp(), x).map_values(|k: Row| full_row(gp(), x, k)) == result_rows(gc(db, ps, avg), ctab(db))
    }),
{
    let rows = ctab(db);
    let g = gc(db, ps, avg);
    let x = prows(db, ps, avg, rows);
    lemma_transfer(db, ps, avg, rows, Seq::empty(), 0);
    let fulls = gkeys(gp(), x).map_values(|k: Row| full_row(gp(), x, k));
    let res = result_rows(g, rows);
    assert(fulls.len() == res.len());
    assert forall|m: int| 0 <= m < fulls.len() implies #[trigger] fulls[m] == res[m] by {
        let k = gkeys(g, rows)[m];
        assert(gkeys(g, rows).contains(k));
        lemma_gkeys_len(db, ps, avg, rows, k);
        lemma_transfer(db, ps, avg, rows, k, 1);
        lemma_transfer(db, ps, avg, rows, k, 0);
        assert(agg_outs(gp(), x, k) =~= agg_outs(g, rows, k));
        assert(full_row(g, rows, k).len() == 3);
        lemma_select_identity(full_row(g, rows, k), g.outs);
    }
    assert(fulls =~= res);
}

/// The body is the normal form's rows when every group count fits int8.
pub proof fn lemma_body(db: Database, ps: Seq<Literal>)
    requires
        db_ok(db), ps_ok(ps), group_caps(g2(ps), ctab(db)), avg_val(db, ps) is Null || avg_val(db, ps) is Num,
        ctab(db).len() < 0x1_0000_0000_0000_0000,
        forall|k: Row| #[trigger] gcount(gc(db, ps, avg_val(db, ps)), ctab(db), k) <= int8_max(),
    ensures
        denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(gc(db, ps, avg_val(db, ps)), ctab(db))),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_expr);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_rows);
    let avg = avg_val(db, ps);
    let rows = ctab(db);
    let x = prows(db, ps, avg, rows);
    lemma_statement(ps);
    lemma_project(db, ps);
    lemma_prows_shape(db, ps, avg);
    lemma_group_premises(db, x);
    lemma_proj2(x);
    lemma_table_rows(db, project_q(ps), x, cols2(), gp());
    lemma_gp_caps(db, ps, avg);
    lemma_group_query(db, x, cols2(), project_q(ps), group_keys(), group_aggs(), gp());
    lemma_rows_transfer(db, ps, avg);
}

} // verus!
