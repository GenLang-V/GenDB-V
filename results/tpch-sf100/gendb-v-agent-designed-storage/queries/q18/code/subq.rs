//! The IN subquery of Q18, `SELECT l_orderkey FROM lineitem GROUP BY l_orderkey HAVING SUM(l_quantity) > $1`,
//! evaluated (as SQL evaluates it) under the 33-column environment of a joined row. Its GROUP BY is the normal form
//! `sub_g` over the lineitem rows projected on (l_orderkey, l_quantity) (`lemma_sub_gb`: one row
//! `(key, SUM)` per key, `rels::lrel` order); HAVING keeps the rows whose sum is above `$1` (`lemma_sub_filter`);
//! SELECT keeps the key (`lemma_sub_q`). `o_orderkey IN (..)` is then true exactly when the order key is `big` on
//! the model (`lemma_in_pred`): it has a lineitem and its quantity sum is above `$1`. The subquery ignores the outer
//! row, so the result is the same for every joined row.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::IntKind;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::{collect, keep_true, group_rows};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::query::param_domain;
use crate::link::query::*;
use crate::link::join::{sum_of, lemma_acc_sum_of, count_term, sum_term};
use crate::link::source::lemma_proj_all_index;
use crate::exec::relational::domain::{filter_results, project_results, group_input_results, group_results,
    lemma_eval_filter, lemma_eval_project, lemma_eval_group_by};
use crate::link::expr::{ival, i128_max, lemma_expr_col, lemma_compare_num, lemma_compare_int, lemma_pred_cmp,
    lemma_align_same, lemma_align_by};
use super::common::isum::*;
use super::model::*;
use super::qspec::*;
use super::rels::*;

verus! {

// ------------------------------------------------------------------------------------------------ the subquery's AST

/// `SUM(l_quantity)` (l_quantity at position 37 of `outer row ++ lineitem row`).
pub open spec fn sub_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(37) }]
}

/// `SELECT .. FROM lineitem GROUP BY l_orderkey` (l_orderkey at position 33).
pub open spec fn sub_gb() -> Query {
    Query::GroupBy { keys: seq![Expr::Col(33)], aggs: sub_aggs(), input: Box::new(Query::Table(0)) }
}

/// `$1` as a numeric.
pub open spec fn lim_expr(ps: Seq<Literal>) -> Expr {
    Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(ps[0])) }
}

/// `HAVING SUM(l_quantity) > $1` (the sum at position 34 of `outer row ++ group row`).
pub open spec fn sub_pred(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(34), b: lim_expr(ps) }
}

pub open spec fn sub_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: sub_pred(ps), input: Box::new(sub_gb()) }
}

/// `SELECT l_orderkey` (position 33 of `outer row ++ group row`).
pub open spec fn sub_q(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: seq![Expr::Col(33)], input: Box::new(sub_filter(ps)) }
}

/// `o_orderkey IN (subquery)` (o_orderkey at position 8 of the joined row).
pub open spec fn in_pred(ps: Seq<Literal>) -> Pred {
    Pred::AnyCmp { op: CmpOp::Eq, e: Expr::Col(8), q: Box::new(sub_q(ps)) }
}

// ------------------------------------------------------------------------------------------------ the normal form

/// The GROUP BY over lineitem rows projected on (l_orderkey, l_quantity): every row qualifies, the key is
/// l_orderkey, the argument the l_quantity coefficient (scale 2).
pub open spec fn sub_g() -> QuerySpec {
    QuerySpec {
        qual: |x: Row| true,
        key: |x: Row| seq![x[0]],
        arg: |j: int, x: Row| ival(x[1]),
        aggs: seq![AggKind::Sum { scale: 2 }],
        outs: seq![0nat, 1],
        grouped: true,
    }
}

/// The GROUP BY's rows: `(l_orderkey, SUM(l_quantity))` per key, in first-occurrence order.
pub open spec fn sub_rows(db: Database) -> Seq<Row> {
    gkeys(sub_g(), lrel(db)).map_values(|k: Row| full_row(sub_g(), lrel(db), k))
}

/// HAVING's truth per group row.
pub open spec fn sub_truths(db: Database, p: QP) -> Seq<Truth> {
    Seq::new(sub_rows(db).len(), |i: int| truth_of(ival(sub_rows(db)[i][1]) > thr(p)))
}

/// The group rows HAVING keeps.
pub open spec fn sub_kept(db: Database, p: QP) -> Seq<Row> {
    keep_true(sub_rows(db), sub_truths(db, p))
}

/// The subquery's rows: the kept keys.
pub open spec fn sub_out(db: Database, p: QP) -> Seq<Row> {
    sub_kept(db, p).map_values(|r: Row| seq![r[0]])
}

/// The facts the subquery lemmas need.
pub open spec fn sub_ok(db: Database, m: M) -> bool {
    db_ok(db) && rel_ok(m, db) && model_ok(m)
}

// ------------------------------------------------------------------------------------------------ generic laws

/// All rows qualify: the qualifying rows are the rows.
proof fn lemma_qrows_all(g: QuerySpec, xs: Seq<Row>)
    requires forall|x: Row| #[trigger] (g.qual)(x),
    ensures qrows(g, xs) == xs,
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_qrows_all(g, xs.drop_last());
        assert(xs.drop_last().push(xs.last()) =~= xs);
    } else {
        assert(qrows(g, xs) =~= xs);
    }
}

/// The absolute sum of a group is at most `b` per row.
proof fn lemma_gabs_le(g: QuerySpec, rows: Seq<Row>, k: Row, j: int, b: int)
    requires
        b >= 0,
        forall|i: int| 0 <= i < rows.len() ==> abs((g.arg)(j, #[trigger] rows[i])) <= b,
    ensures
        0 <= gabs(g, rows, k, j) <= rows.len() * b,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let init = rows.drop_last();
        assert forall|i: int| 0 <= i < init.len() implies abs((g.arg)(j, #[trigger] init[i])) <= b by {
            assert(init[i] == rows[i]);
        }
        lemma_gabs_le(g, init, k, j, b);
        assert(abs((g.arg)(j, rows.last())) <= b) by {
            assert(rows.last() == rows[rows.len() - 1]);
        }
        assert((init.len() as int) * b + b == (rows.len() as int) * b) by (nonlinear_arith)
            requires rows.len() == init.len() + 1;
    }
}

/// `keep_true` keeps exactly the rows whose truth is `True`.
proof fn lemma_keep_true_contains(rows: Seq<Row>, truths: Seq<Truth>, r: Row)
    requires rows.len() == truths.len(),
    ensures
        keep_true(rows, truths).contains(r) <==> exists|i: int| 0 <= i < rows.len() && rows[i] == r && #[trigger] truths[i] is True,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        lemma_keep_true_contains(ri, ti, r);
        let init = keep_true(ri, ti);
        let n = rows.len() - 1;
        if truths.last() is True {
            let k = init.push(rows.last());
            assert(keep_true(rows, truths) == k);
            if k.contains(r) {
                let i = choose|i: int| 0 <= i < k.len() && k[i] == r;
                if i < init.len() {
                    assert(init[i] == r);
                    assert(init.contains(r));
                    let t = choose|t: int| 0 <= t < ri.len() && ri[t] == r && #[trigger] ti[t] is True;
                    assert(rows[t] == r && truths[t] is True);
                } else {
                    assert(rows[n] == r && truths[n] is True);
                }
            }
            if exists|i: int| 0 <= i < rows.len() && rows[i] == r && #[trigger] truths[i] is True {
                let i = choose|i: int| 0 <= i < rows.len() && rows[i] == r && #[trigger] truths[i] is True;
                if i < n {
                    assert(ri[i] == r && ti[i] is True);
                    assert(init.contains(r));
                    let t = choose|t: int| 0 <= t < init.len() && init[t] == r;
                    assert(k[t] == r);
                } else {
                    assert(k[init.len() as int] == r);
                }
            }
        } else {
            assert(keep_true(rows, truths) == init);
            if exists|i: int| 0 <= i < rows.len() && rows[i] == r && #[trigger] truths[i] is True {
                let i = choose|i: int| 0 <= i < rows.len() && rows[i] == r && #[trigger] truths[i] is True;
                assert(i < n);
                assert(ri[i] == r && ti[i] is True);
            }
            if init.contains(r) {
                let t = choose|t: int| 0 <= t < ri.len() && ri[t] == r && #[trigger] ti[t] is True;
                assert(rows[t] == r && truths[t] is True);
            }
        }
    } else {
        assert(keep_true(rows, truths) =~= Seq::<Row>::empty());
    }
}

/// `x = ANY (rows)` over one-column integer rows is whether some row is `(x)`.
proof fn lemma_any_eq_ints(x: int, rows: Seq<Row>)
    requires forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() == 1 && rows[i][0] is Int,
    ensures any_cmp_truth(CmpOp::Eq, Val::Int(x), rows) == Ok::<Truth, SqlError>(truth_of(rows.contains(seq![Val::Int(x)]))),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let init = rows.drop_last();
        assert forall|i: int| 0 <= i < init.len() implies (#[trigger] init[i]).len() == 1 && init[i][0] is Int by {
            assert(init[i] == rows[i]);
        }
        lemma_any_eq_ints(x, init);
        let last = rows.last();
        assert(last == rows[rows.len() - 1]);
        let y = last[0]->Int_0;
        assert(first_col(last) == Ok::<Val, SqlError>(Val::Int(y)));
        lemma_compare_int(x, y);
        assert(cmp_truth(CmpOp::Eq, Val::Int(x), Val::Int(y)) == Ok::<Truth, SqlError>(truth_of(x == y)));
        let s = seq![Val::Int(x)];
        assert((last == s) == (x == y)) by {
            if x == y {
                assert(last =~= s);
            }
        }
        assert(rows.contains(s) == (init.contains(s) || last == s)) by {
            if rows.contains(s) {
                let i = choose|i: int| 0 <= i < rows.len() && rows[i] == s;
                if i < init.len() {
                    assert(init[i] == s);
                }
            }
            if init.contains(s) {
                let i = choose|i: int| 0 <= i < init.len() && init[i] == s;
                assert(rows[i] == s);
            }
        }
    } else {
        assert(!rows.contains(seq![Val::Int(x)]));
    }
}

// ------------------------------------------------------------------------------------------------ the normal form's facts

/// Every projected lineitem row is (Int key, numeric quantity of scale 2 and at most 15 digits).
proof fn lemma_lrel_vals(db: Database, m: M, i: int)
    requires sub_ok(db, m), 0 <= i < lrel(db).len(),
    ensures
        lrel(db)[i].len() == 2,
        lrel(db)[i][0] is Int,
        lrel(db)[i][1] == (Val::Num { coeff: ival(lrel(db)[i][1]), scale: 2 }),
        abs(ival(lrel(db)[i][1])) < pow10(15),
{
    lemma_proj_all_index(db.tables[0], lcols());
    let j = lemma_lrow_at(db, m, i);
}

/// The group keys are exact (one integer per key).
proof fn lemma_sub_keys_exact(db: Database, m: M)
    requires sub_ok(db, m),
    ensures keys_exact(sub_g(), lrel(db)),
{
    let g = sub_g();
    let xs = lrel(db);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (crate::spec::equality::row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        lemma_lrel_vals(db, m, a);
        lemma_lrel_vals(db, m, b);
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert forall|t: int| 0 <= t < ka.len() implies crate::bridge::equality::same_exact_type(#[trigger] ka[t], kb[t]) by {}
        lemma_row_exact(ka, kb);
    }
}

/// Every group's absolute quantity sum fits `i128` (at most `l_n` rows of at most 15 digits).
proof fn lemma_sub_caps(db: Database, m: M)
    requires sub_ok(db, m),
    ensures group_caps(sub_g(), lrel(db)), aggs_match(sub_aggs(), sub_g()),
{
    let g = sub_g();
    let xs = lrel(db);
    assert(pow10(15) == 1000000000000000) by (compute);
    let b = pow10(15);
    lemma_proj_all_index(db.tables[0], lcols());
    assert forall|i: int| 0 <= i < xs.len() implies abs((g.arg)(0, #[trigger] xs[i])) <= b by {
        lemma_lrel_vals(db, m, i);
    }
    assert(xs.len() == m.l_n);
    assert(m.l_n <= u64::MAX);
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
        assert(j == 0);
        lemma_gabs_le(g, xs, k, 0, b);
        assert((xs.len() as int) * b <= 18446744073709551615 * 1000000000000000) by (nonlinear_arith)
            requires xs.len() <= 18446744073709551615, b == 1000000000000000;
    }
    assert(aggs_match(sub_aggs(), g)) by {
        assert(agg_matches(sub_aggs()[0], g.aggs[0]));
    }
}

/// A group key of the normal form is `(l_orderkey)` of some lineitem row, and its row is `(key, SUM)`.
proof fn lemma_sub_row(db: Database, m: M, i: int)
    requires sub_ok(db, m), 0 <= i < sub_rows(db).len(),
    ensures ({
        let k = gkeys(sub_g(), lrel(db))[i];
        &&& k.len() == 1 && k[0] is Int
        &&& gcount(sub_g(), lrel(db), k) > 0
        &&& sub_rows(db)[i] == seq![k[0], Val::Num { coeff: gsum(sub_g(), lrel(db), k, 0), scale: 2 }]
    }),
{
    let g = sub_g();
    let xs = lrel(db);
    let gk = gkeys(g, xs);
    let k = gk[i];
    assert(gk.contains(k));
    lemma_gkeys_witness(g, xs, k);
    let t = choose|t: int| 0 <= t < xs.len() && #[trigger] hit(g, xs[t], k);
    lemma_lrel_vals(db, m, t);
    assert(k == seq![xs[t][0]]);
    assert(agg_outs(g, xs, k) =~= seq![Val::Num { coeff: gsum(g, xs, k, 0), scale: 2 }]);
    assert(sub_rows(db)[i] =~= seq![k[0], Val::Num { coeff: gsum(g, xs, k, 0), scale: 2 }]);
}

/// The normal form's accumulators of key `(v)` are the model's per-key count and quantity sum.
pub proof fn lemma_sub_acc(db: Database, m: M, v: int)
    requires sub_ok(db, m),
    ensures
        gcount(sub_g(), lrel(db), seq![Val::Int(v)]) == kcnt(m, v),
        gsum(sub_g(), lrel(db), seq![Val::Int(v)], 0) == ksum(m, v),
{
    let g = sub_g();
    let xs = lrel(db);
    let k = seq![Val::Int(v)];
    lemma_acc_sum_of(g, xs, k, 0);
    lemma_sum_l(db, m, count_term(g, k));
    lemma_sum_l(db, m, sum_term(g, k, 0));
    assert forall|j: int| 0 <= j < m.l_n implies (#[trigger] lrow(m, j)[0] == Val::Int(lkey(m, j))) && hit(g, lrow(m, j), k) == (lkey(m, j) == v) by {
        let r = lrow(m, j);
        assert((g.key)(r) == seq![Val::Int(lkey(m, j))]);
        if lkey(m, j) == v {
            assert((g.key)(r) =~= k);
        } else {
            assert((g.key)(r)[0] != k[0]);
        }
    }
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] count_term(g, k)(lrow(m, j)) == kcnt_f(m, v)(j) by {
        assert(lrow(m, j)[0] == Val::Int(lkey(m, j)));
    }
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] sum_term(g, k, 0)(lrow(m, j)) == ksum_f(m, v)(j) by {
        assert(lrow(m, j)[0] == Val::Int(lkey(m, j)));
        assert(lrow(m, j)[1] == Val::Num { coeff: lqty(m, j), scale: 2 });
        assert((g.arg)(0, lrow(m, j)) == lqty(m, j));
    }
    lemma_isum_ext(m.l_n, |j: int| count_term(g, k)(lrow(m, j)), kcnt_f(m, v));
    lemma_isum_ext(m.l_n, |j: int| sum_term(g, k, 0)(lrow(m, j)), ksum_f(m, v));
}

// ------------------------------------------------------------------------------------------------ evaluation steps

/// One step of the Filter denotation under a context.
proof fn lemma_filter_unfold(db: Database, ctx: Row, pred: Pred, input: Query, rows: Relation, truths: Seq<Truth>)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(rows),
        collect(filter_results(db, ctx, rows, pred)) == Ok::<Seq<Truth>, SqlError>(truths),
    ensures
        eval_query(db, ctx, Query::Filter { pred, input: Box::new(input) }) == Ok::<Relation, SqlError>(keep_true(rows, truths)),
{
    lemma_eval_filter(db, ctx, pred, Box::new(input));
}

/// One step of the Project denotation under a context.
proof fn lemma_project_unfold(db: Database, ctx: Row, exprs: Seq<Expr>, input: Query, rows: Relation, outs: Seq<Row>)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(rows),
        collect(project_results(db, ctx, rows, exprs)) == Ok::<Seq<Row>, SqlError>(outs),
    ensures
        eval_query(db, ctx, Query::Project { exprs, input: Box::new(input) }) == Ok::<Relation, SqlError>(outs),
{
    lemma_eval_project(db, ctx, exprs, Box::new(input));
}

/// One step of the GROUP BY denotation under a context.
proof fn lemma_gb_unfold(db: Database, ctx: Row, keys: Seq<Expr>, aggs: Seq<Agg>, input: Query, rows: Relation,
    prep: Seq<(Row, Row)>)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(rows),
        collect(group_input_results(db, ctx, rows, keys, aggs)) == Ok::<Seq<(Row, Row)>, SqlError>(prep),
    ensures
        eval_query(db, ctx, Query::GroupBy { keys, aggs, input: Box::new(input) })
            == group_rows(aggs, prep.map_values(|p: (Row, Row)| p.0), prep.map_values(|p: (Row, Row)| p.1)),
{
    lemma_eval_group_by(db, ctx, keys, aggs, Box::new(input));
    lemma_collect_pointwise::<Row>();
    let (ks, avs) = (prep.map_values(|p: (Row, Row)| p.0), prep.map_values(|p: (Row, Row)| p.1));
    assert(collect(group_results(aggs, ks, avs)) == group_rows(aggs, ks, avs));
}

/// One step of the `e op ANY (q)` denotation.
proof fn lemma_anycmp_unfold(db: Database, env: Row, op: CmpOp, e: Expr, q: Query, v: Val, rows: Relation)
    requires
        eval_expr(db, env, e) == Ok::<Val, SqlError>(v),
        eval_query(db, env, q) == Ok::<Relation, SqlError>(rows),
    ensures
        eval_pred(db, env, Pred::AnyCmp { op, e, q: Box::new(q) }) == any_cmp_truth(op, v, rows),
{
}

/// The SUM argument list on `ctx ++ lineitem row`: the quantity.
pub proof fn lemma_sub_args(db: Database, env: Row, v: Val)
    requires eval_expr(db, env, Expr::Col(37)) == Ok::<Val, SqlError>(v),
    ensures agg_args(db, env, sub_aggs()) == Ok::<Row, SqlError>(seq![v]),
{
    let rs = agg_arg_results(db, env, sub_aggs());
    lemma_agg_arg_results_index(db, env, sub_aggs());
    assert(rs[0] == agg_arg(db, env, sub_aggs()[0]));
    assert(rs.len() == 1);
    assert(rs.drop_last().len() == 0);
    assert(collect(rs.drop_last()) == Ok::<Seq<Val>, SqlError>(Seq::empty()));
    assert(rs.last() == Ok::<Val, SqlError>(v));
    assert(Seq::<Val>::empty().push(v) =~= seq![v]);
}

/// One column reference as a one-element list.
pub proof fn lemma_one_col(db: Database, env: Row, i: nat)
    requires i < env.len(),
    ensures eval_exprs(db, env, seq![Expr::Col(i)]) == Ok::<Row, SqlError>(seq![env[i as int]]),
{
    assert(seq![Expr::Col(i)] =~= col_exprs(seq![i]));
    lemma_eval_cols(db, env, seq![i]);
    assert(select(env, seq![i]) =~= seq![env[i as int]]);
}

/// The prepared (key, arguments) of every lineitem row under a 33-column environment.
proof fn lemma_sub_prep(db: Database, m: M, ctx: Row)
    requires sub_ok(db, m), ctx.len() == 33,
    ensures ({
        let t0 = db.tables[0];
        let xs = lrel(db);
        collect(group_input_results(db, ctx, t0, seq![Expr::Col(33)], sub_aggs()))
            == Ok::<Seq<(Row, Row)>, SqlError>(Seq::new(t0.len(), |i: int| ((sub_g().key)(xs[i]), arg_vals(sub_g(), xs[i]))))
    }),
{
    let t0 = db.tables[0];
    let g = sub_g();
    let xs = lrel(db);
    lemma_widths(db);
    lemma_proj_all_index(t0, lcols());
    let prep = Seq::new(t0.len(), |i: int| ((g.key)(xs[i]), arg_vals(g, xs[i])));
    let pre = group_input_results(db, ctx, t0, seq![Expr::Col(33)], sub_aggs());
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] pre[i] == Ok::<(Row, Row), SqlError>(prep[i]) by {
        super::subqrow::lemma_sub_prep_at(db, m, ctx, i);
    }
    lemma_collect_all(pre, prep);
}

/// The subquery's GROUP BY under a 33-column environment: the normal form's group rows.
pub proof fn lemma_sub_gb(db: Database, m: M, ctx: Row)
    requires sub_ok(db, m), ctx.len() == 33,
    ensures eval_query(db, ctx, sub_gb()) == Ok::<Relation, SqlError>(sub_rows(db)),
{
    hide(group_rows);
    let t0 = db.tables[0];
    let g = sub_g();
    let xs = lrel(db);
    lemma_widths(db);
    lemma_proj_all_index(t0, lcols());
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(t0));
    let prep = Seq::new(t0.len(), |i: int| ((g.key)(xs[i]), arg_vals(g, xs[i])));
    lemma_sub_prep(db, m, ctx);
    lemma_gb_unfold(db, ctx, seq![Expr::Col(33)], sub_aggs(), Query::Table(0), t0, prep);
    lemma_qrows_all(g, xs);
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= qkeys(g, xs));
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= qrows(g, xs).map_values(|x: Row| arg_vals(g, x)));
    lemma_sub_keys_exact(db, m);
    lemma_sub_caps(db, m);
    lemma_groups(g, sub_aggs(), xs);
}

/// `$1` as a numeric of scale 0.
proof fn lemma_lim(db: Database, env: Row, ps: Seq<Literal>)
    requires param_domain(ps),
    ensures eval_expr(db, env, lim_expr(ps)) == Ok::<Val, SqlError>(Val::Num { coeff: qp_of(ps).lim, scale: 0 }),
{
    let v = qp_of(ps).lim;
    assert(ps[0] == Literal::Int { v, kind: IntKind::Int4 });
    assert(crate::spec::int::int_in_range(IntKind::Int4, v)) by {
        assert(crate::spec::limits::int4_min() == -2147483648 && crate::spec::limits::int4_max() == 2147483647) by (compute);
    }
    assert(eval_expr(db, env, Expr::Lit(ps[0])) == Ok::<Val, SqlError>(Val::Int(v)));
}

/// HAVING on one group row under the environment.
proof fn lemma_having_row(db: Database, env: Row, ps: Seq<Literal>, s: int)
    requires param_domain(ps), env.len() == 35, env[34] == (Val::Num { coeff: s, scale: 2 }),
    ensures eval_pred(db, env, sub_pred(ps)) == Ok::<Truth, SqlError>(truth_of(s > thr(qp_of(ps)))),
{
    let lim = qp_of(ps).lim;
    lemma_lim(db, env, ps);
    lemma_expr_col(db, env, 34);
    lemma_compare_num(s, 2, lim, 0);
    assert(max_nat(2, 0) == 2);
    lemma_align_same(s, 2);
    assert(pow10(2) == 100) by (compute);
    lemma_align_by(lim, 0, 2, 100);
    lemma_pred_cmp(db, env, CmpOp::Gt, Expr::Col(34), lim_expr(ps), Val::Num { coeff: s, scale: 2 },
        Val::Num { coeff: lim, scale: 0 }, s, 100 * lim);
}

/// The group rows are `(Int key, numeric sum of scale 2)`; HAVING's truth on row `i` is its sum against `$1`.
proof fn lemma_sub_truths(db: Database, m: M, ctx: Row, ps: Seq<Literal>)
    requires sub_ok(db, m), ctx.len() == 33, param_domain(ps),
    ensures
        collect(filter_results(db, ctx, sub_rows(db), sub_pred(ps))) == Ok::<Seq<Truth>, SqlError>(sub_truths(db, qp_of(ps))),
{
    let p = qp_of(ps);
    let rows = sub_rows(db);
    let prs = filter_results(db, ctx, rows, sub_pred(ps));
    let truths = sub_truths(db, p);
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        lemma_sub_row(db, m, i);
        let k = gkeys(sub_g(), lrel(db))[i];
        let s = gsum(sub_g(), lrel(db), k, 0);
        let env = ctx + rows[i];
        assert(env.len() == 35);
        assert(env[34] == rows[i][1]);
        lemma_having_row(db, env, ps, s);
    }
    lemma_collect_all(prs, truths);
}

/// HAVING under a 33-column environment: the kept group rows.
pub proof fn lemma_sub_filter(db: Database, m: M, ctx: Row, ps: Seq<Literal>)
    requires sub_ok(db, m), ctx.len() == 33, param_domain(ps),
    ensures eval_query(db, ctx, sub_filter(ps)) == Ok::<Relation, SqlError>(sub_kept(db, qp_of(ps))),
{
    lemma_sub_gb(db, m, ctx);
    lemma_sub_truths(db, m, ctx, ps);
    lemma_filter_unfold(db, ctx, sub_pred(ps), sub_gb(), sub_rows(db), sub_truths(db, qp_of(ps)));
}

/// The rows HAVING keeps are group rows: `(Int key, sum)`.
proof fn lemma_kept_rows_shape(db: Database, m: M, p: QP)
    requires sub_ok(db, m),
    ensures
        forall|i: int| 0 <= i < sub_kept(db, p).len() ==> (#[trigger] sub_kept(db, p)[i]).len() == 2 && sub_kept(db, p)[i][0] is Int,
{
    let rows = sub_rows(db);
    let kept = sub_kept(db, p);
    assert forall|i: int| 0 <= i < kept.len() implies (#[trigger] kept[i]).len() == 2 && kept[i][0] is Int by {
        lemma_keep_true_member(rows, sub_truths(db, p), i);
        let t = choose|t: int| 0 <= t < rows.len() && rows[t] == kept[i];
        lemma_sub_row(db, m, t);
    }
}

/// SELECT l_orderkey over the kept rows, under a 33-column environment.
proof fn lemma_sub_select(db: Database, m: M, ctx: Row, p: QP)
    requires sub_ok(db, m), ctx.len() == 33,
    ensures
        collect(project_results(db, ctx, sub_kept(db, p), seq![Expr::Col(33)])) == Ok::<Seq<Row>, SqlError>(sub_out(db, p)),
{
    let kept = sub_kept(db, p);
    let rs = project_results(db, ctx, kept, seq![Expr::Col(33)]);
    let out = sub_out(db, p);
    lemma_kept_rows_shape(db, m, p);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(out[i]) by {
        let env = ctx + kept[i];
        assert(kept[i].len() == 2);
        assert(env[33] == kept[i][0]);
        lemma_one_col(db, env, 33);
    }
    lemma_collect_all(rs, out);
}

/// The subquery under a 33-column environment: the kept keys.
pub proof fn lemma_sub_q(db: Database, m: M, ctx: Row, ps: Seq<Literal>)
    requires sub_ok(db, m), ctx.len() == 33, param_domain(ps),
    ensures
        eval_query(db, ctx, sub_q(ps)) == Ok::<Relation, SqlError>(sub_out(db, qp_of(ps))),
        forall|i: int| 0 <= i < sub_out(db, qp_of(ps)).len() ==>
            (#[trigger] sub_out(db, qp_of(ps))[i]).len() == 1 && sub_out(db, qp_of(ps))[i][0] is Int,
{
    let p = qp_of(ps);
    lemma_sub_filter(db, m, ctx, ps);
    lemma_sub_select(db, m, ctx, p);
    lemma_project_unfold(db, ctx, seq![Expr::Col(33)], sub_filter(ps), sub_kept(db, p), sub_out(db, p));
    lemma_kept_rows_shape(db, m, p);
    let out = sub_out(db, p);
    assert forall|i: int| 0 <= i < out.len() implies (#[trigger] out[i]).len() == 1 && out[i][0] is Int by {
        assert(out[i] == seq![sub_kept(db, p)[i][0]]);
    }
}

/// The subquery's rows hold `(v)` exactly when key `v` is big on the model.
proof fn lemma_sub_out_contains(db: Database, m: M, p: QP, v: int)
    requires sub_ok(db, m),
    ensures sub_out(db, p).contains(seq![Val::Int(v)]) <==> big(m, p, v),
{
    let g = sub_g();
    let xs = lrel(db);
    let gk = gkeys(g, xs);
    let rows = sub_rows(db);
    let truths = sub_truths(db, p);
    let kept = sub_kept(db, p);
    let out = sub_out(db, p);
    let s = seq![Val::Int(v)];
    lemma_sub_acc(db, m, v);
    lemma_gkeys(g, xs);
    lemma_kept_rows_shape(db, m, p);
    if out.contains(s) {
        let i = choose|i: int| 0 <= i < out.len() && out[i] == s;
        assert(out[i] == seq![kept[i][0]]);
        assert(out[i][0] == kept[i][0]);
        assert(kept[i][0] == Val::Int(v));
        assert(kept.contains(kept[i]));
        lemma_keep_true_contains(rows, truths, kept[i]);
        let t = choose|t: int| 0 <= t < rows.len() && rows[t] == kept[i] && #[trigger] truths[t] is True;
        lemma_sub_row(db, m, t);
        let k = gk[t];
        assert(k =~= s);
        assert(gk.contains(k));
    }
    if big(m, p, v) {
        assert(gk.contains(s));
        let t = choose|t: int| 0 <= t < gk.len() && gk[t] == s;
        lemma_sub_row(db, m, t);
        assert(truths[t] is True);
        lemma_keep_true_contains(rows, truths, rows[t]);
        assert(kept.contains(rows[t]));
        let i = choose|i: int| 0 <= i < kept.len() && kept[i] == rows[t];
        assert(out[i] =~= s);
    }
}

/// `o_orderkey IN (subquery)` on a joined row whose o_orderkey is `ok`: whether `ok` is big on the model.
pub proof fn lemma_in_pred(db: Database, m: M, ps: Seq<Literal>, env: Row, ok: int)
    requires sub_ok(db, m), param_domain(ps), env.len() == 33, env[8] == Val::Int(ok),
    ensures eval_pred(db, env, in_pred(ps)) == Ok::<Truth, SqlError>(truth_of(big(m, qp_of(ps), ok))),
{
    hide(any_cmp_truth);
    let p = qp_of(ps);
    lemma_expr_col(db, env, 8);
    lemma_sub_q(db, m, env, ps);
    lemma_anycmp_unfold(db, env, CmpOp::Eq, Expr::Col(8), sub_q(ps), Val::Int(ok), sub_out(db, p));
    reveal(any_cmp_truth);
    lemma_any_eq_ints(ok, sub_out(db, p));
    lemma_sub_out_contains(db, m, p, ok);
}

} // verus!
