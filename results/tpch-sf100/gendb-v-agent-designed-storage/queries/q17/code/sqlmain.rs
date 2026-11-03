//! The statement `Project [SUM / 7.0] (Aggregate [SUM(l_extendedprice)] (Filter where (lineitem x part)))` over a
//! typed database, from the value model (`vals`):
//! - the WHERE condition of a joined row `l ++ p` is `vals::kept` of its value rows (`lemma_row_pred`), so the filter
//!   keeps `keep(product, qx)` (`lemma_eval_filter_q`);
//! - any per-row term over the product is a sum over part value rows of sums over lineitem value rows
//!   (`lemma_prod_sum`), so SUM, the number of kept rows and their absolute mass are the per-part totals `psum`,
//!   `pcnt`, `pmass` summed over the part rows (`lemma_eval_agg`);
//! - the projection divides by `7.0` (`lemma_final`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::fns::div::*;
use crate::spec::text::lex_cmp;
use crate::link::join::*;
use crate::link::query::{proj, proj_all};
use crate::link::expr::{ival, tval};
use crate::link::source::lemma_proj_all_index;
use crate::bridge::collect::lemma_collect_all;
use crate::exec::domain::{fits_expr, fits_exprs, lemma_fits_exprs_unfold};
use crate::exec::relational::domain::{fits_query, filter_results, agg_args_results, project_results, project_fs};
use crate::query::*;
use super::vals::*;
use super::typed::*;
use super::sqlsub::*;

verus! {

// ------------------------------------------------------------------------------------------------ the AST

/// The text of a text literal.
pub open spec fn ptext(l: Literal) -> Seq<u8> {
    match l {
        Literal::Text(b) => b,
        _ => Seq::empty(),
    }
}

/// `p_partkey = l_partkey` (n8).
pub open spec fn pred_pk() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(16), b: Expr::Col(1) }
}

/// `p_brand = $1` (n12).
pub open spec fn pred_brand(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Lit(ps[0]) }
}

/// `p_container = $2` (n17).
pub open spec fn pred_cont(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(22), b: Expr::Lit(ps[1]) }
}

/// `l_quantity < (subquery)` (n34).
pub open spec fn pred_lt() -> Pred {
    Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(4), b: sub_expr() }
}

/// The WHERE condition (n35).
pub open spec fn pred_q(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::And(Box::new(Pred::And(Box::new(pred_pk()), Box::new(pred_brand(ps)))), Box::new(pred_cont(ps)))),
        Box::new(pred_lt()),
    )
}

/// `FROM lineitem, part` (n38).
pub open spec fn product_q() -> Query {
    Query::Product { left: Box::new(Query::Table(0)), right: Box::new(Query::Table(3)) }
}

/// The filtered product (n39).
pub open spec fn filter_q(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: pred_q(ps), input: Box::new(product_q()) }
}

/// `SUM(l_extendedprice)` (n5).
pub open spec fn sum_agg() -> Agg {
    Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(5) }
}

/// The aggregate (n40).
pub open spec fn agg_q(ps: Seq<Literal>) -> Query {
    Query::Aggregate { aggs: seq![sum_agg()], input: Box::new(filter_q(ps)) }
}

/// `7.0`.
pub open spec fn seven() -> Val {
    Val::Num { coeff: 70, scale: 1 }
}

/// `SUM(..) / 7.0` (n3).
pub open spec fn out_expr() -> Expr {
    Expr::Call { f: ScalarFn::DivNumeric, args: seq![Expr::Col(0), Expr::Lit(Literal::Num { coeff: 70, scale: 1 })] }
}

/// The statement: the projection of the aggregate, without ORDER BY, OFFSET or LIMIT.
pub proof fn lemma_ast(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == (Query::Project { exprs: seq![out_expr()], input: Box::new(agg_q(ps)) }),
        query_spec_at(ps).keys.len() == 0,
        query_spec_at(ps).offset == 0,
        query_spec_at(ps).limit is None,
{
    assert(query_spec_at(ps).keys =~= Seq::<OrderKey>::empty());
    assert(query_spec_at(ps).body == (Query::Project { exprs: seq![out_expr()], input: Box::new(agg_q(ps)) }));
}

// ------------------------------------------------------------------------------------------------ one joined row

/// The part columns of a joined row (p_partkey, p_brand, p_container at 16, 19, 22).
pub open spec fn xpcols() -> Seq<nat> {
    seq![16nat, 19nat, 22nat]
}

/// The value-level WHERE condition of a joined row.
pub open spec fn qx(ys: Seq<Row>, b: Seq<u8>, c: Seq<u8>) -> spec_fn(Row) -> bool {
    |x: Row| kept(ys, b, c, proj(x, lcols()), proj(x, xpcols()))
}

/// The value rows of a joined row are the value rows of its lineitem and part rows.
pub proof fn lemma_joined_proj(l: Row, p: Row)
    requires l.len() == 16, p.len() == 9,
    ensures
        proj(l + p, lcols()) == proj(l, lcols()),
        proj(l + p, xpcols()) == proj(p, pcols()),
{
    assert(proj(l + p, lcols()) =~= proj(l, lcols()));
    assert(proj(l + p, xpcols()) =~= proj(p, pcols()));
}

/// An equality of texts.
pub proof fn lemma_text_eq(db: Database, env: Row, i: nat, l: Literal, a: Seq<u8>, b: Seq<u8>)
    requires i < env.len(), env[i as int] == Val::Text(a), l == Literal::Text(b),
    ensures eval_pred(db, env, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Lit(l) }) == Ok::<Truth, SqlError>(truth_of(a == b)),
{
    crate::bridge::equality::lemma_lex_cmp_zero(a, b);
    assert(eval_expr(db, env, Expr::Col(i)) == Ok::<Val, SqlError>(Val::Text(a)));
    assert(eval_expr(db, env, Expr::Lit(l)) == Ok::<Val, SqlError>(Val::Text(b)));
    assert(compare(Val::Text(a), Val::Text(b)) == Some(lex_cmp(a, b)));
    assert(cmp_truth(CmpOp::Eq, Val::Text(a), Val::Text(b)) == Ok::<Truth, SqlError>(truth_of(a == b)));
}

/// An equality of integers.
pub proof fn lemma_int_eq(db: Database, env: Row, i: nat, j: nat, a: int, b: int)
    requires i < env.len(), j < env.len(), env[i as int] == Val::Int(a), env[j as int] == Val::Int(b),
    ensures eval_pred(db, env, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Col(j) }) == Ok::<Truth, SqlError>(truth_of(a == b)),
{
    assert(eval_expr(db, env, Expr::Col(i)) == Ok::<Val, SqlError>(Val::Int(a)));
    assert(eval_expr(db, env, Expr::Col(j)) == Ok::<Val, SqlError>(Val::Int(b)));
    assert(compare(Val::Int(a), Val::Int(b)) == Some(sign(a - b)));
    assert(cmp_truth(CmpOp::Eq, Val::Int(a), Val::Int(b)) == Ok::<Truth, SqlError>(truth_of(a == b)));
}

/// `l_quantity < (subquery)` under a joined row: the comparison with `sub_val`, never an error.
proof fn lemma_lt_pred(db: Database, x: Row, pk: int)
    requires
        tables_ok(db),
        db.tables[0].len() <= 0xffff_ffff_ffff_ffff,
        x.len() == 25,
        x[16] == Val::Int(pk),
        num2(x[4]),
    ensures
        eval_pred(db, x, pred_lt()) == cmp_truth(CmpOp::Lt, x[4], sub_val(ys_of(db), pk)),
        cmp_truth(CmpOp::Lt, x[4], sub_val(ys_of(db), pk)) is Ok,
{
    lemma_eval_sub(db, x, pk);
    let sv = sub_val(ys_of(db), pk);
    assert(eval_expr(db, x, Expr::Col(4)) == Ok::<Val, SqlError>(x[4]));
    assert(sv is Null || sv is Num);
}

/// The WHERE condition from its four conjuncts' truths: true exactly when all four are true.
proof fn lemma_and4(db: Database, x: Row, ps: Seq<Literal>, t1: Truth, t2: Truth, t3: Truth, t4: Truth)
    requires
        eval_pred(db, x, pred_pk()) == Ok::<Truth, SqlError>(t1),
        eval_pred(db, x, pred_brand(ps)) == Ok::<Truth, SqlError>(t2),
        eval_pred(db, x, pred_cont(ps)) == Ok::<Truth, SqlError>(t3),
        eval_pred(db, x, pred_lt()) == Ok::<Truth, SqlError>(t4),
    ensures
        eval_pred(db, x, pred_q(ps)) is Ok,
        (eval_pred(db, x, pred_q(ps))->Ok_0 is True) == (t1 is True && t2 is True && t3 is True && t4 is True),
{
    hide(eval_expr);
    let a12 = Pred::And(Box::new(pred_pk()), Box::new(pred_brand(ps)));
    let a123 = Pred::And(Box::new(a12), Box::new(pred_cont(ps)));
    assert(eval_pred(db, x, a12) == Ok::<Truth, SqlError>(truth_and(t1, t2)));
    assert(eval_pred(db, x, a123) == Ok::<Truth, SqlError>(truth_and(truth_and(t1, t2), t3)));
    assert(eval_pred(db, x, pred_q(ps)) == Ok::<Truth, SqlError>(truth_and(truth_and(truth_and(t1, t2), t3), t4)));
}

/// The WHERE condition of the joined row of a typed lineitem row and a typed part row evaluates without error; it
/// is true exactly when the value rows are kept.
pub proof fn lemma_row_pred(db: Database, ps: Seq<Literal>, l: Row, p: Row)
    requires
        tables_ok(db),
        db.tables[0].len() <= 0xffff_ffff_ffff_ffff,
        param_domain(ps),
        lrow_ok(l),
        prow_ok(p),
    ensures
        eval_pred(db, l + p, pred_q(ps)) is Ok,
        (eval_pred(db, l + p, pred_q(ps))->Ok_0 is True) == qx(ys_of(db), ptext(ps[0]), ptext(ps[1]))(l + p),
{
    hide(eval_pred);
    let x = l + p;
    let ys = ys_of(db);
    let (b, c) = (ptext(ps[0]), ptext(ps[1]));
    lemma_joined_proj(l, p);
    let pk = ival(p[0]);
    let lk = ival(l[1]);
    assert(x.len() == 25);
    assert(x[16] == p[0] && x[1] == l[1] && x[19] == p[3] && x[22] == p[6] && x[4] == l[4]);
    reveal(eval_pred);
    lemma_int_eq(db, x, 16, 1, pk, lk);
    lemma_text_eq(db, x, 19, ps[0], tval(p[3]), b);
    lemma_text_eq(db, x, 22, ps[1], tval(p[6]), c);
    lemma_lt_pred(db, x, pk);
    let t4 = cmp_truth(CmpOp::Lt, l[4], sub_val(ys, pk))->Ok_0;
    lemma_and4(db, x, ps, truth_of(pk == lk), truth_of(tval(p[3]) == b), truth_of(tval(p[6]) == c), t4);
    let y = proj(l, lcols());
    let z = proj(p, pcols());
    assert(y[0] == l[1] && y[1] == l[4] && z[0] == p[0] && z[1] == p[3] && z[2] == p[6]);
}

/// `keep_true` of truths that are `True` exactly on the rows of `f`.
pub proof fn lemma_keep_true_iff(rows: Seq<Row>, truths: Seq<Truth>, f: spec_fn(Row) -> bool)
    requires
        truths.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] truths[i] is True) == f(rows[i]),
    ensures keep_true(rows, truths) == keep(rows, f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < ri.len() implies (#[trigger] ti[i] is True) == f(ri[i]) by {
            assert(ti[i] == truths[i] && ri[i] == rows[i]);
        }
        lemma_keep_true_iff(ri, ti, f);
        assert((truths.last() is True) == f(rows.last()));
    }
}

/// The FROM product of a database.
pub open spec fn prod_of(db: Database) -> Seq<Row> {
    product_rows(db.tables[0], db.tables[3])
}

/// Row `i` of the product is lineitem row `i / |part|` joined with part row `i % |part|`.
pub proof fn lemma_prod_at(db: Database, i: int)
    requires 0 <= i < prod_of(db).len(),
    ensures ({
        let np = db.tables[3].len() as int;
        &&& np > 0
        &&& 0 <= i / np < db.tables[0].len()
        &&& 0 <= i % np < np
        &&& prod_of(db)[i] == db.tables[0][i / np] + db.tables[3][i % np]
    }),
{
    let (l, p) = (db.tables[0], db.tables[3]);
    let np = p.len() as int;
    lemma_product_index(l, p);
    assert(np > 0) by {
        if np == 0 {
            assert(prod_of(db).len() == l.len() * 0);
        }
    }
    let a = i / np;
    let b = i % np;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, np);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(i, np);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(i, np);
    assert(i == a * np + b) by (nonlinear_arith) requires i == np * a + b;
    assert(a < l.len()) by (nonlinear_arith) requires i == a * np + b, 0 <= b, i < l.len() * np, np > 0;
    assert(prod_of(db)[a * np + b] == l[a] + p[b]);
}

/// The filtered product: the rows of `lineitem x part` whose value rows are kept.
pub proof fn lemma_eval_filter_q(db: Database, ps: Seq<Literal>)
    requires
        tables_ok(db),
        db.tables[0].len() <= 0xffff_ffff_ffff_ffff,
        param_domain(ps),
    ensures
        eval_query(db, Seq::empty(), filter_q(ps))
            == Ok::<Relation, SqlError>(keep(prod_of(db), qx(ys_of(db), ptext(ps[0]), ptext(ps[1])))),
{
    let ctx = Seq::<Val>::empty();
    let pr = prod_of(db);
    let f = qx(ys_of(db), ptext(ps[0]), ptext(ps[1]));
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(db.tables[0]));
    assert(eval_query(db, ctx, Query::Table(3)) == Ok::<Relation, SqlError>(db.tables[3]));
    assert(eval_query(db, ctx, product_q()) == Ok::<Relation, SqlError>(pr));
    crate::exec::relational::domain::lemma_eval_filter(db, ctx, pred_q(ps), Box::new(product_q()));
    let rs = filter_results(db, ctx, pr, pred_q(ps));
    let truths = Seq::new(pr.len(), |i: int| rs[i]->Ok_0);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(truths[i])
        && ((truths[i] is True) == f(pr[i])) by {
        lemma_prod_at(db, i);
        let np = db.tables[3].len() as int;
        let (l, p) = (db.tables[0][i / np], db.tables[3][i % np]);
        assert(ctx + pr[i] =~= l + p);
        lemma_row_pred(db, ps, l, p);
    }
    lemma_collect_all(rs, truths);
    assert forall|i: int| 0 <= i < pr.len() implies (#[trigger] truths[i] is True) == f(pr[i]) by {
        assert(rs[i] == Ok::<Truth, SqlError>(truths[i]));
    }
    lemma_keep_true_iff(pr, truths, f);
}

// ------------------------------------------------------------------------------------------------ sums over the product

/// One part row's inner sum over the lineitem rows is the sum over the lineitem value rows.
proof fn lemma_inner_part(db: Database, h: spec_fn(Row, Row) -> int, pp: Row)
    requires tables_ok(db), prow_ok(pp),
    ensures
        sum_of(db.tables[0], |ll: Row| (|x: Row| h(proj(x, lcols()), proj(x, xpcols())))(ll + pp))
            == sum_of(ys_of(db), |y: Row| h(y, proj(pp, pcols()))),
{
    let l = db.tables[0];
    let f = |x: Row| h(proj(x, lcols()), proj(x, xpcols()));
    let lm = |r: Row| proj(r, lcols());
    let z = proj(pp, pcols());
    let hz = |y: Row| h(y, z);
    lemma_proj_all_index(l, lcols());
    assert(ys_of(db) == l.map_values(lm));
    assert forall|i: int| 0 <= i < l.len() implies (|ll: Row| f(ll + pp))(#[trigger] l[i]) == (|r: Row| hz(lm(r)))(l[i]) by {
        assert(lrow_ok(l[i]));
        lemma_joined_proj(l[i], pp);
    }
    lemma_sum_of_ext(l, |ll: Row| f(ll + pp), |r: Row| hz(lm(r)));
    lemma_sum_of_map(l, lm, hz);
}

/// A per-row term of the product that reads only the joined row's value rows is a sum, over the part value rows,
/// of sums over the lineitem value rows.
pub proof fn lemma_prod_sum(db: Database, h: spec_fn(Row, Row) -> int)
    requires tables_ok(db),
    ensures
        sum_of(prod_of(db), |x: Row| h(proj(x, lcols()), proj(x, xpcols())))
            == sum_of(zs_of(db), |z: Row| sum_of(ys_of(db), |y: Row| h(y, z))),
{
    let (l, p) = (db.tables[0], db.tables[3]);
    let f = |x: Row| h(proj(x, lcols()), proj(x, xpcols()));
    lemma_sum_of_product_swap(l, p, f);
    let inner = |pp: Row| sum_of(l, |ll: Row| f(ll + pp));
    let g = |z: Row| sum_of(ys_of(db), |y: Row| h(y, z));
    let pm = |r: Row| proj(r, pcols());
    lemma_proj_all_index(p, pcols());
    assert(zs_of(db) == p.map_values(pm));
    assert forall|j: int| 0 <= j < p.len() implies #[trigger] inner(p[j]) == (|r: Row| g(pm(r)))(p[j]) by {
        assert(prow_ok(p[j]));
        lemma_inner_part(db, h, p[j]);
    }
    lemma_sum_of_ext(p, inner, |r: Row| g(pm(r)));
    lemma_sum_of_map(p, pm, g);
}

/// The SUM argument values (l_extendedprice) of rows.
pub open spec fn price_vals(ks: Seq<Row>) -> Seq<Val> {
    ks.map_values(|x: Row| x[5])
}

/// The argument rows `[l_extendedprice]` of rows.
pub open spec fn price_args(ks: Seq<Row>) -> Seq<Row> {
    Seq::new(ks.len(), |i: int| seq![ks[i][5]])
}

/// Every price a numeric of scale 2: all numeric, all non-NULL, exact sum at scale 2 (scale 0 when empty).
pub proof fn lemma_price_sum(ks: Seq<Row>)
    requires forall|i: int| 0 <= i < ks.len() ==> num2(#[trigger] ks[i][5]),
    ensures
        all_of_kind(NumKind::Numeric, price_vals(ks)),
        count_non_null(price_vals(ks)) == ks.len(),
        num_sum(price_vals(ks)) == (sum_of(ks, |x: Row| ival(x[5])), if ks.len() > 0 { 2nat } else { 0nat }),
    decreases ks.len(),
{
    let vs = price_vals(ks);
    if ks.len() > 0 {
        let d = ks.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies num2(#[trigger] d[i][5]) by {
            assert(d[i] == ks[i]);
        }
        lemma_price_sum(d);
        assert(vs.drop_last() =~= price_vals(d));
        assert(num2(ks[ks.len() - 1][5]));
        let c = ival(ks.last()[5]);
        assert(vs.last() == Val::Num { coeff: c, scale: 2 });
        assert(pow10(0) == 1);
        let s = num_sum(price_vals(d));
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

/// Bounds of a sum by a sum of absolute bounds.
pub proof fn lemma_sum_of_within(rows: Seq<Row>, f: spec_fn(Row) -> int, g: spec_fn(Row) -> int)
    requires forall|i: int| 0 <= i < rows.len() ==> -g(#[trigger] rows[i]) <= f(rows[i]) <= g(rows[i]),
    ensures -sum_of(rows, g) <= sum_of(rows, f) <= sum_of(rows, g),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert forall|i: int| 0 <= i < ri.len() implies -g(#[trigger] ri[i]) <= f(ri[i]) <= g(ri[i]) by {
            assert(ri[i] == rows[i]);
        }
        lemma_sum_of_within(ri, f, g);
        assert(-g(rows[rows.len() - 1]) <= f(rows[rows.len() - 1]) <= g(rows[rows.len() - 1]));
    }
}

/// The per-part totals of a database and binding.
pub open spec fn tot_sum(db: Database, ps: Seq<Literal>) -> int {
    sum_of(zs_of(db), |z: Row| psum(ys_of(db), ptext(ps[0]), ptext(ps[1]), z))
}

pub open spec fn tot_cnt(db: Database, ps: Seq<Literal>) -> int {
    sum_of(zs_of(db), |z: Row| pcnt(ys_of(db), ptext(ps[0]), ptext(ps[1]), z))
}

pub open spec fn tot_mass(db: Database, ps: Seq<Literal>) -> int {
    sum_of(zs_of(db), |z: Row| pmass(ys_of(db), ptext(ps[0]), ptext(ps[1]), z))
}

/// The aggregate row's value: NULL without a kept row, else the exact sum at scale 2.
pub open spec fn agg_val(db: Database, ps: Seq<Literal>) -> Val {
    if tot_cnt(db, ps) == 0 { Val::Null } else { Val::Num { coeff: tot_sum(db, ps), scale: 2 } }
}

/// The totals: the count is the number of kept rows, the sum their SUM, both bounded.
pub proof fn lemma_totals(db: Database, ps: Seq<Literal>)
    requires
        tables_ok(db),
        db.tables[0].len() <= 0xffff_ffff_ffff_ffff,
    ensures ({
        let (b, c) = (ptext(ps[0]), ptext(ps[1]));
        let ks = keep(prod_of(db), qx(ys_of(db), b, c));
        &&& tot_cnt(db, ps) == ks.len()
        &&& tot_sum(db, ps) == sum_of(ks, |x: Row| ival(x[5]))
        &&& 0 <= tot_mass(db, ps) <= db.tables[0].len() * p15()
        &&& -tot_mass(db, ps) <= tot_sum(db, ps) <= tot_mass(db, ps)
        &&& tot_cnt(db, ps) >= 0
    }),
{
    let (b, c) = (ptext(ps[0]), ptext(ps[1]));
    let ys = ys_of(db);
    let zs = zs_of(db);
    let pr = prod_of(db);
    let f = qx(ys, b, c);
    let ks = keep(pr, f);
    lemma_value_rows(db);
    // the count and the sum over the kept rows are sums over the product
    let hs = |y: Row, z: Row| tsum(ys, b, c, z)(y);
    let hc = |y: Row, z: Row| tcnt(ys, b, c, z)(y);
    let hm = |y: Row, z: Row| tmass(ys, b, c, z)(y);
    lemma_prod_sum(db, hs);
    lemma_prod_sum(db, hc);
    lemma_prod_sum(db, hm);
    assert forall|j: int| 0 <= j < zs.len() implies (|z: Row| sum_of(ys, |y: Row| hs(y, z)))(#[trigger] zs[j])
        == (|z: Row| psum(ys, b, c, z))(zs[j])
        && (|z: Row| sum_of(ys, |y: Row| hc(y, z)))(zs[j]) == (|z: Row| pcnt(ys, b, c, z))(zs[j])
        && (|z: Row| sum_of(ys, |y: Row| hm(y, z)))(zs[j]) == (|z: Row| pmass(ys, b, c, z))(zs[j]) by {
        let z = zs[j];
        lemma_sum_of_ext(ys, |y: Row| hs(y, z), tsum(ys, b, c, z));
        lemma_sum_of_ext(ys, |y: Row| hc(y, z), tcnt(ys, b, c, z));
        lemma_sum_of_ext(ys, |y: Row| hm(y, z), tmass(ys, b, c, z));
    }
    lemma_sum_of_ext(zs, |z: Row| sum_of(ys, |y: Row| hs(y, z)), |z: Row| psum(ys, b, c, z));
    lemma_sum_of_ext(zs, |z: Row| sum_of(ys, |y: Row| hc(y, z)), |z: Row| pcnt(ys, b, c, z));
    lemma_sum_of_ext(zs, |z: Row| sum_of(ys, |y: Row| hm(y, z)), |z: Row| pmass(ys, b, c, z));
    let xs = |x: Row| hs(proj(x, lcols()), proj(x, xpcols()));
    let xc = |x: Row| hc(proj(x, lcols()), proj(x, xpcols()));
    lemma_keep_members(pr, f);
    assert forall|i: int| 0 <= i < pr.len() && !f(#[trigger] pr[i]) implies xs(pr[i]) == 0 && xc(pr[i]) == 0 by {}
    lemma_sum_of_keep(pr, f, xs);
    lemma_sum_of_keep(pr, f, xc);
    assert forall|i: int| 0 <= i < ks.len() implies xs(#[trigger] ks[i]) == (|x: Row| ival(x[5]))(ks[i]) && xc(ks[i]) == 1 by {
        assert(f(ks[i]));
        assert(pr.contains(ks[i]));
        let m = choose|m: int| 0 <= m < pr.len() && pr[m] == ks[i];
        lemma_prod_at(db, m);
        let np = db.tables[3].len() as int;
        assert(lrow_ok(db.tables[0][m / np]));
        assert(prow_ok(db.tables[3][m % np]));
        lemma_joined_proj(db.tables[0][m / np], db.tables[3][m % np]);
        assert(proj(ks[i], lcols())[2] == ks[i][5]);
    }
    lemma_sum_of_ext(ks, xs, |x: Row| ival(x[5]));
    lemma_sum_of_const(ks, xc, 1);
    // bounds
    lemma_mass_bound(ys, zs, b, c);
    assert forall|j: int| 0 <= j < zs.len() implies -(|z: Row| pmass(ys, b, c, z))(#[trigger] zs[j])
        <= (|z: Row| psum(ys, b, c, z))(zs[j]) <= (|z: Row| pmass(ys, b, c, z))(zs[j])
        && (|z: Row| pcnt(ys, b, c, z))(zs[j]) >= 0 by {
        lemma_part_sums(ys, b, c, zs[j]);
    }
    lemma_sum_of_within(zs, |z: Row| psum(ys, b, c, z), |z: Row| pmass(ys, b, c, z));
}

// ------------------------------------------------------------------------------------------------ the aggregate

/// Joined typed rows: 25 columns, a numeric(15, 2) price.
pub open spec fn rows25_ok(ks: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < ks.len() ==> #[trigger] ks[i].len() == 25 && num2(ks[i][5])
}

/// Rows kept from the product are joined typed rows.
proof fn lemma_kept_typed(db: Database, f: spec_fn(Row) -> bool)
    requires tables_ok(db),
    ensures rows25_ok(keep(prod_of(db), f)),
{
    let pr = prod_of(db);
    let ks = keep(pr, f);
    lemma_keep_members(pr, f);
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] ks[i].len() == 25 && num2(ks[i][5]) by {
        assert(pr.contains(ks[i]));
        let m = choose|m: int| 0 <= m < pr.len() && pr[m] == ks[i];
        lemma_prod_at(db, m);
        let np = db.tables[3].len() as int;
        let (l, p) = (db.tables[0][m / np], db.tables[3][m % np]);
        assert(lrow_ok(l));
        assert(prow_ok(p));
        assert(ks[i] == l + p);
        assert((l + p)[5] == l[5]);
    }
}

/// The SUM arguments of rows of 25 columns, collected.
proof fn lemma_sum_args(db: Database, ks: Seq<Row>)
    requires rows25_ok(ks),
    ensures
        collect(agg_args_results(db, Seq::empty(), ks, seq![sum_agg()])) == Ok::<Seq<Row>, SqlError>(price_args(ks)),
        column(price_args(ks), 0) == price_vals(ks),
{
    let ctx = Seq::<Val>::empty();
    let rs = agg_args_results(db, ctx, ks, seq![sum_agg()]);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(price_args(ks)[i]) by {
        let env = ctx + ks[i];
        assert(env =~= ks[i]);
        let ars = agg_arg_results(db, env, seq![sum_agg()]);
        assert(ars[0] == agg_arg(db, env, sum_agg()));
        assert(agg_arg(db, env, sum_agg()) == eval_expr(db, env, Expr::Col(5)));
        lemma_collect_all(ars, seq![ks[i][5]]);
    }
    lemma_collect_all(rs, price_args(ks));
    assert(column(price_args(ks), 0) =~= price_vals(ks));
}

/// The SUM over the kept rows is `agg_val`.
proof fn lemma_sum_value(db: Database, ps: Seq<Literal>)
    requires
        tables_ok(db),
        db.tables[0].len() <= 0xffff_ffff_ffff_ffff,
    ensures ({
        let ks = keep(prod_of(db), qx(ys_of(db), ptext(ps[0]), ptext(ps[1])));
        agg_value(sum_agg(), price_vals(ks)) == Ok::<Val, SqlError>(agg_val(db, ps))
    }),
{
    let ks = keep(prod_of(db), qx(ys_of(db), ptext(ps[0]), ptext(ps[1])));
    lemma_totals(db, ps);
    lemma_kept_typed(db, qx(ys_of(db), ptext(ps[0]), ptext(ps[1])));
    assert forall|i: int| 0 <= i < ks.len() implies num2(#[trigger] ks[i][5]) by {
        assert(ks[i].len() == 25);
    }
    lemma_price_sum(ks);
    let t = tot_sum(db, ps);
    if ks.len() > 0 {
        assert(abs(t) <= 0x8000_0000_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
            requires -tot_mass(db, ps) <= t <= tot_mass(db, ps), tot_mass(db, ps) <= db.tables[0].len() * p15(),
                db.tables[0].len() <= 0xffff_ffff_ffff_ffff, p15() == 1_000_000_000_000_000;
        lemma_num_in_range_small(t, 2);
    }
}

/// The aggregate node: one row holding `agg_val`.
pub proof fn lemma_eval_agg(db: Database, ps: Seq<Literal>)
    requires
        tables_ok(db),
        db.tables[0].len() <= 0xffff_ffff_ffff_ffff,
        param_domain(ps),
    ensures
        eval_query(db, Seq::empty(), agg_q(ps)) == Ok::<Relation, SqlError>(seq![seq![agg_val(db, ps)]]),
{
    let ctx = Seq::<Val>::empty();
    let f = qx(ys_of(db), ptext(ps[0]), ptext(ps[1]));
    let ks = keep(prod_of(db), f);
    lemma_eval_filter_q(db, ps);
    lemma_kept_typed(db, f);
    lemma_sum_args(db, ks);
    lemma_sum_value(db, ps);
    let args = price_args(ks);
    let v = agg_val(db, ps);
    lemma_agg_row_one(sum_agg(), args, v);
    lemma_aggregate_one(db, filter_q(ps), sum_agg(), ks, args, seq![v]);
}

/// A one-aggregate row from that aggregate's value.
proof fn lemma_agg_row_one(a: Agg, args: Seq<Row>, v: Val)
    requires agg_value(a, column(args, 0)) == Ok::<Val, SqlError>(v),
    ensures agg_row(seq![a], args) == Ok::<Row, SqlError>(seq![v]),
{
    let vs = Seq::new(1, |j: int| agg_value(seq![a][j], column(args, j)));
    assert(vs[0] == agg_value(a, column(args, 0)));
    lemma_collect_all(vs, seq![v]);
}

/// A one-aggregate node over an input of rows `ks` with collected arguments `args` and aggregate row `row`.
proof fn lemma_aggregate_one(db: Database, input: Query, a: Agg, ks: Seq<Row>, args: Seq<Row>, row: Row)
    requires
        eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(ks),
        collect(agg_args_results(db, Seq::empty(), ks, seq![a])) == Ok::<Seq<Row>, SqlError>(args),
        agg_row(seq![a], args) == Ok::<Row, SqlError>(row),
    ensures
        eval_query(db, Seq::empty(), Query::Aggregate { aggs: seq![a], input: Box::new(input) }) == Ok::<Relation, SqlError>(seq![row]),
{
    hide(agg_row);
    hide(collect);
    crate::exec::relational::domain::lemma_eval_aggregate(db, Seq::empty(), seq![a], Box::new(input));
}

// ------------------------------------------------------------------------------------------------ the projection

/// `SUM / 7.0` on the aggregate row: its value, and its domain.
pub proof fn lemma_out_eval(db: Database, v: Val)
    ensures
        eval_expr(db, seq![v], out_expr()) == apply_div(ScalarFn::DivNumeric, seq![v, seven()]),
        fits_expr(db, seq![v], out_expr()) == fits_div(ScalarFn::DivNumeric, seq![v, seven()]),
{
    let env = seq![v];
    let lit = Expr::Lit(Literal::Num { coeff: 70, scale: 1 });
    assert(num_in_range(70, 1)) by (compute);
    assert(1 <= crate::spec::limits::numeric_dscale_max()) by (compute);
    assert(eval_expr(db, env, lit) == Ok::<Val, SqlError>(seven()));
    assert(eval_expr(db, env, Expr::Col(0)) == Ok::<Val, SqlError>(v));
    let es = seq![Expr::Col(0), lit];
    let e1s = seq![Expr::Col(0)];
    assert(es.drop_last() =~= e1s);
    assert(e1s.drop_last() =~= Seq::<Expr>::empty());
    lemma_eval_exprs_step(db, env, es);
    lemma_eval_exprs_step(db, env, e1s);
    lemma_eval_exprs_empty(db, env);
    lemma_fits_exprs_unfold(db, env, es);
    lemma_fits_exprs_unfold(db, env, e1s);
    assert(fits_exprs(db, env, Seq::<Expr>::empty()));
    assert(fits_expr(db, env, Expr::Col(0)));
    assert(fits_expr(db, env, lit));
    assert(Seq::<Val>::empty().push(v) =~= seq![v]);
    assert(seq![v].push(seven()) =~= seq![v, seven()]);
    assert(eval_exprs(db, env, es) == Ok::<Row, SqlError>(seq![v, seven()]));
    assert(fits_exprs(db, env, es));
}

/// The statement from its aggregate row `[v]`: the division's outcome, and outside the capacity domain when the
/// division is outside its domain.
pub proof fn lemma_final(db: Database, ps: Seq<Literal>, v: Val)
    requires eval_query(db, Seq::empty(), agg_q(ps)) == Ok::<Relation, SqlError>(seq![seq![v]]),
    ensures
        denote_body(db, query_spec_at(ps)) == match apply_div(ScalarFn::DivNumeric, seq![v, seven()]) {
            Ok(w) => Ok::<Relation, SqlError>(seq![seq![w]]),
            Err(e) => Err::<Relation, SqlError>(e),
        },
        !fits_div(ScalarFn::DivNumeric, seq![v, seven()]) ==> !fits_query(db, Seq::empty(), query_spec_at(ps).body),
{
    lemma_ast(ps);
    let ctx = Seq::<Val>::empty();
    let exprs = seq![out_expr()];
    let rows = seq![seq![v]];
    assert(ctx + rows[0] =~= seq![v]);
    crate::exec::relational::domain::lemma_eval_project(db, ctx, exprs, Box::new(agg_q(ps)));
    let prs = project_results(db, ctx, rows, exprs);
    lemma_out_eval(db, v);
    lemma_one_expr(db, seq![v], out_expr());
    assert(prs[0] == eval_exprs(db, seq![v], exprs));
    match apply_div(ScalarFn::DivNumeric, seq![v, seven()]) {
        Ok(w) => {
            lemma_collect_all(prs, seq![seq![w]]);
        },
        Err(e) => {
            reveal_with_fuel(collect, 2);
            assert(prs.drop_last() =~= Seq::<Result<Row, SqlError>>::empty());
        },
    }
    if !fits_div(ScalarFn::DivNumeric, seq![v, seven()]) {
        let fs = project_fs(db, ctx, rows, exprs);
        crate::exec::relational::domain::lemma_project_fs_index(db, ctx, rows, exprs);
        lemma_fits_exprs_unfold(db, seq![v], exprs);
        assert(exprs.drop_last() =~= Seq::<Expr>::empty());
        assert(!fs[0]);
        crate::link::capacity::lemma_fits_each_violation(prs, fs, 0);
    }
}

} // verus!
