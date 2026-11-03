//! The statement's body over the three tables (`tables::Tabs`).
//!
//! FROM is the left-major product `partsupp x part` (`prod`); its row `i * |part| + j` is `ps[i] ++ p[j]`. Without a
//! failing `p_type LIKE $2` (or without rows) the WHERE keeps exactly the rows satisfying `q_row`
//! (`lemma_eval_filter_ok`); with one, the WHERE is the error of the first part row whose LIKE fails, when partsupp
//! has rows (`lemma_eval_filter_err`). The GROUP BY then groups the kept rows by `key_of` with the argument `arg_of`
//! (`lemma_eval_body`), whose outcome `common::distinct` states.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::link::join::{keep, lemma_keep_members, lemma_product_index};
use crate::exec::relational::domain::filter_results;
use crate::bridge::collect::{lemma_collect_all, lemma_collect_first_err, lemma_collect_pointwise};
use super::common::relops::*;
use super::sqlq::*;
use super::tables::Tabs;

verus! {

// ------------------------------------------------------------------------------------------------ tables

/// The statement's three tables in a database.
pub open spec fn tabs_of(db: Database) -> Tabs {
    Tabs { p: db.tables[3], ps: db.tables[4], s: db.tables[5] }
}

pub open spec fn p_typed(r: Row) -> bool {
    r.len() == 9 && r[0] is Int && r[3] is Text && r[4] is Text && r[5] is Int
}

pub open spec fn ps_typed(r: Row) -> bool {
    r.len() == 5 && r[0] is Int && r[1] is Int
}

/// The value shapes of every row the statement reads.
pub open spec fn tabs_typed(t: Tabs) -> bool {
    &&& forall|j: int| 0 <= j < t.p.len() ==> #[trigger] p_typed(t.p[j])
    &&& forall|i: int| 0 <= i < t.ps.len() ==> #[trigger] ps_typed(t.ps[i])
    &&& forall|j: int| 0 <= j < t.s.len() ==> #[trigger] s_shape(t.s[j])
}

/// FROM partsupp, part.
pub open spec fn prod(t: Tabs) -> Seq<Row> {
    product_rows(t.ps, t.p)
}

/// FROM evaluates to `prod` (in any context).
pub proof fn lemma_eval_from(db: Database, ctx: Row)
    requires db.tables.len() == 8,
    ensures eval_query(db, ctx, q_from()) == Ok::<Relation, SqlError>(prod(tabs_of(db))),
{
    assert(eval_query(db, ctx, Query::Table(3)) == Ok::<Relation, SqlError>(db.tables[3]));
    assert(eval_query(db, ctx, Query::Table(4)) == Ok::<Relation, SqlError>(db.tables[4]));
}

/// A row of the product is `ps[i] ++ p[j]` with its types.
pub proof fn lemma_prod_row(t: Tabs, x: Row)
    requires tabs_typed(t), prod(t).contains(x),
    ensures
        xrow_ok(x),
        exists|i: int, j: int| 0 <= i < t.ps.len() && 0 <= j < t.p.len() && x == #[trigger] t.ps[i] + #[trigger] t.p[j],
{
    lemma_product_split(t.ps, t.p, x);
    let (i, j) = choose|i: int, j: int| 0 <= i < t.ps.len() && 0 <= j < t.p.len() && x == #[trigger] t.ps[i] + #[trigger] t.p[j];
    assert(ps_typed(t.ps[i]) && p_typed(t.p[j]));
    assert(x[0] == t.ps[i][0] && x[1] == t.ps[i][1] && x[5] == t.p[j][0]);
    assert(x[8] == t.p[j][3] && x[9] == t.p[j][4] && x[10] == t.p[j][5]);
}

// ------------------------------------------------------------------------------------------------ WHERE

/// The WHERE in normal form (on rows whose LIKE does not fail).
pub open spec fn q_row(t: Tabs, m: Prm, x: Row) -> bool {
    pre_q(m, x) && !in_sub(t.s, x[1])
}

pub open spec fn q_f(t: Tabs, m: Prm) -> spec_fn(Row) -> bool {
    |x: Row| q_row(t, m, x)
}

/// The rows the WHERE keeps.
pub open spec fn kept(t: Tabs, m: Prm) -> Seq<Row> {
    keep(prod(t), q_f(t, m))
}

/// No part row's `p_type LIKE $2` fails.
pub open spec fn like_all_ok(t: Tabs, m: Prm) -> bool {
    forall|j: int| 0 <= j < t.p.len() ==> #[trigger] like_res(t.p[j][4], m.pat) is Ok
}

/// The WHERE on one row of the product.
pub proof fn lemma_outer_row(db: Database, ps: Seq<Literal>, x: Row)
    requires
        db.tables.len() == 8,
        tabs_typed(tabs_of(db)),
        params_ok(ps),
        prod(tabs_of(db)).contains(x),
    ensures
        xrow_ok(x),
        exists|j: int| 0 <= j < tabs_of(db).p.len() && #[trigger] tabs_of(db).p[j][4] == x[9],
        like_res(x[9], prm_of(ps).pat) matches Err(e) ==> eval_pred(db, x, outer_pred(ps)) == Err::<Truth, SqlError>(e),
        like_res(x[9], prm_of(ps).pat) is Ok ==> eval_pred(db, x, outer_pred(ps))
            == Ok::<Truth, SqlError>(truth_of(q_row(tabs_of(db), prm_of(ps), x))),
{
    let t = tabs_of(db);
    lemma_prod_row(t, x);
    let (i, j) = choose|i: int, j: int| 0 <= i < t.ps.len() && 0 <= j < t.p.len() && x == #[trigger] t.ps[i] + #[trigger] t.p[j];
    assert(ps_typed(t.ps[i]));
    assert(x[9] == t.p[j][4]);
    assert forall|q: int| 0 <= q < db.tables[5].len() implies #[trigger] s_shape(db.tables[5][q]) by {
        assert(s_shape(t.s[q]));
    }
    lemma_outer_pred(db, ps, x);
}

/// Without a failing LIKE (or without rows) the WHERE keeps exactly the `q_row` rows.
pub proof fn lemma_eval_filter_ok(db: Database, ps: Seq<Literal>)
    requires
        db.tables.len() == 8,
        tabs_typed(tabs_of(db)),
        params_ok(ps),
        like_all_ok(tabs_of(db), prm_of(ps)) || prod(tabs_of(db)).len() == 0,
    ensures
        eval_query(db, Seq::empty(), q_filter(ps)) == Ok::<Relation, SqlError>(kept(tabs_of(db), prm_of(ps))),
{
    let t = tabs_of(db);
    let m = prm_of(ps);
    let rows = prod(t);
    lemma_eval_from(db, Seq::empty());
    let rs = Seq::new(rows.len(), |i: int| eval_pred(db, Seq::<Val>::empty() + rows[i], outer_pred(ps)));
    let tv = Seq::new(rows.len(), |i: int| eval_pred(db, rows[i], outer_pred(ps))->Ok_0);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(tv[i]) by {
        assert(Seq::<Val>::empty() + rows[i] =~= rows[i]);
        assert(rows.contains(rows[i]));
        lemma_outer_row(db, ps, rows[i]);
        let j = choose|j: int| 0 <= j < t.p.len() && #[trigger] t.p[j][4] == rows[i][9];
        assert(like_res(t.p[j][4], m.pat) is Ok);
    }
    lemma_collect_all(rs, tv);
    lemma_collect_pointwise::<Truth>();
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] tv[i] is True) == q_f(t, m)(rows[i]) by {
        assert(Seq::<Val>::empty() + rows[i] =~= rows[i]);
        assert(rows.contains(rows[i]));
        lemma_outer_row(db, ps, rows[i]);
        let j = choose|j: int| 0 <= j < t.p.len() && #[trigger] t.p[j][4] == rows[i][9];
        assert(like_res(t.p[j][4], m.pat) is Ok);
    }
    lemma_keep_true_iff(rows, tv, q_f(t, m));
}

/// Rows `0 .. |part|` of the product are `ps[0] ++ p[j]`.
proof fn lemma_prod_first(t: Tabs, j: int)
    requires t.ps.len() > 0, 0 <= j < t.p.len(),
    ensures j < prod(t).len(), prod(t)[j] == t.ps[0] + t.p[j],
{
    let np = t.p.len() as int;
    lemma_product_index(t.ps, t.p);
    assert(np <= prod(t).len()) by (nonlinear_arith) requires prod(t).len() == t.ps.len() * np, t.ps.len() > 0, np >= 0;
    assert(0 * np + j == j);
}

/// The WHERE on product row `j < |part|`, through part row `j`'s LIKE.
proof fn lemma_first_row(db: Database, ps: Seq<Literal>, j: int)
    requires
        db.tables.len() == 8,
        tabs_typed(tabs_of(db)),
        params_ok(ps),
        tabs_of(db).ps.len() > 0,
        0 <= j < tabs_of(db).p.len(),
    ensures ({
        let t = tabs_of(db);
        let r = filter_results(db, Seq::empty(), prod(t), outer_pred(ps));
        &&& j < r.len()
        &&& like_res(t.p[j][4], prm_of(ps).pat) matches Err(e) ==> r[j] == Err::<Truth, SqlError>(e)
        &&& like_res(t.p[j][4], prm_of(ps).pat) is Ok ==> r[j] is Ok
    }),
{
    let t = tabs_of(db);
    lemma_prod_first(t, j);
    let x = prod(t)[j];
    assert(Seq::<Val>::empty() + x =~= x);
    assert(prod(t).contains(x));
    lemma_outer_row(db, ps, x);
    assert(ps_typed(t.ps[0]));
    assert(x[9] == t.p[j][4]);
}

/// A failing LIKE on part row `j0` (and on no earlier part row) makes the WHERE, and the body, fail with its
/// error, when partsupp has rows.
pub proof fn lemma_eval_filter_err(db: Database, ps: Seq<Literal>, j0: int, e: SqlError)
    requires
        db.tables.len() == 8,
        tabs_typed(tabs_of(db)),
        params_ok(ps),
        0 <= j0 < tabs_of(db).p.len(),
        like_res(tabs_of(db).p[j0][4], prm_of(ps).pat) == Err::<Val, SqlError>(e),
        forall|j: int| 0 <= j < j0 ==> #[trigger] like_res(tabs_of(db).p[j][4], prm_of(ps).pat) is Ok,
        tabs_of(db).ps.len() > 0,
    ensures
        eval_query(db, Seq::empty(), q_filter(ps)) == Err::<Relation, SqlError>(e),
        eval_query(db, Seq::empty(), q_body(ps)) == Err::<Relation, SqlError>(e),
{
    let t = tabs_of(db);
    let rows = prod(t);
    lemma_eval_from(db, Seq::empty());
    let fr = filter_results(db, Seq::empty(), rows, outer_pred(ps));
    let rs = Seq::new(rows.len(), |f: int| eval_pred(db, Seq::<Val>::empty() + rows[f], outer_pred(ps)));
    assert(rs =~= fr);
    assert forall|f: int| 0 <= f < j0 implies #[trigger] rs[f] is Ok by {
        lemma_first_row(db, ps, f);
    }
    lemma_first_row(db, ps, j0);
    lemma_collect_first_err(rs, j0);
    lemma_collect_pointwise::<Truth>();
    assert(eval_query(db, Seq::empty(), q_filter(ps)) == Err::<Relation, SqlError>(e));
}

// ------------------------------------------------------------------------------------------------ GROUP BY

/// The grouping key of a kept row: `p_brand, p_type, p_size`.
pub open spec fn key_of(x: Row) -> Row {
    seq![x[8], x[9], x[10]]
}

/// The aggregate argument of a kept row: `ps_suppkey`.
pub open spec fn arg_of(x: Row) -> Row {
    seq![x[1]]
}

pub open spec fn keys_of(rows: Seq<Row>) -> Seq<Row> {
    rows.map_values(|x: Row| key_of(x))
}

pub open spec fn args_of(rows: Seq<Row>) -> Seq<Row> {
    rows.map_values(|x: Row| arg_of(x))
}

/// Every kept row is a product row (so it has the outer row's types).
pub proof fn lemma_kept_rows(t: Tabs, m: Prm)
    requires tabs_typed(t),
    ensures
        forall|q: int| 0 <= q < kept(t, m).len() ==> prod(t).contains(#[trigger] kept(t, m)[q])
            && xrow_ok(kept(t, m)[q]) && q_row(t, m, kept(t, m)[q]),
{
    lemma_keep_members(prod(t), q_f(t, m));
    assert forall|q: int| 0 <= q < kept(t, m).len() implies prod(t).contains(#[trigger] kept(t, m)[q])
        && xrow_ok(kept(t, m)[q]) && q_row(t, m, kept(t, m)[q]) by {
        lemma_prod_row(t, kept(t, m)[q]);
    }
}

/// One kept row's grouping key.
proof fn lemma_key_row(db: Database, x: Row)
    requires xrow_ok(x),
    ensures eval_exprs(db, x, key_exprs()) == Ok::<Row, SqlError>(key_of(x)),
{
    let ks = expr_results(db, x, key_exprs());
    lemma_expr_results_index(db, x, key_exprs());
    assert forall|q: int| 0 <= q < ks.len() implies #[trigger] ks[q] == Ok::<Val, SqlError>(key_of(x)[q]) by {
        assert(ks[q] == eval_expr(db, x, key_exprs()[q]));
    }
    lemma_collect_all(ks, key_of(x));
}

/// One kept row's aggregate argument.
proof fn lemma_arg_row(db: Database, x: Row)
    requires xrow_ok(x),
    ensures agg_args(db, x, q_aggs()) == Ok::<Row, SqlError>(arg_of(x)),
{
    let ags = agg_arg_results(db, x, q_aggs());
    lemma_agg_arg_results_index(db, x, q_aggs());
    assert(ags[0] == agg_arg(db, x, q_aggs()[0]));
    assert(agg_arg(db, x, q_aggs()[0]) == agg_arg(db, x, Agg::Count(Expr::Col(1))));
    assert(ags[0] == Ok::<Val, SqlError>(x[1]));
    lemma_collect_all(ags, arg_of(x));
}

/// One kept row's GROUP BY input: its key and argument.
proof fn lemma_group_input_row(db: Database, x: Row)
    requires xrow_ok(x),
    ensures group_input(db, Seq::<Val>::empty() + x, key_exprs(), q_aggs())
        == Ok::<(Row, Row), SqlError>((key_of(x), arg_of(x))),
{
    assert(Seq::<Val>::empty() + x =~= x);
    lemma_key_row(db, x);
    lemma_arg_row(db, x);
}

/// The GROUP BY over the WHERE's rows: `group_rows` of their keys and arguments.
pub proof fn lemma_eval_body(db: Database, ps: Seq<Literal>)
    requires
        db.tables.len() == 8,
        tabs_typed(tabs_of(db)),
        params_ok(ps),
        eval_query(db, Seq::empty(), q_filter(ps)) == Ok::<Relation, SqlError>(kept(tabs_of(db), prm_of(ps))),
    ensures
        eval_query(db, Seq::empty(), q_body(ps)) == group_rows(q_aggs(), keys_of(kept(tabs_of(db), prm_of(ps))),
            args_of(kept(tabs_of(db), prm_of(ps)))),
{
    let t = tabs_of(db);
    let m = prm_of(ps);
    let rows = kept(t, m);
    lemma_kept_rows(t, m);
    let gis = crate::exec::relational::domain::group_input_results(db, Seq::empty(), rows, key_exprs(), q_aggs());
    let prepared = Seq::new(rows.len(), |i: int| (key_of(rows[i]), arg_of(rows[i])));
    assert forall|i: int| 0 <= i < gis.len() implies #[trigger] gis[i] == Ok::<(Row, Row), SqlError>(prepared[i]) by {
        crate::exec::relational::domain::lemma_group_input_results(db, Seq::empty(), rows, key_exprs(), q_aggs(), i);
        lemma_group_input_row(db, rows[i]);
    }
    lemma_collect_all(gis, prepared);
    assert(prepared.map_values(|p: (Row, Row)| p.0) =~= keys_of(rows));
    assert(prepared.map_values(|p: (Row, Row)| p.1) =~= args_of(rows));
    lemma_collect_pointwise::<(Row, Row)>();
}

} // verus!
