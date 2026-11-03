//! The statement body of Q12 (`GROUP BY` over `WHERE` over `orders x lineitem`) in terms of the normal form
//! (`agent::normal`): its rows when every group sum fits int8 (`lemma_body_ok`), the exact SQL error of a sum beyond
//! int8 (`lemma_body_sum_err`), and the error of the upper bound `$3 + 1 year` outside the timestamp range on a
//! non-empty FROM (`lemma_body_hi_err`).
//!
//! Every lemma takes a database whose orders and lineitem rows carry the kinds the statement reads (`body_hyps`);
//! `from_rows(db)` is the FROM relation and `xs = proj_all(from_rows(db), j_cols())` its projection.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::link::query::*;
use crate::link::capacity::{lemma_filter_err, lemma_first_input};
use crate::agent::common::int_groups::*;
use crate::agent::normal::*;

verus! {

/// An orders row as the statement reads it.
pub open spec fn o_row_ok(r: Row) -> bool {
    r.len() == 9 && r[0] is Int && r[5] is Text
}

/// A lineitem row as the statement reads it.
pub open spec fn l_row_ok(r: Row) -> bool {
    r.len() == 16 && r[0] is Int && r[10] is Date && r[11] is Date && r[12] is Date && r[14] is Text
}

/// Hypotheses shared by the lemmas: the tables' rows and the parameters.
pub open spec fn body_hyps(db: Database, ps: Seq<Literal>, pd: int) -> bool {
    &&& db.tables.len() > 1
    &&& forall|j: int| 0 <= j < db.tables[1].len() ==> o_row_ok(#[trigger] db.tables[1][j])
    &&& forall|i: int| 0 <= i < db.tables[0].len() ==> l_row_ok(#[trigger] db.tables[0][i])
    &&& params_ok(ps, pd)
}

/// The FROM relation `orders x lineitem`.
pub open spec fn from_rows(db: Database) -> Seq<Row> {
    product_rows(db.tables[1], db.tables[0])
}

/// The normal form at the parameters with upper bound `t1`.
pub open spec fn g_at(ps: Seq<Literal>, pd: int, t1: int) -> QuerySpec {
    q12_spec(p1_of(ps), p2_of(ps), pd, t1)
}

/// Every row of a product is the concatenation of one left and one right row.
pub proof fn lemma_product_row(a: Seq<Row>, b: Seq<Row>, k: int)
    requires 0 <= k < product_rows(a, b).len(),
    ensures exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && product_rows(a, b)[k] == a[i] + b[j],
{
    crate::link::join::lemma_product_index(a, b);
    let nb = b.len() as int;
    assert(nb > 0) by (nonlinear_arith) requires 0 <= k < a.len() * nb, a.len() >= 0;
    let i = k / nb;
    let j = k % nb;
    assert(k == i * nb + j && 0 <= j < nb) by (nonlinear_arith) requires nb > 0, i == k / nb, j == k % nb;
    assert(0 <= i < a.len()) by (nonlinear_arith) requires nb > 0, i == k / nb, 0 <= k < a.len() * nb;
    assert(product_rows(a, b)[i * nb + j] == a[i] + b[j]);
}

/// FROM evaluates to the product, and every joined row has the kinds the statement reads.
pub proof fn lemma_from(db: Database, ps: Seq<Literal>, pd: int)
    requires body_hyps(db, ps, pd),
    ensures
        eval_query(db, Seq::empty(), ast_from()) == Ok::<Relation, SqlError>(from_rows(db)),
        forall|k: int| 0 <= k < from_rows(db).len() ==> j_row_ok(#[trigger] from_rows(db)[k]),
{
    let f = from_rows(db);
    let ctx = Seq::<Val>::empty();
    assert(eval_query(db, ctx, Query::Table(1)) == Ok::<Relation, SqlError>(db.tables[1]));
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(db.tables[0]));
    assert(eval_query(db, ctx, ast_from()) == Ok::<Relation, SqlError>(f));
    assert forall|k: int| 0 <= k < f.len() implies j_row_ok(#[trigger] f[k]) by {
        lemma_product_row(db.tables[1], db.tables[0], k);
        let (i, j) = choose|i: int, j: int| 0 <= i < db.tables[1].len() && 0 <= j < db.tables[0].len()
            && f[k] == db.tables[1][i] + db.tables[0][j];
        assert(o_row_ok(db.tables[1][i]));
        assert(l_row_ok(db.tables[0][j]));
        let (o, l) = (db.tables[1][i], db.tables[0][j]);
        assert((o + l)[0] == o[0] && (o + l)[5] == o[5]);
        assert((o + l)[9] == l[0] && (o + l)[19] == l[10] && (o + l)[20] == l[11] && (o + l)[21] == l[12] && (o + l)[23] == l[14]);
    }
}

/// Projected joined rows: seven values, the ship mode a text.
pub proof fn lemma_xs_ok(rows: Seq<Row>)
    requires forall|k: int| 0 <= k < rows.len() ==> j_row_ok(#[trigger] rows[k]),
    ensures
        proj_all(rows, j_cols()).len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] proj_all(rows, j_cols())[i]).len() == 7
            && proj_all(rows, j_cols())[i][6] is Text,
{
    let xs = proj_all(rows, j_cols());
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] xs[i]).len() == 7 && xs[i][6] is Text by {
        assert(xs[i] == proj(rows[i], j_cols()));
        lemma_proj_row(rows[i]);
    }
}

/// The WHERE of the body evaluates to the kept rows of the normal form.
pub proof fn lemma_input(db: Database, ps: Seq<Literal>, pd: int, t1: int)
    requires
        body_hyps(db, ps, pd),
        from_rows(db).len() > 0 ==> hi_res(pd) == Ok::<int, SqlError>(t1),
    ensures
        eval_query(db, Seq::empty(), ast_input(ps))
            == Ok::<Relation, SqlError>(keep_true(from_rows(db), qual_truths(g_at(ps, pd, t1), proj_all(from_rows(db), j_cols())))),
{
    hide(eval_pred);
    let g = g_at(ps, pd, t1);
    let f = from_rows(db);
    lemma_from(db, ps, pd);
    assert forall|i: int| 0 <= i < f.len() implies
        eval_pred(db, #[trigger] f[i], ast_pred(ps)) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(f[i], j_cols())))) by {
        lemma_pred_row(db, f[i], ps, pd, t1);
    }
    assert(pred_agrees(db, f, j_cols(), ast_pred(ps), g));
    lemma_filter_rows(db, ast_from(), f, j_cols(), ast_pred(ps), g);
}

/// Per-row agreement of the keys and aggregate arguments, and exact keys.
pub proof fn lemma_agree(db: Database, ps: Seq<Literal>, pd: int, t1: int)
    requires body_hyps(db, ps, pd),
    ensures
        keys_agree(db, from_rows(db), j_cols(), ast_keys(), g_at(ps, pd, t1)),
        int_args_agree(db, from_rows(db), j_cols(), ast_aggs(), g_at(ps, pd, t1)),
        keys_exact(g_at(ps, pd, t1), proj_all(from_rows(db), j_cols())),
        int4_sums(ast_aggs(), g_at(ps, pd, t1)),
{
    hide(eval_exprs);
    hide(agg_args);
    let g = g_at(ps, pd, t1);
    let f = from_rows(db);
    lemma_from(db, ps, pd);
    assert forall|i: int| 0 <= i < f.len() && (g.qual)(proj(#[trigger] f[i], j_cols())) implies
        eval_exprs(db, f[i], ast_keys()) == Ok::<Row, SqlError>((g.key)(proj(f[i], j_cols()))) by {
        lemma_keys_row(db, f[i]);
    }
    assert forall|j: int, x: Row| #[trigger] (g.arg)(j, x) == arg_of(j, x) by {}
    assert forall|i: int| 0 <= i < f.len() && (g.qual)(proj(#[trigger] f[i], j_cols())) implies
        agg_args(db, f[i], ast_aggs()) == Ok::<Row, SqlError>(int_args(g, proj(f[i], j_cols()))) by {
        lemma_args_row(db, f[i], g);
    }
    lemma_xs_ok(f);
    assert forall|x: Row| #[trigger] (g.key)(x) == seq![x[6]] by {}
    lemma_keys_exact(g, proj_all(f, j_cols()));
    lemma_aggs_int4(g);
}

/// With int8 sums the body is the normal form's GROUP BY rows.
pub proof fn lemma_body_ok(db: Database, ps: Seq<Literal>, pd: int, t1: int)
    requires
        body_hyps(db, ps, pd),
        from_rows(db).len() > 0 ==> hi_res(pd) == Ok::<int, SqlError>(t1),
        int_caps(g_at(ps, pd, t1), proj_all(from_rows(db), j_cols())),
    ensures
        eval_query(db, Seq::empty(), ast_body(ps))
            == Ok::<Relation, SqlError>(int_result_rows(g_at(ps, pd, t1), proj_all(from_rows(db), j_cols()))),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    lemma_input(db, ps, pd, t1);
    lemma_agree(db, ps, pd, t1);
    lemma_int_group_query(db, from_rows(db), j_cols(), ast_input(ps), ast_keys(), ast_aggs(), g_at(ps, pd, t1));
}

/// A group whose sum `j` leaves int8: the body is the error 22003.
pub proof fn lemma_body_sum_err(db: Database, ps: Seq<Literal>, pd: int, t1: int, k: Row, j: int)
    requires
        body_hyps(db, ps, pd),
        from_rows(db).len() > 0 ==> hi_res(pd) == Ok::<int, SqlError>(t1),
        gcount(g_at(ps, pd, t1), proj_all(from_rows(db), j_cols()), k) > 0,
        0 <= j < 2,
        !int_in_range(IntKind::Int8, gsum(g_at(ps, pd, t1), proj_all(from_rows(db), j_cols()), k, j)),
    ensures
        eval_query(db, Seq::empty(), ast_body(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    lemma_input(db, ps, pd, t1);
    lemma_agree(db, ps, pd, t1);
    lemma_int_group_err(db, from_rows(db), j_cols(), ast_input(ps), ast_keys(), ast_aggs(), g_at(ps, pd, t1), k, j);
}

/// The upper bound fails on a non-empty FROM: the body's meaning is that error.
pub proof fn lemma_body_hi_err(db: Database, ps: Seq<Literal>, pd: int, e: SqlError)
    requires
        body_hyps(db, ps, pd),
        hi_res(pd) == Err::<int, SqlError>(e),
        from_rows(db).len() > 0,
    ensures eval_query(db, Seq::empty(), ast_body(ps)) == Err::<Relation, SqlError>(e),
{
    hide(eval_pred);
    let ctx = Seq::<Val>::empty();
    let f = from_rows(db);
    lemma_from(db, ps, pd);
    assert forall|k: int| 0 <= k < f.len() implies #[trigger] eval_pred(db, ctx + f[k], ast_pred(ps)) is Ok
        || eval_pred(db, ctx + f[k], ast_pred(ps)) == Err::<Truth, SqlError>(e) by {
        assert(ctx + f[k] =~= f[k]);
        lemma_pred_row_err(db, f[k], ps, pd, e);
    }
    assert(ctx + f[0] =~= f[0]);
    lemma_pred_row_err(db, f[0], ps, pd, e);
    lemma_filter_err(db, ctx, ast_pred(ps), Box::new(ast_from()), f, e, 0);
    lemma_first_input(db, ctx, ast_body(ps));
}

} // verus!
