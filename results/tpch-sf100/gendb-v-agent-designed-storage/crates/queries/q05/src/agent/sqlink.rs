//! The link from the Q5 statement to its normal form: on a well-formed database of the schema, the body
//! (`GROUP BY n_name` over the filtered product) evaluates to the normal form's result rows over the product of
//! the stored relations (`lemma_body_ok`); when `$2 + INTERVAL '1' YEAR` fails, the body is that error on a
//! non-empty product and empty otherwise (`lemma_body_err`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::datetime::*;
use crate::spec::typing::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::equality::*;
use crate::schema::schema_spec;
use crate::query::{param_domain, query_spec_at};
use crate::bridge::equality::same_exact_type;
use crate::link::query::*;
use crate::link::join::*;
use crate::link::capacity::*;
use crate::exec::relational::domain::lemma_eval_filter;
use crate::agent::q5spec::*;
use crate::agent::sqlrow::*;

verus! {

/// The joined full rows of the FROM product.
pub open spec fn full_rows(db: Database) -> Seq<Row> {
    joined_of(db.tables, tids())
}

/// Every joined full row has the statement's column shapes.
pub proof fn lemma_rows_typed(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures forall|k: int| 0 <= k < full_rows(db).len() ==> full_shape(#[trigger] full_rows(db)[k]),
{
    let ok = |i: int, x: Row| part_in_table(i, x);
    lemma_inputs_ok(db);
    lemma_joined_parts(db.tables, tids(), full_ws(), ok);
    assert forall|k: int| 0 <= k < full_rows(db).len() implies full_shape(#[trigger] full_rows(db)[k]) by {
        lemma_full_shape(full_rows(db)[k]);
    }
}

/// Projecting the joined full rows on the stored columns gives the product of the stored relations.
pub proof fn lemma_xs(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures proj_all(full_rows(db), q5_cols()) == xs_of(rels_of_db(db)),
{
    let ok = |i: int, x: Row| part_in_table(i, x);
    let rs = rels_of_db(db);
    lemma_inputs_ok(db);
    lemma_q5_cols();
    assert forall|i: int, c: int| 0 <= i < full_ws().len() && 0 <= c < fcols6()[i].len()
        implies #[trigger] fcols6()[i][c] < full_ws()[i] by {
        assert(fcols6()[0] == seq![0nat, 1, 2, 3, 4, 5, 6, 7]);
        assert(fcols6()[1] == seq![0nat, 1, 2, 3, 4, 5, 7]);
        assert(fcols6()[2] == seq![0nat, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]);
        assert(fcols6()[3] == seq![0nat, 1, 2, 3, 4, 5, 6]);
        assert(fcols6()[4] == seq![0nat, 1, 2, 3]);
        assert(fcols6()[5] == seq![0nat, 1, 2]);
    }
    let pts = pts_of(rs);
    assert forall|i: int| 0 <= i < tids().len() implies
        #[trigger] pts[inputs6()[i] as int] == proj_all(db.tables[tids()[i] as int], fcols6()[i]) by {
        if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {} else {}
    }
    lemma_proj_joined(db.tables, tids(), pts, inputs6(), full_ws(), fcols6(), ok);
    lemma_joined6(pts, inputs6());
}

/// The WHERE condition agrees with `q5_qual` on every joined full row.
pub proof fn lemma_pred_agrees(db: Database, ps: Seq<Literal>, prm: Prm, t0: int)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_domain(ps),
        prm == prm_of(ps, prm.hi),
        date_to_ts(prm.lo) == Ok::<int, SqlError>(t0),
        ts_add_interval(t0, 12, 0, 0) == Ok::<int, SqlError>(prm.hi),
    ensures pred_agrees(db, full_rows(db), q5_cols(), q5_pred(ps), q5_g(prm)),
{
    lemma_rows_typed(db);
    let rows = full_rows(db);
    assert forall|i: int| 0 <= i < rows.len() implies
        eval_pred(db, #[trigger] rows[i], q5_pred(ps)) == Ok::<Truth, SqlError>(truth_of((q5_g(prm).qual)(proj(rows[i], q5_cols())))) by {
        lemma_pred_row(db, rows[i], ps, prm, t0);
    }
}

/// The group key and the SUM argument agree with the normal form on every joined full row; the key is exact text.
pub proof fn lemma_group_agrees(db: Database, prm: Prm)
    requires db.schema == schema_spec(), db_wf(db),
    ensures
        keys_agree(db, full_rows(db), q5_cols(), q5_key_exprs(), q5_g(prm)),
        args_agree(db, full_rows(db), q5_cols(), q5_aggs(), q5_g(prm)),
        aggs_match(q5_aggs(), q5_g(prm)),
        keys_exact(q5_g(prm), proj_all(full_rows(db), q5_cols())),
{
    lemma_rows_typed(db);
    let g = q5_g(prm);
    let rows = full_rows(db);
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], q5_cols())) implies
        eval_exprs(db, rows[i], q5_key_exprs()) == Ok::<Row, SqlError>((g.key)(proj(rows[i], q5_cols()))) by {
        lemma_key_row(db, rows[i]);
    }
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], q5_cols())) implies
        agg_args(db, rows[i], q5_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[i], q5_cols()))) by {
        lemma_arg_row(db, rows[i]);
        let y = proj(rows[i], q5_cols());
        assert(arg_vals(g, y) =~= seq![Val::Num { coeff: q5_arg(y), scale: 4 }]);
    }
    assert(agg_matches(q5_aggs()[0], g.aggs[0]));
    let xs = proj_all(rows, q5_cols());
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        lemma_proj_positions(rows[a]);
        lemma_proj_positions(rows[b]);
        assert(xs[a] == proj(rows[a], q5_cols()));
        assert(xs[b] == proj(rows[b], q5_cols()));
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert(ka[0] is Text && kb[0] is Text);
        assert forall|i: int| 0 <= i < ka.len() implies same_exact_type(#[trigger] ka[i], kb[i]) by {}
        lemma_row_exact(ka, kb);
    }
}

/// The normal form's output row of a group is its full row (key, SUM): the select is the identity.
pub proof fn lemma_out_rows(prm: Prm, xs: Seq<Row>)
    ensures
        result_rows(q5_g(prm), xs) == gkeys(q5_g(prm), xs).map_values(|k: Row| full_row(q5_g(prm), xs, k)),
{
    let g = q5_g(prm);
    let ks = gkeys(g, xs);
    lemma_gkeys(g, xs);
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] out_row(g, xs, ks[i]) == full_row(g, xs, ks[i]) by {
        lemma_gkeys_witness(g, xs, ks[i]);
        let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], ks[i]);
        assert(ks[i] == q5_key(xs[m]));
        assert(ks[i].len() == 1);
        let fr = full_row(g, xs, ks[i]);
        assert(fr.len() == 2);
        assert(select(fr, g.outs) =~= fr);
    }
    assert(result_rows(g, xs) =~= ks.map_values(|k: Row| full_row(g, xs, k)));
}

/// The statement body evaluates to the normal form's result rows over the stored relations, inside `group_caps`.
pub proof fn lemma_body_ok(db: Database, ps: Seq<Literal>, prm: Prm, t0: int)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_domain(ps),
        prm == prm_of(ps, prm.hi),
        date_to_ts(prm.lo) == Ok::<int, SqlError>(t0),
        ts_add_interval(t0, 12, 0, 0) == Ok::<int, SqlError>(prm.hi),
        group_caps(q5_g(prm), xs_of(rels_of_db(db))),
    ensures
        denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(q5_g(prm), xs_of(rels_of_db(db)))),
{
    let g = q5_g(prm);
    let rows = full_rows(db);
    let xs = xs_of(rels_of_db(db));
    lemma_query_shape(ps);
    assert(db.tables.len() == 8) by {
        assert(schema_spec().len() == 8) by (compute);
    }
    lemma_from_eval(db);
    lemma_xs(db);
    lemma_pred_agrees(db, ps, prm, t0);
    lemma_group_agrees(db, prm);
    lemma_filter_rows(db, q5_from(), rows, q5_cols(), q5_pred(ps), g);
    lemma_group_query(db, rows, q5_cols(), q5_filter(ps), q5_key_exprs(), q5_aggs(), g);
    lemma_out_rows(prm, xs);
}

/// When `$2 + INTERVAL '1' YEAR` fails with `e`: on a non-empty product every row's WHERE condition fails with
/// `e`, so the body is `e`; on an empty product the body is empty.
pub proof fn lemma_body_err(db: Database, ps: Seq<Literal>, e: SqlError)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_domain(ps),
        forall|env: Row| eval_expr(db, env, #[trigger] hi_expr(ps)) == Err::<Val, SqlError>(e),
    ensures
        full_rows(db).len() > 0 ==> denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(e),
        full_rows(db).len() == 0 ==> denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
{
    let rows = full_rows(db);
    let ctx = Seq::<Val>::empty();
    lemma_query_shape(ps);
    assert(db.tables.len() == 8) by {
        assert(schema_spec().len() == 8) by (compute);
    }
    lemma_from_eval(db);
    if rows.len() > 0 {
        lemma_filter_fails(db, ps, e);
        lemma_first_input(db, ctx, q5_body(ps));
    } else {
        lemma_filter_empty(db, ps);
        lemma_group_empty(db, q5_filter(ps));
    }
}

/// On a non-empty product the WHERE condition fails with `e` on every row: the filter is `e`.
proof fn lemma_filter_fails(db: Database, ps: Seq<Literal>, e: SqlError)
    requires
        db.schema == schema_spec(), db_wf(db), db.tables.len() == 8,
        param_domain(ps),
        forall|env: Row| eval_expr(db, env, #[trigger] hi_expr(ps)) == Err::<Val, SqlError>(e),
        full_rows(db).len() > 0,
        eval_query(db, Seq::empty(), q5_from()) == Ok::<Relation, SqlError>(full_rows(db)),
    ensures eval_query(db, Seq::empty(), q5_filter(ps)) == Err::<Relation, SqlError>(e),
{
    let rows = full_rows(db);
    let ctx = Seq::<Val>::empty();
    lemma_rows_typed(db);
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, ctx + rows[k], q5_pred(ps)) is Ok
        || eval_pred(db, ctx + rows[k], q5_pred(ps)) == Err::<Truth, SqlError>(e) by {
        assert(ctx + rows[k] =~= rows[k]);
        lemma_pred_row_err(db, rows[k], ps, e);
    }
    assert(ctx + rows[0] =~= rows[0]);
    lemma_pred_row_err(db, rows[0], ps, e);
    lemma_filter_err(db, ctx, q5_pred(ps), Box::new(q5_from()), rows, e, 0);
}

/// On an empty product the filter is empty.
proof fn lemma_filter_empty(db: Database, ps: Seq<Literal>)
    requires
        full_rows(db).len() == 0,
        eval_query(db, Seq::empty(), q5_from()) == Ok::<Relation, SqlError>(full_rows(db)),
    ensures eval_query(db, Seq::empty(), q5_filter(ps)) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
{
    let ctx = Seq::<Val>::empty();
    let rows = full_rows(db);
    lemma_eval_filter(db, ctx, q5_pred(ps), Box::new(q5_from()));
    let rs = crate::exec::relational::domain::filter_results(db, ctx, rows, q5_pred(ps));
    assert(rs.len() == 0);
    assert(rs =~= Seq::<Result<Truth, SqlError>>::empty());
    assert(collect(rs) == Ok::<Seq<Truth>, SqlError>(Seq::<Truth>::empty()));
    assert(keep_true(rows, Seq::<Truth>::empty()) =~= Seq::<Row>::empty());
}

/// A GROUP BY over an empty input has no groups.
proof fn lemma_group_empty(db: Database, input: Query)
    requires eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
    ensures
        eval_query(db, Seq::empty(), Query::GroupBy { keys: q5_key_exprs(), aggs: q5_aggs(), input: Box::new(input) })
            == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
{
    let ctx = Seq::<Val>::empty();
    let e = Seq::<Row>::empty();
    crate::exec::relational::domain::lemma_eval_group_by(db, ctx, q5_key_exprs(), q5_aggs(), Box::new(input));
    let gi = crate::exec::relational::domain::group_input_results(db, ctx, e, q5_key_exprs(), q5_aggs());
    assert(gi =~= Seq::<Result<(Row, Row), SqlError>>::empty());
    assert(collect(gi) == Ok::<Seq<(Row, Row)>, SqlError>(Seq::<(Row, Row)>::empty()));
    let prepared = Seq::<(Row, Row)>::empty();
    assert(prepared.map_values(|p: (Row, Row)| p.0) =~= e);
    assert(prepared.map_values(|p: (Row, Row)| p.1) =~= e);
    let gr = crate::exec::relational::domain::group_results(q5_aggs(), e, e);
    assert(distinct_rows(e) =~= e);
    assert(gr =~= Seq::<Result<Row, SqlError>>::empty());
    assert(collect(gr) == Ok::<Seq<Row>, SqlError>(e));
}

} // verus!
