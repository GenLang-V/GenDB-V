// Normal form of `SELECT COUNT(*) AS n FROM readings WHERE value > $1` and its link to the SQL meaning.
//
// The statement is a scalar COUNT(*) over a filtered base table. Its normal form (`count_spec(p)`, a
// `link::query::QuerySpec`) has the WHERE condition `value > p` on the stored row `[value]`, the empty group key and
// one COUNT aggregate. The query loop computes `gcount(count_spec(p), rels[0], [])`, the number of stored rows whose
// value exceeds `p`; `lemma_body` shows that the statement's body evaluates to that count as one int8 row, or to
// the SQL error 22003 when the count exceeds int8 (`spec::relation::agg_value` of COUNT(*)).
//
// Layout facts used throughout: the stored relation `rels[0]` is `proj_all(db.tables[0], [0])` (the declaration's
// `stored_relations`), and each stored row is `[Int(value)]` (the flat interface's `represents`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::int::IntKind;
use crate::spec::scalar::CmpOp;
use crate::spec::limits::int8_max;
use crate::spec::eval::{eval_query, eval_pred, eval_expr, agg_args, agg_arg_results};
use crate::spec::relation::{keep_true, column, agg_value};
use crate::spec::typing::db_wf;
use crate::schema::schema_spec;
use crate::query::query_spec_at;
use crate::link::query::*;
use crate::link::source::lemma_proj_all_index;
use crate::link::expr::{lemma_expr_col, lemma_compare_int, lemma_pred_cmp};
use crate::link::capacity::{lemma_count_value, lemma_aggregate_err};
use crate::stores::flat_readings::interface::represents;
use crate::stores::flat_readings::declaration::{stored_relations, lemma_stored_relations};

verus! {

/// The WHERE condition on a stored row `[value]`: `value > p`.
pub open spec fn above(x: Row, p: int) -> bool {
    match x[0] {
        Val::Int(v) => v > p,
        _ => false,
    }
}

/// The statement's normal form at parameter value `p`: scalar COUNT(*) of the rows with `value > p`.
pub open spec fn count_spec(p: int) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| above(x, p),
        key: |x: Row| Seq::<Val>::empty(),
        arg: |j: int, x: Row| 0int,
        aggs: seq![AggKind::Count],
        outs: seq![0nat],
        grouped: false,
    }
}

/// The stored columns of table `readings`: just `value` (ordinal 0).
pub open spec fn value_cols() -> Seq<nat> {
    seq![0nat]
}

/// The statement's WHERE node at parameter value `p`.
pub open spec fn filter_q(p: int) -> Query {
    Query::Filter {
        pred: Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(0), b: Expr::Lit(Literal::Int { v: p, kind: IntKind::Int8 }) },
        input: Box::new(Query::Table(0)),
    }
}

/// The parameter binding of `$1 = p`.
pub open spec fn binding(p: int) -> Seq<Literal> {
    seq![Literal::Int { v: p, kind: IntKind::Int8 }]
}

/// A scalar key never names a non-empty group: every group's count is at most the scalar group's.
proof fn lemma_gcount_le_scalar(g: QuerySpec, rows: Seq<Row>, k: Row)
    requires scalar_key(g),
    ensures gcount(g, rows, k) <= gcount(g, rows, Seq::<Val>::empty()),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_gcount_le_scalar(g, rows.drop_last(), k);
        assert((g.key)(rows.last()) == Seq::<Val>::empty());
    }
}

/// Under a scalar key, the qualifying rows are as many as the scalar group's count.
proof fn lemma_qrows_len(g: QuerySpec, xs: Seq<Row>)
    requires scalar_key(g),
    ensures qrows(g, xs).len() == gcount(g, xs, Seq::<Val>::empty()),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_qrows_len(g, xs.drop_last());
        assert((g.key)(xs.last()) == Seq::<Val>::empty());
    }
}

/// COUNT(*) takes no argument: its argument row is `[NULL]` in every environment.
proof fn lemma_count_args(db: Database, env: Row)
    ensures agg_args(db, env, seq![Agg::CountStar]) == Ok::<Row, SqlError>(seq![Val::Null]),
{
    let rs = agg_arg_results(db, env, seq![Agg::CountStar]);
    assert(rs.len() == 1);
    assert(rs[0] == Ok::<Val, SqlError>(Val::Null));
    crate::bridge::collect::lemma_collect_all(rs, seq![Val::Null]);
}

/// The base table of a bound database: one relation whose rows are the stored rows `[Int(value)]`.
proof fn lemma_table_rows(db: Database, parts: Seq<crate::gendb_entry::layout::PartView>, rels: Seq<Seq<Row>>)
    requires
        db.schema == schema_spec(),
        db_wf(db),
        stored_relations(db) == rels,
        represents(parts, rels),
    ensures
        db.tables.len() == 1,
        eval_query(db, Seq::empty(), Query::Table(0)) == Ok::<Relation, SqlError>(db.tables[0]),
        proj_all(db.tables[0], value_cols()) == rels[0],
        forall|i: int| 0 <= i < db.tables[0].len() ==> (#[trigger] db.tables[0][i]).len() == 1
            && db.tables[0][i][0] == rels[0][i][0]
            && rels[0][i][0] is Int,
{
    lemma_stored_relations(db);
    let rows = db.tables[0];
    lemma_proj_all_index(rows, value_cols());
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] rows[i]).len() == 1
        && rows[i][0] == rels[0][i][0] && rels[0][i][0] is Int by {
        assert(crate::spec::typing::row_in_table(db.tables[0][i], db.schema[0]));
        assert(proj_all(rows, value_cols())[i][0] == rows[i][0]);
    }
}

/// WHERE `value > p` over the base table keeps the qualifying rows of the normal form, as many as its count.
proof fn lemma_filter(db: Database, parts: Seq<crate::gendb_entry::layout::PartView>, rels: Seq<Seq<Row>>, p: int)
    requires
        db.schema == schema_spec(),
        db_wf(db),
        stored_relations(db) == rels,
        represents(parts, rels),
        int8_min_le(p),
    ensures ({
        let g = count_spec(p);
        let rows = db.tables[0];
        let kept = keep_true(rows, qual_truths(g, proj_all(rows, value_cols())));
        &&& eval_query(db, Seq::empty(), filter_q(p)) == Ok::<Relation, SqlError>(kept)
        &&& kept.len() == gcount(g, rels[0], Seq::<Val>::empty())
    }),
{
    let g = count_spec(p);
    let rows = db.tables[0];
    let cols = value_cols();
    let pred = Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(0), b: Expr::Lit(Literal::Int { v: p, kind: IntKind::Int8 }) };
    lemma_table_rows(db, parts, rels);
    lemma_proj_all_index(rows, cols);
    assert forall|i: int| 0 <= i < rows.len() implies
        eval_pred(db, #[trigger] rows[i], pred) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[i], cols)))) by {
        let v = rows[i][0]->Int_0;
        lemma_expr_col(db, rows[i], 0);
        assert(eval_expr(db, rows[i], Expr::Lit(Literal::Int { v: p, kind: IntKind::Int8 })) == Ok::<Val, SqlError>(Val::Int(p)));
        lemma_compare_int(v, p);
        lemma_pred_cmp(db, rows[i], CmpOp::Gt, Expr::Col(0), Expr::Lit(Literal::Int { v: p, kind: IntKind::Int8 }),
            Val::Int(v), Val::Int(p), v, p);
        assert(proj(rows[i], cols)[0] == rows[i][0]);
    }
    assert(pred_agrees(db, rows, cols, pred, g));
    lemma_filter_rows(db, Query::Table(0), rows, cols, pred, g);
    lemma_kept_rows(g, rows, cols);
    lemma_qrows_len(g, proj_all(rows, cols));
}

/// `p` is an int8 value (so the literal `$1` evaluates without error).
pub open spec fn int8_min_le(p: int) -> bool {
    -0x8000_0000_0000_0000 <= p <= int8_max()
}

/// The statement's body at `$1 = p`: one row `[count]` when the count fits int8, else the SQL error 22003.
pub proof fn lemma_body(db: Database, parts: Seq<crate::gendb_entry::layout::PartView>, rels: Seq<Seq<Row>>, p: int)
    requires
        db.schema == schema_spec(),
        db_wf(db),
        stored_relations(db) == rels,
        represents(parts, rels),
        int8_min_le(p),
    ensures ({
        let count = gcount(count_spec(p), rels[0], Seq::<Val>::empty()) as int;
        let body = query_spec_at(binding(p)).body;
        &&& count <= int8_max() ==> eval_query(db, Seq::empty(), body) == Ok::<Relation, SqlError>(seq![seq![Val::Int(count)]])
        &&& count > int8_max() ==> eval_query(db, Seq::empty(), body) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)
    }),
{
    let g = count_spec(p);
    let rows = db.tables[0];
    let cols = value_cols();
    let aggs = seq![Agg::CountStar];
    let xs = proj_all(rows, cols);
    let kept = keep_true(rows, qual_truths(g, xs));
    let count = gcount(g, rels[0], Seq::<Val>::empty());
    let body = query_spec_at(binding(p)).body;
    lemma_table_rows(db, parts, rels);
    lemma_filter(db, parts, rels, p);
    assert(body == Query::Aggregate { aggs, input: Box::new(filter_q(p)) });
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) implies
        agg_args(db, rows[i], aggs) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[i], cols))) by {
        lemma_count_args(db, rows[i]);
        assert(arg_vals(g, proj(rows[i], cols)) =~= seq![Val::Null]);
    }
    assert(aggs_match(aggs, g));
    if count <= int8_max() {
        assert forall|k: Row, j: int| #![trigger gcount(g, xs, k), g.aggs[j]]
            0 <= j < g.aggs.len() && g.aggs[j] is Count implies gcount(g, xs, k) <= int8_max() by {
            lemma_gcount_le_scalar(g, xs, k);
        }
        assert(group_caps(g, xs));
        lemma_aggregate_query(db, rows, cols, filter_q(p), aggs, g);
        assert(full_row(g, xs, Seq::<Val>::empty()) =~= seq![Val::Int(count as int)]);
    } else {
        let args = Seq::new(kept.len(), |i: int| seq![Val::Null]);
        assert forall|i: int| 0 <= i < kept.len() implies
            #[trigger] agg_args(db, Seq::<Val>::empty() + kept[i], aggs) == Ok::<Row, SqlError>(args[i]) by {
            lemma_count_args(db, Seq::<Val>::empty() + kept[i]);
        }
        let vs = column(args, 0);
        assert(vs.len() == count);
        lemma_count_value(Agg::CountStar, vs);
        assert(agg_value(aggs[0], column(args, 0)) == Err::<Val, SqlError>(SqlError::NumericValueOutOfRange));
        lemma_aggregate_err(db, Seq::empty(), aggs, Box::new(filter_q(p)), kept, args, SqlError::NumericValueOutOfRange, 0);
    }
}

} // verus!
