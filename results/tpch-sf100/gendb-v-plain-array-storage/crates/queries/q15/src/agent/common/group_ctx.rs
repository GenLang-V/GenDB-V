//! WHERE and GROUP BY links of `link::query` under an arbitrary outer context `ctx`: a subquery evaluates its FROM
//! rows in the environment `ctx ++ row`, so its column references are shifted by `|ctx|`. Under per-row agreement
//! of the condition, the key and the aggregate arguments in that environment (`pred_agrees_at`, `keys_agree_at`,
//! `args_agree_at`), a WHERE keeps the normal form's qualifying rows (`lemma_filter_rows_at`) and a GROUP BY over
//! them is the normal form's full row of every group, in first-occurrence order (`lemma_group_query_at`), exactly
//! as `link::query` states them for the empty context.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::link::query::*;
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};

verus! {

/// The condition evaluates, in the environment `ctx ++ rows[i]`, to the normal form's truth of the projected row.
pub open spec fn pred_agrees_at(db: Database, ctx: Row, rows: Seq<Row>, cols: Seq<nat>, pred: Pred, g: QuerySpec) -> bool {
    forall|i: int| 0 <= i < rows.len() ==>
        eval_pred(db, ctx + #[trigger] rows[i], pred) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[i], cols))))
}

/// The key expressions evaluate, in `ctx ++ rows[i]` of a qualifying row, to the normal form's key.
pub open spec fn keys_agree_at(db: Database, ctx: Row, rows: Seq<Row>, cols: Seq<nat>, keys: Seq<Expr>, g: QuerySpec) -> bool {
    forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) ==>
        eval_exprs(db, ctx + rows[i], keys) == Ok::<Row, SqlError>((g.key)(proj(rows[i], cols)))
}

/// The aggregate arguments evaluate, in `ctx ++ rows[i]` of a qualifying row, to the normal form's argument values.
pub open spec fn args_agree_at(db: Database, ctx: Row, rows: Seq<Row>, cols: Seq<nat>, aggs: Seq<Agg>, g: QuerySpec) -> bool {
    forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) ==>
        agg_args(db, ctx + rows[i], aggs) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[i], cols)))
}

/// WHERE under the context `ctx` over an input that evaluates to `rows`: the rows whose projection qualifies.
pub proof fn lemma_filter_rows_at(db: Database, ctx: Row, src: Query, rows: Seq<Row>, cols: Seq<nat>, pred: Pred, g: QuerySpec)
    requires
        eval_query(db, ctx, src) == Ok::<Relation, SqlError>(rows),
        pred_agrees_at(db, ctx, rows, cols, pred, g),
    ensures
        eval_query(db, ctx, Query::Filter { pred, input: Box::new(src) })
            == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(g, proj_all(rows, cols)))),
{
    let xs = proj_all(rows, cols);
    let truths = qual_truths(g, xs);
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(xs[i] == proj(rows[i], cols));
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
}

/// The GROUP BY's prepared (key, arguments) sequence under `ctx` over the kept rows of a WHERE.
pub open spec fn prepared_at(db: Database, ctx: Row, kept: Seq<Row>, keys: Seq<Expr>, aggs: Seq<Agg>) -> Seq<Result<(Row, Row), SqlError>> {
    Seq::new(kept.len(), |i: int|
        match eval_exprs(db, ctx + kept[i], keys) {
            Err(err) => Err(err),
            Ok(k) => match agg_args(db, ctx + kept[i], aggs) {
                Err(err) => Err(err),
                Ok(a) => Ok((k, a)),
            },
        })
}

/// Per kept row under `ctx`: its key tuple and aggregate arguments.
pub proof fn lemma_prepared_at(db: Database, ctx: Row, rows: Seq<Row>, kept: Seq<Row>, cols: Seq<nat>, keys: Seq<Expr>,
    aggs: Seq<Agg>, g: QuerySpec)
    requires
        keys_agree_at(db, ctx, rows, cols, keys, g),
        args_agree_at(db, ctx, rows, cols, aggs, g),
        forall|i: int| 0 <= i < kept.len() ==> rows.contains(#[trigger] kept[i]) && (g.qual)(proj(kept[i], cols)),
    ensures
        collect(prepared_at(db, ctx, kept, keys, aggs)) == Ok::<Seq<(Row, Row)>, SqlError>(
            Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), arg_vals(g, proj(kept[i], cols))))),
{
    hide(eval_exprs);
    hide(agg_args);
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), arg_vals(g, proj(kept[i], cols))));
    let pre = prepared_at(db, ctx, kept, keys, aggs);
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] pre[i] == Ok::<(Row, Row), SqlError>(prep[i]) by {
        assert(rows.contains(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert((g.qual)(proj(rows[m], cols)));
        assert(eval_exprs(db, ctx + rows[m], keys) == Ok::<Row, SqlError>((g.key)(proj(rows[m], cols))));
        assert(agg_args(db, ctx + rows[m], aggs) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[m], cols))));
    }
    lemma_collect_all(pre, prep);
}

/// One step of the GROUP BY denotation under `ctx` over an evaluated input and its prepared sequence.
pub proof fn lemma_groupby_unfold_at(db: Database, ctx: Row, input: Query, keys: Seq<Expr>, aggs: Seq<Agg>, kept: Seq<Row>,
    prep: Seq<(Row, Row)>)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(kept),
        collect(prepared_at(db, ctx, kept, keys, aggs)) == Ok::<Seq<(Row, Row)>, SqlError>(prep),
    ensures
        eval_query(db, ctx, Query::GroupBy { keys, aggs, input: Box::new(input) })
            == group_rows(aggs, prep.map_values(|p: (Row, Row)| p.0), prep.map_values(|p: (Row, Row)| p.1)),
{
    lemma_collect_pointwise::<(Row, Row)>();
}

/// The grouped link under `ctx`: a GROUP BY over an input that evaluates (under `ctx`) to the qualifying rows of
/// `rows` is the full row of every group key, in first-occurrence order.
pub proof fn lemma_group_query_at(db: Database, ctx: Row, rows: Seq<Row>, cols: Seq<nat>, input: Query, keys: Seq<Expr>,
    aggs: Seq<Agg>, g: QuerySpec)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(g, proj_all(rows, cols)))),
        keys_agree_at(db, ctx, rows, cols, keys, g),
        args_agree_at(db, ctx, rows, cols, aggs, g),
        aggs_match(aggs, g),
        keys_exact(g, proj_all(rows, cols)),
        group_caps(g, proj_all(rows, cols)),
    ensures ({
        let xs = proj_all(rows, cols);
        eval_query(db, ctx, Query::GroupBy { keys, aggs, input: Box::new(input) })
            == Ok::<Relation, SqlError>(gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k)))
    }),
{
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_rows);
    let xs = proj_all(rows, cols);
    let kept = keep_true(rows, qual_truths(g, xs));
    let q = qrows(g, xs);
    lemma_kept_rows(g, rows, cols);
    lemma_prepared_at(db, ctx, rows, kept, cols, keys, aggs, g);
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), arg_vals(g, proj(kept[i], cols))));
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= qkeys(g, xs));
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= q.map_values(|x: Row| arg_vals(g, x)));
    lemma_groups(g, aggs, xs);
    lemma_groupby_unfold_at(db, ctx, input, keys, aggs, kept, prep);
}

} // verus!
