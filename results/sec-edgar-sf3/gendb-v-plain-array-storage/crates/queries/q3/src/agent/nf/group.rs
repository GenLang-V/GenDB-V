//! GROUP BY with one `SUM` of a scale-4 numeric column, at any outer context (`link::query`'s grouped link stated
//! for an arbitrary context `ctx` and without a column projection): over an input that evaluates to the qualifying
//! rows of `rows`, the GROUP BY is the full row `key ++ [SUM]` of every group key in first-occurrence order
//! (`gkeys`). In place of `link::query::group_caps` it needs only that every group sum is inside PostgreSQL's
//! numeric format (true for every sum of `i128`-bounded values over a machine-sized relation).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::equality::*;
use crate::exec::relational::domain::{group_input_results, group_results, lemma_eval_group_by};
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::equality::same_exact_type;
use crate::link::join::{keep, lemma_keep_members};
use crate::link::query::{QuerySpec, AggKind, hit, gcount, gsum, gkeys, full_row, agg_outs, agg_out, members, arg_vals,
    qrows, qkeys, key_pool, keys_exact, lemma_pool_exact, lemma_distinct_gkeys, lemma_gkeys, lemma_group_members,
    lemma_members_col, lemma_row_exact, col_exprs, lemma_eval_cols, select};

verus! {

/// The coefficient of a numeric value (0 for any other value).
pub open spec fn coeff(v: Val) -> int {
    match v {
        Val::Num { coeff, scale } => coeff,
        _ => 0,
    }
}

/// The normal form of a GROUP BY `key` with `SUM` of column 7 (scale 4) over the rows satisfying `qual`.
pub open spec fn sum_spec(qual: spec_fn(Row) -> bool, key: spec_fn(Row) -> Row) -> QuerySpec {
    QuerySpec {
        qual,
        key,
        arg: |j: int, x: Row| coeff(x[7]),
        aggs: seq![AggKind::Sum { scale: 4 }],
        outs: Seq::empty(),
        grouped: true,
    }
}

/// `SUM` over a numeric argument.
pub open spec fn one_sum(aggs: Seq<Agg>) -> bool {
    aggs.len() == 1 && aggs[0] is Sum && aggs[0]->Sum_kind == NumKind::Numeric
}

/// The group sums are inside the numeric format.
pub open spec fn sums_in_range(g: QuerySpec, rows: Seq<Row>) -> bool {
    forall|k: Row| #[trigger] num_in_range(gsum(g, rows, k, 0), 4)
}

/// `qrows` (the normal form's qualifying rows) is `keep` of the condition.
pub proof fn lemma_qrows_keep(g: QuerySpec, xs: Seq<Row>)
    ensures qrows(g, xs) == keep(xs, g.qual),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_qrows_keep(g, xs.drop_last());
    }
}

/// The aggregate row of one group.
pub proof fn lemma_agg_row_sum(qual: spec_fn(Row) -> bool, key: spec_fn(Row) -> Row, aggs: Seq<Agg>, xs: Seq<Row>, k: Row)
    requires one_sum(aggs), num_in_range(gsum(sum_spec(qual, key), xs, k, 0), 4),
    ensures ({
        let g = sum_spec(qual, key);
        agg_row(aggs, members(g, xs, k)) == Ok::<Row, SqlError>(agg_outs(g, xs, k))
    }),
{
    let g = sum_spec(qual, key);
    let m = members(g, xs, k);
    let rs = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(m, j)));
    let outs = agg_outs(g, xs, k);
    lemma_members_col(g, xs, k, 0);
    let vs = column(m, 0);
    assert(rs[0] == agg_value(aggs[0], vs));
    assert(outs[0] == agg_out(AggKind::Sum { scale: 4 }, gcount(g, xs, k), gsum(g, xs, k, 0)));
    assert(rs[0] == Ok::<Val, SqlError>(outs[0]));
    lemma_collect_all(rs, outs);
}

/// GROUP BY over the qualifying rows' (key, argument): the full row of every group, first-occurrence order
/// (`link::query::lemma_groups` without `group_caps`).
pub proof fn lemma_groups_sum(qual: spec_fn(Row) -> bool, key: spec_fn(Row) -> Row, aggs: Seq<Agg>, xs: Seq<Row>)
    requires
        one_sum(aggs),
        keys_exact(sum_spec(qual, key), xs),
        sums_in_range(sum_spec(qual, key), xs),
    ensures ({
        let g = sum_spec(qual, key);
        group_rows(aggs, qkeys(g, xs), qrows(g, xs).map_values(|x: Row| arg_vals(g, x)))
            == Ok::<Seq<Row>, SqlError>(gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k)))
    }),
{
    let g = sum_spec(qual, key);
    let ks = qkeys(g, xs);
    let avs = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    let ds = gkeys(g, xs);
    lemma_gkeys(g, xs);
    let grs = Seq::new(ds.len(), |gi: int|
        match agg_row(aggs, group_members(ks, avs, ds[gi])) {
            Ok(a) => Ok(ds[gi] + a),
            Err(e) => Err(e),
        });
    let full = ds.map_values(|k: Row| full_row(g, xs, k));
    assert forall|gi: int| 0 <= gi < grs.len() implies #[trigger] grs[gi] == Ok::<Row, SqlError>(full[gi]) by {
        let k = ds[gi];
        assert(pool.contains(k));
        lemma_group_members(g, xs, k, pool);
        lemma_agg_row_sum(qual, key, aggs, xs, k);
    }
    lemma_collect_all(grs, full);
}

/// Every qualifying row's key and SUM argument evaluate in the environment `ctx ++ row`.
pub open spec fn rows_agree(db: Database, ctx: Row, keys: Seq<Expr>, aggs: Seq<Agg>, g: QuerySpec, rows: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < rows.len() && (g.qual)(#[trigger] rows[i]) ==> {
        &&& eval_exprs(db, ctx + rows[i], keys) == Ok::<Row, SqlError>((g.key)(rows[i]))
        &&& agg_args(db, ctx + rows[i], aggs) == Ok::<Row, SqlError>(arg_vals(g, rows[i]))
    }
}

/// The prepared (key, argument) sequence of the GROUP BY over the qualifying rows.
pub proof fn lemma_group_prepared_ctx(db: Database, ctx: Row, keys: Seq<Expr>, aggs: Seq<Agg>, g: QuerySpec, rows: Seq<Row>)
    requires rows_agree(db, ctx, keys, aggs, g, rows),
    ensures ({
        let kept = keep(rows, g.qual);
        let prep = Seq::new(kept.len(), |i: int| ((g.key)(kept[i]), arg_vals(g, kept[i])));
        &&& collect(group_input_results(db, ctx, kept, keys, aggs)) == Ok::<Seq<(Row, Row)>, SqlError>(prep)
        &&& prep.map_values(|p: (Row, Row)| p.0) == qkeys(g, rows)
        &&& prep.map_values(|p: (Row, Row)| p.1) == qrows(g, rows).map_values(|x: Row| arg_vals(g, x))
    }),
{
    hide(eval_exprs);
    hide(agg_args);
    let kept = keep(rows, g.qual);
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(kept[i]), arg_vals(g, kept[i])));
    let rs = group_input_results(db, ctx, kept, keys, aggs);
    lemma_keep_members(rows, g.qual);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<(Row, Row), SqlError>(prep[i]) by {
        assert(rows.contains(kept[i]) && (g.qual)(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert((g.qual)(rows[m]));
    }
    lemma_collect_all(rs, prep);
    lemma_qrows_keep(g, rows);
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= qkeys(g, rows));
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= qrows(g, rows).map_values(|x: Row| arg_vals(g, x)));
}

/// The grouped link at context `ctx`.
pub proof fn lemma_group_ctx(db: Database, ctx: Row, input: Query, keys: Seq<Expr>, aggs: Seq<Agg>, rows: Seq<Row>,
    qual: spec_fn(Row) -> bool, key: spec_fn(Row) -> Row)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(keep(rows, qual)),
        rows_agree(db, ctx, keys, aggs, sum_spec(qual, key), rows),
        one_sum(aggs),
        keys_exact(sum_spec(qual, key), rows),
        sums_in_range(sum_spec(qual, key), rows),
    ensures ({
        let g = sum_spec(qual, key);
        eval_query(db, ctx, Query::GroupBy { keys, aggs, input: Box::new(input) })
            == Ok::<Relation, SqlError>(gkeys(g, rows).map_values(|k: Row| full_row(g, rows, k)))
    }),
{
    let g = sum_spec(qual, key);
    lemma_eval_group_by(db, ctx, keys, aggs, Box::new(input));
    lemma_group_prepared_ctx(db, ctx, keys, aggs, g, rows);
    let kept = keep(rows, g.qual);
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(kept[i]), arg_vals(g, kept[i])));
    let ks = prep.map_values(|p: (Row, Row)| p.0);
    let avs = prep.map_values(|p: (Row, Row)| p.1);
    assert(collect(group_results(aggs, ks, avs)) == group_rows(aggs, ks, avs));
    lemma_groups_sum(qual, key, aggs, rows);
}

// ------------------------------------------------------------------------------------------- the two GROUP BYs

/// `SUM(<column c>)` over a scale-4 numeric column evaluates to the value.
pub proof fn lemma_sum_arg(db: Database, env: Row, c: nat)
    requires c < env.len(), env[c as int] is Num, env[c as int]->Num_scale == 4,
    ensures
        agg_args(db, env, seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(c) }])
            == Ok::<Row, SqlError>(seq![Val::Num { coeff: coeff(env[c as int]), scale: 4 }]),
{
    let aggs = seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(c) }];
    let rs = agg_arg_results(db, env, aggs);
    assert(rs[0] == agg_arg(db, env, aggs[0]));
    assert(rs[0] == Ok::<Val, SqlError>(env[c as int]));
    lemma_collect_all(rs, seq![env[c as int]]);
    assert(seq![env[c as int]] =~= seq![Val::Num { coeff: coeff(env[c as int]), scale: 4 }]);
}

/// The argument row of a joined row under a `sum_spec`.
pub proof fn lemma_arg_vals(qual: spec_fn(Row) -> bool, key: spec_fn(Row) -> Row, x: Row)
    ensures arg_vals(sum_spec(qual, key), x) == seq![Val::Num { coeff: coeff(x[7]), scale: 4 }],
{
    assert(arg_vals(sum_spec(qual, key), x) =~= seq![Val::Num { coeff: coeff(x[7]), scale: 4 }]);
}

/// Key rows of two values of exact types: SQL "not distinct" is equality.
pub proof fn lemma_keys_exact_from(g: QuerySpec, xs: Seq<Row>)
    requires
        forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) ==> {
            let (ka, kb) = ((g.key)(#[trigger] xs[a]), (g.key)(#[trigger] xs[b]));
            &&& ka.len() == kb.len()
            &&& forall|i: int| 0 <= i < ka.len() ==> same_exact_type(#[trigger] ka[i], kb[i])
        },
    ensures keys_exact(g, xs),
{
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        lemma_row_exact((g.key)(xs[a]), (g.key)(xs[b]));
    }
}

} // verus!
