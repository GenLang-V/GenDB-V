//! The SQL meaning of the statement's operators over the normal form of `nf`:
//! - GROUP BY (under any context) over the joined rows kept by `fq`: one row `key ++ [SUM]` per group key in
//!   first-occurrence order (`gkeys`), when every group's exact sum fits `i128` (`sum_caps`; the toolkit's
//!   `group_caps` asks for the absolute mass, which this query does not need for a value);
//! - the HAVING subquery: the per-cik sums, their AVG (`num_div` of the exact total by the number of ciks);
//! - the HAVING filter over the outer groups.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::equality::*;
use crate::spec::fns::div::*;
use crate::spec::aggs::avg::*;
use crate::link::query::*;
use crate::link::join::{keep, lemma_keep_members};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::bridge::equality::same_exact_type;
use crate::link::expr::i128_max;
use crate::agent::ast::*;
use crate::agent::nf::*;
use crate::agent::common::sums::*;

verus! {

/// Every group of `g` has an exact sum that fits `i128`.
pub open spec fn sum_caps(g: QuerySpec, xs: Seq<Row>) -> bool {
    forall|k: Row| #[trigger] gkeys(g, xs).contains(k) ==> -i128_max() <= gsum(g, xs, k, 0) <= i128_max()
}

/// The toolkit's filter of qualifying rows is `keep` of the qualification.
pub proof fn lemma_qrows_keep(g: QuerySpec, xs: Seq<Row>)
    ensures qrows(g, xs) == keep(xs, g.qual),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_qrows_keep(g, xs.drop_last());
    }
}

/// One group's aggregate row: a single numeric SUM at scale 4 whose exact sum fits `i128`.
pub proof fn lemma_agg_row_sum(g: QuerySpec, aggs: Seq<Agg>, xs: Seq<Row>, k: Row)
    requires
        aggs_match(aggs, g),
        g.aggs == seq![AggKind::Sum { scale: 4 }],
        -i128_max() <= gsum(g, xs, k, 0) <= i128_max(),
    ensures agg_row(aggs, members(g, xs, k)) == Ok::<Row, SqlError>(agg_outs(g, xs, k)),
{
    let m = members(g, xs, k);
    let rs = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(m, j)));
    let outs = agg_outs(g, xs, k);
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(outs[j]) by {
        assert(j == 0);
        lemma_members_col(g, xs, k, 0);
        assert(agg_matches(aggs[0], g.aggs[0]));
        lemma_num_in_range_small(gsum(g, xs, k, 0), 4);
    }
    lemma_collect_all(rs, outs);
}

/// GROUP BY over the qualifying rows' (key, arguments): the full row of every group (sum caps).
pub proof fn lemma_groups_sum(g: QuerySpec, aggs: Seq<Agg>, xs: Seq<Row>)
    requires
        aggs_match(aggs, g),
        g.aggs == seq![AggKind::Sum { scale: 4 }],
        keys_exact(g, xs),
        sum_caps(g, xs),
    ensures
        group_rows(aggs, qkeys(g, xs), qrows(g, xs).map_values(|x: Row| arg_vals(g, x)))
            == Ok::<Seq<Row>, SqlError>(gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k))),
{
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
        assert(ds.contains(k));
        lemma_agg_row_sum(g, aggs, xs, k);
    }
    lemma_collect_all(grs, full);
}

/// One step of the GROUP BY denotation under context `ctx`.
proof fn lemma_groupby_unfold_ctx(db: Database, ctx: Row, input: Query, keys: Seq<Expr>, aggs: Seq<Agg>, kept: Seq<Row>,
    prep: Seq<(Row, Row)>)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(kept),
        collect(Seq::new(kept.len(), |i: int|
            match eval_exprs(db, ctx + kept[i], keys) {
                Err(err) => Err(err),
                Ok(k) => match agg_args(db, ctx + kept[i], aggs) {
                    Err(err) => Err(err),
                    Ok(a) => Ok((k, a)),
                },
            })) == Ok::<Seq<(Row, Row)>, SqlError>(prep),
    ensures
        eval_query(db, ctx, Query::GroupBy { keys, aggs, input: Box::new(input) })
            == group_rows(aggs, prep.map_values(|p: (Row, Row)| p.0), prep.map_values(|p: (Row, Row)| p.1)),
{
    lemma_collect_pointwise::<(Row, Row)>();
}

/// GROUP BY under context `ctx` over an input that evaluates to the rows of `xs` kept by `g.qual`, when keys and
/// arguments evaluate on every qualifying row to the normal form's.
pub proof fn lemma_groupby_ctx(db: Database, ctx: Row, input: Query, keys: Seq<Expr>, aggs: Seq<Agg>, g: QuerySpec,
    xs: Seq<Row>)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(keep(xs, g.qual)),
        forall|i: int| 0 <= i < xs.len() && (g.qual)(#[trigger] xs[i]) ==>
            eval_exprs(db, ctx + xs[i], keys) == Ok::<Row, SqlError>((g.key)(xs[i])),
        forall|i: int| 0 <= i < xs.len() && (g.qual)(#[trigger] xs[i]) ==>
            agg_args(db, ctx + xs[i], aggs) == Ok::<Row, SqlError>(arg_vals(g, xs[i])),
        aggs_match(aggs, g),
        g.aggs == seq![AggKind::Sum { scale: 4 }],
        keys_exact(g, xs),
        sum_caps(g, xs),
    ensures
        eval_query(db, ctx, Query::GroupBy { keys, aggs, input: Box::new(input) })
            == Ok::<Relation, SqlError>(gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k))),
{
    hide(eval_exprs);
    hide(agg_args);
    hide(group_rows);
    let kept = keep(xs, g.qual);
    lemma_qrows_keep(g, xs);
    lemma_keep_members(xs, g.qual);
    let pre = Seq::new(kept.len(), |i: int|
        match eval_exprs(db, ctx + kept[i], keys) {
            Err(err) => Err(err),
            Ok(k) => match agg_args(db, ctx + kept[i], aggs) {
                Err(err) => Err(err),
                Ok(a) => Ok((k, a)),
            },
        });
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(kept[i]), arg_vals(g, kept[i])));
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] pre[i] == Ok::<(Row, Row), SqlError>(prep[i]) by {
        assert(xs.contains(kept[i]) && (g.qual)(kept[i]));
        let m = choose|m: int| 0 <= m < xs.len() && xs[m] == kept[i];
        assert((g.qual)(xs[m]));
    }
    lemma_collect_all(pre, prep);
    lemma_groupby_unfold_ctx(db, ctx, input, keys, aggs, kept, prep);
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= qkeys(g, xs));
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= qrows(g, xs).map_values(|x: Row| arg_vals(g, x)));
    lemma_groups_sum(g, aggs, xs);
}

// ------------------------------------------------------------------------------------------------ the two GROUP BYs

/// Column references and the SUM argument on a qualifying joined row, under a context of length `c`.
proof fn lemma_row_args(db: Database, ctx: Row, x: Row)
    requires joined_row_ok(x),
    ensures
        agg_args(db, ctx + x, seq![agg_sum(ctx.len())]) == Ok::<Row, SqlError>(seq![Val::Num { coeff: coeff(x[7]), scale: 4 }]),
{
    let (n, s) = choose|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) && x == n + s;
    lemma_concat_at(n, s);
    let env = ctx + x;
    assert(env[ctx.len() as int + 7] == x[7]);
    assert(eval_expr(db, env, Expr::Col(ctx.len() + 7)) == Ok::<Val, SqlError>(x[7]));
    assert(agg_arg(db, env, agg_sum(ctx.len())) == Ok::<Val, SqlError>(x[7]));
    let rs = agg_arg_results(db, env, seq![agg_sum(ctx.len())]);
    lemma_agg_arg_results_index(db, env, seq![agg_sum(ctx.len())]);
    lemma_collect_all(rs, seq![x[7]]);
    assert(x[7] == Val::Num { coeff: coeff(x[7]), scale: 4 });
}

/// Keys of the joined rows are exact (text and integer values, never NULL).
pub proof fn lemma_keys_exact(db: Database, g: QuerySpec, ks: spec_fn(Row) -> Row, both: bool)
    requires
        rows_ok(db),
        forall|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) ==> #[trigger] (g.key)(n + s) == ks(s),
        both ==> forall|s: Row| #[trigger] ks(s) == seq![s[2], s[1]],
        !both ==> forall|s: Row| #[trigger] ks(s) == seq![s[1]],
    ensures keys_exact(g, joined(db)),
{
    let xs = joined(db);
    lemma_joined_rows_ok(db);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        let (na, sa) = choose|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) && xs[a] == n + s;
        let (nb, sb) = choose|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) && xs[b] == n + s;
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert(ka == ks(sa) && kb == ks(sb));
        assert forall|i: int| 0 <= i < ka.len() implies same_exact_type(#[trigger] ka[i], kb[i]) by {}
        lemma_row_exact(ka, kb);
    }
}

/// Keys and arguments of the outer GROUP BY on one joined row.
pub proof fn lemma_top_row(db: Database, p0: Seq<u8>, p1: int, x: Row)
    requires joined_row_ok(x),
    ensures
        eval_exprs(db, Seq::<Val>::empty() + x, keys_top()) == Ok::<Row, SqlError>((g_top(p0, p1).key)(x)),
        agg_args(db, Seq::<Val>::empty() + x, seq![agg_sum(0)]) == Ok::<Row, SqlError>(arg_vals(g_top(p0, p1), x)),
{
    hide(eval_exprs);
    hide(agg_args);
    let g = g_top(p0, p1);
    let ctx = Seq::<Val>::empty();
    let env = ctx + x;
    assert(env =~= x);
    assert(x.len() == 29) by {
        let (n, s) = choose|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) && x == n + s;
    }
    assert(keys_top() =~= col_exprs(seq![11nat, 10]));
    lemma_eval_cols(db, env, seq![11nat, 10]);
    assert(select(env, seq![11nat, 10]) =~= (g.key)(x));
    lemma_row_args(db, ctx, x);
    assert(arg_vals(g, x) =~= seq![Val::Num { coeff: coeff(x[7]), scale: 4 }]);
}

/// Keys and arguments of the subquery's GROUP BY on one joined row, under a context of 3 values.
pub proof fn lemma_cik_row(db: Database, p0: Seq<u8>, p1: int, ctx: Row, x: Row)
    requires joined_row_ok(x), ctx.len() == 3,
    ensures
        eval_exprs(db, ctx + x, keys_cik()) == Ok::<Row, SqlError>((g_cik(p0, p1).key)(x)),
        agg_args(db, ctx + x, seq![agg_sum(3)]) == Ok::<Row, SqlError>(arg_vals(g_cik(p0, p1), x)),
{
    let g = g_cik(p0, p1);
    let (n, s) = choose|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) && x == n + s;
    lemma_concat_at(n, s);
    assert(keys_cik() =~= col_exprs(seq![13nat]));
    lemma_eval_cols(db, ctx + x, seq![13nat]);
    assert((ctx + x)[13] == x[10]);
    assert(select(ctx + x, seq![13nat]) =~= (g.key)(x));
    lemma_row_args(db, ctx, x);
    assert(arg_vals(g, x) =~= seq![Val::Num { coeff: coeff(x[7]), scale: 4 }]);
}

/// The outer GROUP BY at the empty context.
pub proof fn lemma_eval_group_top(db: Database, p0: Seq<u8>, p1: int)
    requires rows_ok(db), int_in_range(IntKind::Int4, p1), sum_caps(g_top(p0, p1), joined(db)),
    ensures ({
        let g = g_top(p0, p1);
        let xs = joined(db);
        eval_query(db, Seq::empty(), q_group_top(lits(p0, p1)))
            == Ok::<Relation, SqlError>(gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k)))
    }),
{
    hide(eval_query);
    hide(eval_exprs);
    hide(agg_args);
    let g = g_top(p0, p1);
    let xs = joined(db);
    let ctx = Seq::<Val>::empty();
    lemma_eval_where(db, p0, p1, ctx);
    lemma_joined_rows_ok(db);
    lemma_top_key(p0, p1);
    assert forall|i: int| 0 <= i < xs.len() && (g.qual)(#[trigger] xs[i]) implies
        eval_exprs(db, ctx + xs[i], keys_top()) == Ok::<Row, SqlError>((g.key)(xs[i])) by {
        lemma_top_row(db, p0, p1, xs[i]);
    }
    assert forall|i: int| 0 <= i < xs.len() && (g.qual)(#[trigger] xs[i]) implies
        agg_args(db, ctx + xs[i], seq![agg_sum(0)]) == Ok::<Row, SqlError>(arg_vals(g, xs[i])) by {
        lemma_top_row(db, p0, p1, xs[i]);
    }
    assert(aggs_match(seq![agg_sum(0)], g));
    assert forall|s: Row| #[trigger] key_top_s(s) == seq![s[2], s[1]] by {}
    lemma_keys_exact(db, g, |s: Row| key_top_s(s), true);
    lemma_groupby_ctx(db, ctx, q_where(lits(p0, p1), 0), keys_top(), seq![agg_sum(0)], g, xs);
}

/// The subquery's GROUP BY under a context of 3 values.
pub proof fn lemma_eval_group_cik(db: Database, p0: Seq<u8>, p1: int, ctx: Row)
    requires rows_ok(db), int_in_range(IntKind::Int4, p1), sum_caps(g_cik(p0, p1), joined(db)), ctx.len() == 3,
    ensures ({
        let g = g_cik(p0, p1);
        let xs = joined(db);
        eval_query(db, ctx, q_group_cik(lits(p0, p1)))
            == Ok::<Relation, SqlError>(gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k)))
    }),
{
    hide(eval_query);
    hide(eval_exprs);
    hide(agg_args);
    let g = g_cik(p0, p1);
    let xs = joined(db);
    lemma_eval_where(db, p0, p1, ctx);
    lemma_joined_rows_ok(db);
    lemma_cik_key(p0, p1);
    assert forall|i: int| 0 <= i < xs.len() && (g.qual)(#[trigger] xs[i]) implies
        eval_exprs(db, ctx + xs[i], keys_cik()) == Ok::<Row, SqlError>((g.key)(xs[i])) by {
        lemma_cik_row(db, p0, p1, ctx, xs[i]);
    }
    assert forall|i: int| 0 <= i < xs.len() && (g.qual)(#[trigger] xs[i]) implies
        agg_args(db, ctx + xs[i], seq![agg_sum(3)]) == Ok::<Row, SqlError>(arg_vals(g, xs[i])) by {
        lemma_cik_row(db, p0, p1, ctx, xs[i]);
    }
    assert(aggs_match(seq![agg_sum(3)], g));
    assert forall|s: Row| #[trigger] key_cik_s(s) == seq![s[1]] by {}
    lemma_keys_exact(db, g, |s: Row| key_cik_s(s), false);
    lemma_groupby_ctx(db, ctx, q_where(lits(p0, p1), 3), keys_cik(), seq![agg_sum(3)], g, xs);
}

// ------------------------------------------------------------------------------------------------ the AVG subquery

/// A numeric at scale 4 per key.
pub open spec fn num4(f: spec_fn(Row) -> int) -> spec_fn(Row) -> Val {
    |k: Row| Val::Num { coeff: f(k), scale: 4 }
}

/// The exact sum of the subquery's group `k`.
pub open spec fn cik_sum_fn(p0: Seq<u8>, p1: int, xs: Seq<Row>) -> spec_fn(Row) -> int {
    |k: Row| gsum(g_cik(p0, p1), xs, k, 0)
}

/// The per-cik sums as numeric values.
pub open spec fn cik_sums(p0: Seq<u8>, p1: int, xs: Seq<Row>) -> Seq<Val> {
    gkeys(g_cik(p0, p1), xs).map_values(num4(cik_sum_fn(p0, p1, xs)))
}

/// The exact total of the per-cik sums.
pub open spec fn cik_total(p0: Seq<u8>, p1: int, xs: Seq<Row>) -> int {
    ssum(gkeys(g_cik(p0, p1), xs), cik_sum_fn(p0, p1, xs))
}

/// `num_sum` of numerics at scale 4.
pub proof fn lemma_num_sum_scale4(keys: Seq<Row>, f: spec_fn(Row) -> int)
    ensures ({
        let vs = keys.map_values(num4(f));
        &&& all_of_kind(NumKind::Numeric, vs)
        &&& count_non_null(vs) == keys.len()
        &&& keys.len() > 0 ==> num_sum(vs) == (ssum(keys, f), 4nat)
        &&& keys.len() == 0 ==> num_sum(vs) == (0int, 0nat)
    }),
    decreases keys.len(),
{
    let vs = keys.map_values(num4(f));
    if keys.len() > 0 {
        let ki = keys.drop_last();
        lemma_num_sum_scale4(ki, f);
        let vsi = ki.map_values(num4(f));
        assert(vs.drop_last() =~= vsi);
        assert(pow10(0) == 1);
        let acc = num_sum(vsi);
        if ki.len() == 0 {
            assert(align(acc.0, acc.1, 4) == 0) by (nonlinear_arith)
                requires acc.0 == 0, align(acc.0, acc.1, 4) == acc.0 * pow10((4 - acc.1) as nat);
        } else {
            assert(align(acc.0, 4, 4) == acc.0) by {
                assert((4 - 4) as nat == 0nat);
            }
        }
        assert(align(f(keys.last()), 4, 4) == f(keys.last())) by {
            assert((4 - 4) as nat == 0nat);
        }
    } else {
        assert(vs =~= Seq::<Val>::empty());
    }
}

/// The per-cik sums as one-column rows.
pub open spec fn cik_rows(p0: Seq<u8>, p1: int, xs: Seq<Row>) -> Seq<Row> {
    cik_sums(p0, p1, xs).map_values(|v: Val| seq![v])
}

/// Every group key of the subquery is a one-value row (a cik).
pub proof fn lemma_cik_key_len(db: Database, p0: Seq<u8>, p1: int, k: Row)
    requires rows_ok(db), gkeys(g_cik(p0, p1), joined(db)).contains(k),
    ensures k.len() == 1,
{
    let g = g_cik(p0, p1);
    let xs = joined(db);
    lemma_gkeys_witness(g, xs, k);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
    lemma_joined_rows_ok(db);
    lemma_cik_key(p0, p1);
    assert(joined_row_ok(xs[m]));
    let (n, s) = choose|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) && xs[m] == n + s;
    assert((g.key)(xs[m]) == key_cik_s(s));
}

/// One step of the Project denotation under context `ctx`.
proof fn lemma_project_unfold_ctx(db: Database, ctx: Row, input: Query, exprs: Seq<Expr>, rows: Seq<Row>, out: Seq<Row>)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(rows),
        collect(Seq::new(rows.len(), |i: int| eval_exprs(db, ctx + rows[i], exprs))) == Ok::<Seq<Row>, SqlError>(out),
    ensures eval_query(db, ctx, Query::Project { exprs, input: Box::new(input) }) == Ok::<Relation, SqlError>(out),
{
    lemma_collect_pointwise::<Row>();
}

/// `SELECT sub_total` on one subquery group row.
proof fn lemma_project_row(db: Database, p0: Seq<u8>, p1: int, ctx: Row, i: int)
    requires rows_ok(db), ctx.len() == 3, 0 <= i < gkeys(g_cik(p0, p1), joined(db)).len(),
    ensures ({
        let g = g_cik(p0, p1);
        let xs = joined(db);
        let k = gkeys(g, xs)[i];
        eval_exprs(db, ctx + full_row(g, xs, k), seq![Expr::Col(4)]) == Ok::<Row, SqlError>(cik_rows(p0, p1, xs)[i])
    }),
{
    hide(eval_exprs);
    let g = g_cik(p0, p1);
    let xs = joined(db);
    let ks = gkeys(g, xs);
    let k = ks[i];
    assert(ks.contains(k));
    lemma_cik_key_len(db, p0, p1, k);
    let fr = full_row(g, xs, k);
    lemma_gkeys(g, xs);
    assert(gcount(g, xs, k) > 0);
    assert(agg_outs(g, xs, k)[0] == Val::Num { coeff: gsum(g, xs, k, 0), scale: 4 });
    assert((ctx + fr)[4] == Val::Num { coeff: gsum(g, xs, k, 0), scale: 4 });
    assert(seq![Expr::Col(4)] =~= col_exprs(seq![4nat]));
    lemma_eval_cols(db, ctx + fr, seq![4nat]);
    assert(cik_rows(p0, p1, xs)[i] == seq![cik_sums(p0, p1, xs)[i]]);
    assert(select(ctx + fr, seq![4nat]) =~= cik_rows(p0, p1, xs)[i]);
}

/// `SELECT sub_total` over the per-cik groups.
pub proof fn lemma_eval_project(db: Database, p0: Seq<u8>, p1: int, ctx: Row)
    requires rows_ok(db), int_in_range(IntKind::Int4, p1), sum_caps(g_cik(p0, p1), joined(db)), ctx.len() == 3,
    ensures eval_query(db, ctx, q_project(lits(p0, p1))) == Ok::<Relation, SqlError>(cik_rows(p0, p1, joined(db))),
{
    hide(eval_query);
    hide(eval_exprs);
    let g = g_cik(p0, p1);
    let xs = joined(db);
    let ks = gkeys(g, xs);
    let grows = ks.map_values(|k: Row| full_row(g, xs, k));
    lemma_eval_group_cik(db, p0, p1, ctx);
    let prows = cik_rows(p0, p1, xs);
    let prs = Seq::new(grows.len(), |i: int| eval_exprs(db, ctx + grows[i], seq![Expr::Col(4)]));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Row, SqlError>(prows[i]) by {
        lemma_project_row(db, p0, p1, ctx, i);
    }
    lemma_collect_all(prs, prows);
    lemma_project_unfold_ctx(db, ctx, q_group_cik(lits(p0, p1)), seq![Expr::Col(4)], grows, prows);
}

/// The AVG aggregate's argument on one per-cik row.
pub proof fn lemma_avg_arg_row(db: Database, ctx: Row, prow: Row)
    requires ctx.len() == 3, prow.len() == 1,
    ensures agg_args(db, ctx + prow, seq![agg_avg()]) == Ok::<Row, SqlError>(prow),
{
    let env = ctx + prow;
    assert(env[3] == prow[0]);
    assert(eval_expr(db, env, Expr::Col(3)) == Ok::<Val, SqlError>(prow[0]));
    assert(agg_arg(db, env, agg_avg()) == Ok::<Val, SqlError>(prow[0]));
    let rs = agg_arg_results(db, env, seq![agg_avg()]);
    lemma_agg_arg_results_index(db, env, seq![agg_avg()]);
    lemma_collect_all(rs, seq![prow[0]]);
    assert(seq![prow[0]] =~= prow);
}

/// The AVG aggregate's argument rows are the per-cik rows.
pub proof fn lemma_avg_args(db: Database, ctx: Row, prows: Seq<Row>)
    requires ctx.len() == 3, forall|i: int| 0 <= i < prows.len() ==> (#[trigger] prows[i]).len() == 1,
    ensures
        collect(Seq::new(prows.len(), |i: int| agg_args(db, ctx + prows[i], seq![agg_avg()]))) == Ok::<Seq<Row>, SqlError>(prows),
        forall|i: int| 0 <= i < prows.len() ==> #[trigger] agg_args(db, ctx + prows[i], seq![agg_avg()]) == Ok::<Row, SqlError>(prows[i]),
{
    hide(agg_args);
    let ars = Seq::new(prows.len(), |i: int| agg_args(db, ctx + prows[i], seq![agg_avg()]));
    assert forall|i: int| 0 <= i < prows.len() implies #[trigger] agg_args(db, ctx + prows[i], seq![agg_avg()]) == Ok::<Row, SqlError>(prows[i]) by {
        lemma_avg_arg_row(db, ctx, prows[i]);
    }
    assert forall|i: int| 0 <= i < ars.len() implies #[trigger] ars[i] == Ok::<Row, SqlError>(prows[i]) by {
        lemma_avg_arg_row(db, ctx, prows[i]);
    }
    lemma_collect_all(ars, prows);
}

/// The AVG value of the per-cik sums.
proof fn lemma_avg_value(p0: Seq<u8>, p1: int, xs: Seq<Row>)
    requires
        -i128_max() <= cik_total(p0, p1, xs) <= i128_max(),
        gkeys(g_cik(p0, p1), xs).len() > 0,
        num_div_fits(cik_total(p0, p1, xs), 4, gkeys(g_cik(p0, p1), xs).len() as int, 0),
    ensures
        agg_row(seq![agg_avg()], cik_rows(p0, p1, xs))
            == Ok::<Row, SqlError>(seq![avg_of(cik_total(p0, p1, xs), 4, gkeys(g_cik(p0, p1), xs).len())]),
{
    let g = g_cik(p0, p1);
    let ks = gkeys(g, xs);
    let prows = cik_rows(p0, p1, xs);
    let vs = column(prows, 0);
    assert(vs =~= cik_sums(p0, p1, xs));
    lemma_num_sum_scale4(ks, cik_sum_fn(p0, p1, xs));
    let t = cik_total(p0, p1, xs);
    let c = ks.len() as int;
    lemma_num_in_range_small(t, 4);
    lemma_avg_ok(t, 4, c);
    assert(avg_value(NumKind::Numeric, vs) == Ok::<Val, SqlError>(avg_of(t, 4, c as nat)));
    let avs = Seq::new(1, |j: int| agg_value(seq![agg_avg()][j], column(prows, j)));
    lemma_collect_all(avs, seq![avg_of(t, 4, c as nat)]);
}

/// One step of the Aggregate denotation under context `ctx`.
proof fn lemma_aggregate_unfold_ctx(db: Database, ctx: Row, input: Query, aggs: Seq<Agg>, kept: Seq<Row>, args: Seq<Row>)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(kept),
        collect(Seq::new(kept.len(), |i: int| agg_args(db, ctx + kept[i], aggs))) == Ok::<Seq<Row>, SqlError>(args),
    ensures
        eval_query(db, ctx, Query::Aggregate { aggs, input: Box::new(input) })
            == match agg_row(aggs, args) {
                Err(err) => Err(err),
                Ok(row) => Ok::<Relation, SqlError>(seq![row]),
            },
{
    lemma_collect_pointwise::<Row>();
}

/// The subquery under a context of 3 values: one row holding AVG of the per-cik sums, the exact division of their
/// total by their number, when every per-cik sum fits `i128` and the division is inside its domain.
pub proof fn lemma_eval_avg(db: Database, p0: Seq<u8>, p1: int, ctx: Row)
    requires
        rows_ok(db), int_in_range(IntKind::Int4, p1), sum_caps(g_cik(p0, p1), joined(db)), ctx.len() == 3,
        -i128_max() <= cik_total(p0, p1, joined(db)) <= i128_max(),
        gkeys(g_cik(p0, p1), joined(db)).len() > 0,
        num_div_fits(cik_total(p0, p1, joined(db)), 4, gkeys(g_cik(p0, p1), joined(db)).len() as int, 0),
    ensures
        eval_query(db, ctx, q_avg(lits(p0, p1))) == Ok::<Relation, SqlError>(seq![seq![
            avg_of(cik_total(p0, p1, joined(db)), 4, gkeys(g_cik(p0, p1), joined(db)).len())]]),
{
    let xs = joined(db);
    let prows = cik_rows(p0, p1, xs);
    lemma_eval_project(db, p0, p1, ctx);
    assert forall|i: int| 0 <= i < prows.len() implies (#[trigger] prows[i]).len() == 1 by {}
    lemma_avg_args(db, ctx, prows);
    lemma_avg_value(p0, p1, xs);
    lemma_aggregate_unfold_ctx(db, ctx, q_project(lits(p0, p1)), seq![agg_avg()], prows, prows);
}

// ------------------------------------------------------------------------------------------------ HAVING

/// `HAVING sum > avg` on an outer group row, given the subquery's value.
pub proof fn lemma_having_row(db: Database, p0: Seq<u8>, p1: int, r: Row, avg_c: int, avg_s: nat)
    requires
        r.len() == 3, r[2] is Num, r[2]->Num_scale == 4,
        eval_query(db, r, q_avg(lits(p0, p1))) == Ok::<Relation, SqlError>(seq![seq![Val::Num { coeff: avg_c, scale: avg_s }]]),
    ensures
        eval_pred(db, Seq::<Val>::empty() + r, pred_having(lits(p0, p1)))
            == Ok::<Truth, SqlError>(truth_of(num_cmp(coeff(r[2]), 4, avg_c, avg_s) > 0)),
{
    let env = Seq::<Val>::empty() + r;
    assert(env =~= r);
    assert(eval_expr(db, env, Expr::Col(2)) == Ok::<Val, SqlError>(r[2]));
    assert(eval_expr(db, env, Expr::Subquery(Box::new(q_avg(lits(p0, p1)))))
        == Ok::<Val, SqlError>(Val::Num { coeff: avg_c, scale: avg_s }));
}

} // verus!
