//! When the body is outside the capacity domain: an outer group whose SUM leaves `i128` (its absolute mass does
//! too), or an AVG input outside AVG's domain (its absolute mass beyond `i128`, or the division beyond the
//! evaluator's intermediates) under the HAVING condition of the first group row.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::equality::distinct_rows;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::aggs::avg::*;
use crate::spec::fns::div::*;
use crate::bridge::collect::*;
use crate::exec::relational::domain::*;
use crate::exec::aggs::avg::fits_avg_value;
use crate::exec::domain::fits_expr;
use crate::link::query::{QuerySpec, AggKind, gsum, gcount, gkeys, qrows, qkeys, key_pool, members, arg_vals,
    lemma_gkeys, lemma_pool_exact, lemma_distinct_gkeys, lemma_group_members, lemma_members_col, lemma_qrows_sub};
use crate::link::capacity::*;
use crate::link::join::keep;
use crate::agent::nf::ast::*;
use crate::agent::nf::fromwhere::*;
use crate::agent::nf::group::*;
use crate::agent::nf::sums::*;
use crate::agent::nf::body::*;

verus! {

/// The kept rows' GROUP BY inputs are their keys and arguments.
proof fn lemma_outer_inputs(db: Database, ps: Seq<Literal>, p0: Seq<u8>, p1: int)
    requires binding(ps, p0, p1), tables_shaped(db), vals_ok(db),
    ensures ({
        let g = g_out(p0, p1);
        let rows = keep(joined(db), jq_fn(p0, p1));
        let ks = qkeys(g, joined(db));
        let args = qrows(g, joined(db)).map_values(|x: Row| arg_vals(g, x));
        &&& eval_query(db, Seq::empty(), where_q(0, ps)) == Ok::<Relation, SqlError>(rows)
        &&& ks.len() == rows.len() && args.len() == rows.len()
        &&& forall|i: int| 0 <= i < rows.len() ==> #[trigger] group_input(db, Seq::<Val>::empty() + rows[i], outer_keys(), outer_aggs())
            == Ok::<(Row, Row), SqlError>((ks[i], args[i]))
    }),
{
    let g = g_out(p0, p1);
    let xs = joined(db);
    let rows = keep(xs, jq_fn(p0, p1));
    lemma_where_rows(db, Seq::empty(), ps, p0, p1);
    lemma_qrows_keep(g, xs);
    lemma_qrows_sub(g, xs);
    lemma_agree_outer(db, p0, p1);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + rows[i], outer_keys(), outer_aggs())
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        let x = rows[i];
        assert(xs.contains(x) && (g.qual)(x));
        let m = choose|m: int| 0 <= m < xs.len() && xs[m] == x;
        assert((g.qual)(xs[m]));
        assert(ks[i] == (g.key)(x));
        assert(args[i] == arg_vals(g, x));
    }
}

/// An outer group whose SUM leaves `i128`: the body is outside the capacity domain.
pub proof fn lemma_cap_group(db: Database, ps: Seq<Literal>, p0: Seq<u8>, p1: int, k: Row)
    requires
        binding(ps, p0, p1), tables_shaped(db), vals_ok(db),
        gkeys(g_out(p0, p1), joined(db)).contains(k),
        abs(gsum(g_out(p0, p1), joined(db), k, 0)) > i128::MAX as int,
    ensures !fits_query(db, Seq::empty(), body_q(ps)),
{
    let g = g_out(p0, p1);
    let xs = joined(db);
    let rows = keep(xs, jq_fn(p0, p1));
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    lemma_outer_inputs(db, ps, p0, p1);
    lemma_keys_exact_joined(db, jq_fn(p0, p1), g.key);
    lemma_pool_exact(g, xs);
    let pool = key_pool(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {}
    lemma_distinct_gkeys(g, xs, pool);
    let ds = distinct_rows(ks);
    assert(ds == gkeys(g, xs));
    let gi = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k;
    let aggs = outer_aggs();
    assert(aggs[0] == Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(7) });
    // the group's values: numeric, summing to its SUM, so its mass is beyond `i128`
    lemma_group_members(g, xs, k, pool);
    lemma_members_col(g, xs, k, 0);
    lemma_gkeys(g, xs);
    let vs = column(group_members(ks, args, ds[gi]), 0);
    assert(gcount(g, xs, k) > 0);
    lemma_num_sum_bound(vs);
    assert(!fits_agg_value(aggs[0], vs));
    assert forall|h: int| 0 <= h < ds.len() implies #[trigger] aggs_ok_inside(aggs, group_members(ks, args, ds[h])) by {
        assert(pool.contains(ds[h]));
        lemma_group_members(g, xs, ds[h], pool);
        lemma_members_col(g, xs, ds[h], 0);
        let vh = column(group_members(ks, args, ds[h]), 0);
        assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(group_members(ks, args, ds[h]), j))
            implies agg_value(aggs[j], column(group_members(ks, args, ds[h]), j)) is Ok by {
            assert(j == 0);
            lemma_sum_inside_ok(NumKind::Numeric, Expr::Col(7), vh);
        }
    }
    lemma_group_by_capacity(db, Seq::empty(), outer_keys(), aggs, Box::new(where_q(0, ps)), rows, ks, args, gi, 0);
    lemma_first_input(db, Seq::empty(), body_q(ps));
}

/// An AVG input outside AVG's domain: the HAVING condition of every group row is outside its domain.
pub proof fn lemma_cap_avg(db: Database, ps: Seq<Literal>, p0: Seq<u8>, p1: int)
    requires
        binding(ps, p0, p1), tables_shaped(db), vals_ok(db),
        gb_rows(db, p0, p1).len() > 0,
        !fits_avg_value(NumKind::Numeric, in_sums(db, p0, p1)),
    ensures !fits_query(db, Seq::empty(), body_q(ps)),
{
    let rows = gb_rows(db, p0, p1);
    lemma_outer_rows(db, ps, p0, p1);
    assert forall|i: int| 0 <= i < rows.len() implies !fits_pred(db, Seq::<Val>::empty() + #[trigger] rows[i], having_pred(ps)) by {
        lemma_outer_row(db, p0, p1, i);
        let r = Seq::<Val>::empty() + rows[i];
        assert(r =~= rows[i]);
        lemma_avg_capacity(db, r, ps, p0, p1);
        assert(!fits_expr(db, r, Expr::Subquery(Box::new(avg_q(ps)))));
        assert(eval_expr(db, r, Expr::Col(2)) is Ok);
    }
    lemma_filter_capacity(db, Seq::empty(), having_pred(ps), Box::new(outer_gb(ps)), rows, 0);
}

/// The AVG aggregate under a group row: outside its domain.
proof fn lemma_avg_capacity(db: Database, r: Row, ps: Seq<Literal>, p0: Seq<u8>, p1: int)
    requires
        binding(ps, p0, p1), tables_shaped(db), vals_ok(db), r.len() == 3,
        !fits_avg_value(NumKind::Numeric, in_sums(db, p0, p1)),
    ensures !fits_query(db, r, avg_q(ps)),
{
    let pr = in_proj(db, p0, p1);
    let vs = in_sums(db, p0, p1);
    lemma_inner_proj(db, r, ps, p0, p1);
    let args = pr;
    assert forall|i: int| 0 <= i < pr.len() implies #[trigger] agg_args(db, r + pr[i], avg_aggs()) == Ok::<Row, SqlError>(args[i]) by {
        let env = r + pr[i];
        assert(env[3] == pr[i][0]);
        let ars = agg_arg_results(db, env, avg_aggs());
        assert(ars[0] == agg_arg(db, env, avg_aggs()[0]));
        assert(ars[0] == Ok::<Val, SqlError>(env[3]));
        lemma_collect_all(ars, seq![env[3]]);
        assert(seq![env[3]] =~= pr[i]);
    }
    assert(column(args, 0) =~= vs);
    let aggs = avg_aggs();
    assert(aggs[0] == Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(3) });
    assert(!fits_agg_value(aggs[0], column(args, 0)));
    assert(all_of_kind(NumKind::Numeric, vs)) by {
        lemma_in_sums_numeric(db, p0, p1);
    }
    assert(aggs_ok_inside(aggs, args)) by {
        assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(args, j))
            implies agg_value(aggs[j], column(args, j)) is Ok by {
            assert(j == 0);
            lemma_avg_inside_ok(NumKind::Numeric, Expr::Col(3), vs);
        }
    }
    lemma_aggregate_capacity(db, r, aggs, Box::new(inner_proj(ps)), pr, args, 0);
}

/// The inner SUMs are numeric values (all of kind numeric, none NULL).
pub proof fn lemma_in_sums_numeric(db: Database, p0: Seq<u8>, p1: int)
    ensures
        all_of_kind(NumKind::Numeric, in_sums(db, p0, p1)),
        count_non_null(in_sums(db, p0, p1)) == in_sums(db, p0, p1).len(),
{
    lemma_vals_numeric(in_sums(db, p0, p1));
}

/// Numeric values at scale 4: of kind numeric, none NULL.
pub proof fn lemma_vals_numeric(vs: Seq<Val>)
    requires forall|i: int| 0 <= i < vs.len() ==> (#[trigger] vs[i]) is Num,
    ensures all_of_kind(NumKind::Numeric, vs), count_non_null(vs) == vs.len(),
    decreases vs.len(),
{
    if vs.len() > 0 {
        let d = vs.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]) is Num by {
            assert(d[i] == vs[i]);
        }
        lemma_vals_numeric(d);
    }
}

} // verus!
