//! Capacity: the statement is outside its capacity domain (`!fits_query` of the canonical evaluation) when
//! - an outer group's SUM has absolute mass above `i128::MAX` (`lemma_cap_top`: the outer GROUP BY, the HAVING
//!   filter's first input, is outside its domain);
//! - inside the HAVING subquery (evaluated for every outer group row, a nonempty set), a per-cik SUM's mass, the AVG's
//!   mass, or the AVG's division leaves its domain (`lemma_cap_sub`): every row's HAVING condition is then outside
//!   its domain, and the outer groups evaluate without error.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::equality::distinct_rows;
use crate::spec::aggs::avg::*;
use crate::spec::fns::div::num_div_fits;
use crate::exec::domain::fits_expr;
use crate::exec::relational::domain::{fits_query, fits_pred, fits_agg_value, num_mass_at};
use crate::exec::aggs::avg::fits_avg_value;
use crate::link::query::*;
use crate::link::join::keep;
use crate::link::capacity::*;
use crate::link::expr::i128_max;
use crate::agent::ast::*;
use crate::agent::nf::*;
use crate::agent::eval::*;
use crate::agent::common::sums::*;

verus! {

/// The mass of the SUM's argument values of a group is the toolkit's absolute sum.
pub proof fn lemma_members_mass(g: QuerySpec, xs: Seq<Row>, k: Row)
    requires g.aggs == seq![AggKind::Sum { scale: 4 }],
    ensures
        num_mass_at(column(members(g, xs, k), 0), 4) == gabs(g, xs, k, 0),
        forall|i: int| 0 <= i < column(members(g, xs, k), 0).len() ==>
            (#[trigger] column(members(g, xs, k), 0)[i] matches Val::Num { coeff, scale } ==> scale == 4),
        forall|i: int| 0 <= i < column(members(g, xs, k), 0).len() ==> (#[trigger] column(members(g, xs, k), 0)[i]) is Num,
    decreases xs.len(),
{
    let vs = column(members(g, xs, k), 0);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        lemma_members_mass(g, xi, k);
        let vsi = column(members(g, xi, k), 0);
        if hit(g, x, k) {
            assert(vs =~= vsi.push(arg_vals(g, x)[0]));
            assert(vs.drop_last() =~= vsi);
            assert(arg_vals(g, x)[0] == Val::Num { coeff: (g.arg)(0, x), scale: 4 });
            assert(pow10(0) == 1);
            assert(abs((g.arg)(0, x)) * pow10((4 - 4) as nat) == abs((g.arg)(0, x))) by {
                assert((4 - 4) as nat == 0nat);
            }
            assert forall|i: int| 0 <= i < vs.len() implies
                (#[trigger] vs[i] matches Val::Num { coeff, scale } ==> scale == 4) by {
                if i < vsi.len() {
                    assert(vs[i] == vsi[i]);
                }
            }
            assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i]) is Num by {
                if i < vsi.len() {
                    assert(vs[i] == vsi[i]);
                }
            }
        } else {
            assert(vs =~= vsi);
        }
    } else {
        assert(vs =~= Seq::<Val>::empty());
    }
}

/// Every group's SUM succeeds inside its capacity condition.
proof fn lemma_groups_ok_inside(g: QuerySpec, aggs: Seq<Agg>, xs: Seq<Row>)
    requires
        aggs_match(aggs, g), aggs.len() == 1, aggs[0] is Sum,
        g.aggs == seq![AggKind::Sum { scale: 4 }],
        keys_exact(g, xs),
    ensures ({
        let ks = qkeys(g, xs);
        let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
        forall|h: int| 0 <= h < distinct_rows(ks).len() ==> #[trigger] aggs_ok_inside(aggs, group_members(ks, args, distinct_rows(ks)[h]))
    }),
{
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    let ds = gkeys(g, xs);
    assert forall|h: int| 0 <= h < distinct_rows(ks).len() implies #[trigger] aggs_ok_inside(aggs, group_members(ks, args, distinct_rows(ks)[h])) by {
        let kh = ds[h];
        assert(pool.contains(kh));
        lemma_group_members(g, xs, kh, pool);
        lemma_members_col(g, xs, kh, 0);
        let vh = column(members(g, xs, kh), 0);
        assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(group_members(ks, args, kh), j))
            implies agg_value(aggs[j], column(group_members(ks, args, kh), j)) is Ok by {
            assert(j == 0);
            assert(agg_matches(aggs[0], g.aggs[0]));
            lemma_sum_inside_ok(NumKind::Numeric, aggs[0]->Sum_arg, vh);
        }
    }
}

/// The group of `kk` is a group of the GROUP BY, and its SUM is outside its capacity condition.
proof fn lemma_violating_group(g: QuerySpec, aggs: Seq<Agg>, xs: Seq<Row>, kk: Row) -> (gi: int)
    requires
        aggs_match(aggs, g), aggs.len() == 1, aggs[0] is Sum,
        g.aggs == seq![AggKind::Sum { scale: 4 }],
        keys_exact(g, xs),
        gabs(g, xs, kk, 0) > i128::MAX as int,
    ensures ({
        let ks = qkeys(g, xs);
        let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
        &&& 0 <= gi < distinct_rows(ks).len()
        &&& !fits_agg_value(aggs[0], column(group_members(ks, args, distinct_rows(ks)[gi]), 0))
    }),
{
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    if gcount(g, xs, kk) == 0 {
        lemma_zero_count(g, xs, kk, 0);
    }
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    lemma_gkeys(g, xs);
    let ds = gkeys(g, xs);
    assert(ds.contains(kk));
    let gi = choose|i: int| 0 <= i < ds.len() && ds[i] == kk;
    lemma_group_members(g, xs, kk, pool);
    lemma_members_col(g, xs, kk, 0);
    lemma_members_mass(g, xs, kk);
    let vs = column(members(g, xs, kk), 0);
    lemma_num_mass_uniform(vs, 4);
    assert(vs.len() > 0);
    assert(vs[0] is Num);
    assert(!fits_agg_value(aggs[0], vs));
    gi
}

/// GROUP BY under context `ctx` over the qualifying rows, with a group whose SUM mass exceeds `i128::MAX`: the node is
/// outside its capacity domain.
pub proof fn lemma_cap_groupby(db: Database, ctx: Row, input: Query, keys: Seq<Expr>, aggs: Seq<Agg>, g: QuerySpec,
    xs: Seq<Row>, kk: Row)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(keep(xs, g.qual)),
        forall|i: int| 0 <= i < xs.len() && (g.qual)(#[trigger] xs[i]) ==>
            eval_exprs(db, ctx + xs[i], keys) == Ok::<Row, SqlError>((g.key)(xs[i])),
        forall|i: int| 0 <= i < xs.len() && (g.qual)(#[trigger] xs[i]) ==>
            agg_args(db, ctx + xs[i], aggs) == Ok::<Row, SqlError>(arg_vals(g, xs[i])),
        aggs_match(aggs, g),
        aggs.len() == 1,
        aggs[0] is Sum,
        g.aggs == seq![AggKind::Sum { scale: 4 }],
        keys_exact(g, xs),
        gabs(g, xs, kk, 0) > i128::MAX as int,
    ensures !fits_query(db, ctx, Query::GroupBy { keys, aggs, input: Box::new(input) }),
{
    hide(eval_query);
    hide(eval_exprs);
    hide(agg_args);
    hide(fits_query);
    let kept = keep(xs, g.qual);
    lemma_qrows_keep(g, xs);
    crate::link::join::lemma_keep_members(xs, g.qual);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, ctx + kept[i], keys, aggs)
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(xs.contains(kept[i]) && (g.qual)(kept[i]));
        let m = choose|m: int| 0 <= m < xs.len() && xs[m] == kept[i];
        assert((g.qual)(xs[m]));
    }
    let gi = lemma_violating_group(g, aggs, xs, kk);
    lemma_groups_ok_inside(g, aggs, xs);
    lemma_group_by_capacity(db, ctx, keys, aggs, Box::new(input), kept, ks, args, gi, 0);
}

/// An outer group's SUM mass exceeds `i128::MAX`: the statement is outside its capacity domain.
pub proof fn lemma_cap_top(db: Database, p0: Seq<u8>, p1: int, kk: Row)
    requires rows_ok(db), int_in_range(IntKind::Int4, p1), gabs(g_top(p0, p1), joined(db), kk, 0) > i128::MAX as int,
    ensures !fits_query(db, Seq::empty(), q_body(lits(p0, p1))),
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
    lemma_cap_groupby(db, ctx, q_where(lits(p0, p1), 0), keys_top(), seq![agg_sum(0)], g, xs, kk);
    lemma_first_input(db, ctx, q_body(lits(p0, p1)));
}

/// A per-cik SUM mass exceeds `i128::MAX`: the subquery is outside its domain under every context of 3 values.
pub proof fn lemma_inner_cik(db: Database, p0: Seq<u8>, p1: int, ctx: Row, kk: Row)
    requires rows_ok(db), int_in_range(IntKind::Int4, p1), ctx.len() == 3,
        gabs(g_cik(p0, p1), joined(db), kk, 0) > i128::MAX as int,
    ensures !fits_query(db, ctx, q_avg(lits(p0, p1))),
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
    lemma_cap_groupby(db, ctx, q_where(lits(p0, p1), 3), keys_cik(), seq![agg_sum(3)], g, xs, kk);
    lemma_first_input(db, ctx, q_project(lits(p0, p1)));
    lemma_first_input(db, ctx, q_avg(lits(p0, p1)));
}

/// The AVG over the per-cik sums leaves its domain (its mass, or its division): the subquery is outside its domain
/// under every context of 3 values.
pub proof fn lemma_inner_avg(db: Database, p0: Seq<u8>, p1: int, ctx: Row)
    requires
        rows_ok(db), int_in_range(IntKind::Int4, p1), ctx.len() == 3, sum_caps(g_cik(p0, p1), joined(db)),
        !fits_avg_value(NumKind::Numeric, cik_sums(p0, p1, joined(db))),
    ensures !fits_query(db, ctx, q_avg(lits(p0, p1))),
{
    let xs = joined(db);
    let prows = cik_rows(p0, p1, xs);
    crate::agent::eval::lemma_eval_project(db, p0, p1, ctx);
    assert forall|i: int| 0 <= i < prows.len() implies (#[trigger] prows[i]).len() == 1 by {}
    lemma_avg_args(db, ctx, prows);
    let vs = column(prows, 0);
    assert(vs =~= cik_sums(p0, p1, xs));
    lemma_num_sum_scale4(gkeys(g_cik(p0, p1), xs), cik_sum_fn(p0, p1, xs));
    assert(!fits_agg_value(agg_avg(), vs));
    assert forall|j: int| 0 <= j < 1 && #[trigger] fits_agg_value(seq![agg_avg()][j], column(prows, j))
        implies agg_value(seq![agg_avg()][j], column(prows, j)) is Ok by {
        lemma_avg_inside_ok(NumKind::Numeric, Expr::Col(3), vs);
    }
    assert(aggs_ok_inside(seq![agg_avg()], prows));
    lemma_aggregate_capacity(db, ctx, seq![agg_avg()], Box::new(q_project(lits(p0, p1))), prows, prows, 0);
}

/// Every outer group row has three values.
proof fn lemma_top_rows_len(db: Database, p0: Seq<u8>, p1: int)
    requires rows_ok(db),
    ensures forall|i: int| 0 <= i < gkeys(g_top(p0, p1), joined(db)).len() ==>
        (#[trigger] full_row(g_top(p0, p1), joined(db), gkeys(g_top(p0, p1), joined(db))[i])).len() == 3,
{
    let g = g_top(p0, p1);
    let xs = joined(db);
    assert forall|i: int| 0 <= i < gkeys(g, xs).len() implies
        (#[trigger] full_row(g, xs, gkeys(g, xs)[i])).len() == 3 by {
        let k = gkeys(g, xs)[i];
        assert(gkeys(g, xs).contains(k));
        lemma_gkeys_witness(g, xs, k);
        let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
        lemma_joined_rows_ok(db);
        lemma_top_key(p0, p1);
        assert(joined_row_ok(xs[m]));
        let (n, s) = choose|n: Row, s: Row| num_row_ok(n) && sub_row_ok(s) && xs[m] == n + s;
        assert((g.key)(xs[m]) == key_top_s(s));
    }
}

/// The subquery is outside its domain under every context of 3 values, the outer groups are within theirs and
/// nonempty: the statement is outside its capacity domain (the HAVING filter's first per-row condition).
pub proof fn lemma_cap_sub(db: Database, p0: Seq<u8>, p1: int)
    requires
        rows_ok(db), int_in_range(IntKind::Int4, p1),
        sum_caps(g_top(p0, p1), joined(db)),
        gkeys(g_top(p0, p1), joined(db)).len() > 0,
        forall|ctx: Row| ctx.len() == 3 ==> !#[trigger] fits_query(db, ctx, q_avg(lits(p0, p1))),
    ensures !fits_query(db, Seq::empty(), q_body(lits(p0, p1))),
{
    let ps = lits(p0, p1);
    let g = g_top(p0, p1);
    let xs = joined(db);
    let ctx = Seq::<Val>::empty();
    lemma_eval_group_top(db, p0, p1);
    let grows = gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k));
    lemma_top_rows_len(db, p0, p1);
    assert forall|i: int| 0 <= i < grows.len() implies !#[trigger] fits_pred(db, ctx + grows[i], pred_having(ps)) by {
        let env = ctx + grows[i];
        assert(env.len() == 3);
        assert(!fits_query(db, env, q_avg(ps)));
        assert(fits_expr(db, env, Expr::Col(2)));
        assert(eval_expr(db, env, Expr::Col(2)) is Ok);
        assert(!fits_expr(db, env, Expr::Subquery(Box::new(q_avg(ps)))));
    }
    lemma_filter_capacity(db, ctx, pred_having(ps), Box::new(q_group_top(ps)), grows, 0);
}

} // verus!
