//! The GROUP BY node of the statement.
//!
//! Over the derived table `zs = pred::zrows`, the node evaluates to the group rows of `dkeys(zs)`
//! (`lemma_eval_group`). When every group's absolute volume mass fits `i128` (`groups_fit`), each group row is
//! `[year, sum0, sum1]` with the exact sums of `bag::zsums` (`grow`, `lemma_group_rows`); when some group's mass
//! does not, the node is outside the capacity domain (`lemma_group_capacity`), whatever the group order.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::exec::relational::domain::*;
use crate::query::param_domain;
use crate::gendb_entry::stores::StoresView;
use crate::link::join::sum_of;
use crate::link::query::{gcount, hit};
use crate::link::expr::i128_max;
use crate::link::capacity::{lemma_group_prepared, lemma_group_by_capacity, aggs_ok_inside, lemma_sum_inside_ok};
use crate::bridge::collect::lemma_collect_all;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::ast::*;
use crate::agent::pred::*;
use crate::agent::bag::*;
use crate::agent::group::*;

verus! {

/// The group sums of key `k` over the derived rows.
pub open spec fn gsums(ps: Seq<Literal>, zs: Seq<Row>, k: Row) -> Tot { zsums(ps, zs, k) }

/// The scale of the first sum: 4 when some row of the group counts for `$1`, else 0.
pub open spec fn s0_of(t: Tot) -> nat { if t.n_then > 0 { 4 } else { 0 } }

/// The group row `[year, sum0, sum1]` of key `k`.
pub open spec fn grow(ps: Seq<Literal>, zs: Seq<Row>, k: Row) -> Row {
    let t = gsums(ps, zs, k);
    k + seq![Val::Num { coeff: t.s_then, scale: s0_of(t) }, Val::Num { coeff: t.s_all, scale: 4 }]
}

/// Every group's absolute volume mass fits `i128`.
pub open spec fn groups_fit(ps: Seq<Literal>, zs: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < dkeys(zs).len() ==> #[trigger] gsums(ps, zs, dkeys(zs)[i]).a_all <= i128_max()
}

/// The normal form's count of a key is the count sum.
pub proof fn lemma_gcount(ps: Seq<Literal>, zs: Seq<Row>, k: Row)
    ensures gcount(gspec(), zs, k) == gsums(ps, zs, k).cnt,
    decreases zs.len(),
{
    if zs.len() > 0 {
        lemma_gcount(ps, zs.drop_last(), k);
        assert(hit(gspec(), zs.last(), k) == (zkey(zs.last()) == k));
    }
}

/// The groups have rows: a key of `dkeys` counts at least one row.
pub proof fn lemma_dkey_count(ps: Seq<Literal>, zs: Seq<Row>, i: int)
    requires all_shape(zs), 0 <= i < dkeys(zs).len(),
    ensures gsums(ps, zs, dkeys(zs)[i]).cnt > 0,
{
    lemma_dkeys(zs);
    let k = dkeys(zs)[i];
    assert(dkeys(zs).contains(k));
    lemma_gcount(ps, zs, k);
}

/// The GROUP BY node over the derived table.
pub proof fn lemma_eval_group(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), param_domain(ps), model_ok(sv),
    ensures ({
        let zs = zrows(sv, ps);
        eval_query(db, Seq::empty(), q8_group(ps)) == collect(group_results(group_aggs(ps), zks(zs), zas(ps, zs)))
    }),
{
    let zs = zrows(sv, ps);
    let ctx = Seq::<Val>::empty();
    lemma_eval_inner(db, sv, ps);
    lemma_zrows_shape(sv, ps);
    assert forall|i: int| 0 <= i < zs.len() implies #[trigger] group_input(db, ctx + zs[i], group_keys(), group_aggs(ps))
        == Ok::<(Row, Row), SqlError>((zks(zs)[i], zas(ps, zs)[i])) by {
        assert(ctx + zs[i] =~= zs[i]);
        lemma_group_input(db, ps, zs[i]);
    }
    let prepared = lemma_group_prepared(db, ctx, group_keys(), group_aggs(ps), zs, zks(zs), zas(ps, zs));
    lemma_eval_group_by(db, ctx, group_keys(), group_aggs(ps), Box::new(q8_inner(ps)));
}

/// One group's aggregate row inside the capacity.
pub proof fn lemma_group_value(ps: Seq<Literal>, zs: Seq<Row>, k: Row)
    requires
        all_shape(zs), gsums(ps, zs, k).cnt > 0, gsums(ps, zs, k).a_all <= i128_max(),
    ensures
        agg_row(group_aggs(ps), mem(ps, zs, k)) == Ok::<Row, SqlError>(seq![
            Val::Num { coeff: gsums(ps, zs, k).s_then, scale: s0_of(gsums(ps, zs, k)) },
            Val::Num { coeff: gsums(ps, zs, k).s_all, scale: 4 }]),
{
    let m = mem(ps, zs, k);
    let t = gsums(ps, zs, k);
    lemma_mem_cols(ps, zs, k);
    lemma_zsums_bounds(ps, zs, k);
    let aggs = group_aggs(ps);
    let rs = agg_value_results(aggs, m);
    lemma_agg_row(aggs, m);
    lemma_num_in_range_small(t.s_then, s0_of(t));
    lemma_num_in_range_small(t.s_all, 4);
    let vs = seq![Val::Num { coeff: t.s_then, scale: s0_of(t) }, Val::Num { coeff: t.s_all, scale: 4 }];
    assert(rs[0] == agg_value(aggs[0], column(m, 0)));
    assert(rs[1] == agg_value(aggs[1], column(m, 1)));
    assert(rs[0] == Ok::<Val, SqlError>(vs[0]));
    assert(rs[1] == Ok::<Val, SqlError>(vs[1]));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        if i == 0 {} else { assert(i == 1); }
    }
    lemma_collect_all(rs, vs);
}

/// Bounds of the group sums.
pub proof fn lemma_zsums_bounds(ps: Seq<Literal>, zs: Seq<Row>, k: Row)
    ensures ({
        let t = zsums(ps, zs, k);
        &&& 0 <= t.n_then <= t.cnt
        &&& 0 <= t.a_then <= t.a_all
        &&& -t.a_all <= t.s_all <= t.a_all
        &&& -t.a_then <= t.s_then <= t.a_then
    }),
    decreases zs.len(),
{
    if zs.len() > 0 {
        lemma_zsums_bounds(ps, zs.drop_last(), k);
    }
}

/// Inside the capacity, the GROUP BY node is the group rows of `dkeys`.
pub proof fn lemma_group_rows(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), param_domain(ps), model_ok(sv), groups_fit(ps, zrows(sv, ps)),
    ensures ({
        let zs = zrows(sv, ps);
        eval_query(db, Seq::empty(), q8_group(ps)) == Ok::<Relation, SqlError>(dkeys(zs).map_values(|k: Row| grow(ps, zs, k)))
    }),
{
    let zs = zrows(sv, ps);
    lemma_eval_group(db, sv, ps);
    lemma_zrows_shape(sv, ps);
    lemma_dkeys(zs);
    let ks = zks(zs);
    let args = zas(ps, zs);
    let rs = group_results(group_aggs(ps), ks, args);
    let vs = dkeys(zs).map_values(|k: Row| grow(ps, zs, k));
    assert forall|g: int| 0 <= g < rs.len() implies #[trigger] rs[g] == Ok::<Row, SqlError>(vs[g]) by {
        let k = dkeys(zs)[g];
        assert(ks.contains(k));
        lemma_key_shape(zs, k);
        lemma_members(ps, zs, k);
        lemma_dkey_count(ps, zs, g);
        lemma_group_value(ps, zs, k);
    }
    lemma_collect_all(rs, vs);
}

/// Some group's absolute volume mass leaves `i128`: the GROUP BY node is outside the capacity domain.
pub proof fn lemma_group_capacity(db: Database, sv: StoresView, ps: Seq<Literal>, g: int)
    requires
        tables_of(sv, db), param_domain(ps), model_ok(sv),
        0 <= g < dkeys(zrows(sv, ps)).len(),
        gsums(ps, zrows(sv, ps), dkeys(zrows(sv, ps))[g]).a_all > i128_max(),
    ensures !fits_query(db, Seq::empty(), q8_group(ps)),
{
    let zs = zrows(sv, ps);
    let ctx = Seq::<Val>::empty();
    let ks = zks(zs);
    let args = zas(ps, zs);
    let aggs = group_aggs(ps);
    lemma_eval_inner(db, sv, ps);
    lemma_zrows_shape(sv, ps);
    lemma_dkeys(zs);
    assert forall|i: int| 0 <= i < zs.len() implies #[trigger] group_input(db, ctx + zs[i], group_keys(), aggs)
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(ctx + zs[i] =~= zs[i]);
        lemma_group_input(db, ps, zs[i]);
    }
    // every group's aggregates succeed inside their capacity condition
    assert forall|h: int| 0 <= h < distinct_rows(ks).len() implies #[trigger] aggs_ok_inside(aggs, group_members(ks, args, distinct_rows(ks)[h])) by {
        let k = dkeys(zs)[h];
        assert(ks.contains(k));
        lemma_key_shape(zs, k);
        lemma_members(ps, zs, k);
        let m = mem(ps, zs, k);
        lemma_mem_cols(ps, zs, k);
        assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(m, j)) implies agg_value(aggs[j], column(m, j)) is Ok by {
            if j == 0 {
                lemma_sum_inside_ok(NumKind::Numeric, case_expr(ps), column(m, 0));
            } else {
                assert(j == 1);
                lemma_sum_inside_ok(NumKind::Numeric, Expr::Col(1), column(m, 1));
            }
        }
    }
    // the volume SUM of group `g` is outside its condition
    let k = dkeys(zs)[g];
    assert(ks.contains(k));
    lemma_key_shape(zs, k);
    lemma_members(ps, zs, k);
    lemma_dkey_count(ps, zs, g);
    let m = mem(ps, zs, k);
    lemma_mem_cols(ps, zs, k);
    assert(aggs[1] == Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(1) });
    assert(sum_mass(NumKind::Numeric, column(m, 1)) == gsums(ps, zs, k).a_all);
    assert(!fits_agg_value(aggs[1], column(m, 1)));
    lemma_group_by_capacity(db, ctx, group_keys(), aggs, Box::new(q8_inner(ps)), zs, ks, args, g, 1);
}

} // verus!
