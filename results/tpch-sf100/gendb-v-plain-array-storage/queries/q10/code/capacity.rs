//! `Capacity`: a group whose absolute SUM mass exceeds `i128::MAX` puts the statement outside its capacity domain
//! (`lemma_capacity`).
//!
//! The canonical GROUP BY groups the filtered joined rows by their keys; with exact keys its groups are the normal
//! form's keys and each group's argument column is the normal form's `members` (`link::query`). The SUM's capacity
//! condition is the absolute mass of that column (at scale 4: the sum of the absolute coefficients), which is the
//! group's `gabs`, the customer's `ctabs` (`agent::groups`). Every other group's SUM succeeds inside its condition,
//! so `link::capacity::lemma_group_by_capacity` applies; the projection above inherits it.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::scalar::NumKind;
use crate::spec::equality::distinct_rows;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::{bound_db, capacity_domain};
use crate::query::{query_spec_at, param_domain};
use crate::exec::relational::domain::*;
use crate::link::query::*;
use crate::link::expr::i128_max;
use crate::link::capacity::{lemma_group_by_capacity, lemma_first_input, aggs_ok_inside, lemma_sum_inside_ok, lemma_num_mass_uniform};
use crate::agent::cols::*;
use crate::agent::normal::*;
use crate::agent::denot::*;
use crate::agent::groups::*;

verus! {

/// The absolute mass of a group's argument column is its `gabs`.
pub proof fn lemma_members_mass(g: QuerySpec, xs: Seq<Row>, k: Row)
    requires g.aggs == seq![AggKind::Sum { scale: 4 }],
    ensures num_mass_at(column(members(g, xs, k), 0), 4) == gabs(g, xs, k, 0),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let xi = xs.drop_last();
        lemma_members_mass(g, xi, k);
        let m = members(g, xs, k);
        let mi = members(g, xi, k);
        if hit(g, xs.last(), k) {
            let av = arg_vals(g, xs.last());
            assert(m == mi.push(av));
            assert(column(m, 0) =~= column(mi, 0).push(av[0]));
            assert(av[0] == Val::Num { coeff: (g.arg)(0, xs.last()), scale: 4 });
            assert(column(m, 0).drop_last() =~= column(mi, 0));
            assert(pow10(0) == 1) by (compute);
        } else {
            assert(m == mi);
        }
    } else {
        assert(column(members(g, xs, k), 0) =~= Seq::<Val>::empty());
    }
}

/// Every value of a group's argument column has scale 4.
pub proof fn lemma_members_scale(g: QuerySpec, xs: Seq<Row>, k: Row)
    requires g.aggs == seq![AggKind::Sum { scale: 4 }],
    ensures forall|i: int| 0 <= i < column(members(g, xs, k), 0).len() ==>
        (#[trigger] column(members(g, xs, k), 0)[i]) == (Val::Num { coeff: coeff_of(column(members(g, xs, k), 0)[i]), scale: 4 }),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let xi = xs.drop_last();
        lemma_members_scale(g, xi, k);
        let m = members(g, xs, k);
        let mi = members(g, xi, k);
        if hit(g, xs.last(), k) {
            let av = arg_vals(g, xs.last());
            assert(m == mi.push(av));
            assert(column(m, 0) =~= column(mi, 0).push(av[0]));
        } else {
            assert(m == mi);
        }
    }
}

/// The statement is outside its capacity domain when the group of customer `a0` (whose nation exists) has absolute
/// mass beyond `i128::MAX`.
pub proof fn lemma_capacity(sv: StoresView, db: Database, ps: Seq<Literal>, t1: int, dlo: int, dhi: int, a0: int)
    requires
        bound_db(sv, db), param_domain(ps), hi_res(pd_of(ps)) == Ok::<int, SqlError>(t1), win_of(dlo, dhi, pd_of(ps), t1),
        0 <= a0 < n_c(sv), natok(sv, a0),
        ctabs(sv, dlo, dhi, a0) > i128_max(),
    ensures !capacity_domain(db, query_spec_at(ps)),
{
    let pd = pd_of(ps);
    let (g, xs, rows, cols) = (q_spec(pd, t1), q_xs(db), q_rows(db), q_cols());
    let kstar = ckey(sv, a0);
    lemma_query_shape(ps);
    lemma_cust_group(sv, db, pd, t1, dlo, dhi, a0);
    assert(gabs(g, xs, kstar, 0) > i128_max());
    if gcount(g, xs, kstar) == 0 {
        lemma_zero_count(g, xs, kstar, 0);
    }
    // the filter's rows
    lemma_eval_from(sv, db);
    lemma_pred_agrees(sv, db, ps, t1, dlo, dhi);
    lemma_filter_rows(db, q_from(), rows, cols, q_pred(ps[0]), g);
    let kept = keep_true(rows, qual_truths(g, xs));
    lemma_kept_rows(g, rows, cols);
    lemma_keys_agree(sv, db, ps, t1);
    lemma_args_agree(sv, db, ps, t1);
    lemma_keys_exact(sv, db, ps, t1);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    assert(ks.len() == kept.len() && args.len() == kept.len());
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], q_group_keys(), q_aggs())
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(Seq::<Val>::empty() + kept[i] =~= kept[i]);
        assert(rows.contains(kept[i]) && (g.qual)(proj(kept[i], cols)));
        let r = choose|r: int| 0 <= r < rows.len() && rows[r] == kept[i];
        assert(eval_exprs(db, rows[r], q_group_keys()) == Ok::<Row, SqlError>((g.key)(proj(rows[r], cols))));
        assert(agg_args(db, rows[r], q_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[r], cols))));
        assert(proj(kept[i], cols) == qrows(g, xs)[i]);
    }
    // the canonical groups are the normal form's
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {}
    lemma_distinct_gkeys(g, xs, pool);
    lemma_gkeys(g, xs);
    assert(gkeys(g, xs).contains(kstar));
    let gi = choose|gi: int| 0 <= gi < gkeys(g, xs).len() && gkeys(g, xs)[gi] == kstar;
    assert(distinct_rows(ks)[gi] == kstar);
    // the group of kstar is outside its capacity condition
    assert(pool.contains(kstar)) by {
        assert(pool.contains(gkeys(g, xs)[gi]));
    }
    lemma_group_members(g, xs, kstar, pool);
    let vs = column(members(g, xs, kstar), 0);
    lemma_members_col(g, xs, kstar, 0);
    lemma_members_mass(g, xs, kstar);
    lemma_members_scale(g, xs, kstar);
    assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i] matches Val::Num { coeff, scale } ==> scale == 4) by {}
    lemma_num_mass_uniform(vs, 4);
    assert(vs.len() > 0);
    assert(vs[0] is Num);
    assert(num_max_scale(vs) == 4);
    assert(!fits_agg_value(q_aggs()[0], column(group_members(ks, args, distinct_rows(ks)[gi]), 0)));
    // every group's SUM succeeds inside its condition
    assert forall|h: int| 0 <= h < distinct_rows(ks).len() implies #[trigger] aggs_ok_inside(q_aggs(), group_members(ks, args, distinct_rows(ks)[h])) by {
        let kh = gkeys(g, xs)[h];
        assert(pool.contains(kh));
        lemma_group_members(g, xs, kh, pool);
        lemma_members_col(g, xs, kh, 0);
        let vh = column(members(g, xs, kh), 0);
        assert forall|j: int| 0 <= j < q_aggs().len() && #[trigger] fits_agg_value(q_aggs()[j], column(group_members(ks, args, distinct_rows(ks)[h]), j))
            implies agg_value(q_aggs()[j], column(group_members(ks, args, distinct_rows(ks)[h]), j)) is Ok by {
            assert(j == 0);
            lemma_sum_inside_ok(NumKind::Numeric, q_sum_arg(), vh);
        }
    }
    lemma_group_by_capacity(db, Seq::empty(), q_group_keys(), q_aggs(), Box::new(q_filter(ps[0])), kept, ks, args, gi, 0);
    lemma_first_input(db, Seq::empty(), q_body(ps[0]));
}

} // verus!
