//! `Capacity`: a group whose absolute volume sum exceeds `i128::MAX` puts the statement outside its capacity domain
//! (`lemma_capacity`).
//!
//! The canonical GROUP BY groups the SELECT rows by their keys; with exact keys its groups are the normal form's
//! keys and each group's argument column is the normal form's `members` (`link::query`). The SUM's capacity
//! condition is the absolute mass of that column (at scale 4: the sum of the absolute coefficients), which is the
//! key's `gabs`, at least the group's absolute sum (`answer::lemma_ksum_groups`). Every other group's SUM succeeds
//! inside its condition, so `link::capacity::lemma_group_by_capacity` applies to the body itself.
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
use crate::link::capacity::{lemma_group_by_capacity, aggs_ok_inside, lemma_sum_inside_ok, lemma_num_mass_uniform};
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::denotation::*;
use crate::agent::lines::*;
use crate::agent::groups::*;
use crate::agent::answer::*;

verus! {

/// The absolute mass of a group's argument column is its `gabs`.
pub proof fn lemma_members_mass(xs: Seq<Row>, k: Row)
    ensures num_mass_at(column(members(g2(), xs, k), 0), 4) == gabs(g2(), xs, k, 0),
    decreases xs.len(),
{
    let g = g2();
    if xs.len() > 0 {
        let xi = xs.drop_last();
        lemma_members_mass(xi, k);
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
pub proof fn lemma_members_scale(xs: Seq<Row>, k: Row)
    ensures forall|i: int| 0 <= i < column(members(g2(), xs, k), 0).len() ==>
        (#[trigger] column(members(g2(), xs, k), 0)[i]) == (Val::Num { coeff: coeff_of(column(members(g2(), xs, k), 0)[i]), scale: 4 }),
    decreases xs.len(),
{
    let g = g2();
    if xs.len() > 0 {
        let xi = xs.drop_last();
        lemma_members_scale(xi, k);
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

/// The key of group `gi` has absolute mass beyond `i128::MAX` when the group's absolute sum is.
proof fn lemma_key_mass(sv: StoresView, db: Database, ps: Seq<Literal>, gi: int)
    requires bound_db(sv, db), param_domain(ps), 0 <= gi < 4, lsum(sv, ps, gi, 2, 0, n_l(sv)) > i128_max(),
    ensures
        gabs(g2(), sel_rows(db, ps), grp_key(ps, gi), 0) > i128_max(),
        gcount(g2(), sel_rows(db, ps), grp_key(ps, gi)) > 0,
{
    let (g, xs) = (g2(), sel_rows(db, ps));
    let kstar = grp_key(ps, gi);
    lemma_parts_shape(sv, db);
    lemma_group_sums(sv, db, ps, kstar);
    lemma_ksum_groups(sv, ps, kstar, 2, n_l(sv));
    assert forall|h: int| #[trigger] lsum(sv, ps, h, 2, 0, n_l(sv)) >= 0 by {
        lemma_lsum_bounds(sv, ps, h, 0, n_l(sv));
    }
    if gcount(g, xs, kstar) == 0 {
        lemma_zero_count(g, xs, kstar, 0);
    }
}

/// A GROUP BY over the SELECT rows `rows` (projected identically) whose key `kstar` has absolute mass beyond
/// `i128::MAX` is outside its capacity domain.
proof fn lemma_capacity_key(db: Database, ps: Seq<Literal>, rows: Seq<Row>, kstar: Row)
    requires
        eval_query(db, Seq::empty(), q7_project(ps)) == Ok::<Relation, SqlError>(rows),
        proj_all(rows, c4()) == rows,
        keys_agree(db, rows, c4(), q7_keys(), g2()),
        args_agree(db, rows, c4(), q7_aggs(), g2()),
        keys_exact(g2(), proj_all(rows, c4())),
        gabs(g2(), rows, kstar, 0) > i128_max(),
        gcount(g2(), rows, kstar) > 0,
    ensures !fits_query(db, Seq::empty(), q7_body(ps)),
{
    let (g, cols) = (g2(), c4());
    let xs = proj_all(rows, cols);
    assert forall|x: Row| #[trigger] (g.qual)(x) by {}
    lemma_table_rows(db, q7_project(ps), rows, cols, g);
    let kept = keep_true(rows, qual_truths(g, xs));
    lemma_kept_rows(g, rows, cols);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    assert(ks.len() == kept.len() && args.len() == kept.len());
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], q7_keys(), q7_aggs())
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(Seq::<Val>::empty() + kept[i] =~= kept[i]);
        assert(rows.contains(kept[i]) && (g.qual)(proj(kept[i], cols)));
        let r = choose|r: int| 0 <= r < rows.len() && rows[r] == kept[i];
        assert(eval_exprs(db, rows[r], q7_keys()) == Ok::<Row, SqlError>((g.key)(proj(rows[r], cols))));
        assert(agg_args(db, rows[r], q7_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[r], cols))));
        assert(proj(kept[i], cols) == qrows(g, xs)[i]);
    }
    // the canonical groups are the normal form's
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {}
    lemma_distinct_gkeys(g, xs, pool);
    lemma_gkeys(g, xs);
    assert(gkeys(g, xs).contains(kstar));
    let gix = choose|gix: int| 0 <= gix < gkeys(g, xs).len() && gkeys(g, xs)[gix] == kstar;
    assert(distinct_rows(ks)[gix] == kstar);
    // the group of kstar is outside its capacity condition
    assert(pool.contains(kstar)) by {
        assert(pool.contains(gkeys(g, xs)[gix]));
    }
    lemma_group_members(g, xs, kstar, pool);
    let vs = column(members(g, xs, kstar), 0);
    lemma_members_col(g, xs, kstar, 0);
    lemma_members_mass(xs, kstar);
    lemma_members_scale(xs, kstar);
    assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i] matches Val::Num { coeff, scale } ==> scale == 4) by {}
    lemma_num_mass_uniform(vs, 4);
    assert(vs.len() > 0);
    assert(vs[0] is Num);
    assert(num_max_scale(vs) == 4);
    assert(!fits_agg_value(q7_aggs()[0], column(group_members(ks, args, distinct_rows(ks)[gix]), 0)));
    // every group's SUM succeeds inside its condition
    assert forall|h: int| 0 <= h < distinct_rows(ks).len() implies #[trigger] aggs_ok_inside(q7_aggs(), group_members(ks, args, distinct_rows(ks)[h])) by {
        let kh = gkeys(g, xs)[h];
        assert(pool.contains(kh));
        lemma_group_members(g, xs, kh, pool);
        lemma_members_col(g, xs, kh, 0);
        let vh = column(members(g, xs, kh), 0);
        assert forall|j: int| 0 <= j < q7_aggs().len() && #[trigger] fits_agg_value(q7_aggs()[j], column(group_members(ks, args, distinct_rows(ks)[h]), j))
            implies agg_value(q7_aggs()[j], column(group_members(ks, args, distinct_rows(ks)[h]), j)) is Ok by {
            assert(j == 0);
            lemma_sum_inside_ok(NumKind::Numeric, Expr::Col(3), vh);
        }
    }
    lemma_group_by_capacity(db, Seq::empty(), q7_keys(), q7_aggs(), Box::new(q7_project(ps)), kept, ks, args, gix, 0);
}

/// The statement is outside its capacity domain when group `gi`'s absolute volume sum exceeds `i128::MAX`.
pub proof fn lemma_capacity(sv: StoresView, db: Database, ps: Seq<Literal>, gi: int)
    requires bound_db(sv, db), param_domain(ps), 0 <= gi < 4, lsum(sv, ps, gi, 2, 0, n_l(sv)) > i128_max(),
    ensures !capacity_domain(db, query_spec_at(ps)),
{
    let rows = sel_rows(db, ps);
    lemma_query_shape(ps);
    lemma_sel_proj(sv, db, ps);
    lemma_key_mass(sv, db, ps, gi);
    crate::agent::denotation::lemma_eval_project(sv, db, ps);
    lemma_group_premises(sv, db, ps);
    lemma_capacity_key(db, ps, rows, grp_key(ps, gi));
}

} // verus!
