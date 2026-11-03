//! The capacity answer: when the absolute value mass of some group of the statement's GROUP BY exceeds `i128::MAX`,
//! the SUM of that group is outside its capacity condition (`sum_mass_fits`), every group's aggregates inside theirs
//! succeed (counts fit int8), so the GROUP BY, and with it the HAVING filter on top, is outside `fits_query`
//! (`link::capacity::lemma_group_by_capacity`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::scalar::NumKind;
use crate::spec::equality::distinct_rows;
use crate::spec::numeric::{abs, pow10};
use crate::exec::relational::domain::{fits_query, fits_agg_value, sum_mass, num_mass_at, num_max_scale, sum_mass_fits};
use crate::link::query::{QuerySpec, gcount, gsum, gabs, gkeys, hit, members, qrows, qkeys, key_pool, arg_vals, proj,
    proj_all, qual_truths, keys_agree, args_agree, keys_exact, lemma_kept_rows, lemma_pool_exact, lemma_distinct_gkeys,
    lemma_group_members, lemma_members_col, lemma_gkeys, lemma_zero_count};
use crate::link::capacity::{aggs_ok_inside, lemma_group_by_capacity, lemma_count_value, lemma_sum_inside_ok};
use crate::query::param_domain;
use super::model::*;

verus! {

/// The absolute mass of a group's SUM argument column (all at scale 4) is the group's absolute sum.
proof fn lemma_members_mass(ps: Seq<Literal>, xs: Seq<Row>, k: Row)
    ensures ({
        let vs = column(members(lj_spec(ps), xs, k), 1);
        &&& num_mass_at(vs, 4) == gabs(lj_spec(ps), xs, k, 1)
        &&& gcount(lj_spec(ps), xs, k) > 0 ==> num_max_scale(vs) == 4
    }),
    decreases xs.len(),
{
    let g = lj_spec(ps);
    let vs = column(members(g, xs, k), 1);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        lemma_members_mass(ps, xi, k);
        let vsi = column(members(g, xi, k), 1);
        if hit(g, xs.last(), k) {
            assert(vs =~= vsi.push(arg_vals(g, xs.last())[1]));
            assert(vs.drop_last() =~= vsi);
            assert(arg_vals(g, xs.last())[1] == Val::Num { coeff: coeff7(1, xs.last()), scale: 4 });
            assert(pow10(0) == 1);
            assert(abs(coeff7(1, xs.last())) * pow10((4 - 4) as nat) == abs(coeff7(1, xs.last())));
            if gcount(g, xi, k) == 0 {
                lemma_members_scale_zero(ps, xi, k);
            }
        } else {
            assert(vs =~= vsi);
        }
    } else {
        assert(vs =~= Seq::<Val>::empty());
    }
}

/// A group without rows has no members, so the max scale of its column is 0.
proof fn lemma_members_scale_zero(ps: Seq<Literal>, xs: Seq<Row>, k: Row)
    requires gcount(lj_spec(ps), xs, k) == 0,
    ensures num_max_scale(column(members(lj_spec(ps), xs, k), 1)) == 0,
    decreases xs.len(),
{
    let g = lj_spec(ps);
    if xs.len() > 0 {
        lemma_members_scale_zero(ps, xs.drop_last(), k);
        assert(column(members(g, xs, k), 1) =~= column(members(g, xs.drop_last(), k), 1));
    } else {
        assert(column(members(g, xs, k), 1) =~= Seq::<Val>::empty());
    }
}

/// Every group's aggregates inside their capacity condition succeed.
proof fn lemma_group_ok_inside(ps: Seq<Literal>, xs: Seq<Row>, k: Row)
    requires gcount(lj_spec(ps), xs, k) <= crate::spec::limits::int8_max(),
    ensures aggs_ok_inside(gb_aggs(), members(lj_spec(ps), xs, k)),
{
    let g = lj_spec(ps);
    let m = members(g, xs, k);
    lemma_members_col(g, xs, k, 0);
    lemma_members_col(g, xs, k, 1);
    assert forall|j: int| 0 <= j < gb_aggs().len() && #[trigger] fits_agg_value(gb_aggs()[j], column(m, j))
        implies agg_value(gb_aggs()[j], column(m, j)) is Ok by {
        if j == 0 {
            lemma_count_value(Agg::CountStar, column(m, 0));
        } else {
            lemma_sum_inside_ok(NumKind::Numeric, Expr::Col(7), column(m, 1));
        }
    }
}

/// A group of the statement whose absolute SUM mass exceeds `i128::MAX` puts the statement outside `fits_query`.
pub proof fn lemma_capacity(db: Database, ps: Seq<Literal>, l: Seq<Row>, r: Seq<Row>, k: Row)
    requires
        db.tables.len() == 4,
        db.tables[1] == l,
        db.tables[3] == r,
        nums_ok(l),
        pres_ok(r),
        query_arity(db.schema, Query::Table(3)) == 10,
        param_domain(ps),
        gabs(lj_spec(ps), lj_rows(l, r), k, 1) > i128::MAX,
        forall|k2: Row| #[trigger] gcount(lj_spec(ps), lj_rows(l, r), k2) <= crate::spec::limits::int8_max(),
    ensures !fits_query(db, Seq::empty(), body_query(ps)),
{
    hide(eval_query);
    hide(eval_exprs);
    hide(agg_args);
    let g = lj_spec(ps);
    let xs = lj_rows(l, r);
    let cols = ident19();
    lemma_where_facts(db, ps, l, r);
    let kept = keep_true(xs, qual_truths(g, proj_all(xs, cols)));
    lemma_kept_rows(g, xs, cols);
    let q = qrows(g, xs);
    let ks = qkeys(g, xs);
    let args = q.map_values(|x: Row| arg_vals(g, x));
    assert(proj_all(kept, cols).len() == kept.len());
    assert(q.len() == kept.len());
    // every kept row's (key, arguments)
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], gb_keys(), gb_aggs())
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(Seq::<Val>::empty() + kept[i] =~= kept[i]);
        assert(xs.contains(kept[i]));
        let m = choose|m: int| 0 <= m < xs.len() && xs[m] == kept[i];
        assert((g.qual)(proj(xs[m], cols)));
        assert(eval_exprs(db, xs[m], gb_keys()) == Ok::<Row, SqlError>((g.key)(proj(xs[m], cols))));
        assert(agg_args(db, xs[m], gb_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(xs[m], cols))));
        assert(proj(kept[i], cols) == q[i]);
    }
    // the groups are `gkeys`, each with its members
    lemma_pool_exact(g, xs);
    let pool = key_pool(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    let ds = distinct_rows(ks);
    lemma_gkeys(g, xs);
    if gcount(g, xs, k) == 0 {
        lemma_zero_count(g, xs, k, 1);
    }
    assert(ds.contains(k));
    let gi = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k;
    lemma_group_members(g, xs, k, pool);
    // the overflowing SUM
    lemma_members_col(g, xs, k, 1);
    lemma_members_mass(ps, xs, k);
    let vs = column(group_members(ks, args, ds[gi]), 1);
    assert(!fits_agg_value(gb_aggs()[1], vs));
    // every group's aggregates inside their conditions succeed
    assert forall|h: int| 0 <= h < ds.len() implies #[trigger] aggs_ok_inside(gb_aggs(), group_members(ks, args, ds[h])) by {
        assert(pool.contains(ds[h]));
        lemma_group_members(g, xs, ds[h], pool);
        lemma_group_ok_inside(ps, xs, ds[h]);
    }
    lemma_group_by_capacity(db, Seq::empty(), gb_keys(), gb_aggs(), Box::new(where_query(ps)), kept, ks, args, gi, 1);
    reveal(eval_query);
    assert(!fits_query(db, Seq::empty(), gb_query(ps)));
}

} // verus!
