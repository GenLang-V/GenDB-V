//! The `Capacity` answer: when the absolute mass of some group's SUM argument passes `i128::MAX` (the SUM capacity
//! condition of `exec::relational::domain`), the statement's body is outside `fits_query` (`lemma_capacity`). The
//! GROUP BY's groups are the normal form's (`gkeys`, by exact keys) and each group's members are the normal form's
//! `members`, whose argument column has mass `gabs` at scale 4 (`lemma_members_mass`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::numeric::*;
use crate::spec::limits::*;
use crate::exec::relational::domain::*;
use crate::link::query::*;
use crate::link::capacity::*;
use crate::query::query_spec_at;
use super::sqlq::*;
use super::body::*;

verus! {

/// Every row qualifies: the normal form's qualifying rows are the rows.
proof fn lemma_qrows_all(xs: Seq<Row>)
    ensures qrows(g7(), xs) == xs,
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_qrows_all(xs.drop_last());
        assert(xs.drop_last().push(xs.last()) =~= xs);
    }
}

/// The argument column of group `k`'s members: every value is a scale-4 numeric, of mass `gabs` at scale 4.
proof fn lemma_members_mass(xs: Seq<Row>, k: Row)
    requires forall|i: int| 0 <= i < xs.len() ==> ship_row(#[trigger] xs[i]),
    ensures ({
        let vs = column(members(g7(), xs, k), 0);
        &&& num_max_scale(vs) == if gcount(g7(), xs, k) == 0 { 0nat } else { 4nat }
        &&& num_mass_at(vs, 4) == gabs(g7(), xs, k, 0)
    }),
    decreases xs.len(),
{
    let g = g7();
    let vs = column(members(g, xs, k), 0);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        assert forall|i: int| 0 <= i < xi.len() implies ship_row(#[trigger] xi[i]) by {
            assert(xi[i] == xs[i]);
        }
        lemma_members_mass(xi, k);
        let vsi = column(members(g, xi, k), 0);
        if hit(g, x, k) {
            assert(vs =~= vsi.push(arg_vals(g, x)[0]));
            assert(vs.drop_last() =~= vsi);
            assert(arg_vals(g, x)[0] == Val::Num { coeff: (g.arg)(0, x), scale: 4 });
            assert(pow10(0) == 1);
            assert(abs((g.arg)(0, x)) * pow10(0) == abs((g.arg)(0, x)));
        } else {
            assert(vs =~= vsi);
        }
    } else {
        assert(vs =~= Seq::<Val>::empty());
    }
}

/// A group of `shipping` whose absolute SUM mass passes `i128::MAX` puts the statement outside the capacity domain.
pub proof fn lemma_capacity(db: Database, ps: Seq<Literal>, k: Row)
    requires
        tables_typed(db),
        texts(ps),
        gabs(g7(), ship(db, ps), k, 0) > i128::MAX,
    ensures !fits_query(db, Seq::empty(), query_spec_at(ps).body),
{
    hide(eval_query);
    hide(eval_exprs);
    hide(agg_args);
    let g = g7();
    let xs = ship(db, ps);
    let keys = group_keys();
    let aggs = group_aggs();
    lemma_statement(ps);
    lemma_eval_shipping(db, ps);
    lemma_ship_rows(db, ps);
    lemma_ship_exact(db, ps);
    lemma_qrows_all(xs);
    let ks = qkeys(g, xs);
    let avs = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + xs[i], keys, aggs)
        == Ok::<(Row, Row), SqlError>((ks[i], avs[i])) by {
        assert(Seq::<Val>::empty() + xs[i] =~= xs[i]);
        lemma_ship_eval(db, ps, i);
    }
    // groups: exact keys make the GROUP BY's groups the normal form's
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    let ds = gkeys(g, xs);
    lemma_gkeys(g, xs);
    // the overflowing group is one of them
    if gcount(g, xs, k) == 0 {
        lemma_zero_count(g, xs, k, 0);
    }
    assert(ds.contains(k));
    let gi = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k;
    assert(pool.contains(k));
    lemma_group_members(g, xs, k, pool);
    lemma_members_col(g, xs, k, 0);
    lemma_members_mass(xs, k);
    let vs = column(members(g, xs, k), 0);
    assert(sum_mass(NumKind::Numeric, vs) > i128::MAX);
    assert(!fits_agg_value(aggs[0], column(group_members(ks, avs, distinct_rows(ks)[gi]), 0)));
    // every group's SUM succeeds inside its capacity condition
    assert forall|h: int| 0 <= h < distinct_rows(ks).len() implies #[trigger] aggs_ok_inside(aggs, group_members(ks, avs, distinct_rows(ks)[h])) by {
        let kh = ds[h];
        assert(pool.contains(kh));
        lemma_group_members(g, xs, kh, pool);
        lemma_members_col(g, xs, kh, 0);
        let vh = column(members(g, xs, kh), 0);
        assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(group_members(ks, avs, distinct_rows(ks)[h]), j))
            implies agg_value(aggs[j], column(group_members(ks, avs, distinct_rows(ks)[h]), j)) is Ok by {
            assert(j == 0);
            lemma_sum_inside_ok(NumKind::Numeric, Expr::Col(3), vh);
        }
    }
    lemma_group_by_capacity(db, Seq::empty(), keys, aggs, Box::new(shipping_q(ps)), xs, ks, avs, gi, 0);
}

} // verus!
