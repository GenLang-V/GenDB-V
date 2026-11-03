//! One group's aggregate values in SQL terms (`agg_value_results` / `agg_value_fs` of the GROUP BY members):
//! COUNT(*) is the group's count, COUNT(DISTINCT adsh) the number of its distinct adsh values, and AVG(line) is
//! inside its domain exactly when the division of the exact line sum by the count is (`num_div_fits`), and then
//! it is `avg_of(sum, 0, count)`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::aggs::avg::*;
use crate::spec::fns::div::*;
use crate::exec::relational::domain::*;
use crate::exec::aggs::avg::fits_avg_value;
use crate::link::query::*;
use crate::bridge::equality::same_exact_type;
use super::canon::*;
use super::common::distinct::*;

verus! {

/// A group's count is at most the number of rows.
pub proof fn lemma_gcount_le(xs: Seq<Row>, k: Row)
    ensures gcount(gq(), xs, k) <= xs.len(),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_gcount_le(xs.drop_last(), k);
    }
}

/// The aggregate values of group `k` (a group of the GROUP BY, so its count is positive), given the
/// duplicate-free list `d` of its adsh values.
pub proof fn lemma_group_values(xs: Seq<Row>, k: Row, d: Seq<Val>)
    requires
        rows_typed(xs),
        xs.len() <= 0x1_0000_0000_0000_0000,
        gkeys(gq(), xs).contains(k),
        d.no_duplicates(),
        forall|v: Val| #[trigger] d.contains(v) <==> has_adsh(xs, k, v),
    ensures ({
        let m = members_of(xs, k);
        let c = gcount(gq(), xs, k);
        let sm = gsum(gq(), xs, k, 0);
        let vr = agg_value_results(q_aggs(), m);
        let vf = agg_value_fs(q_aggs(), m);
        &&& c > 0
        &&& vr.len() == 3 && vf.len() == 3
        &&& vr[0] == int_result(IntKind::Int8, c as int) && vf[0]
        &&& vr[1] == int_result(IntKind::Int8, d.len() as int) && vf[1]
        &&& vf[2] == num_div_fits(sm, 0, c as int, 0)
        &&& vf[2] ==> vr[2] == Ok::<Val, SqlError>(avg_of(sm, 0, c))
    }),
{
    let g = gq();
    let m = members_of(xs, k);
    let c = gcount(g, xs, k);
    let sm = gsum(g, xs, k, 0);
    let aggs = q_aggs();
    let vr = agg_value_results(aggs, m);
    let vf = agg_value_fs(aggs, m);
    lemma_gkeys(g, xs);
    lemma_members(xs, k);
    lemma_gcount_le(xs, k);
    let ad = column(m, 1);
    let ln = column(m, 2);
    let inner = Agg::Count(Expr::Col(0));
    let a2 = Agg::Avg { kind: NumKind::Int4, arg: Expr::Col(2) };
    assert(aggs[0] == Agg::CountStar && aggs[1] == Agg::DistinctAgg(Box::new(inner)) && aggs[2] == a2);
    // COUNT(*)
    assert(vr[0] == agg_value(Agg::CountStar, column(m, 0)));
    assert(vf[0]);
    // COUNT(DISTINCT adsh): the distinct values are the adsh values, as many as `d` has.
    assert(exact_vals(ad)) by {
        assert forall|i: int, j: int| 0 <= i < ad.len() && 0 <= j < ad.len() implies same_exact_type(#[trigger] ad[i], #[trigger] ad[j]) by {
            assert(ad[i] is Text && ad[j] is Text);
        }
    }
    lemma_count_distinct(ad);
    assert(ad.to_set() =~= d.to_set()) by {
        ad.to_set_ensures();
        d.to_set_ensures();
    }
    d.unique_seq_to_set();
    assert(vr[1] == agg_value(Agg::DistinctAgg(Box::new(inner)), ad));
    assert(agg_value(Agg::DistinctAgg(Box::new(inner)), ad) == agg_value(inner, distinct_vals(ad)));
    assert(fits_agg_value(inner, distinct_vals(ad)));
    assert(vf[1] == fits_agg_value(Agg::DistinctAgg(Box::new(inner)), ad));
    // AVG(line): an int4 average; its sum mass is at most 2^31 per row.
    assert(vr[2] == avg_value(NumKind::Int4, ln));
    assert(vf[2] == fits_avg_value(NumKind::Int4, ln));
    assert(int_mass(ln) <= i128::MAX as int) by {
        assert(0x8000_0000 * c <= 0x8000_0000 * 0x1_0000_0000_0000_0000int) by (nonlinear_arith)
            requires c <= 0x1_0000_0000_0000_0000int;
    }
    assert(avg_sum(NumKind::Int4, ln) == (sm, 0nat));
    if vf[2] {
        lemma_avg_ok(sm, 0, c as int);
        assert(vr[2] == Ok::<Val, SqlError>(avg_of(sm, 0, c)));
    }
    assert(c > 0);
    assert(vr.len() == 3 && vf.len() == 3);
    assert(vr[0] == int_result(IntKind::Int8, c as int));
    assert(vr[1] == int_result(IntKind::Int8, d.len() as int));
    assert(vf[1]);
    assert(vf[2] == num_div_fits(sm, 0, c as int, 0));
}

} // verus!
