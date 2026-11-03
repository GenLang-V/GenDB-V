//! Exact non-row outcomes of a GROUP BY in the accumulator normal form (`link::query::QuerySpec`): a group whose
//! COUNT exceeds int8 makes the node the SQL error 22003, and otherwise a group whose SUM/AVG absolute mass exceeds
//! `i128` (or whose AVG division leaves the executable domain) puts the node outside `fits_query`.
//!
//! Both hold for any statement in the normal form (any keys, Sum/Avg/Count aggregates of numeric arguments, any
//! row order), under the per-row agreement premises of `link::query::lemma_group_query`. They do not depend on the
//! order of the groups: every aggregate of the normal form either succeeds or fails with 22003, and inside its
//! capacity condition succeeds (`link::capacity`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::limits::*;
use crate::spec::equality::*;
use crate::spec::fns::div::*;
use crate::spec::aggs::avg::*;
use crate::link::query::*;
use crate::link::capacity::*;
use crate::link::expr::i128_max;
use crate::exec::relational::domain::*;
use crate::exec::relational::aggregate::lemma_num_mass_nonneg;
use crate::exec::aggs::avg::fits_avg_value;

verus! {

/// The static scale of a SUM/AVG aggregate kind (0 for COUNT).
pub open spec fn kind_scale(k: AggKind) -> nat {
    match k {
        AggKind::Sum { scale } => scale,
        AggKind::Avg { scale } => scale,
        AggKind::Count => 0,
    }
}

/// The absolute mass of a SUM/AVG member column at its static scale is the normal form's `gabs`.
pub proof fn lemma_members_mass(g: QuerySpec, xs: Seq<Row>, k: Row, j: int)
    requires 0 <= j < g.aggs.len(), !(g.aggs[j] is Count),
    ensures num_mass_at(column(members(g, xs, k), j), kind_scale(g.aggs[j])) == gabs(g, xs, k, j),
    decreases xs.len(),
{
    let s = kind_scale(g.aggs[j]);
    let vs = column(members(g, xs, k), j);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        lemma_members_mass(g, xi, k, j);
        let vsi = column(members(g, xi, k), j);
        if hit(g, x, k) {
            assert(vs =~= vsi.push(arg_vals(g, x)[j]));
            assert(vs.drop_last() =~= vsi);
            assert(arg_vals(g, x)[j] == (Val::Num { coeff: (g.arg)(j, x), scale: s }));
            assert((s - s) as nat == 0nat);
            assert(pow10(0) == 1);
            assert(abs((g.arg)(j, x)) * pow10((s - s) as nat) == abs((g.arg)(j, x)));
        } else {
            assert(vs =~= vsi);
        }
    } else {
        assert(vs =~= Seq::<Val>::empty());
    }
}

/// The SQL premises shared by both outcomes: the input evaluates to the qualifying rows, and keys and arguments
/// agree per row (as `lemma_group_query` takes them).
pub open spec fn group_premises(db: Database, rows: Seq<Row>, cols: Seq<nat>, input: Query, keys: Seq<Expr>,
    aggs: Seq<Agg>, g: QuerySpec) -> bool
{
    &&& eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(g, proj_all(rows, cols))))
    &&& keys_agree(db, rows, cols, keys, g)
    &&& args_agree(db, rows, cols, aggs, g)
    &&& aggs_match(aggs, g)
    &&& keys_exact(g, proj_all(rows, cols))
}

/// Under the premises, the GROUP BY's per-row inputs are the qualifying rows' keys and arguments, its groups are
/// `gkeys` and each group's members are `members`.
pub proof fn lemma_group_inputs(db: Database, rows: Seq<Row>, cols: Seq<nat>, input: Query, keys: Seq<Expr>,
    aggs: Seq<Agg>, g: QuerySpec)
    requires group_premises(db, rows, cols, input, keys, aggs, g),
    ensures ({
        let xs = proj_all(rows, cols);
        let kept = keep_true(rows, qual_truths(g, xs));
        let ks = qkeys(g, xs);
        let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
        &&& ks.len() == kept.len()
        &&& args.len() == kept.len()
        &&& forall|i: int| 0 <= i < kept.len() ==> #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], keys, aggs)
                == Ok::<(Row, Row), SqlError>((ks[i], args[i]))
        &&& distinct_rows(ks) == gkeys(g, xs)
        &&& forall|k: Row| gkeys(g, xs).contains(k) ==> #[trigger] group_members(ks, args, k) == members(g, xs, k)
    }),
{
    let xs = proj_all(rows, cols);
    let kept = keep_true(rows, qual_truths(g, xs));
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    let ctx = Seq::<Val>::empty();
    lemma_kept_rows(g, rows, cols);
    assert(kept.len() == qrows(g, xs).len());
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, ctx + kept[i], keys, aggs)
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(ctx + kept[i] =~= kept[i]);
        assert(rows.contains(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert((g.qual)(proj(rows[m], cols)));
        assert(proj(kept[i], cols) == qrows(g, xs)[i]);
        assert(eval_exprs(db, rows[m], keys) == Ok::<Row, SqlError>((g.key)(proj(rows[m], cols))));
        assert(agg_args(db, rows[m], aggs) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[m], cols))));
    }
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    assert forall|k: Row| gkeys(g, xs).contains(k) implies #[trigger] group_members(ks, args, k) == members(g, xs, k) by {
        let i = choose|i: int| 0 <= i < gkeys(g, xs).len() && gkeys(g, xs)[i] == k;
        assert(pool.contains(gkeys(g, xs)[i]));
        lemma_group_members(g, xs, k, pool);
    }
}

/// Every aggregate value of a non-empty group of the normal form succeeds or fails with 22003.
pub proof fn lemma_agg_ok_or_range(aggs: Seq<Agg>, g: QuerySpec, xs: Seq<Row>, k: Row, j: int)
    requires aggs_match(aggs, g), 0 <= j < aggs.len(), gcount(g, xs, k) > 0,
    ensures ({
        let v = agg_value(aggs[j], column(members(g, xs, k), j));
        v is Ok || v == Err::<Val, SqlError>(SqlError::NumericValueOutOfRange)
    }),
{
    let vs = column(members(g, xs, k), j);
    let n = gcount(g, xs, k);
    lemma_members_col(g, xs, k, j);
    assert(agg_matches(aggs[j], g.aggs[j]));
    match g.aggs[j] {
        AggKind::Count => {
            lemma_count_value(aggs[j], vs);
        },
        AggKind::Sum { scale } => {},
        AggKind::Avg { scale } => {
            assert(count_non_null(vs) as int == n);
            assert(n != 0);
        },
    }
}

/// A group whose COUNT exceeds int8: the GROUP BY is the SQL error 22003 (whatever the group order).
pub proof fn lemma_group_count_err(db: Database, rows: Seq<Row>, cols: Seq<nat>, input: Query, keys: Seq<Expr>,
    aggs: Seq<Agg>, g: QuerySpec, k: Row, j: int)
    requires
        group_premises(db, rows, cols, input, keys, aggs, g),
        0 <= j < g.aggs.len(),
        g.aggs[j] is Count,
        gcount(g, proj_all(rows, cols), k) > int8_max(),
    ensures
        eval_query(db, Seq::empty(), Query::GroupBy { keys, aggs, input: Box::new(input) })
            == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    let xs = proj_all(rows, cols);
    let kept = keep_true(rows, qual_truths(g, xs));
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    let e = SqlError::NumericValueOutOfRange;
    lemma_group_inputs(db, rows, cols, input, keys, aggs, g);
    lemma_gkeys(g, xs);
    let ds = distinct_rows(ks);
    assert(ds.contains(k));
    let gi = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k;
    assert(group_members(ks, args, ds[gi]) == members(g, xs, k));
    lemma_members_col(g, xs, k, j);
    assert(agg_matches(aggs[j], g.aggs[j]));
    lemma_count_value(aggs[j], column(members(g, xs, k), j));
    assert forall|h: int, kk: int| 0 <= h < ds.len() && 0 <= kk < aggs.len() implies
        #[trigger] agg_value(aggs[kk], column(group_members(ks, args, ds[h]), kk)) is Ok
            || agg_value(aggs[kk], column(group_members(ks, args, ds[h]), kk)) == Err::<Val, SqlError>(e) by {
        assert(ds.contains(ds[h]));
        assert(group_members(ks, args, ds[h]) == members(g, xs, ds[h]));
        lemma_agg_ok_or_range(aggs, g, xs, ds[h], kk);
    }
    lemma_group_by_err(db, Seq::empty(), keys, aggs, Box::new(input), kept, ks, args, e, gi, j);
}

/// Inside every group's COUNT range, the aggregates inside their capacity conditions succeed.
pub proof fn lemma_aggs_ok_inside(aggs: Seq<Agg>, g: QuerySpec, xs: Seq<Row>, k: Row)
    requires aggs_match(aggs, g), gcount(g, xs, k) <= int8_max(),
    ensures aggs_ok_inside(aggs, members(g, xs, k)),
{
    let m = members(g, xs, k);
    assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(m, j))
        implies agg_value(aggs[j], column(m, j)) is Ok by {
        let vs = column(m, j);
        lemma_members_col(g, xs, k, j);
        assert(agg_matches(aggs[j], g.aggs[j]));
        match g.aggs[j] {
            AggKind::Count => {
                lemma_count_value(aggs[j], vs);
            },
            AggKind::Sum { scale } => {
                lemma_sum_inside_ok(NumKind::Numeric, aggs[j]->Sum_arg, vs);
            },
            AggKind::Avg { scale } => {
                lemma_avg_inside_ok(NumKind::Numeric, aggs[j]->Avg_arg, vs);
            },
        }
    }
}

/// The capacity violation of one non-COUNT aggregate of a non-empty group: its absolute mass exceeds `i128`, or
/// (AVG) its division leaves the executable domain.
pub open spec fn agg_over(g: QuerySpec, xs: Seq<Row>, k: Row, j: int) -> bool {
    gabs(g, xs, k, j) > i128_max()
        || (g.aggs[j] is Avg && !num_div_fits(gsum(g, xs, k, j), kind_scale(g.aggs[j]), gcount(g, xs, k) as int, 0))
}

/// A violating aggregate is outside its capacity condition.
pub proof fn lemma_agg_over_unfit(aggs: Seq<Agg>, g: QuerySpec, xs: Seq<Row>, k: Row, j: int)
    requires aggs_match(aggs, g), 0 <= j < aggs.len(), !(g.aggs[j] is Count), gcount(g, xs, k) > 0, agg_over(g, xs, k, j),
    ensures !fits_agg_value(aggs[j], column(members(g, xs, k), j)),
{
    let vs = column(members(g, xs, k), j);
    let s = kind_scale(g.aggs[j]);
    lemma_members_col(g, xs, k, j);
    lemma_members_mass(g, xs, k, j);
    assert(agg_matches(aggs[j], g.aggs[j]));
    // every member value is numeric at scale s, and there is one
    assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i] matches Val::Num { coeff, scale } ==> scale == s) by {
        lemma_members_scale(g, xs, k, j, i);
    }
    assert(vs.len() > 0);
    lemma_members_scale(g, xs, k, j, 0);
    assert(vs[0] is Num);
    lemma_num_mass_uniform(vs, s);
    assert(num_max_scale(vs) == s);
}

/// Every member value of a SUM/AVG aggregate is the numeric argument at the static scale.
pub proof fn lemma_members_scale(g: QuerySpec, xs: Seq<Row>, k: Row, j: int, i: int)
    requires 0 <= j < g.aggs.len(), !(g.aggs[j] is Count), 0 <= i < column(members(g, xs, k), j).len(),
    ensures column(members(g, xs, k), j)[i] is Num && column(members(g, xs, k), j)[i]->Num_scale == kind_scale(g.aggs[j]),
    decreases xs.len(),
{
    let vs = column(members(g, xs, k), j);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        let vsi = column(members(g, xi, k), j);
        if hit(g, x, k) {
            assert(vs =~= vsi.push(arg_vals(g, x)[j]));
            if i < vsi.len() {
                lemma_members_scale(g, xi, k, j, i);
            }
        } else {
            assert(vs =~= vsi);
            lemma_members_scale(g, xi, k, j, i);
        }
    } else {
        assert(vs =~= Seq::<Val>::empty());
    }
}

/// Every COUNT in int8 and some non-empty group's aggregate violating its capacity condition: the GROUP BY is
/// outside `fits_query` (whatever the group order).
pub proof fn lemma_group_capacity(db: Database, rows: Seq<Row>, cols: Seq<nat>, input: Query, keys: Seq<Expr>,
    aggs: Seq<Agg>, g: QuerySpec, k: Row, j: int)
    requires
        group_premises(db, rows, cols, input, keys, aggs, g),
        forall|k2: Row| #[trigger] gcount(g, proj_all(rows, cols), k2) <= int8_max(),
        0 <= j < g.aggs.len(),
        !(g.aggs[j] is Count),
        gcount(g, proj_all(rows, cols), k) > 0,
        agg_over(g, proj_all(rows, cols), k, j),
    ensures
        !fits_query(db, Seq::empty(), Query::GroupBy { keys, aggs, input: Box::new(input) }),
{
    let xs = proj_all(rows, cols);
    let kept = keep_true(rows, qual_truths(g, xs));
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    lemma_group_inputs(db, rows, cols, input, keys, aggs, g);
    lemma_gkeys(g, xs);
    let ds = distinct_rows(ks);
    assert(ds.contains(k));
    let gi = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k;
    assert(group_members(ks, args, ds[gi]) == members(g, xs, k));
    lemma_agg_over_unfit(aggs, g, xs, k, j);
    assert forall|h: int| 0 <= h < ds.len() implies #[trigger] aggs_ok_inside(aggs, group_members(ks, args, ds[h])) by {
        assert(ds.contains(ds[h]));
        assert(group_members(ks, args, ds[h]) == members(g, xs, ds[h]));
        lemma_aggs_ok_inside(aggs, g, xs, ds[h]);
    }
    lemma_group_by_capacity(db, Seq::empty(), keys, aggs, Box::new(input), kept, ks, args, gi, j);
}

} // verus!
