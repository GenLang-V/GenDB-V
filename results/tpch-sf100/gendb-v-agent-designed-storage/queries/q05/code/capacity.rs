//! The Capacity answer: when the absolute revenue mass of some group exceeds `i128::MAX`, the statement's GROUP BY
//! is outside its capacity condition (`lemma_capacity`), by `link::capacity::lemma_group_by_capacity` with the
//! qualifying rows' keys and arguments.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::datetime::*;
use crate::spec::typing::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::schema::schema_spec;
use crate::query::param_domain;
use crate::exec::relational::domain::*;
use crate::link::query::*;
use crate::link::join::*;
use crate::link::capacity::*;
use crate::link::expr::i128_max;
use crate::agent::q5spec::*;
use crate::agent::sqlrow::*;
use crate::agent::sqlink::*;

verus! {

/// The absolute mass of a group's SUM arguments at scale 4 is its absolute accumulator.
pub proof fn lemma_members_mass(g: QuerySpec, xs: Seq<Row>, k: Row)
    requires g.aggs == seq![AggKind::Sum { scale: 4 }],
    ensures num_mass_at(column(members(g, xs, k), 0), 4) == gabs(g, xs, k, 0),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        lemma_members_mass(g, xi, k);
        let vi = column(members(g, xi, k), 0);
        if hit(g, x, k) {
            let v = arg_vals(g, x)[0];
            assert(v == Val::Num { coeff: (g.arg)(0, x), scale: 4 });
            assert(column(members(g, xs, k), 0) =~= vi.push(v));
            assert(vi.push(v).drop_last() =~= vi);
            assert(pow10(0) == 1);
            assert(((4 - 4) as nat) == 0nat);
        } else {
            assert(column(members(g, xs, k), 0) =~= vi);
        }
    }
}

/// Inside its mass condition a group's SUM succeeds.
proof fn lemma_inside_ok(g: QuerySpec, xs: Seq<Row>, k: Row)
    requires g.aggs == seq![AggKind::Sum { scale: 4 }],
    ensures aggs_ok_inside(q5_aggs(), members(g, xs, k)),
{
    assert forall|j: int| 0 <= j < q5_aggs().len() && #[trigger] fits_agg_value(q5_aggs()[j], column(members(g, xs, k), j))
        implies agg_value(q5_aggs()[j], column(members(g, xs, k), j)) is Ok by {
        assert(j == 0);
        lemma_members_col(g, xs, k, 0);
        lemma_sum_inside_ok(NumKind::Numeric, rev_expr(), column(members(g, xs, k), 0));
    }
}

/// A group whose absolute revenue mass exceeds `i128::MAX` puts the statement outside its capacity domain.
pub proof fn lemma_capacity(db: Database, ps: Seq<Literal>, prm: Prm, t0: int, k: Row)
    requires
        db.schema == schema_spec(), db_wf(db),
        param_domain(ps),
        prm == prm_of(ps, prm.hi),
        date_to_ts(prm.lo) == Ok::<int, SqlError>(t0),
        ts_add_interval(t0, 12, 0, 0) == Ok::<int, SqlError>(prm.hi),
        gabs(q5_g(prm), xs_of(rels_of_db(db)), k, 0) > i128_max(),
    ensures !fits_query(db, Seq::empty(), q5_body(ps)),
{
    let g = q5_g(prm);
    let rows = full_rows(db);
    let cols = q5_cols();
    let xs = proj_all(rows, cols);
    let ctx = Seq::<Val>::empty();
    assert(db.tables.len() == 8) by {
        assert(schema_spec().len() == 8) by (compute);
    }
    lemma_from_eval(db);
    lemma_xs(db);
    lemma_rows_typed(db);
    lemma_pred_agrees(db, ps, prm, t0);
    lemma_group_agrees(db, prm);
    lemma_filter_rows(db, q5_from(), rows, cols, q5_pred(ps), g);
    let kept = keep_true(rows, qual_truths(g, xs));
    lemma_kept_rows(g, rows, cols);
    // the GROUP BY inputs of the kept rows
    let ks = Seq::new(kept.len(), |i: int| (g.key)(proj(kept[i], cols)));
    let args = Seq::new(kept.len(), |i: int| arg_vals(g, proj(kept[i], cols)));
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, ctx + kept[i], q5_key_exprs(), q5_aggs())
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(ctx + kept[i] =~= kept[i]);
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(full_shape(rows[m]));
        lemma_key_row(db, kept[i]);
        lemma_arg_row(db, kept[i]);
        let y = proj(kept[i], cols);
        assert(arg_vals(g, y) =~= seq![Val::Num { coeff: q5_arg(y), scale: 4 }]);
    }
    assert(ks =~= qkeys(g, xs)) by {
        assert forall|i: int| 0 <= i < ks.len() implies ks[i] == qkeys(g, xs)[i] by {
            assert(proj(kept[i], cols) == qrows(g, xs)[i]);
        }
    }
    assert(args =~= qrows(g, xs).map_values(|x: Row| arg_vals(g, x))) by {
        assert forall|i: int| 0 <= i < args.len() implies args[i] == qrows(g, xs).map_values(|x: Row| arg_vals(g, x))[i] by {
            assert(proj(kept[i], cols) == qrows(g, xs)[i]);
        }
    }
    // the groups are the normal form's groups
    lemma_pool_exact(g, xs);
    let pool = key_pool(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    let ds = gkeys(g, xs);
    assert(distinct_rows(ks) == ds);
    // group k has a row, so it is one of the groups
    if gcount(g, xs, k) == 0 {
        lemma_zero_count(g, xs, k, 0);
    }
    lemma_gkeys(g, xs);
    assert(ds.contains(k));
    let gidx = choose|i: int| 0 <= i < ds.len() && ds[i] == k;
    assert(pool.contains(k)) by {
        assert(ds.contains(ds[gidx]));
    }
    assert forall|h: int| 0 <= h < ds.len() implies #[trigger] aggs_ok_inside(q5_aggs(), group_members(ks, args, distinct_rows(ks)[h])) by {
        assert(pool.contains(ds[h]));
        lemma_group_members(g, xs, ds[h], pool);
        lemma_inside_ok(g, xs, ds[h]);
    }
    // its SUM is outside the mass condition
    lemma_group_members(g, xs, k, pool);
    let vs = column(members(g, xs, k), 0);
    lemma_members_col(g, xs, k, 0);
    lemma_members_mass(g, xs, k);
    assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i] matches Val::Num { coeff, scale } ==> scale == 4) by {
        lemma_vs_scale(g, xs, k, i);
    }
    lemma_num_mass_uniform(vs, 4);
    lemma_count_witness_num(g, xs, k);
    assert(num_max_scale(vs) == 4);
    assert(!fits_agg_value(q5_aggs()[0], column(group_members(ks, args, distinct_rows(ks)[gidx]), 0)));
    lemma_group_by_capacity(db, ctx, q5_key_exprs(), q5_aggs(), Box::new(q5_filter(ps)), kept, ks, args, gidx, 0);
}

/// Every argument value of a group is numeric at scale 4.
proof fn lemma_vs_scale(g: QuerySpec, xs: Seq<Row>, k: Row, i: int)
    requires g.aggs == seq![AggKind::Sum { scale: 4 }], 0 <= i < column(members(g, xs, k), 0).len(),
    ensures column(members(g, xs, k), 0)[i] matches Val::Num { coeff, scale } ==> scale == 4,
    decreases xs.len(),
{
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let vi = column(members(g, xi, k), 0);
        if hit(g, xs.last(), k) {
            assert(column(members(g, xs, k), 0) =~= vi.push(arg_vals(g, xs.last())[0]));
            if i < vi.len() {
                lemma_vs_scale(g, xi, k, i);
            }
        } else {
            assert(column(members(g, xs, k), 0) =~= vi);
            lemma_vs_scale(g, xi, k, i);
        }
    }
}

/// A group with a row has a numeric argument value.
proof fn lemma_count_witness_num(g: QuerySpec, xs: Seq<Row>, k: Row)
    requires g.aggs == seq![AggKind::Sum { scale: 4 }], gcount(g, xs, k) > 0,
    ensures exists|i: int| 0 <= i < column(members(g, xs, k), 0).len() && #[trigger] column(members(g, xs, k), 0)[i] is Num,
    decreases xs.len(),
{
    let xi = xs.drop_last();
    let vi = column(members(g, xi, k), 0);
    if hit(g, xs.last(), k) {
        let vs = column(members(g, xs, k), 0);
        assert(vs =~= vi.push(arg_vals(g, xs.last())[0]));
        assert(vs[vi.len() as int] is Num);
    } else {
        assert(column(members(g, xs, k), 0) =~= vi);
        lemma_count_witness_num(g, xi, k);
    }
}

} // verus!
