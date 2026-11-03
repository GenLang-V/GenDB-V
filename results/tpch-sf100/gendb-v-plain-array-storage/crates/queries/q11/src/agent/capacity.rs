//! The statement outside the capacity domain (`!fits_query(db, [], body)`) when some row qualifies and an exact
//! intermediate leaves `i128`:
//! - a group's absolute mass (`lemma_cap_group`: the GROUP BY's SUM, whatever the group order);
//! - every group fits but the total absolute mass does not (`lemma_cap_total`: the subquery's SUM, reached by the
//!   HAVING condition of the first group row);
//! - both masses fit but `total * $2` does not (`lemma_cap_scaled`: the subquery's projection).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::{row_not_distinct, distinct_rows};
use crate::exec::domain::{fits_expr, fits_exprs, arith_fits, num_arith_fits};
use crate::exec::relational::domain::*;
use crate::link::capacity::*;
use crate::link::expr::{ival, i128_max};
use crate::link::query::*;
use crate::exec::relational::aggregate::lemma_num_mass_nonneg;
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem::*;
use crate::agent::normal::*;
use crate::agent::body::*;

verus! {

/// The absolute mass of a group's SUM arguments at scale 2 is the normal form's `gabs` (arguments at scale 2).
pub proof fn lemma_members_mass(g: QuerySpec, xs: Seq<Row>, k: Row)
    requires g.aggs.len() == 1, g.aggs[0] == (AggKind::Sum { scale: 2 }),
    ensures
        num_mass_at(column(members(g, xs, k), 0), 2) == gabs(g, xs, k, 0),
        num_max_scale(column(members(g, xs, k), 0)) == if gcount(g, xs, k) > 0 { 2nat } else { 0nat },
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
            assert(arg_vals(g, x)[0] == Val::Num { coeff: (g.arg)(0, x), scale: 2 });
            assert(pow10(0) == 1);
            assert((2 - 2) as nat == 0nat);
        } else {
            assert(vs =~= vsi);
        }
    } else {
        assert(vs =~= Seq::<Val>::empty());
    }
}

/// The SUM of a group's arguments: inside its capacity condition exactly when the group's mass is.
pub proof fn lemma_members_fits(g: QuerySpec, xs: Seq<Row>, k: Row, arg: Expr)
    requires g.aggs.len() == 1, g.aggs[0] == (AggKind::Sum { scale: 2 }), gcount(g, xs, k) > 0,
    ensures
        fits_agg_value(Agg::Sum { kind: NumKind::Numeric, arg }, column(members(g, xs, k), 0)) == (gabs(g, xs, k, 0) <= i128::MAX as int),
        aggs_ok_inside(seq![Agg::Sum { kind: NumKind::Numeric, arg }], members(g, xs, k)),
{
    let vs = column(members(g, xs, k), 0);
    lemma_members_mass(g, xs, k);
    lemma_members_col(g, xs, k, 0);
    let a = Agg::Sum { kind: NumKind::Numeric, arg };
    let aggs = seq![a];
    assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(members(g, xs, k), j))
        implies agg_value(aggs[j], column(members(g, xs, k), j)) is Ok by {
        lemma_sum_inside_ok(NumKind::Numeric, arg, vs);
    }
}

/// A key with a positive absolute mass is a group key.
proof fn lemma_gabs_pos(g: QuerySpec, xs: Seq<Row>, k: Row)
    requires gabs(g, xs, k, 0) > 0,
    ensures gcount(g, xs, k) > 0,
{
    if gcount(g, xs, k) == 0 {
        lemma_zero_count(g, xs, k, 0);
    }
}

// ------------------------------------------------------------------------------------------ a group's mass

/// Some group's absolute mass leaves `i128`: the GROUP BY is outside its capacity domain, so is the body.
pub proof fn lemma_cap_group(db: Database, sv: StoresView, p: Seq<u8>, c2: int, k: Row)
    requires
        tables_of(sv, db), stores_wf(sv), bounds_ok(sv),
        gabs(gq(p), from_rows(sv), k, 0) > i128::MAX as int,
    ensures !fits_query(db, Seq::empty(), body(params_of(p, c2))),
{
    let ps = params_of(p, c2);
    let xs = from_rows(sv);
    let g = gq(p);
    let e = Seq::<Val>::empty();
    let kp = kept(sv, p);
    let keys = seq![Expr::Col(0)];
    let aggs = seq![sum_agg(0)];
    let input = Box::new(filtered(0, Literal::Text(p)));
    lemma_filter_eval(db, sv, p, e);
    lemma_kept(sv, p);
    let ks = qkeys(g, xs);
    let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    assert forall|i: int| 0 <= i < kp.len() implies #[trigger] group_input(db, e + kp[i], keys, aggs)
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        lemma_arg_row(db, sv, p, e, kp[i]);
    }
    // the group of `k` among the distinct keys
    lemma_gabs_pos(g, xs, k);
    lemma_gkeys(g, xs);
    let pool = key_pool(g, xs);
    lemma_from_wf(sv);
    lemma_keys_exact_pub(sv, p);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    let ds = gkeys(g, xs);
    assert(ds.contains(k));
    let gi = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == k;
    lemma_group_members(g, xs, k, pool);
    lemma_members_fits(g, xs, k, arg_expr(0));
    assert forall|h: int| 0 <= h < distinct_rows(ks).len()
        implies #[trigger] aggs_ok_inside(aggs, group_members(ks, args, distinct_rows(ks)[h])) by {
        let kh = ds[h];
        assert(ds.contains(kh));
        lemma_group_members(g, xs, kh, pool);
        lemma_members_fits(g, xs, kh, arg_expr(0));
    }
    lemma_group_by_capacity(db, e, keys, aggs, input, kp, ks, args, gi, 0);
    lemma_first_input(db, e, body(ps));
}

/// The grouped block's keys are exact (re-export for the capacity proofs).
pub proof fn lemma_keys_exact_pub(sv: StoresView, p: Seq<u8>)
    requires stores_wf(sv),
    ensures keys_exact(gq(p), from_rows(sv)),
{
    let r = from_rows(sv);
    assert forall|a: int, b: int| 0 <= a < r.len() && 0 <= b < r.len() && (gq(p).qual)(r[a]) && (gq(p).qual)(r[b])
        implies (row_not_distinct(#[trigger] (gq(p).key)(r[a]), #[trigger] (gq(p).key)(r[b])) <==> (gq(p).key)(r[a]) == (gq(p).key)(r[b])) by {
        let (a1, b1, d1) = lemma_from_elem(sv, a);
        let (a2, b2, d2) = lemma_from_elem(sv, b);
        lemma_row3(sv, a1, b1, d1);
        lemma_row3(sv, a2, b2, d2);
        lemma_row_exact((gq(p).key)(r[a]), (gq(p).key)(r[b]));
    }
}

// ------------------------------------------------------------------------------------------ the HAVING subquery

/// A HAVING condition whose subquery is outside its capacity domain under the group row is outside its domain.
proof fn lemma_having_unfit(db: Database, ps: Seq<Literal>, row: Row)
    requires row.len() == 2, !fits_query(db, row, sub_query(ps)),
    ensures !fits_pred(db, Seq::<Val>::empty() + row, having(ps)),
{
    let env = Seq::<Val>::empty() + row;
    assert(env =~= row);
    assert(eval_expr(db, env, Expr::Col(1)) is Ok);
    assert(!fits_expr(db, env, Expr::Subquery(Box::new(sub_query(ps)))));
}

/// Some qualifying row: the group rows are not empty; each has two values.
proof fn lemma_groups_exist(sv: StoresView, p: Seq<u8>)
    requires stores_wf(sv), gcount(sq(p), from_rows(sv), Seq::empty()) > 0,
    ensures
        group_rows_of(sv, p).len() > 0,
        forall|i: int| 0 <= i < group_rows_of(sv, p).len() ==> (#[trigger] group_rows_of(sv, p)[i]).len() == 2,
{
    let xs = from_rows(sv);
    let e = Seq::<Val>::empty();
    let gr = group_rows_of(sv, p);
    lemma_count_witness(sq(p), xs, e);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(sq(p), xs[m], e);
    assert(hit(gq(p), xs[m], (gq(p).key)(xs[m])));
    lemma_hit_count(gq(p), xs, m);
    lemma_gkeys(gq(p), xs);
    assert(gkeys(gq(p), xs).contains((gq(p).key)(xs[m])));
    assert forall|i: int| 0 <= i < gr.len() implies (#[trigger] gr[i]).len() == 2 by {
        let k = gkeys(gq(p), xs)[i];
        assert(gkeys(gq(p), xs).contains(k));
        lemma_group_row(sv, p, k);
    }
}

/// The subquery is outside its capacity domain under every group row: so is the body (its HAVING reaches the first
/// group row, which exists).
proof fn lemma_cap_having(db: Database, sv: StoresView, p: Seq<u8>, c2: int)
    requires
        tables_of(sv, db), stores_wf(sv), bounds_ok(sv),
        group_caps(gq(p), from_rows(sv)),
        gcount(sq(p), from_rows(sv), Seq::empty()) > 0,
        forall|r: Row| r.len() == 2 ==> !#[trigger] fits_query(db, r, sub_query(params_of(p, c2))),
    ensures !fits_query(db, Seq::empty(), body(params_of(p, c2))),
{
    let ps = params_of(p, c2);
    let e = Seq::<Val>::empty();
    let gr = group_rows_of(sv, p);
    lemma_group_rows(db, sv, p);
    lemma_groups_exist(sv, p);
    assert forall|i: int| 0 <= i < gr.len() implies !fits_pred(db, e + #[trigger] gr[i], having(ps)) by {
        lemma_having_unfit(db, ps, gr[i]);
    }
    lemma_filter_capacity(db, e, having(ps), Box::new(grouped(ps[0])), gr, 0);
}

/// A qualifying row makes its key's count positive.
proof fn lemma_hit_count(g: QuerySpec, xs: Seq<Row>, m: int)
    requires 0 <= m < xs.len(), hit(g, xs[m], (g.key)(xs[m])),
    ensures gcount(g, xs, (g.key)(xs[m])) > 0,
    decreases xs.len(),
{
    if m < xs.len() - 1 {
        assert(xs.drop_last()[m] == xs[m]);
        lemma_hit_count(g, xs.drop_last(), m);
    }
}

/// The total absolute mass leaves `i128` (every group fits): the subquery's SUM is outside its domain.
pub proof fn lemma_cap_total(db: Database, sv: StoresView, p: Seq<u8>, c2: int)
    requires
        tables_of(sv, db), stores_wf(sv), bounds_ok(sv),
        group_caps(gq(p), from_rows(sv)),
        gabs(sq(p), from_rows(sv), Seq::empty(), 0) > i128::MAX as int,
    ensures !fits_query(db, Seq::empty(), body(params_of(p, c2))),
{
    let ps = params_of(p, c2);
    let xs = from_rows(sv);
    let g = sq(p);
    let e = Seq::<Val>::empty();
    lemma_gabs_pos(g, xs, e);
    assert forall|r: Row| r.len() == 2 implies !#[trigger] fits_query(db, r, sub_query(ps)) by {
        let kp = kept(sv, p);
        let aggs = seq![sum_agg(2)];
        lemma_filter_eval(db, sv, p, r);
        lemma_kept(sv, p);
        let args = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
        assert forall|i: int| 0 <= i < kp.len() implies #[trigger] agg_args(db, r + kp[i], aggs) == Ok::<Row, SqlError>(args[i]) by {
            lemma_arg_row(db, sv, p, r, kp[i]);
        }
        lemma_scalar_members(g, xs);
        lemma_members_fits(g, xs, e, arg_expr(2));
        lemma_aggregate_capacity(db, r, aggs, Box::new(filtered(2, Literal::Text(p))), kp, args, 0);
        lemma_first_input(db, r, sub_query(ps));
    }
    lemma_cap_having(db, sv, p, c2);
}

/// Both masses fit but `total * $2` leaves `i128`: the subquery's projection is outside its domain.
pub proof fn lemma_cap_scaled(db: Database, sv: StoresView, p: Seq<u8>, c2: int)
    requires
        tables_of(sv, db), stores_wf(sv), bounds_ok(sv),
        group_caps(gq(p), from_rows(sv)),
        group_caps(sq(p), from_rows(sv)),
        gcount(sq(p), from_rows(sv), Seq::empty()) > 0,
        !(i128::MIN as int <= gsum(sq(p), from_rows(sv), Seq::empty(), 0) * c2 <= i128::MAX as int),
        -100000000000000000000000000000000000000 < c2 < 100000000000000000000000000000000000000,
    ensures !fits_query(db, Seq::empty(), body(params_of(p, c2))),
{
    let ps = params_of(p, c2);
    let t = gsum(sq(p), from_rows(sv), Seq::empty(), 0);
    assert forall|r: Row| r.len() == 2 implies !#[trigger] fits_query(db, r, sub_query(ps)) by {
        lemma_sub_agg(db, sv, p, r);
        let v = total_val(sv, p);
        assert(v == Val::Num { coeff: t, scale: 2 });
        let arows = seq![seq![v]];
        let exprs = seq![scaled(ps[1])];
        let env = r + arows[0];
        assert(env[2] == v);
        lemma_lit2(db, env, c2);
        assert(eval_expr(db, env, Expr::Col(2)) == Ok::<Val, SqlError>(v));
        assert(!num_arith_fits(ArithOp::Mul, t, 2, c2, 10));
        assert(!fits_expr(db, env, scaled(ps[1])));
        assert(exprs.drop_last() =~= Seq::<Expr>::empty());
        assert(eval_exprs(db, env, exprs.drop_last()) is Ok) by {
            lemma_eval_exprs_empty(db, env);
        }
        assert(fits_exprs(db, env, exprs.drop_last()));
        assert(!fits_exprs(db, env, exprs));
        let rs = project_results(db, r, arows, exprs);
        let fs = project_fs(db, r, arows, exprs);
        lemma_project_fs_index(db, r, arows, exprs);
        assert(!fs[0]);
        assert(ok_before(rs, 0));
        lemma_each_capacity(rs, fs, 0);
    }
    lemma_cap_having(db, sv, p, c2);
}

} // verus!
