//! When the statement leaves its capacity domain (`exec::relational::domain::fits_query`): the absolute mass of the
//! SUM over all qualifying rows exceeds `i128` (`M > i128::MAX`), or `T * $2` does not fit `i128` while some row
//! qualifies. `lemma_capacity` proves `!fits_query` of the body in both cases:
//! - some group's own mass exceeds `i128`: the GROUP BY leaves its domain (`lemma_cap_group`);
//! - else every group fits, the GROUP BY has a row, and the HAVING subquery (the same for every group row) leaves its
//!   domain: its SUM mass is `M` (`lemma_cap_sub`) or its product `T * $2` overflows (`lemma_cap_mul_sub`), so the
//!   HAVING condition of the first group row is outside its domain (`lemma_cap_having`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::numeric::{abs, pow10};
use crate::spec::relation::{collect, keep_true, column, group_members, agg_value, all_of_kind, count_non_null};
use crate::spec::equality::distinct_rows;
use crate::spec::scalar::{NumKind, ArithOp, CmpOp};
use crate::exec::relational::domain::*;
use crate::exec::domain::*;
use crate::link::expr::{ival, fits_i128, i128_max};
use crate::link::query::*;
use crate::link::capacity::*;
use super::nf::*;
use super::sqlrow::*;
use super::sqlq::*;
use super::tables::Tabs;
use super::bind::tabs_of;

verus! {

/// The members' SUM column holds the group's argument coefficients at scale 2; its mass at scale 2 is `gabs`.
proof fn lemma_members_mass(g: QuerySpec, xs: Seq<Row>, k: Row)
    requires g.aggs == seq![AggKind::Sum { scale: 2 }],
    ensures
        forall|i: int| 0 <= i < column(members(g, xs, k), 0).len()
            ==> (#[trigger] column(members(g, xs, k), 0)[i] matches Val::Num { coeff, scale } ==> scale == 2),
        num_mass_at(column(members(g, xs, k), 0), 2) == gabs(g, xs, k, 0),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let d = xs.drop_last();
        lemma_members_mass(g, d, k);
        let md = members(g, d, k);
        if hit(g, xs.last(), k) {
            let a = arg_vals(g, xs.last());
            assert(members(g, xs, k) == md.push(a));
            assert(column(md.push(a), 0) =~= column(md, 0).push(a[0]));
            assert(a[0] == Val::Num { coeff: (g.arg)(0, xs.last()), scale: 2 });
            assert(pow10(0) == 1) by (compute);
            assert(column(md.push(a), 0).drop_last() =~= column(md, 0));
        }
    }
}

/// A SUM over a group's members fits exactly when the group's mass fits; inside, it succeeds.
proof fn lemma_sum_fits(g: QuerySpec, xs: Seq<Row>, k: Row, d: nat)
    requires g.aggs == seq![AggKind::Sum { scale: 2 }],
    ensures
        fits_agg_value(sum_at(d), column(members(g, xs, k), 0)) <==> gabs(g, xs, k, 0) <= i128_max(),
        aggs_ok_inside(seq![sum_at(d)], members(g, xs, k)),
{
    let vs = column(members(g, xs, k), 0);
    lemma_members_mass(g, xs, k);
    lemma_members_col(g, xs, k, 0);
    lemma_num_mass_uniform(vs, 2);
    if vs.len() > 0 {
        // A member's SUM value is numeric (of kind Numeric, and not NULL: count_non_null == len).
        lemma_non_null_all(vs, 0);
    } else {
        assert(num_mass_at(vs, num_max_scale(vs)) == 0);
        crate::link::query::lemma_abs_bound(g, xs, k, 0);
    }
    if fits_agg_value(sum_at(d), vs) {
        lemma_sum_inside_ok(NumKind::Numeric, arg_at(d), vs);
    }
    assert(column(members(g, xs, k), 0) == vs);
}

/// At most every value is non-NULL.
proof fn lemma_cnn_le(vs: Seq<Val>)
    ensures count_non_null(vs) <= vs.len(),
    decreases vs.len(),
{
    if vs.len() > 0 {
        lemma_cnn_le(vs.drop_last());
    }
}

/// Values of kind Numeric, all non-NULL: each is numeric.
proof fn lemma_non_null_all(vs: Seq<Val>, i: int)
    requires 0 <= i < vs.len(), all_of_kind(NumKind::Numeric, vs), count_non_null(vs) == vs.len(),
    ensures vs[i] is Num,
    decreases vs.len(),
{
    let d = vs.drop_last();
    lemma_cnn_le(d);
    if i < vs.len() - 1 {
        lemma_non_null_all(d, i);
        assert(d[i] == vs[i]);
    }
}

/// Two conditions that agree on every row keep the same rows.
proof fn lemma_qrows_same(g1: QuerySpec, g2: QuerySpec, xs: Seq<Row>)
    requires forall|x: Row| #[trigger] (g1.qual)(x) == (g2.qual)(x),
    ensures qrows(g1, xs) == qrows(g2, xs),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_qrows_same(g1, g2, xs.drop_last());
    }
}

/// The WHERE output is the qualifying joined rows, each typed.
proof fn lemma_kept(db: Database, name: Seq<u8>)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)),
    ensures ({
        let x = xs(tabs_of(db));
        &&& eval_query(db, Seq::empty(), where_q(Literal::Text(name))) == Ok::<Relation, SqlError>(qrows(gq(name), x))
        &&& qrows(gs(name), x) == qrows(gq(name), x)
        &&& forall|i: int| 0 <= i < qrows(gq(name), x).len() ==> #[trigger] x_typed(qrows(gq(name), x)[i])
                && qualx(name, qrows(gq(name), x)[i])
    }),
{
    let t = tabs_of(db);
    let x = xs(t);
    let g = gq(name);
    lemma_where_eval(db, name);
    lemma_proj_xs(t);
    lemma_xs_typed(t);
    crate::link::query::lemma_kept_rows(g, x, id16());
    let kept = keep_true(x, qual_truths(g, x));
    assert forall|i: int| 0 <= i < kept.len() implies (#[trigger] kept[i]).len() == 16 by {
        let j = choose|j: int| 0 <= j < x.len() && x[j] == kept[i];
        assert(x_typed(x[j]));
    }
    assert(proj_all(kept, id16()) =~= kept) by {
        assert forall|i: int| 0 <= i < kept.len() implies #[trigger] proj_all(kept, id16())[i] == kept[i] by {
            lemma_proj16(kept[i]);
        }
    }
    lemma_qrows_same(gs(name), g, x);
    crate::link::query::lemma_qrows_sub(g, x);
    assert forall|i: int| 0 <= i < qrows(g, x).len() implies #[trigger] x_typed(qrows(g, x)[i]) && qualx(name, qrows(g, x)[i]) by {
        let j = choose|j: int| 0 <= j < x.len() && x[j] == qrows(g, x)[i];
        assert(x_typed(x[j]));
    }
}

/// The SUM argument mass of all qualifying rows exceeds `i128`: the HAVING subquery behind any 2-value row is
/// outside its domain.
proof fn lemma_cap_sub(db: Database, name: Seq<u8>, p: Literal, w: Row)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)), w.len() == 2,
        gabs(gs(name), xs(tabs_of(db)), Seq::empty(), 0) > i128_max(),
    ensures !fits_query(db, w, sub_q(Literal::Text(name), p)),
{
    hide(eval_query);
    hide(fits_query);
    hide(agg_args);
    let x = xs(tabs_of(db));
    let g = gs(name);
    let e = Seq::<Val>::empty();
    let lit = Literal::Text(name);
    lemma_kept(db, name);
    let kept = qrows(gq(name), x);
    let f2 = Query::Filter { pred: where_at(2, lit), input: Box::new(prod_q()) };
    crate::agent::sqlq::lemma_where_s_eval_pub(db, w, lit);
    let args = kept.map_values(|r: Row| arg_vals(g, r));
    crate::link::query::lemma_scalar_members(g, x);
    assert(args == members(g, x, e));
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] agg_args(db, w + kept[i], seq![sum_at(2)]) == Ok::<Row, SqlError>(args[i]) by {
        assert(x_typed(kept[i]));
        lemma_args_shift(db, w, kept[i]);
        lemma_args_row(db, kept[i], g);
    }
    lemma_sum_fits(g, x, e, 2);
    lemma_aggregate_capacity(db, w, seq![sum_at(2)], Box::new(f2), kept, args, 0);
    lemma_first_input(db, w, sub_q(lit, p));
}

/// `T * $2` beyond `i128` on the subquery's aggregate row: the projection is outside its domain.
proof fn lemma_mul_unfit(db: Database, env: Row, tc: int, p: Literal)
    requires env.len() == 3, env[2] == (Val::Num { coeff: tc, scale: 2 }), p_ok(p), !fits_i128(tc * p_coeff(p)),
    ensures !fits_exprs(db, env, seq![mul_e(p)]),
{
    hide(eval_query);
    hide(eval_pred);
    hide(fits_query);
    hide(fits_pred);
    let es = seq![mul_e(p)];
    lemma_fits_exprs_unfold(db, env, es);
    assert(es.drop_last() =~= Seq::<Expr>::empty());
    crate::spec::eval::lemma_eval_exprs_empty(db, env);
    let pc = p_coeff(p);
    assert(crate::spec::limits::numeric_int_digits_max() == 131072);
    assert(crate::spec::limits::numeric_dscale_max() == 16383);
    crate::link::query::lemma_digits_in_range(pc, 10, 38);
    assert(eval_expr(db, env, Expr::Lit(p)) == Ok::<Val, SqlError>(Val::Num { coeff: pc, scale: 10 }));
    assert(eval_expr(db, env, Expr::Col(2)) == Ok::<Val, SqlError>(env[2]));
    assert(!arith_fits(ArithOp::Mul, NumKind::Numeric, env[2], Val::Num { coeff: pc, scale: 10 }));
}

/// `T * $2` beyond `i128` while some row qualifies: the HAVING subquery behind any 2-value row is outside its
/// domain.
proof fn lemma_cap_mul_sub(db: Database, name: Seq<u8>, p: Literal, w: Row)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)), w.len() == 2, p_ok(p),
        group_caps(gs(name), xs(tabs_of(db))),
        gcount(gs(name), xs(tabs_of(db)), Seq::empty()) > 0,
        !fits_i128(tot(name, xs(tabs_of(db))) * p_coeff(p)),
    ensures !fits_query(db, w, sub_q(Literal::Text(name), p)),
{
    hide(eval_query);
    hide(fits_query);
    hide(fits_exprs);
    let x = xs(tabs_of(db));
    let e = Seq::<Val>::empty();
    let lit = Literal::Text(name);
    crate::agent::sqlq::lemma_sub_agg_pub(db, name, w);
    let v = Val::Num { coeff: tot(name, x), scale: 2 };
    let rows = seq![seq![v]];
    assert(eval_query(db, w, agg_s(lit)) == Ok::<Relation, SqlError>(rows));
    let env = w + seq![v];
    assert(env[2] == v);
    lemma_mul_unfit(db, env, tot(name, x), p);
    let rs = project_results(db, w, rows, seq![mul_e(p)]);
    let fs = project_fs(db, w, rows, seq![mul_e(p)]);
    lemma_project_fs_index(db, w, rows, seq![mul_e(p)]);
    assert(fs[0] == fits_exprs(db, w + rows[0], seq![mul_e(p)]));
    assert(w + rows[0] == env);
    lemma_fits_each_violation(rs, fs, 0);
    reveal(fits_query);
}

/// Group `k`'s own SUM mass exceeds `i128`: the GROUP BY, hence the body, is outside its domain.
proof fn lemma_cap_group(db: Database, name: Seq<u8>, p: Literal, k: Row)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)),
        gcount(gq(name), xs(tabs_of(db)), k) > 0,
        gabs(gq(name), xs(tabs_of(db)), k, 0) > i128_max(),
    ensures !fits_query(db, Seq::empty(), body_q(Literal::Text(name), p)),
{
    hide(eval_query);
    hide(fits_query);
    hide(agg_args);
    hide(eval_exprs);
    let t = tabs_of(db);
    let x = xs(t);
    let g = gq(name);
    let e = Seq::<Val>::empty();
    let lit = Literal::Text(name);
    lemma_kept(db, name);
    let kept = qrows(g, x);
    let ks = qkeys(g, x);
    let args = kept.map_values(|r: Row| arg_vals(g, r));
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, e + kept[i], seq![Expr::Col(0)], seq![sum_at(0)])
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(x_typed(kept[i]));
        assert(e + kept[i] =~= kept[i]);
        lemma_key_row(db, kept[i]);
        lemma_args_row(db, kept[i], g);
    }
    // The distinct keys are the group keys; the members of each are its normal-form members.
    lemma_keys_exact_pub(t, name);
    lemma_proj_xs(t);
    lemma_pool_exact(g, x);
    let pool = key_pool(g, x);
    lemma_distinct_gkeys(g, x, pool);
    crate::link::query::lemma_gkeys(g, x);
    assert(gkeys(g, x).contains(k));
    let idx = choose|idx: int| 0 <= idx < gkeys(g, x).len() && gkeys(g, x)[idx] == k;
    assert forall|h: int| 0 <= h < distinct_rows(ks).len() implies
        #[trigger] aggs_ok_inside(seq![sum_at(0)], group_members(ks, args, distinct_rows(ks)[h])) by {
        let kh = gkeys(g, x)[h];
        lemma_group_members(g, x, kh, pool);
        lemma_sum_fits(g, x, kh, 0);
    }
    lemma_group_members(g, x, k, pool);
    lemma_sum_fits(g, x, k, 0);
    lemma_group_by_capacity(db, e, seq![Expr::Col(0)], seq![sum_at(0)], Box::new(where_q(lit)), kept, ks, args, idx, 0);
    lemma_first_input(db, e, body_q(lit, p));
}

/// The HAVING condition behind a 2-value row whose subquery is outside its domain is outside its domain.
proof fn lemma_having_unfit(db: Database, lit: Literal, p: Literal, w: Row)
    requires w.len() == 2, !fits_query(db, w, sub_q(lit, p)),
    ensures !fits_pred(db, w, having_p(lit, p)),
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_pred);
    hide(fits_expr);
    hide(eval_expr);
    crate::link::expr::lemma_expr_col(db, w, 1);
    lemma_fits_col(db, w, 1);
    lemma_fits_subq(db, w, sub_q(lit, p));
    lemma_fits_cmp(db, w, CmpOp::Gt, Expr::Col(1), Expr::Subquery(Box::new(sub_q(lit, p))));
}

/// One step of `fits_pred` on a comparison.
proof fn lemma_fits_cmp(db: Database, env: Row, op: CmpOp, a: Expr, b: Expr)
    ensures fits_pred(db, env, Pred::Cmp { op, a, b }) == (fits_expr(db, env, a) && (eval_expr(db, env, a) is Ok ==> fits_expr(db, env, b))),
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_pred);
}

/// A column reference is always inside its domain.
proof fn lemma_fits_col(db: Database, env: Row, i: nat)
    ensures fits_expr(db, env, Expr::Col(i)),
{
    hide(eval_query);
    hide(fits_query);
    hide(eval_pred);
    hide(fits_pred);
}

/// A scalar subquery's domain is its query's.
proof fn lemma_fits_subq(db: Database, env: Row, q: Query)
    ensures fits_expr(db, env, Expr::Subquery(Box::new(q))) == fits_query(db, env, q),
{
    hide(eval_query);
    hide(eval_pred);
    hide(fits_pred);
}

/// Every group fits, there is a group row, and the HAVING subquery is outside its domain behind every 2-value row:
/// the body is outside its domain.
proof fn lemma_cap_having(db: Database, name: Seq<u8>, p: Literal)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)),
        group_caps(gq(name), xs(tabs_of(db))),
        gkeys(gq(name), xs(tabs_of(db))).len() > 0,
        forall|w: Row| w.len() == 2 ==> !#[trigger] fits_query(db, w, sub_q(Literal::Text(name), p)),
    ensures !fits_query(db, Seq::empty(), body_q(Literal::Text(name), p)),
{
    hide(eval_query);
    hide(fits_query);
    hide(full_row);
    let x = xs(tabs_of(db));
    let g = gq(name);
    let e = Seq::<Val>::empty();
    let lit = Literal::Text(name);
    let gr = grows(name, x);
    lemma_group_eval(db, name);
    crate::link::query::lemma_gkeys(g, x);
    assert forall|i: int| 0 <= i < gr.len() implies !#[trigger] fits_pred(db, e + gr[i], having_p(lit, p)) by {
        let k = gkeys(g, x)[i];
        assert(gkeys(g, x).contains(k));
        crate::link::query::lemma_gkeys_witness(g, x, k);
        let m = choose|m: int| 0 <= m < x.len() && #[trigger] hit(g, x[m], k);
        lemma_group_row_pub(g, x, k);
        assert(e + gr[i] =~= gr[i]);
        lemma_having_unfit(db, lit, p, gr[i]);
    }
    lemma_filter_capacity(db, e, having_p(lit, p), Box::new(group_q(lit)), gr, 0);
}

/// The body leaves its capacity domain when the SUM mass of all qualifying rows exceeds `i128`, or when some row
/// qualifies and `T * $2` does not fit `i128`.
pub proof fn lemma_capacity(db: Database, name: Seq<u8>, p: Literal)
    requires db.tables.len() == 8, tabs_typed(tabs_of(db)), p_ok(p),
        gabs(gs(name), xs(tabs_of(db)), Seq::empty(), 0) > i128_max()
        || (gabs(gs(name), xs(tabs_of(db)), Seq::empty(), 0) <= i128_max()
            && gcount(gs(name), xs(tabs_of(db)), Seq::empty()) > 0
            && !fits_i128(tot(name, xs(tabs_of(db))) * p_coeff(p))),
    ensures !fits_query(db, Seq::empty(), body_q(Literal::Text(name), p)),
{
    let x = xs(tabs_of(db));
    let g = gq(name);
    let e = Seq::<Val>::empty();
    let lit = Literal::Text(name);
    if exists|k: Row| #[trigger] gabs(g, x, k, 0) > i128_max() {
        let k = choose|k: Row| #[trigger] gabs(g, x, k, 0) > i128_max();
        if gcount(g, x, k) == 0 {
            crate::link::query::lemma_zero_count(g, x, k, 0);
        }
        lemma_cap_group(db, name, p, k);
    } else {
        assert(group_caps(g, x));
        // Some row qualifies, so some group key exists.
        if gcount(gs(name), x, e) == 0 {
            crate::link::query::lemma_zero_count(gs(name), x, e, 0);
        }
        crate::link::query::lemma_count_witness(gs(name), x, e);
        let m = choose|m: int| 0 <= m < x.len() && #[trigger] hit(gs(name), x[m], e);
        assert(hit(g, x[m], (g.key)(x[m])));
        lemma_count_pos(g, x, m, (g.key)(x[m]));
        crate::link::query::lemma_gkeys(g, x);
        assert(gkeys(g, x).contains((g.key)(x[m])));
        if gabs(gs(name), x, e, 0) > i128_max() {
            assert forall|w: Row| w.len() == 2 implies !#[trigger] fits_query(db, w, sub_q(lit, p)) by {
                lemma_cap_sub(db, name, p, w);
            }
        } else {
            crate::link::join::lemma_acc_sum_of(gs(name), x, e, 0);
            lemma_caps(tabs_of(db), name);
            assert forall|w: Row| w.len() == 2 implies !#[trigger] fits_query(db, w, sub_q(lit, p)) by {
                lemma_cap_mul_sub(db, name, p, w);
            }
        }
        lemma_cap_having(db, name, p);
    }
}

} // verus!
