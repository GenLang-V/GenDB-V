//! The statement's body `SELECT 100.00 * sum0 / sum1` over the aggregate row, stated with the per-lineitem totals
//! `t = line::tot(sv, w, 0, n_l)`:
//! - the output value is `out_val(t)`: NULL without qualifying rows, else PostgreSQL's numeric division of
//!   `10000 * s_pr` (scale `2 + s0`) by `s_all` (scale 4), or its SQL error (`lemma_body_rows`);
//! - outside `out_fits(t)` (the product `10000 * s_pr` or the division leaves its executable domain), or with a
//!   volume mass beyond `i128::MAX`, the body is outside the capacity domain (`lemma_body_rows`,
//!   `lemma_body_mass`);
//! - a failing `$1 + INTERVAL '1' MONTH` on a non-empty product is that error (`lemma_body_err`), and an empty
//!   product gives one NULL (`lemma_body_empty`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::fns::*;
use crate::spec::fns::div::*;
use crate::exec::domain::*;
use crate::exec::relational::domain::*;
use crate::gendb_entry::stores::StoresView;
use crate::link::join::{keep, sum_of, lemma_sum_of_ext};
use crate::link::query::{lemma_node_mul, lemma_digits_in_range};
use crate::link::expr::{fits_i128, i128_max};
use crate::bridge::collect::lemma_collect_all;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::ast::*;
use crate::agent::joined::*;
use crate::agent::agg::*;

verus! {

// ------------------------------------------------------------------------------------------------ the output value

/// The output value of the totals `t`.
pub open spec fn out_val(t: Tot) -> Result<Val, SqlError> {
    if t.cnt == 0 { Ok(Val::Null) } else { num_div(10000 * t.s_pr, 2 + s0_of(t), t.s_all, 4) }
}

/// The output's arithmetic is inside its executable domain.
pub open spec fn out_fits(t: Tot) -> bool {
    t.cnt == 0 || (fits_i128(10000 * t.s_pr) && num_div_fits(10000 * t.s_pr, 2 + s0_of(t), t.s_all, 4))
}

/// The literal `100.00`.
proof fn lemma_hundred(db: Database, g: Row)
    ensures eval_expr(db, g, Expr::Lit(Literal::Num { coeff: 10000, scale: 2 })) == Ok::<Val, SqlError>(Val::Num { coeff: 10000, scale: 2 }),
{
    lemma_num_in_range_small(10000, 2);
    assert(2 <= crate::spec::limits::numeric_dscale_max()) by (compute);
}

/// One evaluation and domain step of an arithmetic node over evaluated operands.
proof fn lemma_arith_node(db: Database, g: Row, op: ArithOp, kind: NumKind, a: Expr, b: Expr, va: Val, vb: Val)
    requires
        eval_expr(db, g, a) == Ok::<Val, SqlError>(va),
        eval_expr(db, g, b) == Ok::<Val, SqlError>(vb),
        fits_expr(db, g, a), fits_expr(db, g, b),
    ensures
        eval_expr(db, g, Expr::Arith { op, kind, a: Box::new(a), b: Box::new(b) }) == arith(op, kind, va, vb),
        fits_expr(db, g, Expr::Arith { op, kind, a: Box::new(a), b: Box::new(b) }) == arith_fits(op, kind, va, vb),
{
}

/// `100.00 * NULL` is NULL, inside its domain.
proof fn lemma_mul_null(db: Database, g: Row)
    requires g.len() == 2, g[0] == Val::Null,
    ensures
        eval_expr(db, g, mul_expr()) == Ok::<Val, SqlError>(Val::Null),
        fits_expr(db, g, mul_expr()),
{
    let lit = Expr::Lit(Literal::Num { coeff: 10000, scale: 2 });
    lemma_hundred(db, g);
    assert(eval_expr(db, g, Expr::Col(0)) == Ok::<Val, SqlError>(g[0]));
    lemma_arith_node(db, g, ArithOp::Mul, NumKind::Numeric, lit, Expr::Col(0), Val::Num { coeff: 10000, scale: 2 }, Val::Null);
}

/// The product of the digit-bounded factors `10000` and `c` is a numeric value at scale `2 + s`.
proof fn lemma_mul_value(c: int, s: nat)
    requires abs(c) <= i128_max(), s <= 4,
    ensures arith(ArithOp::Mul, NumKind::Numeric, Val::Num { coeff: 10000, scale: 2 }, Val::Num { coeff: c, scale: s })
        == Ok::<Val, SqlError>(Val::Num { coeff: 10000 * c, scale: 2 + s }),
{
    let p = 10000 * c;
    assert(abs(p) <= 10000 * i128_max()) by (nonlinear_arith) requires abs(c) <= i128_max(), p == 10000 * c;
    assert(10000 * i128_max() < pow10(44)) by (compute);
    assert(44 <= crate::spec::limits::numeric_int_digits_max()) by (compute);
    lemma_digits_in_range(p, 2 + s, 44);
}

/// `100.00 * sum0` for a numeric `sum0`, and its domain.
proof fn lemma_mul_num(db: Database, g: Row, c: int, s: nat)
    requires g.len() == 2, g[0] == (Val::Num { coeff: c, scale: s }), abs(c) <= i128_max(), s <= 4,
    ensures
        eval_expr(db, g, mul_expr()) == Ok::<Val, SqlError>(Val::Num { coeff: 10000 * c, scale: 2 + s }),
        fits_expr(db, g, mul_expr()) == fits_i128(10000 * c),
{
    let lit = Expr::Lit(Literal::Num { coeff: 10000, scale: 2 });
    lemma_hundred(db, g);
    assert(eval_expr(db, g, Expr::Col(0)) == Ok::<Val, SqlError>(g[0]));
    lemma_arith_node(db, g, ArithOp::Mul, NumKind::Numeric, lit, Expr::Col(0), Val::Num { coeff: 10000, scale: 2 }, g[0]);
    lemma_mul_value(c, s);
    assert(2 + s <= u32::MAX as nat);
}

/// A two-element list of expressions.
proof fn lemma_list2(db: Database, g: Row, a: Expr, b: Expr, va: Val, vb: Val)
    requires eval_expr(db, g, a) == Ok::<Val, SqlError>(va), eval_expr(db, g, b) == Ok::<Val, SqlError>(vb),
    ensures eval_exprs(db, g, seq![a, b]) == Ok::<Row, SqlError>(seq![va, vb]),
{
    hide(eval_expr);
    hide(collect);
    let es = seq![a, b];
    let vs = seq![va, vb];
    let rs = expr_results(db, g, es);
    lemma_expr_results_index(db, g, es);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        if i == 0 {} else { assert(i == 1); }
    }
    lemma_collect_all(rs, vs);
    assert(eval_exprs(db, g, es) == collect(rs));
}

/// The domain of a two-element list whose first element evaluates.
proof fn lemma_fits_list2(db: Database, g: Row, a: Expr, b: Expr)
    requires eval_expr(db, g, a) is Ok,
    ensures fits_exprs(db, g, seq![a, b]) == (fits_expr(db, g, a) && fits_expr(db, g, b)),
{
    hide(eval_expr);
    hide(fits_expr);
    hide(eval_exprs);
    let es = seq![a, b];
    let first = seq![a];
    assert(es.drop_last() =~= first);
    assert(es.last() == b);
    assert(first.drop_last() =~= Seq::<Expr>::empty());
    assert(first.last() == a);
    lemma_fits_exprs_unfold(db, g, es);
    lemma_fits_exprs_unfold(db, g, first);
    assert(fits_exprs(db, g, Seq::<Expr>::empty()));
    reveal(eval_exprs);
    lemma_eval_exprs_empty(db, g);
    lemma_eval_exprs_step(db, g, first);
}

/// One evaluation and domain step of a call over evaluated arguments.
proof fn lemma_call_node(db: Database, g: Row, f: ScalarFn, args: Seq<Expr>, vs: Seq<Val>)
    requires eval_exprs(db, g, args) == Ok::<Row, SqlError>(vs),
    ensures
        eval_expr(db, g, Expr::Call { f, args }) == apply_fn(f, vs),
        fits_expr(db, g, Expr::Call { f, args }) == (fits_exprs(db, g, args) && fits_fn(f, vs)),
{
}

/// The numeric division on two operands: NULL with a NULL operand, else `num_div`; and its domain.
proof fn lemma_apply_div(x: Val, y: Val)
    ensures
        (x is Null || y is Null) ==> apply_fn(ScalarFn::DivNumeric, seq![x, y]) == Ok::<Val, SqlError>(Val::Null)
            && fits_fn(ScalarFn::DivNumeric, seq![x, y]),
        (x is Num && y is Num) ==> apply_fn(ScalarFn::DivNumeric, seq![x, y])
            == num_div(x->Num_coeff, x->Num_scale, y->Num_coeff, y->Num_scale)
            && fits_fn(ScalarFn::DivNumeric, seq![x, y]) == num_div_fits(x->Num_coeff, x->Num_scale, y->Num_coeff, y->Num_scale),
{
    let vs = seq![x, y];
    assert(vs[0] == x && vs[1] == y);
}

/// `100.00 * NULL / NULL` is NULL, inside its domain.
proof fn lemma_div_null(db: Database, g: Row)
    requires g.len() == 2, g[0] == Val::Null, g[1] == Val::Null,
    ensures
        eval_expr(db, g, div_expr()) == Ok::<Val, SqlError>(Val::Null),
        fits_expr(db, g, div_expr()),
{
    hide(apply_fn);
    hide(fits_fn);
    lemma_mul_null(db, g);
    assert(eval_expr(db, g, Expr::Col(1)) == Ok::<Val, SqlError>(g[1]));
    lemma_list2(db, g, mul_expr(), Expr::Col(1), Val::Null, g[1]);
    lemma_fits_list2(db, g, mul_expr(), Expr::Col(1));
    assert(fits_expr(db, g, Expr::Col(1)));
    lemma_call_node(db, g, ScalarFn::DivNumeric, seq![mul_expr(), Expr::Col(1)], seq![Val::Null, g[1]]);
    lemma_apply_div(Val::Null, g[1]);
}

/// `100.00 * sum0 / sum1` on numeric sums: the division, and its domain.
proof fn lemma_div_num(db: Database, g: Row, c0: int, s0: nat, c1: int)
    requires
        g.len() == 2, g[0] == (Val::Num { coeff: c0, scale: s0 }), g[1] == (Val::Num { coeff: c1, scale: 4 }),
        abs(c0) <= i128_max(), s0 <= 4,
    ensures
        eval_expr(db, g, div_expr()) == num_div(10000 * c0, 2 + s0, c1, 4),
        fits_expr(db, g, div_expr()) == (fits_i128(10000 * c0) && num_div_fits(10000 * c0, 2 + s0, c1, 4)),
{
    hide(apply_fn);
    hide(fits_fn);
    hide(num_div);
    hide(num_div_fits);
    let m = Val::Num { coeff: 10000 * c0, scale: 2 + s0 };
    lemma_mul_num(db, g, c0, s0);
    assert(eval_expr(db, g, Expr::Col(1)) == Ok::<Val, SqlError>(g[1]));
    lemma_list2(db, g, mul_expr(), Expr::Col(1), m, g[1]);
    lemma_fits_list2(db, g, mul_expr(), Expr::Col(1));
    assert(fits_expr(db, g, Expr::Col(1)));
    lemma_call_node(db, g, ScalarFn::DivNumeric, seq![mul_expr(), Expr::Col(1)], seq![m, g[1]]);
    lemma_apply_div(m, g[1]);
}

/// `100.00 * sum0 / sum1` on the aggregate row, and its domain.
proof fn lemma_div(db: Database, t: Tot)
    requires t.cnt != 0 ==> abs(t.s_pr) <= i128_max(),
    ensures
        eval_expr(db, grow(t), div_expr()) == out_val(t),
        fits_expr(db, grow(t), div_expr()) == out_fits(t),
{
    hide(num_div);
    hide(num_div_fits);
    hide(eval_expr);
    hide(fits_expr);
    let g = grow(t);
    if t.cnt == 0 {
        lemma_div_null(db, g);
    } else {
        lemma_div_num(db, g, t.s_pr, s0_of(t), t.s_all);
    }
}

/// The output expressions on the aggregate row: one value, or its error; their domain.
proof fn lemma_outs(db: Database, t: Tot)
    requires t.cnt != 0 ==> abs(t.s_pr) <= i128_max(),
    ensures
        eval_exprs(db, grow(t), seq![div_expr()]) == match out_val(t) {
            Ok(v) => Ok::<Row, SqlError>(seq![v]),
            Err(e) => Err(e),
        },
        fits_exprs(db, grow(t), seq![div_expr()]) == out_fits(t),
{
    hide(eval_expr);
    hide(fits_expr);
    let g = grow(t);
    let es = seq![div_expr()];
    lemma_div(db, t);
    assert(es.drop_last() =~= Seq::<Expr>::empty());
    assert(es.last() == div_expr());
    lemma_eval_exprs_empty(db, g);
    lemma_eval_exprs_step(db, g, es);
    lemma_fits_exprs_unfold(db, g, es);
    assert(fits_exprs(db, g, Seq::<Expr>::empty()));
    if let Ok(v) = out_val(t) {
        assert(Seq::<Val>::empty().push(v) =~= seq![v]);
    }
}

/// The body over the aggregate row `grow(t)`: the output row, or its error; outside its domain, `!fits_query`.
pub proof fn lemma_project(db: Database, ps: Seq<Literal>, t: Tot)
    requires
        eval_query(db, Seq::empty(), q_agg(ps)) == Ok::<Relation, SqlError>(seq![grow(t)]),
        t.cnt != 0 ==> abs(t.s_pr) <= i128_max(),
    ensures
        eval_query(db, Seq::empty(), q_body(ps)) == match out_val(t) {
            Ok(v) => Ok::<Relation, SqlError>(seq![seq![v]]),
            Err(e) => Err::<Relation, SqlError>(e),
        },
        !out_fits(t) ==> !fits_query(db, Seq::empty(), q_body(ps)),
{
    let ctx = Seq::<Val>::empty();
    let g = grow(t);
    let rows = seq![g];
    let exprs = seq![div_expr()];
    lemma_outs(db, t);
    assert(ctx + g =~= g);
    lemma_eval_project(db, ctx, exprs, Box::new(q_agg(ps)));
    let rs = project_results(db, ctx, rows, exprs);
    assert(rs.len() == 1 && rs[0] == eval_exprs(db, g, exprs));
    assert(rs.drop_last() =~= Seq::<Result<Row, SqlError>>::empty());
    assert(collect(rs.drop_last()) == Ok::<Seq<Row>, SqlError>(Seq::empty()));
    if let Ok(v) = out_val(t) {
        assert(Seq::<Row>::empty().push(seq![v]) =~= seq![seq![v]]);
    }
    if !out_fits(t) {
        let fs = project_fs(db, ctx, rows, exprs);
        assert(fs[0] == fits_exprs(db, ctx + rows[0], exprs));
        assert(ok_before(rs, 0));
        assert(!fits_each(rs, fs));
    }
}

// ------------------------------------------------------------------------------------------------ kept rows

/// Every kept row has the shape the arguments read.
proof fn lemma_kept_shape(sv: StoresView, w: Win)
    requires domains_ok(sv),
    ensures all_jshape(keep(jrows(sv), jq(w))),
{
    let k = keep(jrows(sv), jq(w));
    lemma_kept_rows(sv, w);
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
    assert forall|i: int| 0 <= i < k.len() implies jshape(#[trigger] k[i]) by {
        let (l, a) = choose|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && k[i] == #[trigger] row2(sv, l, a);
        lemma_row2(sv, l, a);
        assert(num15(l_price(sv)[l]) && num15(l_disc(sv)[l]));
    }
}

/// The number of rows is the sum of 1 over them.
proof fn lemma_sum_one(ks: Seq<Row>, f: spec_fn(Row) -> int)
    requires forall|i: int| 0 <= i < ks.len() ==> f(#[trigger] ks[i]) == 1,
    ensures sum_of(ks, f) == ks.len(),
    decreases ks.len(),
{
    if ks.len() > 0 {
        let ki = ks.drop_last();
        assert forall|i: int| 0 <= i < ki.len() implies f(#[trigger] ki[i]) == 1 by { assert(ki[i] == ks[i]); }
        lemma_sum_one(ki, f);
        assert(f(ks[ks.len() - 1]) == 1);
    }
}

/// The sums over the kept rows are the per-lineitem totals.
pub proof fn lemma_kept_tot(sv: StoresView, w: Win)
    requires model_ok(sv),
    ensures ksums(keep(jrows(sv), jq(w))) == tot(sv, w, 0, n_l(sv) as int),
{
    let k = keep(jrows(sv), jq(w));
    lemma_kept_rows(sv, w);
    lemma_kept_sums(sv, w);
    assert forall|i: int| 0 <= i < k.len() implies (jt_cnt(w))(#[trigger] k[i]) == 1 by {}
    lemma_sum_one(k, jt_cnt(w));
    assert forall|i: int| 0 <= i < k.len() implies (kt_all())(#[trigger] k[i]) == (jt_all(w))(k[i]) by {}
    lemma_sum_of_ext(k, kt_all(), jt_all(w));
    assert forall|i: int| 0 <= i < k.len() implies (kt_abs())(#[trigger] k[i]) == (jt_abs(w))(k[i]) by {}
    lemma_sum_of_ext(k, kt_abs(), jt_abs(w));
    assert forall|i: int| 0 <= i < k.len() implies (kt_npr())(#[trigger] k[i]) == (jt_npr(w))(k[i]) by {}
    lemma_sum_of_ext(k, kt_npr(), jt_npr(w));
    assert forall|i: int| 0 <= i < k.len() implies (kt_pr())(#[trigger] k[i]) == (jt_pr(w))(k[i]) by {}
    lemma_sum_of_ext(k, kt_pr(), jt_pr(w));
    assert forall|i: int| 0 <= i < k.len() implies (kt_apr())(#[trigger] k[i]) == (jt_apr(w))(k[i]) by {}
    lemma_sum_of_ext(k, kt_apr(), jt_apr(w));
}

// ------------------------------------------------------------------------------------------------ the body

/// The body from filtered rows `ks` that are kept joined rows: inside the volume capacity, the output row or its
/// error (and `!fits_query` outside `out_fits`); beyond it, `!fits_query`.
proof fn lemma_body_of(db: Database, ps: Seq<Literal>, ks: Seq<Row>)
    requires
        eval_query(db, Seq::empty(), q_filter(ps)) == Ok::<Relation, SqlError>(ks),
        all_jshape(ks),
    ensures
        ksums(ks).a_all <= i128_max() ==> eval_query(db, Seq::empty(), q_body(ps)) == match out_val(ksums(ks)) {
            Ok(v) => Ok::<Relation, SqlError>(seq![seq![v]]),
            Err(e) => Err::<Relation, SqlError>(e),
        },
        ksums(ks).a_all <= i128_max() && !out_fits(ksums(ks)) ==> !fits_query(db, Seq::empty(), q_body(ps)),
        ksums(ks).a_all > i128_max() ==> !fits_query(db, Seq::empty(), q_body(ps)),
{
    let t = ksums(ks);
    lemma_cols(ks);
    if t.a_all <= i128_max() {
        lemma_eval_agg(db, ps, ks);
        lemma_project(db, ps, t);
    } else {
        lemma_agg_capacity(db, ps, ks);
    }
}

/// The body over a bound database, with the statement's window `w`.
pub proof fn lemma_body_rows(db: Database, sv: StoresView, ps: Seq<Literal>, w: Win, t1: int)
    requires tables_of(sv, db), model_ok(sv), bounds_ok(ps, w, t1),
    ensures ({
        let t = tot(sv, w, 0, n_l(sv) as int);
        &&& t.a_all <= i128_max() ==> eval_query(db, Seq::empty(), q_body(ps)) == match out_val(t) {
                Ok(v) => Ok::<Relation, SqlError>(seq![seq![v]]),
                Err(e) => Err::<Relation, SqlError>(e),
            }
        &&& t.a_all <= i128_max() && !out_fits(t) ==> !fits_query(db, Seq::empty(), q_body(ps))
        &&& t.a_all > i128_max() ==> !fits_query(db, Seq::empty(), q_body(ps))
    }),
{
    crate::agent::joined::lemma_eval_filter(db, sv, ps, w, t1);
    lemma_kept_shape(sv, w);
    lemma_kept_tot(sv, w);
    lemma_body_of(db, ps, keep(jrows(sv), jq(w)));
}

/// An empty product: the body is one NULL, whatever `$1`.
pub proof fn lemma_body_empty(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), model_ok(sv), jrows(sv).len() == 0,
    ensures eval_query(db, Seq::empty(), q_body(ps)) == Ok::<Relation, SqlError>(seq![seq![Val::Null]]),
{
    let w = Win { lo: 0, hi: 0 };
    crate::agent::joined::lemma_eval_filter_empty(db, sv, ps, w);
    let k = keep(jrows(sv), jq(w));
    assert(k =~= Seq::<Row>::empty());
    lemma_kept_shape(sv, w);
    lemma_cols(k);
    lemma_body_of(db, ps, k);
}

/// A failing `$1 + INTERVAL '1' MONTH` on a non-empty product: the body is that error.
pub proof fn lemma_body_err(db: Database, sv: StoresView, ps: Seq<Literal>, pd: int, e: SqlError)
    requires
        tables_of(sv, db),
        ps.len() == 1,
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(pd)),
        month_end_val(pd) == Err::<Val, SqlError>(e),
        jrows(sv).len() > 0,
    ensures eval_query(db, Seq::empty(), q_body(ps)) == Err::<Relation, SqlError>(e),
{
    let ctx = Seq::<Val>::empty();
    crate::agent::joined::lemma_filter_err(db, sv, ps, pd, e);
    lemma_eval_aggregate(db, ctx, q_aggs(), Box::new(q_filter(ps)));
    lemma_eval_project(db, ctx, seq![div_expr()], Box::new(q_agg(ps)));
}

} // verus!
