//! The aggregate node `SUM(CASE WHEN p_type LIKE 'PROMO%' THEN volume ELSE 0 END), SUM(volume)` over the kept
//! joined rows.
//!
//! - On a joined row of the database (`jshape`: price and discount are numeric(15,2) values, `p_type` a text) the
//!   arguments are `jargs(x) = [case, volume]`: the volume `jvol(x)` at scale 4, and the case value, which is the
//!   volume when the part type starts with the characters `PROMO` (`common::like_prefix`) and the numeric `0` of
//!   scale 0 otherwise (`lemma_args`).
//! - Over any rows `ks`, the argument columns have the exact sums, scales and absolute masses of the unguarded
//!   terms `kt_*` (`lemma_cols`): the volume column sums to `s_all` at scale 4; the case column to `s_pr`, at scale 4
//!   when some row is promotional and 0 otherwise.
//! - Inside the SUM capacity (`a_all <= i128::MAX`) the aggregate row is `grow` of the sums (`lemma_eval_agg`);
//!   beyond it the node is outside the capacity domain (`lemma_agg_capacity`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::fns::*;
use crate::spec::fns::like::*;
use crate::exec::relational::domain::*;
use crate::link::join::sum_of;
use crate::link::query::{lemma_node_add, lemma_node_mul, lemma_agg_arg_sum};
use crate::link::expr::{ival, tval, i128_max};
use crate::link::capacity::{lemma_aggregate_capacity, lemma_sum_inside_ok, aggs_ok_inside};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::agent::ast::*;
use crate::agent::line::*;
use crate::agent::joined::*;
use crate::agent::common::like_prefix::*;

verus! {

// ------------------------------------------------------------------------------------------------ per-row arguments

/// The values the aggregate arguments read from a joined row: price and discount as numeric(15,2), the part type
/// as text.
pub open spec fn jshape(x: Row) -> bool {
    &&& x.len() == 25
    &&& x[5] is Num && x[5]->Num_scale == 2 && abs(x[5]->Num_coeff) < pow10(15)
    &&& x[6] is Num && x[6]->Num_scale == 2 && abs(x[6]->Num_coeff) < pow10(15)
    &&& x[20] is Text
}

/// The CASE value of a joined row.
pub open spec fn jcase(x: Row) -> Val {
    if jpromo(x) { Val::Num { coeff: jvol(x), scale: 4 } } else { Val::Num { coeff: 0, scale: 0 } }
}

/// The aggregate arguments of a joined row.
pub open spec fn jargs(x: Row) -> Row { seq![jcase(x), Val::Num { coeff: jvol(x), scale: 4 }] }

/// `CAST(k AS numeric)` of an int4 literal.
proof fn lemma_num_int(db: Database, x: Row, k: int)
    requires -100 <= k <= 100,
    ensures eval_expr(db, x, num_int(k)) == Ok::<Val, SqlError>(Val::Num { coeff: k, scale: 0 }),
{
    assert(int_in_range(IntKind::Int4, k));
    assert(lit_val(Literal::Int { v: k, kind: IntKind::Int4 }) == Ok::<Val, SqlError>(Val::Int(k)));
    assert(eval_expr(db, x, Expr::Lit(Literal::Int { v: k, kind: IntKind::Int4 })) == Ok::<Val, SqlError>(Val::Int(k)));
}

/// `l_extendedprice * (1 - l_discount)` on a joined row.
pub proof fn lemma_vol(db: Database, x: Row)
    requires jshape(x),
    ensures eval_expr(db, x, vol_expr()) == Ok::<Val, SqlError>(Val::Num { coeff: jvol(x), scale: 4 }),
{
    let price = x[5]->Num_coeff;
    let disc = x[6]->Num_coeff;
    let one = num_int(1);
    lemma_num_int(db, x, 1);
    assert(eval_expr(db, x, Expr::Col(5)) == Ok::<Val, SqlError>(x[5]));
    assert(eval_expr(db, x, Expr::Col(6)) == Ok::<Val, SqlError>(x[6]));
    assert(x[5] == Val::Num { coeff: price, scale: 2 });
    assert(x[6] == Val::Num { coeff: disc, scale: 2 });
    assert(pow10(1) == 10 && pow10(2) == 100 && pow10(0) == 1) by (compute);
    assert(crate::spec::limits::numeric_int_digits_max() >= 100) by (compute);
    lemma_node_add(db, x, ArithOp::Sub, one, Expr::Col(6), 1, 0, 1, disc, 2, 15, 2, 100, 1, 16);
    let sub = Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(one), b: Box::new(Expr::Col(6)) };
    assert(1 * 100 - disc * 1 == 100 - disc);
    lemma_node_mul(db, x, Expr::Col(5), sub, price, 2, 15, 100 - disc, 2, 16);
    assert(ival(x[5]) == price && ival(x[6]) == disc);
}

/// A three-element expression list.
proof fn lemma_expr_list3(db: Database, r: Row, a: Expr, b: Expr, c: Expr, va: Val, vb: Val, vc: Val)
    requires
        eval_expr(db, r, a) == Ok::<Val, SqlError>(va),
        eval_expr(db, r, b) == Ok::<Val, SqlError>(vb),
        eval_expr(db, r, c) == Ok::<Val, SqlError>(vc),
    ensures eval_exprs(db, r, seq![a, b, c]) == Ok::<Row, SqlError>(seq![va, vb, vc]),
{
    hide(eval_expr);
    hide(collect);
    let es = seq![a, b, c];
    let vs = seq![va, vb, vc];
    let rs = expr_results(db, r, es);
    lemma_expr_results_index(db, r, es);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        if i == 0 {} else if i == 1 {} else { assert(i == 2); }
    }
    lemma_collect_all(rs, vs);
    assert(eval_exprs(db, r, es) == collect(rs));
}

/// `'PROMO%'` is a prefix pattern of the literal `PROMO`.
pub proof fn lemma_promo_pattern()
    ensures prefix_pattern(promo_pat()), prefix_lit(promo_pat()) == promo_lit(),
{
    let p = promo_pat();
    assert forall|i: int| 0 <= i < p.len() - 1 implies #[trigger] p[i] < 0x80u8 && p[i] != 0x25u8 && p[i] != 0x5Fu8 && p[i] != 0x5Cu8 by {
        if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else {}
    }
    assert(prefix_lit(p) =~= promo_lit());
}

/// `p_type LIKE 'PROMO%'` on a joined row.
pub proof fn lemma_like(db: Database, x: Row)
    requires jshape(x),
    ensures eval_expr(db, x, like_call()) == Ok::<Val, SqlError>(Val::Bool(jpromo(x))),
{
    let s = x[20]->Text_0;
    let args = seq![Expr::Col(20), Expr::Lit(Literal::Text(promo_pat())), Expr::Lit(Literal::Text(esc_bytes()))];
    assert(eval_expr(db, x, Expr::Col(20)) == Ok::<Val, SqlError>(Val::Text(s)));
    assert(eval_expr(db, x, Expr::Lit(Literal::Text(promo_pat()))) == Ok::<Val, SqlError>(Val::Text(promo_pat())));
    assert(eval_expr(db, x, Expr::Lit(Literal::Text(esc_bytes()))) == Ok::<Val, SqlError>(Val::Text(esc_bytes())));
    lemma_expr_list3(db, x, args[0], args[1], args[2], Val::Text(s), Val::Text(promo_pat()), Val::Text(esc_bytes()));
    assert(args == seq![args[0], args[1], args[2]]);
    lemma_promo_pattern();
    lemma_like_prefix(s, promo_pat());
    let vs = seq![Val::Text(s), Val::Text(promo_pat()), Val::Text(esc_bytes())];
    assert(apply_fn(ScalarFn::Like, vs) == like_value(vs[0], vs[1], vs[2]));
    assert(esc_bytes() == seq![92u8]);
    assert(tval(x[20]) == s);
}

/// `CASE WHEN p_type LIKE 'PROMO%' THEN volume ELSE 0 END` on a joined row.
pub proof fn lemma_case(db: Database, x: Row)
    requires jshape(x),
    ensures eval_expr(db, x, case_expr()) == Ok::<Val, SqlError>(jcase(x)),
{
    lemma_like(db, x);
    let cond = Pred::OfBool(like_call());
    assert(eval_pred(db, x, cond) == Ok::<Truth, SqlError>(truth_of(jpromo(x))));
    lemma_vol(db, x);
    lemma_num_int(db, x, 0);
}

proof fn lemma_args_len(db: Database, x: Row)
    ensures agg_arg_results(db, x, q_aggs()).len() == 2,
{
    hide(eval_expr);
    hide(agg_arg);
    hide(collect);
    hide(agg_arg_results);
    lemma_agg_arg_results_index(db, x, q_aggs());
}

proof fn lemma_arg0(db: Database, x: Row)
    requires jshape(x),
    ensures agg_arg_results(db, x, q_aggs())[0] == Ok::<Val, SqlError>(jcase(x)),
{
    hide(eval_expr);
    hide(agg_arg);
    hide(collect);
    hide(agg_arg_results);
    lemma_case(db, x);
    let aggs = q_aggs();
    assert(aggs[0] == Agg::Sum { kind: NumKind::Numeric, arg: case_expr() });
    lemma_agg_arg_sum(db, x, NumKind::Numeric, case_expr());
    lemma_agg_arg_results_index(db, x, aggs);
}

proof fn lemma_arg1(db: Database, x: Row)
    requires jshape(x),
    ensures agg_arg_results(db, x, q_aggs())[1] == Ok::<Val, SqlError>(Val::Num { coeff: jvol(x), scale: 4 }),
{
    hide(eval_expr);
    hide(agg_arg);
    hide(collect);
    hide(agg_arg_results);
    lemma_vol(db, x);
    let aggs = q_aggs();
    assert(aggs[1] == Agg::Sum { kind: NumKind::Numeric, arg: vol_expr() });
    lemma_agg_arg_sum(db, x, NumKind::Numeric, vol_expr());
    lemma_agg_arg_results_index(db, x, aggs);
}

/// The two aggregate arguments of a joined row.
pub proof fn lemma_args(db: Database, x: Row)
    requires jshape(x),
    ensures agg_args(db, x, q_aggs()) == Ok::<Row, SqlError>(jargs(x)),
{
    hide(eval_expr);
    hide(agg_arg);
    hide(collect);
    hide(agg_arg_results);
    lemma_args_len(db, x);
    lemma_arg0(db, x);
    lemma_arg1(db, x);
    let rs = agg_arg_results(db, x, q_aggs());
    let vs = jargs(x);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        if i == 0 {} else { assert(i == 1); }
    }
    lemma_collect_all(rs, vs);
    reveal(collect);
    crate::exec::relational::domain::lemma_agg_args(db, x, q_aggs());
}

// ------------------------------------------------------------------------------------------------ argument columns

/// Unguarded per-row terms of the sums over the kept rows.
pub open spec fn kt_all() -> spec_fn(Row) -> int { |x: Row| jvol(x) }
pub open spec fn kt_abs() -> spec_fn(Row) -> int { |x: Row| abs(jvol(x)) }
pub open spec fn kt_npr() -> spec_fn(Row) -> int { |x: Row| if jpromo(x) { 1int } else { 0int } }
pub open spec fn kt_pr() -> spec_fn(Row) -> int { |x: Row| if jpromo(x) { jvol(x) } else { 0int } }
pub open spec fn kt_apr() -> spec_fn(Row) -> int { |x: Row| if jpromo(x) { abs(jvol(x)) } else { 0int } }

/// The sums over rows `ks`, as a `Tot` (`cnt` is the number of rows).
pub open spec fn ksums(ks: Seq<Row>) -> Tot {
    Tot {
        cnt: ks.len() as int,
        s_all: sum_of(ks, kt_all()),
        a_all: sum_of(ks, kt_abs()),
        n_pr: sum_of(ks, kt_npr()),
        s_pr: sum_of(ks, kt_pr()),
        a_pr: sum_of(ks, kt_apr()),
    }
}

/// The argument rows of rows `ks`.
pub open spec fn kargs(ks: Seq<Row>) -> Seq<Row> { ks.map_values(|x: Row| jargs(x)) }

/// The scale of the case column's sum: 4 when some row is promotional, else 0.
pub open spec fn s0_of(t: Tot) -> nat { if t.n_pr > 0 { 4 } else { 0 } }

/// The argument columns: counts, kinds, exact sums at their scales, and absolute masses; and the bounds of the sums.
pub proof fn lemma_cols(ks: Seq<Row>)
    ensures ({
        let m = kargs(ks);
        let t = ksums(ks);
        let c0 = column(m, 0);
        let c1 = column(m, 1);
        let s1: nat = if t.cnt > 0 { 4 } else { 0 };
        &&& c0.len() == t.cnt && c1.len() == t.cnt
        &&& count_non_null(c0) == t.cnt && count_non_null(c1) == t.cnt
        &&& all_of_kind(NumKind::Numeric, c0) && all_of_kind(NumKind::Numeric, c1)
        &&& num_sum(c0) == (t.s_pr, s0_of(t))
        &&& num_sum(c1) == (t.s_all, s1)
        &&& num_max_scale(c0) == s0_of(t) && num_max_scale(c1) == s1
        &&& num_mass_at(c0, 4) == t.a_pr
        &&& num_mass_at(c1, 4) == t.a_all
        &&& t.n_pr == 0 ==> num_mass_at(c0, 0) == 0
        &&& 0 <= t.n_pr <= t.cnt
        &&& 0 <= t.a_pr <= t.a_all
        &&& -t.a_all <= t.s_all <= t.a_all
        &&& -t.a_pr <= t.s_pr <= t.a_pr
        &&& t.n_pr == 0 ==> t.s_pr == 0 && t.a_pr == 0
        &&& t.cnt == 0 ==> t.s_all == 0 && t.a_all == 0
    }),
    decreases ks.len(),
{
    let m = kargs(ks);
    let t = ksums(ks);
    if ks.len() > 0 {
        let ki = ks.drop_last();
        let x = ks.last();
        lemma_cols(ki);
        let mi = kargs(ki);
        let ti = ksums(ki);
        let v = jvol(x);
        let a = jargs(x);
        assert(m == mi.push(a)) by { assert(m =~= mi.push(a)); }
        assert(column(m, 0) =~= column(mi, 0).push(a[0]));
        assert(column(m, 1) =~= column(mi, 1).push(a[1]));
        assert(column(m, 0).drop_last() =~= column(mi, 0));
        assert(column(m, 1).drop_last() =~= column(mi, 1));
        assert(pow10(0) == 1);
        let si0: nat = s0_of(ti);
        let si1: nat = if ti.cnt > 0 { 4 } else { 0 };
        // the volume column: every value is at scale 4; an empty prefix sums to (0, 0)
        assert(a[1] == (Val::Num { coeff: v, scale: 4 }));
        assert(align(ti.s_all, si1, 4) == ti.s_all) by {
            if ti.cnt > 0 { assert((4 - si1) as nat == 0nat); } else { assert(ti.s_all == 0); }
        }
        assert(align(v, 4, 4) == v) by { assert((4 - 4) as nat == 0nat); }
        if jpromo(x) {
            assert(a[0] == (Val::Num { coeff: v, scale: 4 }));
            assert(align(ti.s_pr, si0, 4) == ti.s_pr) by {
                if ti.n_pr > 0 { assert((4 - si0) as nat == 0nat); } else { assert(ti.s_pr == 0); }
            }
        } else {
            assert(a[0] == (Val::Num { coeff: 0, scale: 0 }));
            assert(align(ti.s_pr, si0, si0) == ti.s_pr) by { assert((si0 - si0) as nat == 0nat); }
            assert(align(0, 0, si0) == 0);
            assert(max_nat(si0, 0) == si0);
            assert(abs(0) * pow10((4 - 0) as nat) == 0);
            assert(abs(0) * pow10((0 - 0) as nat) == 0);
        }
    } else {
        assert(column(m, 0) =~= Seq::<Val>::empty());
        assert(column(m, 1) =~= Seq::<Val>::empty());
    }
}

// ------------------------------------------------------------------------------------------------ the aggregate node

/// The aggregate row of the sums `t`: two NULLs without rows, else the two sums.
pub open spec fn grow(t: Tot) -> Row {
    if t.cnt == 0 {
        seq![Val::Null, Val::Null]
    } else {
        seq![Val::Num { coeff: t.s_pr, scale: s0_of(t) }, Val::Num { coeff: t.s_all, scale: 4 }]
    }
}

/// Inside the SUM capacity the two aggregate values are the sums (NULL without rows).
pub proof fn lemma_agg_row(ks: Seq<Row>)
    requires ksums(ks).a_all <= i128_max(),
    ensures agg_row(q_aggs(), kargs(ks)) == Ok::<Row, SqlError>(grow(ksums(ks))),
{
    let m = kargs(ks);
    let t = ksums(ks);
    lemma_cols(ks);
    let aggs = q_aggs();
    let rs = agg_value_results(aggs, m);
    crate::exec::relational::domain::lemma_agg_row(aggs, m);
    let vs = grow(t);
    if t.cnt > 0 {
        lemma_num_in_range_small(t.s_pr, s0_of(t));
        lemma_num_in_range_small(t.s_all, 4);
    }
    assert(rs[0] == agg_value(aggs[0], column(m, 0)));
    assert(rs[1] == agg_value(aggs[1], column(m, 1)));
    assert(rs[0] == Ok::<Val, SqlError>(vs[0]));
    assert(rs[1] == Ok::<Val, SqlError>(vs[1]));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        if i == 0 {} else { assert(i == 1); }
    }
    lemma_collect_all(rs, vs);
}

/// Every row of `ks` is a joined row with the shape the arguments read.
pub open spec fn all_jshape(ks: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < ks.len() ==> jshape(#[trigger] ks[i])
}

/// The argument rows of rows of the shape.
proof fn lemma_kargs(db: Database, ks: Seq<Row>)
    requires all_jshape(ks),
    ensures
        kargs(ks).len() == ks.len(),
        forall|i: int| 0 <= i < ks.len() ==> #[trigger] agg_args(db, Seq::<Val>::empty() + ks[i], q_aggs())
            == Ok::<Row, SqlError>(kargs(ks)[i]),
{
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] agg_args(db, Seq::<Val>::empty() + ks[i], q_aggs())
        == Ok::<Row, SqlError>(kargs(ks)[i]) by {
        assert(Seq::<Val>::empty() + ks[i] =~= ks[i]);
        assert(jshape(ks[i]));
        lemma_args(db, ks[i]);
    }
}

/// The aggregate node over the filtered rows `ks`, inside the SUM capacity: the one row `grow` of the sums.
pub proof fn lemma_eval_agg(db: Database, ps: Seq<Literal>, ks: Seq<Row>)
    requires
        eval_query(db, Seq::empty(), q_filter(ps)) == Ok::<Relation, SqlError>(ks),
        all_jshape(ks),
        ksums(ks).a_all <= i128_max(),
    ensures eval_query(db, Seq::empty(), q_agg(ps)) == Ok::<Relation, SqlError>(seq![grow(ksums(ks))]),
{
    let ctx = Seq::<Val>::empty();
    let aggs = q_aggs();
    lemma_eval_aggregate(db, ctx, aggs, Box::new(q_filter(ps)));
    lemma_kargs(db, ks);
    let rs = agg_args_results(db, ctx, ks, aggs);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(kargs(ks)[i]) by {}
    lemma_collect_all(rs, kargs(ks));
    lemma_agg_row(ks);
}

/// The volume SUM's absolute mass beyond `i128::MAX`: the aggregate node is outside the capacity domain.
pub proof fn lemma_agg_capacity(db: Database, ps: Seq<Literal>, ks: Seq<Row>)
    requires
        eval_query(db, Seq::empty(), q_filter(ps)) == Ok::<Relation, SqlError>(ks),
        all_jshape(ks),
        ksums(ks).a_all > i128_max(),
    ensures !fits_query(db, Seq::empty(), q_agg(ps)),
{
    let ctx = Seq::<Val>::empty();
    let aggs = q_aggs();
    let m = kargs(ks);
    lemma_kargs(db, ks);
    lemma_cols(ks);
    let t = ksums(ks);
    assert(t.cnt > 0);
    assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(m, j))
        implies agg_value(aggs[j], column(m, j)) is Ok by {
        if j == 0 {
            lemma_sum_inside_ok(NumKind::Numeric, case_expr(), column(m, 0));
        } else {
            assert(j == 1);
            lemma_sum_inside_ok(NumKind::Numeric, vol_expr(), column(m, 1));
        }
    }
    assert(aggs[1] == Agg::Sum { kind: NumKind::Numeric, arg: vol_expr() });
    assert(sum_mass(NumKind::Numeric, column(m, 1)) == t.a_all);
    assert(!fits_agg_value(aggs[1], column(m, 1)));
    lemma_aggregate_capacity(db, ctx, aggs, Box::new(q_filter(ps)), ks, m, 1);
}

} // verus!
