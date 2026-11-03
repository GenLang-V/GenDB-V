//! The aggregate node `SUM(l_extendedprice * (1 - l_discount))` over the kept joined rows (the statement's body).
//!
//! - On a joined row (`joined::jshape`) the argument is the volume `jvol(x)` at scale 4 (`lemma_args`).
//! - Over any rows `ks`, the argument column has the exact sum, scale and absolute mass of the volumes (`lemma_cols`):
//!   the sum `s_all` at scale 4 (scale 0 without rows).
//! - Inside the SUM capacity (`a_all <= i128::MAX`) the aggregate row is `grow` of the sums: NULL without rows, else
//!   the sum (`lemma_eval_agg`); beyond it the node is outside the capacity domain (`lemma_agg_capacity`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::fns::*;
use crate::exec::relational::domain::*;
use crate::link::join::sum_of;
use crate::link::query::{lemma_node_add, lemma_node_mul, lemma_agg_arg_sum};
use crate::link::expr::{ival, i128_max};
use crate::link::capacity::{lemma_aggregate_capacity, lemma_sum_inside_ok};
use crate::bridge::collect::lemma_collect_all;
use crate::agent::ast::*;
use crate::agent::line::*;
use crate::agent::joined::*;

verus! {

// ------------------------------------------------------------------------------------------------ per-row argument

/// The aggregate arguments of a joined row.
pub open spec fn jargs(x: Row) -> Row { seq![Val::Num { coeff: jvol(x), scale: 4 }] }

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

proof fn lemma_args_len(db: Database, x: Row)
    ensures agg_arg_results(db, x, q_aggs()).len() == 1,
{
    hide(eval_expr);
    hide(agg_arg);
    hide(collect);
    hide(agg_arg_results);
    lemma_agg_arg_results_index(db, x, q_aggs());
}

proof fn lemma_arg0(db: Database, x: Row)
    requires jshape(x),
    ensures agg_arg_results(db, x, q_aggs())[0] == Ok::<Val, SqlError>(Val::Num { coeff: jvol(x), scale: 4 }),
{
    hide(eval_expr);
    hide(agg_arg);
    hide(collect);
    hide(agg_arg_results);
    lemma_vol(db, x);
    let aggs = q_aggs();
    assert(aggs[0] == Agg::Sum { kind: NumKind::Numeric, arg: vol_expr() });
    lemma_agg_arg_sum(db, x, NumKind::Numeric, vol_expr());
    lemma_agg_arg_results_index(db, x, aggs);
}

/// The aggregate argument of a joined row.
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
    let rs = agg_arg_results(db, x, q_aggs());
    let vs = jargs(x);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        assert(i == 0);
    }
    lemma_collect_all(rs, vs);
    reveal(collect);
    crate::exec::relational::domain::lemma_agg_args(db, x, q_aggs());
}

// ------------------------------------------------------------------------------------------------ argument column

/// Unguarded per-row terms of the sums over the kept rows.
pub open spec fn kt_all() -> spec_fn(Row) -> int { |x: Row| jvol(x) }
pub open spec fn kt_abs() -> spec_fn(Row) -> int { |x: Row| abs(jvol(x)) }

/// The sums over rows `ks`, as a `Tot` (`cnt` is the number of rows).
pub open spec fn ksums(ks: Seq<Row>) -> Tot {
    Tot { cnt: ks.len() as int, s_all: sum_of(ks, kt_all()), a_all: sum_of(ks, kt_abs()) }
}

/// The argument rows of rows `ks`.
pub open spec fn kargs(ks: Seq<Row>) -> Seq<Row> { ks.map_values(|x: Row| jargs(x)) }

/// The argument column: count, kind, exact sum at its scale, and absolute mass; and the bounds of the sum.
pub proof fn lemma_cols(ks: Seq<Row>)
    ensures ({
        let m = kargs(ks);
        let t = ksums(ks);
        let c0 = column(m, 0);
        let s1: nat = if t.cnt > 0 { 4 } else { 0 };
        &&& c0.len() == t.cnt
        &&& count_non_null(c0) == t.cnt
        &&& all_of_kind(NumKind::Numeric, c0)
        &&& num_sum(c0) == (t.s_all, s1)
        &&& num_max_scale(c0) == s1
        &&& num_mass_at(c0, 4) == t.a_all
        &&& 0 <= t.a_all
        &&& -t.a_all <= t.s_all <= t.a_all
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
        assert(column(m, 0).drop_last() =~= column(mi, 0));
        assert(pow10(0) == 1);
        let si1: nat = if ti.cnt > 0 { 4 } else { 0 };
        assert(a[0] == (Val::Num { coeff: v, scale: 4 }));
        assert(align(ti.s_all, si1, 4) == ti.s_all) by {
            if ti.cnt > 0 { assert((4 - si1) as nat == 0nat); } else { assert(ti.s_all == 0); }
        }
        assert(align(v, 4, 4) == v) by { assert((4 - 4) as nat == 0nat); }
    } else {
        assert(column(m, 0) =~= Seq::<Val>::empty());
    }
}

// ------------------------------------------------------------------------------------------------ the aggregate node

/// The aggregate row of the sums `t`: NULL without rows, else the sum.
pub open spec fn grow(t: Tot) -> Row {
    if t.cnt == 0 { seq![Val::Null] } else { seq![Val::Num { coeff: t.s_all, scale: 4 }] }
}

/// Inside the SUM capacity the aggregate value is the sum (NULL without rows).
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
        lemma_num_in_range_small(t.s_all, 4);
    }
    assert(rs[0] == agg_value(aggs[0], column(m, 0)));
    assert(rs[0] == Ok::<Val, SqlError>(vs[0]));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        assert(i == 0);
    }
    lemma_collect_all(rs, vs);
}

/// Every row of `ks` is a joined row with the shape the argument reads.
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
    ensures eval_query(db, Seq::empty(), q_body(ps)) == Ok::<Relation, SqlError>(seq![grow(ksums(ks))]),
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

/// The SUM's absolute mass beyond `i128::MAX`: the aggregate node is outside the capacity domain.
pub proof fn lemma_agg_capacity(db: Database, ps: Seq<Literal>, ks: Seq<Row>)
    requires
        eval_query(db, Seq::empty(), q_filter(ps)) == Ok::<Relation, SqlError>(ks),
        all_jshape(ks),
        ksums(ks).a_all > i128_max(),
    ensures !fits_query(db, Seq::empty(), q_body(ps)),
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
        assert(j == 0);
        lemma_sum_inside_ok(NumKind::Numeric, vol_expr(), column(m, 0));
    }
    assert(aggs[0] == Agg::Sum { kind: NumKind::Numeric, arg: vol_expr() });
    assert(sum_mass(NumKind::Numeric, column(m, 0)) == t.a_all);
    assert(!fits_agg_value(aggs[0], column(m, 0)));
    lemma_aggregate_capacity(db, ctx, aggs, Box::new(q_filter(ps)), ks, m, 0);
}

} // verus!
