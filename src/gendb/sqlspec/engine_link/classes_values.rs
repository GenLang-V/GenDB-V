//! L3 soundness, value level (engine toolkit; nothing here names a query, a table or a column).
//!
//! What the operator analyses of `engine_link::classes` mean for one evaluation of one operator on values in the
//! analysed classes: `op_sound(r, o)` (the outcome raises only the errors `o.errs` allows, and a value lies in
//! `o.cls`) and, where the analysis says so, the operator's executable-domain condition. One lemma per operator
//! family: constants and columns (`lemma_const_class`, `lemma_column_class`, `lemma_table_rows_in`), error sets
//! (`errs_le`, `lemma_collect_allow`), unary and binary arithmetic (`lemma_neg_op`, `lemma_arith_op`), casts and
//! intervals, scalar functions (`lemma_call_op`), comparisons (`lemma_comparable`, `lemma_any_cmp_ok`), CASE
//! branches (`lemma_class_join`), and aggregate values (`lemma_agg_value`). `engine_link::classes_sound` composes
//! them along the analysis' recursion.
use vstd::prelude::*;
use crate::spec::limits::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::datetime::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::typing::*;
use crate::spec::chars::*;
use crate::spec::equality::*;
use crate::spec::fns::*;
use crate::spec::fns::like::*;
use crate::spec::fns::substring::*;
use crate::spec::fns::extract::*;
use crate::spec::fns::pad::*;
use crate::spec::aggs::avg::*;
use crate::spec::aggs::minmax::*;
use crate::exec::domain::*;
use crate::exec::relational::domain::*;
use crate::exec::aggs::avg::fits_avg_value;
use crate::bridge::collect::*;
use crate::bridge::relation::lemma_distinct_vals_sub;
use crate::bridge::order::lemma_pow10_add;
use crate::bridge::fns::like::{lemma_like_mt_std, no_dangling};
use crate::link::expr::{closed_expr, closed_db, lemma_expr_closed};
use crate::link::capacity::{lemma_collect_uniform_err, lemma_num_mass_uniform, lemma_num_sum_bound};
use crate::engine_link::classes::*;

verus! {

// ------------------------------------------------------------------------------------- error sets

/// Every outcome `a` allows, `b` allows.
pub open spec fn errs_le(a: Errs, b: Errs) -> bool {
    a is Never || a == b
}

/// Both joined error sets are contained in the join.
pub proof fn lemma_errs_join(a: Errs, b: Errs)
    requires errs_join(a, b) is Some,
    ensures errs_le(a, errs_join(a, b)->Some_0), errs_le(b, errs_join(a, b)->Some_0),
{
}

/// All three joined error sets are contained in the join.
pub proof fn lemma_errs_join3(a: Errs, b: Errs, c: Errs)
    requires errs_join3(a, b, c) is Some,
    ensures
        errs_le(a, errs_join3(a, b, c)->Some_0),
        errs_le(b, errs_join3(a, b, c)->Some_0),
        errs_le(c, errs_join3(a, b, c)->Some_0),
{
}

/// An outcome allowed by a smaller error set is allowed by a larger one.
pub proof fn lemma_errs_le_allow<T>(r: Result<T, SqlError>, a: Errs, b: Errs)
    requires errs_allow(r, a), errs_le(a, b),
    ensures errs_allow(r, b),
{
}

/// Elements each allowed by `e`: the first-error collection is allowed by `e`, and an `Ok` collection holds
/// every element's value.
pub proof fn lemma_collect_allow<T>(rs: Seq<Result<T, SqlError>>, e: Errs)
    requires forall|i: int| 0 <= i < rs.len() ==> errs_allow(#[trigger] rs[i], e),
    ensures
        errs_allow(collect(rs), e),
        collect(rs) is Ok ==> collect(rs)->Ok_0.len() == rs.len() && forall|i: int| 0 <= i < rs.len()
            ==> #[trigger] rs[i] == Ok::<T, SqlError>(collect(rs)->Ok_0[i]),
{
    lemma_collect_ok(rs);
    if !(collect(rs) is Ok) {
        let i = choose|i: int| 0 <= i < rs.len() && !(#[trigger] rs[i] is Ok);
        assert(errs_allow(rs[i], e));
        if let Errs::Only(c) = e {
            assert forall|k: int| 0 <= k < rs.len() implies #[trigger] rs[k] is Ok || rs[k] == Err::<T, SqlError>(c) by {
                assert(errs_allow(rs[k], e));
            }
            lemma_collect_uniform_err(rs, c, i);
        }
    }
}

/// Every element inside its domain: the sequence is inside `fits_each`.
pub proof fn lemma_fits_each_all<T>(rs: Seq<Result<T, SqlError>>, fs: Seq<bool>)
    requires forall|i: int| 0 <= i < fs.len() ==> #[trigger] fs[i],
    ensures fits_each(rs, fs),
{
}

// ------------------------------------------------------------------------------------- constants and columns

/// `|x| < 10^digits(|x|)`.
pub proof fn lemma_digits_of(n: int)
    requires n >= 0,
    ensures n < pow10(decimal_digits(n)),
{
    lemma_decimal_digits_bound(n, decimal_digits(n));
}

/// A constant lies in its class (`const_class`).
pub proof fn lemma_const_class(v: Val)
    requires const_class(v) is Some,
    ensures in_class(v, const_class(v)->Some_0),
{
    if let Val::Num { coeff, scale } = v {
        lemma_digits_of(abs(coeff));
    }
}

/// A stored value lies in its column's class (`column_class`).
pub proof fn lemma_column_class(v: Val, c: Column)
    requires value_in_column(v, c),
    ensures in_class(v, column_class(c)),
{
}

/// The rows of a table of a well-formed database are in its column classes.
pub proof fn lemma_table_rows_in(db: Database, t: int)
    requires db_wf(db), 0 <= t < db.schema.len(),
    ensures rows_in(db.tables[t], table_classes(db.schema[t])),
{
    let rows = db.tables[t];
    let ts = db.schema[t];
    assert forall|i: int| 0 <= i < rows.len() implies row_in(#[trigger] rows[i], table_classes(ts)) by {
        assert(row_in_table(rows[i], ts));
        assert forall|c: int| 0 <= c < rows[i].len() implies in_class(#[trigger] rows[i][c], table_classes(ts)[c]) by {
            lemma_column_class(rows[i][c], ts.columns[c]);
        }
    }
}

/// The only value of a `NoValue` class is NULL.
pub proof fn lemma_no_value(v: Val, c: VClass)
    requires in_class(v, c), c.kind is NoValue,
    ensures v is Null,
{
}

/// Concatenated rows (an environment `ctx ++ row`, a joined row) lie in the concatenated classes.
pub proof fn lemma_row_in_concat(a: Row, ca: Seq<VClass>, b: Row, cb: Seq<VClass>)
    requires row_in(a, ca), row_in(b, cb),
    ensures row_in(a + b, ca + cb),
{
    assert forall|i: int| 0 <= i < (a + b).len() implies in_class(#[trigger] (a + b)[i], (ca + cb)[i]) by {
        if i < a.len() {
            assert((a + b)[i] == a[i] && (ca + cb)[i] == ca[i]);
        } else {
            assert((a + b)[i] == b[i - a.len()] && (ca + cb)[i] == cb[i - a.len()]);
        }
    }
}

/// A row in some classes lies in their nullable versions (LEFT JOIN's right side).
pub proof fn lemma_row_in_nullable(r: Row, cs: Seq<VClass>)
    requires row_in(r, cs),
    ensures row_in(r, nullable_classes(cs)),
{
    assert forall|i: int| 0 <= i < r.len() implies in_class(#[trigger] r[i], nullable_classes(cs)[i]) by {
        assert(in_class(r[i], cs[i]));
    }
}

/// The NULL padding row of a LEFT JOIN lies in the nullable classes.
pub proof fn lemma_null_row_in(cs: Seq<VClass>)
    ensures row_in(null_row(cs.len()), nullable_classes(cs)),
{
    assert forall|i: int| 0 <= i < cs.len() implies in_class(#[trigger] null_row(cs.len())[i], nullable_classes(cs)[i]) by {}
}

/// A class containing a NULL argument makes the list's `any_nullable` true.
pub proof fn lemma_any_nullable(cs: Seq<VClass>, k: int)
    requires 0 <= k < cs.len(), cs[k].nullable,
    ensures any_nullable(cs),
    decreases cs.len(),
{
    if k < cs.len() - 1 {
        lemma_any_nullable(cs.drop_last(), k);
        assert(cs.drop_last()[k] == cs[k]);
    }
}

// ------------------------------------------------------------------------------------- results of operators

/// The outcome of one operator meets its analysis: only allowed errors, and a value in the result class.
pub open spec fn op_sound(r: Result<Val, SqlError>, o: ExprInfo) -> bool {
    &&& errs_allow(r, o.errs)
    &&& (r matches Ok(w) ==> in_class(w, o.cls))
}

/// An integer result whose exact value `x` has `|x| <= m` (or any `x` when `m` is at least the kind's magnitude:
/// then only values inside the kind are results).
pub proof fn lemma_int_result(k: IntKind, x: int, m: int, nullable: bool)
    requires abs(x) <= m || m >= kind_mag(k), 0 <= m <= 0x4000_0000_0000_0000_0000_0000_0000_0000,
    ensures op_sound(int_result(k, x), int_result_info(k, m, nullable)),
{
}

/// A numeric result `c * 10^-s` with `|c| < 10^d`.
pub proof fn lemma_num_result(c: int, s: u32, d: int, nullable: bool)
    requires abs(c) < pow10(d as nat), 0 <= d, s as int <= scale_cap(),
    ensures
        op_sound(num_result(c, s as nat), num_result_info(s, d, nullable)),
        num_result_info(s, d, nullable).fits ==> fits_i128(c),
{
    let limit = numeric_int_digits_max() + s;
    if d <= limit {
        lemma_pow10_monotone(d as nat, limit as nat);
        lemma_decimal_digits_bound(abs(c), limit as nat);
        assert(num_in_range(c, s as nat));
        if d <= i128_digits() {
            lemma_pow10_monotone(d as nat, 38);
            lemma_pow10_i128_boundary();
        }
    } else if num_in_range(c, s as nat) {
        lemma_decimal_digits_bound(abs(c), limit as nat);
    }
}

/// A numeric result at scale `s` with no digit bound.
pub proof fn lemma_num_unbounded(c: int, s: u32, nullable: bool)
    requires s as int <= scale_cap(),
    ensures op_sound(num_result(c, s as nat), num_unbounded_info(s, nullable)),
{
    let limit = numeric_int_digits_max() + s;
    if num_in_range(c, s as nat) {
        lemma_decimal_digits_bound(abs(c), limit as nat);
    }
}

/// Unary minus on a value of class `a` meets `neg_op` (and its domain condition when it fits).
pub proof fn lemma_neg_op(k: NumKind, a: VClass, v: Val)
    requires in_class(v, a), neg_op(k, a) is Some,
    ensures
        op_sound(neg(k, v), neg_op(k, a)->Some_0),
        neg_op(k, a)->Some_0.fits ==> neg_fits(k, v),
{
    match (k, a.kind) {
        (_, VKind::NoValue) => {},
        (NumKind::Int4, VKind::Int { mag }) | (NumKind::Int8, VKind::Int { mag }) => {
            if let Val::Int(x) = v {
                lemma_int_result(int_kind_of(k), -x, mag as int, a.nullable);
            }
        },
        (NumKind::Numeric, VKind::Num { scale, digits }) => {
            if let Val::Num { coeff, scale: s } = v {
                match digits {
                    Some(d) => lemma_num_result(-coeff, scale, d as int, a.nullable),
                    None => lemma_num_unbounded(-coeff, scale, a.nullable),
                }
            }
        },
        (NumKind::Numeric, VKind::NumAny) => {},
        _ => {},
    }
}

/// `|x op y|` from `|x| <= a` and `|y| <= b`.
pub proof fn lemma_int_arith_bound(op: ArithOp, x: int, y: int, a: int, b: int)
    requires abs(x) <= a, abs(y) <= b,
    ensures abs(int_arith(op, x, y)) <= match op { ArithOp::Mul => a * b, _ => a + b },
{
    if op is Mul {
        assert(abs(x * y) == abs(x) * abs(y)) by (nonlinear_arith);
        assert(abs(x) * abs(y) <= a * b) by (nonlinear_arith) requires 0 <= abs(x) <= a, 0 <= abs(y) <= b;
    }
}

/// `|c1 * c2| < 10^(d1 + d2)`.
pub proof fn lemma_mul_digits(c1: int, d1: nat, c2: int, d2: nat)
    requires abs(c1) < pow10(d1), abs(c2) < pow10(d2),
    ensures abs(c1 * c2) < pow10(d1 + d2),
{
    lemma_pow10_add(d1, d2);
    let (x, y, px, py) = (abs(c1), abs(c2), pow10(d1), pow10(d2));
    assert(abs(c1 * c2) == x * y) by (nonlinear_arith) requires x == abs(c1), y == abs(c2);
    assert(x * y < px * py) by (nonlinear_arith) requires 0 <= x < px, 0 <= y < py;
}

/// `|c * 10^k| < 10^(d + k)`.
pub proof fn lemma_align_digits(c: int, d: nat, k: nat)
    requires abs(c) < pow10(d),
    ensures abs(c * pow10(k)) < pow10(d + k), pow10(k) >= 1,
{
    lemma_pow10_add(d, k);
    lemma_pow10_positive(k);
    let (x, p, q) = (abs(c), pow10(d), pow10(k));
    assert(abs(c * q) == x * q) by (nonlinear_arith) requires x == abs(c), q >= 1;
    assert(x * q < p * q) by (nonlinear_arith) requires 0 <= x < p, q >= 1;
}

/// Sum or difference of numerics aligned to the common scale.
pub proof fn lemma_addsub_digits(op: ArithOp, c1: int, s1: nat, d1: nat, c2: int, s2: nat, d2: nat)
    requires !(op is Mul), abs(c1) < pow10(d1), abs(c2) < pow10(d2),
    ensures ({
        let s = max_nat(s1, s2);
        let da = d1 + (s - s1);
        let db = d2 + (s - s2);
        let d = (if da >= db { da } else { db }) + 1;
        &&& num_arith(op, c1, s1, c2, s2).1 == s
        &&& abs(num_arith(op, c1, s1, c2, s2).0) < pow10(d as nat)
        &&& abs(align(c1, s1, s)) < pow10(da as nat)
        &&& abs(align(c2, s2, s)) < pow10(db as nat)
        &&& pow10((s - s1) as nat) <= pow10(da as nat)
        &&& pow10((s - s2) as nat) <= pow10(db as nat)
    }),
{
    let s = max_nat(s1, s2);
    let (k1, k2) = ((s - s1) as nat, (s - s2) as nat);
    let da = d1 + k1;
    let db = d2 + k2;
    let m = if da >= db { da } else { db };
    lemma_align_digits(c1, d1, k1);
    lemma_align_digits(c2, d2, k2);
    lemma_pow10_monotone(k1, da as nat);
    lemma_pow10_monotone(k2, db as nat);
    lemma_pow10_monotone(da as nat, m as nat);
    lemma_pow10_monotone(db as nat, m as nat);
    assert(pow10((m + 1) as nat) == 10 * pow10(m as nat));
    let (x, y) = (align(c1, s1, s), align(c2, s2, s));
    assert(abs(x) < pow10(m as nat) && abs(y) < pow10(m as nat));
    assert(abs(x + y) < 2 * pow10(m as nat));
    assert(abs(x - y) < 2 * pow10(m as nat));
}

/// `x <= 10^38` fits `i128`.
pub proof fn lemma_fits_i128_digits(c: int, d: nat)
    requires abs(c) < pow10(d), d <= 38,
    ensures fits_i128(c),
{
    lemma_pow10_monotone(d, 38);
    lemma_pow10_i128_boundary();
}

/// `a op b` on values of classes `a`, `b` meets `arith_op` (and `arith_fits` when it fits).
pub proof fn lemma_arith_op(op: ArithOp, k: NumKind, a: VClass, b: VClass, va: Val, vb: Val)
    requires in_class(va, a), in_class(vb, b), arith_op(op, k, a, b) is Some,
    ensures
        op_sound(arith(op, k, va, vb), arith_op(op, k, a, b)->Some_0),
        arith_op(op, k, a, b)->Some_0.fits ==> arith_fits(op, k, va, vb),
{
    let nullable = a.nullable || b.nullable;
    let o = arith_op(op, k, a, b)->Some_0;
    match (k, a.kind, b.kind) {
        (NumKind::Int4, VKind::Int { mag: x }, VKind::Int { mag: y })
        | (NumKind::Int8, VKind::Int { mag: x }, VKind::Int { mag: y }) => {
            assert(o == int_result_info(int_kind_of(k), match op { ArithOp::Mul => x as int * y as int, _ => x as int + y as int }, nullable));
            if let (Val::Int(p), Val::Int(q)) = (va, vb) {
                lemma_int_arith_bound(op, p, q, x as int, y as int);
                let m = match op { ArithOp::Mul => x as int * y as int, _ => x as int + y as int };
                assert(x as int * y as int <= 0x8000_0000_0000_0000 * 0x8000_0000_0000_0000) by (nonlinear_arith)
                    requires 0 <= x <= 0x8000_0000_0000_0000, 0 <= y <= 0x8000_0000_0000_0000;
                assert(0 <= x as int * y as int) by (nonlinear_arith) requires 0 <= x, 0 <= y;
                lemma_int_result(int_kind_of(k), int_arith(op, p, q), m, nullable);
            } else {
                assert(va is Null || vb is Null);
                assert(o.cls.nullable == nullable);
            }
        },
        (NumKind::Numeric, VKind::Num { scale: s1, digits: d1 }, VKind::Num { scale: s2, digits: d2 }) => {
            if let (Val::Num { coeff: c1, scale: t1 }, Val::Num { coeff: c2, scale: t2 }) = (va, vb) {
                lemma_arith_num(op, a, b, c1, t1, c2, t2);
            } else {
                assert(va is Null || vb is Null);
                assert(o.cls.nullable == nullable);
            }
        },
        (NumKind::Numeric, VKind::Num { .. }, VKind::NumAny) | (NumKind::Numeric, VKind::NumAny, VKind::Num { .. })
        | (NumKind::Numeric, VKind::NumAny, VKind::NumAny) => {
            assert(o == num_any_info(nullable));
        },
        _ => {
            assert(o == null_info());
            assert(va is Null || vb is Null);
        },
    }
}

/// `lemma_arith_op` on two numerics of classes `Num`.
proof fn lemma_arith_num(op: ArithOp, a: VClass, b: VClass, c1: int, t1: nat, c2: int, t2: nat)
    requires
        in_class(Val::Num { coeff: c1, scale: t1 }, a),
        in_class(Val::Num { coeff: c2, scale: t2 }, b),
        a.kind is Num, b.kind is Num,
        arith_op(op, NumKind::Numeric, a, b) is Some,
    ensures
        op_sound(arith(op, NumKind::Numeric, Val::Num { coeff: c1, scale: t1 }, Val::Num { coeff: c2, scale: t2 }),
            arith_op(op, NumKind::Numeric, a, b)->Some_0),
        arith_op(op, NumKind::Numeric, a, b)->Some_0.fits
            ==> arith_fits(op, NumKind::Numeric, Val::Num { coeff: c1, scale: t1 }, Val::Num { coeff: c2, scale: t2 }),
{
    let nullable = a.nullable || b.nullable;
    let o = arith_op(op, NumKind::Numeric, a, b)->Some_0;
    if let (VKind::Num { scale: s1, digits: d1 }, VKind::Num { scale: s2, digits: d2 }) = (a.kind, b.kind) {
        assert(t1 == s1 as nat && t2 == s2 as nat);
        match op {
            ArithOp::Mul => {
                let s = s1 as int + s2 as int;
                match (d1, d2) {
                    (Some(x), Some(y)) => {
                        lemma_mul_digits(c1, x as nat, c2, y as nat);
                        lemma_num_result(c1 * c2, s as u32, x as int + y as int, nullable);
                        if o.fits {
                            assert(x as int + y as int <= 38);
                            lemma_fits_i128_digits(c1 * c2, (x + y) as nat);
                            assert(t1 + t2 <= u32::MAX);
                            assert(num_arith_fits(op, c1, t1, c2, t2));
                        }
                    },
                    _ => lemma_num_unbounded(c1 * c2, s as u32, nullable),
                }
            },
            _ => {
                let s = if s1 >= s2 { s1 } else { s2 };
                let r = num_arith(op, c1, t1, c2, t2);
                assert(max_nat(t1, t2) == s as nat);
                match (d1, d2) {
                    (Some(x), Some(y)) => {
                        lemma_addsub_digits(op, c1, t1, x as nat, c2, t2, y as nat);
                        let da = x as int + (s as int - s1 as int);
                        let db = y as int + (s as int - s2 as int);
                        let d = (if da >= db { da } else { db }) + 1;
                        lemma_num_result(r.0, s, d, nullable);
                        if o.fits {
                            assert(d <= 38);
                            lemma_pow10_monotone(da as nat, 37);
                            lemma_pow10_monotone(db as nat, 37);
                            lemma_pow10_monotone(37, 38);
                            lemma_fits_i128_digits(align(c1, t1, s as nat), da as nat);
                            lemma_fits_i128_digits(align(c2, t2, s as nat), db as nat);
                            lemma_fits_i128_digits(r.0, d as nat);
                            lemma_pow10_i128_boundary();
                            lemma_pow10_positive((s as nat - t1) as nat);
                            lemma_pow10_positive((s as nat - t2) as nat);
                            assert(fits_i128(pow10((s as nat - t1) as nat)));
                            assert(fits_i128(pow10((s as nat - t2) as nat)));
                            assert(r.0 == num_arith(op, c1, t1, c2, t2).0);
                            assert(num_addsub_fits(op, c1, t1, c2, t2));
                        }
                    },
                    _ => lemma_num_unbounded(r.0, s, nullable),
                }
            },
        }
    }
}

/// Digits of a magnitude of at most `2^63`: at most 19.
pub proof fn lemma_mag_digits(m: u128)
    requires m as int <= int_mag_cap(),
    ensures mag_digits(m) <= 19, (m as int) < pow10(mag_digits(m)),
{
    assert(pow10(19) == 10000000000000000000) by (compute);
    lemma_decimal_digits_bound(m as int, 19);
    lemma_digits_of(m as int);
}

/// A cast of a value of class `a` meets `cast_op`.
pub proof fn lemma_cast_op(cast: CastOp, a: VClass, v: Val)
    requires in_class(v, a), cast_op(cast, a) is Some,
    ensures op_sound(crate::spec::scalar::cast(cast, v), cast_op(cast, a)->Some_0),
{
    if let (CastOp::IntToNumeric, VKind::Int { mag }) = (cast, a.kind) {
        lemma_mag_digits(mag);
    }
}

/// `timestamp + interval` on a value of class `a` meets `interval_op`.
pub proof fn lemma_interval_op(months: i32, days: i32, micros: i64, a: VClass, v: Val)
    requires in_class(v, a), interval_op(months, days, micros, a) is Some,
    ensures op_sound(add_interval(v, months, days, micros), interval_op(months, days, micros, a)->Some_0),
{
}

// ------------------------------------------------------------------------------------- scalar functions

/// A closed argument evaluates to its hoisted value in every environment.
pub proof fn lemma_closed_value(db: Database, env: Row, e: Expr)
    requires closed_value(e) is Some,
    ensures eval_expr(db, env, e) == Ok::<Val, SqlError>(closed_value(e)->Some_0),
{
    lemma_expr_closed(db, env, e);
}

/// The values of an evaluated list, by index.
pub proof fn lemma_exprs_values(db: Database, env: Row, es: Seq<Expr>, vs: Row)
    requires eval_exprs(db, env, es) == Ok::<Row, SqlError>(vs),
    ensures vs.len() == es.len(), forall|k: int| 0 <= k < es.len() ==> #[trigger] eval_expr(db, env, es[k]) == Ok::<Val, SqlError>(vs[k]),
{
    hide(eval_expr);
    let rs = expr_results(db, env, es);
    assert(eval_exprs(db, env, es) == collect(rs));
    lemma_collect_ok(rs);
    lemma_expr_results_index(db, env, es);
    assert forall|k: int| 0 <= k < es.len() implies #[trigger] eval_expr(db, env, es[k]) == Ok::<Val, SqlError>(vs[k]) by {
        assert(rs[k] == eval_expr(db, env, es[k]));
        assert(rs[k] == Ok::<Val, SqlError>(vs[k]));
    }
}

/// A scalar function on argument values of classes `cs` meets `call_op` (hoisted constant arguments are the evaluated ones).
pub proof fn lemma_call_op(db: Database, env: Row, f: ScalarFn, args: Seq<Expr>, cs: Seq<VClass>, vs: Row)
    requires
        eval_exprs(db, env, args) == Ok::<Row, SqlError>(vs),
        row_in(vs, cs),
        call_op(f, args, cs) is Some,
    ensures
        op_sound(apply_fn(f, vs), call_op(f, args, cs)->Some_0),
        fits_fn(f, vs),
{
    lemma_exprs_values(db, env, args, vs);
    let o = call_op(f, args, cs)->Some_0;
    assert forall|k: int| 0 <= k < vs.len() && (#[trigger] vs[k]) is Null implies any_nullable(cs) by {
        assert(in_class(vs[k], cs[k]));
        lemma_any_nullable(cs, k);
    }
    match f {
        ScalarFn::Like => {
            let (pv, ev) = (closed_value(args[1])->Some_0, closed_value(args[2])->Some_0);
            lemma_closed_value(db, env, args[1]);
            lemma_closed_value(db, env, args[2]);
            if let (Val::Text(p), Val::Text(e)) = (pv, ev) {
                assert(vs[1] == pv && vs[2] == ev);
                let toks = like_tokens(chars(p), escape_of(chars(e)), 0);
                lemma_none_dangling(toks);
                if let Val::Text(sb) = vs[0] {
                    lemma_like_mt_std(chars(sb), toks);
                }
                assert(in_class(vs[0], cs[0]));
            }
        },
        ScalarFn::Substring2 | ScalarFn::Substring3 => {
            assert(in_class(vs[0], cs[0]) && in_class(vs[1], cs[1]));
            if f is Substring3 {
                assert(in_class(vs[2], cs[2]));
                if closed_value(args[2]) is Some {
                    lemma_closed_value(db, env, args[2]);
                }
            }
            if exists|k: int| 0 <= k < vs.len() && #[trigger] vs[k] is Null {
                let k = choose|k: int| 0 <= k < vs.len() && #[trigger] vs[k] is Null;
                assert(any_nullable(cs));
            }
        },
        ScalarFn::ExtractYear | ScalarFn::ExtractMonth | ScalarFn::ExtractDay => {
            assert(in_class(vs[0], cs[0]));
            if vs[0] is Null {
                assert(any_nullable(cs));
            }
        },
        ScalarFn::PadBpchar => {
            assert(in_class(vs[0], cs[0]) && in_class(vs[1], cs[1]));
            if vs[0] is Null || vs[1] is Null {
                assert(any_nullable(cs));
            }
        },
        _ => {},
    }
}

/// `none_dangling` is `no_dangling`.
pub proof fn lemma_none_dangling(ts: Seq<LikeTok>)
    requires none_dangling(ts),
    ensures no_dangling(ts),
    decreases ts.len(),
{
    if ts.len() > 0 {
        lemma_none_dangling(ts.drop_last());
        assert forall|k: int| 0 <= k < ts.len() implies !(#[trigger] ts[k] is Dangling) by {
            if k < ts.len() - 1 {
                assert(ts.drop_last()[k] == ts[k]);
            }
        }
    }
}

// ------------------------------------------------------------------------------------- comparisons and CASE

/// Values of comparable classes compare without a type error.
pub proof fn lemma_comparable(op: CmpOp, va: Val, a: VClass, vb: Val, b: VClass)
    requires in_class(va, a), in_class(vb, b), comparable(a.kind, b.kind),
    ensures cmp_truth(op, va, vb) is Ok,
{
}

/// `v op ANY (rows)` of a value comparable with the rows' single column raises no error.
pub proof fn lemma_any_cmp_ok(op: CmpOp, v: Val, a: VClass, rows: Seq<Row>, c: VClass)
    requires in_class(v, a), comparable(a.kind, c.kind), rows_in(rows, seq![c]),
    ensures any_cmp_truth(op, v, rows) is Ok,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let d = rows.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies row_in(#[trigger] d[i], seq![c]) by {
            assert(d[i] == rows[i]);
        }
        lemma_any_cmp_ok(op, v, a, d, c);
        let last = rows[rows.len() - 1];
        assert(row_in(last, seq![c]));
        assert(first_col(rows.last()) == Ok::<Val, SqlError>(last[0]));
        lemma_comparable(op, v, a, last[0], c);
    }
}

/// A value of either branch class lies in the joined class.
pub proof fn lemma_class_join(v: Val, a: VClass, b: VClass)
    requires class_join(a, b) is Some, in_class(v, a) || in_class(v, b),
    ensures in_class(v, class_join(a, b)->Some_0),
{
    if let Val::Num { coeff, scale } = v {
        if let (VKind::Num { scale: s1, digits: Some(x) }, VKind::Num { scale: s2, digits: Some(y) }) = (a.kind, b.kind) {
            lemma_pow10_monotone(x as nat, if x >= y { x as nat } else { y as nat });
            lemma_pow10_monotone(y as nat, if x >= y { x as nat } else { y as nat });
        }
    }
}

// ------------------------------------------------------------------------------------- aggregate values

/// Every value is in class `c`.
pub open spec fn vals_in(vs: Seq<Val>, c: VClass) -> bool {
    forall|i: int| 0 <= i < vs.len() ==> in_class(#[trigger] vs[i], c)
}

proof fn lemma_vals_in_prefix(vs: Seq<Val>, c: VClass)
    requires vals_in(vs, c), vs.len() > 0,
    ensures vals_in(vs.drop_last(), c), in_class(vs.last(), c),
{
    assert forall|i: int| 0 <= i < vs.drop_last().len() implies in_class(#[trigger] vs.drop_last()[i], c) by {
        assert(vs.drop_last()[i] == vs[i]);
    }
    assert(in_class(vs[vs.len() - 1], c));
}

/// Values of a class matching the operand kind are all of that kind (SUM / AVG accept them).
pub proof fn lemma_all_of_kind(kind: NumKind, vs: Seq<Val>, c: VClass)
    requires
        vals_in(vs, c),
        match (kind, c.kind) {
            (_, VKind::NoValue) => true,
            (NumKind::Int4, VKind::Int { .. }) | (NumKind::Int8, VKind::Int { .. }) => true,
            (NumKind::Numeric, VKind::Num { .. }) | (NumKind::Numeric, VKind::NumAny) => true,
            _ => false,
        },
    ensures all_of_kind(kind, vs),
    decreases vs.len(),
{
    if vs.len() > 0 {
        lemma_vals_in_prefix(vs, c);
        lemma_all_of_kind(kind, vs.drop_last(), c);
    }
}

/// All-NULL values: no count, no mass.
pub proof fn lemma_all_null(vs: Seq<Val>, t: nat)
    requires forall|i: int| 0 <= i < vs.len() ==> #[trigger] vs[i] is Null,
    ensures count_non_null(vs) == 0, int_mass(vs) == 0, num_mass_at(vs, t) == 0, num_max_scale(vs) == 0,
    decreases vs.len(),
{
    if vs.len() > 0 {
        assert forall|i: int| 0 <= i < vs.drop_last().len() implies #[trigger] vs.drop_last()[i] is Null by {
            assert(vs.drop_last()[i] == vs[i]);
        }
        lemma_all_null(vs.drop_last(), t);
        assert(vs[vs.len() - 1] is Null);
    }
}

/// Values of a class with some non-NULL value: one non-NULL value exists.
pub proof fn lemma_non_null_witness(vs: Seq<Val>) -> (i: int)
    requires count_non_null(vs) > 0,
    ensures 0 <= i < vs.len(), !(vs[i] is Null),
    decreases vs.len(),
{
    if !(vs.last() is Null) {
        vs.len() - 1
    } else {
        let i = lemma_non_null_witness(vs.drop_last());
        assert(vs.drop_last()[i] == vs[i]);
        i
    }
}

/// The running extremum over values of a (non-boolean) class never errs and stays in the class.
pub proof fn lemma_extremum_class(max: bool, vs: Seq<Val>, c: VClass)
    requires vals_in(vs, c), !(c.kind is Bool),
    ensures extremum(max, vs) is Ok, in_class(extremum(max, vs)->Ok_0, VClass { kind: c.kind, nullable: true }),
    decreases vs.len(),
{
    if vs.len() > 0 {
        lemma_vals_in_prefix(vs, c);
        lemma_extremum_class(max, vs.drop_last(), c);
        let acc = extremum(max, vs.drop_last())->Ok_0;
        let v = vs.last();
        if !(v is Null) && !(acc is Null) {
            let cn = VClass { kind: c.kind, nullable: true };
            assert(comparable(c.kind, c.kind));
            lemma_comparable(CmpOp::Eq, v, c, acc, cn);
        }
    }
}

/// Numeric values of one scale `s` with a non-NULL value sum at scale `s`.
pub proof fn lemma_num_sum_scale(vs: Seq<Val>, c: VClass, s: u32)
    requires vals_in(vs, c), c.kind matches VKind::Num { scale, .. } && scale == s, count_non_null(vs) > 0,
    ensures num_sum(vs).1 == s as nat,
{
    assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i] matches Val::Num { coeff, scale } ==> scale == s as nat) by {
        assert(in_class(vs[i], c));
    }
    lemma_num_mass_uniform(vs, s as nat);
    let i = lemma_non_null_witness(vs);
    assert(in_class(vs[i], c));
    assert(vs[i] is Num);
    lemma_num_sum_bound(vs);
}

/// An aggregate over values of class `c` meets `agg_value_info` (and `fits_agg_value` when it fits).
pub proof fn lemma_agg_value(a: Agg, vs: Seq<Val>, c: VClass)
    requires vals_in(vs, c), agg_value_info(a, c) is Some,
    ensures
        op_sound(agg_value(a, vs), agg_value_info(a, c)->Some_0),
        agg_value_info(a, c)->Some_0.fits ==> fits_agg_value(a, vs),
    decreases a,
{
    let o = agg_value_info(a, c)->Some_0;
    match a {
        Agg::CountStar => {},
        Agg::Count(_) => {},
        Agg::Sum { kind, arg } => {
            lemma_all_of_kind(kind, vs, c);
            if c.kind is NoValue {
                assert forall|i: int| 0 <= i < vs.len() implies #[trigger] vs[i] is Null by {
                    assert(in_class(vs[i], c));
                }
                lemma_all_null(vs, 0);
            } else if count_non_null(vs) > 0 {
                match (kind, c.kind) {
                    (NumKind::Int4, _) => {
                        lemma_int_result(IntKind::Int8, int_sum(vs), 0x8000_0000_0000_0000int, true);
                    },
                    (NumKind::Int8, _) => lemma_num_unbounded(int_sum(vs), 0, true),
                    (NumKind::Numeric, VKind::Num { scale, .. }) => {
                        lemma_num_sum_scale(vs, c, scale);
                        lemma_num_unbounded(num_sum(vs).0, scale, true);
                    },
                    _ => {},
                }
            }
        },
        Agg::Avg { kind, arg } => {
            lemma_all_of_kind(kind, vs, c);
            if c.kind is NoValue {
                assert forall|i: int| 0 <= i < vs.len() implies #[trigger] vs[i] is Null by {
                    assert(in_class(vs[i], c));
                }
                lemma_all_null(vs, 0);
            }
        },
        Agg::Min(_) => lemma_extremum_class(false, vs, c),
        Agg::Max(_) => lemma_extremum_class(true, vs, c),
        Agg::DistinctAgg(inner) => {
            let d = distinct_vals(vs);
            lemma_distinct_vals_sub(vs);
            assert forall|i: int| 0 <= i < d.len() implies in_class(#[trigger] d[i], c) by {
                let j = choose|j: int| 0 <= j < vs.len() && vs[j] == d[i];
            }
            lemma_agg_value(*inner, d, c);
        },
    }
}

} // verus!
