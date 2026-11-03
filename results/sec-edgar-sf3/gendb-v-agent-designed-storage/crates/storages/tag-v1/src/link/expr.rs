//! Per-row expression and condition lemmas (optional author toolkit; nothing here names a query, a table or a
//! column). An author who restates a row condition, key or argument in their own terms uses these to show that it
//! equals the VERUS_SQL evaluation (`spec::eval::eval_expr`, `eval_pred`) on every row they cover.
//!
//! - Value helpers: `ival` (the integer a value carries), `tval` (the bytes of a text value), `int_cmp` /
//!   `text_cmp` (two-valued comparisons), `fits_i128`, `text_ok_rec` (a NUL-free literal, decidable by `compute`).
//! - Expressions: columns, text literals, closed (literal-only) expressions, which are evaluated once in the empty
//!   database (`closed_db`, `lemma_expr_closed`), and numeric alignment.
//! - Conditions: comparisons of every admitted type pair (integer, numeric, date, a date against a timestamp at
//!   midnight, text in byte order) and the Kleene connectives on two-valued truths.
//! - Totality: every lemma concludes `Ok(..)` for its node. A condition proved this way evaluates without an SQL error
//!   on every row it covers, not only on qualifying rows, which is what lets an implementation move or split the
//!   condition without changing the query's error behaviour.
//! - `collect`: `lemma_collect_all_ok` and `lemma_collect_pointwise` are this module's names for
//!   `bridge::collect::lemma_collect_all` and `bridge::collect::lemma_collect_pointwise` (re-exports, one
//!   proof each); `lemma_lex_cmp_zero` is `bridge::equality::lemma_lex_cmp_zero`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::datetime::*;
use crate::spec::text::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::typing::*;

/// `collect` of all-`Ok` elements is `Ok` of their values (`bridge::collect::lemma_collect_all`).
pub use crate::bridge::collect::lemma_collect_all as lemma_collect_all_ok;
/// `collect` depends only on the elements (`bridge::collect::lemma_collect_pointwise`).
pub use crate::bridge::collect::lemma_collect_pointwise;
/// `lex_cmp` is `-1`, `0` or `1`, and `0` exactly on equal byte strings (`bridge::equality::lemma_lex_cmp_zero`).
pub use crate::bridge::equality::lemma_lex_cmp_zero;

verus! {

// ------------------------------------------------------------------------------------------ value helpers

/// The integer carried by a value: numeric coefficient, integer, day or microsecond count (0 otherwise).
pub open spec fn ival(v: Val) -> int {
    match v {
        Val::Num { coeff, .. } => coeff,
        Val::Int(x) => x,
        Val::Date(d) => d,
        Val::Ts(t) => t,
        _ => 0,
    }
}

/// The bytes of a text value (empty otherwise).
pub open spec fn tval(v: Val) -> Seq<u8> {
    match v {
        Val::Text(b) => b,
        _ => Seq::empty(),
    }
}

/// `i128::MAX` as an integer.
pub open spec fn i128_max() -> int {
    0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
}

/// `i128::MIN` as an integer.
pub open spec fn i128_min() -> int {
    -0x8000_0000_0000_0000_0000_0000_0000_0000
}

/// Exact value inside the `i128` range (what checked `i128` arithmetic computes without overflow).
pub open spec fn fits_i128(x: int) -> bool {
    i128_min() <= x <= i128_max()
}

/// Two-valued integer comparison, indexed by the VERUS_SQL operator.
pub open spec fn int_cmp(op: CmpOp, x: int, y: int) -> bool {
    match op {
        CmpOp::Eq => x == y,
        CmpOp::Ne => x != y,
        CmpOp::Lt => x < y,
        CmpOp::Le => x <= y,
        CmpOp::Gt => x > y,
        CmpOp::Ge => x >= y,
    }
}

/// Two-valued text comparison in byte order (`spec::text::lex_cmp`, the VERUS_SQL text order); equality and
/// inequality are stated as sequence (in)equality.
pub open spec fn text_cmp(op: CmpOp, a: Seq<u8>, b: Seq<u8>) -> bool {
    match op {
        CmpOp::Eq => a == b,
        CmpOp::Ne => a != b,
        CmpOp::Lt => lex_cmp(a, b) < 0,
        CmpOp::Le => lex_cmp(a, b) <= 0,
        CmpOp::Gt => lex_cmp(a, b) > 0,
        CmpOp::Ge => lex_cmp(a, b) >= 0,
    }
}

/// The text comparison is the SQL comparison's truth for every operator.
pub proof fn lemma_text_cmp_holds(op: CmpOp, a: Seq<u8>, b: Seq<u8>)
    ensures cmp_holds(op, lex_cmp(a, b)) == text_cmp(op, a, b),
{
    lemma_lex_cmp_zero(a, b);
}

/// Text without a NUL byte, decided by recursion (so `by (compute)` decides it for a literal).
pub open spec fn text_ok_rec(b: Seq<u8>) -> bool
    decreases b.len(),
{
    b.len() == 0 || (b.last() != 0u8 && text_ok_rec(b.drop_last()))
}

/// `text_ok_rec` is `spec::text::text_ok`.
pub proof fn lemma_text_ok_rec(b: Seq<u8>)
    requires text_ok_rec(b),
    ensures text_ok(b),
    decreases b.len(),
{
    if b.len() > 0 {
        let d = b.drop_last();
        lemma_text_ok_rec(d);
        assert forall|i: int| 0 <= i < b.len() implies #[trigger] b[i] != 0u8 by {
            if i < d.len() {
                assert(b[i] == d[i]);
            }
        }
    }
}

// ------------------------------------------------------------------------------------ per-row expressions

/// Expressions without column references.
pub open spec fn closed_expr(e: Expr) -> bool
    decreases e,
{
    match e {
        Expr::Col(_) => false,
        Expr::Lit(_) => true,
        Expr::Neg { kind, arg } => closed_expr(*arg),
        Expr::Arith { op, kind, a, b } => closed_expr(*a) && closed_expr(*b),
        Expr::Cast { cast, arg } => closed_expr(*arg),
        Expr::AddInterval { arg, months, days, micros } => closed_expr(*arg),
        // Not treated as closed (conservative: `lemma_expr_closed` covers the arithmetic fragment only).
        Expr::Call { .. } => false,
        Expr::If { .. } => false,
        Expr::Subquery(_) => false,
    }
}

/// The database in which closed (literal-only) expressions are evaluated once; closed expressions do not read
/// the database (`lemma_expr_closed`).
pub open spec fn closed_db() -> Database {
    Database { schema: Seq::empty(), tables: Seq::empty() }
}

/// A column reference inside the environment.
pub proof fn lemma_expr_col(db: Database, env: Row, i: nat)
    requires i < env.len(),
    ensures eval_expr(db, env, Expr::Col(i)) == Ok::<Val, SqlError>(env[i as int]),
{
}

/// A text literal is its bytes.
pub proof fn lemma_expr_text(db: Database, env: Row, b: Seq<u8>)
    ensures eval_expr(db, env, Expr::Lit(Literal::Text(b))) == Ok::<Val, SqlError>(Val::Text(b)),
{
}

/// A closed expression has the same value in every environment and database (so its value can be computed once).
pub proof fn lemma_expr_closed(db: Database, env: Row, e: Expr)
    requires closed_expr(e),
    ensures eval_expr(db, env, e) == eval_expr(closed_db(), Seq::empty(), e),
    decreases e,
{
    match e {
        Expr::Neg { kind, arg } => lemma_expr_closed(db, env, *arg),
        Expr::Arith { op, kind, a, b } => {
            lemma_expr_closed(db, env, *a);
            lemma_expr_closed(db, env, *b);
        },
        Expr::Cast { cast, arg } => lemma_expr_closed(db, env, *arg),
        Expr::AddInterval { arg, months, days, micros } => lemma_expr_closed(db, env, *arg),
        _ => {},
    }
}

/// Aligned coefficient with a known power of ten.
pub proof fn lemma_align_by(c: int, from: nat, to: nat, f: int)
    requires from <= to, pow10((to - from) as nat) == f,
    ensures align(c, from, to) == c * f,
{
}

/// Aligned coefficient at the same scale.
pub proof fn lemma_align_same(c: int, s: nat)
    ensures align(c, s, s) == c,
{
    assert((s - s) as nat == 0nat);
    assert(pow10(0) == 1);
}

// ------------------------------------------------------------------------------------- per-row conditions

/// A comparison outcome `sign(x - y)` holds exactly when `int_cmp` does.
pub proof fn lemma_cmp_holds_sign(op: CmpOp, x: int, y: int)
    ensures cmp_holds(op, sign(x - y)) == int_cmp(op, x, y),
{
}

/// Exact order of two decimals: the integer order of their coefficients at the common scale.
pub proof fn lemma_compare_num(c1: int, s1: nat, c2: int, s2: nat)
    ensures
        compare(Val::Num { coeff: c1, scale: s1 }, Val::Num { coeff: c2, scale: s2 })
            == Some(sign(align(c1, s1, max_nat(s1, s2)) - align(c2, s2, max_nat(s1, s2)))),
{
}

/// Integers compare by their difference.
pub proof fn lemma_compare_int(x: int, y: int)
    ensures compare(Val::Int(x), Val::Int(y)) == Some(sign(x - y)),
{
}

/// Dates compare by their day counts.
pub proof fn lemma_compare_date(x: int, y: int)
    ensures compare(Val::Date(x), Val::Date(y)) == Some(sign(x - y)),
{
}

/// A date against a timestamp at midnight of day `k` is the order of the day counts.
pub proof fn lemma_compare_date_midnight(d: int, k: int)
    ensures
        compare(Val::Date(d), Val::Ts(k * usecs_per_day())) == Some(sign(d - k)),
        compare(Val::Ts(k * usecs_per_day()), Val::Date(d)) == Some(sign(k - d)),
{
    let u = usecs_per_day();
    assert(date_as_usecs(d) == d * u);
    assert(d * u - k * u == (d - k) * u) by (nonlinear_arith);
    assert(k * u - d * u == (k - d) * u) by (nonlinear_arith);
    assert(u > 0);
    if d - k > 0 {
        assert((d - k) * u > 0) by (nonlinear_arith) requires d - k > 0, u > 0;
        assert((k - d) * u < 0) by (nonlinear_arith) requires k - d < 0, u > 0;
    } else if d - k < 0 {
        assert((d - k) * u < 0) by (nonlinear_arith) requires d - k < 0, u > 0;
        assert((k - d) * u > 0) by (nonlinear_arith) requires k - d > 0, u > 0;
    }
}

/// A comparison of two non-NULL values ordered like the integers `x`, `y` is the two-valued `int_cmp`.
pub proof fn lemma_pred_cmp(db: Database, env: Row, op: CmpOp, a: Expr, b: Expr, va: Val, vb: Val, x: int, y: int)
    requires
        eval_expr(db, env, a) == Ok::<Val, SqlError>(va),
        eval_expr(db, env, b) == Ok::<Val, SqlError>(vb),
        !(va is Null),
        !(vb is Null),
        compare(va, vb) == Some(sign(x - y)),
    ensures
        eval_pred(db, env, Pred::Cmp { op, a, b }) == Ok::<Truth, SqlError>(truth_of(int_cmp(op, x, y))),
{
    lemma_cmp_holds_sign(op, x, y);
}

/// A comparison of two text values is the two-valued `text_cmp` of their bytes.
pub proof fn lemma_pred_text_cmp(db: Database, env: Row, op: CmpOp, a: Expr, b: Expr, x: Seq<u8>, y: Seq<u8>)
    requires
        eval_expr(db, env, a) == Ok::<Val, SqlError>(Val::Text(x)),
        eval_expr(db, env, b) == Ok::<Val, SqlError>(Val::Text(y)),
    ensures
        eval_pred(db, env, Pred::Cmp { op, a, b }) == Ok::<Truth, SqlError>(truth_of(text_cmp(op, x, y))),
{
    lemma_text_cmp_holds(op, x, y);
}

/// Kleene AND of two-valued truths is Boolean AND.
pub proof fn lemma_pred_and(db: Database, env: Row, a: Pred, b: Pred, x: bool, y: bool)
    requires
        eval_pred(db, env, a) == Ok::<Truth, SqlError>(truth_of(x)),
        eval_pred(db, env, b) == Ok::<Truth, SqlError>(truth_of(y)),
    ensures
        eval_pred(db, env, Pred::And(Box::new(a), Box::new(b))) == Ok::<Truth, SqlError>(truth_of(x && y)),
{
}

/// Kleene OR of two-valued truths is Boolean OR.
pub proof fn lemma_pred_or(db: Database, env: Row, a: Pred, b: Pred, x: bool, y: bool)
    requires
        eval_pred(db, env, a) == Ok::<Truth, SqlError>(truth_of(x)),
        eval_pred(db, env, b) == Ok::<Truth, SqlError>(truth_of(y)),
    ensures
        eval_pred(db, env, Pred::Or(Box::new(a), Box::new(b))) == Ok::<Truth, SqlError>(truth_of(x || y)),
{
}

/// Kleene NOT of a two-valued truth is Boolean NOT.
pub proof fn lemma_pred_not(db: Database, env: Row, a: Pred, x: bool)
    requires eval_pred(db, env, a) == Ok::<Truth, SqlError>(truth_of(x)),
    ensures eval_pred(db, env, Pred::Not(Box::new(a))) == Ok::<Truth, SqlError>(truth_of(!x)),
{
}

} // verus!
