//! Checked examples of the structural constructors: scalar-subquery cardinality, the three-valued `ANY` quantifier
//! behind IN / NOT IN, lazy CASE and SELECT DISTINCT by value equality (PostgreSQL reference fixture `cov_s`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::equality::*;
use crate::spec::int::*;

verus! {

/// No row is NULL, one row is its column, two rows raise 21000.
pub proof fn pin_subquery_value() {
    assert(subquery_value(Seq::empty()) == Ok::<Val, SqlError>(Val::Null));
    assert(subquery_value(seq![seq![Val::Int(7)]]) == Ok::<Val, SqlError>(Val::Int(7)));
    assert(subquery_value(seq![seq![Val::Int(7)], seq![Val::Int(7)]]) == Err::<Val, SqlError>(SqlError::CardinalityViolation));
}

/// `2 IN (1, NULL)` is Unknown, so `2 NOT IN (1, NULL)` is Unknown too; `1 IN (1, NULL)` is True; anything
/// (even NULL) `IN` the empty set is False, so `NOT IN` of the empty set is True.
pub proof fn pin_any_cmp_3vl() {
    let r1 = seq![Val::Int(1)];
    let rn = seq![Val::Null];
    let one = seq![r1];
    let rows = seq![r1, rn];
    assert(rows.drop_last() =~= one);
    assert(one.drop_last() =~= Seq::<Row>::empty());
    assert(rows.last() == rn && one.last() == r1);
    assert(first_col(r1) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(first_col(rn) == Ok::<Val, SqlError>(Val::Null));
    assert(any_cmp_truth(CmpOp::Eq, Val::Null, Seq::empty()) == Ok::<Truth, SqlError>(Truth::False));
    // 2 IN (1, NULL)
    assert(compare(Val::Int(2), Val::Int(1)) == Some(1int));
    assert(cmp_truth(CmpOp::Eq, Val::Int(2), Val::Int(1)) == Ok::<Truth, SqlError>(Truth::False));
    assert(any_cmp_truth(CmpOp::Eq, Val::Int(2), Seq::empty()) == Ok::<Truth, SqlError>(Truth::False));
    assert(any_cmp_truth(CmpOp::Eq, Val::Int(2), one) == Ok::<Truth, SqlError>(Truth::False));
    assert(cmp_truth(CmpOp::Eq, Val::Int(2), Val::Null) == Ok::<Truth, SqlError>(Truth::Unknown));
    assert(any_cmp_truth(CmpOp::Eq, Val::Int(2), rows) == Ok::<Truth, SqlError>(Truth::Unknown));
    assert(truth_not(Truth::Unknown) == Truth::Unknown);
    // 1 IN (1, NULL)
    assert(compare(Val::Int(1), Val::Int(1)) == Some(0int));
    assert(any_cmp_truth(CmpOp::Eq, Val::Int(1), Seq::empty()) == Ok::<Truth, SqlError>(Truth::False));
    assert(any_cmp_truth(CmpOp::Eq, Val::Int(1), one) == Ok::<Truth, SqlError>(Truth::True));
    assert(any_cmp_truth(CmpOp::Eq, Val::Int(1), rows) == Ok::<Truth, SqlError>(Truth::True));
}

/// CASE is lazy: the ELSE branch (an out-of-range column reference, whose value would be an error) is not
/// evaluated when the condition is True.
pub proof fn pin_if_lazy(db: Database) {
    let one = Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 });
    let cond = Pred::Cmp { op: CmpOp::Eq, a: one, b: one };
    let e = Expr::If { cond: Box::new(cond), then_e: Box::new(one), else_e: Box::new(Expr::Col(99)) };
    let env = Seq::<Val>::empty();
    assert(int_in_range(IntKind::Int4, 1));
    assert(eval_expr(db, env, one) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(eval_expr(db, env, Expr::Col(99)) is Err);
    assert(compare(Val::Int(1), Val::Int(1)) == Some(0int));
    assert(eval_pred(db, env, cond) == Ok::<Truth, SqlError>(Truth::True));
    assert(eval_expr(db, env, e) == Ok::<Val, SqlError>(Val::Int(1)));
}

/// DISTINCT keeps the first row of each class of not-distinct rows: NULLs together, duplicates once.
pub proof fn pin_distinct_rows() {
    let a = seq![Val::Null, Val::Int(1)];
    let b = seq![Val::Int(2), Val::Int(1)];
    let ab = seq![a, b];
    let rows = seq![a, b, a];
    assert(val_not_distinct(Val::Null, Val::Null));
    assert(compare(Val::Int(1), Val::Int(1)) == Some(0int));
    assert(val_not_distinct(a[1], a[1]));
    assert(row_not_distinct(a, a));
    assert(!val_not_distinct(b[0], a[0]));
    assert(!row_not_distinct(b, a));
    assert(!row_not_distinct(a, b));
    assert(rows.drop_last() =~= ab);
    assert(ab.drop_last() =~= seq![a]);
    assert(seq![a].drop_last() =~= Seq::<Row>::empty());
    assert(seq![a].last() == a && ab.last() == b && rows.last() == a);
    assert(distinct_rows(Seq::<Row>::empty()) =~= Seq::<Row>::empty());
    assert(!has_not_distinct(Seq::<Row>::empty(), a));
    assert(distinct_rows(seq![a]) =~= seq![a]);
    assert(!has_not_distinct(Seq::<Row>::empty(), b));
    assert(!has_not_distinct(seq![a], b));
    assert(distinct_rows(ab) =~= ab);
    assert(has_not_distinct(seq![a], a));
    assert(has_not_distinct(ab, a));
    assert(distinct_rows(rows) =~= ab);
}

} // verus!
