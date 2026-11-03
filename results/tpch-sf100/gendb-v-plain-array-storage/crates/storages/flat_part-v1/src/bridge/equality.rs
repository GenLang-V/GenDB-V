//! Laws of SQL value equality (`spec::equality`): it is an equivalence relation on values and rows (so the
//! first-occurrence representatives of GROUP BY / DISTINCT are well defined as classes), and on values of one
//! exact type (same variant, and for numerics the same scale: every stored column and every core expression
//! before division/AVG) it coincides with structural equality, so the switch from structural to value equality
//! changes no result of the core fragment. Distinct rows are input rows.
//!
//! The laws on non-NULL values reduce to the comparison laws of `bridge::order` (`compare` is antisymmetric and
//! transitive within a comparison family), which is why this module depends on `order`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::text::*;
use crate::spec::equality::*;
use crate::bridge::order::*;

verus! {

/// Byte strings compare equal exactly when they are equal, and `lex_cmp` is `-1`, `0` or `1`. (Public: the link
/// toolkit re-exports it as `link::expr::lemma_lex_cmp_zero`, so the library has one proof of it.)
pub proof fn lemma_lex_cmp_zero(a: Seq<u8>, b: Seq<u8>)
    ensures (lex_cmp(a, b) == 0) == (a == b), -1 <= lex_cmp(a, b) <= 1,
    decreases a.len(),
{
    if a.len() == 0 || b.len() == 0 {
        if a.len() == 0 && b.len() == 0 {
            assert(a =~= b);
        }
    } else if a[0] == b[0] {
        let (ta, tb) = (a.drop_first(), b.drop_first());
        lemma_lex_cmp_zero(ta, tb);
        if ta == tb {
            assert(a =~= b) by {
                assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
                    if i > 0 {
                        assert(a[i] == ta[i - 1] && b[i] == tb[i - 1]);
                    }
                }
            }
        }
        if a == b {
            assert(ta =~= tb);
        }
    } else {
        assert(a != b) by {
            if a == b {
                assert(a[0] == b[0]);
            }
        }
    }
}

/// Reflexive on every value.
pub proof fn lemma_val_not_distinct_refl(a: Val)
    ensures val_not_distinct(a, a),
{
    if !(a is Null) {
        lemma_compare_antisym(a, a);
    }
}

/// Symmetric.
pub proof fn lemma_val_not_distinct_symm(a: Val, b: Val)
    requires val_not_distinct(a, b),
    ensures val_not_distinct(b, a),
{
    if !(a is Null) {
        lemma_compare_antisym(a, b);
    }
}

/// Transitive.
pub proof fn lemma_val_not_distinct_trans(a: Val, b: Val, c: Val)
    requires val_not_distinct(a, b), val_not_distinct(b, c),
    ensures val_not_distinct(a, c),
{
    if !(a is Null) {
        lemma_compare_antisym(a, b);
        lemma_compare_antisym(b, c);
        lemma_compare_antisym(a, c);
        lemma_compare_trans(a, b, c);
        lemma_compare_trans(c, b, a);
    }
}

/// Rows: reflexive, symmetric and transitive, column by column.
pub proof fn lemma_row_not_distinct_refl(r: Row)
    ensures row_not_distinct(r, r),
{
    assert forall|i: int| 0 <= i < r.len() implies val_not_distinct(#[trigger] r[i], r[i]) by {
        lemma_val_not_distinct_refl(r[i]);
    }
}

pub proof fn lemma_row_not_distinct_symm(r: Row, s: Row)
    requires row_not_distinct(r, s),
    ensures row_not_distinct(s, r),
{
    assert forall|i: int| 0 <= i < s.len() implies val_not_distinct(#[trigger] s[i], r[i]) by {
        lemma_val_not_distinct_symm(r[i], s[i]);
    }
}

pub proof fn lemma_row_not_distinct_trans(r: Row, s: Row, t: Row)
    requires row_not_distinct(r, s), row_not_distinct(s, t),
    ensures row_not_distinct(r, t),
{
    assert forall|i: int| 0 <= i < r.len() implies val_not_distinct(#[trigger] r[i], t[i]) by {
        lemma_val_not_distinct_trans(r[i], s[i], t[i]);
    }
}

/// Values of one exact type: the same variant, and for numerics the same scale.
pub open spec fn same_exact_type(a: Val, b: Val) -> bool {
    match (a, b) {
        (Val::Null, _) => true,
        (_, Val::Null) => true,
        (Val::Bool(_), Val::Bool(_)) => true,
        (Val::Int(_), Val::Int(_)) => true,
        (Val::Num { scale: s1, .. }, Val::Num { scale: s2, .. }) => s1 == s2,
        (Val::Date(_), Val::Date(_)) => true,
        (Val::Ts(_), Val::Ts(_)) => true,
        (Val::Text(_), Val::Text(_)) => true,
        _ => false,
    }
}

/// On values of one exact type, value equality is structural equality.
pub proof fn lemma_val_not_distinct_structural(a: Val, b: Val)
    requires same_exact_type(a, b),
    ensures val_not_distinct(a, b) == (a == b),
{
    match (a, b) {
        (Val::Num { coeff: c1, scale: s1 }, Val::Num { coeff: c2, scale: s2 }) => {
            assert(pow10(0) == 1);
            assert(align(c1, s1, s1) == c1);
            assert(align(c2, s2, s1) == c2);
        },
        (Val::Text(x), Val::Text(y)) => {
            lemma_lex_cmp_zero(x, y);
        },
        _ => {},
    }
}

/// Every row of `distinct_rows(rows)` (a class representative) is a row of `rows`.
pub proof fn lemma_distinct_rows_sub(rows: Seq<Row>)
    ensures
        forall|g: int| 0 <= g < distinct_rows(rows).len() ==> rows.contains(#[trigger] distinct_rows(rows)[g]),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let init = rows.drop_last();
        lemma_distinct_rows_sub(init);
        let d = distinct_rows(rows);
        assert forall|g: int| 0 <= g < d.len() implies rows.contains(#[trigger] d[g]) by {
            if g < distinct_rows(init).len() {
                let j = choose|j: int| 0 <= j < init.len() && init[j] == d[g];
                assert(rows[j] == d[g]);
            } else {
                assert(rows[rows.len() - 1] == d[g]);
            }
        }
    }
}

} // verus!
