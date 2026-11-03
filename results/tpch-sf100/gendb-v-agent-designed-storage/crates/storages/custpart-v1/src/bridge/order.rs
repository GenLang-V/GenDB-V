//! ORDER BY: the canonical output `denote_top` (stable insertion sort of the canonical body, then OFFSET/LIMIT)
//! is one of the outputs `ordered_ok` allows. The sort is correct because, on the rows of a checked query, the
//! key comparison is a total preorder: within one comparison family `compare` is antisymmetric and
//! transitive (exact numeric order across scales and int/numeric, exact date/timestamp order, bytewise text),
//! NULL placement and DESC preserve that, and lexicographic combination preserves it. Type soundness
//! (`bridge::typing`) supplies "one family per key column".
//!
//! Sections, bottom up: integer helpers (`lemma_pow10_add` is also used by `bridge::fns::div`, the exec
//! aggregates and `link`), value comparison laws (also used by `bridge::equality`), key comparison, the
//! insertion sort `sort_rows`, and the top-level theorem.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::datetime::*;
use crate::spec::text::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::typing::*;
use crate::bridge::typing::*;

verus! {

// ---------------------------------------------------------------- integer helpers

/// A positive factor keeps the sign.
pub proof fn lemma_sign_scale(x: int, p: int)
    requires p >= 1,
    ensures sign(x * p) == sign(x),
{
    if x > 0 {
        assert(x * p > 0) by (nonlinear_arith) requires x > 0, p >= 1;
    } else if x < 0 {
        assert(x * p < 0) by (nonlinear_arith) requires x < 0, p >= 1;
    } else {
        assert(x * p == 0);
    }
}

/// `10^(a+b) = 10^a · 10^b`.
pub proof fn lemma_pow10_add(a: nat, b: nat)
    ensures pow10(a + b) == pow10(a) * pow10(b),
    decreases a,
{
    if a == 0 {
        assert(pow10(0) == 1);
    } else {
        lemma_pow10_add((a - 1) as nat, b);
        assert(pow10(a + b) == 10 * pow10((a - 1 + b) as nat));
        assert(pow10(a) == 10 * pow10((a - 1) as nat));
        let x = pow10((a - 1) as nat);
        let y = pow10(b);
        assert(10 * (x * y) == (10 * x) * y) by (nonlinear_arith);
    }
}

// ---------------------------------------------------------------- value comparison

/// Numeric order at any common scale `s` at least both scales.
pub proof fn lemma_num_cmp_at(c1: int, s1: nat, c2: int, s2: nat, s: nat)
    requires s1 <= s, s2 <= s,
    ensures num_cmp(c1, s1, c2, s2) == sign(align(c1, s1, s) - align(c2, s2, s)),
{
    let m = max_nat(s1, s2);
    let p = pow10((s - m) as nat);
    let q1 = pow10((m - s1) as nat);
    let q2 = pow10((m - s2) as nat);
    lemma_pow10_add((m - s1) as nat, (s - m) as nat);
    lemma_pow10_add((m - s2) as nat, (s - m) as nat);
    lemma_pow10_positive((s - m) as nat);
    assert(pow10((s - s1) as nat) == q1 * p);
    assert(pow10((s - s2) as nat) == q2 * p);
    let a1 = c1 * q1;
    let a2 = c2 * q2;
    assert(c1 * (q1 * p) == a1 * p) by (nonlinear_arith) requires a1 == c1 * q1;
    assert(c2 * (q2 * p) == a2 * p) by (nonlinear_arith) requires a2 == c2 * q2;
    assert(a1 * p - a2 * p == (a1 - a2) * p) by (nonlinear_arith);
    lemma_sign_scale(a1 - a2, p);
}

/// `(coefficient, scale)` of a value of the numeric family (an integer is at scale 0).
pub open spec fn num_parts(v: Val) -> (int, nat) {
    match v {
        Val::Int(x) => (x, 0),
        Val::Num { coeff, scale } => (coeff, scale),
        _ => (0, 0),
    }
}

/// Position on the one microsecond time line of a value of the datetime family (a date is its midnight).
pub open spec fn dt_key(v: Val) -> int {
    match v {
        Val::Date(d) => d * usecs_per_day(),
        Val::Ts(t) => t,
        _ => 0,
    }
}

/// On the numeric family, `compare` is exact decimal order (`num_cmp`).
pub proof fn lemma_compare_num(a: Val, b: Val)
    requires val_family(a) == 1, val_family(b) == 1,
    ensures compare(a, b) == Some(num_cmp(num_parts(a).0, num_parts(a).1, num_parts(b).0, num_parts(b).1)),
{
    assert(pow10(0) == 1);
    if let (Val::Int(x), Val::Int(y)) = (a, b) {
        assert(align(x, 0, 0) == x);
        assert(align(y, 0, 0) == y);
    }
}

/// On the datetime family, `compare` is the order of the time-line positions.
pub proof fn lemma_compare_dt(a: Val, b: Val)
    requires val_family(a) == 2, val_family(b) == 2,
    ensures compare(a, b) == Some(sign(dt_key(a) - dt_key(b))),
{
    if let (Val::Date(x), Val::Date(y)) = (a, b) {
        assert(x * usecs_per_day() - y * usecs_per_day() == (x - y) * usecs_per_day()) by (nonlinear_arith);
        lemma_sign_scale(x - y, usecs_per_day());
    }
}

/// Bytewise text order is antisymmetric and in {-1, 0, 1} ...
pub proof fn lemma_lex_cmp_antisym(a: Seq<u8>, b: Seq<u8>)
    ensures lex_cmp(a, b) == -lex_cmp(b, a), -1 <= lex_cmp(a, b) <= 1,
    decreases a.len(),
{
    if a.len() > 0 && b.len() > 0 && a[0] == b[0] {
        lemma_lex_cmp_antisym(a.drop_first(), b.drop_first());
    }
}

/// ... and `lex_cmp(.,.) <= 0` is transitive.
pub proof fn lemma_lex_cmp_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires lex_cmp(a, b) <= 0, lex_cmp(b, c) <= 0,
    ensures lex_cmp(a, c) <= 0,
    decreases a.len(),
{
    if a.len() > 0 && b.len() > 0 && c.len() > 0 && a[0] == b[0] && b[0] == c[0] {
        lemma_lex_cmp_trans(a.drop_first(), b.drop_first(), c.drop_first());
    }
}

/// Within one comparison family, `compare` is defined, antisymmetric and in {-1, 0, 1}.
pub proof fn lemma_compare_antisym(a: Val, b: Val)
    requires val_family(a) >= 0, val_family(a) == val_family(b),
    ensures
        compare(a, b) is Some,
        compare(b, a) is Some,
        compare(a, b)->0 == -compare(b, a)->0,
        -1 <= compare(a, b)->0 <= 1,
{
    if val_family(a) == 1 {
        lemma_compare_num(a, b);
        lemma_compare_num(b, a);
        let s = max_nat(num_parts(a).1, num_parts(b).1);
        lemma_num_cmp_at(num_parts(a).0, num_parts(a).1, num_parts(b).0, num_parts(b).1, s);
        lemma_num_cmp_at(num_parts(b).0, num_parts(b).1, num_parts(a).0, num_parts(a).1, s);
    } else if val_family(a) == 2 {
        lemma_compare_dt(a, b);
        lemma_compare_dt(b, a);
    } else if val_family(a) == 3 {
        if let (Val::Text(x), Val::Text(y)) = (a, b) {
            lemma_lex_cmp_antisym(x, y);
        }
    }
}

/// Within one comparison family, `compare(.,.) <= 0` is transitive.
pub proof fn lemma_compare_trans(a: Val, b: Val, c: Val)
    requires
        val_family(a) >= 0, val_family(a) == val_family(b), val_family(b) == val_family(c),
        compare(a, b)->0 <= 0, compare(b, c)->0 <= 0,
    ensures
        compare(a, c)->0 <= 0,
{
    lemma_compare_antisym(a, b);
    lemma_compare_antisym(b, c);
    lemma_compare_antisym(a, c);
    if val_family(a) == 1 {
        let (ca, sa) = num_parts(a);
        let (cb, sb) = num_parts(b);
        let (cc, sc) = num_parts(c);
        let s = max_nat(max_nat(sa, sb), sc);
        lemma_compare_num(a, b);
        lemma_compare_num(b, c);
        lemma_compare_num(a, c);
        lemma_num_cmp_at(ca, sa, cb, sb, s);
        lemma_num_cmp_at(cb, sb, cc, sc, s);
        lemma_num_cmp_at(ca, sa, cc, sc, s);
    } else if val_family(a) == 2 {
        lemma_compare_dt(a, b);
        lemma_compare_dt(b, c);
        lemma_compare_dt(a, c);
    } else if val_family(a) == 3 {
        if let (Val::Text(x), Val::Text(y), Val::Text(z)) = (a, b, c) {
            lemma_lex_cmp_trans(x, y, z);
        }
    }
}

/// Every defined comparison is -1, 0 or 1 (so the executable negation for DESC cannot overflow).
pub proof fn lemma_compare_range(a: Val, b: Val)
    requires compare(a, b) is Some,
    ensures -1 <= compare(a, b)->0 <= 1,
{
    if let (Val::Text(x), Val::Text(y)) = (a, b) {
        lemma_lex_cmp_antisym(x, y);
    }
}

// ---------------------------------------------------------------- keys

/// The value `key_cmp` compares for key `k` in row `r` (NULL when the column is missing).
pub open spec fn key_val(k: OrderKey, r: Row) -> Val {
    if k.col < r.len() { r[k.col as int] } else { Val::Null }
}

/// The key value of `r` is NULL or of family `fam`.
pub open spec fn key_ok(k: OrderKey, fam: int, r: Row) -> bool {
    key_val(k, r) is Null || val_family(key_val(k, r)) == fam
}

/// `key_ok` for every key, with `fams[i]` the family of key `i`.
pub open spec fn keys_ok(keys: Seq<OrderKey>, fams: Seq<int>, r: Row) -> bool {
    keys.len() == fams.len() && forall|i: int| 0 <= i < keys.len() ==> #[trigger] key_ok(keys[i], fams[i], r)
}

/// One key on rows whose key values share a family: antisymmetric, in {-1, 0, 1} (NULL placement and DESC
/// preserve that) ...
pub proof fn lemma_key_cmp_antisym(k: OrderKey, fam: int, r1: Row, r2: Row)
    requires key_ok(k, fam, r1), key_ok(k, fam, r2),
    ensures key_cmp(k, r1, r2) == -key_cmp(k, r2, r1), -1 <= key_cmp(k, r1, r2) <= 1,
{
    let a = key_val(k, r1);
    let b = key_val(k, r2);
    if !(a is Null) && !(b is Null) {
        lemma_compare_antisym(a, b);
    }
}

/// ... and `key_cmp(.,.) <= 0` is transitive.
pub proof fn lemma_key_cmp_trans(k: OrderKey, fam: int, r1: Row, r2: Row, r3: Row)
    requires
        key_ok(k, fam, r1), key_ok(k, fam, r2), key_ok(k, fam, r3),
        key_cmp(k, r1, r2) <= 0, key_cmp(k, r2, r3) <= 0,
    ensures
        key_cmp(k, r1, r3) <= 0,
{
    let a = key_val(k, r1);
    let b = key_val(k, r2);
    let c = key_val(k, r3);
    if !(a is Null) && !(b is Null) && !(c is Null) {
        lemma_compare_antisym(a, b);
        lemma_compare_antisym(b, c);
        lemma_compare_antisym(a, c);
        if k.desc {
            lemma_compare_trans(c, b, a);
        } else {
            lemma_compare_trans(a, b, c);
        }
    }
}

pub proof fn lemma_keys_ok_tail(keys: Seq<OrderKey>, fams: Seq<int>, r: Row)
    requires keys_ok(keys, fams, r), keys.len() > 0,
    ensures keys_ok(keys.drop_first(), fams.drop_first(), r), key_ok(keys[0], fams[0], r),
{
    assert forall|i: int| 0 <= i < keys.len() - 1 implies #[trigger] key_ok(keys.drop_first()[i], fams.drop_first()[i], r) by {
        assert(key_ok(keys[i + 1], fams[i + 1], r));
    }
}

/// The lexicographic combination is antisymmetric ...
pub proof fn lemma_keys_cmp_antisym(keys: Seq<OrderKey>, fams: Seq<int>, r1: Row, r2: Row)
    requires keys_ok(keys, fams, r1), keys_ok(keys, fams, r2),
    ensures keys_cmp(keys, r1, r2) == -keys_cmp(keys, r2, r1),
    decreases keys.len(),
{
    if keys.len() > 0 {
        lemma_keys_ok_tail(keys, fams, r1);
        lemma_keys_ok_tail(keys, fams, r2);
        lemma_key_cmp_antisym(keys[0], fams[0], r1, r2);
        lemma_keys_cmp_antisym(keys.drop_first(), fams.drop_first(), r1, r2);
    }
}

/// ... and transitive: a total preorder on rows satisfying `keys_ok`.
pub proof fn lemma_keys_cmp_trans(keys: Seq<OrderKey>, fams: Seq<int>, r1: Row, r2: Row, r3: Row)
    requires
        keys_ok(keys, fams, r1), keys_ok(keys, fams, r2), keys_ok(keys, fams, r3),
        keys_cmp(keys, r1, r2) <= 0, keys_cmp(keys, r2, r3) <= 0,
    ensures
        keys_cmp(keys, r1, r3) <= 0,
    decreases keys.len(),
{
    if keys.len() > 0 {
        let k = keys[0];
        let f = fams[0];
        lemma_keys_ok_tail(keys, fams, r1);
        lemma_keys_ok_tail(keys, fams, r2);
        lemma_keys_ok_tail(keys, fams, r3);
        lemma_key_cmp_antisym(k, f, r1, r2);
        lemma_key_cmp_antisym(k, f, r2, r3);
        lemma_key_cmp_antisym(k, f, r1, r3);
        let x = key_cmp(k, r1, r2);
        let y = key_cmp(k, r2, r3);
        lemma_key_cmp_trans(k, f, r1, r2, r3);
        if key_cmp(k, r1, r3) == 0 {
            // r3 ~ r1 on this key, so both steps are ties on it and the tails decide.
            lemma_key_cmp_trans(k, f, r3, r1, r2);
            lemma_key_cmp_trans(k, f, r2, r3, r1);
            assert(x == 0 && y == 0);
            lemma_keys_cmp_trans(keys.drop_first(), fams.drop_first(), r1, r2, r3);
        }
    }
}

// ---------------------------------------------------------------- insertion sort

/// Every row of `s` satisfies `keys_ok`.
pub open spec fn all_keys_ok(keys: Seq<OrderKey>, fams: Seq<int>, s: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> keys_ok(keys, fams, #[trigger] s[i])
}

/// Appending a row that is not below any row keeps a sequence sorted.
pub proof fn lemma_sorted_push(keys: Seq<OrderKey>, s: Seq<Row>, x: Row)
    requires
        sorted_by(keys, s),
        forall|i: int| 0 <= i < s.len() ==> keys_cmp(keys, #[trigger] s[i], x) <= 0,
    ensures
        sorted_by(keys, s.push(x)),
{
    let t = s.push(x);
    assert forall|i: int, j: int| 0 <= i < j < t.len() implies keys_cmp(keys, #[trigger] t[i], #[trigger] t[j]) <= 0 by {
        assert(t[i] == s[i]);
        if j < s.len() {
            assert(t[j] == s[j]);
        }
    }
}

/// Dropping the last row keeps a sequence sorted and its rows' key families.
pub proof fn lemma_sorted_prefix(keys: Seq<OrderKey>, fams: Seq<int>, s: Seq<Row>)
    requires sorted_by(keys, s), all_keys_ok(keys, fams, s), s.len() > 0,
    ensures sorted_by(keys, s.drop_last()), all_keys_ok(keys, fams, s.drop_last()),
{
    let d = s.drop_last();
    assert forall|i: int, j: int| 0 <= i < j < d.len() implies keys_cmp(keys, #[trigger] d[i], #[trigger] d[j]) <= 0 by {
        assert(d[i] == s[i] && d[j] == s[j]);
    }
    assert forall|i: int| 0 <= i < d.len() implies keys_ok(keys, fams, #[trigger] d[i]) by {
        assert(d[i] == s[i]);
    }
}

/// Every row of `t` is `r` or a row of `s` (the rows after inserting `r` into `s`).
pub open spec fn from_or(t: Seq<Row>, s: Seq<Row>, r: Row) -> bool {
    forall|i: int| 0 <= i < t.len() ==> #[trigger] t[i] == r || s.contains(t[i])
}

/// Inserting a row into a sorted sequence keeps it sorted, adds exactly that row to the bag, and keeps every
/// row's key families. Induction on `s`: either `r` goes last (it is not below `s.last()`, hence by
/// transitivity not below any row), or `s.last()` stays last after inserting `r` into the prefix.
pub proof fn lemma_insert_sorted(keys: Seq<OrderKey>, fams: Seq<int>, s: Seq<Row>, r: Row)
    requires
        sorted_by(keys, s),
        all_keys_ok(keys, fams, s),
        keys_ok(keys, fams, r),
    ensures
        sorted_by(keys, insert_sorted(keys, s, r)),
        insert_sorted(keys, s, r).to_multiset() == s.to_multiset().insert(r),
        all_keys_ok(keys, fams, insert_sorted(keys, s, r)),
        from_or(insert_sorted(keys, s, r), s, r),
    decreases s.len(),
{
    // Only the preorder laws of `keys_cmp` are needed; keep its recursive definition out of the proof.
    hide(keys_cmp);
    let t = insert_sorted(keys, s, r);
    s.to_multiset_ensures();
    if s.len() == 0 {
        assert(s.push(r) =~= t);
    } else if keys_cmp(keys, s.last(), r) <= 0 {
        let n = s.len() - 1;
        assert forall|i: int| 0 <= i < s.len() implies keys_cmp(keys, #[trigger] s[i], r) <= 0 by {
            if i < n {
                assert(keys_cmp(keys, s[i], s[n]) <= 0);
                lemma_keys_cmp_trans(keys, fams, s[i], s[n], r);
            }
        }
        lemma_sorted_push(keys, s, r);
        assert forall|i: int| 0 <= i < t.len() implies #[trigger] t[i] == r || s.contains(t[i]) by {
            if i < s.len() { assert(t[i] == s[i]); }
        }
    } else {
        let d = s.drop_last();
        let last = s.last();
        let n = d.len() as int;
        lemma_sorted_prefix(keys, fams, s);
        lemma_insert_sorted(keys, fams, d, r);
        let u = insert_sorted(keys, d, r);
        assert(t == u.push(last));
        assert(keys_ok(keys, fams, s[n]));
        lemma_keys_cmp_antisym(keys, fams, last, r);
        assert forall|i: int| 0 <= i < u.len() implies keys_cmp(keys, #[trigger] u[i], last) <= 0 by {
            if u[i] != r {
                assert(d.contains(u[i]));
                let j = choose|j: int| 0 <= j < d.len() && d[j] == u[i];
                assert(keys_cmp(keys, s[j], s[n]) <= 0);
            }
        }
        lemma_sorted_push(keys, u, last);
        assert forall|i: int| 0 <= i < t.len() implies #[trigger] t[i] == r || s.contains(t[i]) by {
            if i < u.len() {
                assert(t[i] == u[i]);
                if u[i] != r {
                    let j = choose|j: int| 0 <= j < d.len() && d[j] == u[i];
                    assert(s[j] == t[i]);
                }
            } else {
                assert(s[n] == t[i]);
            }
        }
        assert forall|i: int| 0 <= i < t.len() implies keys_ok(keys, fams, #[trigger] t[i]) by {
            if i < u.len() { assert(t[i] == u[i]); }
        }
        u.to_multiset_ensures();
        d.to_multiset_ensures();
        assert(s == d.push(last));
        assert(t.to_multiset() =~= s.to_multiset().insert(r));
    }
}

/// The insertion sort is sorted, a permutation (same bag), and keeps every row's key families.
pub proof fn lemma_sort_rows(keys: Seq<OrderKey>, fams: Seq<int>, s: Seq<Row>)
    requires all_keys_ok(keys, fams, s),
    ensures
        sorted_by(keys, sort_rows(keys, s)),
        sort_rows(keys, s).to_multiset() == s.to_multiset(),
        all_keys_ok(keys, fams, sort_rows(keys, s)),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let d = s.drop_last();
        assert(all_keys_ok(keys, fams, d)) by {
            assert forall|i: int| 0 <= i < d.len() implies keys_ok(keys, fams, #[trigger] d[i]) by {
                assert(d[i] == s[i]);
            }
        }
        lemma_sort_rows(keys, fams, d);
        assert(keys_ok(keys, fams, s[s.len() - 1]));
        lemma_insert_sorted(keys, fams, sort_rows(keys, d), s.last());
        d.to_multiset_ensures();
        assert(s == d.push(s.last()));
    }
}

// ---------------------------------------------------------------- top level

/// Each ORDER BY key of `keys_in_range(keys, n)` names a column below `n` (the definition recurses on the last key).
pub proof fn lemma_keys_in_range(keys: Seq<OrderKey>, n: nat, i: int)
    requires keys_in_range(keys, n), 0 <= i < keys.len(),
    ensures keys[i].col < n,
    decreases keys.len(),
{
    if i < keys.len() - 1 {
        lemma_keys_in_range(keys.drop_last(), n, i);
    }
}

/// Families of the ORDER BY key columns of a checked statement.
pub open spec fn key_families(keys: Seq<OrderKey>, tys: Seq<ColTy>) -> Seq<int> {
    Seq::new(keys.len(), |i: int| family(tys[keys[i].col as int].ty))
}

/// The canonical output is allowed (`spec::order` obligation): on a well-formed database, a checked
/// statement's `denote_top` is a sorted permutation of the body's bag, sliced by OFFSET/LIMIT.
pub proof fn lemma_denote_top_ok(db: Database, oq: OrderedQuery)
    requires
        db_wf(db),
        wf_ordered(db.schema, oq),
    ensures
        ordered_ok(db, oq, denote_top(db, oq)),
{
    match denote_body(db, oq) {
        Err(e) => {},
        Ok(rows) => {
            let tys = type_query(db.schema, Seq::empty(), oq.body)->0;
            assert(row_typed(Seq::empty(), Seq::empty()));
            lemma_query_family(db, Seq::empty(), Seq::empty(), oq.body);
            let fams = key_families(oq.keys, tys);
            assert forall|i: int| 0 <= i < rows.len() implies keys_ok(oq.keys, fams, #[trigger] rows[i]) by {
                assert(row_typed(rows[i], tys));
                assert forall|j: int| 0 <= j < oq.keys.len() implies #[trigger] key_ok(oq.keys[j], fams[j], rows[i]) by {
                    lemma_keys_in_range(oq.keys, tys.len(), j);
                    let c = oq.keys[j].col as int;
                    assert(val_has_family(rows[i][c], tys[c].ty));
                }
            }
            let p = sort_rows(oq.keys, rows);
            lemma_sort_rows(oq.keys, fams, rows);
            assert(sorted_by(oq.keys, p));
        },
    }
}

} // verus!
