//! The join of TPC-H Q8 collapsed to one term per lineitem row.
//!
//! A sum over the joined rows `jrows(db)` of `jterm(ps, w)` (the weight of a qualifying row) equals a sum over the
//! lineitem rows of `lterm(db, ps, w)`: the weight of the lineitem's one joined row `jx(db, l)` if it qualifies.
//! `jx` finds the matching row of each other FROM input by its primary key (column 0): part by `l_partkey`, supplier
//! by `l_suppkey`, orders by `l_orderkey`, customer by `o_custkey`, n1 by `c_nationkey`, n2 by `s_nationkey`, region
//! by `n1.n_regionkey`. With the declared primary keys each lookup has at most one row (`key0`), so the product's
//! sum over each input collapses to that row (`lemma_collapse`); a joined prefix that already breaks a key equality
//! (`viol`) contributes nothing (`lemma_c*_viol`).
//!
//! The proof walks the left-deep product from the right: region, n2, n1, customer, orders (each collapsed), then
//! moves lineitem outward (`lemma_sum_of_product_swap`) and collapses supplier and part for each lineitem row.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::link::join::*;
use crate::link::expr::ival;
use super::sql::*;
use super::norm::*;

verus! {

// ------------------------------------------------------------------------------------------------ keyed lookups

/// The row of `t` whose column 0 is `v`, if any.
pub open spec fn find(t: Seq<Row>, v: Val) -> Option<Row> {
    if exists|i: int| 0 <= i < t.len() && (#[trigger] t[i])[0] == v {
        Some(t[choose|i: int| 0 <= i < t.len() && (#[trigger] t[i])[0] == v])
    } else {
        None
    }
}

/// Column 0 is a key of `t` (no two rows share it).
pub open spec fn key0(t: Seq<Row>) -> bool {
    forall|i: int, j: int| 0 <= i < t.len() && 0 <= j < t.len() && (#[trigger] t[i])[0] == (#[trigger] t[j])[0] ==> i == j
}

/// `find` returns the row holding the key, or nothing when no row does.
pub proof fn lemma_find(t: Seq<Row>, v: Val)
    requires key0(t),
    ensures
        find(t, v) is None <==> forall|i: int| 0 <= i < t.len() ==> (#[trigger] t[i])[0] != v,
        forall|i: int| 0 <= i < t.len() && (#[trigger] t[i])[0] == v ==> find(t, v) == Some(t[i]),
        find(t, v) matches Some(r) ==> r[0] == v && t.contains(r),
{
    if exists|i: int| 0 <= i < t.len() && (#[trigger] t[i])[0] == v {
        let i0 = choose|i: int| 0 <= i < t.len() && (#[trigger] t[i])[0] == v;
        assert(find(t, v) == Some(t[i0]));
    }
}

/// A sum over a keyed relation of a term that vanishes off key `v` is the term of `v`'s row.
pub proof fn lemma_collapse(t: Seq<Row>, v: Val, h: spec_fn(Row) -> int)
    requires
        key0(t),
        forall|i: int| 0 <= i < t.len() && (#[trigger] t[i])[0] != v ==> h(t[i]) == 0,
    ensures
        sum_of(t, h) == match find(t, v) {
            Some(r) => h(r),
            None => 0,
        },
{
    lemma_find(t, v);
    if exists|i: int| 0 <= i < t.len() && (#[trigger] t[i])[0] == v {
        let i0 = choose|i: int| 0 <= i < t.len() && (#[trigger] t[i])[0] == v;
        lemma_sum_of_remove(t, i0, h);
        let rest = t.remove(i0);
        assert forall|i: int| 0 <= i < rest.len() implies h(#[trigger] rest[i]) == 0 by {
            let j = if i < i0 { i } else { i + 1 };
            assert(rest[i] == t[j]);
            assert(t[j][0] != v);
        }
        lemma_sum_of_zero(rest, h);
    } else {
        assert forall|i: int| 0 <= i < t.len() implies h(#[trigger] t[i]) == 0 by {
            assert(t[i][0] != v);
        }
        lemma_sum_of_zero(t, h);
    }
}

// ------------------------------------------------------------------------------------------------ broken prefixes

/// The joined prefix `a` already breaks one of the key equalities of the WHERE condition.
pub open spec fn viol(a: Row) -> bool {
    ||| (a.len() > 17 && a[0] != a[17])
    ||| (a.len() > 18 && a[9] != a[18])
    ||| (a.len() > 32 && a[16] != a[32])
    ||| (a.len() > 41 && a[33] != a[41])
    ||| (a.len() > 49 && a[44] != a[49])
    ||| (a.len() > 53 && a[12] != a[53])
    ||| (a.len() > 57 && a[51] != a[57])
}

/// Extending a broken prefix keeps it broken.
pub proof fn lemma_viol_ext(a: Row, b: Row)
    requires viol(a),
    ensures viol(a + b),
{
    let x = a + b;
    assert(x.len() >= a.len());
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] x[i] == a[i] by {}
}

/// A broken joined row does not qualify.
pub proof fn lemma_viol_jqual(ps: Seq<Literal>, x: Row)
    requires viol(x), x.len() == 60,
    ensures !jqual(ps, x),
{
}

// ------------------------------------------------------------------------------------------------ collapsed terms

/// Region collapsed (`a`: a joined prefix through n2, 57 values).
pub open spec fn c7(db: Database, f: spec_fn(Row) -> int, a: Row) -> int {
    match find(db.tables[7], a[51]) {
        Some(r) => f(a + r),
        None => 0,
    }
}

/// n2 collapsed (`a`: through n1, 53 values).
pub open spec fn c6(db: Database, f: spec_fn(Row) -> int, a: Row) -> int {
    match find(db.tables[6], a[12]) {
        Some(n) => c7(db, f, a + n),
        None => 0,
    }
}

/// n1 collapsed (`a`: through customer, 49 values).
pub open spec fn c5(db: Database, f: spec_fn(Row) -> int, a: Row) -> int {
    match find(db.tables[6], a[44]) {
        Some(n) => c6(db, f, a + n),
        None => 0,
    }
}

/// Customer collapsed (`a`: through orders, 41 values).
pub open spec fn c4(db: Database, f: spec_fn(Row) -> int, a: Row) -> int {
    match find(db.tables[2], a[33]) {
        Some(c) => c5(db, f, a + c),
        None => 0,
    }
}

/// Orders collapsed (`a`: through lineitem, 32 values).
pub open spec fn c3(db: Database, f: spec_fn(Row) -> int, a: Row) -> int {
    match find(db.tables[1], a[16]) {
        Some(o) => c4(db, f, a + o),
        None => 0,
    }
}

/// Supplier and part collapsed: the term of lineitem row `l`.
pub open spec fn c1(db: Database, f: spec_fn(Row) -> int, l: Row) -> int {
    match find(db.tables[3], l[1]) {
        Some(p) => match find(db.tables[5], l[2]) {
            Some(s) => c3(db, f, p + s + l),
            None => 0,
        },
        None => 0,
    }
}

/// The facts the collapse needs: table value kinds and the primary keys of the looked-up tables.
pub open spec fn join_ok(db: Database) -> bool {
    &&& tables_typed(db)
    &&& key0(db.tables[1]) && key0(db.tables[2]) && key0(db.tables[3])
    &&& key0(db.tables[5]) && key0(db.tables[6]) && key0(db.tables[7])
}

/// A found row is a row of its table.
proof fn lemma_found(t: Seq<Row>, v: Val, r: Row)
    requires key0(t), find(t, v) == Some(r),
    ensures exists|i: int| 0 <= i < t.len() && t[i] == r,
{
    lemma_find(t, v);
    assert(t.contains(r));
}

/// Every collapsed term of a broken prefix is 0.
pub proof fn lemma_c7_viol(db: Database, ps: Seq<Literal>, w: spec_fn(Row) -> int, a: Row)
    requires join_ok(db), viol(a), a.len() == 57,
    ensures c7(db, jterm(ps, w), a) == 0,
{
    if let Some(r) = find(db.tables[7], a[51]) {
        lemma_found(db.tables[7], a[51], r);
        lemma_viol_ext(a, r);
        lemma_viol_jqual(ps, a + r);
    }
}

pub proof fn lemma_c6_viol(db: Database, ps: Seq<Literal>, w: spec_fn(Row) -> int, a: Row)
    requires join_ok(db), viol(a), a.len() == 53,
    ensures c6(db, jterm(ps, w), a) == 0,
{
    if let Some(n) = find(db.tables[6], a[12]) {
        lemma_found(db.tables[6], a[12], n);
        lemma_viol_ext(a, n);
        lemma_c7_viol(db, ps, w, a + n);
    }
}

pub proof fn lemma_c5_viol(db: Database, ps: Seq<Literal>, w: spec_fn(Row) -> int, a: Row)
    requires join_ok(db), viol(a), a.len() == 49,
    ensures c5(db, jterm(ps, w), a) == 0,
{
    if let Some(n) = find(db.tables[6], a[44]) {
        lemma_found(db.tables[6], a[44], n);
        lemma_viol_ext(a, n);
        lemma_c6_viol(db, ps, w, a + n);
    }
}

pub proof fn lemma_c4_viol(db: Database, ps: Seq<Literal>, w: spec_fn(Row) -> int, a: Row)
    requires join_ok(db), viol(a), a.len() == 41,
    ensures c4(db, jterm(ps, w), a) == 0,
{
    if let Some(c) = find(db.tables[2], a[33]) {
        lemma_found(db.tables[2], a[33], c);
        lemma_viol_ext(a, c);
        lemma_c5_viol(db, ps, w, a + c);
    }
}

pub proof fn lemma_c3_viol(db: Database, ps: Seq<Literal>, w: spec_fn(Row) -> int, a: Row)
    requires join_ok(db), viol(a), a.len() == 32,
    ensures c3(db, jterm(ps, w), a) == 0,
{
    if let Some(o) = find(db.tables[1], a[16]) {
        lemma_found(db.tables[1], a[16], o);
        lemma_viol_ext(a, o);
        lemma_c4_viol(db, ps, w, a + o);
    }
}

// ------------------------------------------------------------------------------------------------ row lengths

/// Every row of `s` has `n` values.
pub open spec fn width(s: Seq<Row>, n: int) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).len() == n
}

pub proof fn lemma_product_width(a: Seq<Row>, b: Seq<Row>, na: int, nb: int)
    requires width(a, na), width(b, nb),
    ensures width(product_rows(a, b), na + nb),
{
    crate::bridge::relation::lemma_product_rows_elems(a, b);
    let p = product_rows(a, b);
    assert forall|k: int| 0 <= k < p.len() implies (#[trigger] p[k]).len() == na + nb by {
        assert(crate::bridge::relation::is_concat(p[k], a, b));
        let (i, j) = choose|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && p[k] == #[trigger] a[i] + #[trigger] b[j];
        assert(a[i].len() == na && b[j].len() == nb);
    }
}

/// The left-deep prefixes of the joined relation.
pub open spec fn j2(db: Database) -> Seq<Row> { product_rows(db.tables[3], db.tables[5]) }
pub open spec fn j3(db: Database) -> Seq<Row> { product_rows(j2(db), db.tables[0]) }
pub open spec fn j4(db: Database) -> Seq<Row> { product_rows(j3(db), db.tables[1]) }
pub open spec fn j5(db: Database) -> Seq<Row> { product_rows(j4(db), db.tables[2]) }
pub open spec fn j6(db: Database) -> Seq<Row> { product_rows(j5(db), db.tables[6]) }
pub open spec fn j7(db: Database) -> Seq<Row> { product_rows(j6(db), db.tables[6]) }

pub proof fn lemma_widths(db: Database)
    requires tables_typed(db),
    ensures
        width(db.tables[3], 9), width(db.tables[5], 7), width(db.tables[0], 16), width(db.tables[1], 9),
        width(db.tables[2], 8), width(db.tables[6], 4), width(db.tables[7], 3),
        width(j3(db), 32), width(j4(db), 41), width(j5(db), 49), width(j6(db), 53), width(j7(db), 57),
        jrows(db) == product_rows(j7(db), db.tables[7]),
{
    let t = db.tables;
    assert(width(t[3], 9)) by { assert forall|i: int| 0 <= i < t[3].len() implies (#[trigger] t[3][i]).len() == 9 by { assert(pa_typed(t[3][i])); } }
    assert(width(t[5], 7)) by { assert forall|i: int| 0 <= i < t[5].len() implies (#[trigger] t[5][i]).len() == 7 by { assert(su_typed(t[5][i])); } }
    assert(width(t[0], 16)) by { assert forall|i: int| 0 <= i < t[0].len() implies (#[trigger] t[0][i]).len() == 16 by { assert(li_typed(t[0][i])); } }
    assert(width(t[1], 9)) by { assert forall|i: int| 0 <= i < t[1].len() implies (#[trigger] t[1][i]).len() == 9 by { assert(or_typed(t[1][i])); } }
    assert(width(t[2], 8)) by { assert forall|i: int| 0 <= i < t[2].len() implies (#[trigger] t[2][i]).len() == 8 by { assert(cu_typed(t[2][i])); } }
    assert(width(t[6], 4)) by { assert forall|i: int| 0 <= i < t[6].len() implies (#[trigger] t[6][i]).len() == 4 by { assert(na_typed(t[6][i])); } }
    assert(width(t[7], 3)) by { assert forall|i: int| 0 <= i < t[7].len() implies (#[trigger] t[7][i]).len() == 3 by { assert(re_typed(t[7][i])); } }
    lemma_product_width(t[3], t[5], 9, 7);
    lemma_product_width(j2(db), t[0], 16, 16);
    lemma_product_width(j3(db), t[1], 32, 9);
    lemma_product_width(j4(db), t[2], 41, 8);
    lemma_product_width(j5(db), t[6], 49, 4);
    lemma_product_width(j6(db), t[6], 53, 4);
}

// ------------------------------------------------------------------------------------------------ collapse steps

/// One collapse step: a product with a keyed right input whose term vanishes off the key `a[kpos]` sums like the
/// collapsed term `ck` over the left input.
pub proof fn lemma_step(a: Seq<Row>, t: Seq<Row>, g: spec_fn(Row) -> int, kpos: int, ck: spec_fn(Row) -> int)
    requires
        key0(t),
        forall|i: int, k: int| 0 <= i < a.len() && 0 <= k < t.len() && (#[trigger] t[k])[0] != (#[trigger] a[i])[kpos]
            ==> g(a[i] + t[k]) == 0,
        forall|i: int| 0 <= i < a.len() ==> ck(#[trigger] a[i]) == match find(t, a[i][kpos]) {
            Some(r) => g(a[i] + r),
            None => 0,
        },
    ensures sum_of(product_rows(a, t), g) == sum_of(a, ck),
{
    lemma_sum_of_product(a, t, g);
    let inner = |x: Row| sum_of(t, |y: Row| g(x + y));
    assert forall|i: int| 0 <= i < a.len() implies inner(#[trigger] a[i]) == ck(a[i]) by {
        let x = a[i];
        let h = |y: Row| g(x + y);
        assert forall|k: int| 0 <= k < t.len() && (#[trigger] t[k])[0] != x[kpos] implies h(t[k]) == 0 by {
            assert(t[k][0] != a[i][kpos]);
        }
        lemma_collapse(t, x[kpos], h);
    }
    lemma_sum_of_ext(a, inner, ck);
}

/// The collapsed terms as functions.
pub open spec fn c7f(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int { |a: Row| c7(db, f, a) }
pub open spec fn c6f(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int { |a: Row| c6(db, f, a) }
pub open spec fn c5f(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int { |a: Row| c5(db, f, a) }
pub open spec fn c4f(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int { |a: Row| c4(db, f, a) }
pub open spec fn c3f(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int { |a: Row| c3(db, f, a) }
pub open spec fn c1f(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int { |l: Row| c1(db, f, l) }

/// Region, n2, n1, customer and orders collapsed: the sum over the joined rows is a sum over the lineitem prefixes.
pub proof fn lemma_collapse_right(db: Database, ps: Seq<Literal>, w: spec_fn(Row) -> int)
    requires join_ok(db),
    ensures sum_of(jrows(db), jterm(ps, w)) == sum_of(j3(db), c3f(db, jterm(ps, w))),
{
    let f = jterm(ps, w);
    let t = db.tables;
    lemma_widths(db);
    // region
    assert forall|i: int, k: int| 0 <= i < j7(db).len() && 0 <= k < t[7].len() && (#[trigger] t[7][k])[0] != (#[trigger] j7(db)[i])[51]
        implies f(j7(db)[i] + t[7][k]) == 0 by {
        let x = j7(db)[i] + t[7][k];
        assert(x[51] == j7(db)[i][51] && x[57] == t[7][k][0]);
        lemma_viol_jqual(ps, x);
    }
    lemma_step(j7(db), t[7], f, 51, c7f(db, f));
    // n2
    assert forall|i: int, k: int| 0 <= i < j6(db).len() && 0 <= k < t[6].len() && (#[trigger] t[6][k])[0] != (#[trigger] j6(db)[i])[12]
        implies c7f(db, f)(j6(db)[i] + t[6][k]) == 0 by {
        let x = j6(db)[i] + t[6][k];
        assert(x[12] == j6(db)[i][12] && x[53] == t[6][k][0]);
        lemma_c7_viol(db, ps, w, x);
    }
    lemma_step(j6(db), t[6], c7f(db, f), 12, c6f(db, f));
    // n1
    assert forall|i: int, k: int| 0 <= i < j5(db).len() && 0 <= k < t[6].len() && (#[trigger] t[6][k])[0] != (#[trigger] j5(db)[i])[44]
        implies c6f(db, f)(j5(db)[i] + t[6][k]) == 0 by {
        let x = j5(db)[i] + t[6][k];
        assert(x[44] == j5(db)[i][44] && x[49] == t[6][k][0]);
        lemma_c6_viol(db, ps, w, x);
    }
    lemma_step(j5(db), t[6], c6f(db, f), 44, c5f(db, f));
    // customer
    assert forall|i: int, k: int| 0 <= i < j4(db).len() && 0 <= k < t[2].len() && (#[trigger] t[2][k])[0] != (#[trigger] j4(db)[i])[33]
        implies c5f(db, f)(j4(db)[i] + t[2][k]) == 0 by {
        let x = j4(db)[i] + t[2][k];
        assert(x[33] == j4(db)[i][33] && x[41] == t[2][k][0]);
        lemma_c5_viol(db, ps, w, x);
    }
    lemma_step(j4(db), t[2], c5f(db, f), 33, c4f(db, f));
    // orders
    assert forall|i: int, k: int| 0 <= i < j3(db).len() && 0 <= k < t[1].len() && (#[trigger] t[1][k])[0] != (#[trigger] j3(db)[i])[16]
        implies c4f(db, f)(j3(db)[i] + t[1][k]) == 0 by {
        let x = j3(db)[i] + t[1][k];
        assert(x[16] == j3(db)[i][16] && x[32] == t[1][k][0]);
        lemma_c4_viol(db, ps, w, x);
    }
    lemma_step(j3(db), t[1], c4f(db, f), 16, c3f(db, f));
}

/// Supplier then part collapsed for one lineitem row `l`.
pub proof fn lemma_collapse_left_row(db: Database, ps: Seq<Literal>, w: spec_fn(Row) -> int, l: Row)
    requires join_ok(db), l.len() == 16,
    ensures sum_of(j2(db), |x: Row| c3(db, jterm(ps, w), x + l)) == c1(db, jterm(ps, w), l),
{
    let f = jterm(ps, w);
    let t = db.tables;
    lemma_widths(db);
    let h = |x: Row| c3(db, f, x + l);
    lemma_sum_of_product(t[3], t[5], h);
    let mid = |p: Row| match find(t[5], l[2]) {
        Some(s) => c3(db, f, p + s + l),
        None => 0,
    };
    let inner = |x: Row| sum_of(t[5], |y: Row| h(x + y));
    assert forall|i: int| 0 <= i < t[3].len() implies inner(#[trigger] t[3][i]) == mid(t[3][i]) by {
        let p = t[3][i];
        let hs = |y: Row| h(p + y);
        assert forall|k: int| 0 <= k < t[5].len() && (#[trigger] t[5][k])[0] != l[2] implies hs(t[5][k]) == 0 by {
            let x = p + t[5][k] + l;
            assert(x[9] == t[5][k][0] && x[18] == l[2]);
            lemma_c3_viol(db, ps, w, x);
        }
        lemma_collapse(t[5], l[2], hs);
    }
    lemma_sum_of_ext(t[3], inner, mid);
    assert forall|i: int| 0 <= i < t[3].len() && (#[trigger] t[3][i])[0] != l[1] implies mid(t[3][i]) == 0 by {
        let p = t[3][i];
        if let Some(s) = find(t[5], l[2]) {
            lemma_found(t[5], l[2], s);
            let x = p + s + l;
            assert(x[0] == p[0] && x[17] == l[1]);
            lemma_c3_viol(db, ps, w, x);
        }
    }
    lemma_collapse(t[3], l[1], mid);
}

/// The sum over the joined rows is a sum over the lineitem rows of their collapsed terms.
pub proof fn lemma_collapse_all(db: Database, ps: Seq<Literal>, w: spec_fn(Row) -> int)
    requires join_ok(db),
    ensures sum_of(jrows(db), jterm(ps, w)) == sum_of(db.tables[0], c1f(db, jterm(ps, w))),
{
    let f = jterm(ps, w);
    let t = db.tables;
    lemma_widths(db);
    lemma_collapse_right(db, ps, w);
    lemma_sum_of_product_swap(j2(db), t[0], c3f(db, f));
    let inner = |y: Row| sum_of(j2(db), |x: Row| c3f(db, f)(x + y));
    assert forall|i: int| 0 <= i < t[0].len() implies inner(#[trigger] t[0][i]) == c1f(db, f)(t[0][i]) by {
        let l = t[0][i];
        lemma_collapse_left_row(db, ps, w, l);
        lemma_sum_of_ext(j2(db), |x: Row| c3f(db, f)(x + l), |x: Row| c3(db, f, x + l));
    }
    lemma_sum_of_ext(t[0], inner, c1f(db, f));
}

// ------------------------------------------------------------------------------------------------ one lineitem's term

/// What a qualifying lineitem row contributes: the year of its order, its volume (scale 4) and whether its
/// supplier's nation is `$1`.
pub struct LHit {
    pub year: int,
    pub vol: int,
    pub hit: bool,
}

/// The lineitem row `l`'s contribution: `None` when some lookup finds no row or the row does not qualify.
pub open spec fn lhit(db: Database, ps: Seq<Literal>, l: Row) -> Option<LHit> {
    let t = db.tables;
    match find(t[3], l[1]) {
        None => None,
        Some(p) => if p[4] != Val::Text(txt(ps[2])) { None } else {
            match find(t[5], l[2]) {
                None => None,
                Some(s) => match find(t[1], l[0]) {
                    None => None,
                    Some(o) => if !(d95() <= dval(o[4]) <= d96e()) { None } else {
                        match find(t[2], o[1]) {
                            None => None,
                            Some(c) => match find(t[6], c[3]) {
                                None => None,
                                Some(n1) => match find(t[7], n1[2]) {
                                    None => None,
                                    Some(r) => if r[1] != Val::Text(txt(ps[1])) { None } else {
                                        match find(t[6], s[3]) {
                                            None => None,
                                            Some(n2) => Some(LHit {
                                                year: year_of(dval(o[4])),
                                                vol: ival(l[5]) * (100 - ival(l[6])),
                                                hit: n2[1] == Val::Text(txt(ps[0])),
                                            }),
                                        }
                                    },
                                },
                            },
                        }
                    },
                },
            }
        },
    }
}

/// A weight that depends on a qualifying row's year, volume and nation match only.
pub open spec fn weight_of(w: spec_fn(Row) -> int, ww: spec_fn(LHit) -> int, b0: Seq<u8>) -> bool {
    forall|x: Row| #[trigger] w(x) == ww(LHit { year: jyear(x), vol: vol_of(x), hit: x[54] == Val::Text(b0) })
}

/// The term of a lineitem row from its contribution.
pub open spec fn hterm(h: Option<LHit>, ww: spec_fn(LHit) -> int) -> int {
    match h {
        Some(v) => ww(v),
        None => 0,
    }
}

/// The collapsed term of a lineitem row is its contribution's weight.
pub proof fn lemma_c1_lhit(db: Database, ps: Seq<Literal>, w: spec_fn(Row) -> int, ww: spec_fn(LHit) -> int, l: Row)
    requires
        join_ok(db),
        weight_of(w, ww, txt(ps[0])),
        li_typed(l),
    ensures c1(db, jterm(ps, w), l) == hterm(lhit(db, ps, l), ww),
{
    let t = db.tables;
    let f = jterm(ps, w);
    lemma_widths(db);
    lemma_find(t[3], l[1]);
    lemma_find(t[5], l[2]);
    lemma_find(t[1], l[0]);
    if let (Some(p), Some(s), Some(o)) = (find(t[3], l[1]), find(t[5], l[2]), find(t[1], l[0])) {
        lemma_found(t[3], l[1], p);
        lemma_found(t[5], l[2], s);
        lemma_found(t[1], l[0], o);
        let a3 = p + s + l;
        assert(a3.len() == 32 && a3[16] == l[0]);
        let a4 = a3 + o;
        assert(a4.len() == 41 && a4[33] == o[1]);
        lemma_find(t[2], o[1]);
        if let Some(c) = find(t[2], o[1]) {
            lemma_found(t[2], o[1], c);
            let a5 = a4 + c;
            assert(a5.len() == 49 && a5[44] == c[3]);
            lemma_find(t[6], c[3]);
            if let Some(n1) = find(t[6], c[3]) {
                lemma_found(t[6], c[3], n1);
                let a6 = a5 + n1;
                assert(a6.len() == 53 && a6[12] == s[3]);
                lemma_find(t[6], s[3]);
                if let Some(n2) = find(t[6], s[3]) {
                    lemma_found(t[6], s[3], n2);
                    let a7 = a6 + n2;
                    assert(a7.len() == 57 && a7[51] == n1[2]);
                    lemma_find(t[7], n1[2]);
                    if let Some(r) = find(t[7], n1[2]) {
                        lemma_found(t[7], n1[2], r);
                        let x = a7 + r;
                        assert(x == join8(p, s, l, o, c, n1, n2, r));
                        assert(pa_typed(p) && su_typed(s) && or_typed(o) && cu_typed(c) && na_typed(n1) && na_typed(n2) && re_typed(r));
                        lemma_join8_at(p, s, l, o, c, n1, n2, r);
                        assert(c1(db, f, l) == f(x));
                        assert(w(x) == ww(LHit { year: jyear(x), vol: vol_of(x), hit: x[54] == Val::Text(txt(ps[0])) }));
                    }
                }
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ primary keys

/// Under the declared primary keys, column 0 is a key of orders, customer, part, supplier, nation and region.
pub proof fn lemma_keys(db: Database)
    requires
        db_ok(db),
        crate::spec::constraints::constraints_hold(crate::gendb_constraints::declared_db(db)),
    ensures key0(db.tables[1]) && key0(db.tables[2]) && key0(db.tables[3]) && key0(db.tables[5])
        && key0(db.tables[6]) && key0(db.tables[7]),
{
    lemma_key0(db, 1);
    lemma_key0(db, 2);
    lemma_key0(db, 3);
    lemma_key0(db, 5);
    lemma_key0(db, 6);
    lemma_key0(db, 7);
}

proof fn lemma_key0(db: Database, t: int)
    requires
        db_ok(db),
        crate::spec::constraints::constraints_hold(crate::gendb_constraints::declared_db(db)),
        t == 1 || t == 2 || t == 3 || t == 5 || t == 6 || t == 7,
    ensures key0(db.tables[t]),
{
    let ddb = crate::gendb_constraints::declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    let cols = seq![0nat];
    let key = crate::spec::types::Constraint::Key { cols, primary: true, nulls_distinct: true };
    assert(ddb.schema[t].constraints[0] == key) by {
        assert(crate::gendb_constraints::declared_schema()[t].constraints[0] == key);
    }
    assert(ddb.tables == db.tables);
    assert(db.tables.len() == 8) by { lemma_tables_typed(db); }
    let rows = db.tables[t];
    assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && (#[trigger] rows[i])[0] == (#[trigger] rows[j])[0]
        implies i == j by {
        let ka = crate::spec::constraints::key_of(rows[i], cols);
        let kb = crate::spec::constraints::key_of(rows[j], cols);
        assert(ka =~= kb);
        crate::bridge::equality::lemma_row_not_distinct_refl(ka);
        crate::bridge::constraints::lemma_primary_key_identifies(ddb, t, 0, cols, true, i, j);
    }
}

} // verus!
