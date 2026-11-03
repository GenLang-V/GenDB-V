//! From the 6-way product to lineitem: any per-row term of the SELECT list, summed over the joined rows the WHERE
//! keeps, equals a sum over the lineitem table of a term found by key lookups (`lemma_reduce`).
//!
//! The product is left-deep: P2 = supplier x lineitem, P3 = P2 x orders, P4 = P3 x customer, P5 = P4 x nation,
//! P6 = P5 x nation. `h6` is the term on a joined row (zero unless `jq`). Going up one level, the sum over the
//! right input of `h_{k+1}(x ++ r)` collapses to the one row whose key the WHERE condition equates with a column
//! of `x` (each right input has a primary key on column 0, `keysum::lemma_sum_by_key`): `h5`..`h2` look up n2,
//! n1, customer and orders; `h1` looks up the supplier of a lineitem row (the supplier sum is exchanged with the
//! lineitem sum first). The completions `c5`..`c2` rebuild the joined row a nonzero term came from.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::relation::*;
use crate::spec::ast::Literal;
use crate::link::join::*;
use super::common::keysum::*;
use super::sqlq::*;

verus! {

// ------------------------------------------------------------------------------------------------ the inputs

pub open spec fn t_sup(db: Database) -> Seq<Row> { db.tables[5] }
pub open spec fn t_li(db: Database) -> Seq<Row> { db.tables[0] }
pub open spec fn t_ord(db: Database) -> Seq<Row> { db.tables[1] }
pub open spec fn t_cust(db: Database) -> Seq<Row> { db.tables[2] }
pub open spec fn t_nat(db: Database) -> Seq<Row> { db.tables[6] }

pub open spec fn p2(db: Database) -> Seq<Row> { product_rows(t_sup(db), t_li(db)) }
pub open spec fn p3(db: Database) -> Seq<Row> { product_rows(p2(db), t_ord(db)) }
pub open spec fn p4(db: Database) -> Seq<Row> { product_rows(p3(db), t_cust(db)) }
pub open spec fn p5(db: Database) -> Seq<Row> { product_rows(p4(db), t_nat(db)) }
pub open spec fn p6(db: Database) -> Seq<Row> { product_rows(p5(db), t_nat(db)) }

/// Every row of `rows` has `w` columns.
pub open spec fn all_len(rows: Seq<Row>, w: nat) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() == w
}

/// The shapes and keys the reduction uses: widths of the five tables, and a unique column 0 in each looked-up
/// table.
pub open spec fn red_ok(db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& all_len(t_sup(db), 7)
    &&& all_len(t_li(db), 16)
    &&& all_len(t_ord(db), 9)
    &&& all_len(t_cust(db), 8)
    &&& all_len(t_nat(db), 4)
    &&& key_unique(t_sup(db), 0)
    &&& key_unique(t_ord(db), 0)
    &&& key_unique(t_cust(db), 0)
    &&& key_unique(t_nat(db), 0)
}

/// Rows of a product of fixed-width inputs have the summed width.
pub proof fn lemma_product_len(a: Seq<Row>, b: Seq<Row>, wa: nat, wb: nat)
    requires all_len(a, wa), all_len(b, wb),
    ensures all_len(product_rows(a, b), wa + wb),
{
    crate::bridge::relation::lemma_product_rows_elems(a, b);
    let p = product_rows(a, b);
    assert forall|k: int| 0 <= k < p.len() implies (#[trigger] p[k]).len() == wa + wb by {
        assert(crate::bridge::relation::is_concat(p[k], a, b));
        let (i, j) = choose|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && p[k] == #[trigger] a[i] + #[trigger] b[j];
        assert(a[i].len() == wa && b[j].len() == wb);
    }
}

/// The widths of the five levels.
pub proof fn lemma_level_lens(db: Database)
    requires red_ok(db),
    ensures
        all_len(p2(db), 23), all_len(p3(db), 32), all_len(p4(db), 40), all_len(p5(db), 44), all_len(p6(db), 48),
{
    lemma_product_len(t_sup(db), t_li(db), 7, 16);
    lemma_product_len(p2(db), t_ord(db), 23, 9);
    lemma_product_len(p3(db), t_cust(db), 32, 8);
    lemma_product_len(p4(db), t_nat(db), 40, 4);
    lemma_product_len(p5(db), t_nat(db), 44, 4);
}

// ------------------------------------------------------------------------------------------------ terms per level

/// The term on a joined row: `phi` of the SELECT list where the WHERE condition holds, else 0.
pub open spec fn h6(ps: Seq<Literal>, phi: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| if jq(ps, x) { phi(px(x)) } else { 0int }
}

/// Level P5 (44 columns): n2 by c_nationkey (column 35).
pub open spec fn h5(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| if has_key(t_nat(db), 0, x[35]) { h6(ps, phi)(x + key_row(t_nat(db), 0, x[35])) } else { 0int }
}

/// Level P4 (40 columns): n1 by s_nationkey (column 3).
pub open spec fn h4(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| if has_key(t_nat(db), 0, x[3]) { h5(db, ps, phi)(x + key_row(t_nat(db), 0, x[3])) } else { 0int }
}

/// Level P3 (32 columns): customer by o_custkey (column 24).
pub open spec fn h3(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| if has_key(t_cust(db), 0, x[24]) { h4(db, ps, phi)(x + key_row(t_cust(db), 0, x[24])) } else { 0int }
}

/// Level P2 (23 columns): orders by l_orderkey (column 7).
pub open spec fn h2(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| if has_key(t_ord(db), 0, x[7]) { h3(db, ps, phi)(x + key_row(t_ord(db), 0, x[7])) } else { 0int }
}

/// A lineitem row (16 columns): supplier by l_suppkey (column 2).
pub open spec fn h1(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |l: Row| if has_key(t_sup(db), 0, l[2]) { h2(db, ps, phi)(key_row(t_sup(db), 0, l[2]) + l) } else { 0int }
}

/// The joined row a level-5 term comes from.
pub open spec fn c5(db: Database, x: Row) -> Row { x + key_row(t_nat(db), 0, x[35]) }
pub open spec fn c4(db: Database, x: Row) -> Row { c5(db, x + key_row(t_nat(db), 0, x[3])) }
pub open spec fn c3(db: Database, x: Row) -> Row { c4(db, x + key_row(t_cust(db), 0, x[24])) }
pub open spec fn c2(db: Database, x: Row) -> Row { c3(db, x + key_row(t_ord(db), 0, x[7])) }

/// A key row of a fixed-width table has that width.
proof fn lemma_key_row_len(rows: Seq<Row>, k: Val, w: nat)
    requires all_len(rows, w), has_key(rows, 0, k),
    ensures key_row(rows, 0, k).len() == w,
{
    lemma_key_row(rows, 0, k);
}

/// A nonzero level-5 term: its completion satisfies the WHERE condition and extends `x`.
proof fn lemma_nz5(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int, x: Row)
    requires red_ok(db), x.len() == 44, h5(db, ps, phi)(x) != 0,
    ensures
        jq(ps, c5(db, x)), c5(db, x).len() == 48,
        forall|k: int| 0 <= k < 44 ==> #[trigger] c5(db, x)[k] == x[k],
{
    lemma_key_row_len(t_nat(db), x[35], 4);
}

proof fn lemma_nz4(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int, x: Row)
    requires red_ok(db), x.len() == 40, h4(db, ps, phi)(x) != 0,
    ensures
        jq(ps, c4(db, x)), c4(db, x).len() == 48,
        forall|k: int| 0 <= k < 40 ==> #[trigger] c4(db, x)[k] == x[k],
{
    let n1 = key_row(t_nat(db), 0, x[3]);
    lemma_key_row_len(t_nat(db), x[3], 4);
    let y = x + n1;
    lemma_nz5(db, ps, phi, y);
    assert forall|k: int| 0 <= k < 40 implies #[trigger] c4(db, x)[k] == x[k] by {
        assert(c5(db, y)[k] == y[k]);
    }
}

proof fn lemma_nz3(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int, x: Row)
    requires red_ok(db), x.len() == 32, h3(db, ps, phi)(x) != 0,
    ensures
        jq(ps, c3(db, x)), c3(db, x).len() == 48,
        forall|k: int| 0 <= k < 32 ==> #[trigger] c3(db, x)[k] == x[k],
{
    let c = key_row(t_cust(db), 0, x[24]);
    lemma_key_row_len(t_cust(db), x[24], 8);
    let y = x + c;
    lemma_nz4(db, ps, phi, y);
    assert forall|k: int| 0 <= k < 32 implies #[trigger] c3(db, x)[k] == x[k] by {
        assert(c4(db, y)[k] == y[k]);
    }
}

proof fn lemma_nz2(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int, x: Row)
    requires red_ok(db), x.len() == 23, h2(db, ps, phi)(x) != 0,
    ensures
        jq(ps, c2(db, x)), c2(db, x).len() == 48,
        forall|k: int| 0 <= k < 23 ==> #[trigger] c2(db, x)[k] == x[k],
{
    let o = key_row(t_ord(db), 0, x[7]);
    lemma_key_row_len(t_ord(db), x[7], 9);
    let y = x + o;
    lemma_nz3(db, ps, phi, y);
    assert forall|k: int| 0 <= k < 23 implies #[trigger] c2(db, x)[k] == x[k] by {
        assert(c3(db, y)[k] == y[k]);
    }
}

// ------------------------------------------------------------------------------------------------ one level each

/// n2: the sum over nation of `h6(x ++ n)` is `h5(x)`.
proof fn lemma_level6(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int, x: Row)
    requires red_ok(db), x.len() == 44,
    ensures sum_of(t_nat(db), |n: Row| h6(ps, phi)(x + n)) == h5(db, ps, phi)(x),
{
    let rows = t_nat(db);
    let f = |n: Row| h6(ps, phi)(x + n);
    assert forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) != 0 implies colv(rows[i], 0) == x[35] by {
        let y = x + rows[i];
        assert(jq(ps, y));
        assert(y[35] == x[35] && y[44] == rows[i][0]);
    }
    lemma_sum_by_key(rows, 0, x[35], f);
}

/// n1: the sum over nation of `h5(x ++ n)` is `h4(x)`.
proof fn lemma_level5(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int, x: Row)
    requires red_ok(db), x.len() == 40,
    ensures sum_of(t_nat(db), |n: Row| h5(db, ps, phi)(x + n)) == h4(db, ps, phi)(x),
{
    let rows = t_nat(db);
    let f = |n: Row| h5(db, ps, phi)(x + n);
    assert forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) != 0 implies colv(rows[i], 0) == x[3] by {
        let y = x + rows[i];
        assert(y.len() == 44);
        lemma_nz5(db, ps, phi, y);
        assert(c5(db, y)[3] == y[3] && c5(db, y)[40] == y[40]);
    }
    lemma_sum_by_key(rows, 0, x[3], f);
}

/// customer: the sum over customer of `h4(x ++ c)` is `h3(x)`.
proof fn lemma_level4(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int, x: Row)
    requires red_ok(db), x.len() == 32,
    ensures sum_of(t_cust(db), |c: Row| h4(db, ps, phi)(x + c)) == h3(db, ps, phi)(x),
{
    let rows = t_cust(db);
    let f = |c: Row| h4(db, ps, phi)(x + c);
    assert forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) != 0 implies colv(rows[i], 0) == x[24] by {
        let y = x + rows[i];
        assert(y.len() == 40);
        lemma_nz4(db, ps, phi, y);
        assert(c4(db, y)[32] == y[32] && c4(db, y)[24] == y[24]);
    }
    lemma_sum_by_key(rows, 0, x[24], f);
}

/// orders: the sum over orders of `h3(x ++ o)` is `h2(x)`.
proof fn lemma_level3(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int, x: Row)
    requires red_ok(db), x.len() == 23,
    ensures sum_of(t_ord(db), |o: Row| h3(db, ps, phi)(x + o)) == h2(db, ps, phi)(x),
{
    let rows = t_ord(db);
    let f = |o: Row| h3(db, ps, phi)(x + o);
    assert forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) != 0 implies colv(rows[i], 0) == x[7] by {
        let y = x + rows[i];
        assert(y.len() == 32);
        lemma_nz3(db, ps, phi, y);
        assert(c3(db, y)[23] == y[23] && c3(db, y)[7] == y[7]);
    }
    lemma_sum_by_key(rows, 0, x[7], f);
}

/// supplier: the sum over supplier of `h2(s ++ l)` is `h1(l)`.
proof fn lemma_level2(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int, l: Row)
    requires red_ok(db), l.len() == 16,
    ensures sum_of(t_sup(db), |s: Row| h2(db, ps, phi)(s + l)) == h1(db, ps, phi)(l),
{
    let rows = t_sup(db);
    let f = |s: Row| h2(db, ps, phi)(s + l);
    assert forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) != 0 implies colv(rows[i], 0) == l[2] by {
        let y = rows[i] + l;
        assert(rows[i].len() == 7);
        assert(y.len() == 23);
        lemma_nz2(db, ps, phi, y);
        assert(c2(db, y)[0] == y[0] && c2(db, y)[9] == y[9]);
    }
    lemma_sum_by_key(rows, 0, l[2], f);
}

// ------------------------------------------------------------------------------------------------ the chain

/// One product level: `sum_of(a x b, f) == sum_of(a, g)` when the inner sum over `b` is `g` on every row of `a`.
proof fn lemma_product_level(a: Seq<Row>, b: Seq<Row>, f: spec_fn(Row) -> int, g: spec_fn(Row) -> int)
    requires forall|i: int| 0 <= i < a.len() ==> sum_of(b, |y: Row| f(#[trigger] a[i] + y)) == g(a[i]),
    ensures sum_of(product_rows(a, b), f) == sum_of(a, g),
{
    lemma_sum_of_product(a, b, f);
    lemma_sum_of_ext(a, |x: Row| sum_of(b, |y: Row| f(x + y)), g);
}

/// The sum of `h6` over the 6-way product is the sum of `h1` over lineitem.
pub proof fn lemma_chain(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int)
    requires red_ok(db),
    ensures sum_of(p6(db), h6(ps, phi)) == sum_of(t_li(db), h1(db, ps, phi)),
{
    lemma_level_lens(db);
    let (f6, f5, f4, f3, f2, f1) = (h6(ps, phi), h5(db, ps, phi), h4(db, ps, phi), h3(db, ps, phi), h2(db, ps, phi), h1(db, ps, phi));
    assert forall|i: int| 0 <= i < p5(db).len() implies sum_of(t_nat(db), |y: Row| f6(#[trigger] p5(db)[i] + y)) == f5(p5(db)[i]) by {
        lemma_level6(db, ps, phi, p5(db)[i]);
    }
    lemma_product_level(p5(db), t_nat(db), f6, f5);
    assert forall|i: int| 0 <= i < p4(db).len() implies sum_of(t_nat(db), |y: Row| f5(#[trigger] p4(db)[i] + y)) == f4(p4(db)[i]) by {
        lemma_level5(db, ps, phi, p4(db)[i]);
    }
    lemma_product_level(p4(db), t_nat(db), f5, f4);
    assert forall|i: int| 0 <= i < p3(db).len() implies sum_of(t_cust(db), |y: Row| f4(#[trigger] p3(db)[i] + y)) == f3(p3(db)[i]) by {
        lemma_level4(db, ps, phi, p3(db)[i]);
    }
    lemma_product_level(p3(db), t_cust(db), f4, f3);
    assert forall|i: int| 0 <= i < p2(db).len() implies sum_of(t_ord(db), |y: Row| f3(#[trigger] p2(db)[i] + y)) == f2(p2(db)[i]) by {
        lemma_level3(db, ps, phi, p2(db)[i]);
    }
    lemma_product_level(p2(db), t_ord(db), f3, f2);
    // supplier x lineitem: exchange, then collapse the supplier sum per lineitem row
    lemma_sum_of_product_swap(t_sup(db), t_li(db), f2);
    assert forall|j: int| 0 <= j < t_li(db).len() implies
        (|l: Row| sum_of(t_sup(db), |s: Row| f2(s + l)))(#[trigger] t_li(db)[j]) == f1(t_li(db)[j]) by {
        lemma_level2(db, ps, phi, t_li(db)[j]);
    }
    lemma_sum_of_ext(t_li(db), |l: Row| sum_of(t_sup(db), |s: Row| f2(s + l)), f1);
}

} // verus!
