//! The statement over value rows, independent of storage.
//!
//! A lineitem value row is `[l_partkey, l_quantity, l_extendedprice]` (`yrow`, numerics as coefficients of scale 2), a
//! part value row is `[p_partkey, p_brand, p_container]`. For the lineitem rows `ys` (any order: every quantity here
//! is a sum over `ys`, so only its multiset matters, `lemma_perm_*`):
//! - `sub_val(ys, k)`: the correlated subquery `0.2 * AVG(l_quantity)` over the rows of key `k`: NULL without such a
//!   row, else `2 q` at scale `r + 1` where `q` at scale `r` is the PostgreSQL quotient `num_div(sum, 2, count, 0)`;
//! - `kept(ys, b, c, y, z)`: the WHERE condition of the joined row `(y, z)` is true for brand `b` and container `c`;
//! - `psum`/`pcnt`/`pmass`: per part row `z`, the sum of l_extendedprice, the number and the absolute sum of the
//!   lineitem rows it keeps.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::fns::div::*;
use crate::link::join::*;
use crate::link::expr::ival;

verus! {

/// `10^15`: the exclusive bound of a numeric(15, 2) coefficient.
pub open spec fn p15() -> int {
    1_000_000_000_000_000
}

/// A lineitem value row `[l_partkey, l_quantity, l_extendedprice]`.
pub open spec fn yrow(k: int, q: int, x: int) -> Row {
    seq![Val::Int(k), Val::Num { coeff: q, scale: 2 }, Val::Num { coeff: x, scale: 2 }]
}

/// A typed lineitem value row (numeric(15, 2) coefficients below `10^15` in absolute value).
pub open spec fn y_ok(y: Row) -> bool {
    &&& y == yrow(ival(y[0]), ival(y[1]), ival(y[2]))
    &&& -p15() < ival(y[1]) < p15()
    &&& -p15() < ival(y[2]) < p15()
}

/// Every row typed.
pub open spec fn ys_ok(ys: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < ys.len() ==> y_ok(#[trigger] ys[i])
}

/// The row has key `k`.
pub open spec fn is_key(y: Row, k: int) -> bool {
    y[0] == Val::Int(k)
}

/// Quantity of a row of key `k`, else 0.
pub open spec fn tq(k: int) -> spec_fn(Row) -> int {
    |y: Row| if is_key(y, k) { ival(y[1]) } else { 0int }
}

/// 1 for a row of key `k`, else 0.
pub open spec fn t1(k: int) -> spec_fn(Row) -> int {
    |y: Row| if is_key(y, k) { 1int } else { 0int }
}

/// Sum of the quantity coefficients of the rows of key `k`.
pub open spec fn qsum(ys: Seq<Row>, k: int) -> int {
    sum_of(ys, tq(k))
}

/// Number of rows of key `k`.
pub open spec fn qcnt(ys: Seq<Row>, k: int) -> int {
    sum_of(ys, t1(k))
}

/// `0.2 * a` for the AVG outcome `a` (a numeric `q` at scale `r` gives `2 q` at scale `r + 1`).
pub open spec fn times_fifth(a: Result<Val, SqlError>) -> Val {
    match a {
        Ok(Val::Num { coeff, scale }) => Val::Num { coeff: 2 * coeff, scale: scale + 1 },
        _ => Val::Null,
    }
}

/// The subquery's value for part key `k`.
pub open spec fn sub_val(ys: Seq<Row>, k: int) -> Val {
    if qcnt(ys, k) == 0 { Val::Null } else { times_fifth(num_div(qsum(ys, k), 2, qcnt(ys, k), 0)) }
}

/// `a < b` is true (SQL comparison; NULL gives Unknown).
pub open spec fn lt_true(a: Val, b: Val) -> bool {
    cmp_truth(CmpOp::Lt, a, b) == Ok::<Truth, SqlError>(Truth::True)
}

/// The WHERE condition of the joined row of lineitem value row `y` and part value row `z`.
pub open spec fn kept(ys: Seq<Row>, b: Seq<u8>, c: Seq<u8>, y: Row, z: Row) -> bool {
    &&& z[0] == y[0]
    &&& z[1] == Val::Text(b)
    &&& z[2] == Val::Text(c)
    &&& lt_true(y[1], sub_val(ys, ival(z[0])))
}

/// l_extendedprice of a kept row, else 0.
pub open spec fn tsum(ys: Seq<Row>, b: Seq<u8>, c: Seq<u8>, z: Row) -> spec_fn(Row) -> int {
    |y: Row| if kept(ys, b, c, y, z) { ival(y[2]) } else { 0int }
}

/// 1 for a kept row, else 0.
pub open spec fn tcnt(ys: Seq<Row>, b: Seq<u8>, c: Seq<u8>, z: Row) -> spec_fn(Row) -> int {
    |y: Row| if kept(ys, b, c, y, z) { 1int } else { 0int }
}

/// |l_extendedprice| of a kept row, else 0.
pub open spec fn tmass(ys: Seq<Row>, b: Seq<u8>, c: Seq<u8>, z: Row) -> spec_fn(Row) -> int {
    |y: Row| if kept(ys, b, c, y, z) { abs(ival(y[2])) } else { 0int }
}

/// Per part row: the sum of l_extendedprice over the lineitem rows it keeps.
pub open spec fn psum(ys: Seq<Row>, b: Seq<u8>, c: Seq<u8>, z: Row) -> int {
    sum_of(ys, tsum(ys, b, c, z))
}

/// Per part row: the number of lineitem rows it keeps.
pub open spec fn pcnt(ys: Seq<Row>, b: Seq<u8>, c: Seq<u8>, z: Row) -> int {
    sum_of(ys, tcnt(ys, b, c, z))
}

/// Per part row: the absolute sum of l_extendedprice over the lineitem rows it keeps.
pub open spec fn pmass(ys: Seq<Row>, b: Seq<u8>, c: Seq<u8>, z: Row) -> int {
    sum_of(ys, tmass(ys, b, c, z))
}

/// Totals over part rows `zs` of a per-part function.
pub open spec fn over_parts(zs: Seq<Row>, f: spec_fn(Row) -> int) -> int {
    sum_of(zs, f)
}

// ------------------------------------------------------------------------------------------------ order independence

/// The same multiset of lineitem rows gives the same subquery value.
pub proof fn lemma_perm_sub(ys1: Seq<Row>, ys2: Seq<Row>, k: int)
    requires ys1.to_multiset() == ys2.to_multiset(),
    ensures
        qsum(ys1, k) == qsum(ys2, k),
        qcnt(ys1, k) == qcnt(ys2, k),
        sub_val(ys1, k) == sub_val(ys2, k),
{
    lemma_sum_of_perm(ys1, ys2, tq(k));
    lemma_sum_of_perm(ys1, ys2, t1(k));
}

/// The same multiset of lineitem rows gives the same per-part sums.
pub proof fn lemma_perm_part(ys1: Seq<Row>, ys2: Seq<Row>, b: Seq<u8>, c: Seq<u8>, z: Row)
    requires ys1.to_multiset() == ys2.to_multiset(),
    ensures
        psum(ys1, b, c, z) == psum(ys2, b, c, z),
        pcnt(ys1, b, c, z) == pcnt(ys2, b, c, z),
        pmass(ys1, b, c, z) == pmass(ys2, b, c, z),
{
    lemma_perm_sub(ys1, ys2, ival(z[0]));
    assert forall|y: Row| #[trigger] kept(ys1, b, c, y, z) == kept(ys2, b, c, y, z) by {}
    lemma_sum_of_perm(ys1, ys2, tsum(ys1, b, c, z));
    lemma_sum_of_perm(ys1, ys2, tcnt(ys1, b, c, z));
    lemma_sum_of_perm(ys1, ys2, tmass(ys1, b, c, z));
    assert forall|i: int| 0 <= i < ys2.len() implies tsum(ys1, b, c, z)(#[trigger] ys2[i]) == tsum(ys2, b, c, z)(ys2[i]) by {}
    assert forall|i: int| 0 <= i < ys2.len() implies tcnt(ys1, b, c, z)(#[trigger] ys2[i]) == tcnt(ys2, b, c, z)(ys2[i]) by {}
    assert forall|i: int| 0 <= i < ys2.len() implies tmass(ys1, b, c, z)(#[trigger] ys2[i]) == tmass(ys2, b, c, z)(ys2[i]) by {}
    lemma_sum_of_ext(ys2, tsum(ys1, b, c, z), tsum(ys2, b, c, z));
    lemma_sum_of_ext(ys2, tcnt(ys1, b, c, z), tcnt(ys2, b, c, z));
    lemma_sum_of_ext(ys2, tmass(ys1, b, c, z), tmass(ys2, b, c, z));
}

// ------------------------------------------------------------------------------------------------ sums

/// A sum of terms each at most the corresponding other term is at most the other sum.
pub proof fn lemma_sum_of_le(rows: Seq<Row>, f: spec_fn(Row) -> int, g: spec_fn(Row) -> int)
    requires forall|i: int| 0 <= i < rows.len() ==> f(#[trigger] rows[i]) <= g(rows[i]),
    ensures sum_of(rows, f) <= sum_of(rows, g),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert forall|i: int| 0 <= i < ri.len() implies f(#[trigger] ri[i]) <= g(ri[i]) by {
            assert(ri[i] == rows[i]);
        }
        lemma_sum_of_le(ri, f, g);
        assert(f(rows[rows.len() - 1]) <= g(rows[rows.len() - 1]));
    }
}

/// A sum of a constant.
pub proof fn lemma_sum_of_const(rows: Seq<Row>, f: spec_fn(Row) -> int, v: int)
    requires forall|i: int| 0 <= i < rows.len() ==> f(#[trigger] rows[i]) == v,
    ensures sum_of(rows, f) == rows.len() * v,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert forall|i: int| 0 <= i < ri.len() implies f(#[trigger] ri[i]) == v by {
            assert(ri[i] == rows[i]);
        }
        lemma_sum_of_const(ri, f, v);
        assert(f(rows[rows.len() - 1]) == v);
        assert(ri.len() * v + v == rows.len() * v) by (nonlinear_arith) requires rows.len() == ri.len() + 1;
    }
}

/// Nonnegative terms: nonnegative sum.
pub proof fn lemma_sum_of_nonneg(rows: Seq<Row>, f: spec_fn(Row) -> int)
    requires forall|i: int| 0 <= i < rows.len() ==> f(#[trigger] rows[i]) >= 0,
    ensures sum_of(rows, f) >= 0,
{
    lemma_sum_of_le(rows, |r: Row| 0int, f);
    lemma_sum_of_zero(rows, |r: Row| 0int);
}

/// The sum of one more row of a sequence prefix.
pub proof fn lemma_sum_of_take(rows: Seq<Row>, f: spec_fn(Row) -> int, i: int)
    requires 0 <= i < rows.len(),
    ensures sum_of(rows.take(i + 1), f) == sum_of(rows.take(i), f) + f(rows[i]),
{
    assert(rows.take(i + 1).drop_last() =~= rows.take(i));
}

/// The sum over a subrange `[a, b)` extended by its next row.
pub proof fn lemma_sum_of_sub_push(rows: Seq<Row>, f: spec_fn(Row) -> int, a: int, b: int)
    requires 0 <= a <= b < rows.len(),
    ensures sum_of(rows.subrange(a, b + 1), f) == sum_of(rows.subrange(a, b), f) + f(rows[b]),
{
    assert(rows.subrange(a, b + 1).drop_last() =~= rows.subrange(a, b));
}

/// A sum over a subrange of nonnegative terms is at most the sum over the whole sequence.
pub proof fn lemma_sum_of_sub_le(rows: Seq<Row>, f: spec_fn(Row) -> int, a: int, b: int)
    requires
        0 <= a <= b <= rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> f(#[trigger] rows[i]) >= 0,
    ensures sum_of(rows.subrange(a, b), f) <= sum_of(rows, f),
{
    let (x, y, z) = (rows.subrange(0, a), rows.subrange(a, b), rows.subrange(b, rows.len() as int));
    assert(rows =~= x + y + z);
    lemma_sum_of_append(x + y, z, f);
    lemma_sum_of_append(x, y, f);
    assert forall|i: int| 0 <= i < x.len() implies f(#[trigger] x[i]) >= 0 by {
        assert(x[i] == rows[i]);
    }
    assert forall|i: int| 0 <= i < z.len() implies f(#[trigger] z[i]) >= 0 by {
        assert(z[i] == rows[b + i]);
    }
    lemma_sum_of_nonneg(x, f);
    lemma_sum_of_nonneg(z, f);
}

/// A sum whose terms vanish outside `[a, b)` is the sum over `[a, b)`.
pub proof fn lemma_sum_of_window(rows: Seq<Row>, f: spec_fn(Row) -> int, a: int, b: int)
    requires
        0 <= a <= b <= rows.len(),
        forall|i: int| 0 <= i < rows.len() && !(a <= i < b) ==> f(#[trigger] rows[i]) == 0,
    ensures sum_of(rows, f) == sum_of(rows.subrange(a, b), f),
{
    let (x, y, z) = (rows.subrange(0, a), rows.subrange(a, b), rows.subrange(b, rows.len() as int));
    assert(rows =~= x + y + z);
    lemma_sum_of_append(x + y, z, f);
    lemma_sum_of_append(x, y, f);
    assert forall|i: int| 0 <= i < x.len() implies f(#[trigger] x[i]) == 0 by {
        assert(x[i] == rows[i]);
    }
    assert forall|i: int| 0 <= i < z.len() implies f(#[trigger] z[i]) == 0 by {
        assert(z[i] == rows[b + i]);
    }
    lemma_sum_of_zero(x, f);
    lemma_sum_of_zero(z, f);
}

// ------------------------------------------------------------------------------------------------ bounds

/// The quantity sum of key `k` is bounded by the count times `10^15`.
pub proof fn lemma_qsum_bound(ys: Seq<Row>, k: int)
    requires ys_ok(ys),
    ensures
        0 <= qcnt(ys, k) <= ys.len(),
        -qcnt(ys, k) * p15() <= qsum(ys, k) <= qcnt(ys, k) * p15(),
    decreases ys.len(),
{
    if ys.len() > 0 {
        let d = ys.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies y_ok(#[trigger] d[i]) by {
            assert(d[i] == ys[i]);
        }
        lemma_qsum_bound(d, k);
        assert(y_ok(ys[ys.len() - 1]));
        let c0 = qcnt(d, k);
        if is_key(ys.last(), k) {
            assert(-(c0 + 1) * p15() == -c0 * p15() - p15()) by (nonlinear_arith);
            assert((c0 + 1) * p15() == c0 * p15() + p15()) by (nonlinear_arith);
        }
    }
}

/// Every per-part mass term is nonnegative, the absolute value of the sum term, and at most `10^15` on rows of
/// the part's key (0 on others).
pub proof fn lemma_tmass_le(ys: Seq<Row>, b: Seq<u8>, c: Seq<u8>, z: Row, y: Row)
    requires y_ok(y),
    ensures
        0 <= tmass(ys, b, c, z)(y) <= if z[0] == y[0] { p15() } else { 0 },
        tmass(ys, b, c, z)(y) == abs(tsum(ys, b, c, z)(y)),
{
}

/// The part keys (column 0) are pairwise distinct.
pub open spec fn keys_distinct(zs: Seq<Row>) -> bool {
    forall|a: int, b: int| 0 <= a < zs.len() && 0 <= b < zs.len() && a != b ==> #[trigger] zs[a][0] != #[trigger] zs[b][0]
}

/// `m` on the part rows of key `v`, else 0.
pub open spec fn key_term(v: Val, m: int) -> spec_fn(Row) -> int {
    |z: Row| if z[0] == v { m } else { 0int }
}

/// Distinct keys: at most one part row has key `v`, so its term sums to at most `m`.
pub proof fn lemma_key_once(zs: Seq<Row>, v: Val, m: int)
    requires keys_distinct(zs), m >= 0,
    ensures 0 <= sum_of(zs, key_term(v, m)) <= m,
    decreases zs.len(),
{
    if zs.len() > 0 {
        let d = zs.drop_last();
        assert forall|a: int, b: int| 0 <= a < d.len() && 0 <= b < d.len() && a != b implies #[trigger] d[a][0] != #[trigger] d[b][0] by {
            assert(d[a] == zs[a] && d[b] == zs[b]);
        }
        lemma_key_once(d, v, m);
        if zs.last()[0] == v {
            assert forall|i: int| 0 <= i < d.len() implies key_term(v, m)(#[trigger] d[i]) == 0 by {
                assert(d[i] == zs[i]);
                assert(zs[i][0] != zs[zs.len() - 1][0]);
            }
            lemma_sum_of_zero(d, key_term(v, m));
        }
    }
}

/// The total mass over the part rows: each typed lineitem row is kept by at most one part row (distinct part keys),
/// so the total is at most `|ys| * 10^15`.
pub proof fn lemma_mass_bound(ys: Seq<Row>, zs: Seq<Row>, b: Seq<u8>, c: Seq<u8>)
    requires ys_ok(ys), keys_distinct(zs),
    ensures 0 <= sum_of(zs, |z: Row| pmass(ys, b, c, z)) <= ys.len() * p15(),
{
    let h = |z: Row, y: Row| tmass(ys, b, c, z)(y);
    lemma_sum_of_swap(zs, ys, h);
    assert forall|i: int| 0 <= i < zs.len() implies (|z: Row| pmass(ys, b, c, z))(#[trigger] zs[i])
        == (|x: Row| sum_of(ys, |y: Row| h(x, y)))(zs[i]) by {
        let z = zs[i];
        lemma_sum_of_ext(ys, tmass(ys, b, c, z), |y: Row| h(z, y));
    }
    lemma_sum_of_ext(zs, |z: Row| pmass(ys, b, c, z), |x: Row| sum_of(ys, |y: Row| h(x, y)));
    let g = |y: Row| sum_of(zs, |x: Row| h(x, y));
    assert forall|i: int| 0 <= i < ys.len() implies 0 <= #[trigger] g(ys[i]) <= p15() by {
        let y = ys[i];
        assert(y_ok(y));
        assert forall|j: int| 0 <= j < zs.len() implies (|x: Row| h(x, y))(#[trigger] zs[j]) <= key_term(y[0], p15())(zs[j])
            && 0 <= (|x: Row| h(x, y))(zs[j]) by {
            lemma_tmass_le(ys, b, c, zs[j], y);
        }
        lemma_sum_of_le(zs, |x: Row| h(x, y), key_term(y[0], p15()));
        lemma_sum_of_nonneg(zs, |x: Row| h(x, y));
        lemma_key_once(zs, y[0], p15());
    }
    lemma_sum_of_le(ys, g, |y: Row| p15());
    lemma_sum_of_const(ys, |y: Row| p15(), p15());
    lemma_sum_of_nonneg(ys, g);
}

/// Per part row: `|psum| <= pmass`, `pmass >= 0`, `pcnt >= 0`, and a kept row exists when the count is positive.
pub proof fn lemma_part_sums(ys: Seq<Row>, b: Seq<u8>, c: Seq<u8>, z: Row)
    requires ys_ok(ys),
    ensures
        -pmass(ys, b, c, z) <= psum(ys, b, c, z) <= pmass(ys, b, c, z),
        pcnt(ys, b, c, z) >= 0,
        pmass(ys, b, c, z) >= 0,
    decreases ys.len(),
{
    if ys.len() > 0 {
        let d = ys.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies y_ok(#[trigger] d[i]) by {
            assert(d[i] == ys[i]);
        }
        lemma_part_sums_rec(ys, d, b, c, z);
    }
}

/// One step of `lemma_part_sums` over the prefix `d` (the subquery stays over all of `ys`).
proof fn lemma_part_sums_rec(ys: Seq<Row>, d: Seq<Row>, b: Seq<u8>, c: Seq<u8>, z: Row)
    requires ys_ok(d),
    ensures
        -sum_of(d, tmass(ys, b, c, z)) <= sum_of(d, tsum(ys, b, c, z)) <= sum_of(d, tmass(ys, b, c, z)),
        sum_of(d, tcnt(ys, b, c, z)) >= 0,
        sum_of(d, tmass(ys, b, c, z)) >= 0,
    decreases d.len(),
{
    if d.len() > 0 {
        let e = d.drop_last();
        assert forall|i: int| 0 <= i < e.len() implies y_ok(#[trigger] e[i]) by {
            assert(e[i] == d[i]);
        }
        lemma_part_sums_rec(ys, e, b, c, z);
    }
}

} // verus!
