//! The statement's condition and value on one joined row of query values, and its accumulators as sums over the
//! stored rows.
//!
//! A joined row `w = y ++ z` has ten values: a lineitem row `y = [l_partkey, l_quantity, l_extendedprice,
//! l_discount, l_shipinstruct, l_shipmode]` (`model::li_val`) and a part row `z = [p_partkey, p_brand, p_size,
//! p_container]` (`model::pa_val`). Arm `a` (0, 1, 2: the three OR'ed conjunctions with `$1, $2`, `$3, $4`,
//! `$5, $6`) holds when the keys are equal, the part side holds (`part_arm`: brand, container list, size range) and
//! the lineitem side holds (`li_arm`: quantity window, ship mode, ship instruction). `wq` is the OR of the arms, `wv`
//! the value `l_extendedprice * (1 - l_discount)` as a coefficient of scale 4.
//!
//! The container lists of the arms are disjoint (their first bytes are `S`, `M` and `L`), so at most one arm's part
//! side holds for a part row (`arm_of`); the condition of a joined row is then that arm's key and lineitem side
//! (`lemma_wq_arm`).
//!
//! Accumulator `k` (0 count, 1 sum, 2 absolute mass) of a joined row is `contrib(k, wq, wv)`. Summed part-major:
//! per part row `z`, over every stored lineitem row (`pin`), then over a range of stored part rows (`tot`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::numeric::abs;
use crate::link::expr::{ival, tval};
use crate::link::join::{sum_of, lemma_sum_of_append, lemma_sum_of_zero};
use crate::gendb_entry::layout::PartView;
use super::model::*;

verus! {

// ------------------------------------------------------------------------------------------------ literals

pub open spec fn sm_case() -> Seq<u8> { seq![83u8, 77u8, 32u8, 67u8, 65u8, 83u8, 69u8] }
pub open spec fn sm_box() -> Seq<u8> { seq![83u8, 77u8, 32u8, 66u8, 79u8, 88u8] }
pub open spec fn sm_pack() -> Seq<u8> { seq![83u8, 77u8, 32u8, 80u8, 65u8, 67u8, 75u8] }
pub open spec fn sm_pkg() -> Seq<u8> { seq![83u8, 77u8, 32u8, 80u8, 75u8, 71u8] }
pub open spec fn med_bag() -> Seq<u8> { seq![77u8, 69u8, 68u8, 32u8, 66u8, 65u8, 71u8] }
pub open spec fn med_box() -> Seq<u8> { seq![77u8, 69u8, 68u8, 32u8, 66u8, 79u8, 88u8] }
pub open spec fn med_pkg() -> Seq<u8> { seq![77u8, 69u8, 68u8, 32u8, 80u8, 75u8, 71u8] }
pub open spec fn med_pack() -> Seq<u8> { seq![77u8, 69u8, 68u8, 32u8, 80u8, 65u8, 67u8, 75u8] }
pub open spec fn lg_case() -> Seq<u8> { seq![76u8, 71u8, 32u8, 67u8, 65u8, 83u8, 69u8] }
pub open spec fn lg_box() -> Seq<u8> { seq![76u8, 71u8, 32u8, 66u8, 79u8, 88u8] }
pub open spec fn lg_pack() -> Seq<u8> { seq![76u8, 71u8, 32u8, 80u8, 65u8, 67u8, 75u8] }
pub open spec fn lg_pkg() -> Seq<u8> { seq![76u8, 71u8, 32u8, 80u8, 75u8, 71u8] }

/// `'AIR'`.
pub open spec fn air() -> Seq<u8> { seq![65u8, 73u8, 82u8] }
/// `'AIR REG'`.
pub open spec fn air_reg() -> Seq<u8> { seq![65u8, 73u8, 82u8, 32u8, 82u8, 69u8, 71u8] }
/// `'DELIVER IN PERSON'`.
pub open spec fn dip() -> Seq<u8> {
    seq![68u8, 69u8, 76u8, 73u8, 86u8, 69u8, 82u8, 32u8, 73u8, 78u8, 32u8, 80u8, 69u8, 82u8, 83u8, 79u8, 78u8]
}

/// Container `i` (0..4) of arm `a`, in the statement's order.
pub open spec fn cont_lit(a: int, i: int) -> Seq<u8> {
    if a == 0 {
        if i == 0 { sm_case() } else if i == 1 { sm_box() } else if i == 2 { sm_pack() } else { sm_pkg() }
    } else if a == 1 {
        if i == 0 { med_bag() } else if i == 1 { med_box() } else if i == 2 { med_pkg() } else { med_pack() }
    } else {
        if i == 0 { lg_case() } else if i == 1 { lg_box() } else if i == 2 { lg_pack() } else { lg_pkg() }
    }
}

/// The upper size bound of arm `a`.
pub open spec fn smax(a: int) -> int {
    if a == 0 { 5 } else if a == 1 { 10 } else { 15 }
}

// ------------------------------------------------------------------------------------------------ the binding

/// The bytes of a text literal.
pub open spec fn ptext(l: Literal) -> Seq<u8> {
    match l {
        Literal::Text(b) => b,
        _ => Seq::empty(),
    }
}

/// The value of an integer literal.
pub open spec fn pint(l: Literal) -> int {
    match l {
        Literal::Int { v, .. } => v,
        _ => 0,
    }
}

/// The brand parameter of arm `a` (`$1`, `$3`, `$5`).
pub open spec fn brand_p(ps: Seq<Literal>, a: int) -> Seq<u8> {
    ptext(ps[2 * a])
}

/// The quantity parameter of arm `a` (`$2`, `$4`, `$6`).
pub open spec fn qty_p(ps: Seq<Literal>, a: int) -> int {
    pint(ps[2 * a + 1])
}

// ------------------------------------------------------------------------------------------------ the condition

/// The container is in arm `a`'s list.
pub open spec fn cont_in(a: int, c: Seq<u8>) -> bool {
    c == cont_lit(a, 0) || c == cont_lit(a, 1) || c == cont_lit(a, 2) || c == cont_lit(a, 3)
}

/// `l_shipmode IN ('AIR', 'AIR REG')`.
pub open spec fn mode_in(m: Seq<u8>) -> bool {
    m == air() || m == air_reg()
}

/// The part side of arm `a`: brand, container and size.
pub open spec fn part_arm(ps: Seq<Literal>, a: int, b: Seq<u8>, sz: int, c: Seq<u8>) -> bool {
    b == brand_p(ps, a) && cont_in(a, c) && 1 <= sz && sz <= smax(a)
}

/// The lineitem side of arm `a`: quantity (coefficient of scale 2) in `[$q, $q + 10]`, ship mode and instruction.
pub open spec fn li_arm(ps: Seq<Literal>, a: int, q: int, si: Seq<u8>, sm: Seq<u8>) -> bool {
    100 * qty_p(ps, a) <= q && q <= 100 * (qty_p(ps, a) + 10) && mode_in(sm) && si == dip()
}

/// Arm `a` on a joined row.
pub open spec fn arm_w(ps: Seq<Literal>, a: int, w: Row) -> bool {
    &&& ival(w[6]) == ival(w[0])
    &&& part_arm(ps, a, tval(w[7]), ival(w[8]), tval(w[9]))
    &&& li_arm(ps, a, ival(w[1]), tval(w[4]), tval(w[5]))
}

/// The WHERE condition on a joined row.
pub open spec fn wq(ps: Seq<Literal>, w: Row) -> bool {
    arm_w(ps, 0, w) || arm_w(ps, 1, w) || arm_w(ps, 2, w)
}

/// `l_extendedprice * (1 - l_discount)`: a coefficient of scale 4.
pub open spec fn wv(w: Row) -> int {
    ival(w[2]) * (100 - ival(w[3]))
}

/// The arm whose part side holds for part values `(b, sz, c)` (3: none).
pub open spec fn arm_of(ps: Seq<Literal>, b: Seq<u8>, sz: int, c: Seq<u8>) -> int {
    if part_arm(ps, 0, b, sz, c) { 0 } else if part_arm(ps, 1, b, sz, c) { 1 } else if part_arm(ps, 2, b, sz, c) { 2 } else { 3 }
}

/// The arm of a part value row.
pub open spec fn zarm(ps: Seq<Literal>, z: Row) -> int {
    arm_of(ps, tval(z[1]), ival(z[2]), tval(z[3]))
}

/// The first byte of every container of arm `a`.
pub proof fn lemma_cont_first(a: int, c: Seq<u8>)
    requires 0 <= a < 3, cont_in(a, c),
    ensures c.len() > 0, c[0] == (if a == 0 { 83u8 } else if a == 1 { 77u8 } else { 76u8 }),
{
}

/// The container lists are disjoint: at most one arm's part side holds.
pub proof fn lemma_arms_disjoint(ps: Seq<Literal>, a: int, a2: int, b: Seq<u8>, sz: int, c: Seq<u8>)
    requires 0 <= a < 3, 0 <= a2 < 3, part_arm(ps, a, b, sz, c), part_arm(ps, a2, b, sz, c),
    ensures a == a2,
{
    lemma_cont_first(a, c);
    lemma_cont_first(a2, c);
}

/// Joining lineitem values `y` and part values `z`.
pub proof fn lemma_joined(y: Row, z: Row)
    requires y.len() == 6, z.len() == 4,
    ensures
        (y + z).len() == 10,
        (y + z)[0] == y[0], (y + z)[1] == y[1], (y + z)[2] == y[2], (y + z)[3] == y[3], (y + z)[4] == y[4],
        (y + z)[5] == y[5],
        (y + z)[6] == z[0], (y + z)[7] == z[1], (y + z)[8] == z[2], (y + z)[9] == z[3],
{
}

/// The condition of a joined row is its part's arm (if any) with equal keys and that arm's lineitem side.
pub proof fn lemma_wq_arm(ps: Seq<Literal>, y: Row, z: Row)
    requires y.len() == 6, z.len() == 4,
    ensures
        wq(ps, y + z) == (zarm(ps, z) < 3 && ival(z[0]) == ival(y[0])
            && li_arm(ps, zarm(ps, z), ival(y[1]), tval(y[4]), tval(y[5]))),
        0 <= zarm(ps, z) <= 3,
{
    lemma_joined(y, z);
    let (b, sz, c) = (tval(z[1]), ival(z[2]), tval(z[3]));
    let a = zarm(ps, z);
    if a < 3 {
        assert forall|a2: int| 0 <= a2 < 3 && a2 != a implies !part_arm(ps, a2, b, sz, c) by {
            if part_arm(ps, a2, b, sz, c) {
                lemma_arms_disjoint(ps, a, a2, b, sz, c);
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ accumulators

/// The contribution of a joined row to accumulator `k` (0 count, 1 sum, 2 absolute mass): none unless it qualifies.
pub open spec fn contrib(k: int, q: bool, v: int) -> int {
    if !q { 0 } else if k == 0 { 1 } else if k == 1 { v } else { abs(v) }
}

/// Accumulator `k`'s term of a joined row.
pub open spec fn term(ps: Seq<Literal>, k: int) -> spec_fn(Row) -> int {
    |w: Row| contrib(k, wq(ps, w), wv(w))
}

/// Accumulator `k`'s term of lineitem row `y` joined with part row `z`.
pub open spec fn jt(ps: Seq<Literal>, k: int, z: Row) -> spec_fn(Row) -> int {
    |y: Row| term(ps, k)(y + z)
}

/// Per part row `z`: accumulator `k` over every stored lineitem row.
pub open spec fn pin(fp: Seq<PartView>, ps: Seq<Literal>, k: int) -> spec_fn(Row) -> int {
    |z: Row| sum_of(li_rows(fp), jt(ps, k, z))
}

/// Accumulator `k` over the stored part rows `j0 .. j1`, each joined with every stored lineitem row.
pub open spec fn tot(fp: Seq<PartView>, cp: Seq<PartView>, ps: Seq<Literal>, k: int, j0: int, j1: int) -> int {
    sum_of(pa_rows(cp).subrange(j0, j1), pin(fp, ps, k))
}

/// Per part row `z`: accumulator `k` over the key index positions `p0 .. p1`.
pub open spec fn kin(fp: Seq<PartView>, ps: Seq<Literal>, k: int, z: Row, p0: int, p1: int) -> int {
    sum_of(irows(fp).subrange(p0, p1), jt(ps, k, z))
}

/// Contributions: count 0 or 1, sum within the mass, mass nonnegative.
pub proof fn lemma_contrib_bounds(q: bool, v: int)
    ensures
        0 <= contrib(0, q, v) <= 1,
        -contrib(2, q, v) <= contrib(1, q, v) <= contrib(2, q, v),
        contrib(2, q, v) >= 0,
        contrib(0, q, v) == 0 ==> contrib(1, q, v) == 0 && contrib(2, q, v) == 0,
{
}

// ------------------------------------------------------------------------------------------------ range sums

/// One more row of a range.
pub proof fn lemma_sum_step(rows: Seq<Row>, f: spec_fn(Row) -> int, r0: int, i: int)
    requires 0 <= r0 <= i < rows.len(),
    ensures sum_of(rows.subrange(r0, i + 1), f) == sum_of(rows.subrange(r0, i), f) + f(rows[i]),
{
    let s = rows.subrange(r0, i + 1);
    assert(s.drop_last() =~= rows.subrange(r0, i));
    assert(s.last() == rows[i]);
}

/// The empty range sums to 0.
pub proof fn lemma_sum_empty(rows: Seq<Row>, f: spec_fn(Row) -> int, r0: int)
    requires 0 <= r0 <= rows.len(),
    ensures sum_of(rows.subrange(r0, r0), f) == 0,
{
    assert(rows.subrange(r0, r0).len() == 0);
}

/// A range splits at any point.
pub proof fn lemma_sum_split(rows: Seq<Row>, f: spec_fn(Row) -> int, a: int, b: int, c: int)
    requires 0 <= a <= b <= c <= rows.len(),
    ensures sum_of(rows.subrange(a, c), f) == sum_of(rows.subrange(a, b), f) + sum_of(rows.subrange(b, c), f),
{
    assert(rows.subrange(a, c) =~= rows.subrange(a, b) + rows.subrange(b, c));
    lemma_sum_of_append(rows.subrange(a, b), rows.subrange(b, c), f);
}

/// A range whose terms are all zero sums to 0.
pub proof fn lemma_sum_zero_range(rows: Seq<Row>, f: spec_fn(Row) -> int, a: int, b: int)
    requires
        0 <= a <= b <= rows.len(),
        forall|i: int| a <= i < b ==> f(#[trigger] rows[i]) == 0,
    ensures sum_of(rows.subrange(a, b), f) == 0,
{
    let w = rows.subrange(a, b);
    assert forall|i: int| 0 <= i < w.len() implies f(#[trigger] w[i]) == 0 by {
        assert(w[i] == rows[a + i]);
    }
    lemma_sum_of_zero(w, f);
}

/// A range of nonnegative terms sums to at least any of its subranges.
pub proof fn lemma_sum_sub_le(rows: Seq<Row>, f: spec_fn(Row) -> int, a: int, b: int, c: int, d: int)
    requires
        0 <= a <= b <= c <= d <= rows.len(),
        forall|i: int| a <= i < d ==> f(#[trigger] rows[i]) >= 0,
    ensures
        sum_of(rows.subrange(b, c), f) <= sum_of(rows.subrange(a, d), f),
        sum_of(rows.subrange(b, c), f) >= 0,
{
    lemma_sum_split(rows, f, a, b, d);
    lemma_sum_split(rows, f, b, c, d);
    lemma_sum_nonneg(rows, f, a, b);
    lemma_sum_nonneg(rows, f, c, d);
    lemma_sum_nonneg(rows, f, b, c);
}

/// A range of nonnegative terms has a nonnegative sum.
pub proof fn lemma_sum_nonneg(rows: Seq<Row>, f: spec_fn(Row) -> int, a: int, b: int)
    requires
        0 <= a <= b <= rows.len(),
        forall|i: int| a <= i < b ==> f(#[trigger] rows[i]) >= 0,
    ensures sum_of(rows.subrange(a, b), f) >= 0,
    decreases b - a,
{
    if b > a {
        lemma_sum_nonneg(rows, f, a, b - 1);
        lemma_sum_step(rows, f, a, b - 1);
    } else {
        lemma_sum_empty(rows, f, a);
    }
}

/// Termwise bounds `-g <= f <= g` and `0 <= h <= 1`, `h == 0 ==> f == g == 0` carry over to range sums.
pub proof fn lemma_sum_within(rows: Seq<Row>, f: spec_fn(Row) -> int, g: spec_fn(Row) -> int, h: spec_fn(Row) -> int,
    a: int, b: int)
    requires
        0 <= a <= b <= rows.len(),
        forall|i: int| a <= i < b ==> -g(#[trigger] rows[i]) <= f(rows[i]) <= g(rows[i]),
        forall|i: int| a <= i < b ==> 0 <= #[trigger] h(rows[i]),
        forall|i: int| a <= i < b ==> h(#[trigger] rows[i]) == 0 ==> g(rows[i]) == 0,
    ensures
        -sum_of(rows.subrange(a, b), g) <= sum_of(rows.subrange(a, b), f) <= sum_of(rows.subrange(a, b), g),
        sum_of(rows.subrange(a, b), h) >= 0,
        sum_of(rows.subrange(a, b), h) == 0 ==> sum_of(rows.subrange(a, b), g) == 0,
    decreases b - a,
{
    if b > a {
        lemma_sum_within(rows, f, g, h, a, b - 1);
        lemma_sum_step(rows, f, a, b - 1);
        lemma_sum_step(rows, g, a, b - 1);
        lemma_sum_step(rows, h, a, b - 1);
        assert(g(rows[b - 1]) >= 0);
        assert(sum_of(rows.subrange(a, b - 1), g) >= 0);
    } else {
        lemma_sum_empty(rows, f, a);
        lemma_sum_empty(rows, g, a);
        lemma_sum_empty(rows, h, a);
    }
}

/// The three accumulators' terms: count in `[0, 1]`, sum within the mass, mass 0 when the count is.
pub proof fn lemma_term_bounds(ps: Seq<Literal>, w: Row)
    ensures
        0 <= term(ps, 0)(w) <= 1,
        -term(ps, 2)(w) <= term(ps, 1)(w) <= term(ps, 2)(w),
        term(ps, 0)(w) == 0 ==> term(ps, 2)(w) == 0,
{
    lemma_contrib_bounds(wq(ps, w), wv(w));
}

} // verus!
