//! Word scan of the Q21 counts over storage `li_ordruns` (facts' columns plus the run lengths of l_orderkey; model:
//! `super::model`, runs: `super::runs`). A task's stored lineitem rows are read in words of up to 64 consecutive rows
//! inside one group; bit `u` of a word's masks is row `a + u`:
//! - `bm` (`run_bits`): a run of equal l_orderkey (one stored order, `runs_aligned`) starts at the row; walked from
//!   the run lengths (1 byte per order), so l_orderkey itself is never read by the scan;
//! - `lm`: the row is late (`l_commitdate < l_receiptdate`), from the codes and the group's clamped base difference
//!   (`late_bits64`: a constant trip count for full words, so the compiler vectorizes it);
//! - `sm` (`first_late`): late rows whose previous row is not a late row of the same order; only these rows'
//!   suppliers are tested against the slot bitmap (`x`), except rows killed by a neighbouring late row of the same
//!   order with another supplier (`change_bits64`, `lemma_kill`);
//! - `cm`: the candidates: `x`, plus every late row continuing a late stretch of one order from a candidate (one
//!   carry-chain fill, `fill` / `lemma_fill`).
//! A row outside `cm` never counts (`nohit`): it is not late, or its supplier is no slot, or it continues a late
//! stretch of its order whose previous row never counts (`lemma_chain`: a counting late row's late predecessor of the
//! same order has the same supplier, so it counts too). Each candidate is decided exactly over its run (`eval_run`):
//! the run holding it is found by walking the run lengths from the word's first run, EXISTS / NOT EXISTS scan the
//! run's rows (just read), and the order's status is read at row `r` of orders only for a row that passes them
//! (`lemma_run_lines`: the run is exactly the lines of stored order `r`).
use vstd::prelude::*;
use vstd::prelude::{add, sub, mul};
use vstd::std_specs::bits::{axiom_u64_trailing_zeros, u64_trailing_zeros};
use super::model::*;
use super::kernel::*;
use super::supp::*;
use super::common::occ::*;
use super::runs::*;

verus! {

// ------------------------------------------------------------------------------------------------ bits

/// Bit `i` of `x`.
pub open spec fn bt(x: u64, i: u64) -> bool {
    (x >> i) & 1u64 == 1u64
}

/// Late rows whose previous row is not known to be a late row of the same order: `lin` is the previous word's last
/// late bit, `bm` the boundary bits.
pub open spec fn first_late(lm: u64, bm: u64, lin: u64) -> u64 {
    lm & (bm | !((lm << 1u64) | lin))
}

/// `x` and every block of `m`'s consecutive bits whose bit below is in `x` (or, at bit 0, `cin`).
pub open spec fn fill(x: u64, m: u64, cin: u64) -> u64 {
    x | ((add(m, ((x << 1u64) | cin) & m) ^ m) & m)
}

/// The bits below `len` (`len <= 64`).
pub open spec fn low_mask(len: u64) -> u64 {
    if len >= 64 { !0u64 } else { sub(1u64 << len, 1u64) }
}

pub proof fn lemma_zero_bit(u: u64)
    requires u < 64,
    ensures !bt(0u64, u),
{
    assert((0u64 >> u) & 1u64 != 1u64) by (bit_vector) requires u < 64;
}

proof fn lemma_or_bit(acc: u64, b: u64, i: u64, u: u64)
    requires i < 64, b <= 1, u < 64,
    ensures bt(acc | (b << i), u) == (bt(acc, u) || (u == i && b == 1)),
{
    assert(((acc | (b << i)) >> u) & 1u64 == 1u64 <==> (((acc >> u) & 1u64 == 1u64) || (u == i && b == 1)))
        by (bit_vector) requires i < 64, b <= 1, u < 64;
}

/// Setting bit `i` of an accumulator whose bits from `i` on are clear.
pub proof fn lemma_or_bits(acc: u64, b: u64, i: u64)
    requires i < 64, b <= 1,
    ensures forall|u: u64| u < 64 ==> #[trigger] bt(acc | (b << i), u) == (bt(acc, u) || (u == i && b == 1)),
{
    assert forall|u: u64| u < 64 implies #[trigger] bt(acc | (b << i), u) == (bt(acc, u) || (u == i && b == 1)) by {
        lemma_or_bit(acc, b, i, u);
    }
}

proof fn lemma_clear_bit(t: u64, i: u64, u: u64)
    requires i < 64, u < 64,
    ensures bt(t & !(1u64 << i), u) == (bt(t, u) && u != i),
{
    assert(((t & !(1u64 << i)) >> u) & 1u64 == 1u64 <==> (((t >> u) & 1u64 == 1u64) && u != i)) by (bit_vector)
        requires i < 64, u < 64;
}

pub proof fn lemma_clear_bits(t: u64, i: u64)
    requires i < 64, bt(t, i),
    ensures
        forall|u: u64| u < 64 ==> #[trigger] bt(t & !(1u64 << i), u) == (bt(t, u) && u != i),
        (t & !(1u64 << i)) < t,
{
    assert forall|u: u64| u < 64 implies #[trigger] bt(t & !(1u64 << i), u) == (bt(t, u) && u != i) by {
        lemma_clear_bit(t, i, u);
    }
    assert((t >> i) & 1u64 == 1u64 ==> (t & !(1u64 << i)) < t) by (bit_vector) requires i < 64;
}

proof fn lemma_and_bit(a: u64, b: u64, u: u64)
    requires u < 64,
    ensures
        bt(a & b, u) == (bt(a, u) && bt(b, u)),
        bt(a & !b, u) == (bt(a, u) && !bt(b, u)),
        bt(a | b, u) == (bt(a, u) || bt(b, u)),
{
    assert(((a & b) >> u) & 1u64 == 1u64 <==> ((a >> u) & 1u64 == 1u64 && (b >> u) & 1u64 == 1u64)) by (bit_vector)
        requires u < 64;
    assert(((a & !b) >> u) & 1u64 == 1u64 <==> ((a >> u) & 1u64 == 1u64 && (b >> u) & 1u64 != 1u64)) by (bit_vector)
        requires u < 64;
    assert(((a | b) >> u) & 1u64 == 1u64 <==> ((a >> u) & 1u64 == 1u64 || (b >> u) & 1u64 == 1u64)) by (bit_vector)
        requires u < 64;
}

proof fn lemma_first_late_bit(lm: u64, bm: u64, lin: u64, u: u64)
    requires lin <= 1, u < 64,
    ensures
        bt(first_late(lm, bm, lin), u) == (bt(lm, u) && (bt(bm, u)
            || !(if u == 0 { lin == 1 } else { bt(lm, (u - 1) as u64) }))),
{
    assert(((lm & (bm | !((lm << 1u64) | lin))) >> u) & 1u64 == 1u64 <==> ((lm >> u) & 1u64 == 1u64
        && ((bm >> u) & 1u64 == 1u64 || !(if u == 0 { lin == 1 } else { (lm >> sub(u, 1u64)) & 1u64 == 1u64 }))))
        by (bit_vector) requires lin <= 1, u < 64;
}

/// The fill leaves no bit of `m` clear whose bit below is set (or, at bit 0, whose carry-in is set).
proof fn lemma_fill(x: u64, m: u64, cin: u64, u: u64)
    requires x & m == 0, cin <= 1, u < 64,
    ensures
        (bt(m, u) && !bt(fill(x, m, cin), u)) ==> (if u == 0 { cin == 0 } else { !bt(fill(x, m, cin), (u - 1) as u64) }),
        !bt(fill(x, m, cin), u) ==> !bt(x, u),
{
    assert(({
        let cm = x | ((add(m, ((x << 1u64) | cin) & m) ^ m) & m);
        (((cm >> u) & 1u64 == 1u64) == false && (m >> u) & 1u64 == 1u64)
            ==> (if u == 0 { cin == 0 } else { (cm >> sub(u, 1u64)) & 1u64 != 1u64 })
    })) by (bit_vector) requires x & m == 0, cin <= 1, u < 64;
    assert(({
        let cm = x | ((add(m, ((x << 1u64) | cin) & m) ^ m) & m);
        ((cm >> u) & 1u64 != 1u64) ==> (x >> u) & 1u64 != 1u64
    })) by (bit_vector) requires u < 64;
}

proof fn lemma_disjoint(x0: u64, s: u64, l: u64)
    ensures (x0 & s) & (l & !s) == 0,
{
    assert((x0 & s) & (l & !s) == 0) by (bit_vector);
}

proof fn lemma_wadd(m: u64, t: u64)
    ensures m.wrapping_add(t) == add(m, t),
{
    assert(add(m, t) == if m as int + t as int > u64::MAX { (m as int + t as int - 0x1_0000_0000_0000_0000) as u64 }
        else { (m + t) as u64 }) by (bit_vector);
}

proof fn lemma_low_mask(y: u64, len: u64, u: u64)
    requires 1 <= len <= 64, u < 64,
    ensures bt(y & low_mask(len), u) == (bt(y, u) && u < len),
{
    if len >= 64 {
        assert(((y & !0u64) >> u) & 1u64 == (y >> u) & 1u64) by (bit_vector) requires u < 64;
    } else {
        assert(((y & sub(1u64 << len, 1u64)) >> u) & 1u64 == 1u64 <==> ((y >> u) & 1u64 == 1u64 && u < len))
            by (bit_vector) requires len < 64, u < 64;
    }
}

/// The last bit as a 0/1 word.
proof fn lemma_top_bit(x: u64, i: u64)
    requires i < 64,
    ensures (x >> i) & 1u64 <= 1, ((x >> i) & 1u64 == 1) == bt(x, i),
{
    assert((x >> i) & 1u64 <= 1) by (bit_vector);
}

/// Number of set bits of `x` (SWAR; LLVM compiles it to one popcount).
pub open spec fn swar(x: u64) -> u64 {
    let a = sub(x, (x >> 1u64) & 0x5555_5555_5555_5555u64);
    let b = add(a & 0x3333_3333_3333_3333u64, (a >> 2u64) & 0x3333_3333_3333_3333u64);
    let c = add(b, b >> 4u64) & 0x0f0f_0f0f_0f0f_0f0fu64;
    mul(c, 0x0101_0101_0101_0101u64) >> 56u64
}

proof fn lemma_wmul(x: u64, y: u64)
    ensures x.wrapping_mul(y) == mul(x, y),
{
    assert(mul(x, y) == ((x as nat * y as nat) % 0x1_0000_0000_0000_0000nat) as u64) by (bit_vector);
}

pub proof fn lemma_wsub(x: u64, y: u64)
    ensures x.wrapping_sub(y) == sub(x, y),
{
    assert(sub(x, y) == if x >= y { (x - y) as u64 } else { (x as int - y as int + 0x1_0000_0000_0000_0000) as u64 })
        by (bit_vector);
}

/// The SWAR popcount of the low-bit mask `2^z - 1` is `z`.
proof fn lemma_swar_mask(z: u64)
    requires z < 64,
    ensures swar(sub(1u64 << z, 1u64)) == z,
{
    assert(swar(sub(1u64 << z, 1u64)) == z) by (bit_vector) requires z < 64;
}

/// The isolated lowest set bit of `t` is bit `trailing_zeros(t)`, and the bits below it are clear.
proof fn lemma_lowbit_pow(t: u64)
    requires t != 0,
    ensures ({
        let z = u64_trailing_zeros(t) as u64;
        z < 64 && t & add(!t, 1u64) == 1u64 << z && t & sub(1u64 << z, 1u64) == 0
    }),
{
    axiom_u64_trailing_zeros(t);
    let z = u64_trailing_zeros(t) as u64;
    assert(t & add(!t, 1u64) == 1u64 << z && t & sub(1u64 << z, 1u64) == 0) by (bit_vector)
        requires z < 64, (t >> z) & 1u64 == 1u64, t << sub(64u64, z) == 0;
}

/// Number of set bits.
#[inline]
fn pop(x: u64) -> (r: u64)
    ensures r == swar(x),
    no_unwind
{
    let s1 = (x >> 1u64) & 0x5555_5555_5555_5555u64;
    let a = x.wrapping_sub(s1);
    let b = (a & 0x3333_3333_3333_3333u64).wrapping_add((a >> 2u64) & 0x3333_3333_3333_3333u64);
    let c = b.wrapping_add(b >> 4u64) & 0x0f0f_0f0f_0f0f_0f0fu64;
    let d = c.wrapping_mul(0x0101_0101_0101_0101u64);
    proof {
        lemma_wsub(x, s1);
        lemma_wadd(a & 0x3333_3333_3333_3333u64, (a >> 2u64) & 0x3333_3333_3333_3333u64);
        lemma_wadd(b, b >> 4u64);
        lemma_wmul(c, 0x0101_0101_0101_0101u64);
    }
    d >> 56u64
}

/// The index of the highest set bit of `y != 0` (a hint only).
#[inline]
fn high_index(y: u64) -> usize
    no_unwind
{
    let mut z = y | (y >> 1u64);
    z = z | (z >> 2u64);
    z = z | (z >> 4u64);
    z = z | (z >> 8u64);
    z = z | (z >> 16u64);
    z = z | (z >> 32u64);
    (pop(z) as usize).wrapping_sub(1)
}

/// The lowest set bit of `t`: the popcount of the bits below its isolated lowest bit (compiled to one tzcnt), and
/// `t & (t - 1)` clears exactly that bit.
#[inline]
pub fn low_index(t: u64) -> (r: u64)
    requires t != 0,
    ensures
        r < 64,
        bt(t, r),
        forall|u: u64| u < r ==> !#[trigger] bt(t, u),
        t & sub(t, 1u64) == t & !(1u64 << r),
    no_unwind
{
    let lb = t & (!t).wrapping_add(1u64);
    let i = pop(lb.wrapping_sub(1u64));
    proof {
        lemma_wadd(!t, 1u64);
        lemma_wsub(lb, 1u64);
        lemma_lowbit_pow(t);
        let z = u64_trailing_zeros(t) as u64;
        lemma_swar_mask(z);
        assert(i == z);
        assert(t & sub(t, 1u64) == t & !(1u64 << z) && (t >> z) & 1u64 == 1u64) by (bit_vector)
            requires z < 64, t & add(!t, 1u64) == 1u64 << z, t != 0;
        assert forall|u: u64| u < i implies !#[trigger] bt(t, u) by {
            assert((t >> u) & 1u64 != 1u64) by (bit_vector) requires u < z, z < 64, t & sub(1u64 << z, 1u64) == 0;
        }
    }
    i
}

/// The `len` elements of `s` from `a` on (`split_at`, which cannot unwind).
pub fn sub_slice<T>(s: &[T], a: usize, len: usize) -> (w: &[T])
    requires a + len <= s@.len(),
    ensures w@ == s@.subrange(a as int, a + len),
    no_unwind
{
    let (_, r) = s.split_at(a);
    let (w, _) = r.split_at(len);
    proof { assert(w@ =~= s@.subrange(a as int, a + len)); }
    w
}

// ------------------------------------------------------------------------------------------------ row facts

/// No slot holds supplier key `v`.
pub open spec fn no_slot(ks: Seq<i64>, v: int) -> bool {
    forall|t: int| 0 <= t < ks.len() ==> #[trigger] ks[t] != v
}

/// Row `j` counts for no slot key of `ks`.
pub open spec fn nohit(c: Cols, f: int, ks: Seq<i64>, j: int) -> bool {
    forall|t: int| 0 <= t < ks.len() ==> !#[trigger] lhit(c, f, ks[t] as int, j)
}

/// A late row whose previous row is a late row of the same order counts only when that one does (both have the
/// same supplier, else the previous row is a NOT EXISTS witness; then EXISTS and NOT EXISTS agree).
pub proof fn lemma_chain(c: Cols, f: int, ks: Seq<i64>, j: int)
    requires
        1 <= j < c.n_l,
        late(c, j),
        late(c, j - 1),
        lkey(c, j) == lkey(c, j - 1),
        nohit(c, f, ks, j - 1),
    ensures nohit(c, f, ks, j),
{
    assert forall|t: int| 0 <= t < ks.len() implies !#[trigger] lhit(c, f, ks[t] as int, j) by {
        if lhit(c, f, ks[t] as int, j) {
            if lsupp(c, j - 1) != lsupp(c, j) {
                assert(other(c, j - 1, j) && late(c, j - 1));
                assert(ex3(c, j));
            } else {
                let i = choose|i: int| 0 <= i < c.n_l && #[trigger] other(c, i, j);
                assert(other(c, i, j - 1));
                assert(ex2(c, j - 1));
                if ex3(c, j - 1) {
                    let i2 = choose|i2: int| 0 <= i2 < c.n_l && #[trigger] other(c, i2, j - 1) && late(c, i2);
                    assert(other(c, i2, j) && late(c, i2));
                    assert(ex3(c, j));
                }
                assert(lhit(c, f, ks[t] as int, j - 1));
            }
        }
    }
}

/// `off` is the supplier base minus the slot table's first key, clamped to `[-2^33, 2^33]`.
pub open spec fn off_ok(off: int, d: int) -> bool {
    if d >= 0x2_0000_0000 { off == 0x2_0000_0000 } else if d <= -0x2_0000_0000 { off == -0x2_0000_0000 } else { off == d }
}

fn off_of(sb: i64, kmin: i64) -> (r: i64)
    ensures off_ok(r as int, sb - kmin),
    no_unwind
{
    let d = sb as i128 - kmin as i128;
    if d >= 0x2_0000_0000i128 {
        0x2_0000_0000i64
    } else if d <= -0x2_0000_0000i128 {
        -0x2_0000_0000i64
    } else {
        d as i64
    }
}

/// Facts of row `j` of segment `sg`.
proof fn lemma_seg_row(c: Cols, k: int, sg: Seg, a: int, j: int)
    requires
        cols_ok(c, k),
        0 <= a < c.n_l,
        seg_ok(c, a, sg),
        a <= j < sg.gend,
    ensures
        j < c.n_l,
        lkey(c, j) == sg.kb + c.lk_codes@[j],
        lsupp(c, j) == sg.sb + c.ls_codes@[j],
        late(c, j) == (c.lc_codes@[j] - c.lr_codes@[j] < sg.dl),
{
    lemma_in_group(c, k, j, sg.gl as int);
    lemma_dl(sg.dl as int, c.lr_bases@[sg.gl as int] - c.lc_bases@[sg.gl as int], c.lc_codes@[j] - c.lr_codes@[j]);
}

/// Facts of every row of a word `[a, a + len)` of segment `sg`.
proof fn lemma_word_rows(c: Cols, k: int, sg: Seg, a: int, len: int)
    requires
        cols_ok(c, k),
        0 <= a < c.n_l,
        seg_ok(c, a, sg),
        a + len <= sg.gend,
    ensures
        a + len <= c.n_l,
        c.lk_codes@.len() == c.n_l,
        c.ls_codes@.len() == c.n_l,
        c.lc_codes@.len() == c.n_l,
        c.lr_codes@.len() == c.n_l,
        forall|j: int| a <= j < a + len ==> #[trigger] lkey(c, j) == sg.kb + c.lk_codes@[j],
        forall|j: int| a <= j < a + len ==> #[trigger] lsupp(c, j) == sg.sb + c.ls_codes@[j],
        forall|j: int| a <= j < a + len ==> #[trigger] late(c, j) == (c.lc_codes@[j] - c.lr_codes@[j] < sg.dl),
{
    assert forall|j: int| a <= j < a + len implies #[trigger] lkey(c, j) == sg.kb + c.lk_codes@[j] by {
        lemma_seg_row(c, k, sg, a, j);
    }
    assert forall|j: int| a <= j < a + len implies #[trigger] lsupp(c, j) == sg.sb + c.ls_codes@[j] by {
        lemma_seg_row(c, k, sg, a, j);
    }
    assert forall|j: int| a <= j < a + len implies #[trigger] late(c, j) == (c.lc_codes@[j] - c.lr_codes@[j] < sg.dl) by {
        lemma_seg_row(c, k, sg, a, j);
    }
}

// ------------------------------------------------------------------------------------------------ word masks

/// A word's masks: boundary hint bits, late bits, candidate bits.
pub struct Masks {
    pub bm: u64,
    pub lm: u64,
    pub cm: u64,
}

/// The word's late bits are exact, and a row outside the candidates never counts.
pub open spec fn masks_ok(c: Cols, f: int, ks: Seq<i64>, a: int, len: int, w: Masks) -> bool {
    &&& forall|u: u64| u < len ==> #[trigger] bt(w.lm, u) == late(c, a + u)
    &&& forall|u: u64| u < len && !#[trigger] bt(w.cm, u) ==> nohit(c, f, ks, a + u)
    &&& forall|u: u64| len <= u < 64 ==> !#[trigger] bt(w.cm, u)
}

/// The facts the candidate proof (`lemma_word_nohit`) needs about one word's masks: exact late bits, sound boundary
/// bits, the tested first-late rows (`first_late` outside `kill`) without a slot bit have no slot supplier, and the
/// `kill` rows never count.
pub open spec fn word_facts(c: Cols, f: int, ks: Seq<i64>, a: int, len: int, lm: u64, bm: u64, x0: u64, kill: u64,
    cin: u64, lin: u64) -> bool
{
    &&& 0 <= a
    &&& 1 <= len <= 64
    &&& a + len <= c.n_l
    &&& cin <= 1
    &&& lin <= 1
    &&& lin == 1 ==> a > 0 && late(c, a - 1)
    &&& cin == 0 ==> a > 0 && nohit(c, f, ks, a - 1)
    &&& forall|u: u64| u < len ==> #[trigger] bt(lm, u) == late(c, a + u)
    &&& forall|u: u64| u < len && !#[trigger] bt(bm, u) ==> a + u > 0 && lkey(c, a + u) == lkey(c, a + u - 1)
    &&& forall|u: u64| u < len && #[trigger] bt(first_late(lm, bm, lin) & !kill, u) && !bt(x0, u)
        ==> no_slot(ks, lsupp(c, a + u))
    &&& forall|u: u64| u < len && #[trigger] bt(kill, u) ==> nohit(c, f, ks, a + u)
}

proof fn lemma_disjoint2(x0: u64, s0: u64, k: u64, l: u64)
    ensures (x0 & (s0 & !k)) & (l & !s0) == 0,
{
    assert((x0 & (s0 & !k)) & (l & !s0) == 0) by (bit_vector);
}

/// A late row of row `j`'s order with another supplier is a NOT EXISTS witness: `j` never counts.
proof fn lemma_ex3_nohit(c: Cols, f: int, ks: Seq<i64>, j: int, i: int)
    requires 0 <= i < c.n_l, other(c, i, j), late(c, i),
    ensures nohit(c, f, ks, j),
{
    assert(ex3(c, j));
}

/// Rows `a + u` outside the candidates never count (induction over `u`: a late row continuing a late stretch takes
/// the fact from the row before).
proof fn lemma_word_nohit(c: Cols, f: int, ks: Seq<i64>, a: int, len: int, lm: u64, bm: u64, x0: u64, kill: u64,
    cin: u64, lin: u64, u: u64)
    requires
        word_facts(c, f, ks, a, len, lm, bm, x0, kill, cin, lin),
        u < len,
    ensures
        ({
            let s0 = first_late(lm, bm, lin);
            !bt(fill(x0 & (s0 & !kill), lm & !s0, cin), u) ==> nohit(c, f, ks, a + u)
        }),
    decreases u,
{
    let s0 = first_late(lm, bm, lin);
    let s = s0 & !kill;
    let x = x0 & s;
    let m = lm & !s0;
    let cm = fill(x, m, cin);
    if u > 0 {
        lemma_word_nohit(c, f, ks, a, len, lm, bm, x0, kill, cin, lin, (u - 1) as u64);
    }
    lemma_first_late_bit(lm, bm, lin, u);
    lemma_and_bit(x0, s, u);
    lemma_and_bit(s0, kill, u);
    lemma_and_bit(lm, s0, u);
    lemma_disjoint2(x0, s0, kill, lm);
    lemma_fill(x, m, cin, u);
    if !bt(cm, u) {
        let j = a + u;
        if !bt(lm, u) {
            assert(!late(c, j));
        } else if bt(s0, u) {
            if bt(kill, u) {
                assert(nohit(c, f, ks, j));
            } else {
                assert(bt(s, u));
                assert(!bt(x0, u));
                assert(no_slot(ks, lsupp(c, j)));
                assert forall|t: int| 0 <= t < ks.len() implies !#[trigger] lhit(c, f, ks[t] as int, j) by {
                    assert(ks[t] != lsupp(c, j));
                }
            }
        } else {
            assert(bt(m, u));
            assert(!bt(bm, u));
            assert(lkey(c, j) == lkey(c, j - 1));
            if u == 0 {
                assert(lin == 1);
                assert(cin == 0);
            } else {
                assert(bt(lm, (u - 1) as u64));
                assert(late(c, a + (u - 1) as u64));
                assert(!bt(cm, (u - 1) as u64));
                assert(nohit(c, f, ks, a + (u - 1) as u64));
            }
            lemma_chain(c, f, ks, j);
        }
    }
}

/// The kill rows (late rows following a late row of the same order with another supplier, and those rows) never
/// count.
proof fn lemma_kill(c: Cols, f: int, ks: Seq<i64>, a: int, len: int, lm: u64, bm: u64, lin: u64, dm: u64, u: u64)
    requires
        0 <= a,
        1 <= len <= 64,
        a + len <= c.n_l,
        lin <= 1,
        lin == 1 ==> a > 0 && late(c, a - 1),
        forall|v: u64| v < len ==> #[trigger] bt(lm, v) == late(c, a + v),
        forall|v: u64| len <= v < 64 ==> !#[trigger] bt(lm, v),
        forall|v: u64| v < len && !#[trigger] bt(bm, v) ==> a + v > 0 && lkey(c, a + v) == lkey(c, a + v - 1),
        forall|v: u64| v < len && #[trigger] bt(dm, v) ==> v >= 1 && lsupp(c, a + v) != lsupp(c, a + v - 1),
        u < len,
    ensures ({
        let kk = (lm & !first_late(lm, bm, lin)) & dm;
        bt(kk | (kk >> 1u64), u) ==> nohit(c, f, ks, a + u)
    }),
{
    let s0 = first_late(lm, bm, lin);
    let mm = lm & !s0;
    let kk = mm & dm;
    lemma_and_bit(kk, kk >> 1u64, u);
    assert(bt(kk >> 1u64, u) == (u < 63 && bt(kk, (u + 1) as u64))) by {
        assert(((kk >> 1u64) >> u) & 1u64 == 1u64 <==> (u < 63 && (kk >> add(u, 1u64)) & 1u64 == 1u64)) by (bit_vector)
            requires u < 64;
    }
    lemma_and_bit(mm, dm, u);
    lemma_and_bit(lm, s0, u);
    lemma_first_late_bit(lm, bm, lin, u);
    if bt(kk, u) {
        let j = a + u;
        assert(u >= 1);
        assert(bt(lm, (u - 1) as u64));
        assert(late(c, a + (u - 1) as u64));
        assert(other(c, j - 1, j) && late(c, j - 1));
        lemma_ex3_nohit(c, f, ks, j, j - 1);
    } else if u < 63 && bt(kk, (u + 1) as u64) {
        let v = (u + 1) as u64;
        lemma_and_bit(mm, dm, v);
        lemma_and_bit(lm, s0, v);
        lemma_first_late_bit(lm, bm, lin, v);
        assert(bt(lm, v));
        assert(v < len);
        let j = a + u;
        assert(late(c, j + 1));
        assert(lkey(c, j + 1) == lkey(c, j));
        assert(lsupp(c, j + 1) != lsupp(c, j));
        assert(other(c, j + 1, j));
        lemma_ex3_nohit(c, f, ks, j, j + 1);
    }
}

// ------------------------------------------------------------------------------------------------ bit loops

/// Late bits of `len` rows from their code slices: bit `u` is `lc[u] - lr[u] < dl`; bits from `len` on are clear.
#[inline(always)]
fn late_bits(lcw: &[u16], lrw: &[u16], dl: i32, len: usize) -> (m: u64)
    requires
        1 <= len <= 64,
        lcw@.len() == len,
        lrw@.len() == len,
    ensures
        forall|u: u64| u < len ==> #[trigger] bt(m, u) == (lcw@[u as int] - lrw@[u as int] < dl),
        forall|u: u64| len <= u < 64 ==> !#[trigger] bt(m, u),
    no_unwind
{
    let mut m: u64 = 0;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bt(m, u) by { lemma_zero_bit(u); }
    }
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len <= 64,
            lcw@.len() == len,
            lrw@.len() == len,
            forall|u: u64| u < i ==> #[trigger] bt(m, u) == (lcw@[u as int] - lrw@[u as int] < dl),
            forall|u: u64| i <= u < 64 ==> !#[trigger] bt(m, u),
        decreases len - i,
    {
        let d = (((lcw[i] as i32) - (lrw[i] as i32)) < dl) as u64;
        proof { lemma_or_bits(m, d, i as u64); }
        m = m | (d << (i as u64));
        i = i + 1;
    }
    m
}

/// `late_bits` of a full word (a constant trip count, so the compiler vectorizes the loop without a remainder).
#[inline(always)]
fn late_bits64(lcw: &[u16], lrw: &[u16], dl: i32) -> (m: u64)
    requires
        lcw@.len() == 64,
        lrw@.len() == 64,
    ensures
        forall|u: u64| u < 64 ==> #[trigger] bt(m, u) == (lcw@[u as int] - lrw@[u as int] < dl),
    no_unwind
{
    let mut m: u64 = 0;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bt(m, u) by { lemma_zero_bit(u); }
    }
    let mut i: usize = 0;
    while i < 64
        invariant
            i <= 64,
            lcw@.len() == 64,
            lrw@.len() == 64,
            forall|u: u64| u < i ==> #[trigger] bt(m, u) == (lcw@[u as int] - lrw@[u as int] < dl),
            forall|u: u64| i <= u < 64 ==> !#[trigger] bt(m, u),
        decreases 64 - i,
    {
        let d = (((lcw[i] as i32) - (lrw[i] as i32)) < dl) as u64;
        proof { lemma_or_bits(m, d, i as u64); }
        m = m | (d << (i as u64));
        i = i + 1;
    }
    m
}

/// Change bits of `len` values: bit `u >= 1` is `w[u] != w[u - 1]`; bit 0 and the bits from `len` on are clear.
#[inline(always)]
fn change_bits(w: &[u32], len: usize) -> (m: u64)
    requires
        1 <= len <= 64,
        w@.len() == len,
    ensures
        forall|u: u64| u < len ==> #[trigger] bt(m, u) == (u >= 1 && w@[u as int] != w@[u - 1]),
        forall|u: u64| len <= u < 64 ==> !#[trigger] bt(m, u),
    no_unwind
{
    let mut m: u64 = 0;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bt(m, u) by { lemma_zero_bit(u); }
    }
    let mut i: usize = 1;
    while i < len
        invariant
            1 <= i <= len <= 64,
            w@.len() == len,
            forall|u: u64| u < i ==> #[trigger] bt(m, u) == (u >= 1 && w@[u as int] != w@[u - 1]),
            forall|u: u64| i <= u < 64 ==> !#[trigger] bt(m, u),
        decreases len - i,
    {
        let d = (w[i] != w[i - 1]) as u64;
        proof { lemma_or_bits(m, d, i as u64); }
        m = m | (d << (i as u64));
        i = i + 1;
    }
    m
}

/// `change_bits` of a full word (constant trip count).
#[inline(always)]
fn change_bits64(w: &[u32]) -> (m: u64)
    requires
        w@.len() == 64,
    ensures
        forall|u: u64| u < 64 ==> #[trigger] bt(m, u) == (u >= 1 && w@[u as int] != w@[u - 1]),
    no_unwind
{
    let mut m: u64 = 0;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bt(m, u) by { lemma_zero_bit(u); }
    }
    let mut i: usize = 1;
    while i < 64
        invariant
            1 <= i <= 64,
            w@.len() == 64,
            forall|u: u64| u < i ==> #[trigger] bt(m, u) == (u >= 1 && w@[u as int] != w@[u - 1]),
            forall|u: u64| i <= u < 64 ==> !#[trigger] bt(m, u),
        decreases 64 - i,
    {
        let d = (w[i] != w[i - 1]) as u64;
        proof { lemma_or_bits(m, d, i as u64); }
        m = m | (d << (i as u64));
        i = i + 1;
    }
    m
}

// ------------------------------------------------------------------------------------------------ word masks

/// The masks of the word `[a, a + len)` of segment `sg`. `bm` are the word's boundary bits (clear only on a row with
/// the previous row's key), `cin` / `lin` the previous row's candidate / late bit, `off` the clamped difference of the
/// segment's supplier base and the slot table's first key.
fn word_masks(c: &Cols, k: Ghost<int>, sm: &SuppMap, f: Ghost<int>, sg: &Seg, a: usize, len: usize, bm: u64,
    cin: u64, lin: u64, off: i64) -> (w: Masks)
    requires
        cols_ok(*c, k@),
        smap_ok(*sm),
        sm.dense,
        sm.range <= 0x400_0000,
        a < c.n_l,
        seg_ok(*c, a as int, *sg),
        1 <= len <= 64,
        a + len <= sg.gend,
        forall|u: u64| u < len && !#[trigger] bt(bm, u) ==> a + u > 0 && lkey(*c, a + u) == lkey(*c, a + u - 1),
        cin <= 1,
        lin <= 1,
        lin == 1 ==> a > 0 && late(*c, a - 1),
        cin == 0 ==> a > 0 && nohit(*c, f@, sm.skeys@, a - 1),
        off_ok(off as int, sg.sb - sm.kmin),
    ensures
        masks_ok(*c, f@, sm.skeys@, a as int, len as int, w),
        w.bm == bm,
    no_unwind
{
    let ghost ks = sm.skeys@;
    let ghost aa = a as int;
    proof { lemma_word_rows(*c, k@, *sg, aa, len as int); }
    let lcw = sub_slice(c.lc_codes, a, len);
    let lrw = sub_slice(c.lr_codes, a, len);
    let lsw = sub_slice(c.ls_codes, a, len);
    let dl = sg.dl as i32;
    // Late bits and supplier change bits.
    proof {
        assert(-65536 <= sg.dl <= 65536) by {
            let diff = c.lr_bases@[sg.gl as int] - c.lc_bases@[sg.gl as int];
            assert(dl_ok(sg.dl as int, diff));
        }
    }
    let lm: u64;
    let dm: u64;
    if len == 64 {
        lm = late_bits64(lcw, lrw, dl);
        dm = change_bits64(lsw);
    } else {
        lm = late_bits(lcw, lrw, dl, len);
        dm = change_bits(lsw, len);
    }
    proof {
        assert forall|u: u64| u < len implies #[trigger] bt(lm, u) == late(*c, aa + u) by {
            assert(lcw@[u as int] == c.lc_codes@[aa + u] && lrw@[u as int] == c.lr_codes@[aa + u]);
        }
        assert forall|u: u64| u < len && #[trigger] bt(dm, u) implies u >= 1 && lsupp(*c, aa + u) != lsupp(*c, aa + u - 1) by {
            assert(lsw@[u as int] == c.ls_codes@[aa + u] && lsw@[u - 1] == c.ls_codes@[aa + u - 1]);
        }
    }
    proof {
        assert forall|u: u64| len <= u < 64 implies !#[trigger] bt(lm, u) by {}
    }
    // First late rows of a late stretch.
    let s0 = lm & (bm | !((lm << 1u64) | lin));
    proof { assert(s0 == first_late(lm, bm, lin)); }
    // Kill rows: a late row after a late row of the same order with another supplier, and that row (each is the
    // other's NOT EXISTS witness).
    let kk = (lm & !s0) & dm;
    let kill = kk | (kk >> 1u64);
    proof {
        assert forall|u: u64| u < len && #[trigger] bt(kill, u) implies nohit(*c, f@, ks, aa + u) by {
            lemma_kill(*c, f@, ks, aa, len as int, lm, bm, lin, dm, u);
        }
    }
    // The remaining first late rows: their suppliers against the slot bitmap.
    let s = s0 & !kill;
    let mut x0: u64 = 0;
    let mut t: u64 = s;
    let range = sm.range as i64;
    while t != 0
        invariant
            smap_ok(*sm),
            sm.dense,
            sm.range <= 0x400_0000,
            range as int == sm.range,
            ks == sm.skeys@,
            1 <= len <= 64,
            aa == a as int,
            aa + len <= c.ls_codes@.len(),
            lsw@ == c.ls_codes@.subrange(aa, aa + len),
            off_ok(off as int, sg.sb - sm.kmin),
            forall|j: int| aa <= j < aa + len ==> #[trigger] lsupp(*c, j) == sg.sb + c.ls_codes@[j],
            forall|u: u64| u < len && #[trigger] bt(s, u) && !bt(t, u) && !bt(x0, u) ==> no_slot(ks, lsupp(*c, aa + u)),
        decreases t,
    {
        let i = low_index(t);
        proof { lemma_clear_bits(t, i); }
        if (i as usize) < len {
            let v = off + lsw[i as usize] as i64;
            let nb: u64 = if v >= 0 && v < range {
                let vu = v as usize;
                proof {
                    assert(vu / 64 < sm.bits@.len()) by (nonlinear_arith)
                        requires vu < sm.range, sm.bits@.len() * 64 >= sm.range;
                }
                (sm.bits[vu / 64] >> ((vu % 64) as u64)) & 1u64
            } else {
                0
            };
            proof {
                let j = aa + i;
                let key = lsupp(*c, j);
                assert(lsw@[i as int] == c.ls_codes@[j]);
                assert(key == sg.sb + c.ls_codes@[j]);
                if nb == 0 {
                    if v >= 0 && v < range {
                        let vu = v as int;
                        assert(vu == key - sm.kmin);
                        assert(!bit_of(sm.bits@, vu));
                        assert(sm.slots@[vu] == NONE);
                        assert forall|t2: int| 0 <= t2 < ks.len() implies #[trigger] ks[t2] != key by {
                            if ks[t2] == key {
                                assert(sm.slots@[ks[t2] - sm.kmin] == t2);
                            }
                        }
                    } else {
                        assert(key - sm.kmin < 0 || key - sm.kmin >= sm.range);
                        assert forall|t2: int| 0 <= t2 < ks.len() implies #[trigger] ks[t2] != key by {}
                    }
                }
                if v >= 0 && v < range {
                    let w0 = sm.bits@[(v as int) / 64];
                    let b0 = ((v as int) % 64) as u64;
                    assert((w0 >> b0) & 1u64 <= 1) by (bit_vector);
                }
                assert(nb <= 1);
                lemma_or_bits(x0, nb, i);
            }
            x0 = x0 | (nb << i);
        }
        proof { lemma_wsub(t, 1u64); }
        t = t & t.wrapping_sub(1u64);
    }
    // Candidates: the tested rows with a slot supplier and the late stretches they start.
    let x = x0 & s;
    let m = lm & !s0;
    let tt = ((x << 1u64) | cin) & m;
    let cm0 = x | ((m.wrapping_add(tt) ^ m) & m);
    proof {
        lemma_wadd(m, tt);
        assert(cm0 == fill(x, m, cin));
    }
    let lmask: u64 = if len == 64 {
        !0u64
    } else {
        let l = len as u64;
        proof { assert((1u64 << l) >= 1) by (bit_vector) requires l < 64; }
        (1u64 << l) - 1
    };
    let cm = (cm0 & lmask) & !kill;
    proof {
        assert(lmask == low_mask(len as u64));
        assert(s == first_late(lm, bm, lin) & !kill);
        assert forall|u: u64| u < len && #[trigger] bt(first_late(lm, bm, lin) & !kill, u) && !bt(x0, u)
            implies no_slot(ks, lsupp(*c, aa + u)) by {
            lemma_zero_bit(u);
        }
        assert(word_facts(*c, f@, ks, aa, len as int, lm, bm, x0, kill, cin, lin));
        assert forall|u: u64| u < len && !#[trigger] bt(cm, u) implies nohit(*c, f@, ks, aa + u) by {
            lemma_and_bit(cm0 & lmask, kill, u);
            lemma_low_mask(cm0, len as u64, u);
            lemma_word_nohit(*c, f@, ks, aa, len as int, lm, bm, x0, kill, cin, lin, u);
        }
        assert forall|u: u64| len <= u < 64 implies !#[trigger] bt(cm, u) by {
            lemma_and_bit(cm0 & lmask, kill, u);
            lemma_low_mask(cm0, len as u64, u);
        }
    }
    Masks { bm, lm, cm }
}

// ------------------------------------------------------------------------------------------------ one candidate

/// l_suppkey and the late test of row `i`, with the segment's bases when the row lies in it.
fn row_at(c: &Cols, k: Ghost<int>, sg: &Seg, gs: usize, i: usize) -> (r: (i64, bool))
    requires
        cols_ok(*c, k@),
        i < c.n_l,
        gs == sg.gl * c.bs_l,
        sg.gl < c.lk_bases@.len(),
        sg.gend <= sg.gl * c.bs_l + c.bs_l,
        sg.sb == c.ls_bases@[sg.gl as int],
        dl_ok(sg.dl as int, c.lr_bases@[sg.gl as int] - c.lc_bases@[sg.gl as int]),
    ensures
        r.0 == lsupp(*c, i as int),
        r.1 == late(*c, i as int),
    no_unwind
{
    if gs <= i && i < sg.gend {
        proof {
            lemma_in_group(*c, k@, i as int, sg.gl as int);
            lemma_dl(sg.dl as int, c.lr_bases@[sg.gl as int] - c.lc_bases@[sg.gl as int],
                c.lc_codes@[i as int] - c.lr_codes@[i as int]);
        }
        (sg.sb + c.ls_codes[i] as i64, (c.lc_codes[i] as i64) - (c.lr_codes[i] as i64) < sg.dl)
    } else {
        proof {
            lemma_group_of_row(i as int, c.bs_l as int);
            lemma_div_below(i as int, c.bs_l as int, c.lk_bases@.len() as int);
            lemma_in_group(*c, k@, i as int, (i / c.bs_l) as int);
            assert(in_i64(lcmt(*c, i as int)) && in_i64(lrcp(*c, i as int)));
        }
        let g = i / c.bs_l;
        (c.ls_bases[g] + c.ls_codes[i] as i64, c.lc_bases[g] + (c.lc_codes[i] as i64) < c.lr_bases[g] + (c.lr_codes[i] as i64))
    }
}

/// On the run `[st, en)` holding every row of row `j`'s order, EXISTS and NOT EXISTS of `j` are the witnesses
/// `wo` / `wb` of the scan over the run (`n_l` when none).
proof fn lemma_run_ex(c: Cols, j: int, st: int, en: int, s: int, wo: int, wb: int)
    requires
        0 <= st <= j < en <= c.n_l,
        s == lsupp(c, j),
        forall|u: int| 0 <= u < c.n_l && #[trigger] lkey(c, u) == lkey(c, j) ==> st <= u < en,
        forall|u: int| st <= u < en ==> #[trigger] lkey(c, u) == lkey(c, j),
        wo < c.n_l ==> st <= wo < en && lsupp(c, wo) != s,
        wo == c.n_l ==> forall|u: int| st <= u < en ==> #[trigger] lsupp(c, u) == s,
        wb < c.n_l ==> st <= wb < en && lsupp(c, wb) != s && late(c, wb),
        wb == c.n_l ==> forall|u: int| st <= u < en ==> !(#[trigger] lsupp(c, u) != s && late(c, u)),
        wo <= c.n_l,
        wb <= c.n_l,
    ensures
        ex2(c, j) == (wo < c.n_l),
        ex3(c, j) == (wb < c.n_l),
{
    if ex2(c, j) {
        let u = choose|u: int| 0 <= u < c.n_l && #[trigger] other(c, u, j);
        assert(lkey(c, u) == lkey(c, j));
        assert(st <= u < en);
        if wo == c.n_l {
            assert(lsupp(c, u) == s);
        }
    }
    if wo < c.n_l {
        assert(lkey(c, wo) == lkey(c, j));
        assert(other(c, wo, j));
    }
    if ex3(c, j) {
        let u = choose|u: int| 0 <= u < c.n_l && #[trigger] other(c, u, j) && late(c, u);
        assert(lkey(c, u) == lkey(c, j));
        assert(st <= u < en);
        if wb == c.n_l {
            assert(!(lsupp(c, u) != s && late(c, u)));
        }
    }
    if wb < c.n_l {
        assert(lkey(c, wb) == lkey(c, j));
        assert(other(c, wb, j) && late(c, wb));
    }
}

/// Whether row `j` (in run `r` starting at `st`, the lines of stored orders row `r`) counts, exactly: `Some(t)` when
/// it counts for slot `t`, `None` when it counts for none. EXISTS / NOT EXISTS scan the run first (its rows were just
/// read); the order's status is read at row `r` only for a row that passes them.
fn eval_run(c: &Cols, k: Ghost<int>, sm: &SuppMap, f: u64, sg: &Seg, gs: usize, j: usize, r: usize, st: usize)
    -> (res: Option<usize>)
    requires
        runs_ready(*c, k@),
        smap_ok(*sm),
        j < c.n_l,
        seg_ok(*c, j as int, *sg),
        gs == sg.gl * c.bs_l,
        cur_ok(*c, r as int, st as int, j as int),
    ensures
        res matches Some(t) ==> t < sm.ns && lhit(*c, f as int, sm.skeys@[t as int] as int, j as int),
        res is None ==> nohit(*c, f as int, sm.skeys@, j as int),
    no_unwind
{
    let ghost jj = j as int;
    let ghost rr = r as int;
    proof {
        lemma_in_group(*c, k@, jj, sg.gl as int);
    }
    let (s, lt) = row_at(c, k, sg, gs, j);
    if !lt {
        return None;
    }
    // Witness rows of another supplier (`wo`) in the run; a late row of another supplier ends the scan.
    proof { lemma_run_end(*c, rr); }
    let en = st + c.rl[r] as usize;
    let n_l = c.n_l;
    let mut wo: usize = n_l;
    let mut i = st;
    while i < en
        invariant
            runs_ready(*c, k@),
            n_l == c.n_l,
            st <= i <= en <= n_l,
            st <= j < en,
            r < c.n_o,
            late(*c, j as int),
            smap_ok(*sm),
            st == rstart(*c, r as int),
            en == rstart(*c, r + 1),
            s == lsupp(*c, j as int),
            jj == j as int,
            gs == sg.gl * c.bs_l,
            seg_ok(*c, jj, *sg),
            wo <= n_l,
            wo < n_l ==> st <= wo < i && lsupp(*c, wo as int) != s,
            wo == n_l ==> forall|u: int| st <= u < i ==> #[trigger] lsupp(*c, u) == s,
            forall|u: int| st <= u < i ==> !(#[trigger] lsupp(*c, u) != s && late(*c, u)),
        decreases en - i,
    {
        let (si, li) = row_at(c, k, sg, gs, i);
        if si != s {
            if li {
                // A late line of another supplier: NOT EXISTS fails.
                proof {
                    lemma_run_lines(*c, r as int);
                    assert(lkey(*c, jj) == okey(*c, r as int));
                    assert(lkey(*c, i as int) == okey(*c, r as int));
                    assert(other(*c, i as int, jj));
                    lemma_ex3_nohit(*c, f as int, sm.skeys@, jj, i as int);
                }
                return None;
            }
            if wo == n_l {
                wo = i;
            }
        }
        i = i + 1;
    }
    proof {
        lemma_run_lines(*c, rr);
        lemma_rpos_of(*c, rr);
        assert(lkey(*c, jj) == okey(*c, rr));
        lemma_run_ex(*c, jj, st as int, en as int, s as int, wo as int, n_l as int);
    }
    if wo == n_l {
        // No line of another supplier: EXISTS fails.
        return None;
    }
    // The order's status.
    proof {
        lemma_group_of_row(rr, c.bs_o as int);
        lemma_div_below(rr, c.bs_o as int, c.ok_bases@.len() as int);
        assert(0 <= ostat(*c, rr) < k@);
    }
    if c.os_bases[r / c.bs_o] + c.os_codes[r] as u64 != f {
        proof { assert(!ofound(*c, f as int, jj)); }
        return None;
    }
    proof { assert(ofound(*c, f as int, jj)); }
    slot_of(sm, s)
}

// ------------------------------------------------------------------------------------------------ a range of rows

/// Row `j` lies inside run `r` past its first row: it has the previous row's key.
proof fn lemma_in_run(c: Cols, r: int, j: int)
    requires runs_model(c), 0 <= r < c.n_o, rstart(c, r) < j < rstart(c, r) + c.rl@[r],
    ensures j > 0, lkey(c, j) == lkey(c, j - 1),
{
    let st = rstart(c, r);
    lemma_rstart_bounds(c, r);
    assert(lsame(c, r, j - st));
    assert(lsame(c, r, j - 1 - st));
}

/// Run `r + 1` exists when it starts before the last row.
proof fn lemma_next_run(c: Cols, r: int)
    requires runs_model(c), 0 <= r < c.n_o, rstart(c, r + 1) < c.n_l,
    ensures r + 1 < c.n_o, c.rl@[r + 1] >= 1,
{
    if r + 1 == c.n_o {
        lemma_rstart_bounds(c, r + 1);
    }
}

/// The boundary bits of the word `[a, a + len)`: bit `u` set when a run starts at row `a + u`. `(rc, rs)` is the run
/// holding row `a`; the result's `(r, st)` is the run holding row `a + len - 1`.
fn run_bits(c: &Cols, k: Ghost<int>, a: usize, len: usize, rc: usize, rs: usize) -> (res: (u64, usize, usize))
    requires
        runs_ready(*c, k@),
        1 <= len <= 64,
        a + len <= c.n_l,
        cur_ok(*c, rc as int, rs as int, a as int),
    ensures
        forall|u: u64| u < len && !#[trigger] bt(res.0, u) ==> a + u > 0 && lkey(*c, a + u) == lkey(*c, a + u - 1),
        cur_ok(*c, res.1 as int, res.2 as int, a + len - 1),
    no_unwind
{
    let ghost aa = a as int;
    let mut bm: u64 = if rs == a { 1 } else { 0 };
    let mut r = rc;
    let mut st = rs;
    proof { lemma_run_end(*c, rc as int); }
    let mut nx = rs + c.rl[rc] as usize;
    let end = a + len;
    proof {
        assert forall|u: u64| u < 64 implies #[trigger] bt(bm, u) == (u == 0 && rs == a) by {
            let b = bm;
            assert((b >> u) & 1u64 == 1u64 <==> (u == 0 && b == 1)) by (bit_vector) requires b <= 1, u < 64;
        }
        // The rows of run rc from row a on, past its first row, have the previous row's key.
        assert forall|u: u64| u < len && aa + u < nx && !#[trigger] bt(bm, u) implies aa + u > 0 && lkey(*c, aa + u) == lkey(*c, aa + u - 1) by {
            lemma_in_run(*c, rc as int, aa + u);
        }
    }
    while nx < end
        invariant
            runs_ready(*c, k@),
            aa == a as int,
            end == a + len,
            1 <= len <= 64,
            end <= c.n_l,
            r < c.n_o,
            st == rstart(*c, r as int),
            st < end,
            nx == st + c.rl@[r as int],
            aa < nx,
            nx == rstart(*c, r + 1),
            nx <= c.n_l,
            forall|u: u64| u < len && aa + u < nx && !#[trigger] bt(bm, u) ==> aa + u > 0 && lkey(*c, aa + u) == lkey(*c, aa + u - 1),
            forall|u: u64| u < 64 && aa + u >= nx ==> !#[trigger] bt(bm, u),
        decreases c.n_l - nx,
    {
        let b = (nx - a) as u64;
        proof {
            lemma_next_run(*c, r as int);
            lemma_run_end(*c, r + 1);
            lemma_or_bits(bm, 1u64, b);
        }
        bm = bm | (1u64 << b);
        let ghost old_nx = nx as int;
        r = r + 1;
        st = nx;
        nx = st + c.rl[r] as usize;
        proof {
            assert(nx > old_nx);
            assert forall|u: u64| u < len && aa + u < nx && !#[trigger] bt(bm, u) implies aa + u > 0 && lkey(*c, aa + u) == lkey(*c, aa + u - 1) by {
                if aa + u > st {
                    lemma_in_run(*c, r as int, aa + u);
                }
            }
        }
    }
    proof {
        assert forall|u: u64| u < len && !#[trigger] bt(bm, u) implies aa + u > 0 && lkey(*c, aa + u) == lkey(*c, aa + u - 1) by {
            if aa + u < nx {
            } 
        }
        if rs < aa && r == rc {
            // Row a itself lies past the first row of run rc.
        }
    }
    (bm, r, st)
}

/// The counting rows of the stored lineitem rows `[lo, stop)` as an event list: `buf[0 .. used)` names the slot of
/// each counting row (`hits_ok`). The scan stops before a word when fewer than 64 free entries are left, so `stop`
/// is `le` unless the buffer ran short; with at least 64 entries it covers at least one word. `(r0, s0)` is the run
/// holding row `lo`; the result's cursor holds row `stop` (when `stop < le`).
pub fn scan_range(c: &Cols, k: Ghost<int>, sm: &SuppMap, f: u64, lo: usize, le: usize, r0: usize, s0: usize,
    buf0: Vec<u32>, cap: usize) -> (r: (Vec<u32>, usize, usize, usize, usize))
    requires
        runs_ready(*c, k@),
        smap_ok(*sm),
        sm.dense,
        sm.range <= 0x400_0000,
        lo <= le <= c.n_l,
        cap == buf0@.len(),
        lo < le ==> cur_ok(*c, r0 as int, s0 as int, lo as int),
    ensures
        r.0@.len() == cap,
        r.1 <= cap,
        lo <= r.2 <= le,
        cap >= 64 && lo < le ==> lo < r.2,
        hits_ok(*c, f as int, sm.skeys@, r.0@.subrange(0, r.1 as int), lo as int, r.2 as int),
        r.2 < le ==> cur_ok(*c, r.3 as int, r.4 as int, r.2 as int),
    no_unwind
{
    let ghost ks = sm.skeys@;
    let ghost ff = f as int;
    let mut buf = buf0;
    let mut used: usize = 0;
    let mut a = lo;
    let mut sg = seg_of(c, k, a);
    let mut cin: u64 = 1;
    let mut lin: u64 = 0;
    // The run holding row a.
    let mut rc = r0;
    let mut rs = s0;
    proof {
        assert forall|tt: int| 0 <= tt < ks.len() implies #[trigger] occ(buf@.subrange(0, 0), tt) as int
            == cnt(*c, ff, ks[tt] as int, lo as int, lo as int) by {
            lemma_occ_empty(buf@.subrange(0, 0), tt);
        }
    }
    while a < le && cap - used >= 64
        invariant
            runs_ready(*c, k@),
            smap_ok(*sm),
            sm.dense,
            sm.range <= 0x400_0000,
            ks == sm.skeys@,
            ff == f as int,
            lo <= a <= le <= c.n_l,
            cap >= 64 && lo < le ==> (a == lo ==> cap - used >= 64),
            seg_ok(*c, a as int, sg),
            buf@.len() == cap,
            used <= cap,
            hits_ok(*c, ff, ks, buf@.subrange(0, used as int), lo as int, a as int),
            a < le ==> cur_ok(*c, rc as int, rs as int, a as int),
            cin <= 1,
            lin <= 1,
            lin == 1 ==> a > 0 && late(*c, a - 1),
            cin == 0 ==> a > 0 && nohit(*c, ff, ks, a - 1),
        decreases le - a,
    {
        let gend = if sg.gend < le { sg.gend } else { le };
        let len = if gend - a < 64 { gend - a } else { 64 };
        let off = off_of(sg.sb, sm.kmin);
        let (bm, r_last, s_last) = run_bits(c, k, a, len, rc, rs);
        let w = word_masks(c, k, sm, Ghost(ff), &sg, a, len, bm, cin, lin, off);
        proof {
            assert(sg.gl * c.bs_l <= a);
        }
        let gs = sg.gl * c.bs_l;
        let ghost u0 = used as int;
        // The candidates, lowest first; rows between them never count. (cr, cs) walks the runs from row a.
        let mut t = w.cm;
        let mut pos: u64 = 0;
        let mut cr = rc;
        let mut cs = rs;
        while t != 0
            invariant
                runs_ready(*c, k@),
                smap_ok(*sm),
                sm.dense,
                ks == sm.skeys@,
                ff == f as int,
                lo <= a,
                a + len <= gend <= sg.gend,
                gend <= le <= c.n_l,
                1 <= len <= 64,
                seg_ok(*c, a as int, sg),
                gs == sg.gl * c.bs_l,
                masks_ok(*c, ff, ks, a as int, len as int, w),
                pos <= len,
                forall|u: u64| pos <= u < 64 ==> #[trigger] bt(t, u) == bt(w.cm, u),
                forall|u: u64| u < pos ==> !#[trigger] bt(t, u),
                buf@.len() == cap,
                u0 + 64 <= cap,
                u0 <= used <= u0 + pos,
                hits_ok(*c, ff, ks, buf@.subrange(0, used as int), lo as int, a + pos),
                cr < c.n_o,
                cs == rstart(*c, cr as int),
                cs <= a + pos,
            decreases t,
        {
            let i = low_index(t);
            let ghost hv = buf@.subrange(0, used as int);
            proof {
                lemma_clear_bits(t, i);
                if i < pos {
                    assert(!bt(t, i));
                }
                assert(bt(w.cm, i));
                assert(i < len);
                // Rows a + pos .. a + i are no candidates.
                assert forall|tt: int| 0 <= tt < ks.len() implies #[trigger] occ(hv, tt) as int
                    == cnt(*c, ff, ks[tt] as int, lo as int, a + i) by {
                    assert forall|j: int| a + pos <= j < a + i implies !#[trigger] lhit(*c, ff, ks[tt] as int, j) by {
                        let u = (j - a) as u64;
                        assert(!bt(t, u));
                        assert(!bt(w.cm, u));
                        assert(nohit(*c, ff, ks, a + u));
                    }
                    lemma_cnt_none(*c, ff, ks[tt] as int, a + pos, a + i);
                    lemma_cnt_split(*c, ff, ks[tt] as int, lo as int, a + pos, a + i);
                }
            }
            let j = a + i as usize;
            // The run holding j.
            proof { lemma_run_end(*c, cr as int); }
            while cs + (c.rl[cr] as usize) <= j
                invariant
                    runs_ready(*c, k@),
                    j < c.n_l,
                    cr < c.n_o,
                    cs == rstart(*c, cr as int),
                    cs <= j,
                    cs + c.rl@[cr as int] <= c.n_l,
                decreases j - cs,
            {
                proof {
                    lemma_run_end(*c, cr as int);
                    lemma_next_run(*c, cr as int);
                }
                cs = cs + c.rl[cr] as usize;
                cr = cr + 1;
                proof { lemma_run_end(*c, cr as int); }
            }
            proof { lemma_run_end(*c, cr as int); }
            let r = eval_run(c, k, sm, f, &sg, gs, j, cr, cs);
            match r {
                Some(ts) => {
                    proof {
                        assert(ts < ks.len());
                        assert(ks.len() == sm.ns && sm.ns < NONE);
                    }
                    buf[used] = ts as u32;
                    proof {
                        assert(buf@.subrange(0, used + 1) =~= hv.push(ts as u32));
                        assert forall|tt: int| 0 <= tt < ks.len() implies #[trigger] occ(buf@.subrange(0, used + 1), tt) as int
                            == cnt(*c, ff, ks[tt] as int, lo as int, j + 1) by {
                            lemma_occ_push(hv, ts as u32, tt);
                            lemma_cnt_step(*c, ff, ks[tt] as int, lo as int, j as int);
                            if tt != ts {
                                assert(ks[tt] != ks[ts as int]);
                            }
                        }
                        assert forall|ii: int| 0 <= ii < used + 1 implies
                            (#[trigger] buf@.subrange(0, used + 1)[ii] as int) < ks.len() by {
                            if ii < used {
                                assert(buf@.subrange(0, used + 1)[ii] == hv[ii]);
                            }
                        }
                    }
                    used = used + 1;
                },
                None => {
                    proof {
                        assert forall|tt: int| 0 <= tt < ks.len() implies #[trigger] occ(hv, tt) as int
                            == cnt(*c, ff, ks[tt] as int, lo as int, j + 1) by {
                            lemma_cnt_step(*c, ff, ks[tt] as int, lo as int, j as int);
                        }
                    }
                },
            }
            proof { lemma_wsub(t, 1u64); }
            t = t & t.wrapping_sub(1u64);
            pos = i + 1;
        }
        proof {
            let hv = buf@.subrange(0, used as int);
            assert forall|tt: int| 0 <= tt < ks.len() implies #[trigger] occ(hv, tt) as int
                == cnt(*c, ff, ks[tt] as int, lo as int, a + len) by {
                assert forall|j: int| a + pos <= j < a + len implies !#[trigger] lhit(*c, ff, ks[tt] as int, j) by {
                    let u = (j - a) as u64;
                    lemma_zero_bit(u);
                    assert(!bt(w.cm, u));
                    assert(nohit(*c, ff, ks, a + u));
                }
                lemma_cnt_none(*c, ff, ks[tt] as int, a + pos, a + len);
                lemma_cnt_split(*c, ff, ks[tt] as int, lo as int, a + pos, a + len);
            }
            lemma_top_bit(w.cm, (len - 1) as u64);
            lemma_top_bit(w.lm, (len - 1) as u64);
            lemma_in_group(*c, k@, a + len - 1, sg.gl as int);
            lemma_run_end(*c, r_last as int);
        }
        cin = (w.cm >> ((len - 1) as u64)) & 1u64;
        lin = (w.lm >> ((len - 1) as u64)) & 1u64;
        // The run holding the next word's first row.
        let nx = s_last + c.rl[r_last] as usize;
        if nx == a + len {
            if nx < c.n_l {
                proof { lemma_next_run(*c, r_last as int); lemma_rstart_bounds(*c, r_last + 1); }
                rc = r_last + 1;
                rs = nx;
            }
        } else {
            rc = r_last;
            rs = s_last;
        }
        a = a + len;
        if a < c.n_l && a == sg.gend {
            sg = seg_next(c, k, a, sg);
        }
    }
    (buf, used, a, rc, rs)
}

} // verus!
