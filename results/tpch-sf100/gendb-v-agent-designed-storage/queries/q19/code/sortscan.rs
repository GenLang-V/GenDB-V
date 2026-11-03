//! The sorted plan of one task over the part rows `j_lo .. j_hi` (`sort_run`), with the same output as
//! `kernel::scan_range` (`out_ok`): the accumulators over those part rows.
//!
//! 1. Part rows (`scan_parts`): per 64K-row block, three 256-entry tables give for each brand, container and size
//!    code the set of arms (bits 0, 1, 2) whose part side that value satisfies (`tab_ok`); a row's arms are the AND
//!    of its three entries (`lemma_bit3_and`), so most rows cost three table loads. A row with an arm is batched
//!    (`Batch`, up to 64 rows: key, arm, ghost part row).
//! 2. A full batch (`flush`): the key ranges of its rows in the l_partkey key index are guessed from the directory of
//!    storage `li_partdir` and confirmed (`range_check`, else searched), all guesses first so the probes' memory
//!    latencies overlap; then each row's range is recorded (`Coll::rng`, packed `lb | arm << 30 | ub << 32`) and its
//!    stored rows are counted per bucket of `bsz` stored rows (`add_range`). The entries of a range are its stored
//!    rows `s` with the arm, `s * 4 + arm` (`enc32`), in index order; `Coll::e` is the ghost sequence of every entry
//!    so far, and for each accumulator its sum (`ev`) plus the batch's part rows' totals is the total over the part
//!    rows scanned (`tot_inv`).
//! 3. The counts become bucket starts and every range is walked again, each entry written at its bucket's cursor
//!    (`scatter`; `common::bucketsort`): `Coll::ents` then holds the entries sorted by `s / bsz`.
//! 4. The entries are evaluated in that order (`evaluate`): rows close together in storage are read together.
//!    Sums over the sorted entries equal sums over `Coll::e` (`lemma_sorted_sum`), which are the part rows' totals.
//!
//! A task whose buffers are too small, or whose sorted entry decodes badly, reports `ok == false`; the caller then
//! falls back to the kernel scan.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::link::expr::ival;
use crate::link::join::sum_of;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use super::common::fastdiv::{Divisor, divisor_ok};
use super::common::bucketsort::*;
use super::model::*;
use super::terms::*;
use super::decode::*;
use super::sums::*;
use super::kernel::*;

verus! {

// ------------------------------------------------------------------------------------------------ entries

/// The entry of stored row `s` under arm `a`.
pub open spec fn enc32(s: int, a: int) -> u32 {
    (s * 4 + a) as u32
}

/// The stored row of an entry.
pub open spec fn e_row(e: u32) -> int {
    e as int / 4
}

/// The arm of an entry.
pub open spec fn e_arm(e: u32) -> int {
    e as int % 4
}

/// Accumulator `kk`'s term of an entry: its row's contribution under its arm.
pub open spec fn ev(fp: Seq<PartView>, ps: Seq<Literal>, kk: int) -> spec_fn(u32) -> int {
    |e: u32| contrib(kk, row_qual(fp, ps, e_arm(e), e_row(e)), row_val(fp, e_row(e)))
}

/// The bucket of an entry: its row divided by the bucket size.
pub open spec fn bkey(bsz: int) -> spec_fn(u32) -> int {
    |e: u32| e_row(e) / bsz
}

/// `(s << 2) | a` is the entry of `s` and `a`; it decodes back.
proof fn lemma_enc(s: u32, a: u32)
    requires s < 0x4000_0000, a < 4,
    ensures
        (s << 2u32) | a == enc32(s as int, a as int),
        e_row(enc32(s as int, a as int)) == s,
        e_arm(enc32(s as int, a as int)) == a,
{
    assert((s << 2u32) | a == s * 4u32 + a) by (bit_vector)
        requires s < 0x4000_0000u32, a < 4u32;
    assert(s * 4u32 + a == (s as int * 4 + a as int) as u32);
}

/// Decoding an entry with shifts and masks.
proof fn lemma_dec(e: u32)
    ensures (e >> 2u32) as int == e_row(e), (e & 3u32) as int == e_arm(e),
{
    assert(e >> 2u32 == e / 4u32) by (bit_vector);
    assert(e & 3u32 == e % 4u32) by (bit_vector);
}

/// The terms of an entry: count in `[0, 1]`, sum within the mass, mass nonnegative and 0 with the count.
proof fn lemma_ev_bounds(fp: Seq<PartView>, ps: Seq<Literal>)
    ensures
        forall|x: u32| 0 <= #[trigger] ev(fp, ps, 0)(x) <= 1,
        forall|x: u32| #[trigger] ev(fp, ps, 2)(x) >= 0,
        forall|x: u32| -ev(fp, ps, 2)(x) <= #[trigger] ev(fp, ps, 1)(x) <= ev(fp, ps, 2)(x),
        forall|x: u32| #[trigger] ev(fp, ps, 0)(x) == 0 ==> ev(fp, ps, 2)(x) == 0,
{
    assert forall|x: u32| 0 <= #[trigger] ev(fp, ps, 0)(x) <= 1 by {
        lemma_contrib_bounds(row_qual(fp, ps, e_arm(x), e_row(x)), row_val(fp, e_row(x)));
    }
    assert forall|x: u32| #[trigger] ev(fp, ps, 2)(x) >= 0 by {
        lemma_contrib_bounds(row_qual(fp, ps, e_arm(x), e_row(x)), row_val(fp, e_row(x)));
    }
    assert forall|x: u32| -ev(fp, ps, 2)(x) <= #[trigger] ev(fp, ps, 1)(x) <= ev(fp, ps, 2)(x) by {
        lemma_contrib_bounds(row_qual(fp, ps, e_arm(x), e_row(x)), row_val(fp, e_row(x)));
    }
    assert forall|x: u32| #[trigger] ev(fp, ps, 0)(x) == 0 implies ev(fp, ps, 2)(x) == 0 by {
        lemma_contrib_bounds(row_qual(fp, ps, e_arm(x), e_row(x)), row_val(fp, e_row(x)));
    }
}

// ------------------------------------------------------------------------------------------------ packed ranges

/// A recorded range: `lb | a << 30 | ub << 32`.
pub open spec fn pack(lb: u64, ub: u64, a: u64) -> u64 {
    lb | (a << 30u64) | (ub << 32u64)
}

proof fn lemma_pack(lb: u64, ub: u64, a: u64)
    requires lb < 0x4000_0000, ub < 0x4000_0000, a < 4,
    ensures
        pack(lb, ub, a) & 0x3fff_ffffu64 == lb,
        (pack(lb, ub, a) >> 30u64) & 3u64 == a,
        pack(lb, ub, a) >> 32u64 == ub,
{
    assert((lb | (a << 30u64) | (ub << 32u64)) & 0x3fff_ffffu64 == lb) by (bit_vector)
        requires lb < 0x4000_0000u64, ub < 0x4000_0000u64, a < 4u64;
    assert(((lb | (a << 30u64) | (ub << 32u64)) >> 30u64) & 3u64 == a) by (bit_vector)
        requires lb < 0x4000_0000u64, ub < 0x4000_0000u64, a < 4u64;
    assert((lb | (a << 30u64) | (ub << 32u64)) >> 32u64 == ub) by (bit_vector)
        requires lb < 0x4000_0000u64, ub < 0x4000_0000u64, a < 4u64;
}

// ------------------------------------------------------------------------------------------------ arm tables

/// Three flags as bits 0, 1, 2.
pub open spec fn bit3(x0: bool, x1: bool, x2: bool) -> u8 {
    (if x0 { 1u8 } else { 0u8 }) | (if x1 { 2u8 } else { 0u8 }) | (if x2 { 4u8 } else { 0u8 })
}

/// The AND of three flag sets has bit `a` exactly when all three have it.
proof fn lemma_bit3_and(x0: bool, x1: bool, x2: bool, y0: bool, y1: bool, y2: bool, z0: bool, z1: bool, z2: bool)
    ensures ({
        let m = bit3(x0, x1, x2) & bit3(y0, y1, y2) & bit3(z0, z1, z2);
        &&& (m & 1u8 != 0) == (x0 && y0 && z0)
        &&& (m & 2u8 != 0) == (x1 && y1 && z1)
        &&& (m == 0) == !((x0 && y0 && z0) || (x1 && y1 && z1) || (x2 && y2 && z2))
    }),
{
    let x = bit3(x0, x1, x2);
    let y = bit3(y0, y1, y2);
    let z = bit3(z0, z1, z2);
    let m = x & y & z;
    assert((m & 1u8 != 0) == (x0 && y0 && z0) && (m & 2u8 != 0) == (x1 && y1 && z1)
        && (m == 0) == !((x0 && y0 && z0) || (x1 && y1 && z1) || (x2 && y2 && z2))) by (bit_vector)
        requires
            x == (if x0 { 1u8 } else { 0u8 }) | (if x1 { 2u8 } else { 0u8 }) | (if x2 { 4u8 } else { 0u8 }),
            y == (if y0 { 1u8 } else { 0u8 }) | (if y1 { 2u8 } else { 0u8 }) | (if y2 { 4u8 } else { 0u8 }),
            z == (if z0 { 1u8 } else { 0u8 }) | (if z1 { 2u8 } else { 0u8 }) | (if z2 { 4u8 } else { 0u8 }),
            m == x & y & z;
}

/// Container index `ci` is one of arm `k`'s four.
pub open spec fn cin(k: ArmK, ci: int) -> bool {
    ci == k.c0 || ci == k.c1 || ci == k.c2 || ci == k.c3
}

/// The size bound of arm `k`.
pub open spec fn sin(k: ArmK, sz: int) -> bool {
    1 <= sz && sz <= k.smax
}

/// The arm tables of a block with dictionary bases `brb`, `ctb` and size base `szb`: entry `c` of the brand
/// (`0 .. 256`), container (`256 .. 512`) and size (`512 .. 768`) table holds the arms that code `c` satisfies.
pub open spec fn tab_ok(t: Seq<u8>, arms: Arms, brb: u64, ctb: u64, szb: i64) -> bool {
    &&& t.len() == 768
    &&& forall|c: int| 0 <= c < 256 ==> #[trigger] t[c] == bit3(brb + c == arms.a0.b, brb + c == arms.a1.b,
            brb + c == arms.a2.b)
    &&& forall|c: int| 256 <= c < 512 ==> #[trigger] t[c] == bit3(cin(arms.a0, ctb + c - 256),
            cin(arms.a1, ctb + c - 256), cin(arms.a2, ctb + c - 256))
    &&& forall|c: int| 512 <= c < 768 ==> #[trigger] t[c] == bit3(sin(arms.a0, szb + c - 512),
            sin(arms.a1, szb + c - 512), sin(arms.a2, szb + c - 512))
}

/// `base + c == v` without overflow.
#[inline(always)]
fn is_at(base: u64, c: u64, v: u64) -> (r: bool)
    ensures r == (base + c == v),
    no_unwind
{
    base <= v && v - base == c
}

/// The arm tables of one block.
pub fn build_tabs(tabs: &mut Vec<u8>, arms: &Arms, brb: u64, ctb: u64, szb: i64)
    requires old(tabs)@.len() == 768,
    ensures tab_ok(final(tabs)@, *arms, brb, ctb, szb),
    no_unwind
{
    let k0 = arms.a0;
    let k1 = arms.a1;
    let k2 = arms.a2;
    let mut c: usize = 0;
    while c < 256
        invariant
            tabs@.len() == 768,
            c <= 256,
            k0 == arms.a0 && k1 == arms.a1 && k2 == arms.a2,
            forall|x: int| 0 <= x < c ==> #[trigger] tabs@[x] == bit3(brb + x == arms.a0.b, brb + x == arms.a1.b,
                brb + x == arms.a2.b),
            forall|x: int| 256 <= x < 256 + c ==> #[trigger] tabs@[x] == bit3(cin(arms.a0, ctb + x - 256),
                cin(arms.a1, ctb + x - 256), cin(arms.a2, ctb + x - 256)),
            forall|x: int| 512 <= x < 512 + c ==> #[trigger] tabs@[x] == bit3(sin(arms.a0, szb + x - 512),
                sin(arms.a1, szb + x - 512), sin(arms.a2, szb + x - 512)),
        decreases 256 - c,
    {
        let cc = c as u64;
        let b0 = is_at(brb, cc, k0.b);
        let b1 = is_at(brb, cc, k1.b);
        let b2 = is_at(brb, cc, k2.b);
        let tb: u8 = (if b0 { 1u8 } else { 0u8 }) | (if b1 { 2u8 } else { 0u8 }) | (if b2 { 4u8 } else { 0u8 });
        let c0 = is_at(ctb, cc, k0.c0) || is_at(ctb, cc, k0.c1) || is_at(ctb, cc, k0.c2) || is_at(ctb, cc, k0.c3);
        let c1 = is_at(ctb, cc, k1.c0) || is_at(ctb, cc, k1.c1) || is_at(ctb, cc, k1.c2) || is_at(ctb, cc, k1.c3);
        let c2 = is_at(ctb, cc, k2.c0) || is_at(ctb, cc, k2.c1) || is_at(ctb, cc, k2.c2) || is_at(ctb, cc, k2.c3);
        let tc: u8 = (if c0 { 1u8 } else { 0u8 }) | (if c1 { 2u8 } else { 0u8 }) | (if c2 { 4u8 } else { 0u8 });
        let sz: i128 = szb as i128 + c as i128;
        let s0 = 1 <= sz && sz <= k0.smax as i128;
        let s1 = 1 <= sz && sz <= k1.smax as i128;
        let s2 = 1 <= sz && sz <= k2.smax as i128;
        let ts: u8 = (if s0 { 1u8 } else { 0u8 }) | (if s1 { 2u8 } else { 0u8 }) | (if s2 { 4u8 } else { 0u8 });
        put(tabs, c, tb);
        put(tabs, 256 + c, tc);
        put(tabs, 512 + c, ts);
        proof {
            assert(tabs@[c as int] == bit3(brb + c == arms.a0.b, brb + c == arms.a1.b, brb + c == arms.a2.b));
            assert(tabs@[256 + c] == bit3(cin(arms.a0, ctb + (256 + c) - 256), cin(arms.a1, ctb + (256 + c) - 256),
                cin(arms.a2, ctb + (256 + c) - 256)));
            assert(tabs@[512 + c] == bit3(sin(arms.a0, szb + (512 + c) - 512), sin(arms.a1, szb + (512 + c) - 512),
                sin(arms.a2, szb + (512 + c) - 512)));
        }
        c = c + 1;
    }
}

/// Part row `j` (block `g`, codes `bc`, `cc`, `sc`): its arm mask `m` decides its arm.
proof fn lemma_row_arm(cp: Seq<PartView>, ps: Seq<Literal>, arms: Arms, tabs: Seq<u8>, brb: u64, ctb: u64, szb: i64,
    j: int, bc: int, cc: int, sc: int, m: u8)
    requires
        pa_shape(cp),
        arms_ok(arms, ps, cp),
        0 <= j < n_pa(cp),
        tab_ok(tabs, arms, brb, ctb, szb),
        0 <= bc < 256 && 0 <= cc < 256 && 0 <= sc < 256,
        bidx_at(cp, j) == brb + bc,
        cidx_at(cp, j) == ctb + cc,
        size_at(cp, j) == szb + sc,
        m == tabs[bc] & tabs[256 + cc] & tabs[512 + sc],
    ensures ({
        let a = zarm(ps, pa_rows(cp)[j]);
        &&& m == 0 ==> a == 3
        &&& m != 0 && m & 1u8 != 0 ==> a == 0
        &&& m != 0 && m & 1u8 == 0 && m & 2u8 != 0 ==> a == 1
        &&& m != 0 && m & 1u8 == 0 && m & 2u8 == 0 ==> a == 2
    }),
{
    lemma_part_row_vals(cp, ps, j);
    let bi = bidx_at(cp, j);
    let ci = cidx_at(cp, j);
    let sz = size_at(cp, j);
    assert(tabs[bc] == bit3(bi == arms.a0.b, bi == arms.a1.b, bi == arms.a2.b));
    assert(tabs[256 + cc] == bit3(cin(arms.a0, ctb + (256 + cc) - 256), cin(arms.a1, ctb + (256 + cc) - 256),
        cin(arms.a2, ctb + (256 + cc) - 256)));
    assert(tabs[512 + sc] == bit3(sin(arms.a0, szb + (512 + sc) - 512), sin(arms.a1, szb + (512 + sc) - 512),
        sin(arms.a2, szb + (512 + sc) - 512)));
    lemma_bit3_and(bi == arms.a0.b, bi == arms.a1.b, bi == arms.a2.b, cin(arms.a0, ci), cin(arms.a1, ci), cin(arms.a2, ci),
        sin(arms.a0, sz), sin(arms.a1, sz), sin(arms.a2, sz));
    let (bt, ct) = (bdict(cp, bi), cdict(cp, ci));
    assert((bi == arms.a0.b) == (bt == brand_p(ps, 0)));
    assert((bi == arms.a1.b) == (bt == brand_p(ps, 1)));
    assert((bi == arms.a2.b) == (bt == brand_p(ps, 2)));
    assert(cin(arms.a0, ci) == cont_in(0, ct));
    assert(cin(arms.a1, ci) == cont_in(1, ct));
    assert(cin(arms.a2, ci) == cont_in(2, ct));
}

/// The part values of row `j` and its arm.
proof fn lemma_part_row_vals(cp: Seq<PartView>, ps: Seq<Literal>, j: int)
    requires pa_shape(cp), 0 <= j < n_pa(cp),
    ensures
        pa_rows(cp)[j].len() == 4,
        ival(pa_rows(cp)[j][0]) == pkey_at(cp, j),
        zarm(ps, pa_rows(cp)[j]) == arm_of(ps, bdict(cp, bidx_at(cp, j)), size_at(cp, j), cdict(cp, cidx_at(cp, j))),
        0 <= bidx_at(cp, j) < n_bd(cp),
        0 <= cidx_at(cp, j) < n_cd(cp),
{
}

// ------------------------------------------------------------------------------------------------ the batch

/// Up to 64 part rows with an arm, waiting for their key ranges.
pub struct Batch {
    /// Keys.
    pub bk: Vec<i64>,
    /// Arms.
    pub ba: Vec<u8>,
    /// Range guesses, then exact ranges.
    pub blb: Vec<usize>,
    pub bub: Vec<usize>,
    /// Number of rows.
    pub nb: usize,
    /// The part rows (ghost).
    pub zb: Ghost<Seq<Row>>,
}

pub open spec fn batch_ok(b: Batch, ps: Seq<Literal>) -> bool {
    &&& b.bk@.len() == 64 && b.ba@.len() == 64 && b.blb@.len() == 64 && b.bub@.len() == 64
    &&& b.nb <= 64
    &&& b.zb@.len() == b.nb
    &&& forall|i: int| 0 <= i < b.nb ==> {
        &&& (#[trigger] b.zb@[i]).len() == 4
        &&& ival(b.zb@[i][0]) == b.bk@[i]
        &&& zarm(ps, b.zb@[i]) == b.ba@[i]
        &&& b.ba@[i] < 3
    }
}

// ------------------------------------------------------------------------------------------------ the collection

/// The recorded ranges, the bucket counts and, after `scatter`, the sorted entries.
pub struct Coll {
    /// Packed ranges.
    pub rng: Vec<u64>,
    /// Sorted entries (after the scatter).
    pub ents: Vec<u32>,
    /// Bucket counts, then cursors.
    pub offs: Vec<u32>,
    /// Number of ranges and of entries.
    pub nr: usize,
    pub ne: usize,
    /// The entries in range order (ghost), and per range its bounds, arm and first entry.
    pub e: Ghost<Seq<u32>>,
    pub rl: Ghost<Seq<int>>,
    pub ru: Ghost<Seq<int>>,
    pub ra: Ghost<Seq<int>>,
    pub rs: Ghost<Seq<int>>,
}

/// The ranges' entries: range `r` covers key index positions `rl[r] .. ru[r]`, its entries start at `rs[r]`.
pub open spec fn ranges_ok(c: Coll, fp: Seq<PartView>) -> bool {
    let (e, nr) = (c.e@, c.nr as int);
    let (rl, ru, ra, rs) = (c.rl@, c.ru@, c.ra@, c.rs@);
    &&& c.ne == e.len()
    &&& nr <= c.rng@.len()
    &&& rl.len() == nr && ru.len() == nr && ra.len() == nr && rs.len() == nr
    &&& forall|r: int| 0 <= r < nr ==> {
        &&& 0 <= #[trigger] rl[r] <= ru[r] <= n_li(fp)
        &&& 0 <= ra[r] < 3
        &&& 0 <= rs[r] && rs[r] + (ru[r] - rl[r]) <= e.len()
        &&& c.rng@[r] == pack(rl[r] as u64, ru[r] as u64, ra[r] as u64)
    }
    &&& forall|r: int, q: int| 0 <= r < nr && rl[r] <= q < ru[r] ==>
            #[trigger] e[rs[r] + q - rl[r]] == enc32(irow_at(fp, q), ra[r])
    &&& forall|r: int| 0 <= r < nr - 1 ==> #[trigger] rs[r + 1] == rs[r] + (ru[r] - rl[r])
    &&& nr > 0 ==> rs[0] == 0
    &&& nr > 0 ==> rs[nr - 1] + (ru[nr - 1] - rl[nr - 1]) == e.len()
    &&& nr == 0 ==> e.len() == 0
}

/// The entries and the bucket counts.
pub open spec fn coll_ok(c: Coll, fp: Seq<PartView>, bsz: int, nbk: int) -> bool {
    &&& ranges_ok(c, fp)
    &&& c.ents@.len() <= u32::MAX
    &&& c.ne <= c.ents@.len()
    &&& nbk <= c.offs@.len()
    &&& keys_in(c.e@, bkey(bsz), nbk)
    &&& forall|b: int| 0 <= b < nbk ==> #[trigger] c.offs@[b] == cnt(c.e@, bkey(bsz), b)
}

/// The totals over the part rows `j_lo .. j`: the entries' sums plus the batched part rows' totals.
pub open spec fn tot_inv(fp: Seq<PartView>, cp: Seq<PartView>, ps: Seq<Literal>, j_lo: int, j: int, e: Seq<u32>,
    zb: Seq<Row>) -> bool {
    &&& tot(fp, cp, ps, 0, j_lo, j) == sumf(e, ev(fp, ps, 0)) + sum_of(zb, pin(fp, ps, 0))
    &&& tot(fp, cp, ps, 1, j_lo, j) == sumf(e, ev(fp, ps, 1)) + sum_of(zb, pin(fp, ps, 1))
    &&& tot(fp, cp, ps, 2, j_lo, j) == sumf(e, ev(fp, ps, 2)) + sum_of(zb, pin(fp, ps, 2))
}

/// The run of entries of positions `lb .. p` under arm `a`.
pub open spec fn run(fp: Seq<PartView>, lb: int, p: int, a: int) -> Seq<u32> {
    Seq::new((p - lb) as nat, |i: int| enc32(irow_at(fp, lb + i), a))
}

/// The entry of position `p` under the part row's arm has the position's terms for that part row.
proof fn lemma_entry_terms(fp: Seq<PartView>, ps: Seq<Literal>, z: Row, a: int, k: i64, p: int)
    requires
        li_shape(fp), 0 <= p < n_li(fp), n_li(fp) < 0x4000_0000,
        z.len() == 4, ival(z[0]) == k, zarm(ps, z) == a, 0 <= a < 3,
        ikey_at(fp, p) == k,
    ensures ({
        let e = enc32(irow_at(fp, p), a);
        &&& ev(fp, ps, 0)(e) == jt(ps, 0, z)(irows(fp)[p])
        &&& ev(fp, ps, 1)(e) == jt(ps, 1, z)(irows(fp)[p])
        &&& ev(fp, ps, 2)(e) == jt(ps, 2, z)(irows(fp)[p])
        &&& e_row(e) == irow_at(fp, p)
        &&& e_arm(e) == a
    }),
{
    lemma_ikey(fp, p);
    let s = irow_at(fp, p);
    lemma_pos_in(fp, ps, z, a, k, p);
    assert(0 <= s * 4 + a < 0x1_0000_0000);
    assert(enc32(s, a) as int == s * 4 + a);
    assert((s * 4 + a) / 4 == s && (s * 4 + a) % 4 == a) by (nonlinear_arith)
        requires 0 <= s, 0 <= a < 4;
}

/// Adds the range `lb .. ub` (exactly the positions of key `k`) of part row `z` with arm `a`: records it and counts
/// its entries per bucket. False when the buffers are full (the collection unchanged in a usable way is not needed:
/// the task then fails).
pub fn add_range(li: &LiCols, c: &mut Coll, dvb: &Divisor, nbk: usize, lb: usize, ub: usize, a: u8,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(z): Ghost<Row>, Ghost(k): Ghost<i64>)
    -> (ok: bool)
    requires
        li_cols_ok(*li, fp),
        li.n < 0x4000_0000,
        divisor_ok(*dvb, dvb.d as int),
        (li.n as int) / (dvb.d as int) < nbk,
        coll_ok(*old(c), fp, dvb.d as int, nbk as int),
        exact_range(fp, k, lb as int, ub as int),
        z.len() == 4, ival(z[0]) == k, zarm(ps, z) == a, a < 3,
    ensures
        ok ==> coll_ok(*final(c), fp, dvb.d as int, nbk as int),
        ok ==> final(c).e@ == old(c).e@ + run(fp, lb as int, ub as int, a as int),
        ok ==> sumf(final(c).e@, ev(fp, ps, 0)) == sumf(old(c).e@, ev(fp, ps, 0)) + pin(fp, ps, 0)(z),
        ok ==> sumf(final(c).e@, ev(fp, ps, 1)) == sumf(old(c).e@, ev(fp, ps, 1)) + pin(fp, ps, 1)(z),
        ok ==> sumf(final(c).e@, ev(fp, ps, 2)) == sumf(old(c).e@, ev(fp, ps, 2)) + pin(fp, ps, 2)(z),
    no_unwind
{
    let ghost bsz = dvb.d as int;
    let ghost key = bkey(bsz);
    let ghost e0 = c.e@;
    let ghost c0 = *c;
    let nents = c.ents.len();
    if c.nr >= c.rng.len() || ub - lb > nents - c.ne {
        return false;
    }
    let nr = c.nr;
    proof {
        lemma_pack(lb as u64, ub as u64, a as u64);
    }
    put(&mut c.rng, nr, (lb as u64) | ((a as u64) << 30u64) | ((ub as u64) << 32u64));
    proof {
        lemma_sum_empty(irows(fp), jt(ps, 0, z), lb as int);
        lemma_sum_empty(irows(fp), jt(ps, 1, z), lb as int);
        lemma_sum_empty(irows(fp), jt(ps, 2, z), lb as int);
        assert(e0 + run(fp, lb as int, lb as int, a as int) =~= e0);
    }
    let mut p = lb;
    while p < ub
        invariant
            li_cols_ok(*li, fp),
            li.n < 0x4000_0000,
            divisor_ok(*dvb, dvb.d as int),
            bsz == dvb.d as int,
            key == bkey(bsz),
            (li.n as int) / (dvb.d as int) < nbk,
            exact_range(fp, k, lb as int, ub as int),
            lb <= ub,
            z.len() == 4, ival(z[0]) == k, zarm(ps, z) == a, a < 3,
            lb <= p <= ub,
            c.e@ == e0 + run(fp, lb as int, p as int, a as int),
            c.ne == c.e@.len(),
            c.ne + (ub - p) <= nents,
            c.ents@.len() == nents,
            nents <= u32::MAX,
            nbk <= c.offs@.len(),
            keys_in(c.e@, key, nbk as int),
            forall|b: int| 0 <= b < nbk ==> #[trigger] c.offs@[b] == cnt(c.e@, key, b),
            sumf(c.e@, ev(fp, ps, 0)) == sumf(e0, ev(fp, ps, 0)) + kin(fp, ps, 0, z, lb as int, p as int),
            sumf(c.e@, ev(fp, ps, 1)) == sumf(e0, ev(fp, ps, 1)) + kin(fp, ps, 1, z, lb as int, p as int),
            sumf(c.e@, ev(fp, ps, 2)) == sumf(e0, ev(fp, ps, 2)) + kin(fp, ps, 2, z, lb as int, p as int),
        decreases ub - p,
    {
        let s = pos_row(li, p, Ghost(fp));
        let b = dvb.div(s as u64) as usize;
        let ghost e_old = c.e@;
        let ghost x = enc32(s as int, a as int);
        proof {
            lemma_entry_terms(fp, ps, z, a as int, k, p as int);
            lemma_kin_step(fp, ps, z, lb as int, p as int);
            lemma_sumf_push(e_old, ev(fp, ps, 0), x);
            lemma_sumf_push(e_old, ev(fp, ps, 1), x);
            lemma_sumf_push(e_old, ev(fp, ps, 2), x);
            assert(key(x) == b) by {
                assert(e_row(x) == s);
            }
            vstd::arithmetic::div_mod::lemma_div_is_ordered(s as int, li.n as int, bsz);
            assert forall|bb: int| 0 <= bb < nbk implies #[trigger] cnt(e_old.push(x), key, bb)
                == cnt(e_old, key, bb) + (if bb == b { 1int } else { 0int }) by {
                lemma_bsel_push(e_old, key, bb, x);
            }
            assert(cnt(e_old, key, b as int) < nents) by {
                lemma_cnt_le_len(e_old, key, b as int);
            }
        }
        let cb = c.offs[b];
        put(&mut c.offs, b, cb + 1);
        c.e = Ghost(e_old.push(x));
        proof {
            assert(c.e@ =~= e0 + run(fp, lb as int, p + 1, a as int));
            assert forall|i: int| 0 <= i < c.e@.len() implies 0 <= #[trigger] key(c.e@[i]) < nbk by {
                if i < e_old.len() {
                    assert(c.e@[i] == e_old[i]);
                }
            }
        }
        c.ne = c.ne + 1;
        p = p + 1;
    }
    proof {
        lemma_walk_total(fp, ps, z, k, lb as int, ub as int);
        let rl2 = c0.rl@.push(lb as int);
        let ru2 = c0.ru@.push(ub as int);
        let ra2 = c0.ra@.push(a as int);
        let rs2 = c0.rs@.push(e0.len() as int);
        let ee = c.e@;
        assert forall|r: int, q: int| 0 <= r < nr + 1 && rl2[r] <= q < ru2[r] implies
            #[trigger] ee[rs2[r] + q - rl2[r]] == enc32(irow_at(fp, q), ra2[r]) by {
            if r < nr {
                assert(ee[rs2[r] + q - rl2[r]] == e0[rs2[r] + q - rl2[r]]);
            } else {
                assert(ee[rs2[r] + q - rl2[r]] == run(fp, lb as int, ub as int, a as int)[q - lb]);
            }
        }
    }
    c.rl = Ghost(c0.rl@.push(lb as int));
    c.ru = Ghost(c0.ru@.push(ub as int));
    c.ra = Ghost(c0.ra@.push(a as int));
    c.rs = Ghost(c0.rs@.push(e0.len() as int));
    c.nr = nr + 1;
    true
}

/// A bucket count is at most the length.
proof fn lemma_cnt_le_len(s: Seq<u32>, key: spec_fn(u32) -> int, b: int)
    ensures cnt(s, key, b) <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_cnt_le_len(s.drop_last(), key, b);
    }
}


// ------------------------------------------------------------------------------------------------ batches

/// The batched part rows' exact key ranges: directory guesses first, then their checks (a search where one fails).
fn batch_ranges(li: &LiCols, dir: &Dir, b: &mut Batch, Ghost(fp): Ghost<Seq<PartView>>)
    requires
        li_cols_ok(*li, fp),
        li.kind >= 1,
        dir_ok(*dir),
        old(b).bk@.len() == 64 && old(b).ba@.len() == 64 && old(b).blb@.len() == 64 && old(b).bub@.len() == 64,
        old(b).nb <= 64,
    ensures
        final(b).bk == old(b).bk && final(b).ba == old(b).ba && final(b).nb == old(b).nb && final(b).zb == old(b).zb,
        final(b).blb@.len() == 64 && final(b).bub@.len() == 64,
        forall|i: int| 0 <= i < final(b).nb ==>
            exact_range(fp, #[trigger] final(b).bk@[i], final(b).blb@[i] as int, final(b).bub@[i] as int),
    no_unwind
{
    let nb = b.nb;
    let mut i: usize = 0;
    while i < nb
        invariant
            nb == b.nb, nb <= 64, i <= nb,
            b.bk@.len() == 64 && b.blb@.len() == 64 && b.bub@.len() == 64,
            b.bk == old(b).bk && b.ba == old(b).ba && b.nb == old(b).nb && b.zb == old(b).zb,
            dir_ok(*dir),
        decreases nb - i,
    {
        let k = b.bk[i];
        let mut lb: usize = 0;
        let mut ub: usize = 0;
        if dir.mode == 1 && k >= dir.kmin && dir.n >= 2 {
            let e: i128 = k as i128 - dir.kmin as i128;
            if e < (dir.n - 1) as i128 {
                lb = dir.offs[e as usize] as usize;
                ub = dir.offs[e as usize + 1] as usize;
            }
        }
        put(&mut b.blb, i, lb);
        put(&mut b.bub, i, ub);
        i = i + 1;
    }
    let mut i2: usize = 0;
    while i2 < nb
        invariant
            li_cols_ok(*li, fp),
            li.kind >= 1,
            dir_ok(*dir),
            nb == b.nb, nb <= 64, i2 <= nb,
            b.bk@.len() == 64 && b.blb@.len() == 64 && b.bub@.len() == 64,
            b.bk == old(b).bk && b.ba == old(b).ba && b.nb == old(b).nb && b.zb == old(b).zb,
            forall|x: int| 0 <= x < i2 ==> exact_range(fp, #[trigger] b.bk@[x], b.blb@[x] as int, b.bub@[x] as int),
        decreases nb - i2,
    {
        let k = b.bk[i2];
        let lb = b.blb[i2];
        let ub = b.bub[i2];
        if !range_check(li, k, lb, ub, Ghost(fp)) {
            let (lb2, ub2) = find_range(li, dir, k, 0, i64::MIN, i64::MAX, Ghost(fp));
            put(&mut b.blb, i2, lb2);
            put(&mut b.bub, i2, ub2);
        }
        i2 = i2 + 1;
    }
}

/// The batched part rows' ranges added to the collection, in batch order; the batch is then empty. False when the
/// buffers are full.
fn flush(li: &LiCols, dir: &Dir, b: &mut Batch, c: &mut Coll, dvb: &Divisor, nbk: usize,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>) -> (ok: bool)
    requires
        li_cols_ok(*li, fp),
        li.kind >= 1,
        li.n < 0x4000_0000,
        dir_ok(*dir),
        divisor_ok(*dvb, dvb.d as int),
        (li.n as int) / (dvb.d as int) < nbk,
        batch_ok(*old(b), ps),
        coll_ok(*old(c), fp, dvb.d as int, nbk as int),
    ensures
        batch_ok(*final(b), ps),
        final(b).nb == 0,
        ok ==> coll_ok(*final(c), fp, dvb.d as int, nbk as int),
        ok ==> sumf(final(c).e@, ev(fp, ps, 0)) == sumf(old(c).e@, ev(fp, ps, 0)) + sum_of(old(b).zb@, pin(fp, ps, 0)),
        ok ==> sumf(final(c).e@, ev(fp, ps, 1)) == sumf(old(c).e@, ev(fp, ps, 1)) + sum_of(old(b).zb@, pin(fp, ps, 1)),
        ok ==> sumf(final(c).e@, ev(fp, ps, 2)) == sumf(old(c).e@, ev(fp, ps, 2)) + sum_of(old(b).zb@, pin(fp, ps, 2)),
    no_unwind
{
    let ghost zb = b.zb@;
    let ghost e0 = c.e@;
    batch_ranges(li, dir, b, Ghost(fp));
    let nb = b.nb;
    let mut i: usize = 0;
    proof {
        lemma_sum_empty(zb, pin(fp, ps, 0), 0);
        lemma_sum_empty(zb, pin(fp, ps, 1), 0);
        lemma_sum_empty(zb, pin(fp, ps, 2), 0);
    }
    while i < nb
        invariant
            li_cols_ok(*li, fp),
            li.n < 0x4000_0000,
            divisor_ok(*dvb, dvb.d as int),
            (li.n as int) / (dvb.d as int) < nbk,
            nb == b.nb, nb <= 64, i <= nb,
            zb == b.zb@,
            batch_ok(*b, ps),
            forall|x: int| 0 <= x < nb ==> exact_range(fp, #[trigger] b.bk@[x], b.blb@[x] as int, b.bub@[x] as int),
            coll_ok(*c, fp, dvb.d as int, nbk as int),
            sumf(c.e@, ev(fp, ps, 0)) == sumf(e0, ev(fp, ps, 0)) + sum_of(zb.subrange(0, i as int), pin(fp, ps, 0)),
            sumf(c.e@, ev(fp, ps, 1)) == sumf(e0, ev(fp, ps, 1)) + sum_of(zb.subrange(0, i as int), pin(fp, ps, 1)),
            sumf(c.e@, ev(fp, ps, 2)) == sumf(e0, ev(fp, ps, 2)) + sum_of(zb.subrange(0, i as int), pin(fp, ps, 2)),
        decreases nb - i,
    {
        let k = b.bk[i];
        let lb = b.blb[i];
        let ub = b.bub[i];
        let a = b.ba[i];
        proof {
            assert(exact_range(fp, b.bk@[i as int], b.blb@[i as int] as int, b.bub@[i as int] as int));
            assert(zb[i as int].len() == 4);
            lemma_sum_step(zb, pin(fp, ps, 0), 0, i as int);
            lemma_sum_step(zb, pin(fp, ps, 1), 0, i as int);
            lemma_sum_step(zb, pin(fp, ps, 2), 0, i as int);
        }
        if !add_range(li, c, dvb, nbk, lb, ub, a, Ghost(fp), Ghost(ps), Ghost(zb[i as int]), Ghost(k)) {
            b.nb = 0;
            b.zb = Ghost(Seq::empty());
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(zb.subrange(0, nb as int) =~= zb);
    }
    b.nb = 0;
    b.zb = Ghost(Seq::empty());
    true
}

// ------------------------------------------------------------------------------------------------ the part rows

/// Adding part row `z` to the batched rows adds its totals.
proof fn lemma_sum_push(zb: Seq<Row>, f: spec_fn(Row) -> int, z: Row)
    ensures sum_of(zb.push(z), f) == sum_of(zb, f) + f(z),
{
    assert(zb.push(z).drop_last() =~= zb);
}

/// The inputs of a task's scan over the part rows `j_lo .. j_hi`.
pub open spec fn sort_pre(li: LiCols, pa: PaCols, lk: LiK, arms: Arms, dir: Dir, dvb: Divisor, nbk: int,
    fp: Seq<PartView>, cp: Seq<PartView>, ps: Seq<Literal>) -> bool {
    &&& scan_pre(li, pa, lk, arms, fp, cp, ps)
    &&& dir_ok(dir)
    &&& li.kind >= 1
    &&& li.n < 0x4000_0000
    &&& divisor_ok(dvb, dvb.d as int)
    &&& (li.n as int) / (dvb.d as int) < nbk
}

/// The scan of the part rows `j_lo .. j_hi`: every row with an arm is batched, full batches are flushed; at the end
/// the collection holds the entries of every such row (`tot_inv` with an empty batch). False when the buffers are
/// full.
fn scan_parts(li: &LiCols, pa: &PaCols, lk: &LiK, arms: &Arms, dir: &Dir, dvb: &Divisor, nbk: usize,
    tabs: &mut Vec<u8>, b: &mut Batch, c: &mut Coll, j_lo: usize, j_hi: usize,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>) -> (ok: bool)
    requires
        sort_pre(*li, *pa, *lk, *arms, *dir, *dvb, nbk as int, fp, cp, ps),
        j_lo <= j_hi <= pa.n,
        old(tabs)@.len() == 768,
        batch_ok(*old(b), ps),
        old(b).nb == 0,
        coll_ok(*old(c), fp, dvb.d as int, nbk as int),
        old(c).e@.len() == 0,
    ensures
        ok ==> coll_ok(*final(c), fp, dvb.d as int, nbk as int),
        ok ==> tot_inv(fp, cp, ps, j_lo as int, j_hi as int, final(c).e@, Seq::empty()),
    no_unwind
{
    let ghost zs = pa_rows(cp);
    let br = pa.br;
    let ct = pa.ct;
    let szc = pa.sz;
    let mut j = j_lo;
    proof {
        lemma_sum_empty(zs, pin(fp, ps, 0), j_lo as int);
        lemma_sum_empty(zs, pin(fp, ps, 1), j_lo as int);
        lemma_sum_empty(zs, pin(fp, ps, 2), j_lo as int);
        assert(sumf(c.e@, ev(fp, ps, 0)) == 0 && sumf(c.e@, ev(fp, ps, 1)) == 0 && sumf(c.e@, ev(fp, ps, 2)) == 0);
    }
    while j < j_hi
        invariant
            sort_pre(*li, *pa, *lk, *arms, *dir, *dvb, nbk as int, fp, cp, ps),
            zs == pa_rows(cp),
            br == pa.br && ct == pa.ct && szc == pa.sz,
            j_lo <= j <= j_hi <= pa.n,
            tabs@.len() == 768,
            batch_ok(*b, ps),
            coll_ok(*c, fp, dvb.d as int, nbk as int),
            tot_inv(fp, cp, ps, j_lo as int, j as int, c.e@, b.zb@),
        decreases j_hi - j,
    {
        let g = (j as u64 / pa.bs) as usize;
        proof {
            lemma_pa_decode(cp, j as int);
            cpc_lemma_block_end(j as int, pa.bs as int, n_pa(cp));
        }
        let g_end0 = (g as u64 + 1) * pa.bs;
        let g_end: usize = if g_end0 < j_hi as u64 { g_end0 as usize } else { j_hi };
        let pkb = pa.pkb[g];
        let brb = pa.brb[g];
        let ctb = pa.ctb[g];
        let szb = pa.szb[g];
        build_tabs(tabs, arms, brb, ctb, szb);
        while j < g_end
            invariant
                sort_pre(*li, *pa, *lk, *arms, *dir, *dvb, nbk as int, fp, cp, ps),
                zs == pa_rows(cp),
                br == pa.br && ct == pa.ct && szc == pa.sz,
                j_lo <= j <= g_end <= j_hi <= pa.n,
                (g as int) * (pa.bs as int) <= j,
                g_end <= (g as int + 1) * (pa.bs as int),
                g < pa.pkb@.len() && g < pa.brb@.len() && g < pa.szb@.len() && g < pa.ctb@.len(),
                pkb == pa.pkb@[g as int] && brb == pa.brb@[g as int] && szb == pa.szb@[g as int] && ctb == pa.ctb@[g as int],
                tab_ok(tabs@, *arms, brb, ctb, szb),
                batch_ok(*b, ps),
                coll_ok(*c, fp, dvb.d as int, nbk as int),
                tot_inv(fp, cp, ps, j_lo as int, j as int, c.e@, b.zb@),
            decreases g_end - j,
        {
            proof {
                lemma_block(j as int, g as int, pa.bs as int);
                lemma_pa_decode(cp, j as int);
                lemma_sum_step(zs, pin(fp, ps, 0), j_lo as int, j as int);
                lemma_sum_step(zs, pin(fp, ps, 1), j_lo as int, j as int);
                lemma_sum_step(zs, pin(fp, ps, 2), j_lo as int, j as int);
            }
            let ghost z = zs[j as int];
            let bc = br[j] as usize;
            let cc = ct[j] as usize;
            let sc = szc[j] as usize;
            let m = tabs[bc] & tabs[256 + cc] & tabs[512 + sc];
            proof {
                lemma_row_arm(cp, ps, *arms, tabs@, brb, ctb, szb, j as int, bc as int, cc as int, sc as int, m);
                lemma_part_row_vals(cp, ps, j as int);
            }
            if m != 0 {
                let a: u8 = if m & 1u8 != 0 { 0 } else if m & 2u8 != 0 { 1 } else { 2 };
                let k = pkb + pa.pk[j] as i64;
                if b.nb == 64 {
                    let ghost e1 = c.e@;
                    let ghost zb1 = b.zb@;
                    if !flush(li, dir, b, c, dvb, nbk, Ghost(fp), Ghost(ps)) {
                        return false;
                    }
                    proof {
                        lemma_sum_empty(Seq::<Row>::empty(), pin(fp, ps, 0), 0);
                        lemma_sum_empty(Seq::<Row>::empty(), pin(fp, ps, 1), 0);
                        lemma_sum_empty(Seq::<Row>::empty(), pin(fp, ps, 2), 0);
                        assert(Seq::<Row>::empty().subrange(0, 0) =~= Seq::<Row>::empty());
                        assert(b.zb@ =~= Seq::<Row>::empty());
                    }
                }
                let nb = b.nb;
                put(&mut b.bk, nb, k);
                put(&mut b.ba, nb, a);
                let ghost zb0 = b.zb@;
                b.zb = Ghost(zb0.push(z));
                b.nb = nb + 1;
                proof {
                    lemma_sum_push(zb0, pin(fp, ps, 0), z);
                    lemma_sum_push(zb0, pin(fp, ps, 1), z);
                    lemma_sum_push(zb0, pin(fp, ps, 2), z);
                    assert forall|i: int| 0 <= i < b.nb implies {
                        &&& (#[trigger] b.zb@[i]).len() == 4
                        &&& ival(b.zb@[i][0]) == b.bk@[i]
                        &&& zarm(ps, b.zb@[i]) == b.ba@[i]
                        &&& b.ba@[i] < 3
                    } by {
                        if i < nb {
                            assert(b.zb@[i] == zb0[i]);
                        }
                    }
                }
            } else {
                proof {
                    lemma_pin_none(fp, ps, 0, z);
                    lemma_pin_none(fp, ps, 1, z);
                    lemma_pin_none(fp, ps, 2, z);
                }
            }
            j = j + 1;
        }
    }
    if b.nb > 0 {
        if !flush(li, dir, b, c, dvb, nbk, Ghost(fp), Ghost(ps)) {
            return false;
        }
    }
    proof {
        assert(b.zb@ =~= Seq::<Row>::empty());
        lemma_sum_empty(Seq::<Row>::empty(), pin(fp, ps, 0), 0);
        lemma_sum_empty(Seq::<Row>::empty(), pin(fp, ps, 1), 0);
        lemma_sum_empty(Seq::<Row>::empty(), pin(fp, ps, 2), 0);
        assert(Seq::<Row>::empty().subrange(0, 0) =~= Seq::<Row>::empty());
    }
    true
}


// ------------------------------------------------------------------------------------------------ the scatter

/// The first entry of range `r`, or the number of entries after the last range.
pub open spec fn rstart(c: Coll, r: int) -> int {
    if r < c.nr { c.rs@[r] } else { c.e@.len() as int }
}

/// The entries sorted by bucket into `ents`: the counts become bucket starts, then every range is walked again and
/// each entry written at its bucket's cursor.
fn scatter(li: &LiCols, c: &mut Coll, dvb: &Divisor, nbk: usize, Ghost(fp): Ghost<Seq<PartView>>)
    requires
        li_cols_ok(*li, fp),
        li.n < 0x4000_0000,
        divisor_ok(*dvb, dvb.d as int),
        coll_ok(*old(c), fp, dvb.d as int, nbk as int),
    ensures
        final(c).e == old(c).e,
        final(c).ne == old(c).ne,
        final(c).ents@.len() == old(c).ents@.len(),
        sorted_by(final(c).ents@, final(c).e@, bkey(dvb.d as int), nbk as int),
    no_unwind
{
    let ghost key = bkey(dvb.d as int);
    let ghost e = c.e@;
    let ghost c0 = *c;
    counts_to_starts(&mut c.offs, nbk, Ghost(e), Ghost(key));
    proof {
        lemma_partition(e, key, nbk as int, |x: u32| 0int);
        lemma_scatter_init(c.ents@, c.offs@, e, key, nbk as int);
        assert(e.take(rstart(c0, 0)) =~= Seq::<u32>::empty());
    }
    let nr = c.nr;
    let mut r: usize = 0;
    while r < nr
        invariant
            li_cols_ok(*li, fp),
            li.n < 0x4000_0000,
            divisor_ok(*dvb, dvb.d as int),
            key == bkey(dvb.d as int),
            nr == c.nr,
            r <= nr,
            c.e == c0.e && c.nr == c0.nr && c.ne == c0.ne && c.rng == c0.rng,
            c.rl == c0.rl && c.ru == c0.ru && c.ra == c0.ra && c.rs == c0.rs,
            c.ents@.len() == c0.ents@.len(),
            ranges_ok(c0, fp),
            keys_in(e, key, nbk as int),
            start(e, key, nbk as int) == e.len(),
            e == c.e@,
            0 <= rstart(c0, r as int) <= e.len(),
            scatter_inv(c.ents@, c.offs@, e.take(rstart(c0, r as int)), e, key, nbk as int),
        decreases nr - r,
    {
        let w = c.rng[r];
        let ghost (rl, ru, ra) = (c0.rl@[r as int], c0.ru@[r as int], c0.ra@[r as int]);
        proof {
            lemma_pack(rl as u64, ru as u64, ra as u64);
        }
        let lb = (w & 0x3fff_ffffu64) as usize;
        let a = ((w >> 30u64) & 3u64) as u32;
        let ub = (w >> 32u64) as usize;
        let ghost i0 = c0.rs@[r as int];
        let mut p = lb;
        while p < ub
            invariant
                li_cols_ok(*li, fp),
                li.n < 0x4000_0000,
                divisor_ok(*dvb, dvb.d as int),
                key == bkey(dvb.d as int),
                nr == c.nr,
                r < nr,
                c.e == c0.e && c.nr == c0.nr && c.ne == c0.ne && c.rng == c0.rng,
                c.rl == c0.rl && c.ru == c0.ru && c.ra == c0.ra && c.rs == c0.rs,
                c.ents@.len() == c0.ents@.len(),
                ranges_ok(c0, fp),
                keys_in(e, key, nbk as int),
                start(e, key, nbk as int) == e.len(),
                e == c.e@,
                lb == rl && ub == ru && a == ra,
                rl == c0.rl@[r as int] && ru == c0.ru@[r as int] && ra == c0.ra@[r as int],
                i0 == c0.rs@[r as int],
                0 <= rl <= ru <= n_li(fp),
                0 <= ra < 3,
                i0 + (ru - rl) <= e.len(),
                lb <= p <= ub,
                scatter_inv(c.ents@, c.offs@, e.take(i0 + p - lb), e, key, nbk as int),
            decreases ub - p,
        {
            let s = pos_row(li, p, Ghost(fp));
            let bkt = dvb.div(s as u64) as usize;
            let x = ((s as u32) << 2u32) | a;
            let ghost i = i0 + p - lb;
            proof {
                lemma_enc(s as u32, a);
                assert(e[i0 + p - rl] == enc32(irow_at(fp, p as int), ra));
                assert(e.take(i).len() == i);
                assert(key(e[i]) == bkt) by {
                    assert(e_row(e[i]) == s);
                }
                lemma_scatter_step(c.ents@, c.offs@, e.take(i), e, key, nbk as int, bkt as int);
                assert(e.take(i).push(e[i]) =~= e.take(i + 1));
            }
            let pos = c.offs[bkt];
            put(&mut c.ents, pos as usize, x);
            put(&mut c.offs, bkt, pos + 1);
            p = p + 1;
        }
        proof {
            lemma_rs_next(c0, fp, r as int);
        }
        r = r + 1;
    }
    proof {
        assert(e.take(e.len() as int) =~= e);
        lemma_scatter_done(c.ents@, c.offs@, e, key, nbk as int);
    }
}

/// Range `r` ends where the next one starts.
proof fn lemma_rs_next(c: Coll, fp: Seq<PartView>, r: int)
    requires ranges_ok(c, fp), 0 <= r < c.nr,
    ensures rstart(c, r + 1) == c.rs@[r] + (c.ru@[r] - c.rl@[r]),
{
}


// ------------------------------------------------------------------------------------------------ evaluation

/// The arms' quantity windows (coefficients of scale 2), by arm.
#[derive(Clone, Copy)]
pub struct Win {
    pub lo: [i64; 3],
    pub hi: [i64; 3],
}

pub open spec fn win_ok(w: Win, ps: Seq<Literal>) -> bool {
    forall|a: int| 0 <= a < 3 ==> #[trigger] w.lo@[a] == 100 * qty_p(ps, a) && w.hi@[a] == 100 * (qty_p(ps, a) + 10)
}

/// The accumulators over the entries `ents[0 .. ne]`, in that order: `(true, None)` when the mass exceeds
/// `i128::MAX`, `(false, _)` when an entry does not decode to a stored row and an arm.
fn evaluate(li: &LiCols, lk: &LiK, w: &Win, ents: &Vec<u32>, ne: usize,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: (bool, Option<Acc>))
    requires
        li_cols_ok(*li, fp),
        li_k_ok(*lk, fp),
        win_ok(*w, ps),
        ne <= ents@.len(),
    ensures
        r.0 ==> (r.1 matches Some(acc) ==> {
            &&& acc.sum == sumf(ents@.take(ne as int), ev(fp, ps, 1))
            &&& acc.mass == sumf(ents@.take(ne as int), ev(fp, ps, 2))
            &&& acc.any == (sumf(ents@.take(ne as int), ev(fp, ps, 0)) > 0)
            &&& acc_small(acc)
        }),
        r.0 ==> (r.1 is None ==> sumf(ents@.take(ne as int), ev(fp, ps, 2)) > mmax()),
    no_unwind
{
    let ghost es = ents@;
    let mut sum: i128 = 0;
    let mut mass: i128 = 0;
    let mut any = false;
    let mut x: usize = 0;
    proof {
        lemma_ev_bounds(fp, ps);
        assert(es.take(0) =~= Seq::<u32>::empty());
    }
    while x < ne
        invariant
            li_cols_ok(*li, fp),
            li_k_ok(*lk, fp),
            win_ok(*w, ps),
            es == ents@,
            ne <= es.len(),
            x <= ne,
            sum == sumf(es.take(x as int), ev(fp, ps, 1)),
            mass == sumf(es.take(x as int), ev(fp, ps, 2)),
            any == (sumf(es.take(x as int), ev(fp, ps, 0)) > 0),
            sumf(es.take(x as int), ev(fp, ps, 0)) >= 0,
            0 <= mass <= mmax(),
            -mass <= sum <= mass,
            forall|y: u32| 0 <= #[trigger] ev(fp, ps, 0)(y) <= 1,
            forall|y: u32| #[trigger] ev(fp, ps, 2)(y) >= 0,
        decreases ne - x,
    {
        let e = ents[x];
        let s = (e >> 2u32) as usize;
        let a = (e & 3u32) as usize;
        proof {
            lemma_dec(e);
            lemma_sumf_take(es, ev(fp, ps, 0), x as int);
            lemma_sumf_take(es, ev(fp, ps, 1), x as int);
            lemma_sumf_take(es, ev(fp, ps, 2), x as int);
        }
        if a >= 3 || s >= li.n {
            return (false, None);
        }
        let qlo = w.lo[a];
        let qhi = w.hi[a];
        proof {
            assert(w.lo@[a as int] == 100 * qty_p(ps, a as int));
        }
        match row_add(li, lk, s, qlo, qhi, sum, mass, Ghost(fp), Ghost(ps), Ghost(a as int)) {
            None => {
                proof {
                    let et = es.take(ne as int);
                    assert(et.take(x + 1) =~= es.take(x + 1));
                    lemma_sumf_prefix_le(et, ev(fp, ps, 2), x + 1);
                }
                return (true, None);
            },
            Some((s2, m2, hit)) => {
                sum = s2;
                mass = m2;
                any = any || hit;
            },
        }
        x = x + 1;
    }
    (true, Some(Acc { sum, mass, any }))
}

// ------------------------------------------------------------------------------------------------ the task

/// One worker's share: the part rows `j_lo .. j_hi`, with its buffers.
pub struct SortTask {
    pub li: LiCols,
    pub pa: PaCols,
    pub lk: LiK,
    pub arms: Arms,
    pub win: Win,
    pub dir: Dir,
    /// Division by the bucket size (stored rows per bucket) and the number of buckets.
    pub dvb: Divisor,
    pub nbk: usize,
    pub j_lo: usize,
    pub j_hi: usize,
    pub tabs: Vec<u8>,
    pub b: Batch,
    pub c: Coll,
    pub fp: Ghost<Seq<PartView>>,
    pub cp: Ghost<Seq<PartView>>,
    pub ps: Ghost<Seq<Literal>>,
}

pub open spec fn task_pre(t: SortTask) -> bool {
    &&& sort_pre(t.li, t.pa, t.lk, t.arms, t.dir, t.dvb, t.nbk as int, t.fp@, t.cp@, t.ps@)
    &&& win_ok(t.win, t.ps@)
    &&& t.j_lo <= t.j_hi <= t.pa.n
    &&& t.tabs@.len() == 768
    &&& batch_ok(t.b, t.ps@)
    &&& t.b.nb == 0
    &&& coll_ok(t.c, t.fp@, t.dvb.d as int, t.nbk as int)
    &&& t.c.e@.len() == 0
}

/// The task: scan, scatter, evaluate.
pub fn sort_run(t: SortTask) -> (out: (bool, Option<Acc>))
    requires task_pre(t),
    ensures out.0 ==> out_ok(t.fp@, t.cp@, t.ps@, t.j_lo as int, t.j_hi as int, out.1),
    no_unwind
{
    let ghost (fp, cp, ps) = (t.fp@, t.cp@, t.ps@);
    let ghost t0 = t;
    let mut t = t;
    let ok = scan_parts(&t.li, &t.pa, &t.lk, &t.arms, &t.dir, &t.dvb, t.nbk, &mut t.tabs, &mut t.b, &mut t.c,
        t.j_lo, t.j_hi, Ghost(fp), Ghost(cp), Ghost(ps));
    if !ok {
        return (false, None);
    }
    let ghost e = t.c.e@;
    scatter(&t.li, &mut t.c, &t.dvb, t.nbk, Ghost(fp));
    proof {
        let key = bkey(t.dvb.d as int);
        lemma_sorted_sum(t.c.ents@, e, key, t.nbk as int, ev(fp, ps, 0));
        lemma_sorted_sum(t.c.ents@, e, key, t.nbk as int, ev(fp, ps, 1));
        lemma_sorted_sum(t.c.ents@, e, key, t.nbk as int, ev(fp, ps, 2));
        assert(sum_of(Seq::<Row>::empty(), pin(fp, ps, 0)) == 0);
        assert(sum_of(Seq::<Row>::empty(), pin(fp, ps, 1)) == 0);
        assert(sum_of(Seq::<Row>::empty(), pin(fp, ps, 2)) == 0);
    }
    let r = evaluate(&t.li, &t.lk, &t.win, &t.c.ents, t.c.ne, Ghost(fp), Ghost(ps));
    r
}

impl WorkerTask for SortTask {
    type Output = (bool, Option<Acc>);

    open spec fn pre(&self) -> bool {
        task_pre(*self)
    }

    open spec fn post(&self, out: (bool, Option<Acc>)) -> bool {
        out.0 ==> out_ok(self.fp@, self.cp@, self.ps@, self.j_lo as int, self.j_hi as int, out.1)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.j_lo as u64, self.j_hi as u64)
    }

    fn run(self) -> (out: (bool, Option<Acc>)) {
        sort_run(self)
    }
}


// ------------------------------------------------------------------------------------------------ the plan

/// A task over the part rows `j_lo .. j_hi` with fresh buffers (`cap_e` entries, `cap_r` ranges).
fn new_task(li: &LiCols, pa: &PaCols, lk: &LiK, arms: &Arms, win: &Win, dir: &Dir, dvb: &Divisor, nbk: usize,
    j_lo: usize, j_hi: usize, cap_e: usize, cap_r: usize,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>) -> (t: SortTask)
    requires
        sort_pre(*li, *pa, *lk, *arms, *dir, *dvb, nbk as int, fp, cp, ps),
        win_ok(*win, ps),
        j_lo <= j_hi <= pa.n,
        cap_e <= u32::MAX,
        nbk < usize::MAX,
    ensures
        task_pre(t),
        t.j_lo == j_lo && t.j_hi == j_hi,
        t.fp@ == fp && t.cp@ == cp && t.ps@ == ps,
        t.pa == *pa,
{
    let offs = crate::gendb_entry::work::filled(nbk + 1, 0u32);
    let b = Batch { bk: vec![0i64; 64], ba: vec![0u8; 64], blb: vec![0usize; 64], bub: vec![0usize; 64], nb: 0,
        zb: Ghost(Seq::empty()) };
    let c = Coll { rng: vec![0u64; cap_r], ents: vec![0u32; cap_e], offs, nr: 0, ne: 0, e: Ghost(Seq::empty()),
        rl: Ghost(Seq::empty()), ru: Ghost(Seq::empty()), ra: Ghost(Seq::empty()), rs: Ghost(Seq::empty()) };
    let t = SortTask { li: *li, pa: *pa, lk: *lk, arms: *arms, win: *win, dir: *dir, dvb: *dvb, nbk, j_lo, j_hi,
        tabs: vec![0u8; 768], b, c, fp: Ghost(fp), cp: Ghost(cp), ps: Ghost(ps) };
    proof {
        assert forall|bb: int| 0 <= bb < nbk implies #[trigger] t.c.offs@[bb] == cnt(t.c.e@, bkey(dvb.d as int), bb) by {
            assert(t.c.offs@[bb] == 0);
        }
    }
    t
}

/// The tasks `t` of a partition `bnds` of the part rows.
pub open spec fn stasks_ok(tasks: Seq<SortTask>, bnds: Seq<int>, fp: Seq<PartView>, cp: Seq<PartView>,
    ps: Seq<Literal>) -> bool {
    &&& bnds.len() == tasks.len() + 1
    &&& bnds[0] == 0
    &&& forall|t: int| 0 <= t < tasks.len() ==> {
        &&& (#[trigger] tasks[t]).j_lo == bnds[t]
        &&& tasks[t].j_hi == bnds[t + 1]
        &&& tasks[t].fp@ == fp && tasks[t].cp@ == cp && tasks[t].ps@ == ps
        &&& tasks[t].pre()
    }
}

/// Adds the task outputs in range order; `None` when a task failed (the caller falls back).
fn merge_sorted(outs: &Vec<(bool, Option<Acc>)>, Ghost(tv): Ghost<Seq<SortTask>>, Ghost(bnds): Ghost<Seq<int>>,
    n: usize, Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Option<Option<Acc>>)
    requires
        stasks_ok(tv, bnds, fp, cp, ps),
        bnds[tv.len() as int] == n,
        n == n_pa(cp),
        outs@.len() == tv.len(),
        forall|t: int| 0 <= t < tv.len() ==> (#[trigger] tv[t]).post(outs@[t]),
    ensures r matches Some(o) ==> out_ok(fp, cp, ps, 0, n as int, o),
{
    let ghost zs = pa_rows(cp);
    let mut acc = Acc { sum: 0, mass: 0, any: false };
    let mut i: usize = 0;
    proof {
        if tv.len() > 0 {
            assert(tv[0].pre());
        }
        lemma_sum_empty(zs, pin(fp, ps, 0), 0);
        lemma_sum_empty(zs, pin(fp, ps, 1), 0);
        lemma_sum_empty(zs, pin(fp, ps, 2), 0);
    }
    while i < outs.len()
        invariant
            stasks_ok(tv, bnds, fp, cp, ps),
            bnds[tv.len() as int] == n,
            n == n_pa(cp),
            outs@.len() == tv.len(),
            forall|t: int| 0 <= t < tv.len() ==> (#[trigger] tv[t]).post(outs@[t]),
            zs == pa_rows(cp),
            i <= tv.len(),
            0 <= bnds[i as int] <= n,
            acc_ok(acc, fp, cp, ps, 0, bnds[i as int]),
            acc_small(acc),
        decreases outs.len() - i,
    {
        let ghost (m, e) = (bnds[i as int], bnds[i + 1]);
        proof {
            assert(tv[i as int].pre());
            assert(tv[i as int].post(outs@[i as int]));
            assert(pa_cols_ok(tv[i as int].pa, cp));
        }
        let (ok, o) = outs[i];
        if !ok {
            return None;
        }
        proof {
            lemma_tot_mass_le(fp, cp, ps, 0, m, e, n as int);
            lemma_tot_mass_le(fp, cp, ps, 0, 0, m, n as int);
            lemma_sum_split(zs, pin(fp, ps, 0), 0, m, e);
            lemma_sum_split(zs, pin(fp, ps, 1), 0, m, e);
            lemma_sum_split(zs, pin(fp, ps, 2), 0, m, e);
            lemma_tot_mass_le(fp, cp, ps, 0, 0, e, n as int);
            lemma_tot_bounds(fp, cp, ps, 0, m);
            lemma_tot_bounds(fp, cp, ps, m, e);
        }
        let x = match o {
            Some(x) => x,
            None => return Some(None),
        };
        if x.mass > i128::MAX - acc.mass {
            return Some(None);
        }
        acc = Acc { sum: acc.sum + x.sum, mass: acc.mass + x.mass, any: acc.any || x.any };
        i = i + 1;
    }
    proof {
        if tv.len() == 0 {
            assert(bnds[0] == 0);
        }
    }
    Some(Some(acc))
}

/// The sorted plan over every part row with `workers` tasks at most: `None` when it does not apply (no key index,
/// too many lineitem rows) or a task's buffers were too small; the caller then runs the kernel scan.
pub fn sorted_plan(li: &LiCols, pa: &PaCols, lk: &LiK, arms: &Arms, dir: &Dir, workers: usize,
    dispatch: &mut crate::gendb_entry::parallel::Dispatch,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Option<Result<Option<Acc>, crate::gendb_entry::runtime::QueryError>>)
    requires
        scan_pre(*li, *pa, *lk, *arms, fp, cp, ps),
        dir_ok(*dir),
        1 <= workers <= crate::gendb_entry::parallel::MAX_WORKERS,
    ensures
        r matches Some(Ok(o)) ==> out_ok(fp, cp, ps, 0, n_pa(cp), o),
        r matches Some(Err(e)) ==> e is WorkerFailed,
{
    if li.kind == 0 || li.n >= 0x4000_0000 {
        return None;
    }
    let nt: usize = if workers == 1 || pa.n < 65536 { 1 } else { workers };
    let bsz: u64 = if nt == 1 { 65536 } else { 262144 };
    let dvb = Divisor::new(bsz);
    let nbk: usize = (li.n as u64 / bsz) as usize + 1;
    let win = Win { lo: [arms.a0.qlo, arms.a1.qlo, arms.a2.qlo], hi: [arms.a0.qhi, arms.a1.qhi, arms.a2.qhi] };
    proof {
        assert(win.lo@[0] == arms.a0.qlo && win.lo@[1] == arms.a1.qlo && win.lo@[2] == arms.a2.qlo);
        assert(win.hi@[0] == arms.a0.qhi && win.hi@[1] == arms.a1.qhi && win.hi@[2] == arms.a2.qhi);
        assert(win_ok(win, ps));
    }
    // Entry and range capacities: generous bounds (lazily mapped); a task beyond them fails and the caller falls back.
    let mut cap_e: usize = li.n / 8 / nt + 65536;
    if cap_e < 8_500_000 {
        cap_e = 8_500_000;
    }
    if nt == 1 {
        let cap_r: usize = if pa.n / 64 + 4096 < 4_200_000 { 4_200_000 } else { pa.n / 64 + 4096 };
        let t = new_task(li, pa, lk, arms, &win, dir, &dvb, nbk, 0, pa.n, cap_e, cap_r, Ghost(fp), Ghost(cp), Ghost(ps));
        let (ok, o) = t.run();
        if !ok {
            return None;
        }
        return Some(Ok(o));
    }
    let mut tasks: Vec<SortTask> = Vec::new();
    let ghost mut bnds: Seq<int> = seq![0int];
    let mut a: usize = 0;
    let mut t: usize = 0;
    while t < nt
        invariant
            scan_pre(*li, *pa, *lk, *arms, fp, cp, ps),
            sort_pre(*li, *pa, *lk, *arms, *dir, dvb, nbk as int, fp, cp, ps),
            win_ok(win, ps),
            cap_e <= u32::MAX,
            nbk < usize::MAX,
            1 <= nt <= crate::gendb_entry::parallel::MAX_WORKERS,
            t <= nt,
            a <= pa.n,
            t == nt ==> a == pa.n,
            tasks@.len() == t,
            bnds[t as int] == a,
            stasks_ok(tasks@, bnds, fp, cp, ps),
        decreases nt - t,
    {
        proof {
            let num = (t as int + 1) * (pa.n as int);
            assert(num <= (nt as int) * (pa.n as int)) by (nonlinear_arith)
                requires num == (t as int + 1) * (pa.n as int), t + 1 <= nt, pa.n >= 0;
            assert(0 <= num <= 64 * 0xffff_ffff_ffff_ffff) by (nonlinear_arith)
                requires num == (t as int + 1) * (pa.n as int), t + 1 <= 64, 0 <= pa.n <= 0xffff_ffff_ffff_ffff;
            assert(num / (nt as int) <= pa.n as int) by (nonlinear_arith)
                requires num <= (nt as int) * (pa.n as int), nt >= 1, num >= 0;
        }
        let e0 = ((t as u128 + 1) * pa.n as u128 / nt as u128) as usize;
        let e1 = if e0 < a { a } else { e0 };
        let e = if t + 1 == nt { pa.n } else { e1 };
        let cap_r: usize = if (e - a) / 64 + 4096 < 4_200_000 { 4_200_000 } else { (e - a) / 64 + 4096 };
        let task = new_task(li, pa, lk, arms, &win, dir, &dvb, nbk, a, e, cap_e, cap_r, Ghost(fp), Ghost(cp), Ghost(ps));
        let ghost old_tasks = tasks@;
        tasks.push(task);
        proof {
            bnds = bnds.push(e as int);
            assert forall|k: int| 0 <= k < tasks@.len() implies {
                &&& (#[trigger] tasks@[k]).j_lo == bnds[k]
                &&& tasks@[k].j_hi == bnds[k + 1]
                &&& tasks@[k].fp@ == fp && tasks@[k].cp@ == cp && tasks@[k].ps@ == ps
                &&& tasks@[k].pre()
            } by {
                if k < t {
                    assert(tasks@[k] == old_tasks[k]);
                }
            }
        }
        a = e;
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = match crate::gendb_entry::parallel::fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Some(Err(crate::gendb_entry::runtime::QueryError::WorkerFailed(e))),
    };
    match merge_sorted(&outs, Ghost(tv), Ghost(bnds), pa.n, Ghost(fp), Ghost(cp), Ghost(ps)) {
        Some(o) => Some(Ok(o)),
        None => None,
    }
}

} // verus!
