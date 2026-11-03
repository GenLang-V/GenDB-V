//! Pass 1 of the fast plan: per task, a range of lineitem blocks; per supplier key slot `t` (key `kmin + t`), the
//! saturated sum `min(255, sum q)` of `q = revenue / 2^qs + 1` over the task's qualifying rows of that key
//! (`acc_ok`): an upper bound of the group's revenue in units of `2^qs`, small enough for one byte per key.
//!
//! Layout read: lineitem blocks of `bs` rows; per block the l_shipdate base and zone maximum (a block whose dates
//! miss the window is skipped), then 64-row chunks: the mask of shipdate codes in the window (`range_mask16`), the
//! entries of all 64 rows in one vectorized loop (`chunk_entries`: slot in the low 24 bits, bound unit capped at 255
//! in the high 8 bits, and a mask of rows whose revenue is not positive), then the set bits of the mask in
//! increasing order (`pop_lowest`). Each entry goes to its slot byte directly (`bcap == 0`) or is appended to the
//! bucket of its slot (`t >> sh`, at most 64 buckets of `bcap` entries); a full bucket is flushed into its slot
//! bytes (`flush`), so the bytes a flush touches are one small key range that stays in cache. Invariant
//! (`bk_ok`/`slot_ok`): per slot, `sat(byte + pending units) == sat(bound sum)`; capping a unit at 255 and adding
//! in another order keep it (`lemma_sat_cap`, `lemma_sat_add`). Guards per block (else the task fails and the query
//! takes the general plan): price base in `[0, 2^32]`, discount base in `[0, 256]`, key base near `kmin`; per
//! qualifying row: revenue positive. These make every qualifying row's revenue lie in `(0, 2^42)` (`fast_row`).
use vstd::prelude::*;
use vstd::arithmetic::power2::pow2;
use crate::spec::value::*;
use crate::link::query::*;
use crate::link::expr::ival;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use super::group::*;
use super::model::*;
use super::general::{kr, row_vals, lemma_hit_row};
use super::common::bits::*;

verus! {

// ------------------------------------------------------------------------------------------------ specification

/// The bound unit of a row: its revenue in units of `2^qs`, rounded up past it (`revenue < 2^qs * q` when the
/// revenue is not negative).
pub open spec fn qv_of(x: Row, qs: nat) -> int {
    rev_of(x) / (pow2(qs) as int) + 1
}

/// The normal form of the bound sums: `revenue0`'s groups with the bound unit as argument.
pub open spec fn qb(lo: int, hi: int, qs: nat) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| qual_of(lo, hi, x),
        key: |x: Row| key_of(x),
        arg: |j: int, x: Row| qv_of(x, qs),
        aggs: seq![AggKind::Sum { scale: 4 }],
        outs: seq![0nat, 1nat],
        grouped: true,
    }
}

/// `x` saturated at 255.
pub open spec fn sat(x: int) -> int {
    if x < 255 { x } else { 255 }
}

/// The fast plan's row fact: a qualifying row has a revenue in `(0, 2^42)`.
pub open spec fn fast_row(lo: int, hi: int, x: Row) -> bool {
    qual_of(lo, hi, x) ==> 0 < rev_of(x) < 0x400_0000_0000
}

/// The window and the key slots of the fast plan.
#[derive(Clone, Copy)]
pub struct Win {
    pub lo: i64,
    pub hi: i64,
    pub kmin: i64,
    pub cap: usize,
    pub qs: u64,
}

/// Every stored row's key lies in the slots `[kmin, kmin + cap)`.
pub open spec fn keys_in(c: Li, w: Win) -> bool {
    forall|j: int| 0 <= j < c.n ==> w.kmin <= #[trigger] supp_v(c, j) < w.kmin + w.cap
}

/// First row of block `g`.
pub open spec fn rs(c: Li, g: int) -> int {
    if g * c.bs <= c.n { g * c.bs } else { c.n as int }
}

/// The bound sums of the rows `[r0, r)` in the slots `[0, cap)`, saturated.
pub open spec fn acc_ok(acc: Seq<u8>, w: Win, xs: Seq<Row>, r0: int, r: int) -> bool {
    &&& acc.len() >= w.cap
    &&& forall|t: int| 0 <= t < w.cap ==> #[trigger] acc[t] as int
            == sat(gsum(qb(w.lo as int, w.hi as int, w.qs as nat), xs.subrange(r0, r), kr(w.kmin + t), 0))
}

/// Every row of `[a, b)` has the fast plan's row fact.
pub open spec fn rows_fast(w: Win, xs: Seq<Row>, a: int, b: int) -> bool {
    forall|j: int| a <= j < b ==> fast_row(w.lo as int, w.hi as int, #[trigger] xs[j])
}

/// What the kernels need of the window and slices.
pub open spec fn kern_ok(c: Li, w: Win) -> bool {
    &&& li_shape(c)
    &&& keys_in(c, w)
    &&& w.qs < 64
    &&& c.bs <= 0x1_0000_0000
    &&& forall|j: int| 0 <= j < c.n ==> #[trigger] ship_v(c, j) <= c.ship_zmax@[j / c.bs as int]
}

// ------------------------------------------------------------------------------------------------ lemmas

/// Group keys of distinct slots differ.
pub proof fn lemma_kr_inj(a: int, b: int)
    ensures (kr(a) == kr(b)) == (a == b),
{
    if kr(a) == kr(b) {
        assert(kr(a)[0] == kr(b)[0]);
    }
}

/// `sat(sat(s) + q) == sat(s + q)` for `s, q >= 0`.
pub proof fn lemma_sat_add(s: int, q: int)
    requires s >= 0, q >= 0,
    ensures sat(sat(s) + q) == sat(s + q),
{
}

/// The bound sums over rows with the fast row fact are not negative.
pub proof fn lemma_qsum_nonneg(w: Win, xs: Seq<Row>, r0: int, r: int, k: Row)
    requires 0 <= r0 <= r <= xs.len(), rows_fast(w, xs, r0, r),
    ensures gsum(qb(w.lo as int, w.hi as int, w.qs as nat), xs.subrange(r0, r), k, 0) >= 0,
    decreases r - r0,
{
    let g = qb(w.lo as int, w.hi as int, w.qs as nat);
    if r > r0 {
        lemma_qsum_nonneg(w, xs, r0, r - 1, k);
        lemma_range_step(g, xs, r0, r - 1, k, 0);
        if hit(g, xs[r - 1], k) {
            assert(fast_row(w.lo as int, w.hi as int, xs[r - 1]));
            vstd::arithmetic::power2::lemma_pow2_pos(w.qs as nat);
            assert(rev_of(xs[r - 1]) / (pow2(w.qs as nat) as int) >= 0) by (nonlinear_arith)
                requires rev_of(xs[r - 1]) > 0, pow2(w.qs as nat) > 0;
        }
    } else {
        lemma_empty(g, xs, r0, k, 0);
    }
}

/// One non-qualifying row leaves every bound sum.
pub proof fn lemma_step_skip(acc: Seq<u8>, w: Win, xs: Seq<Row>, r0: int, j: int)
    requires
        acc_ok(acc, w, xs, r0, j),
        0 <= r0 <= j < xs.len(),
        !qual_of(w.lo as int, w.hi as int, xs[j]),
    ensures acc_ok(acc, w, xs, r0, j + 1),
{
    let g = qb(w.lo as int, w.hi as int, w.qs as nat);
    assert forall|t: int| 0 <= t < w.cap implies #[trigger] acc[t] as int == sat(gsum(g, xs.subrange(r0, j + 1), kr(w.kmin + t), 0)) by {
        lemma_range_step(g, xs, r0, j, kr(w.kmin + t), 0);
    }
}

/// Non-qualifying rows `[a, b)` leave every bound sum.
pub proof fn lemma_skip_range(acc: Seq<u8>, w: Win, xs: Seq<Row>, r0: int, a: int, b: int)
    requires
        acc_ok(acc, w, xs, r0, a),
        rows_fast(w, xs, r0, a),
        0 <= r0 <= a <= b <= xs.len(),
        forall|j: int| a <= j < b ==> !qual_of(w.lo as int, w.hi as int, #[trigger] xs[j]),
    ensures acc_ok(acc, w, xs, r0, b), rows_fast(w, xs, r0, b),
    decreases b - a,
{
    if a < b {
        lemma_step_skip(acc, w, xs, r0, a);
        lemma_skip_range(acc, w, xs, r0, a + 1, b);
    }
}

/// One qualifying row of slot `t0` with bound unit `q` adds `q` to its slot (saturated) and nothing elsewhere.
pub proof fn lemma_step_hit(acc: Seq<u8>, w: Win, xs: Seq<Row>, r0: int, j: int, t0: int, nv: u8)
    requires
        acc_ok(acc, w, xs, r0, j),
        rows_fast(w, xs, r0, j),
        0 <= r0 <= j < xs.len(),
        0 <= t0 < w.cap,
        qual_of(w.lo as int, w.hi as int, xs[j]),
        key_of(xs[j]) == kr(w.kmin + t0),
        qv_of(xs[j], w.qs as nat) >= 0,
        nv as int == sat(acc[t0] as int + qv_of(xs[j], w.qs as nat)),
    ensures acc_ok(acc.update(t0, nv), w, xs, r0, j + 1),
{
    let g = qb(w.lo as int, w.hi as int, w.qs as nat);
    let acc2 = acc.update(t0, nv);
    assert forall|t: int| 0 <= t < w.cap implies #[trigger] acc2[t] as int == sat(gsum(g, xs.subrange(r0, j + 1), kr(w.kmin + t), 0)) by {
        lemma_range_step(g, xs, r0, j, kr(w.kmin + t), 0);
        lemma_kr_inj(w.kmin + t, w.kmin + t0);
        if t == t0 {
            lemma_qsum_nonneg(w, xs, r0, j, kr(w.kmin + t));
            lemma_sat_add(gsum(g, xs.subrange(r0, j), kr(w.kmin + t), 0), qv_of(xs[j], w.qs as nat));
        }
    }
}

/// Row `j` of block `b` lies in the block's rows and decodes with its block's bases.
pub proof fn lemma_block_row(c: Li, b: int, j: int)
    requires li_shape(c), 0 <= b, rs(c, b) <= j < rs(c, b + 1),
    ensures j / (c.bs as int) == b, 0 <= j < c.n, b < c.nb,
{
    let bs = c.bs as int;
    assert(b * bs <= j < (b + 1) * bs);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(b * bs, j, bs);
    vstd::arithmetic::div_mod::lemma_div_multiples_vanish(b, bs);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, bs);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, bs);
    assert(j / bs == b) by (nonlinear_arith)
        requires b * bs <= j, j < (b + 1) * bs, bs >= 1, j == bs * (j / bs) + j % bs, 0 <= j % bs < bs;
    crate::stores::lisupp::interface::common::read::lemma_div_lt(j, bs, c.nb as int);
}

/// Block starts are nondecreasing.
pub proof fn lemma_rs_mono(c: Li, a: int, b: int)
    requires 0 <= a <= b,
    ensures rs(c, a) <= rs(c, b), rs(c, 0) == 0,
{
    assert(a * (c.bs as int) <= b * (c.bs as int)) by (nonlinear_arith) requires a <= b, c.bs >= 0;
}

/// The block start `rs(c, g)` in `usize`.
pub fn row_start(c: &Li, g: usize) -> (r: usize)
    requires li_shape(*c), g <= c.nb, c.bs <= 0x1_0000_0000,
    ensures r == rs(*c, g as int),
    no_unwind
{
    proof {
        assert(g as int * c.bs as int <= 0x1_0000_0000_0000_0000 * 0x1_0000_0000) by (nonlinear_arith)
            requires g <= 0x1_0000_0000_0000_0000, c.bs <= 0x1_0000_0000;
    }
    let gb = g as u128 * c.bs as u128;
    if gb <= c.n as u128 { gb as usize } else { c.n }
}

// ------------------------------------------------------------------------------------------------ block decoding

/// `x` clamped into `[0, 65536]`.
pub open spec fn clamp16(x: int) -> int {
    if x < 0 { 0 } else if x > 65536 { 65536 } else { x }
}

fn clamp16_exec(x: i128) -> (r: u32)
    ensures r as int == clamp16(x as int),
    no_unwind
{
    if x < 0 { 0 } else if x > 65536 { 65536 } else { x as u32 }
}

/// The per-block decoding facts of a qualifying-row step.
pub open spec fn blk_ok(c: Li, w: Win, b: int, kofs: i64, bp: i64, dd: i64) -> bool {
    &&& 0 <= b < c.nb
    &&& kofs == c.supp_base@[b] - w.kmin
    &&& -0x1_0000_0000 <= kofs <= 0x1_0000_0000
    &&& bp == c.price_base@[b] && 0 <= bp <= 0x1_0000_0000
    &&& dd == 100 - c.disc_base@[b] && 0 <= c.disc_base@[b] <= 0x100
}

// ------------------------------------------------------------------------------------------------ pending units

/// Entries per bucket when the tasks run serially on the calling thread (see `fast::pass1`).
pub const BCAP: usize = 2048;

/// A pending entry's slot (low 24 bits).
pub open spec fn es(e: u32) -> int {
    (e & 0xFF_FFFFu32) as int
}

/// A pending entry's bound unit, capped at 255 (high 8 bits).
pub open spec fn eu(e: u32) -> int {
    (e >> 24u32) as int
}

/// `q` capped at 255 (what an entry holds; the slot bytes saturate at 255 anyway).
pub open spec fn cap8(q: int) -> int {
    if q < 255 { q } else { 255 }
}

/// The pending units of slot `t` among the entries `s`.
pub open spec fn psum(s: Seq<u32>, t: int) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if es(s[0]) == t { eu(s[0]) } else { 0 }) + psum(s.subrange(1, s.len() as int), t)
    }
}

/// The bucket of slot `t` (`t >> sh`).
pub open spec fn bko(t: int, sh: u32) -> int {
    ((t as u32) >> sh) as int
}

/// The (unsaturated) bound sum of slot `t` over the rows `[r0, r)`.
pub open spec fn gq(w: Win, xs: Seq<Row>, r0: int, r: int, t: int) -> int {
    gsum(qb(w.lo as int, w.hi as int, w.qs as nat), xs.subrange(r0, r), kr(w.kmin + t), 0)
}

/// Slot `t`: its byte plus its pending units, saturated, is its bound sum, saturated.
pub open spec fn slot_ok(acc: Seq<u8>, pend: Seq<Seq<u32>>, sh: u32, w: Win, xs: Seq<Row>, r0: int, r: int, t: int)
    -> bool
{
    sat(acc[t] as int + psum(pend[bko(t, sh)], t)) == sat(gq(w, xs, r0, r, t))
}

/// The bucket buffers: `cnt.len()` buckets of `bcap` entries in `buf`; bucket `b` holds the entries `pend[b]`, each
/// of a slot of bucket `b`.
pub open spec fn bufs_ok(buf: Seq<u32>, cnt: Seq<usize>, sh: u32, bcap: int, pend: Seq<Seq<u32>>, w: Win) -> bool {
    &&& sh < 32
    &&& w.cap <= 0x100_0000
    &&& cnt.len() == pend.len()
    &&& 0 <= bcap <= usize::MAX
    &&& buf.len() == cnt.len() * bcap
    &&& forall|t: int| 0 <= t < w.cap ==> #[trigger] bko(t, sh) < cnt.len()
    &&& forall|b: int| 0 <= b < cnt.len() ==> (#[trigger] pend[b]).len() == cnt[b] && cnt[b] <= bcap
    &&& forall|b: int, i: int| 0 <= b < cnt.len() && 0 <= i < cnt[b] ==>
            buf[b * bcap + i] == #[trigger] pend[b][i] && 0 <= es(pend[b][i]) < w.cap && bko(es(pend[b][i]), sh) == b
}

/// The pass-1 state after the rows `[r0, r)`: slot bytes plus pending entries give every slot's saturated bound sum.
pub open spec fn bk_ok(acc: Seq<u8>, buf: Seq<u32>, cnt: Seq<usize>, sh: u32, bcap: int, pend: Seq<Seq<u32>>, w: Win,
    xs: Seq<Row>, r0: int, r: int) -> bool
{
    &&& acc.len() >= w.cap
    &&& bufs_ok(buf, cnt, sh, bcap, pend, w)
    &&& forall|t: int| 0 <= t < w.cap ==> #[trigger] slot_ok(acc, pend, sh, w, xs, r0, r, t)
}

/// Row `j`'s entry facts: `bad` iff its revenue is not positive; otherwise `e` packs its slot and capped unit.
pub open spec fn ent_ok(c: Li, w: Win, j: int, e: u32, bad: bool) -> bool {
    &&& bad <==> price_v(c, j) * (100 - disc_v(c, j)) <= 0
    &&& !bad ==> es(e) == supp_v(c, j) - w.kmin && eu(e) == cap8(qv_of(xs_of(c)[j], w.qs as nat))
}

// ------------------------------------------------------------------------------------------------ lemmas (pending)

pub proof fn lemma_psum_nonneg(s: Seq<u32>, t: int)
    ensures psum(s, t) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_psum_nonneg(s.subrange(1, s.len() as int), t);
    }
}

/// Appending an entry adds its units to its slot.
pub proof fn lemma_psum_push(s: Seq<u32>, e: u32, t: int)
    ensures psum(s.push(e), t) == psum(s, t) + if es(e) == t { eu(e) } else { 0 },
    decreases s.len(),
{
    let s2 = s.push(e);
    assert(s2[0] == if s.len() == 0 { e } else { s[0] });
    if s.len() == 0 {
        assert(s2.subrange(1, s2.len() as int) =~= Seq::<u32>::empty());
        assert(psum(Seq::<u32>::empty(), t) == 0);
        assert(psum(s, t) == 0);
    } else {
        let r = s.subrange(1, s.len() as int);
        assert(s2.subrange(1, s2.len() as int) =~= r.push(e));
        lemma_psum_push(r, e, t);
        assert(psum(s, t) == (if es(s[0]) == t { eu(s[0]) } else { 0 }) + psum(r, t));
    }
    assert(psum(s2, t) == (if es(s2[0]) == t { eu(s2[0]) } else { 0 }) + psum(s2.subrange(1, s2.len() as int), t));
}

/// The entries from position `i` on: the entry at `i` and those after it.
pub proof fn lemma_psum_skip(s: Seq<u32>, i: int, t: int)
    requires 0 <= i < s.len(),
    ensures psum(s.subrange(i, s.len() as int), t)
        == (if es(s[i]) == t { eu(s[i]) } else { 0 }) + psum(s.subrange(i + 1, s.len() as int), t),
{
    let r = s.subrange(i, s.len() as int);
    assert(r.subrange(1, r.len() as int) =~= s.subrange(i + 1, s.len() as int));
}

/// Saturation forgets everything above 255: equal saturations stay equal after adding `q` on one side and `q` capped
/// at 255 on the other.
pub proof fn lemma_sat_cap(a: int, b: int, q: int)
    requires a >= 0, q >= 0, sat(a) == sat(b),
    ensures sat(a + cap8(q)) == sat(b + q),
{
}

/// A row outside the window changes no bound sum.
pub proof fn lemma_gq_skip(w: Win, xs: Seq<Row>, r0: int, j: int, t: int)
    requires 0 <= r0 <= j < xs.len(), !qual_of(w.lo as int, w.hi as int, xs[j]),
    ensures gq(w, xs, r0, j + 1, t) == gq(w, xs, r0, j, t),
{
    lemma_range_step(qb(w.lo as int, w.hi as int, w.qs as nat), xs, r0, j, kr(w.kmin + t), 0);
}

/// A row in the window adds its unit to its own slot only.
pub proof fn lemma_gq_hit(w: Win, xs: Seq<Row>, r0: int, j: int, t0: int, t: int)
    requires
        0 <= r0 <= j < xs.len(),
        qual_of(w.lo as int, w.hi as int, xs[j]),
        key_of(xs[j]) == kr(w.kmin + t0),
    ensures gq(w, xs, r0, j + 1, t) == gq(w, xs, r0, j, t) + if t == t0 { qv_of(xs[j], w.qs as nat) } else { 0 },
{
    lemma_range_step(qb(w.lo as int, w.hi as int, w.qs as nat), xs, r0, j, kr(w.kmin + t), 0);
    lemma_kr_inj(w.kmin + t, w.kmin + t0);
}

/// Rows outside the window keep the state (and the fast row fact).
pub proof fn lemma_bk_skip(acc: Seq<u8>, buf: Seq<u32>, cnt: Seq<usize>, sh: u32, bcap: int, pend: Seq<Seq<u32>>,
    w: Win, xs: Seq<Row>, r0: int, a: int, b: int)
    requires
        bk_ok(acc, buf, cnt, sh, bcap, pend, w, xs, r0, a),
        rows_fast(w, xs, r0, a),
        0 <= r0 <= a <= b <= xs.len(),
        forall|j: int| a <= j < b ==> !qual_of(w.lo as int, w.hi as int, #[trigger] xs[j]),
    ensures bk_ok(acc, buf, cnt, sh, bcap, pend, w, xs, r0, b), rows_fast(w, xs, r0, b),
    decreases b - a,
{
    if a < b {
        assert forall|t: int| 0 <= t < w.cap implies #[trigger] slot_ok(acc, pend, sh, w, xs, r0, a + 1, t) by {
            assert(slot_ok(acc, pend, sh, w, xs, r0, a, t));
            lemma_gq_skip(w, xs, r0, a, t);
        }
        lemma_bk_skip(acc, buf, cnt, sh, bcap, pend, w, xs, r0, a + 1, b);
    }
}

/// `b * bcap + i` with `i < bcap` lies inside bucket `b` (below `(b + 1) * bcap`, inside `n * bcap` for `b < n`).
pub proof fn lemma_slot_index(b: int, i: int, n: int, bcap: int)
    requires 0 <= b < n, 0 <= i < bcap,
    ensures 0 <= b * bcap + i < n * bcap, b * bcap <= b * bcap + i,
{
    assert(b * bcap + i < n * bcap) by (nonlinear_arith) requires 0 <= b < n, 0 <= i < bcap;
    assert(b * bcap >= 0) by (nonlinear_arith) requires b >= 0, bcap >= 0;
}

/// Bucket `b` ends inside the buffer of `n` buckets.
pub proof fn lemma_slot_base(b: int, n: int, bcap: int)
    requires 0 <= b < n, bcap >= 0,
    ensures 0 <= b * bcap, b * bcap + bcap <= n * bcap,
{
    assert(b * bcap + bcap <= n * bcap) by (nonlinear_arith) requires 0 <= b < n, bcap >= 0;
    assert(b * bcap >= 0) by (nonlinear_arith) requires b >= 0, bcap >= 0;
}

/// Positions in distinct buckets differ.
pub proof fn lemma_slot_disjoint(b: int, i: int, b0: int, i0: int, bcap: int)
    requires 0 <= b, 0 <= b0, b != b0, 0 <= i < bcap, 0 <= i0 < bcap,
    ensures b * bcap + i != b0 * bcap + i0,
{
    if b < b0 {
        assert(b * bcap + i < b0 * bcap + i0) by (nonlinear_arith) requires b < b0, 0 <= i < bcap, 0 <= i0;
    } else {
        assert(b0 * bcap + i0 < b * bcap + i) by (nonlinear_arith) requires b0 < b, 0 <= i0 < bcap, 0 <= i;
    }
}

/// A row in the window, applied to its slot byte directly (`nv` is the byte plus the entry's unit, saturated).
pub proof fn lemma_bk_direct(acc: Seq<u8>, buf: Seq<u32>, cnt: Seq<usize>, sh: u32, bcap: int, pend: Seq<Seq<u32>>,
    w: Win, xs: Seq<Row>, r0: int, j: int, e: u32, nv: u8)
    requires
        bk_ok(acc, buf, cnt, sh, bcap, pend, w, xs, r0, j),
        0 <= r0 <= j < xs.len(),
        qual_of(w.lo as int, w.hi as int, xs[j]),
        0 <= es(e) < w.cap,
        key_of(xs[j]) == kr(w.kmin + es(e)),
        qv_of(xs[j], w.qs as nat) >= 0,
        eu(e) == cap8(qv_of(xs[j], w.qs as nat)),
        nv as int == sat(acc[es(e)] as int + eu(e)),
    ensures bk_ok(acc.update(es(e), nv), buf, cnt, sh, bcap, pend, w, xs, r0, j + 1),
{
    let t0 = es(e);
    let acc2 = acc.update(t0, nv);
    let q = qv_of(xs[j], w.qs as nat);
    assert forall|t: int| 0 <= t < w.cap implies #[trigger] slot_ok(acc2, pend, sh, w, xs, r0, j + 1, t) by {
        assert(slot_ok(acc, pend, sh, w, xs, r0, j, t));
        lemma_gq_hit(w, xs, r0, j, t0, t);
        if t == t0 {
            let p = psum(pend[bko(t, sh)], t);
            lemma_psum_nonneg(pend[bko(t, sh)], t);
            lemma_sat_add(acc[t] as int + eu(e), p);
            lemma_sat_cap(acc[t] as int + p, gq(w, xs, r0, j, t), q);
        }
    }
}

/// A row in the window, appended as entry `e` to the bucket of its slot (not full).
pub proof fn lemma_bk_push(acc: Seq<u8>, buf: Seq<u32>, cnt: Seq<usize>, sh: u32, bcap: int, pend: Seq<Seq<u32>>,
    w: Win, xs: Seq<Row>, r0: int, j: int, e: u32)
    requires
        bk_ok(acc, buf, cnt, sh, bcap, pend, w, xs, r0, j),
        0 <= r0 <= j < xs.len(),
        qual_of(w.lo as int, w.hi as int, xs[j]),
        0 <= es(e) < w.cap,
        key_of(xs[j]) == kr(w.kmin + es(e)),
        qv_of(xs[j], w.qs as nat) >= 0,
        eu(e) == cap8(qv_of(xs[j], w.qs as nat)),
        cnt[bko(es(e), sh)] < bcap,
    ensures ({
        let b0 = bko(es(e), sh);
        bk_ok(acc, buf.update(b0 * bcap + cnt[b0], e), cnt.update(b0, (cnt[b0] + 1) as usize), sh, bcap,
            pend.update(b0, pend[b0].push(e)), w, xs, r0, j + 1)
    }),
{
    let t0 = es(e);
    let b0 = bko(t0, sh);
    let n0 = cnt[b0] as int;
    let buf2 = buf.update(b0 * bcap + n0, e);
    let cnt2 = cnt.update(b0, (n0 + 1) as usize);
    let pend2 = pend.update(b0, pend[b0].push(e));
    let q = qv_of(xs[j], w.qs as nat);
    assert(b0 < cnt.len());
    lemma_slot_index(b0, n0, cnt.len() as int, bcap);
    assert(pend[b0].len() == cnt[b0]);
    assert forall|b: int| 0 <= b < cnt2.len() implies (#[trigger] pend2[b]).len() == cnt2[b] && cnt2[b] <= bcap by {
        if b != b0 {
            assert(pend2[b] == pend[b]);
            assert(pend[b].len() == cnt[b] && cnt[b] <= bcap);
        }
    }
    assert forall|b: int, i: int| 0 <= b < cnt2.len() && 0 <= i < cnt2[b] implies
        buf2[b * bcap + i] == #[trigger] pend2[b][i] && 0 <= es(pend2[b][i]) < w.cap && bko(es(pend2[b][i]), sh) == b by {
        if b == b0 {
            if i < n0 {
                assert(pend2[b][i] == pend[b][i]);
                assert(b * bcap + i != b0 * bcap + n0);
            }
        } else {
            assert(pend2[b] == pend[b]);
            assert(pend[b].len() == cnt[b] && cnt[b] <= bcap);
            assert(buf[b * bcap + i] == pend[b][i]);
            lemma_slot_disjoint(b, i, b0, n0, bcap);
        }
    }
    assert(bufs_ok(buf2, cnt2, sh, bcap, pend2, w));
    assert forall|t: int| 0 <= t < w.cap implies #[trigger] slot_ok(acc, pend2, sh, w, xs, r0, j + 1, t) by {
        assert(slot_ok(acc, pend, sh, w, xs, r0, j, t));
        lemma_gq_hit(w, xs, r0, j, t0, t);
        let bt = bko(t, sh);
        if bt == b0 {
            lemma_psum_push(pend[b0], e, t);
            if t == t0 {
                lemma_psum_nonneg(pend[b0], t);
                lemma_sat_cap(acc[t] as int + psum(pend[b0], t), gq(w, xs, r0, j, t), q);
            }
        }
    }
}

/// The initial state: zero bytes and empty buckets over no rows.
pub proof fn lemma_bk_init(acc: Seq<u8>, buf: Seq<u32>, cnt: Seq<usize>, sh: u32, bcap: int, w: Win, xs: Seq<Row>,
    r0: int)
    requires
        acc.len() >= w.cap,
        forall|t: int| 0 <= t < acc.len() ==> #[trigger] acc[t] == 0,
        forall|b: int| 0 <= b < cnt.len() ==> #[trigger] cnt[b] == 0,
        sh < 32, w.cap <= 0x100_0000, 0 <= bcap <= usize::MAX, buf.len() == cnt.len() * bcap,
        forall|t: int| 0 <= t < w.cap ==> #[trigger] bko(t, sh) < cnt.len(),
        0 <= r0 <= xs.len(),
    ensures bk_ok(acc, buf, cnt, sh, bcap, Seq::new(cnt.len(), |b: int| Seq::<u32>::empty()), w, xs, r0, r0),
{
    let pend = Seq::new(cnt.len(), |b: int| Seq::<u32>::empty());
    assert forall|b: int| 0 <= b < cnt.len() implies (#[trigger] pend[b]).len() == cnt[b] && cnt[b] <= bcap by {
        assert(cnt[b] == 0);
    }
    assert forall|b: int, i: int| 0 <= b < cnt.len() && 0 <= i < cnt[b] implies
        buf[b * bcap + i] == #[trigger] pend[b][i] && 0 <= es(pend[b][i]) < w.cap && bko(es(pend[b][i]), sh) == b by {
        assert(cnt[b] == 0);
    }
    assert(bufs_ok(buf, cnt, sh, bcap, pend, w));
    assert forall|t: int| 0 <= t < w.cap implies #[trigger] slot_ok(acc, pend, sh, w, xs, r0, r0, t) by {
        lemma_empty(qb(w.lo as int, w.hi as int, w.qs as nat), xs, r0, kr(w.kmin + t), 0);
        assert(pend[bko(t, sh)] =~= Seq::<u32>::empty());
    }
}

/// Every bucket empty: the slot bytes are the saturated bound sums.
pub proof fn lemma_bk_done(acc: Seq<u8>, buf: Seq<u32>, cnt: Seq<usize>, sh: u32, bcap: int, pend: Seq<Seq<u32>>,
    w: Win, xs: Seq<Row>, r0: int, r: int)
    requires
        bk_ok(acc, buf, cnt, sh, bcap, pend, w, xs, r0, r),
        forall|b: int| 0 <= b < cnt.len() ==> #[trigger] cnt[b] == 0,
    ensures acc_ok(acc, w, xs, r0, r),
{
    assert forall|t: int| 0 <= t < w.cap implies #[trigger] acc[t] as int
        == sat(gsum(qb(w.lo as int, w.hi as int, w.qs as nat), xs.subrange(r0, r), kr(w.kmin + t), 0)) by {
        assert(slot_ok(acc, pend, sh, w, xs, r0, r, t));
        let b = bko(t, sh);
        assert(pend[b].len() == cnt[b]);
        assert(psum(pend[b], t) == 0);
    }
}

// ------------------------------------------------------------------------------------------------ the kernel

/// Row `j` of block `b`: its slot, revenue and bound unit from the block bases (`None`-free arithmetic: every value
/// fits its type).
proof fn lemma_row_codes(c: Li, w: Win, b: int, j: int, kofs: i64, bp: i64, dd: i64)
    requires
        kern_ok(c, w), w.cap <= 0x100_0000,
        blk_ok(c, w, b, kofs, bp, dd),
        rs(c, b) <= j < rs(c, b + 1),
    ensures
        0 <= j < c.n, j / (c.bs as int) == b,
        0 <= kofs + c.supp@[j] < w.cap,
        kofs + c.supp@[j] == supp_v(c, j) - w.kmin,
        0 <= bp + c.price@[j] < 0x2_0000_0000,
        -0x200 < dd - c.disc@[j] <= 100,
        (bp + c.price@[j]) * (dd - c.disc@[j]) == price_v(c, j) * (100 - disc_v(c, j)),
        -0x400_0000_0000 < (bp + c.price@[j]) * (dd - c.disc@[j]) < 0x400_0000_0000,
        key_of(xs_of(c)[j]) == kr(supp_v(c, j)),
        rev_of(xs_of(c)[j]) == price_v(c, j) * (100 - disc_v(c, j)),
        qual_of(w.lo as int, w.hi as int, xs_of(c)[j]) == (w.lo <= c.ship_base@[b] + c.ship@[j] <= w.hi),
{
    lemma_block_row(c, b, j);
    lemma_hit_row(c, w.lo as int, w.hi as int, j, supp_v(c, j));
    assert(w.kmin <= supp_v(c, j) < w.kmin + w.cap);
    assert(c.price@[j] < 0x1_0000_0000);
    assert(c.disc@[j] < 0x100);
    let pv = bp + c.price@[j];
    let dv = dd - c.disc@[j];
    assert(-0x400_0000_0000 < pv * dv < 0x400_0000_0000) by (nonlinear_arith)
        requires 0 <= pv < 0x2_0000_0000, -0x200 < dv <= 100;
}

/// 64 zero entries (a literal: an array repeat expression is a call that may unwind).
pub const ZERO64: [u32; 64] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
];

/// The entries of the rows `[k, k + 64)` of block `b` (a loop the compiler vectorizes): bit `i` of the mask is set
/// iff row `k + i` has a revenue not above 0; otherwise entry `i` packs its slot and capped bound unit.
#[inline(always)]
fn chunk_entries(c: &Li, w: &Win, k: usize, b: usize, kofs: i64, bp: i64, dd: i64) -> (r: ([u32; 64], u64))
    requires
        kern_ok(*c, *w), w.cap <= 0x100_0000,
        k + 64 <= c.n,
        rs(*c, b as int) <= k, k + 64 <= rs(*c, b + 1),
        blk_ok(*c, *w, b as int, kofs, bp, dd),
    ensures forall|i: int| 0 <= i < 64 ==> #[trigger] ent_ok(*c, *w, k + i, r.0@[i], bit(r.1, i)),
    no_unwind
{
    let mut ent: [u32; 64] = ZERO64;
    let mut bad: u64 = 0;
    proof {
        assert forall|i: int| 0 <= i < 64 implies !#[trigger] bit(bad, i) by { lemma_no_bit_of_zero(i); }
    }
    let mut i: usize = 0;
    while i < 64
        invariant
            kern_ok(*c, *w), w.cap <= 0x100_0000,
            k + 64 <= c.n,
            rs(*c, b as int) <= k, k + 64 <= rs(*c, b + 1),
            blk_ok(*c, *w, b as int, kofs, bp, dd),
            i <= 64,
            forall|ii: int| 0 <= ii < i ==> #[trigger] ent_ok(*c, *w, k + ii, ent@[ii], bit(bad, ii)),
            forall|ii: int| i <= ii < 64 ==> !#[trigger] bit(bad, ii),
        decreases 64 - i,
    {
        let j = k + i;
        proof {
            lemma_row_codes(*c, *w, b as int, j as int, kofs, bp, dd);
            vstd::arithmetic::power2::lemma_pow2_pos(w.qs as nat);
        }
        let pv = bp + c.price[j] as i64;
        let dv = dd - c.disc[j] as i64;
        let v = pv * dv;
        let vu: u64 = if v > 0 { v as u64 } else { 0 };
        proof {
            vstd::bits::lemma_u64_shr_is_div(vu, w.qs);
            assert(vu as nat / pow2(w.qs as nat) <= vu) by (nonlinear_arith)
                requires pow2(w.qs as nat) >= 1;
        }
        let q = (vu >> w.qs) + 1;
        let q8: u32 = if q > 255 { 255 } else { q as u32 };
        let t = (kofs + c.supp[j] as i64) as u32;
        proof {
            lemma_pack24(t, q8);
        }
        let ghost e0 = ent@;
        ent[i] = t | (q8 << 24u32);
        let nb: u64 = if v <= 0 { 1 } else { 0 };
        let ghost b0 = bad;
        bad = bad | (nb << (i as u64));
        proof {
            assert forall|ii: int| 0 <= ii < 64 implies #[trigger] bit(bad, ii)
                == (if ii == i { bit(b0, ii) || nb == 1 } else { bit(b0, ii) }) by {
                lemma_set_bit(b0, nb, i as u64, ii);
            }
            let e = ent@[i as int];
            assert(!bit(b0, i as int));
            assert(ent_ok(*c, *w, k + i, e, bit(bad, i as int))) by {
                if v > 0 {
                    assert(q == qv_of(xs_of(*c)[j as int], w.qs as nat));
                }
            }
            assert forall|ii: int| 0 <= ii < i + 1 implies #[trigger] ent_ok(*c, *w, k + ii, ent@[ii], bit(bad, ii)) by {
                if ii < i {
                    assert(ent_ok(*c, *w, k + ii, e0[ii], bit(b0, ii)));
                    assert(ent@[ii] == e0[ii]);
                }
            }
        }
        i = i + 1;
    }
    (ent, bad)
}

/// The bound units of the rows `[k, k + 64)` of block `b`, by their mask of shipdate codes in the window: in direct
/// mode (`bcap == 0`) straight into the slot bytes, else appended to the buckets (a full bucket is flushed first).
fn chunk64(c: &Li, w: &Win, acc: &mut Vec<u8>, buf: &mut Vec<u32>, cnt: &mut Vec<usize>, sh: u32, bcap: usize,
    k: usize, b: usize, sl: u32, sh16: u32, kofs: i64, bp: i64, dd: i64,
    Ghost(r0): Ghost<int>, Ghost(sb): Ghost<int>, Ghost(pend): Ghost<Seq<Seq<u32>>>)
    -> (r: (bool, Ghost<Seq<Seq<u32>>>))
    requires
        kern_ok(*c, *w),
        bk_ok(old(acc)@, old(buf)@, old(cnt)@, sh, bcap as int, pend, *w, xs_of(*c), r0, k as int),
        rows_fast(*w, xs_of(*c), r0, k as int),
        0 <= r0 <= k, k + 64 <= c.n,
        rs(*c, b as int) <= k, k + 64 <= rs(*c, b + 1),
        blk_ok(*c, *w, b as int, kofs, bp, dd),
        sb == c.ship_base@[b as int],
        sl as int == clamp16(w.lo - sb),
        sh16 as int == clamp16(w.hi - sb + 1),
    ensures
        r.0 ==> bk_ok(final(acc)@, final(buf)@, final(cnt)@, sh, bcap as int, r.1@, *w, xs_of(*c), r0, k + 64)
            && rows_fast(*w, xs_of(*c), r0, k + 64),
        final(acc)@.len() == old(acc)@.len(),
        final(buf)@.len() == old(buf)@.len(),
        final(cnt)@.len() == old(cnt)@.len(),
    no_unwind
{
    let ghost xs = xs_of(*c);
    let ghost mut pend = pend;
    let mask = range_mask16(c.ship, k, sl, sh16);
    // a row qualifies exactly when its code is in [sl, sh16)
    proof {
        assert forall|bb: int| 0 <= bb < 64 implies (#[trigger] bit(mask, bb) <==> qual_of(w.lo as int, w.hi as int, xs[k + bb])) by {
            lemma_row_codes(*c, *w, b as int, k + bb, kofs, bp, dd);
        }
    }
    if mask == 0 {
        proof {
            assert forall|j: int| k <= j < k + 64 implies !qual_of(w.lo as int, w.hi as int, #[trigger] xs[j]) by {
                assert(!bit(0u64, j - k)) by { lemma_no_bit_of_zero(j - k); }
                assert(bit(mask, j - k) <==> qual_of(w.lo as int, w.hi as int, xs[j]));
            }
            lemma_bk_skip(acc@, buf@, cnt@, sh, bcap as int, pend, *w, xs, r0, k as int, k + 64);
        }
        return (true, Ghost(pend));
    }
    // the last of the 64 rows, read first: its bounds checks tell the compiler that the whole chunk is inside every
    // column, so the entry loop needs none and is vectorized
    let _last = (c.price[k + 63], c.disc[k + 63], c.supp[k + 63]);
    let (ent, bad) = chunk_entries(c, w, k, b, kofs, bp, dd);
    if bad & mask != 0 {
        return (false, Ghost(pend));
    }
    let ghost mut lim: int = 0;
    let mut m = mask;
    while m != 0
        invariant
            kern_ok(*c, *w),
            xs == xs_of(*c),
            0 <= r0 <= k, k + 64 <= c.n,
            rs(*c, b as int) <= k, k + 64 <= rs(*c, b + 1),
            blk_ok(*c, *w, b as int, kofs, bp, dd),
            bad & mask == 0,
            forall|i: int| 0 <= i < 64 ==> #[trigger] ent_ok(*c, *w, k + i, ent@[i], bit(bad, i)),
            forall|bb: int| 0 <= bb < 64 ==> (#[trigger] bit(mask, bb) <==> qual_of(w.lo as int, w.hi as int, xs[k + bb])),
            0 <= lim <= 64,
            bk_ok(acc@, buf@, cnt@, sh, bcap as int, pend, *w, xs, r0, k + lim),
            rows_fast(*w, xs, r0, k + lim),
            acc@.len() == old(acc)@.len(),
            buf@.len() == old(buf)@.len(),
            cnt@.len() == old(cnt)@.len(),
            forall|bb: int| 0 <= bb < 64 ==> (#[trigger] bit(m, bb) <==> (lim <= bb && bit(mask, bb))),
        decreases 64 - lim,
    {
        let (p, rest) = pop_lowest(m);
        proof {
            assert(lim <= p);
            assert forall|j: int| k + lim <= j < k + p implies !qual_of(w.lo as int, w.hi as int, #[trigger] xs[j]) by {
                assert(!bit(m, j - k));
            }
            lemma_bk_skip(acc@, buf@, cnt@, sh, bcap as int, pend, *w, xs, r0, k + lim, k + p);
        }
        let j = k + p as usize;
        let e = ent[p as usize];
        proof {
            let jj = j as int;
            assert(bit(mask, p as int));
            assert(qual_of(w.lo as int, w.hi as int, xs[jj]));
            lemma_and_zero_bit(bad, mask, p as int);
            assert(ent_ok(*c, *w, k + p, e, bit(bad, p as int)));
            lemma_row_codes(*c, *w, b as int, jj, kofs, bp, dd);
            lemma_top8(e);
            vstd::arithmetic::power2::lemma_pow2_pos(w.qs as nat);
            assert(rev_of(xs[jj]) / (pow2(w.qs as nat) as int) >= 0) by (nonlinear_arith)
                requires rev_of(xs[jj]) > 0, pow2(w.qs as nat) > 0;
            assert(qv_of(xs[jj], w.qs as nat) >= 1);
            assert(key_of(xs[jj]) == kr(w.kmin + es(e)));
            assert(fast_row(w.lo as int, w.hi as int, xs[jj]));
        }
        let t = (e & 0xFF_FFFFu32) as usize;
        let u = e >> 24u32;
        if bcap == 0 {
            let cur = acc[t] as u32;
            let nw = cur + u;
            let nv: u8 = if nw > 255 { 255 } else { nw as u8 };
            proof {
                lemma_bk_direct(acc@, buf@, cnt@, sh, bcap as int, pend, *w, xs, r0, j as int, e, nv);
            }
            put(acc, t, nv);
        } else {
            let bk = ((t as u32) >> sh) as usize;
            proof {
                assert(bko(es(e), sh) == bk);
                assert(bk < cnt@.len());
                assert(pend[bk as int].len() == cnt@[bk as int]);
            }
            if cnt[bk] == bcap {
                let ghost p0 = pend;
                flush(acc, buf, cnt, sh, bcap, bk, Ghost(p0), Ghost(*w), Ghost(xs), Ghost(r0), Ghost(j as int));
                proof {
                    pend = p0.update(bk as int, Seq::<u32>::empty());
                }
            }
            let pos = cnt[bk];
            proof {
                assert(buf@.len() == buf.len());
                lemma_slot_index(bk as int, pos as int, cnt@.len() as int, bcap as int);
                lemma_bk_push(acc@, buf@, cnt@, sh, bcap as int, pend, *w, xs, r0, j as int, e);
                pend = pend.update(bk as int, pend[bk as int].push(e));
            }
            put(buf, bk * bcap + pos, e);
            put(cnt, bk, pos + 1);
        }
        let ghost m0 = m;
        m = rest;
        proof {
            lim = p + 1;
            assert forall|bb: int| 0 <= bb < 64 implies (#[trigger] bit(m, bb) <==> (lim <= bb && bit(mask, bb))) by {
                assert(bit(m0, bb) <==> (lim - 1 <= bb && bit(mask, bb)));
            }
        }
    }
    proof {
        assert forall|j: int| k + lim <= j < k + 64 implies !qual_of(w.lo as int, w.hi as int, #[trigger] xs[j]) by {
            assert(!bit(0u64, j - k)) by { lemma_no_bit_of_zero(j - k); }
            assert(bit(m, j - k) <==> (lim <= j - k && bit(mask, j - k)));
        }
        lemma_bk_skip(acc@, buf@, cnt@, sh, bcap as int, pend, *w, xs, r0, k + lim, k + 64);
    }
    (true, Ghost(pend))
}

/// The entries of bucket `b0` into their slot bytes; the bucket is then empty.
pub fn flush(acc: &mut Vec<u8>, buf: &Vec<u32>, cnt: &mut Vec<usize>, sh: u32, bcap: usize, b0: usize,
    Ghost(pend): Ghost<Seq<Seq<u32>>>, Ghost(w): Ghost<Win>, Ghost(xs): Ghost<Seq<Row>>, Ghost(r0): Ghost<int>,
    Ghost(r): Ghost<int>)
    requires
        bk_ok(old(acc)@, buf@, old(cnt)@, sh, bcap as int, pend, w, xs, r0, r),
        b0 < old(cnt)@.len(),
    ensures
        bk_ok(final(acc)@, buf@, final(cnt)@, sh, bcap as int, pend.update(b0 as int, Seq::<u32>::empty()), w, xs, r0, r),
        final(cnt)@ == old(cnt)@.update(b0 as int, 0usize),
        final(acc)@.len() == old(acc)@.len(),
    no_unwind
{
    let n = cnt[b0];
    let ghost s = pend[b0 as int];
    let ghost acc0 = acc@;
    proof {
        assert(buf@.len() == buf.len());
        assert(s.len() == n && n <= bcap);
        lemma_slot_base(b0 as int, cnt@.len() as int, bcap as int);
        assert(s.subrange(0, n as int) =~= s);
        assert forall|t: int| 0 <= t < w.cap && bko(t, sh) == b0 implies
            sat(#[trigger] acc@[t] as int + psum(s.subrange(0, n as int), t)) == sat(gq(w, xs, r0, r, t)) by {
            assert(slot_ok(acc0, pend, sh, w, xs, r0, r, t));
        }
    }
    let base = b0 * bcap;
    proof {
        assert forall|ii: int| 0 <= ii < n implies buf@[base + ii] == #[trigger] s[ii] by {
            assert(buf@[b0 * bcap + ii] == pend[b0 as int][ii]);
        }
    }
    let mut i: usize = 0;
    while i < n
        invariant
            bk_ok(acc0, buf@, cnt@, sh, bcap as int, pend, w, xs, r0, r),
            b0 < cnt@.len(),
            n == cnt@[b0 as int], s == pend[b0 as int], s.len() == n,
            base == b0 * bcap,
            base + n <= buf@.len(), buf@.len() <= usize::MAX,
            forall|ii: int| 0 <= ii < n ==> buf@[base + ii] == #[trigger] s[ii],
            i <= n,
            acc@.len() == acc0.len(),
            forall|t: int| 0 <= t < w.cap && bko(t, sh) != b0 ==> #[trigger] acc@[t] == acc0[t],
            forall|t: int| 0 <= t < w.cap && bko(t, sh) == b0 ==>
                sat(#[trigger] acc@[t] as int + psum(s.subrange(i as int, n as int), t)) == sat(gq(w, xs, r0, r, t)),
        decreases n - i,
    {
        let e = buf[base + i];
        proof {
            assert(e == s[i as int]);
            assert(0 <= es(e) < w.cap && bko(es(e), sh) == b0);
            lemma_top8(e);
        }
        let t = (e & 0xFF_FFFFu32) as usize;
        let u = e >> 24u32;
        let cur = acc[t] as u32;
        let nw = cur + u;
        let nv: u8 = if nw > 255 { 255 } else { nw as u8 };
        let ghost a1 = acc@;
        put(acc, t, nv);
        proof {
            assert(s[i as int] == e);
            assert forall|tt: int| 0 <= tt < w.cap && bko(tt, sh) == b0 implies
                sat(#[trigger] acc@[tt] as int + psum(s.subrange(i + 1, n as int), tt)) == sat(gq(w, xs, r0, r, tt)) by {
                lemma_psum_skip(s, i as int, tt);
                lemma_psum_nonneg(s.subrange(i + 1, n as int), tt);
                if tt == t {
                    lemma_sat_add(a1[tt] as int + eu(e), psum(s.subrange(i + 1, n as int), tt));
                }
            }
        }
        i = i + 1;
    }
    let ghost cnt0 = cnt@;
    put(cnt, b0, 0);
    proof {
        let pend2 = pend.update(b0 as int, Seq::<u32>::empty());
        assert forall|b: int| 0 <= b < cnt@.len() implies (#[trigger] pend2[b]).len() == cnt@[b] && cnt@[b] <= bcap by {
            if b != b0 {
                assert(pend2[b] == pend[b]);
                assert(pend[b].len() == cnt0[b] && cnt0[b] <= bcap);
            }
        }
        assert forall|b: int, ii: int| 0 <= b < cnt@.len() && 0 <= ii < cnt@[b] implies
            buf@[b * bcap + ii] == #[trigger] pend2[b][ii] && 0 <= es(pend2[b][ii]) < w.cap && bko(es(pend2[b][ii]), sh) == b by {
            assert(b != b0);
            assert(pend2[b] == pend[b]);
            assert(pend[b].len() == cnt0[b]);
            assert(buf@[b * bcap + ii] == pend[b][ii]);
        }
        assert(bufs_ok(buf@, cnt@, sh, bcap as int, pend2, w));
        assert forall|t: int| 0 <= t < w.cap implies #[trigger] slot_ok(acc@, pend2, sh, w, xs, r0, r, t) by {
            assert(slot_ok(acc0, pend, sh, w, xs, r0, r, t));
            if bko(t, sh) == b0 {
                assert(s.subrange(n as int, n as int) =~= Seq::<u32>::empty());
                assert(pend2[b0 as int] =~= Seq::<u32>::empty());
            }
        }
    }
}

/// Every bucket into the slot bytes.
pub fn flush_all(acc: &mut Vec<u8>, buf: &Vec<u32>, cnt: &mut Vec<usize>, sh: u32, bcap: usize,
    Ghost(pend): Ghost<Seq<Seq<u32>>>, Ghost(w): Ghost<Win>, Ghost(xs): Ghost<Seq<Row>>, Ghost(r0): Ghost<int>,
    Ghost(r): Ghost<int>)
    requires bk_ok(old(acc)@, buf@, old(cnt)@, sh, bcap as int, pend, w, xs, r0, r),
    ensures
        acc_ok(final(acc)@, w, xs, r0, r),
        final(acc)@.len() == old(acc)@.len(),
    no_unwind
{
    let ghost mut pend = pend;
    let nbk = cnt.len();
    let mut b: usize = 0;
    while b < nbk
        invariant
            nbk == cnt@.len(),
            b <= nbk,
            bk_ok(acc@, buf@, cnt@, sh, bcap as int, pend, w, xs, r0, r),
            forall|bb: int| 0 <= bb < b ==> #[trigger] cnt@[bb] == 0,
            acc@.len() == old(acc)@.len(),
        decreases nbk - b,
    {
        let ghost c0 = cnt@;
        flush(acc, buf, cnt, sh, bcap, b, Ghost(pend), Ghost(w), Ghost(xs), Ghost(r0), Ghost(r));
        proof {
            pend = pend.update(b as int, Seq::<u32>::empty());
            assert forall|bb: int| 0 <= bb < b + 1 implies #[trigger] cnt@[bb] == 0 by {
                if bb < b { assert(c0[bb] == 0); }
            }
        }
        b = b + 1;
    }
    proof {
        lemma_bk_done(acc@, buf@, cnt@, sh, bcap as int, pend, w, xs, r0, r);
    }
}

/// The rows of block `b` (`[rs(b), rs(b + 1))`).
pub fn block_pass(c: &Li, w: &Win, acc: &mut Vec<u8>, buf: &mut Vec<u32>, cnt: &mut Vec<usize>, sh: u32, bcap: usize,
    b: usize, Ghost(r0): Ghost<int>, Ghost(pend): Ghost<Seq<Seq<u32>>>) -> (r: (bool, Ghost<Seq<Seq<u32>>>))
    requires
        kern_ok(*c, *w),
        b < c.nb,
        0 <= r0 <= rs(*c, b as int),
        bk_ok(old(acc)@, old(buf)@, old(cnt)@, sh, bcap as int, pend, *w, xs_of(*c), r0, rs(*c, b as int)),
        rows_fast(*w, xs_of(*c), r0, rs(*c, b as int)),
    ensures
        r.0 ==> bk_ok(final(acc)@, final(buf)@, final(cnt)@, sh, bcap as int, r.1@, *w, xs_of(*c), r0, rs(*c, b + 1))
            && rows_fast(*w, xs_of(*c), r0, rs(*c, b + 1)),
        final(acc)@.len() == old(acc)@.len(),
        final(buf)@.len() == old(buf)@.len(),
        final(cnt)@.len() == old(cnt)@.len(),
    no_unwind
{
    let ghost xs = xs_of(*c);
    let ghost mut pend = pend;
    let start = row_start(c, b);
    let end = row_start(c, b + 1);
    proof {
        lemma_rs_mono(*c, b as int, b + 1);
    }
    let sb = c.ship_base[b];
    let sz = c.ship_zmax[b];
    if sb > w.hi || sz < w.lo {
        // the zone map: every shipdate of the block is in [sb, sz], outside the window
        proof {
            assert forall|j: int| start <= j < end implies !qual_of(w.lo as int, w.hi as int, #[trigger] xs[j]) by {
                lemma_block_row(*c, b as int, j);
                lemma_hit_row(*c, w.lo as int, w.hi as int, j, supp_v(*c, j));
                assert(ship_v(*c, j) <= c.ship_zmax@[j / c.bs as int]);
                assert(ship_v(*c, j) >= c.ship_base@[b as int]);
            }
            lemma_bk_skip(acc@, buf@, cnt@, sh, bcap as int, pend, *w, xs, r0, start as int, end as int);
        }
        return (true, Ghost(pend));
    }
    let bk = c.supp_base[b];
    let bp = c.price_base[b];
    let bd = c.disc_base[b];
    let kd = bk as i128 - w.kmin as i128;
    if !(0 <= bp && bp <= 0x1_0000_0000 && 0 <= bd && bd <= 0x100 && -0x1_0000_0000 <= kd && kd <= 0x1_0000_0000) {
        return (false, Ghost(pend));
    }
    let kofs = kd as i64;
    let dd = 100 - bd;
    let sl = clamp16_exec(w.lo as i128 - sb as i128);
    let sh16 = clamp16_exec(w.hi as i128 - sb as i128 + 1);
    let mut k = start;
    while end - k >= 64
        invariant
            kern_ok(*c, *w),
            xs == xs_of(*c),
            b < c.nb,
            start == rs(*c, b as int), end == rs(*c, b + 1),
            start <= k <= end <= c.n,
            0 <= r0 <= start,
            blk_ok(*c, *w, b as int, kofs, bp, dd),
            sb == c.ship_base@[b as int],
            sl as int == clamp16(w.lo - sb),
            sh16 as int == clamp16(w.hi - sb + 1),
            bk_ok(acc@, buf@, cnt@, sh, bcap as int, pend, *w, xs, r0, k as int),
            rows_fast(*w, xs, r0, k as int),
            acc@.len() == old(acc)@.len(),
            buf@.len() == old(buf)@.len(),
            cnt@.len() == old(cnt)@.len(),
        decreases end - k,
    {
        let (ok, Ghost(p2)) = chunk64(c, w, acc, buf, cnt, sh, bcap, k, b, sl, sh16, kofs, bp, dd,
            Ghost(r0), Ghost(sb as int), Ghost(pend));
        if !ok {
            return (false, Ghost(pend));
        }
        proof {
            pend = p2;
        }
        k = k + 64;
    }
    while k < end
        invariant
            kern_ok(*c, *w),
            xs == xs_of(*c),
            b < c.nb,
            start == rs(*c, b as int), end == rs(*c, b + 1),
            start <= k <= end <= c.n,
            0 <= r0 <= start,
            blk_ok(*c, *w, b as int, kofs, bp, dd),
            sb == c.ship_base@[b as int],
            sl as int == clamp16(w.lo - sb),
            sh16 as int == clamp16(w.hi - sb + 1),
            bk_ok(acc@, buf@, cnt@, sh, bcap as int, pend, *w, xs, r0, k as int),
            rows_fast(*w, xs, r0, k as int),
            acc@.len() == old(acc)@.len(),
            buf@.len() == old(buf)@.len(),
            cnt@.len() == old(cnt)@.len(),
        decreases end - k,
    {
        let cs = c.ship[k] as u32;
        proof {
            lemma_row_codes(*c, *w, b as int, k as int, kofs, bp, dd);
        }
        if sl <= cs && cs < sh16 {
            let pv = bp + c.price[k] as i64;
            let dv = dd - c.disc[k] as i64;
            let v = pv * dv;
            if v <= 0 {
                return (false, Ghost(pend));
            }
            let vu = v as u64;
            proof {
                vstd::bits::lemma_u64_shr_is_div(vu, w.qs);
                vstd::arithmetic::power2::lemma_pow2_pos(w.qs as nat);
                assert(vu as nat / pow2(w.qs as nat) <= vu) by (nonlinear_arith)
                    requires pow2(w.qs as nat) >= 1;
            }
            let q = (vu >> w.qs) + 1;
            let q8: u32 = if q > 255 { 255 } else { q as u32 };
            let t = (kofs + c.supp[k] as i64) as u32;
            let e = t | (q8 << 24u32);
            proof {
                lemma_pack24(t, q8);
                let kk = k as int;
                assert(q == qv_of(xs[kk], w.qs as nat));
                assert(key_of(xs[kk]) == kr(w.kmin + es(e)));
                assert(fast_row(w.lo as int, w.hi as int, xs[kk]));
            }
            let tu = t as usize;
            let cur = acc[tu] as u32;
            let nw = cur + q8;
            let nv: u8 = if nw > 255 { 255 } else { nw as u8 };
            proof {
                lemma_bk_direct(acc@, buf@, cnt@, sh, bcap as int, pend, *w, xs, r0, k as int, e, nv);
            }
            put(acc, tu, nv);
        } else {
            proof {
                lemma_bk_skip(acc@, buf@, cnt@, sh, bcap as int, pend, *w, xs, r0, k as int, k + 1);
            }
        }
        k = k + 1;
    }
    (true, Ghost(pend))
}

} // verus!
