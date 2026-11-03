//! The partsupp scan of one row range `lo .. hi` (rows sorted by ps_partkey): one pass emits the range's groups
//! (`groups::groups_ok`), its SUM total and absolute mass. A row qualifies when its supplier key's flag byte is
//! set (`supp::flags_ok`). Rows go a chunk of at most `CHUNK_ROWS` at a time: `chunk_mask` builds the chunk's
//! qualification mask without a branch per row (the flag index is the key's code plus the frame-of-reference group's
//! clamped offset, wrapped to `u64` so that one compare sends every out-of-range key to the zero sentinel; codes are
//! read through a per-word subslice and the index is clamped to the flag array's last slot, so the compiled loop has
//! no bounds checks), optionally touching the payload cache lines of each word first (`touch`: overlaps their loads
//! with the mask work on few threads), then `take_chunk` visits only the set bits (`common::lowbit::low_bit`) with
//! the scan state in locals (`Acc`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::numeric::{abs, pow10};
use crate::link::expr::ival;
use crate::gendb_entry::parallel::WorkerTask;
use super::tables::*;
use super::nf::*;
use super::rows::*;
use super::groups::*;
use super::supp::*;
use super::common::lowbit::{bit_at, low_bit};
use super::bitmap::{bm_ok, bm_bit};

verus! {

pub const MAXM: u128 = 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff;
/// Clamp of a group's supplier-key offset: codes are below 2^32 and the flag range below 2^40, so beyond
/// +-2^40 no row of the group can hit the range.
pub const OFF_LIM: i64 = 0x100_0000_0000;
/// Largest flag range the scan accepts.
pub const RANGE_LIM: usize = 0x1000_0000;

/// What the scan of rows `lo .. hi` returns when it succeeds.
pub open spec fn scan_ok(t: Tabs, name: Seq<u8>, lo: int, hi: int, keys: Seq<i64>, sums: Seq<i128>, len: int,
    total: i128, mass: u128, lb: i128) -> bool
{
    &&& groups_ok(t, name, lo, hi, keys, sums, len, lb)
    &&& total as int == tsum(t, name, lo, hi)
    &&& mass as int == tabs(t, name, lo, hi)
    &&& mass <= MAXM
}

/// The facts the scan needs: the handles, the flags and sorted keys.
pub open spec fn scan_env(c: PSCols, fl: Seq<u8>, smin: i64, range: usize, t: Tabs, name: Seq<u8>) -> bool {
    &&& pscols_ok(c, t.ps)
    &&& tabs_typed(t)
    &&& flags_ok(t, name, fl, smin as int, range as int)
    &&& range < RANGE_LIM
    &&& sorted_rows(t, 0, t.ps.len() as int)
}

/// Row `r`'s values from the handles.
proof fn lemma_row_vals(c: PSCols, t: Tabs, r: int)
    requires pscols_ok(c, t.ps), tabs_typed(t), 0 <= r < c.n,
    ensures
        rkey(t, r) == fv32(c.key_c@, c.key_b@, c.bs as int, r),
        rval(t, r) == fv32(c.cost_c@, c.cost_b@, c.bs as int, r) * fv16(c.qty_c@, c.qty_b@, c.bs as int, r),
        ival(t.ps[r][1]) == fv32(c.supp_c@, c.supp_b@, c.bs as int, r),
        t.ps[r][1] == Val::Int(fv32(c.supp_c@, c.supp_b@, c.bs as int, r)),
        i64r(fv32(c.key_c@, c.key_b@, c.bs as int, r)),
        i64r(fv16(c.qty_c@, c.qty_b@, c.bs as int, r)),
        abs(fv32(c.cost_c@, c.cost_b@, c.bs as int, r)) < pow10(15),
        abs(fv32(c.cost_c@, c.cost_b@, c.bs as int, r)) < 1000000000000000,
        0 <= r / (c.bs as int) < c.ng,
{
    assert(pow10(15) == 1000000000000000) by (compute);
    assert(ps_row_ok(c, t.ps[r], r));
    lemma_grp_bound(c.n as int, c.bs as int, c.ng as int, r);
    let cost = fv32(c.cost_c@, c.cost_b@, c.bs as int, r);
    let qty = fv16(c.qty_c@, c.qty_b@, c.bs as int, r);
    assert(cost * qty == qty * cost) by (nonlinear_arith);
}

/// `|cost * qty|` of a row fits easily in `i128` (below `2^113`).
proof fn lemma_val_bound(cost: int, qty: int)
    requires abs(cost) < pow10(15), i64r(qty),
    ensures abs(cost * qty) < 0x2_0000_0000_0000_0000_0000_0000_0000,
{
    assert(pow10(15) == 1000000000000000) by (compute);
    let (a, b) = (abs(cost), abs(qty));
    assert(abs(cost * qty) == a * b) by (nonlinear_arith) requires a == abs(cost), b == abs(qty);
    assert(a * b <= 1000000000000000 * 0x8000_0000_0000_0000) by (nonlinear_arith)
        requires 0 <= a < 1000000000000000, 0 <= b <= 0x8000_0000_0000_0000;
}

/// The flag lookup of row `r` decides whether it qualifies.
proof fn lemma_flag(c: PSCols, fl: Seq<u8>, smin: i64, range: usize, t: Tabs, name: Seq<u8>, r: int, off: int, o: int, ix: int)
    requires
        scan_env(c, fl, smin, range, t, name), 0 <= r < c.n,
        o == c.supp_b@[r / (c.bs as int)] - smin,
        off == (if o < -OFF_LIM { -OFF_LIM as int } else if o > OFF_LIM { OFF_LIM as int } else { o }),
        ix == (if 0 <= off + c.supp_c@[r] < range { off + c.supp_c@[r] } else { range as int }),
    ensures 0 <= ix <= range, (fl[ix] != 0) == rowq(t, name, r),
{
    lemma_row_vals(c, t, r);
    let sv = fv32(c.supp_c@, c.supp_b@, c.bs as int, r);
    assert(sv - smin == o + c.supp_c@[r]);
    if 0 <= off + c.supp_c@[r] < range {
        // In range: the clamp did not apply (a clamped offset puts every code out of range).
        assert(off == o);
        assert(fl[ix] != 0 <==> sq(t, name, Val::Int(smin + ix)));
    } else {
        if sq(t, name, Val::Int(sv)) {
            assert(smin <= sv < smin + range);
        }
    }
}

/// Scan outcomes: the range's groups are in the buffers; the buffers were too small (smaller than the range);
/// the range's absolute mass exceeds `i128`.
pub const SCAN_OK: u8 = 0;
pub const SCAN_FULL: u8 = 1;
pub const SCAN_OVER: u8 = 2;

/// Rows per qualification mask chunk (64 rows per mask word).
pub const CHUNK_ROWS: usize = 4096;
/// Mask words per chunk: 64 words of 64 rows, and one spare word (`chunk_mask` keeps its cache-line touches there).
pub const CHUNK_WORDS: usize = 65;

/// The scalar state of a range scan: the closed groups `0 .. len` (in the group buffers), the open run
/// `(cur, acc)` (key of row `cur_row`), and the total and mass so far.
#[derive(Clone, Copy)]
pub struct Acc {
    pub len: usize,
    pub have: bool,
    pub cur: i64,
    pub acc: i128,
    pub total: i128,
    pub mass: u128,
    pub cur_row: Ghost<int>,
}

/// The scan state after rows `lo .. r` (group buffers `keys/sums` of `cap` slots).
pub open spec fn acc_inv(keys: Seq<i64>, sums: Seq<i128>, a: Acc, lb: i128, t: Tabs, name: Seq<u8>, lo: int, r: int,
    cap: int) -> bool
{
    &&& keys.len() == cap && sums.len() == cap
    &&& a.len <= cap
    &&& a.total as int == tsum(t, name, lo, r)
    &&& a.mass as int == tabs(t, name, lo, r)
    &&& a.mass <= MAXM
    &&& a.have ==> a.len < r - lo
    &&& scan_inv(t, name, lo, r, keys, sums, a.len as int, a.have, a.cur, a.acc, a.cur_row@, lb)
}


/// Words `0 .. nw` of `mask` flag the qualifying rows of `r0 .. e`: bit `i` of word `w` is row `r0 + 64 w + i`.
pub open spec fn mask_ok(mask: Seq<u64>, nw: int, r0: int, e: int, t: Tabs, name: Seq<u8>) -> bool {
    &&& 0 <= nw <= mask.len()
    &&& forall|w: int, i: int| 0 <= w < nw && 0 <= i < 64 ==>
            #[trigger] bit_at(mask[w], i) == (r0 + 64 * w + i < e && rowq(t, name, r0 + 64 * w + i))
}

/// Setting bit `s` (`f` is 0 or 1) changes only bit `s`.
proof fn lemma_bit_set(m: u64, f: u64, s: u64, i: u64)
    requires f <= 1, s < 64, i < 64,
    ensures
        i == s ==> (((m | (f << s)) >> i) & 1u64 == 1u64) == ((((m >> i) & 1u64) == 1u64) || f == 1),
        i != s ==> ((m | (f << s)) >> i) & 1u64 == (m >> i) & 1u64,
{
    assert(i == s ==> (((m | (f << s)) >> i) & 1u64 == 1u64) == ((((m >> i) & 1u64) == 1u64) || f == 1)) by (bit_vector)
        requires f <= 1, s < 64, i < 64;
    assert(i != s ==> ((m | (f << s)) >> i) & 1u64 == (m >> i) & 1u64) by (bit_vector)
        requires f <= 1, s < 64, i < 64;
}

/// Clearing set bit `s` changes only bit `s`, and lowers the word.
proof fn lemma_bit_clear(m: u64, s: u64, i: u64)
    requires s < 64, i < 64, (m >> s) & 1u64 == 1u64,
    ensures
        i == s ==> ((m ^ (1u64 << s)) >> i) & 1u64 == 0u64,
        i != s ==> ((m ^ (1u64 << s)) >> i) & 1u64 == (m >> i) & 1u64,
        (m ^ (1u64 << s)) < m,
{
    assert(i == s ==> ((m ^ (1u64 << s)) >> i) & 1u64 == 0u64) by (bit_vector)
        requires s < 64, i < 64, (m >> s) & 1u64 == 1u64;
    assert(i != s ==> ((m ^ (1u64 << s)) >> i) & 1u64 == (m >> i) & 1u64) by (bit_vector)
        requires s < 64, i < 64;
    assert((m ^ (1u64 << s)) < m) by (bit_vector)
        requires s < 64, (m >> s) & 1u64 == 1u64;
}

/// No bit of zero is set.
proof fn lemma_bit_zero(i: u64)
    requires i < 64,
    ensures (0u64 >> i) & 1u64 == 0u64,
{
    assert((0u64 >> i) & 1u64 == 0u64) by (bit_vector);
}

/// Rows `a .. b` that do not qualify change nothing.
proof fn lemma_skip_rows(keys: Seq<i64>, sums: Seq<i128>, st: Acc, lb: i128, t: Tabs, name: Seq<u8>, lo: int, a: int, b: int,
    cap: int)
    requires
        lo <= a <= b, acc_inv(keys, sums, st, lb, t, name, lo, a, cap),
        forall|r: int| a <= r < b ==> !#[trigger] rowq(t, name, r),
    ensures acc_inv(keys, sums, st, lb, t, name, lo, b, cap),
    decreases b - a,
{
    if a < b {
        assert(!rowq(t, name, a));
        lemma_step_skip(t, name, lo, a, keys, sums, st.len as int, st.have, st.cur, st.acc, st.cur_row@, lb);
        lemma_skip_rows(keys, sums, st, lb, t, name, lo, a + 1, b, cap);
    }
}

/// A code plus a clamped offset, wrapped to `u64`, is below `rng < 2^63` exactly when the true sum lies in
/// `0 .. rng` (a negative sum wraps to at least `2^64 - 2^40`).
proof fn lemma_wrap_index(code: u64, off: i64, u: u64, rng: u64)
    requires
        u == code.wrapping_add_signed(off), code < 0x1_0000_0000, -OFF_LIM <= off <= OFF_LIM,
        rng < 0x8000_0000_0000_0000,
    ensures (u < rng) == (0 <= code + off && code + off < rng), u < rng ==> u == code + off,
{
}

/// The number of mask words of a chunk is at most 64 (`CHUNK_ROWS / 64`).
proof fn lemma_chunk_words(len: int)
    requires 0 <= len <= CHUNK_ROWS,
    ensures (len + 63) / 64 <= 64,
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered(len + 63, 4159, 64);
    assert(4159int / 64 == 64) by (compute);
}

/// The qualification mask of rows `r0 .. e` (inside frame-of-reference group `g`, at most `CHUNK_ROWS` rows) into
/// `mask[0 .. nw]`, `nw = ceil((e - r0) / 64)`. Branch-free per row; each word's supplier codes are read through a
/// subslice and the flag index is clamped to the flag array's last slot, so the compiled loop has no bounds check.
/// With `touch`, each word first reads one value per cache line of its rows' cost, quantity and key columns (folded
/// into the spare last mask word), so that those lines load while the mask is computed and `take_chunk` finds them
/// in cache; this helps a single thread and only adds traffic when many threads share the memory bandwidth.
#[inline(never)]
fn chunk_mask(c: &PSCols, fl: &Vec<u8>, smin: i64, range: usize, supp_c: &[u32], off: i64, r0: usize, e: usize,
    mask: &mut Vec<u64>, touch: bool, Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>, Ghost(g): Ghost<int>, Ghost(o): Ghost<int>)
    -> (nw: usize)
    requires
        scan_env(*c, fl@, smin, range, t, name),
        r0 <= e <= c.n, e - r0 <= CHUNK_ROWS, old(mask)@.len() == CHUNK_WORDS, supp_c@ == c.supp_c@,
        0 <= g < c.ng, g * c.bs <= r0, e <= g * c.bs + c.bs,
        o == c.supp_b@[g] - smin,
        off as int == (if o < -OFF_LIM { -OFF_LIM as int } else if o > OFF_LIM { OFF_LIM as int } else { o }),
    ensures
        final(mask)@.len() == old(mask)@.len(),
        nw as int == (e - r0 + 63) / 64,
        mask_ok(final(mask)@, nw as int, r0 as int, e as int, t, name),
    no_unwind
{
    let last: usize = fl.len() - 1;
    let rng: u64 = last as u64;
    assert(last == range);
    let cost_c = c.cost_c;
    let qty_c = c.qty_c;
    let key_c = c.key_c;
    let krun = c.krun;
    let nw: usize = (e - r0 + 63) / 64;
    proof { lemma_chunk_words(e - r0); }
    let mut sink: u32 = 0;
    let mut w: usize = 0;
    while w < nw
        invariant
            scan_env(*c, fl@, smin, range, t, name),
            r0 <= e <= c.n, e - r0 <= CHUNK_ROWS, supp_c@ == c.supp_c@, rng == range, last == range,
            cost_c@ == c.cost_c@, qty_c@ == c.qty_c@, key_c@ == c.key_c@,
            mask@.len() == CHUNK_WORDS, nw as int == (e - r0 + 63) / 64, nw <= 64, w <= nw,
            0 <= g < c.ng, g * c.bs <= r0, e <= g * c.bs + c.bs,
            o == c.supp_b@[g] - smin,
            off as int == (if o < -OFF_LIM { -OFF_LIM as int } else if o > OFF_LIM { OFF_LIM as int } else { o }),
            forall|x: int, i: int| 0 <= x < w && 0 <= i < 64 ==>
                #[trigger] bit_at(mask@[x], i) == (r0 + 64 * x + i < e && rowq(t, name, r0 + 64 * x + i)),
        decreases nw - w,
    {
        let b0: usize = r0 + 64 * w;
        let b1: usize = if e - b0 > 64 { b0 + 64 } else { e };
        if touch {
            let mut k: usize = b0;
            while k < b1
                invariant b0 <= k <= b1 <= c.n, cost_c@.len() == c.n, key_c@.len() == c.n,
                decreases b1 - k,
            {
                sink = sink ^ cost_c[k] ^ (if krun { 0u32 } else { key_c[k] });
                k = if b1 - k > 16 { k + 16 } else { b1 };
            }
            let mut k: usize = b0;
            while k < b1
                invariant b0 <= k <= b1 <= c.n, qty_c@.len() == c.n,
                decreases b1 - k,
            {
                sink = sink ^ (qty_c[k] as u32);
                k = if b1 - k > 32 { k + 32 } else { b1 };
            }
        }
        let ws: &[u32] = supp_c.split_at(b0).1.split_at(b1 - b0).0;
        assert(ws@.len() == b1 - b0);
        assert(forall|i: int| 0 <= i < b1 - b0 ==> #[trigger] ws@[i] == supp_c@[b0 + i]);
        // `ws` has exactly `cnt` codes (`split_at`), so the compiled loop needs no bounds check on it.
        let cnt: usize = b1 - b0;
        let mut m: u64 = 0;
        let mut i: usize = 0;
        proof {
            assert forall|x: int| 0 <= x < 64 implies bit_at(m, x) == (x < i && rowq(t, name, b0 + x)) by {
                lemma_bit_zero(x as u64);
            }
        }
        while i < cnt
            invariant
                scan_env(*c, fl@, smin, range, t, name),
                r0 <= b0 <= b1 <= e <= c.n, b1 - b0 <= 64, cnt == b1 - b0, i <= cnt, supp_c@ == c.supp_c@, ws@.len() == cnt,
                rng == range, last == range,
                forall|x: int| 0 <= x < b1 - b0 ==> #[trigger] ws@[x] == supp_c@[b0 + x],
                0 <= g < c.ng, g * c.bs <= r0, e <= g * c.bs + c.bs,
                o == c.supp_b@[g] - smin,
                off as int == (if o < -OFF_LIM { -OFF_LIM as int } else if o > OFF_LIM { OFF_LIM as int } else { o }),
                forall|x: int| 0 <= x < 64 ==> bit_at(m, x) == (x < i && rowq(t, name, b0 + x)),
            decreases cnt - i,
        {
            let ghost j = b0 + i;
            proof {
                super::tables::lemma_in_group(c.bs as int, g, j);
                lemma_row_vals(*c, t, j);
                assert(ws@[i as int] == supp_c@[j]);
            }
            // One unsigned compare maps every key outside `smin .. smin + range` (a negative offset wraps to a
            // huge value) to the zero sentinel `fl[range]`, the flag array's last slot.
            let u: u64 = (ws[i] as u64).wrapping_add_signed(off);
            let ix: usize = if u < rng { u as usize } else { last };
            proof {
                lemma_wrap_index(supp_c@[j] as u64, off, u, rng);
                lemma_flag(*c, fl@, smin, range, t, name, j, off as int, o, ix as int);
            }
            let f: u64 = fl[ix] as u64;
            proof {
                assert(fl@[ix as int] <= 1);
                assert((f == 1) == rowq(t, name, j));
            }
            let s: u64 = i as u64;
            let ghost m0 = m;
            m = m | (f << s);
            proof {
                assert forall|x: int| 0 <= x < 64 implies bit_at(m, x) == (x < i + 1 && rowq(t, name, b0 + x)) by {
                    lemma_bit_set(m0, f, s, x as u64);
                    assert(bit_at(m0, x) == (x < i && rowq(t, name, b0 + x)));
                }
            }
            i = i + 1;
        }
        let ghost mk0 = mask@;
        crate::gendb_entry::work::put(mask, w, m);
        proof {
            assert forall|x: int, i: int| 0 <= x < w + 1 && 0 <= i < 64 implies
                #[trigger] bit_at(mask@[x], i) == (r0 + 64 * x + i < e && rowq(t, name, r0 + 64 * x + i)) by {
                if x < w {
                    assert(mask@[x] == mk0[x]);
                } else {
                    assert(mask@[x] == m);
                    assert(bit_at(m, i) == (i < cnt && rowq(t, name, b0 + i)));
                    assert(b0 + i == r0 + 64 * x + i);
                    if b0 + i >= b1 && b0 + i < e {
                        assert(b1 == b0 + 64);
                    }
                }
            }
        }
        w = w + 1;
    }
    // The touched values go to the spare last word (beyond the `nw <= 64` mask words), so the reads stay.
    let ghost mk1 = mask@;
    crate::gendb_entry::work::put(mask, CHUNK_WORDS - 1, sink as u64);
    proof {
        assert forall|x: int, i: int| 0 <= x < nw && 0 <= i < 64 implies
            #[trigger] bit_at(mask@[x], i) == (r0 + 64 * x + i < e && rowq(t, name, r0 + 64 * x + i)) by {
            assert(mask@[x] == mk1[x]);
        }
    }
    nw
}

/// Masking a word with the low `len` bits keeps exactly its bits below `len`.
proof fn lemma_low_mask(v: u64, len: u64, lm: u64, i: u64)
    requires
        1 <= len <= 64, i < 64,
        (len == 64 && lm == 0xffff_ffff_ffff_ffffu64) || (len < 64 && lm == sub(1u64 << len, 1u64)),
    ensures (((v & lm) >> i) & 1u64 == 1u64) == (i < len && ((v >> i) & 1u64 == 1u64)),
{
    assert((((v & lm) >> i) & 1u64 == 1u64) == (i < len && ((v >> i) & 1u64 == 1u64))) by (bit_vector)
        requires
            1 <= len <= 64, i < 64,
            (len == 64 && lm == 0xffff_ffff_ffff_ffffu64) || (len < 64 && lm == sub(1u64 << len, 1u64));
}

/// The two-word window `(x >> s) | (y << (64 - s))`: bit `i` is bit `i + s` of `x`, or bit `i + s - 64` of `y`.
proof fn lemma_shift_pair(x: u64, y: u64, s: u64, i: u64)
    requires 0 < s < 64, i < 64,
    ensures
        add(i, s) < 64 ==> (((((x >> s) | (y << sub(64u64, s))) >> i) & 1u64) == 1u64) == (((x >> add(i, s)) & 1u64) == 1u64),
        add(i, s) >= 64 ==> (((((x >> s) | (y << sub(64u64, s))) >> i) & 1u64) == 1u64)
            == (((y >> sub(add(i, s), 64u64)) & 1u64) == 1u64),
{
    assert(add(i, s) < 64 ==> (((((x >> s) | (y << sub(64u64, s))) >> i) & 1u64) == 1u64) == (((x >> add(i, s)) & 1u64) == 1u64))
        by (bit_vector) requires 0 < s < 64, i < 64;
    assert(add(i, s) >= 64 ==> (((((x >> s) | (y << sub(64u64, s))) >> i) & 1u64) == 1u64)
        == (((y >> sub(add(i, s), 64u64)) & 1u64) == 1u64))
        by (bit_vector) requires 0 < s < 64, i < 64;
}

/// One shifted word: bit `i` of `(x >> s) | 0` is bit `i + s` of `x` while `i + s < 64`.
proof fn lemma_shift_one(x: u64, s: u64, i: u64)
    requires s < 64, i < 64, add(i, s) < 64,
    ensures ((((x >> s) | 0u64) >> i) & 1u64 == 1u64) == (((x >> add(i, s)) & 1u64) == 1u64),
{
    assert(((((x >> s) | 0u64) >> i) & 1u64 == 1u64) == (((x >> add(i, s)) & 1u64) == 1u64)) by (bit_vector)
        requires s < 64, i < 64, add(i, s) < 64;
}

/// The `len` bits of a bitmap starting at bit `s` of word `x` (continuing into `y`): bit `i < len` of the result is
/// bit `i + s` of `x` (or bit `i + s - 64` of `y`), higher bits are clear. `y` is read only when the window crosses.
#[inline(always)]
fn window(x: u64, y: u64, s: u64, len: u64) -> (m: u64)
    requires s < 64, 1 <= len <= 64,
    ensures
        forall|i: int| 0 <= i < 64 ==> #[trigger] bit_at(m, i)
            == (i < len && (if i + s < 64 { bit_at(x, i + s) } else { bit_at(y, i + s - 64) })),
    no_unwind
{
    let cross = s > 0 && len > 64 - s;
    let hi: u64 = if cross { y << (64 - s) } else { 0 };
    let lm: u64 = if len == 64 {
        0xffff_ffff_ffff_ffffu64
    } else {
        assert(1u64 << len >= 1u64) by (bit_vector) requires len < 64;
        (1u64 << len) - 1
    };
    let v: u64 = (x >> s) | hi;
    let m = v & lm;
    proof {
        assert forall|i: int| 0 <= i < 64 implies #[trigger] bit_at(m, i)
            == (i < len && (if i + s < 64 { bit_at(x, i + s) } else { bit_at(y, i + s - 64) })) by {
            lemma_low_mask(v, len, lm, i as u64);
            if i < len {
                if cross {
                    lemma_shift_pair(x, y, s, i as u64);
                } else {
                    lemma_shift_one(x, s, i as u64);
                }
            }
        }
    }
    m
}

/// The qualification mask of rows `r0 .. e` (at most `CHUNK_ROWS` rows, inside frame-of-reference group `g`) into
/// `mask[0 .. nw]`, read from the qualifying-row bitmap `bm` (`bitmap::bm_ok`): each mask word is a 64-bit window of
/// the bitmap. With `touch`, each word first reads one value per cache line of its rows' cost and quantity (as
/// `chunk_mask` does).
#[inline(never)]
fn chunk_mask_bm(c: &PSCols, bm: &Vec<u64>, r0: usize, e: usize, mask: &mut Vec<u64>, touch: bool, Ghost(t): Ghost<Tabs>,
    Ghost(name): Ghost<Seq<u8>>) -> (nw: usize)
    requires
        bm_ok(bm@, c.n as int, t, name), c.cost_c@.len() == c.n, c.qty_c@.len() == c.n,
        r0 <= e <= c.n, e - r0 <= CHUNK_ROWS, old(mask)@.len() == CHUNK_WORDS,
    ensures
        final(mask)@.len() == old(mask)@.len(),
        nw as int == (e - r0 + 63) / 64,
        mask_ok(final(mask)@, nw as int, r0 as int, e as int, t, name),
    no_unwind
{
    let cost_c = c.cost_c;
    let qty_c = c.qty_c;
    let nw: usize = (e - r0 + 63) / 64;
    proof { lemma_chunk_words(e - r0); }
    let mut sink: u32 = 0;
    let mut w: usize = 0;
    while w < nw
        invariant
            bm_ok(bm@, c.n as int, t, name), cost_c@.len() == c.n, qty_c@.len() == c.n,
            r0 <= e <= c.n, e - r0 <= CHUNK_ROWS,
            mask@.len() == CHUNK_WORDS, nw as int == (e - r0 + 63) / 64, nw <= 64, w <= nw,
            forall|x: int, i: int| 0 <= x < w && 0 <= i < 64 ==>
                #[trigger] bit_at(mask@[x], i) == (r0 + 64 * x + i < e && rowq(t, name, r0 + 64 * x + i)),
        decreases nw - w,
    {
        let b0: usize = r0 + 64 * w;
        let b1: usize = if e - b0 > 64 { b0 + 64 } else { e };
        if touch {
            let mut k: usize = b0;
            while k < b1
                invariant b0 <= k <= b1 <= c.n, cost_c@.len() == c.n,
                decreases b1 - k,
            {
                sink = sink ^ cost_c[k];
                k = if b1 - k > 16 { k + 16 } else { b1 };
            }
            let mut k: usize = b0;
            while k < b1
                invariant b0 <= k <= b1 <= c.n, qty_c@.len() == c.n,
                decreases b1 - k,
            {
                sink = sink ^ (qty_c[k] as u32);
                k = if b1 - k > 32 { k + 32 } else { b1 };
            }
        }
        let len: usize = b1 - b0;
        let q: usize = b0 / 64;
        let s: usize = b0 % 64;
        let n = c.n;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b0 as int, 64);
            assert(q < bm@.len());
        }
        let x: u64 = bm[q];
        let cross = s > 0 && len > 64 - s;
        let y: u64 = if cross {
            proof {
                assert(b0 + 64 - s <= b1 - 1);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse((b0 + 64 - s) as int, 64, q + 1, 0);
            }
            bm[q + 1]
        } else {
            0
        };
        let m = window(x, y, s as u64, len as u64);
        proof {
            assert forall|i: int| 0 <= i < 64 implies bit_at(m, i) == (b0 + i < e && rowq(t, name, b0 + i)) by {
                if i < len {
                    let r = b0 + i;
                    assert(bm_bit(bm@, r) == rowq(t, name, r));
                    if i + s < 64 {
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(r, 64, q as int, s + i);
                    } else {
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(r, 64, q + 1, s + i - 64);
                        assert(cross);
                    }
                } else {
                    assert(b0 + i >= b1);
                    if b0 + i < e {
                        assert(b1 == b0 + 64);
                    }
                }
            }
        }
        let ghost mk0 = mask@;
        crate::gendb_entry::work::put(mask, w, m);
        proof {
            assert forall|x2: int, i: int| 0 <= x2 < w + 1 && 0 <= i < 64 implies
                #[trigger] bit_at(mask@[x2], i) == (r0 + 64 * x2 + i < e && rowq(t, name, r0 + 64 * x2 + i)) by {
                if x2 < w {
                    assert(mask@[x2] == mk0[x2]);
                } else {
                    assert(mask@[x2] == m);
                    assert(b0 + i == r0 + 64 * x2 + i);
                }
            }
        }
        w = w + 1;
    }
    let ghost mk1 = mask@;
    crate::gendb_entry::work::put(mask, CHUNK_WORDS - 1, sink as u64);
    proof {
        assert forall|x: int, i: int| 0 <= x < nw && 0 <= i < 64 implies
            #[trigger] bit_at(mask@[x], i) == (r0 + 64 * x + i < e && rowq(t, name, r0 + 64 * x + i)) by {
            assert(mask@[x] == mk1[x]);
        }
    }
    nw
}

/// Takes the qualifying rows of `r0 .. e` (flagged by `mask[0 .. ceil((e - r0) / 64)]`, inside frame-of-reference
/// group `g`) into the scan state `a0` of rows `lo .. r0`: visits only the set bits, state in locals.
#[inline(never)]
fn take_chunk(keys: &mut Vec<i64>, sums: &mut Vec<i128>, a0: Acc, lb: i128, mask: &Vec<u64>, r0: usize, e: usize,
    c: &PSCols, cb: i64, qb: i64, kb: i64, Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>, Ghost(lo): Ghost<int>,
    Ghost(hi): Ghost<int>, Ghost(cap): Ghost<int>, Ghost(g): Ghost<int>) -> (r: (Acc, u8))
    requires
        acc_inv(old(keys)@, old(sums)@, a0, lb, t, name, lo, r0 as int, cap),
        pscols_ok(*c, t.ps), tabs_typed(t),
        sorted_rows(t, 0, t.ps.len() as int),
        0 <= lo <= r0 <= e <= hi <= c.n, e - r0 <= CHUNK_ROWS,
        mask_ok(mask@, (e - r0 + 63) / 64, r0 as int, e as int, t, name),
        0 <= g < c.ng, g * c.bs <= r0, e <= g * c.bs + c.bs,
        cb == c.cost_b@[g], qb == c.qty_b@[g], kb == c.key_b@[g],
    ensures
        final(keys)@.len() == old(keys)@.len(), final(sums)@.len() == old(sums)@.len(),
        r.1 == SCAN_OK || r.1 == SCAN_FULL || r.1 == SCAN_OVER,
        r.1 == SCAN_OK ==> acc_inv(final(keys)@, final(sums)@, r.0, lb, t, name, lo, e as int, cap),
        r.1 == SCAN_FULL ==> cap < hi - lo,
        r.1 == SCAN_OVER ==> tabs(t, name, lo, hi) > MAXM,
    no_unwind
{
    let cost_c = c.cost_c;
    let qty_c = c.qty_c;
    let key_c = c.key_c;
    let mut a = a0;
    let nw: usize = (e - r0 + 63) / 64;
    let mut w: usize = 0;
    while w < nw
        invariant
            pscols_ok(*c, t.ps), tabs_typed(t), sorted_rows(t, 0, t.ps.len() as int),
            cost_c@ == c.cost_c@, qty_c@ == c.qty_c@, key_c@ == c.key_c@,
            0 <= lo <= r0 <= e <= hi <= c.n, nw as int == (e - r0 + 63) / 64, w <= nw,
            mask_ok(mask@, nw as int, r0 as int, e as int, t, name),
            0 <= g < c.ng, g * c.bs <= r0, e <= g * c.bs + c.bs,
            cb == c.cost_b@[g], qb == c.qty_b@[g], kb == c.key_b@[g],
            keys@.len() == old(keys)@.len(), sums@.len() == old(sums)@.len(),
            acc_inv(keys@, sums@, a, lb, t, name, lo, if r0 + 64 * w < e { r0 + 64 * w } else { e as int }, cap),
        decreases nw - w,
    {
        let base: usize = r0 + 64 * w;
        let wend: usize = if e - base > 64 { base + 64 } else { e };
        let mut m: u64 = mask[w];
        let mut p: usize = base;
        proof {
            assert forall|i: int| 0 <= i < 64 implies bit_at(m, i) == (p <= base + i < wend && rowq(t, name, base + i)) by {
                assert(bit_at(mask@[w as int], i) == (r0 + 64 * w + i < e && rowq(t, name, r0 + 64 * w + i)));
                if base + i >= wend && base + i < e {
                    assert(wend == base + 64);
                }
            }
        }
        while m != 0
            invariant
                pscols_ok(*c, t.ps), tabs_typed(t), sorted_rows(t, 0, t.ps.len() as int),
                cost_c@ == c.cost_c@, qty_c@ == c.qty_c@, key_c@ == c.key_c@,
                0 <= lo <= r0 <= base <= p <= wend <= e <= hi <= c.n, wend - base <= 64,
                0 <= g < c.ng, g * c.bs <= r0, e <= g * c.bs + c.bs,
                cb == c.cost_b@[g], qb == c.qty_b@[g], kb == c.key_b@[g],
                keys@.len() == old(keys)@.len(), sums@.len() == old(sums)@.len(),
                forall|i: int| 0 <= i < 64 ==> bit_at(m, i) == (p <= base + i < wend && rowq(t, name, base + i)),
                acc_inv(keys@, sums@, a, lb, t, name, lo, p as int, cap),
            decreases m,
        {
            let tz: u64 = low_bit(m);
            proof {
                assert(bit_at(m, tz as int));
                assert forall|x: int| p <= x < base + tz implies !#[trigger] rowq(t, name, x) by {
                    assert(!bit_at(m, x - base));
                    assert(base + (x - base) == x);
                }
                lemma_skip_rows(keys@, sums@, a, lb, t, name, lo, p as int, base + tz, cap);
            }
            let j: usize = base + tz as usize;
            proof {
                super::tables::lemma_in_group(c.bs as int, g, j as int);
                lemma_row_vals(*c, t, j as int);
            }
            let cost: i64 = cb + cost_c[j] as i64;
            let qty: i64 = qb + qty_c[j] as i64;
            proof { lemma_val_bound(cost as int, qty as int); }
            let v: i128 = cost as i128 * qty as i128;
            // The key: from the run layout (no key column read) or from the key column.
            let key: i64 = if c.krun {
                proof {
                    reveal(krun_ok);
                    assert(fv32(c.key_c@, c.key_b@, c.bs as int, j as int) == c.kfirst + j as int / 4);
                }
                c.kfirst + (j / 4) as i64
            } else {
                kb + key_c[j] as i64
            };
            assert(key as int == rkey(t, j as int));
            // Take row j (qualifying, key `key`, argument `v`).
            let av: u128 = if v < 0 { (-v) as u128 } else { v as u128 };
            let m2: u128 = a.mass + av;
            if m2 > MAXM {
                proof {
                    assert(tabs(t, name, lo, j + 1) == m2);
                    lemma_split(t, name, 0, lo, j + 1, hi);
                    lemma_bounds(t, name, 0, j + 1, hi);
                }
                return (a, SCAN_OVER);
            }
            proof {
                lemma_bounds(t, name, a.cur as int, lo, j + 1);
                lemma_bounds(t, name, key as int, lo, j + 1);
            }
            if a.have && key == a.cur {
                proof { lemma_step_same(t, name, lo, j as int, keys@, sums@, a.len as int, a.cur, a.acc, a.cur_row@, (a.acc + v) as i128, lb); }
                a.acc = a.acc + v;
            } else {
                let ghost keys0 = keys@;
                let ghost sums0 = sums@;
                let ghost a1 = a;
                let emit = a.have && a.acc > lb;
                if a.have {
                    // Sorted rows: the open run's key is not above this row's; it differs, so it is below.
                    assert(rkey(t, a.cur_row@) <= rkey(t, j as int));
                }
                if emit {
                    if a.len >= keys.len() {
                        return (a, SCAN_FULL);
                    }
                    let len = a.len;
                    crate::gendb_entry::work::put(keys, len, a.cur);
                    crate::gendb_entry::work::put(sums, len, a.acc);
                    a.len = len + 1;
                }
                proof {
                    lemma_step_new(t, name, lo, j as int, keys0, sums0, a1.len as int, a1.have, a1.cur, a1.acc, a1.cur_row@,
                        keys@, sums@, a.len as int, key, v, lb, emit);
                }
                a.cur = key;
                a.acc = v;
                a.have = true;
                a.cur_row = Ghost(j as int);
            }
            a.mass = m2;
            a.total = a.total + v;
            let ghost mb = m;
            m = m ^ (1u64 << tz);
            proof {
                assert forall|i: int| 0 <= i < 64 implies bit_at(m, i) == (j + 1 <= base + i < wend && rowq(t, name, base + i)) by {
                    lemma_bit_clear(mb, tz, i as u64);
                    assert(bit_at(mb, i) == (p <= base + i < wend && rowq(t, name, base + i)));
                    if i < tz {
                        assert(!bit_at(mb, i));
                    }
                }
                lemma_bit_clear(mb, tz, 0);
            }
            p = j + 1;
        }
        proof {
            assert forall|x: int| p <= x < wend implies !#[trigger] rowq(t, name, x) by {
                lemma_bit_zero((x - base) as u64);
                assert(!bit_at(m, x - base));
                assert(base + (x - base) == x);
            }
            lemma_skip_rows(keys@, sums@, a, lb, t, name, lo, p as int, wend as int, cap);
        }
        w = w + 1;
    }
    (a, SCAN_OK)
}

/// The scan of rows `lo .. hi` into the group buffers `keys/sums` (fresh: no group yet). Returns the final state and
/// the status. Rows are taken a chunk of at most `CHUNK_ROWS` at a time: a branch-free qualification mask
/// (`chunk_mask`), then only its set bits are visited (`take_chunk`).
pub fn scan_range(c: &PSCols, fl: &Vec<u8>, smin: i64, range: usize, lo: usize, hi: usize,
    keys: &mut Vec<i64>, sums: &mut Vec<i128>, lb: i128, mask: &mut Vec<u64>, touch: bool, bm: &Vec<u64>, use_bm: bool,
    Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>)
    -> (r: (Acc, u8))
    requires
        scan_env(*c, fl@, smin, range, t, name),
        use_bm ==> bm_ok(bm@, c.n as int, t, name),
        lo <= hi <= c.n,
        old(keys)@.len() == old(sums)@.len(),
        old(mask)@.len() == CHUNK_WORDS,
    ensures
        final(keys)@.len() == old(keys)@.len(),
        final(sums)@.len() == old(sums)@.len(),
        final(mask)@.len() == CHUNK_WORDS,
        r.1 == SCAN_OK || r.1 == SCAN_FULL || r.1 == SCAN_OVER,
        r.1 == SCAN_OK ==> r.0.len <= final(keys)@.len()
            && scan_ok(t, name, lo as int, hi as int, final(keys)@, final(sums)@, r.0.len as int, r.0.total, r.0.mass, lb),
        r.1 == SCAN_FULL ==> old(keys)@.len() < hi - lo,
        r.1 == SCAN_OVER ==> tabs(t, name, lo as int, hi as int) > MAXM,
    no_unwind
{
    let bs = c.bs;
    let ghost cap = keys@.len() as int;
    let mut a = Acc { len: 0, have: false, cur: 0, acc: 0, total: 0, mass: 0, cur_row: Ghost(0) };
    proof { lemma_scan_start(t, name, lo as int, keys@, sums@, lb); }
    let supp_c = c.supp_c;
    let mut r = lo;
    while r < hi
        invariant
            scan_env(*c, fl@, smin, range, t, name),
            use_bm ==> bm_ok(bm@, c.n as int, t, name),
            lo <= r <= hi <= c.n, bs == c.bs, supp_c@ == c.supp_c@,
            keys@.len() == cap, sums@.len() == cap, mask@.len() == CHUNK_WORDS,
            acc_inv(keys@, sums@, a, lb, t, name, lo as int, r as int, cap),
            cap == old(keys)@.len(), cap == old(sums)@.len(),
        decreases hi - r,
    {
        // One frame-of-reference group: rows r .. gend share the bases of group g.
        let g = r / bs;
        proof {
            lemma_row_vals(*c, t, r as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(r as int, bs as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(r as int, bs as int);
            assert((bs as int) * (g as int) == (g as int) * (bs as int)) by (nonlinear_arith);
        }
        let gend0: usize = if hi - r > bs - r % bs { r + (bs - r % bs) } else { hi };
        let gend = gend0;
        let o: i128 = c.supp_b[g] as i128 - smin as i128;
        let off: i64 = if o < -(OFF_LIM as i128) { -OFF_LIM } else if o > OFF_LIM as i128 { OFF_LIM } else { o as i64 };
        let cb = c.cost_b[g];
        let qb = c.qty_b[g];
        let kb = c.key_b[g];
        while r < gend
            invariant
                scan_env(*c, fl@, smin, range, t, name),
                use_bm ==> bm_ok(bm@, c.n as int, t, name),
                lo <= r <= gend <= hi <= c.n, bs == c.bs, supp_c@ == c.supp_c@,
                g * bs <= r, gend <= g * bs + bs, g < c.ng,
                o as int == c.supp_b@[g as int] - smin,
                off as int == (if o < -OFF_LIM { -OFF_LIM as int } else if o > OFF_LIM { OFF_LIM as int } else { o as int }),
                cb == c.cost_b@[g as int], qb == c.qty_b@[g as int], kb == c.key_b@[g as int],
                keys@.len() == cap, sums@.len() == cap, mask@.len() == CHUNK_WORDS,
                acc_inv(keys@, sums@, a, lb, t, name, lo as int, r as int, cap),
                cap == old(keys)@.len(), cap == old(sums)@.len(),
            decreases gend - r,
        {
            let e: usize = if gend - r > CHUNK_ROWS { r + CHUNK_ROWS } else { gend };
            if use_bm {
                chunk_mask_bm(c, bm, r, e, mask, touch, Ghost(t), Ghost(name));
            } else {
                chunk_mask(c, fl, smin, range, supp_c, off, r, e, mask, touch, Ghost(t), Ghost(name), Ghost(g as int), Ghost(o as int));
            }
            let (a2, s) = take_chunk(keys, sums, a, lb, mask, r, e, c, cb, qb, kb, Ghost(t), Ghost(name), Ghost(lo as int),
                Ghost(hi as int), Ghost(cap), Ghost(g as int));
            if s != SCAN_OK {
                return (a2, s);
            }
            a = a2;
            r = e;
        }
    }
    let ghost keys0 = keys@;
    let ghost sums0 = sums@;
    let ghost len0 = a.len;
    let emit = a.have && a.acc > lb;
    if emit {
        if a.len >= keys.len() {
            return (a, SCAN_FULL);
        }
        let len = a.len;
        crate::gendb_entry::work::put(keys, len, a.cur);
        crate::gendb_entry::work::put(sums, len, a.acc);
        a.len = len + 1;
    }
    proof { lemma_scan_end(t, name, lo as int, hi as int, keys0, sums0, len0 as int, a.have, a.cur, a.acc, a.cur_row@, keys@, sums@, a.len as int, lb, emit); }
    (a, SCAN_OK)
}

} // verus!
