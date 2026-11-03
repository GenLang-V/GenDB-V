//! Parallel scan of `num` for the rows with `uom = $1`, keeping per task only those whose value coefficient is
//! at least a task-local threshold that rises when the preallocated buffer fills up.
//!
//! Layout: a task covers rows `lo..hi` of `num`. Its buffer `rows/coeffs[0..len]` holds exactly
//! `cands(lo, i, thr)` (the rows seen so far with `uom = $1` and coefficient `>= thr`, in row order) with their
//! coefficients. When the buffer is full, the threshold rises above its smallest coefficient (to about the
//! median of a sample) and the buffer is filtered in place, so it always holds every candidate of the range at
//! the current threshold.
//!
//! Kernel: per block of 64 rows, a bit mask of the rows whose `uom` has `$1`'s length (branch-free over the
//! 65 offsets, vectorized); for each set bit (lowest first) the value is compared with the threshold, and only a
//! row at or above it has its `uom` bytes compared. So the scan streams the `uom` offsets, loads one value per
//! row of the right length, and touches `uom` bytes almost never.
use vstd::prelude::*;
use crate::gendb_entry::parallel::WorkerTask;
use crate::link::query::{text_at, text_wf, TextCol, TextView};
use crate::agent::spec::*;

verus! {

/// Number of sampled coefficients used to choose a raised threshold.
pub const SAMPLE: usize = 32;

/// One task: rows `lo..hi` of `num` (`uom` and `value` are the whole parts, `param` the bytes of `$1`).
pub struct ScanTask {
    pub lo: usize,
    pub hi: usize,
    pub uom: TextCol,
    pub value: &'static [i128],
    pub param: &'static [u8],
    pub plen: usize,
    pub cap: usize,
    pub rows: Vec<usize>,
    pub coeffs: Vec<i128>,
    pub scratch: Vec<i128>,
    pub ctx: Ghost<Ctx>,
}

/// The output of a task: when `ok`, the first `len` entries list `cands(lo, hi, thr)`. `ok` is false only when
/// the threshold could not rise (every buffered coefficient is `i128::MAX`).
pub struct ScanOut {
    pub ok: bool,
    pub thr: i128,
    pub len: usize,
    pub rows: Vec<usize>,
    pub coeffs: Vec<i128>,
}

/// The facts a task relies on.
pub open spec fn scan_inputs_ok(t: ScanTask) -> bool {
    let c = t.ctx@;
    &&& ctx_ok(c)
    &&& t.uom@ == uom_view(c.np)
    &&& t.value@ == coeff_seq(c.np)
    &&& t.param@ == c.pv
    &&& t.plen == t.param@.len()
    &&& t.lo <= t.hi <= c.n
    &&& t.cap >= 1
    &&& t.rows@.len() == t.cap
    &&& t.coeffs@.len() == t.cap
    &&& t.scratch@.len() == SAMPLE
}

/// What a task's output means.
pub open spec fn scan_out_ok(c: Ctx, lo: int, hi: int, out: ScanOut) -> bool {
    out.ok ==> lists(c, out.rows@, out.coeffs@, out.len as int, cands(c, lo, hi, out.thr as int))
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        scan_inputs_ok(*self)
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        scan_out_ok(self.ctx@, self.lo as int, self.hi as int, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: ScanOut) {
        scan_range(self)
    }
}

/// Whether row `r` of the text column `t` (`n` rows) equals `param` (`plen` bytes).
pub fn text_is(t: &TextCol, r: usize, param: &'static [u8], plen: usize, Ghost(n): Ghost<int>) -> (hit: bool)
    requires
        text_wf(t@, n),
        r < n,
        plen == param@.len(),
    ensures
        hit == (text_at(t@, r as int) == param@),
    no_unwind
{
    let a = t.offsets[r];
    let b = t.offsets[r + 1];
    proof {
        assert(0 <= t@.offsets[r as int] <= t@.offsets[r + 1] <= t@.bytes.len());
        assert(text_at(t@, r as int).len() == b - a);
    }
    if (b - a) as usize != plen {
        return false;
    }
    let bytes: &'static [u8] = t.bytes;
    let (_, tail) = bytes.split_at(a as usize);
    let (mid, _) = tail.split_at(plen);
    proof {
        assert(mid@ =~= text_at(t@, r as int));
    }
    let mut k: usize = 0;
    while k < plen
        invariant
            k <= plen,
            plen == param@.len(),
            mid@.len() == plen,
            mid@ == text_at(t@, r as int),
            forall|q: int| 0 <= q < k ==> mid@[q] == param@[q],
        decreases plen - k,
    {
        if mid[k] != param[k] {
            proof {
                assert(mid@[k as int] != param@[k as int]);
            }
            return false;
        }
        k = k + 1;
    }
    proof {
        assert(mid@ =~= param@);
    }
    true
}

/// A threshold above the smallest of `coeffs[0..len]` (about the median of a sample), or `None` when the
/// smallest is `i128::MAX`.
fn raised_threshold(coeffs: &Vec<i128>, len: usize, scratch: &mut Vec<i128>) -> (r: Option<i128>)
    requires
        1 <= len <= coeffs@.len(),
        old(scratch)@.len() == SAMPLE,
    ensures
        final(scratch)@.len() == SAMPLE,
        r matches Some(t) ==> exists|k: int| 0 <= k < len && coeffs@[k] < t,
    no_unwind
{
    let mut lo_val = coeffs[0];
    let mut lo_at: usize = 0;
    let mut k: usize = 1;
    while k < len
        invariant
            1 <= len <= coeffs@.len(),
            k <= len,
            lo_at < len,
            lo_val == coeffs@[lo_at as int],
        decreases len - k,
    {
        if coeffs[k] < lo_val {
            lo_val = coeffs[k];
            lo_at = k;
        }
        k = k + 1;
    }
    // Sample up to SAMPLE coefficients evenly and sort them (insertion sort) to estimate the median.
    let m: usize = if len < SAMPLE { len } else { SAMPLE };
    let step: usize = len / m;
    let mut j: usize = 0;
    while j < m
        invariant
            1 <= m <= SAMPLE,
            m <= len <= coeffs@.len(),
            step == len / m,
            j <= m,
            scratch@.len() == SAMPLE,
        decreases m - j,
    {
        proof {
            assert(j * step <= (m - 1) * step) by (nonlinear_arith) requires j <= m - 1, step >= 0;
            assert((m - 1) * step < len) by (nonlinear_arith) requires step == len / m, m >= 1, len >= m;
        }
        scratch[j] = coeffs[j * step];
        j = j + 1;
    }
    let mut a: usize = 1;
    while a < m
        invariant
            1 <= m <= SAMPLE,
            1 <= a <= m,
            scratch@.len() == SAMPLE,
        decreases m - a,
    {
        let x = scratch[a];
        let mut b: usize = a;
        while b > 0 && scratch[b - 1] > x
            invariant
                b <= a < m <= SAMPLE,
                scratch@.len() == SAMPLE,
            decreases b,
        {
            let y = scratch[b - 1];
            scratch[b] = y;
            b = b - 1;
        }
        scratch[b] = x;
        a = a + 1;
    }
    let med = scratch[m / 2];
    if med > lo_val {
        Some(med)
    } else if lo_val < i128::MAX {
        Some(lo_val + 1)
    } else {
        None
    }
}

/// Keep the buffered entries with coefficient at least `nt`, in order.
fn compact(rows: &mut Vec<usize>, coeffs: &mut Vec<i128>, len: usize, nt: i128,
    Ghost(c): Ghost<Ctx>, Ghost(before): Ghost<Seq<int>>) -> (w: usize)
    requires
        lists(c, old(rows)@, old(coeffs)@, len as int, before),
    ensures
        final(rows)@.len() == old(rows)@.len(),
        final(coeffs)@.len() == old(coeffs)@.len(),
        lists(c, final(rows)@, final(coeffs)@, w as int, before.filter(ge_thr(c, nt as int))),
    no_unwind
{
    let ghost f = ge_thr(c, nt as int);
    proof {
        reveal(Seq::filter);
        assert(before.subrange(0, 0).filter(f) =~= Seq::<int>::empty());
    }
    let mut w: usize = 0;
    let mut r: usize = 0;
    while r < len
        invariant
            w <= r <= len,
            len <= rows@.len(), len <= coeffs@.len(),
            rows@.len() == old(rows)@.len(),
            coeffs@.len() == old(coeffs)@.len(),
            before.len() == len,
            f == ge_thr(c, nt as int),
            forall|k: int| r <= k < len ==> #[trigger] rows@[k] as int == before[k],
            forall|k: int| r <= k < len ==> #[trigger] coeffs@[k] as int == coeff(c, before[k]),
            lists(c, rows@, coeffs@, w as int, before.subrange(0, r as int).filter(f)),
        decreases len - r,
    {
        let rr = rows[r];
        let cc = coeffs[r];
        let ghost x = before[r as int];
        let ghost kept = before.subrange(0, r as int).filter(f);
        proof {
            assert(rr as int == x && cc as int == coeff(c, x));
            lemma_filter_push(before.subrange(0, r as int), x, f);
            assert(before.subrange(0, r as int + 1) =~= before.subrange(0, r as int).push(x));
        }
        if cc >= nt {
            rows[w] = rr;
            coeffs[w] = cc;
            proof {
                assert(kept.push(x)[w as int] == x);
                assert forall|k: int| 0 <= k < w + 1 implies #[trigger] rows@[k] as int == kept.push(x)[k] by {
                    if k < w {
                        assert(kept.push(x)[k] == kept[k]);
                    }
                }
                assert forall|k: int| 0 <= k < w + 1 implies #[trigger] coeffs@[k] as int == coeff(c, kept.push(x)[k]) by {
                    if k < w {
                        assert(kept.push(x)[k] == kept[k]);
                    }
                }
            }
            w = w + 1;
            proof {
                assert(before.subrange(0, r as int + 1).filter(f) == kept.push(x));
                assert(lists(c, rows@, coeffs@, w as int, kept.push(x)));
            }
        } else {
            proof {
                assert(!f(x));
                assert(before.subrange(0, r as int + 1).filter(f) == kept);
            }
        }
        r = r + 1;
    }
    proof {
        assert(before.subrange(0, len as int) =~= before);
    }
    w
}

// ------------------------------------------------------------------------------------------------ bit masks

/// Bit `j` of `m`.
pub open spec fn bit(m: u64, j: u64) -> bool {
    (m >> j) & 1u64 == 1u64
}

/// Setting bit `k` (when `b == 1`) leaves the other bits.
proof fn lemma_bit_or(m: u64, b: u64, k: u64, j: u64)
    requires b <= 1, k < 64, j < 64,
    ensures bit(m | (b << k), j) <==> (bit(m, j) || (j == k && b == 1)),
{
    assert(((m | (b << k)) >> j) & 1u64 == 1u64 <==> ((m >> j) & 1u64 == 1u64 || (j == k && b == 1)))
        by (bit_vector)
        requires b <= 1, k < 64, j < 64;
}

/// Flipping bit `t` leaves the other bits.
proof fn lemma_bit_flip(m: u64, t: u64, j: u64)
    requires t < 64, j < 64,
    ensures bit(m ^ (1u64 << t), j) <==> (bit(m, j) != (j == t)),
{
    assert(((m ^ (1u64 << t)) >> j) & 1u64 == 1u64 <==> (((m >> j) & 1u64 == 1u64) != (j == t)))
        by (bit_vector)
        requires t < 64, j < 64;
}

/// No bit of zero is set.
proof fn lemma_bit_zero(j: u64)
    ensures !bit(0u64, j),
{
    assert((0u64 >> j) & 1u64 == 0u64) by (bit_vector);
}

/// Bits below `t` of a value whose low `t` bits are clear are clear.
proof fn lemma_bit_low(m: u64, t: u64, j: u64)
    requires t < 64, j < t, m & sub(1u64 << t, 1u64) == 0u64,
    ensures !bit(m, j),
{
    assert((m >> j) & 1u64 == 0u64) by (bit_vector)
        requires t < 64, j < t, m & sub(1u64 << t, 1u64) == 0u64;
}

/// Index of the lowest set bit of `m != 0` (branch-free: the set bit of `m & -m` located by six masks).
#[inline(always)]
fn lowest_bit(m: u64) -> (t: u64)
    requires m != 0,
    ensures
        t < 64,
        bit(m, t),
        forall|j: u64| j < t ==> !#[trigger] bit(m, j),
    no_unwind
{
    proof {
        assert(!m < 0xFFFF_FFFF_FFFF_FFFFu64) by (bit_vector) requires m != 0u64;
    }
    let low: u64 = m & (!m + 1);
    let b0: u64 = if low & 0xAAAA_AAAA_AAAA_AAAAu64 != 0 { 1 } else { 0 };
    let b1: u64 = if low & 0xCCCC_CCCC_CCCC_CCCCu64 != 0 { 2 } else { 0 };
    let b2: u64 = if low & 0xF0F0_F0F0_F0F0_F0F0u64 != 0 { 4 } else { 0 };
    let b3: u64 = if low & 0xFF00_FF00_FF00_FF00u64 != 0 { 8 } else { 0 };
    let b4: u64 = if low & 0xFFFF_0000_FFFF_0000u64 != 0 { 16 } else { 0 };
    let b5: u64 = if low & 0xFFFF_FFFF_0000_0000u64 != 0 { 32 } else { 0 };
    let t: u64 = b0 | b1 | b2 | b3 | b4 | b5;
    proof {
        assert(t < 64 && (m >> t) & 1u64 == 1u64 && m & sub(1u64 << t, 1u64) == 0u64) by (bit_vector)
            requires
                m != 0u64,
                low == m & add(!m, 1u64),
                (low & 0xAAAA_AAAA_AAAA_AAAAu64 != 0u64 ==> b0 == 1u64), (low & 0xAAAA_AAAA_AAAA_AAAAu64 == 0u64 ==> b0 == 0u64),
                (low & 0xCCCC_CCCC_CCCC_CCCCu64 != 0u64 ==> b1 == 2u64), (low & 0xCCCC_CCCC_CCCC_CCCCu64 == 0u64 ==> b1 == 0u64),
                (low & 0xF0F0_F0F0_F0F0_F0F0u64 != 0u64 ==> b2 == 4u64), (low & 0xF0F0_F0F0_F0F0_F0F0u64 == 0u64 ==> b2 == 0u64),
                (low & 0xFF00_FF00_FF00_FF00u64 != 0u64 ==> b3 == 8u64), (low & 0xFF00_FF00_FF00_FF00u64 == 0u64 ==> b3 == 0u64),
                (low & 0xFFFF_0000_FFFF_0000u64 != 0u64 ==> b4 == 16u64), (low & 0xFFFF_0000_FFFF_0000u64 == 0u64 ==> b4 == 0u64),
                (low & 0xFFFF_FFFF_0000_0000u64 != 0u64 ==> b5 == 32u64), (low & 0xFFFF_FFFF_0000_0000u64 == 0u64 ==> b5 == 0u64),
                t == b0 | b1 | b2 | b3 | b4 | b5;
        assert forall|j: u64| j < t implies !#[trigger] bit(m, j) by {
            lemma_bit_low(m, t, j);
        }
    }
    t
}

/// The offsets window of 64 rows: `w[k]` is offset `i + k`, nondecreasing and nonnegative.
pub open spec fn window_ok(w: Seq<i64>) -> bool {
    &&& w.len() == 65
    &&& forall|k: int| 0 <= k < 64 ==> 0 <= #[trigger] w[k] <= w[k + 1]
}

/// Value `j` of the window has `pl` bytes.
pub open spec fn len_hit(w: Seq<i64>, j: int, pl: u64) -> bool {
    w[j + 1] - w[j] == pl
}

/// Bit `k` of the result is set exactly when value `k` of the window has `pl` bytes (branch-free, so the
/// compiler vectorizes it).
#[inline(always)]
fn len_mask(w: &[i64], pl: u64) -> (m: u64)
    requires window_ok(w@),
    ensures forall|j: u64| j < 64 ==> (#[trigger] bit(m, j) <==> len_hit(w@, j as int, pl)),
    no_unwind
{
    let mut m: u64 = 0;
    let mut k: usize = 0;
    proof {
        assert forall|j: u64| j < 64 implies !#[trigger] bit(m, j) by {
            lemma_bit_zero(j);
        }
    }
    while k < 64
        invariant
            k <= 64,
            window_ok(w@),
            forall|j: u64| j < 64 ==> (#[trigger] bit(m, j) <==> (j < k && len_hit(w@, j as int, pl))),
        decreases 64 - k,
    {
        proof {
            assert(0 <= w@[k as int] <= w@[k + 1]);
        }
        let b: u64 = if (w[k + 1] - w[k]) as u64 == pl { 1 } else { 0 };
        proof {
            assert(b == 1 <==> len_hit(w@, k as int, pl));
            assert forall|j: u64| j < 64 implies
                (#[trigger] bit(m | (b << (k as u64)), j) <==> (j < k + 1 && len_hit(w@, j as int, pl))) by {
                lemma_bit_or(m, b, k as u64, j);
            }
        }
        m = m | (b << (k as u64));
        k = k + 1;
    }
    m
}

// ------------------------------------------------------------------------------------------------ the scan

/// Rows `a..b` hold no candidate: the candidate list is unchanged across them.
pub proof fn lemma_cands_skip(c: Ctx, lo: int, a: int, b: int, thr: int)
    requires lo <= a <= b, forall|r: int| a <= r < b ==> !#[trigger] cand(c, r, thr),
    ensures cands(c, lo, b, thr) == cands(c, lo, a, thr),
    decreases b - a,
{
    if b > a {
        lemma_cands_skip(c, lo, a, b - 1, thr);
        assert(!cand(c, b - 1, thr));
    }
}

/// A row whose `uom` has another length than `$1` is no candidate.
proof fn lemma_len_miss(c: Ctx, uom: TextView, w: Seq<i64>, i: int, j: int, thr: int)
    requires
        text_wf(uom, c.n),
        uom == uom_view(c.np),
        0 <= i, i + 64 <= c.n,
        w == uom.offsets.subrange(i, i + 65),
        0 <= j < 64,
        !len_hit(w, j, c.pv.len() as u64),
    ensures
        !cand(c, i + j, thr),
{
    let r = i + j;
    assert(w[j] == uom.offsets[r] && w[j + 1] == uom.offsets[r + 1]);
    assert(0 <= uom.offsets[r] <= uom.offsets[r + 1] <= uom.bytes.len());
    assert(uom_text(c, r).len() == uom.offsets[r + 1] - uom.offsets[r]);
}

/// The candidate buffer of a task: `rows/coeffs[0..len]` list `cands(lo, i, thr)` for the rows `i` scanned so far.
#[verifier::opaque]
pub open spec fn buf_ok(c: Ctx, lo: int, i: int, cap: usize, rows: Seq<usize>, coeffs: Seq<i128>, scratch: Seq<i128>,
    len: usize, thr: i128) -> bool {
    &&& cap >= 1
    &&& rows.len() == cap
    &&& coeffs.len() == cap
    &&& scratch.len() == SAMPLE
    &&& len <= cap
    &&& lists(c, rows, coeffs, len as int, cands(c, lo, i, thr as int))
}

/// The columns and binding a task reads.
#[verifier::opaque]
pub open spec fn cols_ok(c: Ctx, uom: TextCol, value: Seq<i128>, param: Seq<u8>, plen: usize) -> bool {
    &&& text_wf(uom@, c.n)
    &&& uom@ == uom_view(c.np)
    &&& value == coeff_seq(c.np)
    &&& value.len() == c.n
    &&& param == c.pv
    &&& plen == param.len()
}

/// The buffer still holds when rows `a..b` hold no candidate.
proof fn lemma_buf_skip(c: Ctx, lo: int, a: int, b: int, cap: usize, rows: Seq<usize>, coeffs: Seq<i128>,
    scratch: Seq<i128>, len: usize, thr: i128)
    requires
        lo <= a <= b,
        buf_ok(c, lo, a, cap, rows, coeffs, scratch, len, thr),
        forall|r: int| a <= r < b ==> !#[trigger] cand(c, r, thr as int),
    ensures
        buf_ok(c, lo, b, cap, rows, coeffs, scratch, len, thr),
{
    reveal(buf_ok);
    lemma_cands_skip(c, lo, a, b, thr as int);
}

/// The buffer still holds after a row below the threshold.
proof fn lemma_buf_below(c: Ctx, lo: int, r: int, cap: usize, rows: Seq<usize>, coeffs: Seq<i128>,
    scratch: Seq<i128>, len: usize, thr: i128)
    requires
        lo <= r,
        buf_ok(c, lo, r, cap, rows, coeffs, scratch, len, thr),
        coeff(c, r) < thr,
    ensures
        buf_ok(c, lo, r + 1, cap, rows, coeffs, scratch, len, thr),
{
    reveal(buf_ok);
    lemma_cands_step(c, lo, r, thr as int);
}

/// The rows of a block whose mask bit is clear (from bit `p` on) hold no candidate.
proof fn lemma_gap(c: Ctx, uom: TextCol, value: Seq<i128>, param: Seq<u8>, plen: usize, w: Seq<i64>, mk: u64,
    i: int, p: int, t: int, thr: int)
    requires
        cols_ok(c, uom, value, param, plen),
        0 <= i, i + 64 <= c.n,
        w == uom@.offsets.subrange(i, i + 65),
        0 <= p <= t <= 64,
        forall|j: u64| j < 64 ==> (#[trigger] bit(mk, j) <==> (j >= p && len_hit(w, j as int, plen as u64))),
        forall|j: u64| p <= j < t ==> !#[trigger] bit(mk, j),
    ensures
        forall|r: int| i + p <= r < i + t ==> !#[trigger] cand(c, r, thr),
{
    reveal(cols_ok);
    assert forall|r: int| i + p <= r < i + t implies !#[trigger] cand(c, r, thr) by {
        let j = (r - i) as u64;
        assert(!bit(mk, j));
        lemma_len_miss(c, uom@, w, i, j as int, thr);
    }
}

/// The offsets of a block of 64 rows form a window.
proof fn lemma_window(c: Ctx, uom: TextCol, value: Seq<i128>, param: Seq<u8>, plen: usize, i: int, w: Seq<i64>)
    requires
        cols_ok(c, uom, value, param, plen),
        0 <= i, i + 64 <= c.n,
        w == uom@.offsets.subrange(i, i + 65),
    ensures
        window_ok(w),
{
    reveal(cols_ok);
    assert forall|k: int| 0 <= k < 64 implies 0 <= #[trigger] w[k] <= w[k + 1] by {
        assert(w[k] == uom@.offsets[i + k] && w[k + 1] == uom@.offsets[i + k + 1]);
    }
}

/// The facts of `cols_ok` the exec code needs.
proof fn lemma_cols(c: Ctx, uom: TextCol, value: Seq<i128>, param: Seq<u8>, plen: usize)
    requires cols_ok(c, uom, value, param, plen),
    ensures
        uom@.offsets.len() == c.n + 1,
        uom.offsets@ == uom@.offsets,
        value == coeff_seq(c.np),
        value.len() == c.n,
        plen == param.len(),
{
    reveal(cols_ok);
}

/// Visit row `r` (its `uom` may or may not be `$1`): append it when it is a candidate, raising the threshold
/// first when the buffer is full. Returns `(ok, len, thr)`; when `ok`, the buffer covers rows up to `r + 1`.
fn visit_row(uom: &TextCol, value: &'static [i128], param: &'static [u8], plen: usize,
    rows: &mut Vec<usize>, coeffs: &mut Vec<i128>, scratch: &mut Vec<i128>, cap: usize, len: usize, thr: i128,
    r: usize, Ghost(c): Ghost<Ctx>, Ghost(lo): Ghost<int>) -> (res: (bool, usize, i128))
    requires
        cols_ok(c, *uom, value@, param@, plen),
        lo <= r < c.n,
        buf_ok(c, lo, r as int, cap, old(rows)@, old(coeffs)@, old(scratch)@, len, thr),
    ensures
        final(rows)@.len() == cap,
        final(coeffs)@.len() == cap,
        final(scratch)@.len() == SAMPLE,
        res.0 ==> buf_ok(c, lo, r + 1, cap, final(rows)@, final(coeffs)@, final(scratch)@, res.1, res.2),
    no_unwind
{
    proof {
        reveal(cols_ok);
        reveal(buf_ok);
    }
    let x = value[r];
    let mut len = len;
    let mut thr = thr;
    if x >= thr {
        let hit = text_is(uom, r, param, plen, Ghost(c.n));
        proof {
            assert(uom_text(c, r as int) == text_at(uom@, r as int));
        }
        if hit {
            if len == cap {
                let ghost oc = coeffs@;
                match raised_threshold(coeffs, len, scratch) {
                    None => {
                        return (false, len, thr);
                    },
                    Some(nt) => {
                        let ghost before = cands(c, lo, r as int, thr as int);
                        let w = compact(rows, coeffs, len, nt, Ghost(c), Ghost(before));
                        proof {
                            let k = choose|k: int| 0 <= k < len && oc[k] < nt;
                            assert(oc[k] as int == coeff(c, before[k]));
                            lemma_cands_range(c, lo, r as int, thr as int, k);
                            lemma_cands_raise(c, lo, r as int, thr as int, nt as int);
                            lemma_filter_drops(before, ge_thr(c, nt as int), k);
                        }
                        len = w;
                        thr = nt;
                    },
                }
            }
            if x >= thr {
                rows[len] = r;
                coeffs[len] = x;
                proof {
                    let p = cands(c, lo, r as int, thr as int);
                    assert forall|k: int| 0 <= k < len + 1 implies #[trigger] rows@[k] as int == p.push(r as int)[k] by {
                        if k < len {
                            assert(p.push(r as int)[k] == p[k]);
                        }
                    }
                    assert forall|k: int| 0 <= k < len + 1 implies #[trigger] coeffs@[k] as int == coeff(c, p.push(r as int)[k]) by {
                        if k < len {
                            assert(p.push(r as int)[k] == p[k]);
                        }
                    }
                }
                len = len + 1;
            }
        }
    }
    proof {
        lemma_cands_step(c, lo, r as int, thr as int);
        reveal(buf_ok);
    }
    (true, len, thr)
}

/// One block of 64 rows `i..i + 64`: the length bit mask of the block's `uom` values (vectorized), then for each
/// set bit the row visit (value check first; the bytes only when the value reaches the threshold).
fn scan_block(uom: &TextCol, value: &'static [i128], param: &'static [u8], plen: usize,
    rows: &mut Vec<usize>, coeffs: &mut Vec<i128>, scratch: &mut Vec<i128>, cap: usize, len: usize, thr: i128,
    i: usize, hi: usize, Ghost(c): Ghost<Ctx>, Ghost(lo): Ghost<int>) -> (res: (bool, usize, i128))
    requires
        cols_ok(c, *uom, value@, param@, plen),
        lo <= i, i + 64 <= hi, hi <= c.n,
        buf_ok(c, lo, i as int, cap, old(rows)@, old(coeffs)@, old(scratch)@, len, thr),
    ensures
        final(rows)@.len() == cap,
        final(coeffs)@.len() == cap,
        final(scratch)@.len() == SAMPLE,
        res.0 ==> buf_ok(c, lo, i + 64, cap, final(rows)@, final(coeffs)@, final(scratch)@, res.1, res.2),
    no_unwind
{
    proof {
        lemma_cols(c, *uom, value@, param@, plen);
        reveal(buf_ok);
    }
    let off: &'static [i64] = uom.offsets;
    let (_, tail) = off.split_at(i);
    let (w, _) = tail.split_at(65);
    proof {
        assert(w@ =~= uom@.offsets.subrange(i as int, i + 65));
        lemma_window(c, *uom, value@, param@, plen, i as int, w@);
    }
    let pl: u64 = plen as u64;
    let mut mk: u64 = len_mask(w, pl);
    let mut p: usize = 0;
    let mut len = len;
    let mut thr = thr;
    while mk != 0
        invariant
            lo <= i, i + 64 <= hi, hi <= c.n,
            p <= 64,
            cols_ok(c, *uom, value@, param@, plen),
            w@ == uom@.offsets.subrange(i as int, i + 65),
            pl == plen,
            forall|j: u64| j < 64 ==> (#[trigger] bit(mk, j) <==> (j >= p && len_hit(w@, j as int, pl))),
            buf_ok(c, lo, i + p, cap, rows@, coeffs@, scratch@, len, thr),
        decreases 64 - p,
    {
        let t = lowest_bit(mk);
        proof {
            // The rows between the previous set bit and this one have another length: no candidates.
            lemma_gap(c, *uom, value@, param@, plen, w@, mk, i as int, p as int, t as int, thr as int);
            lemma_buf_skip(c, lo, i + p, i + t, cap, rows@, coeffs@, scratch@, len, thr);
        }
        let ghost old_mk = mk;
        mk = mk ^ (1u64 << t);
        proof {
            assert forall|j: u64| j < 64 implies (#[trigger] bit(mk, j) <==> (j >= t + 1 && len_hit(w@, j as int, pl))) by {
                lemma_bit_flip(old_mk, t, j);
            }
        }
        let r = i + t as usize;
        proof {
            lemma_cols(c, *uom, value@, param@, plen);
        }
        // Fast path: most rows of the right length are below the threshold.
        if value[r] >= thr {
            let res = visit_row(uom, value, param, plen, rows, coeffs, scratch, cap, len, thr, r, Ghost(c), Ghost(lo));
            if !res.0 {
                return res;
            }
            len = res.1;
            thr = res.2;
        } else {
            proof {
                lemma_buf_below(c, lo, r as int, cap, rows@, coeffs@, scratch@, len, thr);
            }
        }
        p = t as usize + 1;
    }
    proof {
        assert forall|j: u64| p <= j < 64 implies !#[trigger] bit(mk, j) by {
            lemma_bit_zero(j);
        }
        lemma_gap(c, *uom, value@, param@, plen, w@, mk, i as int, p as int, 64, thr as int);
        lemma_buf_skip(c, lo, i + p, i + 64, cap, rows@, coeffs@, scratch@, len, thr);
    }
    (true, len, thr)
}

/// The task body: the candidates of `lo..hi` at the final threshold. Whole blocks of 64 rows go through
/// `scan_block`; the rows after the last whole block are visited one by one.
pub fn scan_range(t: ScanTask) -> (out: ScanOut)
    requires
        scan_inputs_ok(t),
    ensures
        scan_out_ok(t.ctx@, t.lo as int, t.hi as int, out),
    no_unwind
{
    let ghost c = t.ctx@;
    let ScanTask { lo, hi, uom, value, param, plen, cap, rows, coeffs, scratch, ctx: _ } = t;
    let mut rows = rows;
    let mut coeffs = coeffs;
    let mut scratch = scratch;
    let mut thr: i128 = i128::MIN;
    let mut len: usize = 0;
    proof {
        lemma_num_text_wf(c);
        reveal(cols_ok);
        reveal(buf_ok);
        assert(cands(c, lo as int, lo as int, thr as int) =~= Seq::<int>::empty());
    }
    let mut i: usize = lo;
    while hi - i >= 64
        invariant
            lo <= i <= hi <= c.n,
            cols_ok(c, uom, value@, param@, plen),
            buf_ok(c, lo as int, i as int, cap, rows@, coeffs@, scratch@, len, thr),
        decreases hi - i,
    {
        let res = scan_block(&uom, value, param, plen, &mut rows, &mut coeffs, &mut scratch, cap, len, thr, i, hi,
            Ghost(c), Ghost(lo as int));
        if !res.0 {
            return ScanOut { ok: false, thr, len, rows, coeffs };
        }
        len = res.1;
        thr = res.2;
        i = i + 64;
    }
    while i < hi
        invariant
            lo <= i <= hi <= c.n,
            cols_ok(c, uom, value@, param@, plen),
            buf_ok(c, lo as int, i as int, cap, rows@, coeffs@, scratch@, len, thr),
        decreases hi - i,
    {
        let res = visit_row(&uom, value, param, plen, &mut rows, &mut coeffs, &mut scratch, cap, len, thr, i,
            Ghost(c), Ghost(lo as int));
        if !res.0 {
            return ScanOut { ok: false, thr, len, rows, coeffs };
        }
        len = res.1;
        thr = res.2;
        i = i + 1;
    }
    proof {
        reveal(buf_ok);
    }
    ScanOut { ok: true, thr, len, rows, coeffs }
}

} // verus!
