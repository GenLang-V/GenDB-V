//! The lineitem scan of one row range (`scan_range`, and `ScanTask` as a `fork_join` task): per ship-mode slot the
//! number of qualifying lineitem rows with an order (`n0`, `n1`) and how many of them have a high-priority order
//! (`h0`, `h1`). Slot 0 is `$1`, slot 1 is `$2` when it differs from `$1`.
//!
//! The range is scanned in blocks of `BLOCK` rows through seven branch-light loops over small buffers, so that the
//! loads of different rows overlap (memory-level parallelism):
//! 1. candidates (`collect_cands`): per 64-row word a branch-free mask of the date conditions (receipt day in the
//!    stored-day window `[dlo, dhi)`, commit before receipt, ship before commit; vectorized over a full word), then
//!    its set bits as offsets from the block start: the list `range_filter(base, end, p_dates)`;
//! 2. mode offsets (`mode_offsets`): each candidate's `l_shipmode` offset and length, then (`mode_first`) the first
//!    byte at that offset;
//! 3. modes (`mode_select`): the candidates whose ship mode is `$1` or `$2` (`p_mode`), with their slot; the bytes
//!    are compared only when the length and the first byte match;
//! 4. keys (`order_keys`): each such row's `l_orderkey` and the orders row where dbgen puts that key;
//! 5. orders (`order_prios`): the orders row of the key (the dbgen guess when `o_orderkey` there is the key, else a
//!    linear search; `o_orderkey` is duplicate-free) and its `o_orderpriority` offset and length (length -1: no order);
//! 6. counts (`count_rows`): the priority test (`1-URGENT` or `2-HIGH`) and the slot counts.
//! The counts of a range are range sums of guarded 0/1 terms per row (`acc_ok`).
use vstd::prelude::*;
use vstd::std_specs::bits::u64_trailing_zeros;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::link::query::{text_wf, text_at};
use crate::agent::common::bits::*;
use crate::agent::common::tz::{tz64, tz_table_array};
use crate::agent::common::selection::*;
use crate::agent::tables::*;
use crate::agent::normal::{is_high, urgent, high2};
use crate::agent::sums::*;

verus! {

/// Rows per block (offsets in a block fit `u32`); also the length of every scratch buffer.
pub const BLOCK: usize = 4096;

/// The stored columns a scan reads (whole parts) and their lengths (`slice.len()` may unwind in a worker).
#[derive(Clone, Copy)]
pub struct Cols {
    pub rcpt: &'static [i32],
    pub cmt: &'static [i32],
    pub ship: &'static [i32],
    pub moff: &'static [i64],
    pub mbytes: &'static [u8],
    pub lokey: &'static [i64],
    pub okey: &'static [i64],
    pub poff: &'static [i64],
    pub pbytes: &'static [u8],
    pub nl: usize,
    pub no: usize,
    pub nmb: usize,
    pub npb: usize,
}

/// The slices are the stored columns of `sv`, the text columns are well formed and `o_orderkey` is duplicate-free.
pub open spec fn cols_ok(c: Cols, sv: StoresView) -> bool {
    &&& c.rcpt@ == lrd(sv) && c.cmt@ == lcd(sv) && c.ship@ == lsd(sv) && c.lokey@ == lok(sv)
    &&& c.moff@ == lmode(sv).offsets && c.mbytes@ == lmode(sv).bytes
    &&& c.okey@ == ok(sv) && c.poff@ == oprio(sv).offsets && c.pbytes@ == oprio(sv).bytes
    &&& c.nl as int == n_l(sv) && c.no as int == n_o(sv)
    &&& c.nmb as int == c.mbytes@.len() && c.npb as int == c.pbytes@.len()
    &&& lsd(sv).len() == n_l(sv) && lcd(sv).len() == n_l(sv) && lrd(sv).len() == n_l(sv)
    &&& text_wf(lmode(sv), n_l(sv))
    &&& text_wf(oprio(sv), n_o(sv))
    &&& keys_unique(ok(sv))
}

/// The parameters of the scan: the two ship modes with their lengths, whether they differ, and the stored-day
/// window `[dlo, dhi)` of the receipt date.
#[derive(Clone, Copy)]
pub struct Probe {
    pub p1: &'static [u8],
    pub p1len: usize,
    pub p2: &'static [u8],
    pub p2len: usize,
    pub two: bool,
    pub dlo: i32,
    pub dhi: i32,
}

pub open spec fn probe_ok(q: Probe) -> bool {
    &&& q.p1len as int == q.p1@.len()
    &&& q.p2len as int == q.p2@.len()
    &&& q.two == (q.p1@ != q.p2@)
}

/// Per-slot counts of a row range.
#[derive(Clone, Copy)]
pub struct Counts {
    pub n0: u64,
    pub h0: u64,
    pub n1: u64,
    pub h1: u64,
}

// ------------------------------------------------------------------------------------------------ row conditions

/// Stage 1 condition: the date conditions of row `i`.
pub open spec fn p_dates(sv: StoresView, q: Probe) -> spec_fn(int) -> bool {
    |i: int| l_dates_ok(sv, q.dlo as int, q.dhi as int, i)
}

/// Stage 3 condition: the ship mode of row `i` is `$1`, or `$2` when it differs.
pub open spec fn p_mode(sv: StoresView, q: Probe) -> spec_fn(int) -> bool {
    |i: int| mode_at(sv, i) == q.p1@ || (q.two && mode_at(sv, i) == q.p2@)
}

/// Rows passing stages 1 and 3.
pub open spec fn p_qual(sv: StoresView, q: Probe) -> spec_fn(int) -> bool {
    and_pred(p_dates(sv, q), p_mode(sv, q))
}

/// The slot of a row passing stage 3.
pub open spec fn slot_of(sv: StoresView, q: Probe, i: int) -> u8 {
    if mode_at(sv, i) == q.p1@ { 0 } else { 1 }
}

/// The order of row `i` exists.
pub open spec fn has_order(sv: StoresView, i: int) -> bool {
    has_key(ok(sv), lok(sv)[i])
}

/// The order of row `i` has a high priority.
pub open spec fn high_order(sv: StoresView, i: int) -> bool {
    is_high(prio_at(sv, key_row(ok(sv), lok(sv)[i])))
}

/// Count terms of slot `s`: rows of the slot with an order (`t_n`), and with a high-priority order (`t_h`).
pub open spec fn t_n(sv: StoresView, q: Probe, s: u8) -> spec_fn(int) -> int {
    |i: int| if slot_of(sv, q, i) == s && has_order(sv, i) { 1int } else { 0int }
}

pub open spec fn t_h(sv: StoresView, q: Probe, s: u8) -> spec_fn(int) -> int {
    |i: int| if slot_of(sv, q, i) == s && has_order(sv, i) && high_order(sv, i) { 1int } else { 0int }
}

/// The range sum of a slot term over the rows passing stages 1 and 3.
pub open spec fn rs(sv: StoresView, q: Probe, lo: int, hi: int, f: spec_fn(int) -> int) -> int {
    range_sum(lo, hi, guard(p_qual(sv, q), f))
}

/// `acc` holds the counts of the rows `[lo, hi)`.
pub open spec fn acc_ok(acc: Counts, sv: StoresView, q: Probe, lo: int, hi: int) -> bool {
    &&& acc.n0 as int == rs(sv, q, lo, hi, t_n(sv, q, 0))
    &&& acc.h0 as int == rs(sv, q, lo, hi, t_h(sv, q, 0))
    &&& acc.n1 as int == rs(sv, q, lo, hi, t_n(sv, q, 1))
    &&& acc.h1 as int == rs(sv, q, lo, hi, t_h(sv, q, 1))
}

/// The counts of a range are at most its length.
pub proof fn lemma_rs_bound(sv: StoresView, q: Probe, lo: int, hi: int, f: spec_fn(int) -> int)
    requires lo <= hi, forall|i: int| 0 <= #[trigger] f(i) <= 1,
    ensures 0 <= rs(sv, q, lo, hi, f) <= hi - lo,
{
    let gf = guard(p_qual(sv, q), f);
    assert forall|i: int| lo <= i < hi implies 0 <= #[trigger] gf(i) <= 1 by {
        assert(0 <= f(i) <= 1);
    }
    lemma_range_sum_01(gf, lo, hi);
}

// ------------------------------------------------------------------------------------------------ 1: candidates

/// Bit `u` of a word mask at row `w` (rows `w..we`): the date conditions of row `w + u`.
pub open spec fn mask_ok(m: u64, sv: StoresView, q: Probe, w: int, we: int) -> bool {
    forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (u < we - w && l_dates_ok(sv, q.dlo as int, q.dhi as int, w + u))
}

/// The date conditions of 64 consecutive rows as a mask (branch-free; the compiler vectorizes it since the slice
/// lengths are known).
fn mask64(rc: &[i32], cm: &[i32], sh: &[i32], dlo: i32, dhi: i32) -> (m: u64)
    requires rc@.len() == 64, cm@.len() == 64, sh@.len() == 64,
    ensures
        forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (dlo <= rc@[u as int] < dhi && cm@[u as int] < rc@[u as int]
            && sh@[u as int] < cm@[u as int]),
    no_unwind
{
    let mut m: u64 = 0;
    let mut u: usize = 0;
    proof {
        assert forall|v: u64| v < 64 implies !#[trigger] bit(0u64, v) by { lemma_bit_zero(v); }
    }
    while u < 64
        invariant
            rc@.len() == 64, cm@.len() == 64, sh@.len() == 64, u <= 64,
            forall|v: u64| v < 64 ==> #[trigger] bit(m, v) == (v < u && dlo <= rc@[v as int] < dhi
                && cm@[v as int] < rc@[v as int] && sh@[v as int] < cm@[v as int]),
        decreases 64 - u,
    {
        let r = rc[u];
        let c = cm[u];
        let s = sh[u];
        let x = ((r >= dlo) as u64) & ((r < dhi) as u64) & ((c < r) as u64) & ((s < c) as u64);
        proof {
            let (a1, a2, a3, a4) = ((r >= dlo) as u64, (r < dhi) as u64, (c < r) as u64, (s < c) as u64);
            assert(x <= 1 && (x == 1) == (a1 == 1 && a2 == 1 && a3 == 1 && a4 == 1)) by (bit_vector)
                requires a1 <= 1, a2 <= 1, a3 <= 1, a4 <= 1, x == a1 & a2 & a3 & a4;
        }
        let ghost m0 = m;
        m = m | (x << (u as u64));
        proof {
            assert forall|v: u64| v < 64 implies #[trigger] bit(m, v) == (v < u + 1 && dlo <= rc@[v as int] < dhi
                && cm@[v as int] < rc@[v as int] && sh@[v as int] < cm@[v as int]) by {
                lemma_bit_set(m0, x, u as u64, v);
            }
        }
        u = u + 1;
    }
    m
}

/// The date mask of rows `w..we` (at most 64), one row at a time.
fn mask_tail(c: &Cols, q: &Probe, w: usize, we: usize, Ghost(sv): Ghost<StoresView>) -> (m: u64)
    requires cols_ok(*c, sv), w < we <= c.nl, we - w <= 64,
    ensures mask_ok(m, sv, *q, w as int, we as int),
    no_unwind
{
    let mut m: u64 = 0;
    let mut j = w;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
    }
    while j < we
        invariant
            cols_ok(*c, sv), w <= j <= we <= c.nl, we - w <= 64,
            forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (u < j - w && l_dates_ok(sv, q.dlo as int, q.dhi as int, w + u)),
        decreases we - j,
    {
        let r = c.rcpt[j];
        let cm = c.cmt[j];
        let s = c.ship[j];
        let x = (r >= q.dlo && r < q.dhi && cm < r && s < cm) as u64;
        let t = (j - w) as u64;
        let ghost m0 = m;
        m = m | (x << t);
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (u < j + 1 - w && l_dates_ok(sv, q.dlo as int, q.dhi as int, w + u)) by {
                lemma_bit_set(m0, x, t, u);
            }
        }
        j = j + 1;
    }
    m
}

/// The date mask of the word at row `w` (rows `w..we`): `mask64` over the slices of a full word, else `mask_tail`.
fn word_mask(c: &Cols, q: &Probe, w: usize, we: usize, Ghost(sv): Ghost<StoresView>) -> (m: u64)
    requires cols_ok(*c, sv), w < we <= c.nl, we - w <= 64,
    ensures mask_ok(m, sv, *q, w as int, we as int),
    no_unwind
{
    if we - w == 64 {
        let (_, t1) = c.rcpt.split_at(w);
        let (rc, _) = t1.split_at(64);
        let (_, t2) = c.cmt.split_at(w);
        let (cm, _) = t2.split_at(64);
        let (_, t3) = c.ship.split_at(w);
        let (sh, _) = t3.split_at(64);
        let m = mask64(rc, cm, sh, q.dlo, q.dhi);
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (u < we - w && l_dates_ok(sv, q.dlo as int, q.dhi as int, w + u)) by {
                assert(rc@[u as int] == t1@[u as int] && t1@[u as int] == lrd(sv)[w + u]);
                assert(cm@[u as int] == t2@[u as int] && t2@[u as int] == lcd(sv)[w + u]);
                assert(sh@[u as int] == t3@[u as int] && t3@[u as int] == lsd(sv)[w + u]);
            }
        }
        m
    } else {
        mask_tail(c, q, w, we, Ghost(sv))
    }
}

/// Stage 1: the rows of `[base, end)` passing the date conditions, as offsets from `base` in `cand`.
fn collect_cands(c: &Cols, q: &Probe, base: usize, end: usize, cand: &mut Vec<u32>, table: &[u8; 64],
    Ghost(sv): Ghost<StoresView>) -> (nc: usize)
    requires
        cols_ok(*c, sv),
        base <= end <= c.nl,
        end - base <= BLOCK,
        old(cand)@.len() == BLOCK,
        table@.len() == 64,
    ensures
        final(cand)@.len() == BLOCK,
        sel_matches(final(cand)@, nc as int, base as int, range_filter(base as int, end as int, p_dates(sv, *q))),
    no_unwind
{
    let ghost p = p_dates(sv, *q);
    let mut nc: usize = 0;
    let mut w = base;
    proof {
        assert(range_filter(base as int, base as int, p) =~= Seq::<int>::empty());
    }
    while w < end
        invariant
            cols_ok(*c, sv),
            base <= w <= end <= c.nl,
            end - base <= BLOCK,
            cand@.len() == BLOCK,
            table@.len() == 64,
            p == p_dates(sv, *q),
            nc <= w - base,
            sel_matches(cand@, nc as int, base as int, range_filter(base as int, w as int, p)),
        decreases end - w,
    {
        let we = if end - w >= 64 { w + 64 } else { end };
        let mut m = word_mask(c, q, w, we, Ghost(sv));
        // `pos`: the rows `w .. w + pos` of the word are listed (bits below `pos` are cleared).
        let ghost mut pos: int = 0;
        while m != 0
            invariant
                cols_ok(*c, sv),
                base <= w < we <= end <= c.nl,
                we - w <= 64,
                end - base <= BLOCK,
                cand@.len() == BLOCK,
                table@.len() == 64,
                p == p_dates(sv, *q),
                0 <= pos <= we - w,
                nc <= w - base + pos,
                forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (pos <= u < we - w && l_dates_ok(sv, q.dlo as int, q.dhi as int, w + u)),
                sel_matches(cand@, nc as int, base as int, range_filter(base as int, w + pos, p)),
            decreases we - w - pos,
        {
            proof { lemma_first_bit(m); }
            let t = tz64(m, table) as u64;
            proof {
                assert(bit(m, t));
                assert forall|r: int| w + pos <= r < w + t implies !#[trigger] p(r) by {
                    let u = (r - w) as u64;
                    assert(!bit(m, u));
                }
                lemma_range_filter_skip(base as int, w + pos, w + t, p);
            }
            let ghost m1 = m;
            m = m & (m - 1);
            proof {
                assert(m1 - 1 == sub(m1, 1));
                assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (t + 1 <= u < we - w && l_dates_ok(sv, q.dlo as int, q.dhi as int, w + u)) by {
                    lemma_clear_lowest(m1, t, u);
                }
            }
            let off = (w - base + t as usize) as u32;
            proof {
                lemma_sel_write(cand@, nc as int, base as int, range_filter(base as int, w + t, p), off, true);
                assert(range_filter(base as int, w + t + 1, p) == range_filter(base as int, w + t, p).push(w + t));
            }
            cand[nc] = off;
            nc = nc + 1;
            proof { pos = t + 1; }
        }
        proof {
            assert forall|r: int| w + pos <= r < we implies !#[trigger] p(r) by {
                let u = (r - w) as u64;
                assert(!bit(m, u)) by { lemma_bit_zero(u); }
            }
            lemma_range_filter_skip(base as int, w + pos, we as int, p);
        }
        w = we;
    }
    nc
}

// ------------------------------------------------------------------------------------------------ 2, 3: ship modes

/// The listed rows lie in `[0, nl)`.
pub open spec fn rows_in(s: Seq<int>, n: int) -> bool {
    forall|t: int| 0 <= t < s.len() ==> 0 <= #[trigger] s[t] < n
}

/// Stage 2: the `l_shipmode` offset `ma[t]` and length `ml[t]` of each listed row `s[t]`.
pub open spec fn offs_ok(ma: Seq<usize>, ml: Seq<usize>, s: Seq<int>, sv: StoresView) -> bool {
    forall|t: int| 0 <= t < s.len() ==> {
        &&& #[trigger] ma[t] as int == lmode(sv).offsets[s[t]]
        &&& ml[t] as int == lmode(sv).offsets[s[t] + 1] - lmode(sv).offsets[s[t]]
    }
}

fn mode_offsets(c: &Cols, base: usize, nc: usize, cand: &Vec<u32>, ma: &mut Vec<usize>, ml: &mut Vec<usize>,
    Ghost(s): Ghost<Seq<int>>, Ghost(sv): Ghost<StoresView>)
    requires
        cols_ok(*c, sv),
        sel_matches(cand@, nc as int, base as int, s),
        rows_in(s, c.nl as int),
        old(ma)@.len() == BLOCK, old(ml)@.len() == BLOCK, nc <= BLOCK,
    ensures
        final(ma)@.len() == BLOCK, final(ml)@.len() == BLOCK,
        offs_ok(final(ma)@, final(ml)@, s, sv),
    no_unwind
{
    let mut t: usize = 0;
    while t < nc
        invariant
            cols_ok(*c, sv),
            sel_matches(cand@, nc as int, base as int, s),
            rows_in(s, c.nl as int),
            ma@.len() == BLOCK, ml@.len() == BLOCK, nc <= BLOCK, t <= nc,
            forall|u: int| 0 <= u < t ==> {
                &&& #[trigger] ma@[u] as int == lmode(sv).offsets[s[u]]
                &&& ml@[u] as int == lmode(sv).offsets[s[u] + 1] - lmode(sv).offsets[s[u]]
            },
        decreases nc - t,
    {
        let i = base + cand[t] as usize;
        proof {
            assert(i as int == s[t as int]);
            assert(0 <= lmode(sv).offsets[i as int] <= lmode(sv).offsets[i + 1]);
        }
        let a = c.moff[i];
        let b = c.moff[i + 1];
        let ghost (ma0, ml0) = (ma@, ml@);
        ma[t] = a as usize;
        ml[t] = (b - a) as usize;
        proof {
            assert forall|u: int| 0 <= u < t + 1 implies {
                &&& #[trigger] ma@[u] as int == lmode(sv).offsets[s[u]]
                &&& ml@[u] as int == lmode(sv).offsets[s[u] + 1] - lmode(sv).offsets[s[u]]
            } by {
                if u < t {
                    assert(ma@[u] == ma0[u] && ml@[u] == ml0[u]);
                }
            }
        }
        t = t + 1;
    }
}

/// Stage 2b: `mf[t]` is the `l_shipmode` byte at offset `ma[t]` (0 when the offset is past the bytes).
pub open spec fn first_ok(mf: Seq<u8>, ma: Seq<usize>, n: int, b: Seq<u8>) -> bool {
    forall|t: int| 0 <= t < n ==> #[trigger] mf[t] == if (ma[t] as int) < b.len() { b[ma[t] as int] } else { 0u8 }
}

/// Stage 2b: the first ship-mode byte of each listed row. One independent load per row, so the cache misses overlap;
/// stage 3 then rules out most rows by length and first byte, and compares the bytes of the rest from the cache.
fn mode_first(c: &Cols, nc: usize, ma: &Vec<usize>, mf: &mut Vec<u8>, Ghost(sv): Ghost<StoresView>)
    requires
        cols_ok(*c, sv),
        ma@.len() == BLOCK, old(mf)@.len() == BLOCK, nc <= BLOCK,
    ensures
        final(mf)@.len() == BLOCK,
        first_ok(final(mf)@, ma@, nc as int, c.mbytes@),
    no_unwind
{
    let mut t: usize = 0;
    while t < nc
        invariant
            cols_ok(*c, sv),
            ma@.len() == BLOCK, mf@.len() == BLOCK, nc <= BLOCK, t <= nc,
            first_ok(mf@, ma@, t as int, c.mbytes@),
        decreases nc - t,
    {
        let a = ma[t];
        let x = if a < c.nmb { c.mbytes[a] } else { 0u8 };
        let ghost mf0 = mf@;
        mf[t] = x;
        proof {
            assert forall|u: int| 0 <= u < t + 1 implies #[trigger] mf@[u]
                == if (ma@[u] as int) < c.mbytes@.len() { c.mbytes@[ma@[u] as int] } else { 0u8 } by {
                if u < t {
                    assert(mf@[u] == mf0[u]);
                }
            }
        }
        t = t + 1;
    }
}

/// A row whose ship mode is `p` has `p`'s length, and (when `p` is not empty) `p`'s first byte at its offset.
proof fn lemma_mode_prefix(sv: StoresView, i: int, a: usize, l: usize, f: u8, p: Seq<u8>)
    requires
        0 <= lmode(sv).offsets[i] <= lmode(sv).offsets[i + 1] <= lmode(sv).bytes.len(),
        a as int == lmode(sv).offsets[i],
        l as int == lmode(sv).offsets[i + 1] - lmode(sv).offsets[i],
        f == if (a as int) < lmode(sv).bytes.len() { lmode(sv).bytes[a as int] } else { 0u8 },
        mode_at(sv, i) == p,
    ensures
        l == p.len(),
        p.len() > 0 ==> f == p[0],
{
    assert(mode_at(sv, i).len() == l);
    if p.len() > 0 {
        assert(mode_at(sv, i)[0] == lmode(sv).bytes[a as int]);
    }
}

/// `b[start .. start + plen]` is `p` (`plen` its length).
fn bytes_eq(b: &[u8], blen: usize, start: usize, p: &[u8], plen: usize) -> (r: bool)
    requires blen == b@.len(), plen == p@.len(), start + plen <= blen,
    ensures r == (b@.subrange(start as int, start + plen) == p@),
    no_unwind
{
    let mut j: usize = 0;
    while j < plen
        invariant
            blen == b@.len(), plen == p@.len(), start + plen <= blen, j <= plen,
            b@.subrange(start as int, start + j) == p@.subrange(0, j as int),
        decreases plen - j,
    {
        if b[start + j] != p[j] {
            proof {
                assert(b@.subrange(start as int, start + plen)[j as int] == b@[start + j]);
            }
            return false;
        }
        proof {
            assert(b@.subrange(start as int, start + j + 1) =~= b@.subrange(start as int, start + j).push(b@[start + j]));
            assert(p@.subrange(0, j + 1) =~= p@.subrange(0, j as int).push(p@[j as int]));
        }
        j = j + 1;
    }
    proof {
        assert(p@.subrange(0, plen as int) =~= p@);
    }
    true
}

/// The ship mode of row `i` is `p` exactly when the stored length is `p`'s and the bytes match.
fn mode_is(c: &Cols, a: usize, l: usize, p: &[u8], plen: usize, Ghost(i): Ghost<int>, Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires
        cols_ok(*c, sv), 0 <= i < c.nl, plen == p@.len(),
        a as int == lmode(sv).offsets[i],
        l as int == lmode(sv).offsets[i + 1] - lmode(sv).offsets[i],
    ensures r == (mode_at(sv, i) == p@),
    no_unwind
{
    proof {
        assert(0 <= lmode(sv).offsets[i] <= lmode(sv).offsets[i + 1] <= lmode(sv).bytes.len());
    }
    if l != plen {
        proof {
            if mode_at(sv, i) == p@ {
                assert(mode_at(sv, i).len() == l);
            }
        }
        false
    } else {
        bytes_eq(c.mbytes, c.nmb, a, p, plen)
    }
}

/// Stage 3: the listed rows `s` whose ship mode is `$1`, or `$2` when it differs (`seq_filter(s, p_mode)`), as
/// offsets in `qrow`, with their slots in `qslot`. A row is compared byte by byte only when its length and first
/// byte (`mf`) match a mode, which keeps the branches of the comparison predictable.
fn mode_select(c: &Cols, q: &Probe, base: usize, nc: usize, cand: &Vec<u32>, ma: &Vec<usize>, ml: &Vec<usize>,
    mf: &Vec<u8>, qrow: &mut Vec<u32>, qslot: &mut Vec<u8>, Ghost(s): Ghost<Seq<int>>, Ghost(sv): Ghost<StoresView>)
    -> (nq: usize)
    requires
        cols_ok(*c, sv),
        probe_ok(*q),
        sel_matches(cand@, nc as int, base as int, s),
        rows_in(s, c.nl as int),
        offs_ok(ma@, ml@, s, sv),
        first_ok(mf@, ma@, nc as int, c.mbytes@),
        ma@.len() == BLOCK, ml@.len() == BLOCK, mf@.len() == BLOCK, nc <= BLOCK,
        old(qrow)@.len() == BLOCK, old(qslot)@.len() == BLOCK,
    ensures
        final(qrow)@.len() == BLOCK, final(qslot)@.len() == BLOCK,
        nq <= nc,
        sel_matches(final(qrow)@, nq as int, base as int, seq_filter(s, p_mode(sv, *q))),
        forall|t: int| 0 <= t < nq ==> #[trigger] final(qslot)@[t] == slot_of(sv, *q, seq_filter(s, p_mode(sv, *q))[t]),
    no_unwind
{
    let ghost pm = p_mode(sv, *q);
    // First bytes of the two modes (0 for an empty mode, whose first byte is never compared).
    let f1: u8 = if q.p1len > 0 { q.p1[0] } else { 0u8 };
    let f2: u8 = if q.p2len > 0 { q.p2[0] } else { 0u8 };
    let mut nq: usize = 0;
    let mut t: usize = 0;
    proof {
        assert(s.take(0) =~= Seq::<int>::empty());
    }
    while t < nc
        invariant
            cols_ok(*c, sv),
            probe_ok(*q),
            sel_matches(cand@, nc as int, base as int, s),
            rows_in(s, c.nl as int),
            offs_ok(ma@, ml@, s, sv),
            first_ok(mf@, ma@, nc as int, c.mbytes@),
            ma@.len() == BLOCK, ml@.len() == BLOCK, mf@.len() == BLOCK, nc <= BLOCK,
            qrow@.len() == BLOCK, qslot@.len() == BLOCK,
            q.p1len > 0 ==> f1 == q.p1@[0],
            q.p2len > 0 ==> f2 == q.p2@[0],
            pm == p_mode(sv, *q),
            t <= nc, nq <= t,
            sel_matches(qrow@, nq as int, base as int, seq_filter(s.take(t as int), pm)),
            forall|u: int| 0 <= u < nq ==> #[trigger] qslot@[u] == slot_of(sv, *q, seq_filter(s.take(t as int), pm)[u]),
        decreases nc - t,
    {
        let ghost i = s[t as int];
        let a = ma[t];
        let l = ml[t];
        let f = mf[t];
        // Necessary conditions of a match: the length, and the first byte of a nonempty mode.
        let pre1 = l == q.p1len && (q.p1len == 0 || f == f1);
        let pre2 = q.two && l == q.p2len && (q.p2len == 0 || f == f2);
        proof {
            assert(0 <= lmode(sv).offsets[i] <= lmode(sv).offsets[i + 1] <= lmode(sv).bytes.len());
            assert(f == if (a as int) < lmode(sv).bytes.len() { lmode(sv).bytes[a as int] } else { 0u8 });
            if mode_at(sv, i) == q.p1@ {
                lemma_mode_prefix(sv, i, a, l, f, q.p1@);
            }
            if mode_at(sv, i) == q.p2@ {
                lemma_mode_prefix(sv, i, a, l, f, q.p2@);
            }
        }
        let mut is1 = false;
        let mut is2 = false;
        if pre1 || pre2 {
            is1 = pre1 && mode_is(c, a, l, q.p1, q.p1len, Ghost(i), Ghost(sv));
            is2 = pre2 && mode_is(c, a, l, q.p2, q.p2len, Ghost(i), Ghost(sv));
        }
        proof {
            assert(is1 == (mode_at(sv, i) == q.p1@));
            assert(is2 == (q.two && mode_at(sv, i) == q.p2@));
        }
        let keep = is1 || is2;
        let slot: u8 = if is1 { 0 } else { 1 };
        let off = cand[t];
        let ghost f0 = seq_filter(s.take(t as int), pm);
        proof {
            assert(keep == pm(i));
            assert(base + off as int == i);
            lemma_take_step(s, t as int);
            lemma_seq_filter_push(s.take(t as int), i, pm);
            lemma_sel_write(qrow@, nq as int, base as int, f0, off, keep);
        }
        let ghost qslot0 = qslot@;
        qrow[nq] = off;
        qslot[nq] = slot;
        proof {
            let f1 = seq_filter(s.take(t + 1), pm);
            assert forall|u: int| 0 <= u < (if keep { nq + 1 } else { nq as int }) implies
                #[trigger] qslot@[u] == slot_of(sv, *q, f1[u]) by {
                if u < nq {
                    assert(qslot@[u] == qslot0[u]);
                    assert(f1[u] == f0[u]);
                } else {
                    assert(f1[u] == i);
                }
            }
        }
        nq = nq + if keep { 1usize } else { 0usize };
        t = t + 1;
    }
    proof {
        assert(s.take(nc as int) =~= s);
    }
    nq
}

// ------------------------------------------------------------------------------------------------ 4, 5: orders

/// The orders row where dbgen puts key `k` (`32 * (i / 8) + i % 8` for the `i`-th order, counting from 1), or `no`
/// when `k` is not of that form within the table. A guess: the caller checks `o_orderkey` there.
fn dbgen_row(k: i64, no: usize) -> (g: usize)
    no_unwind
{
    if k > 0 {
        let ku = k as u64;
        let low = ku % 32;
        if low < 8 {
            let i = (ku / 32) * 8 + low;
            if i >= 1 && i - 1 < (no as u64) {
                return (i - 1) as usize;
            }
        }
    }
    no
}

/// Stage 4: the order key `qkey[t]` of each listed row `s[t]`, and its dbgen row guess `qg[t]`.
fn order_keys(c: &Cols, base: usize, nq: usize, qrow: &Vec<u32>, qkey: &mut Vec<i64>, qg: &mut Vec<usize>,
    Ghost(s): Ghost<Seq<int>>, Ghost(sv): Ghost<StoresView>)
    requires
        cols_ok(*c, sv),
        sel_matches(qrow@, nq as int, base as int, s),
        rows_in(s, c.nl as int),
        old(qkey)@.len() == BLOCK, old(qg)@.len() == BLOCK, nq <= BLOCK,
    ensures
        final(qkey)@.len() == BLOCK, final(qg)@.len() == BLOCK,
        forall|t: int| 0 <= t < nq ==> #[trigger] final(qkey)@[t] == lok(sv)[s[t]],
    no_unwind
{
    let mut t: usize = 0;
    while t < nq
        invariant
            cols_ok(*c, sv),
            sel_matches(qrow@, nq as int, base as int, s),
            rows_in(s, c.nl as int),
            qkey@.len() == BLOCK, qg@.len() == BLOCK, nq <= BLOCK, t <= nq,
            forall|u: int| 0 <= u < t ==> #[trigger] qkey@[u] == lok(sv)[s[u]],
        decreases nq - t,
    {
        let i = base + qrow[t] as usize;
        proof { assert(i as int == s[t as int]); }
        let k = c.lokey[i];
        qkey[t] = k;
        qg[t] = dbgen_row(k, c.no);
        t = t + 1;
    }
}

/// The orders row of key `k` by a linear search (`no` when there is none).
fn order_scan(c: &Cols, k: i64, Ghost(sv): Ghost<StoresView>) -> (j: usize)
    requires cols_ok(*c, sv),
    ensures
        j <= c.no,
        j < c.no ==> ok(sv)[j as int] == k,
        j == c.no ==> !has_key(ok(sv), k),
    no_unwind
{
    let mut j: usize = 0;
    while j < c.no
        invariant cols_ok(*c, sv), j <= c.no, forall|r: int| 0 <= r < j ==> ok(sv)[r] != k,
        decreases c.no - j,
    {
        if c.okey[j] == k {
            return j;
        }
        j = j + 1;
    }
    j
}

/// The row of an existing key is `key_row` (the key column is duplicate-free).
proof fn lemma_key_row(sv: StoresView, k: i64, j: int)
    requires keys_unique(ok(sv)), 0 <= j < n_o(sv), ok(sv)[j] == k,
    ensures has_key(ok(sv), k), key_row(ok(sv), k) == j,
{
    assert(has_key(ok(sv), k));
    let r = key_row(ok(sv), k);
    assert(ok(sv)[r] == ok(sv)[j]);
}

/// Stage 5: per listed key `keys[t]`: `pl[t] >= 0` exactly when its order exists, and then `pa[t]`, `pl[t]` are the
/// offset and length of the order's `o_orderpriority`.
pub open spec fn prio_ok(pa: Seq<usize>, pl: Seq<i64>, keys: Seq<i64>, n: int, sv: StoresView) -> bool {
    forall|t: int| 0 <= t < n ==> {
        &&& (#[trigger] pl[t] >= 0) == has_key(ok(sv), keys[t])
        &&& has_key(ok(sv), keys[t]) ==> {
            let j = key_row(ok(sv), keys[t]);
            &&& 0 <= j < n_o(sv)
            &&& pa[t] as int == oprio(sv).offsets[j]
            &&& pl[t] as int == oprio(sv).offsets[j + 1] - oprio(sv).offsets[j]
        }
    }
}

fn order_prios(c: &Cols, nq: usize, qkey: &Vec<i64>, qg: &Vec<usize>, pa: &mut Vec<usize>, pl: &mut Vec<i64>,
    Ghost(sv): Ghost<StoresView>)
    requires
        cols_ok(*c, sv),
        qkey@.len() == BLOCK, qg@.len() == BLOCK, nq <= BLOCK,
        old(pa)@.len() == BLOCK, old(pl)@.len() == BLOCK,
    ensures
        final(pa)@.len() == BLOCK, final(pl)@.len() == BLOCK,
        prio_ok(final(pa)@, final(pl)@, qkey@, nq as int, sv),
    no_unwind
{
    let mut t: usize = 0;
    while t < nq
        invariant
            cols_ok(*c, sv),
            qkey@.len() == BLOCK, qg@.len() == BLOCK, nq <= BLOCK, t <= nq,
            pa@.len() == BLOCK, pl@.len() == BLOCK,
            prio_ok(pa@, pl@, qkey@, t as int, sv),
        decreases nq - t,
    {
        let k = qkey[t];
        let g0 = qg[t];
        let g = if g0 < c.no && c.okey[g0] == k { g0 } else { order_scan(c, k, Ghost(sv)) };
        let ghost (pa0, pl0) = (pa@, pl@);
        if g < c.no {
            proof {
                lemma_key_row(sv, k, g as int);
                assert(0 <= oprio(sv).offsets[g as int] <= oprio(sv).offsets[g + 1]);
            }
            let a = c.poff[g];
            let b = c.poff[g + 1];
            pa[t] = a as usize;
            pl[t] = b - a;
        } else {
            pa[t] = 0;
            pl[t] = -1;
        }
        proof {
            assert forall|u: int| 0 <= u < t + 1 implies {
                &&& (#[trigger] pl@[u] >= 0) == has_key(ok(sv), qkey@[u])
                &&& has_key(ok(sv), qkey@[u]) ==> {
                    let j = key_row(ok(sv), qkey@[u]);
                    &&& 0 <= j < n_o(sv)
                    &&& pa@[u] as int == oprio(sv).offsets[j]
                    &&& pl@[u] as int == oprio(sv).offsets[j + 1] - oprio(sv).offsets[j]
                }
            } by {
                if u < t {
                    assert(pa@[u] == pa0[u] && pl@[u] == pl0[u]);
                }
            }
        }
        t = t + 1;
    }
}

// ------------------------------------------------------------------------------------------------ 6: counts

/// The priority at bytes `a .. a + l` of `o_orderpriority` is high (`1-URGENT` or `2-HIGH`).
fn prio_high(c: &Cols, a: usize, l: i64, Ghost(sv): Ghost<StoresView>) -> (h: bool)
    requires cols_ok(*c, sv), l >= 0, a + l <= c.npb,
    ensures h == is_high(oprio(sv).bytes.subrange(a as int, a + l)),
    no_unwind
{
    let ghost b = oprio(sv).bytes.subrange(a as int, a + l);
    if l == 8 {
        let r = c.pbytes[a] == 49u8 && c.pbytes[a + 1] == 45u8 && c.pbytes[a + 2] == 85u8 && c.pbytes[a + 3] == 82u8
            && c.pbytes[a + 4] == 71u8 && c.pbytes[a + 5] == 69u8 && c.pbytes[a + 6] == 78u8 && c.pbytes[a + 7] == 84u8;
        proof {
            if r {
                assert(b =~= urgent());
            } else if b == urgent() {
                assert(b[0] == 49u8 && b[1] == 45u8 && b[2] == 85u8 && b[3] == 82u8);
                assert(b[4] == 71u8 && b[5] == 69u8 && b[6] == 78u8 && b[7] == 84u8);
            }
            assert(b.len() != high2().len());
        }
        r
    } else if l == 6 {
        let r = c.pbytes[a] == 50u8 && c.pbytes[a + 1] == 45u8 && c.pbytes[a + 2] == 72u8 && c.pbytes[a + 3] == 73u8
            && c.pbytes[a + 4] == 71u8 && c.pbytes[a + 5] == 72u8;
        proof {
            if r {
                assert(b =~= high2());
            } else if b == high2() {
                assert(b[0] == 50u8 && b[1] == 45u8 && b[2] == 72u8 && b[3] == 73u8);
                assert(b[4] == 71u8 && b[5] == 72u8);
            }
            assert(b.len() != urgent().len());
        }
        r
    } else {
        proof {
            assert(b.len() != urgent().len());
            assert(b.len() != high2().len());
        }
        false
    }
}

/// The counts `acc` hold the totals `n0 .. h1` plus the slot terms of the first `t` listed rows of `s`.
pub open spec fn partial_ok(acc: Counts, sv: StoresView, q: Probe, s: Seq<int>, t: int, n0: int, h0: int, n1: int, h1: int) -> bool {
    &&& acc.n0 as int == n0 + seq_sum(s.take(t), t_n(sv, q, 0))
    &&& acc.h0 as int == h0 + seq_sum(s.take(t), t_h(sv, q, 0))
    &&& acc.n1 as int == n1 + seq_sum(s.take(t), t_n(sv, q, 1))
    &&& acc.h1 as int == h1 + seq_sum(s.take(t), t_h(sv, q, 1))
}

/// The slot terms are 0/1.
proof fn lemma_terms_01(sv: StoresView, q: Probe)
    ensures
        forall|i: int| 0 <= #[trigger] t_n(sv, q, 0)(i) <= 1,
        forall|i: int| 0 <= #[trigger] t_h(sv, q, 0)(i) <= 1,
        forall|i: int| 0 <= #[trigger] t_n(sv, q, 1)(i) <= 1,
        forall|i: int| 0 <= #[trigger] t_h(sv, q, 1)(i) <= 1,
{
}

/// A sum of 0/1 terms over a prefix of a list is at most the prefix length.
proof fn lemma_prefix_bound(s: Seq<int>, t: int, f: spec_fn(int) -> int)
    requires 0 <= t <= s.len(), forall|i: int| 0 <= #[trigger] f(i) <= 1,
    ensures 0 <= seq_sum(s.take(t), f) <= t,
{
    let p = s.take(t);
    assert forall|u: int| 0 <= u < p.len() implies 0 <= #[trigger] f(p[u]) <= 1 by {}
    lemma_seq_sum_01(p, f);
}

/// Stage 6: adds the slot terms of the listed rows `s` to `acc`.
fn count_rows(c: &Cols, nq: usize, qslot: &Vec<u8>, pa: &Vec<usize>, pl: &Vec<i64>, qkey: &Vec<i64>, acc: &mut Counts,
    Ghost(s): Ghost<Seq<int>>, Ghost(n0): Ghost<int>, Ghost(h0): Ghost<int>, Ghost(n1): Ghost<int>, Ghost(h1): Ghost<int>,
    Ghost(sv): Ghost<StoresView>, Ghost(q): Ghost<Probe>)
    requires
        cols_ok(*c, sv),
        s.len() == nq, rows_in(s, c.nl as int),
        qslot@.len() == BLOCK, pa@.len() == BLOCK, pl@.len() == BLOCK, qkey@.len() == BLOCK, nq <= BLOCK,
        forall|t: int| 0 <= t < nq ==> #[trigger] qslot@[t] == slot_of(sv, q, s[t]),
        forall|t: int| 0 <= t < nq ==> #[trigger] qkey@[t] == lok(sv)[s[t]],
        prio_ok(pa@, pl@, qkey@, nq as int, sv),
        partial_ok(*old(acc), sv, q, s, 0, n0, h0, n1, h1),
        0 <= n0, 0 <= h0, 0 <= n1, 0 <= h1,
        n0 + nq <= u64::MAX, h0 + nq <= u64::MAX, n1 + nq <= u64::MAX, h1 + nq <= u64::MAX,
    ensures
        partial_ok(*final(acc), sv, q, s, nq as int, n0, h0, n1, h1),
    no_unwind
{
    let mut t: usize = 0;
    proof { lemma_terms_01(sv, q); }
    while t < nq
        invariant
            cols_ok(*c, sv),
            s.len() == nq, rows_in(s, c.nl as int),
            qslot@.len() == BLOCK, pa@.len() == BLOCK, pl@.len() == BLOCK, qkey@.len() == BLOCK, nq <= BLOCK,
            forall|u: int| 0 <= u < nq ==> #[trigger] qslot@[u] == slot_of(sv, q, s[u]),
            forall|u: int| 0 <= u < nq ==> #[trigger] qkey@[u] == lok(sv)[s[u]],
            prio_ok(pa@, pl@, qkey@, nq as int, sv),
            t <= nq,
            partial_ok(*acc, sv, q, s, t as int, n0, h0, n1, h1),
            0 <= n0, 0 <= h0, 0 <= n1, 0 <= h1,
            n0 + nq <= u64::MAX, h0 + nq <= u64::MAX, n1 + nq <= u64::MAX, h1 + nq <= u64::MAX,
            forall|i: int| 0 <= #[trigger] t_n(sv, q, 0)(i) <= 1,
            forall|i: int| 0 <= #[trigger] t_h(sv, q, 0)(i) <= 1,
            forall|i: int| 0 <= #[trigger] t_n(sv, q, 1)(i) <= 1,
            forall|i: int| 0 <= #[trigger] t_h(sv, q, 1)(i) <= 1,
        decreases nq - t,
    {
        let ghost i = s[t as int];
        let l = pl[t];
        proof {
            lemma_take_step(s, t as int);
            lemma_seq_sum_push(s.take(t as int), i, t_n(sv, q, 0));
            lemma_seq_sum_push(s.take(t as int), i, t_h(sv, q, 0));
            lemma_seq_sum_push(s.take(t as int), i, t_n(sv, q, 1));
            lemma_seq_sum_push(s.take(t as int), i, t_h(sv, q, 1));
            lemma_prefix_bound(s, t + 1, t_n(sv, q, 0));
            lemma_prefix_bound(s, t + 1, t_h(sv, q, 0));
            lemma_prefix_bound(s, t + 1, t_n(sv, q, 1));
            lemma_prefix_bound(s, t + 1, t_h(sv, q, 1));
            assert(qkey@[t as int] == lok(sv)[i]);
            assert((l >= 0) == has_order(sv, i));
        }
        if l >= 0 {
            let a = pa[t];
            let ghost j = key_row(ok(sv), lok(sv)[i]);
            proof {
                assert(0 <= oprio(sv).offsets[j] <= oprio(sv).offsets[j + 1] <= oprio(sv).bytes.len());
            }
            let high = prio_high(c, a, l, Ghost(sv));
            proof {
                assert(oprio(sv).bytes.subrange(a as int, a + l) == prio_at(sv, j));
                assert(high == high_order(sv, i));
            }
            let h: u64 = if high { 1 } else { 0 };
            if qslot[t] == 0 {
                acc.n0 = acc.n0 + 1;
                acc.h0 = acc.h0 + h;
            } else {
                acc.n1 = acc.n1 + 1;
                acc.h1 = acc.h1 + h;
            }
        }
        t = t + 1;
    }
    proof {
        assert(s.take(nq as int) =~= s);
    }
}

// ------------------------------------------------------------------------------------------------ the range

/// The scratch buffers of a scan (each `BLOCK` entries).
pub struct Bufs {
    pub cand: Vec<u32>,
    pub ma: Vec<usize>,
    pub ml: Vec<usize>,
    pub mf: Vec<u8>,
    pub qrow: Vec<u32>,
    pub qslot: Vec<u8>,
    pub qkey: Vec<i64>,
    pub qg: Vec<usize>,
    pub pa: Vec<usize>,
    pub pl: Vec<i64>,
}

pub open spec fn bufs_ok(b: Bufs) -> bool {
    &&& b.cand@.len() == BLOCK && b.ma@.len() == BLOCK && b.ml@.len() == BLOCK && b.mf@.len() == BLOCK
    &&& b.qrow@.len() == BLOCK && b.qslot@.len() == BLOCK && b.qkey@.len() == BLOCK
    &&& b.qg@.len() == BLOCK && b.pa@.len() == BLOCK && b.pl@.len() == BLOCK
}

/// Allocates the scratch buffers (on the calling thread; zeroed allocations, so their pages are first touched by the
/// worker that uses them).
pub fn new_bufs() -> (b: Bufs)
    ensures bufs_ok(b),
{
    Bufs {
        cand: vec![0u32; BLOCK],
        ma: vec![0usize; BLOCK],
        ml: vec![0usize; BLOCK],
        mf: vec![0u8; BLOCK],
        qrow: vec![0u32; BLOCK],
        qslot: vec![0u8; BLOCK],
        qkey: vec![0i64; BLOCK],
        qg: vec![0usize; BLOCK],
        pa: vec![0usize; BLOCK],
        pl: vec![0i64; BLOCK],
    }
}

/// One block `[base, end)`: its listed rows are `range_filter(base, end, p_qual)`, and the counts of `[lo, base)`
/// become those of `[lo, end)`.
proof fn lemma_block_sums(sv: StoresView, q: Probe, lo: int, base: int, end: int, f: spec_fn(int) -> int)
    requires lo <= base <= end,
    ensures
        rs(sv, q, lo, end, f) == rs(sv, q, lo, base, f) + seq_sum(seq_filter(range_filter(base, end, p_dates(sv, q)), p_mode(sv, q)), f),
{
    lemma_filter_range_filter(base, end, p_dates(sv, q), p_mode(sv, q));
    lemma_sum_range_filter(base, end, p_qual(sv, q), f);
    lemma_range_sum_split(guard(p_qual(sv, q), f), lo, base, end);
}

/// The counts of the rows `[lo, hi)`.
pub fn scan_range(c: &Cols, q: &Probe, lo: usize, hi: usize, bf: Bufs, Ghost(sv): Ghost<StoresView>) -> (acc: Counts)
    requires cols_ok(*c, sv), probe_ok(*q), lo <= hi <= c.nl, bufs_ok(bf),
    ensures acc_ok(acc, sv, *q, lo as int, hi as int),
    no_unwind
{
    let Bufs { cand, ma, ml, mf, qrow, qslot, qkey, qg, pa, pl } = bf;
    let (mut cand, mut ma, mut ml, mut mf, mut qrow, mut qslot, mut qkey, mut qg, mut pa, mut pl) =
        (cand, ma, ml, mf, qrow, qslot, qkey, qg, pa, pl);
    let table = tz_table_array();
    let mut acc = Counts { n0: 0, h0: 0, n1: 0, h1: 0 };
    let ghost (pd1, pm) = (p_dates(sv, *q), p_mode(sv, *q));
    proof { lemma_terms_01(sv, *q); }
    let mut base = lo;
    while base < hi
        invariant
            cols_ok(*c, sv), probe_ok(*q), lo <= base <= hi <= c.nl,
            cand@.len() == BLOCK && ma@.len() == BLOCK && ml@.len() == BLOCK && mf@.len() == BLOCK,
            qrow@.len() == BLOCK && qslot@.len() == BLOCK && qkey@.len() == BLOCK,
            qg@.len() == BLOCK && pa@.len() == BLOCK && pl@.len() == BLOCK,
            table@.len() == 64,
            pd1 == p_dates(sv, *q), pm == p_mode(sv, *q),
            acc_ok(acc, sv, *q, lo as int, base as int),
            forall|i: int| 0 <= #[trigger] t_n(sv, *q, 0)(i) <= 1,
            forall|i: int| 0 <= #[trigger] t_h(sv, *q, 0)(i) <= 1,
            forall|i: int| 0 <= #[trigger] t_n(sv, *q, 1)(i) <= 1,
            forall|i: int| 0 <= #[trigger] t_h(sv, *q, 1)(i) <= 1,
        decreases hi - base,
    {
        let end = if hi - base >= BLOCK { base + BLOCK } else { hi };
        let nc = collect_cands(c, q, base, end, &mut cand, &table, Ghost(sv));
        let ghost s1 = range_filter(base as int, end as int, pd1);
        proof {
            lemma_range_filter_bounds(base as int, end as int, pd1);
        }
        mode_offsets(c, base, nc, &cand, &mut ma, &mut ml, Ghost(s1), Ghost(sv));
        mode_first(c, nc, &ma, &mut mf, Ghost(sv));
        let nq = mode_select(c, q, base, nc, &cand, &ma, &ml, &mf, &mut qrow, &mut qslot, Ghost(s1), Ghost(sv));
        let ghost s12 = seq_filter(s1, pm);
        proof {
            lemma_filter_range_filter(base as int, end as int, pd1, pm);
            lemma_range_filter_bounds(base as int, end as int, p_qual(sv, *q));
            assert(rows_in(s12, c.nl as int));
            assert(nq <= end - base) by {
                assert(nc <= end - base) by {
                    assert(s1.len() <= end - base) by { lemma_range_filter_len(base as int, end as int, pd1); }
                }
            }
        }
        order_keys(c, base, nq, &qrow, &mut qkey, &mut qg, Ghost(s12), Ghost(sv));
        order_prios(c, nq, &qkey, &qg, &mut pa, &mut pl, Ghost(sv));
        let ghost (n0, h0, n1, h1) = (acc.n0 as int, acc.h0 as int, acc.n1 as int, acc.h1 as int);
        proof {
            assert(s12.take(0) =~= Seq::<int>::empty());
            lemma_rs_bound(sv, *q, lo as int, base as int, t_n(sv, *q, 0));
            lemma_rs_bound(sv, *q, lo as int, base as int, t_h(sv, *q, 0));
            lemma_rs_bound(sv, *q, lo as int, base as int, t_n(sv, *q, 1));
            lemma_rs_bound(sv, *q, lo as int, base as int, t_h(sv, *q, 1));
        }
        count_rows(c, nq, &qslot, &pa, &pl, &qkey, &mut acc, Ghost(s12), Ghost(n0), Ghost(h0), Ghost(n1), Ghost(h1),
            Ghost(sv), Ghost(*q));
        proof {
            assert(s12.take(nq as int) =~= s12);
            lemma_block_sums(sv, *q, lo as int, base as int, end as int, t_n(sv, *q, 0));
            lemma_block_sums(sv, *q, lo as int, base as int, end as int, t_h(sv, *q, 0));
            lemma_block_sums(sv, *q, lo as int, base as int, end as int, t_n(sv, *q, 1));
            lemma_block_sums(sv, *q, lo as int, base as int, end as int, t_h(sv, *q, 1));
        }
        base = end;
    }
    acc
}

/// The scan of rows `[lo, hi)` as a `fork_join` task, with its scratch buffers.
pub struct ScanTask {
    pub c: Cols,
    pub q: Probe,
    pub lo: usize,
    pub hi: usize,
    pub bf: Bufs,
    pub sv: Ghost<StoresView>,
}

impl WorkerTask for ScanTask {
    type Output = Counts;

    open spec fn pre(&self) -> bool {
        &&& cols_ok(self.c, self.sv@)
        &&& probe_ok(self.q)
        &&& self.lo <= self.hi <= self.c.nl
        &&& bufs_ok(self.bf)
    }

    open spec fn post(&self, out: Counts) -> bool {
        acc_ok(out, self.sv@, self.q, self.lo as int, self.hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: Counts) {
        let ScanTask { c, q, lo, hi, bf, sv } = self;
        scan_range(&c, &q, lo, hi, bf, sv)
    }
}

} // verus!
