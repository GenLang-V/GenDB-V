//! Q12 scan kernel over storage `facts`' parts (model: `super::model`). A scan task walks the stored lineitem row
//! groups `[g0, g1)`; a group whose receipt-date zone (`[base, zone max]`) misses the window, or whose commit dates
//! all start at the window's end or later, is skipped. Whole 4096-row blocks of a small group take the bitmap path
//! when it applies (`super::runs`: run ranks and ship-mode bitmaps, word by word); otherwise per row the four
//! lineitem conditions are evaluated without branches and the order of a qualifying line is found by a cursor over
//! the stored orders rows (`Cursor`): the first qualifying line of a task looks its key up in the orders key index,
//! and when the lineitem rows follow the orders (`lines_clustered`) later lines walk forward from the previous
//! order (the order of a later line is never earlier). The line then counts for its ship-mode entry, as high
//! (`'1-URGENT'`/`'2-HIGH'`) or low priority.
use vstd::prelude::*;
use crate::gendb_entry::parallel::WorkerTask;
use crate::stores::facts::interface::common::keyidx::{fkey, key_find};
use super::model::*;
use super::common::bits::*;
use super::runs::*;

verus! {

/// `n` zero counters.
pub open spec fn zeros(n: nat) -> Seq<usize> {
    Seq::new(n, |_i: int| 0usize)
}

/// The first stored row of lineitem group `g` (`n_l` past the last group).
pub open spec fn row_of(c: Cols, g: int) -> int {
    if g * c.bs_l >= c.n_l { c.n_l as int } else { g * c.bs_l }
}

/// Position `p` of the orders cursor, with its group `gp` and the `rem` rows of that group left from `p` on.
pub struct Cursor {
    pub p: usize,
    pub gp: usize,
    pub rem: usize,
    /// When set, `p` is the order position of an earlier line of this task (`cursor_ok`).
    pub valid: bool,
}

/// The cursor's group bookkeeping.
pub open spec fn cursor_shape(c: Cols, cur: Cursor) -> bool {
    &&& cur.p <= c.n_o
    &&& cur.gp * c.bs_o <= cur.p
    &&& cur.p + cur.rem == cur.gp * c.bs_o + c.bs_o
    &&& 1 <= cur.rem <= c.bs_o
}

/// A valid cursor stands at the order of some line `jp` before row `j` (lines clustered).
pub open spec fn cursor_ok(c: Cols, cur: Cursor, jp: int, j: int) -> bool {
    &&& cursor_shape(c, cur)
    &&& cur.valid ==> lines_clustered(c) && 0 <= jp < j && cur.p == rpos(c, lkey(c, jp))
}

/// The stored orders row of key `k` by the orders key index (`rpos`).
#[inline(always)]
fn order_pos(c: &Cols, Ghost(kp): Ghost<int>, Ghost(km): Ghost<int>, k: i64) -> (p: usize)
    requires
        cols_ok(*c, kp, km),
        keys_distinct(*c),
    ensures
        p as int == rpos(*c, k as int),
    no_unwind
{
    match key_find(c.ok_codes, c.ok_bases, c.oi_codes, c.oi_bases, c.bs_o, c.oi_kind, c.n_o, k as i128) {
        Some(p) => {
            proof {
                assert(okey(*c, p as int) == k);
                lemma_rpos_of(*c, p as int);
            }
            p
        },
        None => {
            proof {
                assert forall|q: int| 0 <= q < c.n_o implies #[trigger] okey(*c, q) != k by {
                    assert(fkey(c.ok_codes@, c.ok_bases@, c.bs_o as int, q) != k);
                }
                lemma_rpos_none(*c, k as int);
            }
            c.n_o
        },
    }
}

/// The `len` codes of `s` from `a`, as an exact-length slice.
fn sub32(s: &[u32], a: usize, len: usize) -> (r: &[u32])
    requires a + len <= s@.len(),
    ensures r@ == s@.subrange(a as int, a + len),
    no_unwind
{
    let (_, t) = s.split_at(a);
    let (r, _) = t.split_at(len);
    r
}

/// The lane mask of 16 codes: lane `i` is set exactly when code `i` is `kk`; lanes 16.. are clear. Built as a `u32`
/// word (one wide vector compare) and widened.
#[inline(always)]
fn eq_mask16(cs: &[u32], kk: u32) -> (x: u64)
    requires cs@.len() == 16,
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] lane(x, i) == (cs@[i] == kk),
        clear_from(x, 16),
    no_unwind
{
    let mut y: u32 = 0;
    let mut b: u32 = 0;
    proof {
        lemma_zero_lanes32();
    }
    while b < 16
        invariant
            cs@.len() == 16,
            b <= 16,
            clear_from32(y, b as int),
            forall|i: int| 0 <= i < b ==> #[trigger] lane32(y, i) == (cs@[i] == kk),
        decreases 16 - b,
    {
        let q: u32 = if cs[b as usize] == kk { 1 } else { 0 };
        y = put_lane32(y, b, q);
        b = b + 1;
    }
    proof {
        lemma_widen16(y);
    }
    y as u64
}

/// No row of `[a, b)` has key `k`, and `a <= rpos(k)`: then `b <= rpos(k)`.
proof fn lemma_rpos_skip(c: Cols, k: int, a: int, b: int)
    requires
        0 <= a <= b <= c.n_o,
        a <= rpos(c, k),
        forall|q: int| a <= q < b ==> #[trigger] okey(c, q) != k,
    ensures b <= rpos(c, k),
    decreases b - a,
{
    if a < b {
        lemma_rpos_walk(c, k, a);
        lemma_rpos_skip(c, k, a + 1, b);
    }
}

/// Rows `[p, p + n)` (`n >= 1`) of orders group `gp`: the group has a base, and their keys are that base plus
/// their raw codes.
proof fn lemma_group_keys(c: Cols, kp: int, km: int, gp: int, p: int, n: int)
    requires
        cols_ok(c, kp, km),
        n >= 1,
        0 <= gp,
        gp * c.bs_o <= p,
        p + n <= gp * c.bs_o + c.bs_o,
        p + n <= c.n_o,
    ensures
        gp < c.ok_bases@.len(),
        forall|q: int| p <= q < p + n ==> #[trigger] okey(c, q) == c.ok_bases@[gp] + c.ok_codes@[q],
{
    lemma_div_group(p, c.bs_o as int, gp);
    lemma_div_below(p, c.bs_o as int, c.ok_bases@.len() as int);
    assert forall|q: int| p <= q < p + n implies #[trigger] okey(c, q) == c.ok_bases@[gp] + c.ok_codes@[q] by {
        lemma_div_group(q, c.bs_o as int, gp);
    }
}

/// From a cursor at or before `rpos(k)`, the first stored orders row at or after it with key `k` (or `n_o`):
/// within a group every code shares the group base, so the walk compares raw codes with `k - base`, 16 at a time
/// (lane masks), then one at a time to the group's end.
#[inline(always)]
fn walk(c: &Cols, tab: &[u8; 64], Ghost(kp): Ghost<int>, Ghost(km): Ghost<int>, cur: &mut Cursor, k: i64)
    requires
        tz_table_ok(*tab),
        cols_ok(*c, kp, km),
        cursor_shape(*c, *old(cur)),
        old(cur).p <= rpos(*c, k as int),
        old(cur).valid,
    ensures
        cursor_shape(*c, *final(cur)),
        final(cur).p as int == rpos(*c, k as int),
        final(cur).valid,
    no_unwind
{
    let n_o = c.n_o;
    let bs_o = c.bs_o;
    let mut p = cur.p;
    let mut gp = cur.gp;
    let mut rem = cur.rem;
    let mut found = false;
    while !found && p < n_o
        invariant
            tz_table_ok(*tab),
            cols_ok(*c, kp, km),
            n_o == c.n_o,
            bs_o == c.bs_o,
            cursor_shape(*c, Cursor { p, gp, rem, valid: true }),
            p <= rpos(*c, k as int),
            found ==> p < n_o && okey(*c, p as int) == k,
        decreases n_o - p + if found { 0int } else { 1 },
    {
        let lim = n_o - p;
        let span = if rem < lim { rem } else { lim };
        proof {
            lemma_group_keys(*c, kp, km, gp as int, p as int, span as int);
        }
        let d = k as i128 - c.ok_bases[gp] as i128;
        let mut i: usize = 0;
        if 0 <= d && d <= u32::MAX as i128 {
            let kk = d as u32;
            // Invariant: no row of `[p, p + i)` has key `k` unless found at `p + i`.
            while !found && span - i >= 16
                invariant
                    tz_table_ok(*tab),
                    cols_ok(*c, kp, km),
                    n_o == c.n_o,
                    p + span <= n_o,
                    i <= span,
                    kk == k - c.ok_bases@[gp as int],
                    forall|q: int| p <= q < p + span ==> #[trigger] okey(*c, q) == c.ok_bases@[gp as int] + c.ok_codes@[q],
                    forall|q: int| p <= q < p + i ==> #[trigger] okey(*c, q) != k,
                    found ==> i < span && okey(*c, p + i) == k,
                decreases span - i + if found { 0int } else { 1 },
            {
                let cs = sub32(c.ok_codes, p + i, 16);
                let m = eq_mask16(cs, kk);
                if m != 0 {
                    let t = lowest_lane(tab, m);
                    proof {
                        assert(t < 16) by {
                            if t >= 16 {
                                assert(!lane(m, t as int));
                            }
                        }
                        assert forall|q: int| p <= q < p + i + t implies #[trigger] okey(*c, q) != k by {
                            if q >= p + i {
                                assert(!lane(m, q - p - i));
                                assert(cs@[q - p - i] == c.ok_codes@[q]);
                            }
                        }
                        assert(cs@[t as int] == kk);
                    }
                    i = i + t as usize;
                    found = true;
                } else {
                    proof {
                        assert forall|q: int| p <= q < p + i + 16 implies #[trigger] okey(*c, q) != k by {
                            if q >= p + i {
                                lemma_zero_lanes();
                                assert(!lane(m, q - p - i));
                                assert(cs@[q - p - i] == c.ok_codes@[q]);
                            }
                        }
                    }
                    i = i + 16;
                }
            }
            while !found && i < span
                invariant
                    tz_table_ok(*tab),
                    cols_ok(*c, kp, km),
                    n_o == c.n_o,
                    p + span <= n_o,
                    i <= span,
                    kk == k - c.ok_bases@[gp as int],
                    forall|q: int| p <= q < p + span ==> #[trigger] okey(*c, q) == c.ok_bases@[gp as int] + c.ok_codes@[q],
                    forall|q: int| p <= q < p + i ==> #[trigger] okey(*c, q) != k,
                    found ==> i < span && okey(*c, p + i) == k,
                decreases span - i + if found { 0int } else { 1 },
            {
                if c.ok_codes[p + i] == kk {
                    found = true;
                } else {
                    i = i + 1;
                }
            }
        } else {
            proof {
                assert forall|q: int| p <= q < p + span implies #[trigger] okey(*c, q) != k by {}
            }
            i = span;
        }
        proof {
            lemma_rpos_skip(*c, k as int, p as int, p + i);
        }
        if found {
            p = p + i;
            rem = rem - i;
        } else if span == rem {
            proof {
                lemma_next_group(gp as int, bs_o as int);
                lemma_group_le(gp as int, bs_o as int);
            }
            p = p + i;
            gp = gp + 1;
            rem = bs_o;
        } else {
            p = p + i;
            rem = rem - i;
        }
    }
    proof {
        lemma_rpos_bound(*c, k as int);
        if p < n_o {
            lemma_rpos_first(*c, k as int, p as int);
        }
    }
    cur.p = p;
    cur.gp = gp;
    cur.rem = rem;
}

/// A cursor valid at row `j` stays valid at every later row.
pub proof fn lemma_cursor_later(c: Cols, cur: Cursor, jp: int, j: int, j2: int)
    requires cursor_ok(c, cur, jp, j), j <= j2,
    ensures cursor_ok(c, cur, jp, j2),
{
}

/// Moves the cursor to the order of key `k` (`rpos(k)`): a forward walk from a valid cursor, else a key-index lookup
/// (which validates the cursor when the lines are clustered).
#[inline(always)]
fn seek(c: &Cols, tab: &[u8; 64], Ghost(kp): Ghost<int>, Ghost(km): Ghost<int>, clustered: bool, cur: &mut Cursor, k: i64,
    Ghost(jp): Ghost<int>, Ghost(j): Ghost<int>) -> (jp2: Ghost<int>)
    requires
        tz_table_ok(*tab),
        cols_ok(*c, kp, km),
        keys_distinct(*c),
        clustered ==> lines_clustered(*c),
        0 <= j < c.n_l,
        k == lkey(*c, j),
        cursor_ok(*c, *old(cur), jp, j),
    ensures
        final(cur).p as int == rpos(*c, k as int),
        cursor_ok(*c, *final(cur), jp2@, j + 1),
    no_unwind
{
    let n_o = c.n_o;
    let bs_o = c.bs_o;
    if cur.valid {
        proof {
            lemma_lines_le(*c, jp, j);
        }
        walk(c, tab, Ghost(kp), Ghost(km), cur, k);
        Ghost(j)
    } else {
        let p = order_pos(c, Ghost(kp), Ghost(km), k);
        proof {
            lemma_rpos_bound(*c, k as int);
            lemma_group_of_row(p as int, bs_o as int);
        }
        cur.p = p;
        cur.gp = p / bs_o;
        cur.rem = bs_o - p % bs_o;
        cur.valid = clustered;
        Ghost(j)
    }
}

/// One scan task: lineitem groups `[g0, g1)`, `km` zero counters per aggregate (high, low).
pub struct ScanTask {
    pub cols: Cols,
    pub win: Win,
    pub kp: usize,
    pub km: usize,
    pub g0: usize,
    pub g1: usize,
    pub clustered: bool,
    pub hi_cnt: Vec<usize>,
    pub lo_cnt: Vec<usize>,
    /// Scratch flags of one block (general path).
    pub flags: [u8; FB],
    /// Scratch of one block (fast path): the lane masks of its words, and the l_orderkey and l_shipmode codes of
    /// its qualifying rows in row order.
    pub masks: [u64; 64],
    pub keys: [u32; FB],
    pub modes: [u8; FB],
    /// The lowest-lane table (`tz_table`).
    pub tab: [u8; 64],
    /// The bitmap path (`fast_ok`, when `fast`): the l_orderkey run starts (storage `li_okruns`), the bitmaps of
    /// storage `li_okmode` and the selected ship-mode bitmaps.
    pub st: &'static [u32],
    pub bits: Bits,
    pub sel: Sel,
    pub fast: bool,
}

/// The counters hold the counts of rows `[j0, j)`.
pub open spec fn counts_at(c: Cols, w: Win, km: int, hi_cnt: Seq<usize>, lo_cnt: Seq<usize>, j0: int, j: int) -> bool {
    &&& hi_cnt.len() == km
    &&& lo_cnt.len() == km
    &&& forall|d: int| 0 <= d < km ==> #[trigger] hi_cnt[d] as int == cnt(c, w, 0, d, j0, j)
    &&& forall|d: int| 0 <= d < km ==> #[trigger] lo_cnt[d] as int == cnt(c, w, 1, d, j0, j)
}

/// One row: the counters move from `[j0, j)` to `[j0, j + 1)` when the row's contribution is added.
pub proof fn lemma_counts_step(c: Cols, w: Win, km: int, h0: Seq<usize>, l0: Seq<usize>, h1: Seq<usize>, l1: Seq<usize>,
    j0: int, j: int)
    requires
        j0 <= j,
        counts_at(c, w, km, h0, l0, j0, j),
        h1.len() == km,
        l1.len() == km,
        forall|d: int| 0 <= d < km ==> #[trigger] h1[d] as int == h0[d] + lval(c, w, 0, d, j),
        forall|d: int| 0 <= d < km ==> #[trigger] l1[d] as int == l0[d] + lval(c, w, 1, d, j),
    ensures counts_at(c, w, km, h1, l1, j0, j + 1),
{
    assert forall|d: int| 0 <= d < km implies #[trigger] h1[d] as int == cnt(c, w, 0, d, j0, j + 1) by {
        lemma_cnt_step(c, w, 0, d, j0, j);
    }
    assert forall|d: int| 0 <= d < km implies #[trigger] l1[d] as int == cnt(c, w, 1, d, j0, j + 1) by {
        lemma_cnt_step(c, w, 1, d, j0, j);
    }
}

/// Rows `[a, b)` that never qualify leave the counters unchanged.
pub proof fn lemma_counts_skip(c: Cols, w: Win, km: int, h: Seq<usize>, l: Seq<usize>, j0: int, a: int, b: int)
    requires
        j0 <= a <= b,
        counts_at(c, w, km, h, l, j0, a),
        forall|j: int| a <= j < b ==> !#[trigger] lqual(c, w, j),
    ensures counts_at(c, w, km, h, l, j0, b),
{
    assert forall|d: int| 0 <= d < km implies #[trigger] h[d] as int == cnt(c, w, 0, d, j0, b) by {
        lemma_cnt_split(c, w, 0, d, j0, a, b);
        lemma_cnt_none(c, w, 0, d, a, b);
    }
    assert forall|d: int| 0 <= d < km implies #[trigger] l[d] as int == cnt(c, w, 1, d, j0, b) by {
        lemma_cnt_split(c, w, 1, d, j0, a, b);
        lemma_cnt_none(c, w, 1, d, a, b);
    }
}

/// Rows per block of the two-phase scan (flags of one block stay in the L1 cache).
pub const FB: usize = 4096;

/// Per-group thresholds of the branch-free row test on the raw codes of group `g`: receipt code in `[rl, rh]`,
/// `commit code - receipt code < dcr`, `ship code - commit code < dsc`, mode code `e0` or `e1`.
pub struct Thr {
    pub rl: i32,
    pub rh: i32,
    pub dcr: i32,
    pub dsc: i32,
    pub e0: i32,
    pub e1: i32,
}

/// `t` clamped to `[lo, hi]`.
pub open spec fn clampi(t: int, lo: int, hi: int) -> int {
    if t < lo { lo } else if t > hi { hi } else { t }
}

/// The code of dictionary entry `s` in a group of base `mb` (codes are U8), or -1 (no code).
pub open spec fn ecode(s: int, mb: int) -> int {
    if mb <= s && s - mb <= 255 { s - mb } else { -1 }
}

/// The thresholds of group `g` for window `w`.
pub open spec fn thr_ok(c: Cols, w: Win, g: int, t: Thr) -> bool {
    &&& t.rl == clampi(w.lo - c.lr_bases@[g], -1, 65536)
    &&& t.rh == clampi(w.hi - c.lr_bases@[g], -1, 65536)
    &&& t.dcr == clampi(c.lr_bases@[g] - c.lc_bases@[g], -65535, 65536)
    &&& t.dsc == clampi(c.lc_bases@[g] - c.ls_bases@[g], -65535, 65536)
    &&& t.e0 == ecode(w.s0 as int, c.lm_bases@[g] as int)
    &&& t.e1 == ecode(w.s1 as int, c.lm_bases@[g] as int)
}

/// The two selected modes are distinct (or both absent): at most one matches a row.
pub open spec fn win_ok(w: Win) -> bool {
    w.s0 != w.s1 || w.s0 == u64::MAX
}

/// `t` clamped to `[lo, hi]`, computed in `i128`.
fn clamp_i32(t: i128, lo: i32, hi: i32) -> (r: i32)
    requires lo <= hi,
    ensures r as int == clampi(t as int, lo as int, hi as int),
    no_unwind
{
    if t < lo as i128 { lo } else if t > hi as i128 { hi } else { t as i32 }
}

/// The code of entry `s` in a group of base `mb`, or -1.
fn ecode_exec(s: u64, mb: u64) -> (r: i32)
    ensures r as int == ecode(s as int, mb as int),
    no_unwind
{
    if mb <= s && s - mb <= 255 { (s - mb) as i32 } else { -1 }
}

/// The thresholds of group `g`.
fn group_thr(c: &Cols, w: &Win, g: usize) -> (t: Thr)
    requires
        g < c.lk_bases@.len(),
        c.lr_bases@.len() == c.lk_bases@.len(),
        c.lc_bases@.len() == c.lk_bases@.len(),
        c.ls_bases@.len() == c.lk_bases@.len(),
        c.lm_bases@.len() == c.lk_bases@.len(),
    ensures thr_ok(*c, *w, g as int, t),
    no_unwind
{
    let rb = c.lr_bases[g] as i128;
    let cb = c.lc_bases[g] as i128;
    let sb = c.ls_bases[g] as i128;
    let mb = c.lm_bases[g];
    Thr {
        rl: clamp_i32(w.lo as i128 - rb, -1, 65536),
        rh: clamp_i32(w.hi as i128 - rb, -1, 65536),
        dcr: clamp_i32(rb - cb, -65535, 65536),
        dsc: clamp_i32(cb - sb, -65535, 65536),
        e0: ecode_exec(w.s0, mb),
        e1: ecode_exec(w.s1, mb),
    }
}

/// The branch-free test on the raw codes of row `j` (in group `g`) is `lqual`, and the two mode tests never both
/// hold.
proof fn lemma_row_test(c: Cols, w: Win, kp: int, km: int, g: int, t: Thr, j: int)
    requires
        cols_ok(c, kp, km),
        win_ok(w),
        0 <= j < c.n_l,
        j / c.bs_l as int == g,
        thr_ok(c, w, g, t),
    ensures ({
        let r = c.lr_codes@[j] as int;
        let cc = c.lc_codes@[j] as int;
        let s = c.ls_codes@[j] as int;
        let m = c.lm_codes@[j] as int;
        &&& lqual(c, w, j) == (r >= t.rl && r <= t.rh && cc - r < t.dcr && s - cc < t.dsc && (m == t.e0 || m == t.e1))
        &&& !(m == t.e0 && m == t.e1)
    }),
{
    let r = c.lr_codes@[j] as int;
    let cc = c.lc_codes@[j] as int;
    let m = c.lm_codes@[j] as int;
    assert(0 <= lmode(c, j) < km);
    assert(lmode(c, j) == c.lm_bases@[g] + m);
    if m == t.e0 && m == t.e1 {
        assert(lmode(c, j) == w.s0 && lmode(c, j) == w.s1);
    }
}

/// Counts stored lineitem row `j` (a qualifying line of mode entry `m`): seeks its order and adds it to the high or
/// low counter of `m` when the order exists.
#[inline(always)]
fn count_line(c: &Cols, tab: &[u8; 64], w: &Win, Ghost(kp): Ghost<int>, km: usize, clustered: bool, kb: i64, kc: u32, Ghost(j): Ghost<int>, m: usize,
    cur: &mut Cursor, Ghost(jp): Ghost<int>, hi_cnt: &mut Vec<usize>, lo_cnt: &mut Vec<usize>, Ghost(j0): Ghost<int>)
    -> (jp2: Ghost<int>)
    requires
        tz_table_ok(*tab),
        cols_ok(*c, kp, km as int),
        keys_distinct(*c),
        clustered ==> lines_clustered(*c),
        0 <= j0 <= j < c.n_l,
        kb == c.lk_bases@[j / c.bs_l as int],
        kc == c.lk_codes@[j],
        lqual(*c, *w, j),
        m as int == lmode(*c, j),
        cursor_ok(*c, *old(cur), jp, j),
        counts_at(*c, *w, km as int, old(hi_cnt)@, old(lo_cnt)@, j0, j),
    ensures
        cursor_ok(*c, *final(cur), jp2@, j + 1),
        counts_at(*c, *w, km as int, final(hi_cnt)@, final(lo_cnt)@, j0, j + 1),
    no_unwind
{
    let ghost h0 = hi_cnt@;
    let ghost l0 = lo_cnt@;
    proof {
        assert(in_i64(lkey(*c, j)));
        lemma_cnt_bound(*c, *w, 0, m as int, j0, j);
        lemma_cnt_bound(*c, *w, 1, m as int, j0, j);
    }
    let k = kb + kc as i64;
    let jp2 = seek(c, tab, Ghost(kp), Ghost(km as int), clustered, cur, k, Ghost(jp), Ghost(j));
    let p = cur.p;
    if p < c.n_o {
        proof {
            lemma_div_group(p as int, c.bs_o as int, cur.gp as int);
            lemma_div_below(p as int, c.bs_o as int, c.ok_bases@.len() as int);
            assert(0 <= oprio(*c, p as int) < kp);
        }
        let e = c.op_bases[cur.gp] + c.op_codes[p] as u64;
        // Branch-free: the priority of a line's order is unpredictable.
        let h0b: usize = if e == w.u0 { 1 } else { 0 };
        let h1b: usize = if e == w.u1 { 1 } else { 0 };
        let h: usize = h0b | h1b;
        proof {
            assert(h == 1usize <==> (h0b == 1usize || h1b == 1usize)) by (bit_vector)
                requires h0b <= 1, h1b <= 1, h == h0b | h1b;
            assert(h <= 1usize) by (bit_vector)
                requires h0b <= 1, h1b <= 1, h == h0b | h1b;
        }
        hi_cnt[m] = hi_cnt[m] + h;
        lo_cnt[m] = lo_cnt[m] + (1 - h);
    }
    proof {
        assert(rpos(*c, lkey(*c, j)) == p);
        assert forall|d: int| 0 <= d < km implies #[trigger] hi_cnt@[d] as int == h0[d] + lval(*c, *w, 0, d, j) by {
            if d != m as int {
                assert(lval(*c, *w, 0, d, j) == 0);
            }
        }
        assert forall|d: int| 0 <= d < km implies #[trigger] lo_cnt@[d] as int == l0[d] + lval(*c, *w, 1, d, j) by {
            if d != m as int {
                assert(lval(*c, *w, 1, d, j) == 0);
            }
        }
        lemma_counts_step(*c, *w, km as int, h0, l0, hi_cnt@, lo_cnt@, j0, j);
    }
    jp2
}

/// Scans the `n` rows from `b0` of lineitem group `g` (one block) in two phases: the qualifying flags of every row
/// (branch-free, over exact-length code slices), then the qualifying lines.
fn scan_block(c: &Cols, tab: &[u8; 64], w: &Win, Ghost(kp): Ghost<int>, km: usize, clustered: bool, g: usize, t: &Thr, b0: usize,
    n: usize, flags: &mut [u8], cur: &mut Cursor, Ghost(jp): Ghost<int>, hi_cnt: &mut Vec<usize>,
    lo_cnt: &mut Vec<usize>, Ghost(j0): Ghost<int>) -> (jp2: Ghost<int>)
    requires
        tz_table_ok(*tab),
        cols_ok(*c, kp, km as int),
        keys_distinct(*c),
        clustered ==> lines_clustered(*c),
        win_ok(*w),
        0 <= j0 <= b0,
        b0 + n <= c.n_l,
        n <= old(flags)@.len(),
        g * c.bs_l <= b0,
        b0 + n <= g * c.bs_l + c.bs_l,
        g < c.lk_bases@.len(),
        thr_ok(*c, *w, g as int, *t),
        cursor_ok(*c, *old(cur), jp, b0 as int),
        counts_at(*c, *w, km as int, old(hi_cnt)@, old(lo_cnt)@, j0, b0 as int),
    ensures
        final(flags)@.len() == old(flags)@.len(),
        cursor_ok(*c, *final(cur), jp2@, b0 + n),
        counts_at(*c, *w, km as int, final(hi_cnt)@, final(lo_cnt)@, j0, b0 + n),
    no_unwind
{
    let ghost mut jp = jp;
    let ghost flen = flags@.len();
    let (_, rt) = c.lr_codes.split_at(b0);
    let (rc, _) = rt.split_at(n);
    let (_, ct) = c.lc_codes.split_at(b0);
    let (cc, _) = ct.split_at(n);
    let (_, st) = c.ls_codes.split_at(b0);
    let (sc, _) = st.split_at(n);
    let (_, mt) = c.lm_codes.split_at(b0);
    let (mc, _) = mt.split_at(n);
    let (fb, _) = flags.split_at_mut(n);
    let rl = t.rl;
    let rh = t.rh;
    let dcr = t.dcr;
    let dsc = t.dsc;
    let e0 = t.e0;
    let e1 = t.e1;
    // Phase 1: fb[i] == 1 exactly when row b0 + i qualifies.
    let mut i: usize = 0;
    while i < n
        invariant
            tz_table_ok(*tab),
            cols_ok(*c, kp, km as int),
            win_ok(*w),
            b0 + n <= c.n_l,
            g * c.bs_l <= b0,
            b0 + n <= g * c.bs_l + c.bs_l,
            thr_ok(*c, *w, g as int, *t),
            rl == t.rl && rh == t.rh && dcr == t.dcr && dsc == t.dsc && e0 == t.e0 && e1 == t.e1,
            rc@ == c.lr_codes@.subrange(b0 as int, b0 + n),
            cc@ == c.lc_codes@.subrange(b0 as int, b0 + n),
            sc@ == c.ls_codes@.subrange(b0 as int, b0 + n),
            mc@ == c.lm_codes@.subrange(b0 as int, b0 + n),
            fb@.len() == n,
            i <= n,
            forall|k: int| 0 <= k < i ==> (#[trigger] fb@[k] != 0) == lqual(*c, *w, b0 + k),
        decreases n - i,
    {
        proof {
            lemma_div_group(b0 + i, c.bs_l as int, g as int);
            lemma_row_test(*c, *w, kp, km as int, g as int, *t, b0 + i);
        }
        let r = rc[i] as i32;
        let cv = cc[i] as i32;
        let s = sc[i] as i32;
        let m = mc[i] as i32;
        let b1: u8 = if r >= rl { 1 } else { 0 };
        let b2: u8 = if r <= rh { 1 } else { 0 };
        let b3: u8 = if cv - r < dcr { 1 } else { 0 };
        let b4: u8 = if s - cv < dsc { 1 } else { 0 };
        let b5: u8 = if m == e0 { 1 } else { 0 };
        let b6: u8 = if m == e1 { 1 } else { 0 };
        fb[i] = if b1 + b2 + b3 + b4 + b5 + b6 == 5 { 1 } else { 0 };
        i = i + 1;
    }
    // Phase 2: the qualifying lines, in row order.
    let kb = c.lk_bases[g];
    let mb = c.lm_bases[g];
    let mut i: usize = 0;
    while i < n
        invariant
            tz_table_ok(*tab),
            cols_ok(*c, kp, km as int),
            keys_distinct(*c),
            clustered ==> lines_clustered(*c),
            0 <= j0 <= b0,
            b0 + n <= c.n_l,
            g * c.bs_l <= b0,
            b0 + n <= g * c.bs_l + c.bs_l,
            g < c.lk_bases@.len(),
            kb == c.lk_bases@[g as int],
            mb == c.lm_bases@[g as int],
            mc@ == c.lm_codes@.subrange(b0 as int, b0 + n),
            fb@.len() == n,
            i <= n,
            forall|k: int| 0 <= k < n ==> (#[trigger] fb@[k] != 0) == lqual(*c, *w, b0 + k),
            cursor_ok(*c, *cur, jp, b0 + i),
            counts_at(*c, *w, km as int, hi_cnt@, lo_cnt@, j0, b0 + i),
        decreases n - i,
    {
        let j = b0 + i;
        if fb[i] != 0 {
            proof {
                lemma_div_group(j as int, c.bs_l as int, g as int);
                assert(0 <= lmode(*c, j as int) < km);
            }
            let m = (mb + mc[i] as u64) as usize;
            let jpg = count_line(c, tab, w, Ghost(kp), km, clustered, kb, c.lk_codes[j], Ghost(j as int), m, cur, Ghost(jp), hi_cnt, lo_cnt, Ghost(j0));
            proof {
                jp = jpg@;
            }
        } else {
            proof {
                let ghost h = hi_cnt@;
                let ghost l = lo_cnt@;
                assert(!lqual(*c, *w, j as int));
                lemma_counts_skip(*c, *w, km as int, h, l, j0, j as int, j + 1);
            }
        }
        i = i + 1;
    }
    Ghost(jp)
}

// ------------------------------------------------------------------------------------------------ 16-bit fast path

/// Rows per lane word of the fast path (one `u64` lane mask).
pub const WL: usize = 64;

/// `t` clamped to the `i16` range.
pub open spec fn clamp16(t: int) -> int {
    clampi(t, -32768, 32767)
}

/// Every receipt, commit and ship code of lineitem group `g` is at most 32767 (by the group's zone maxima), so the
/// codes are exact as `i16` and so are their differences.
pub open spec fn group_small(c: Cols, g: int) -> bool {
    &&& c.lr_zmax@[g] - c.lr_bases@[g] <= 32767
    &&& c.lc_zmax@[g] - c.lc_bases@[g] <= 32767
    &&& c.ls_zmax@[g] - c.ls_bases@[g] <= 32767
}

/// Thresholds of the 16-bit row test of group `g` (`thr16_ok`): on raw codes `r`, `c`, `s`, `m` (as `i16`) a row
/// qualifies exactly when `r > ra`, `r <= rb`, `c - r <= ecr`, `s - c <= esc` and `m` is `m0` or `m1`; valid when
/// `fast` (`group_small`).
pub struct Thr16 {
    pub fast: bool,
    pub ra: i16,
    pub rb: i16,
    pub ecr: i16,
    pub esc: i16,
    pub m0: i16,
    pub m1: i16,
}

/// The 16-bit thresholds of group `g` for window `w`.
pub open spec fn thr16_ok(c: Cols, w: Win, g: int, t: Thr16) -> bool {
    &&& t.fast ==> group_small(c, g)
    &&& t.ra == clamp16(w.lo - c.lr_bases@[g] - 1)
    &&& t.rb == clamp16(w.hi - c.lr_bases@[g])
    &&& t.ecr == clamp16(c.lr_bases@[g] - c.lc_bases@[g] - 1)
    &&& t.esc == clamp16(c.lc_bases@[g] - c.ls_bases@[g] - 1)
    &&& t.m0 == ecode(w.s0 as int, c.lm_bases@[g] as int)
    &&& t.m1 == ecode(w.s1 as int, c.lm_bases@[g] as int)
}

/// `t` clamped to the `i16` range, computed in `i128`.
fn clamp_i16(t: i128) -> (r: i16)
    ensures r as int == clamp16(t as int),
    no_unwind
{
    if t < -32768 { -32768 } else if t > 32767 { 32767 } else { t as i16 }
}

/// The 16-bit thresholds of group `g`.
fn group_thr16(c: &Cols, w: &Win, g: usize) -> (t: Thr16)
    requires
        g < c.lk_bases@.len(),
        c.lr_bases@.len() == c.lk_bases@.len(),
        c.lc_bases@.len() == c.lk_bases@.len(),
        c.ls_bases@.len() == c.lk_bases@.len(),
        c.lm_bases@.len() == c.lk_bases@.len(),
        c.lr_zmax@.len() == c.lk_bases@.len(),
        c.lc_zmax@.len() == c.lk_bases@.len(),
        c.ls_zmax@.len() == c.lk_bases@.len(),
    ensures thr16_ok(*c, *w, g as int, t),
    no_unwind
{
    let rb = c.lr_bases[g] as i128;
    let cb = c.lc_bases[g] as i128;
    let sb = c.ls_bases[g] as i128;
    let mb = c.lm_bases[g];
    let fast = c.lr_zmax[g] as i128 - rb <= 32767 && c.lc_zmax[g] as i128 - cb <= 32767
        && c.ls_zmax[g] as i128 - sb <= 32767;
    Thr16 {
        fast,
        ra: clamp_i16(w.lo as i128 - rb - 1),
        rb: clamp_i16(w.hi as i128 - rb),
        ecr: clamp_i16(rb - cb - 1),
        esc: clamp_i16(cb - sb - 1),
        m0: ecode_exec(w.s0, mb) as i16,
        m1: ecode_exec(w.s1, mb) as i16,
    }
}

/// The 16-bit test on the raw codes of row `j` (in a small group `g`) is `lqual`; the codes fit in `i16`, and the
/// two mode tests never both hold.
proof fn lemma_row_test16(c: Cols, w: Win, kp: int, km: int, g: int, t: Thr16, j: int)
    requires
        cols_ok(c, kp, km),
        win_ok(w),
        0 <= j < c.n_l,
        j / c.bs_l as int == g,
        thr16_ok(c, w, g, t),
        t.fast,
    ensures ({
        let r = c.lr_codes@[j] as int;
        let cc = c.lc_codes@[j] as int;
        let s = c.ls_codes@[j] as int;
        let m = c.lm_codes@[j] as int;
        &&& r <= 32767 && cc <= 32767 && s <= 32767
        &&& lqual(c, w, j) == (r > t.ra && r <= t.rb && cc - r <= t.ecr && s - cc <= t.esc && (m == t.m0 || m == t.m1))
        &&& !(m == t.m0 && m == t.m1)
    }),
{
    let r = c.lr_codes@[j] as int;
    let cc = c.lc_codes@[j] as int;
    let m = c.lm_codes@[j] as int;
    assert(lrcp(c, j) <= c.lr_zmax@[g]);
    assert(lcmt(c, j) <= c.lc_zmax@[g]);
    assert(lship(c, j) <= c.ls_zmax@[g]);
    assert(0 <= lmode(c, j) < km);
    assert(lmode(c, j) == c.lm_bases@[g] + m);
    if m == t.m0 && m == t.m1 {
        assert(lmode(c, j) == w.s0 && lmode(c, j) == w.s1);
    }
}


/// The `u32` lane mask of the 32 rows from `j0 + off` (`off` 0 or 32) of a 64-row word in a small group `g`: lane
/// `k` is set exactly when row `j0 + off + k` qualifies. Branch-free over exact-length code slices.
#[inline(always)]
fn half_mask(c: &Cols, w: &Win, Ghost(kp): Ghost<int>, Ghost(km): Ghost<int>, Ghost(g): Ghost<int>, t: &Thr16,
    Ghost(j0): Ghost<int>, rw: &[u16], cw: &[u16], sw: &[u16], mw: &[u8], off: usize) -> (x: u32)
    requires
        cols_ok(*c, kp, km),
        win_ok(*w),
        0 <= j0,
        j0 + 64 <= c.n_l,
        g * c.bs_l <= j0,
        j0 + 64 <= g * c.bs_l + c.bs_l,
        thr16_ok(*c, *w, g, *t),
        t.fast,
        rw@ == c.lr_codes@.subrange(j0, j0 + 64),
        cw@ == c.lc_codes@.subrange(j0, j0 + 64),
        sw@ == c.ls_codes@.subrange(j0, j0 + 64),
        mw@ == c.lm_codes@.subrange(j0, j0 + 64),
        off == 0 || off == 32,
    ensures forall|k: int| 0 <= k < 32 ==> #[trigger] lane32(x, k) == lqual(*c, *w, j0 + off + k),
    no_unwind
{
    let ra = t.ra;
    let rb = t.rb;
    let ecr = t.ecr;
    let esc = t.esc;
    let m0 = t.m0;
    let m1 = t.m1;
    let mut x: u32 = 0;
    let mut b: u32 = 0;
    proof {
        lemma_zero_lanes32();
    }
    while b < 32
        invariant
            cols_ok(*c, kp, km),
            win_ok(*w),
            0 <= j0,
            j0 + 64 <= c.n_l,
            g * c.bs_l <= j0,
            j0 + 64 <= g * c.bs_l + c.bs_l,
            thr16_ok(*c, *w, g, *t),
            t.fast,
            ra == t.ra && rb == t.rb && ecr == t.ecr && esc == t.esc && m0 == t.m0 && m1 == t.m1,
            rw@ == c.lr_codes@.subrange(j0, j0 + 64),
            cw@ == c.lc_codes@.subrange(j0, j0 + 64),
            sw@ == c.ls_codes@.subrange(j0, j0 + 64),
            mw@ == c.lm_codes@.subrange(j0, j0 + 64),
            off == 0 || off == 32,
            b <= 32,
            clear_from32(x, b as int),
            forall|k: int| 0 <= k < b ==> #[trigger] lane32(x, k) == lqual(*c, *w, j0 + off + k),
        decreases 32 - b,
    {
        let i = off + b as usize;
        proof {
            lemma_div_group(j0 + i, c.bs_l as int, g);
            lemma_row_test16(*c, *w, kp, km, g, *t, j0 + i);
        }
        let r = rw[i] as i16;
        let cv = cw[i] as i16;
        let s = sw[i] as i16;
        let m = mw[i] as i16;
        let q1: u32 = if r > ra { 1 } else { 0 };
        let q2: u32 = if r <= rb { 1 } else { 0 };
        let q3: u32 = if cv - r <= ecr { 1 } else { 0 };
        let q4: u32 = if s - cv <= esc { 1 } else { 0 };
        let q5: u32 = if m == m0 { 1 } else { 0 };
        let q6: u32 = if m == m1 { 1 } else { 0 };
        let q: u32 = q1 & q2 & q3 & q4 & (q5 | q6);
        proof {
            assert(q <= 1u32 && (q == 1u32 <==> (q1 == 1u32 && q2 == 1u32 && q3 == 1u32 && q4 == 1u32
                && (q5 == 1u32 || q6 == 1u32)))) by (bit_vector)
                requires q1 <= 1 && q2 <= 1 && q3 <= 1 && q4 <= 1 && q5 <= 1 && q6 <= 1,
                    q == q1 & q2 & q3 & q4 & (q5 | q6);
            assert((q == 1) == lqual(*c, *w, j0 + i));
        }
        x = put_lane32(x, b, q);
        b = b + 1;
    }
    x
}

/// The lane mask of the 64 rows from `j0` (in a small group `g`): lane `k` is set exactly when row `j0 + k`
/// qualifies. Two 32-row halves (`half_mask`) joined.
#[inline(always)]
pub fn word_mask(c: &Cols, w: &Win, Ghost(kp): Ghost<int>, Ghost(km): Ghost<int>, Ghost(g): Ghost<int>, t: &Thr16,
    Ghost(j0): Ghost<int>, rw: &[u16], cw: &[u16], sw: &[u16], mw: &[u8]) -> (x: u64)
    requires
        cols_ok(*c, kp, km),
        win_ok(*w),
        0 <= j0,
        j0 + 64 <= c.n_l,
        g * c.bs_l <= j0,
        j0 + 64 <= g * c.bs_l + c.bs_l,
        thr16_ok(*c, *w, g, *t),
        t.fast,
        rw@ == c.lr_codes@.subrange(j0, j0 + 64),
        cw@ == c.lc_codes@.subrange(j0, j0 + 64),
        sw@ == c.ls_codes@.subrange(j0, j0 + 64),
        mw@ == c.lm_codes@.subrange(j0, j0 + 64),
    ensures forall|k: int| 0 <= k < 64 ==> #[trigger] lane(x, k) == lqual(*c, *w, j0 + k),
    no_unwind
{
    let lo = half_mask(c, w, Ghost(kp), Ghost(km), Ghost(g), t, Ghost(j0), rw, cw, sw, mw, 0);
    let hi = half_mask(c, w, Ghost(kp), Ghost(km), Ghost(g), t, Ghost(j0), rw, cw, sw, mw, 32);
    let x = (lo as u64) | ((hi as u64) << 32u64);
    proof {
        lemma_join32(lo, hi, x);
        assert forall|k: int| 0 <= k < 64 implies #[trigger] lane(x, k) == lqual(*c, *w, j0 + k) by {
            if k < 32 {
                assert(lane32(lo, k) == lqual(*c, *w, j0 + 0 + k));
            } else {
                assert(lane32(hi, k - 32) == lqual(*c, *w, j0 + 32 + (k - 32)));
            }
        }
    }
    x
}

/// The `len` codes of `s` from `a`, as an exact-length slice.
pub fn sub16(s: &[u16], a: usize, len: usize) -> (r: &[u16])
    requires a + len <= s@.len(),
    ensures r@ == s@.subrange(a as int, a + len),
    no_unwind
{
    let (_, t) = s.split_at(a);
    let (r, _) = t.split_at(len);
    r
}

/// The `len` codes of `s` from `a`, as an exact-length slice.
pub fn sub8(s: &[u8], a: usize, len: usize) -> (r: &[u8])
    requires a + len <= s@.len(),
    ensures r@ == s@.subrange(a as int, a + len),
    no_unwind
{
    let (_, t) = s.split_at(a);
    let (r, _) = t.split_at(len);
    r
}

// ------------------------------------------------------------------------------------------------ gathered blocks

/// Number of qualifying rows in `[a, j)`: the rank of row `j` among the qualifying rows from `a`.
pub open spec fn qn(c: Cols, w: Win, a: int, j: int) -> int
    decreases j - a,
{
    if j <= a { 0 } else { qn(c, w, a, j - 1) + if lqual(c, w, j - 1) { 1int } else { 0int } }
}

/// One more row: the rank grows by one when the row qualifies.
proof fn lemma_qn_step(c: Cols, w: Win, a: int, j: int)
    requires a <= j,
    ensures qn(c, w, a, j + 1) == qn(c, w, a, j) + if lqual(c, w, j) { 1int } else { 0int },
{
}

/// The rank of row `j` from `a` lies in `[0, j - a]`.
proof fn lemma_qn_bound(c: Cols, w: Win, a: int, j: int)
    requires a <= j,
    ensures 0 <= qn(c, w, a, j) <= j - a,
    decreases j - a,
{
    if j > a {
        lemma_qn_bound(c, w, a, j - 1);
    }
}

/// Rows `[j, e)` that never qualify keep the rank.
proof fn lemma_qn_skip(c: Cols, w: Win, a: int, j: int, e: int)
    requires
        a <= j <= e,
        forall|k: int| j <= k < e ==> !#[trigger] lqual(c, w, k),
    ensures qn(c, w, a, e) == qn(c, w, a, j),
    decreases e - j,
{
    if e > j {
        lemma_qn_skip(c, w, a, j, e - 1);
        lemma_qn_step(c, w, a, e - 1);
    }
}

/// The first `n` qualifying rows from `b0`, in row order and below `e`: row `rows[q]` qualifies, has rank `q`, and
/// its l_orderkey and l_shipmode codes are `keys[q]` and `modes[q]`.
pub open spec fn rows_ok(c: Cols, w: Win, b0: int, e: int, n: int, rows: Seq<int>, keys: Seq<u32>, modes: Seq<u8>)
    -> bool
{
    &&& rows.len() == n
    &&& n <= keys.len()
    &&& n <= modes.len()
    &&& forall|q: int| 0 <= q < n ==> {
        &&& b0 <= #[trigger] rows[q] < e
        &&& rows[q] < c.n_l
        &&& lqual(c, w, rows[q])
        &&& qn(c, w, b0, rows[q]) == q
        &&& keys[q] == c.lk_codes@[rows[q]]
        &&& modes[q] == c.lm_codes@[rows[q]]
    }
}

/// Lane `k` of mask `wi` is row `b0 + 64 * wi + k` of the block: set exactly when that row qualifies.
pub open spec fn masks_ok(c: Cols, w: Win, b0: int, nw: int, masks: Seq<u64>) -> bool {
    forall|wi: int, k: int| 0 <= wi < nw && 0 <= k < 64 ==> #[trigger] lane(masks[wi], k) == lqual(c, w, b0 + 64 * wi + k)
}

/// The rank never decreases: `qn(a, i) <= qn(a, j)` for `i <= j`.
proof fn lemma_qn_mono(c: Cols, w: Win, a: int, i: int, j: int)
    requires a <= i <= j,
    ensures qn(c, w, a, i) <= qn(c, w, a, j),
    decreases j - i,
{
    if j > i {
        lemma_qn_mono(c, w, a, i, j - 1);
        lemma_qn_step(c, w, a, j - 1);
    }
}

/// Equal ranks at `i <= j`: no row of `[i, j)` qualifies.
proof fn lemma_qn_flat(c: Cols, w: Win, a: int, i: int, j: int)
    requires
        a <= i <= j,
        qn(c, w, a, i) == qn(c, w, a, j),
    ensures forall|k: int| i <= k < j ==> !#[trigger] lqual(c, w, k),
    decreases j - i,
{
    if i < j {
        lemma_qn_step(c, w, a, i);
        lemma_qn_mono(c, w, a, i + 1, j);
        lemma_qn_flat(c, w, a, i + 1, j);
    }
}

/// Appends the qualifying rows among the 64 rows from `wb` (the set lanes of `x0`) to `rows` (ghost) and their
/// codes to `keys` / `modes`, at their ranks from `b0`; returns the rank of row `wb + 64`.
#[inline(always)]
fn gather_word(c: &Cols, tab: &[u8; 64], w: &Win, Ghost(kp): Ghost<int>, Ghost(km): Ghost<int>, b0: usize, wb: usize, x0: u64,
    q0: usize, keys: &mut [u32], modes: &mut [u8], Ghost(rows0): Ghost<Seq<int>>) -> (r: (usize, Ghost<Seq<int>>))
    requires
        tz_table_ok(*tab),
        cols_ok(*c, kp, km),
        b0 <= wb,
        wb + 64 <= b0 + FB,
        wb + 64 <= c.n_l,
        old(keys)@.len() == FB,
        old(modes)@.len() == FB,
        forall|k: int| 0 <= k < 64 ==> #[trigger] lane(x0, k) == lqual(*c, *w, wb + k),
        q0 == qn(*c, *w, b0 as int, wb as int),
        rows_ok(*c, *w, b0 as int, wb as int, q0 as int, rows0, old(keys)@, old(modes)@),
    ensures
        final(keys)@.len() == FB,
        final(modes)@.len() == FB,
        r.0 == qn(*c, *w, b0 as int, wb + 64),
        rows_ok(*c, *w, b0 as int, wb + 64, r.0 as int, r.1@, final(keys)@, final(modes)@),
    no_unwind
{
    let mut x = x0;
    let ghost mut pos: int = 0;
    let mut q = q0;
    let ghost mut rows = rows0;
    while x != 0
        invariant
            tz_table_ok(*tab),
            cols_ok(*c, kp, km),
            b0 <= wb,
            wb + 64 <= b0 + FB,
            wb + 64 <= c.n_l,
            keys@.len() == FB,
            modes@.len() == FB,
            forall|k: int| 0 <= k < 64 ==> #[trigger] lane(x0, k) == lqual(*c, *w, wb + k),
            0 <= pos <= 64,
            forall|k: int| 0 <= k < 64 ==> #[trigger] lane(x, k) == (k >= pos && lane(x0, k)),
            q == qn(*c, *w, b0 as int, wb + pos),
            rows_ok(*c, *w, b0 as int, wb + pos, q as int, rows, keys@, modes@),
        decreases 64 - pos,
    {
        let t = lowest_lane(tab, x);
        let j = wb + t as usize;
        proof {
            assert(t >= pos);
            assert forall|k: int| wb + pos <= k < j implies !#[trigger] lqual(*c, *w, k) by {
                assert(!lane(x, k - wb));
            }
            lemma_qn_skip(*c, *w, b0 as int, wb + pos, j as int);
            assert(lqual(*c, *w, j as int)) by {
                assert(lane(x0, t as int));
            }
            lemma_qn_bound(*c, *w, b0 as int, j as int);
            lemma_qn_step(*c, *w, b0 as int, j as int);
        }
        keys[q] = c.lk_codes[j];
        modes[q] = c.lm_codes[j];
        proof {
            rows = rows.push(j as int);
        }
        q = q + 1;
        let ghost xo = x;
        x = clear_lowest(x, Ghost(t));
        proof {
            assert forall|k: int| 0 <= k < 64 implies #[trigger] lane(x, k) == (k >= t + 1 && lane(x0, k)) by {
                if k < t {
                    assert(!lane(xo, k));
                }
            }
            pos = t + 1;
        }
    }
    proof {
        assert forall|k: int| wb + pos <= k < wb + 64 implies !#[trigger] lqual(*c, *w, k) by {
            lemma_zero_lanes();
            assert(!lane(x, k - wb));
        }
        lemma_qn_skip(*c, *w, b0 as int, wb + pos, wb + 64);
    }
    (q, Ghost(rows))
}

/// Rows between two rows of one group lie in that group.
proof fn lemma_same_group(a: int, j: int, b: int, bs: int)
    requires 0 <= a <= j <= b, bs >= 1, a / bs == b / bs,
    ensures j / bs == a / bs,
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered(a, j, bs);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(j, b, bs);
}

/// Scans the `FB` rows from `b0` of a small lineitem group `g` in three passes: the lane masks of its 64 words, the
/// l_orderkey and l_shipmode codes of the qualifying rows gathered in row order (independent loads), then the
/// orders of those lines with the cursor, counted per ship-mode entry.
fn scan_block_fast(c: &Cols, tab: &[u8; 64], w: &Win, Ghost(kp): Ghost<int>, km: usize, clustered: bool, g: usize, t: &Thr16,
    b0: usize, masks: &mut [u64], keys: &mut [u32], modes: &mut [u8], cur: &mut Cursor, Ghost(jp): Ghost<int>,
    hi_cnt: &mut Vec<usize>, lo_cnt: &mut Vec<usize>, Ghost(j0): Ghost<int>) -> (jp2: Ghost<int>)
    requires
        tz_table_ok(*tab),
        cols_ok(*c, kp, km as int),
        keys_distinct(*c),
        clustered ==> lines_clustered(*c),
        win_ok(*w),
        0 <= j0 <= b0,
        b0 + FB <= c.n_l,
        g * c.bs_l <= b0,
        b0 + FB <= g * c.bs_l + c.bs_l,
        g < c.lk_bases@.len(),
        thr16_ok(*c, *w, g as int, *t),
        t.fast,
        old(masks)@.len() == 64,
        old(keys)@.len() == FB,
        old(modes)@.len() == FB,
        cursor_ok(*c, *old(cur), jp, b0 as int),
        counts_at(*c, *w, km as int, old(hi_cnt)@, old(lo_cnt)@, j0, b0 as int),
    ensures
        final(masks)@.len() == 64,
        final(keys)@.len() == FB,
        final(modes)@.len() == FB,
        cursor_ok(*c, *final(cur), jp2@, b0 + FB),
        counts_at(*c, *w, km as int, final(hi_cnt)@, final(lo_cnt)@, j0, b0 + FB),
    no_unwind
{
    let ghost mut jp = jp;
    // Pass 1: lane masks.
    let mut wi: usize = 0;
    while wi < 64
        invariant
            tz_table_ok(*tab),
            cols_ok(*c, kp, km as int),
            win_ok(*w),
            0 <= j0 <= b0,
            b0 + FB <= c.n_l,
            g * c.bs_l <= b0,
            b0 + FB <= g * c.bs_l + c.bs_l,
            thr16_ok(*c, *w, g as int, *t),
            t.fast,
            masks@.len() == 64,
            wi <= 64,
            masks_ok(*c, *w, b0 as int, wi as int, masks@),
        decreases 64 - wi,
    {
        let wb = b0 + WL * wi;
        let rw = sub16(c.lr_codes, wb, WL);
        let cw = sub16(c.lc_codes, wb, WL);
        let sw = sub16(c.ls_codes, wb, WL);
        let mw = sub8(c.lm_codes, wb, WL);
        let x = word_mask(c, w, Ghost(kp), Ghost(km as int), Ghost(g as int), t, Ghost(wb as int), rw, cw, sw, mw);
        let ghost m0 = masks@;
        masks[wi] = x;
        proof {
            assert forall|v: int, k: int| 0 <= v < wi + 1 && 0 <= k < 64 implies
                #[trigger] lane(masks@[v], k) == lqual(*c, *w, b0 + 64 * v + k) by {
                if v < wi {
                    assert(masks@[v] == m0[v]);
                }
            }
        }
        wi = wi + 1;
    }
    // Pass 2: the qualifying rows (ghost) and their codes, in row order.
    let mut nq: usize = 0;
    let ghost mut rows: Seq<int> = Seq::empty();
    let mut wi: usize = 0;
    while wi < 64
        invariant
            tz_table_ok(*tab),
            cols_ok(*c, kp, km as int),
            b0 + FB <= c.n_l,
            masks@.len() == 64,
            keys@.len() == FB,
            modes@.len() == FB,
            masks_ok(*c, *w, b0 as int, 64, masks@),
            wi <= 64,
            nq == qn(*c, *w, b0 as int, b0 + 64 * wi),
            rows_ok(*c, *w, b0 as int, b0 + 64 * wi, nq as int, rows, keys@, modes@),
        decreases 64 - wi,
    {
        let wb = b0 + WL * wi;
        let x = masks[wi];
        proof {
            assert forall|k: int| 0 <= k < 64 implies #[trigger] lane(x, k) == lqual(*c, *w, wb + k) by {
                assert(lane(masks@[wi as int], k) == lqual(*c, *w, b0 + 64 * wi + k));
            }
        }
        let (q2, rows2) = gather_word(c, tab, w, Ghost(kp), Ghost(km as int), b0, wb, x, nq, keys, modes, Ghost(rows));
        nq = q2;
        proof {
            rows = rows2@;
        }
        wi = wi + 1;
    }
    // Pass 3: the qualifying lines in row order, by rank; the rows between them never qualify (equal ranks).
    let kb = c.lk_bases[g];
    let mb = c.lm_bases[g];
    proof {
        lemma_div_group(b0 as int, c.bs_l as int, g as int);
        lemma_div_group(b0 + FB - 1, c.bs_l as int, g as int);
    }
    let ghost mut e: int = b0 as int;
    let mut q: usize = 0;
    while q < nq
        invariant
            tz_table_ok(*tab),
            cols_ok(*c, kp, km as int),
            keys_distinct(*c),
            clustered ==> lines_clustered(*c),
            0 <= j0 <= b0,
            b0 + FB <= c.n_l,
            (b0 as int) / (c.bs_l as int) == g,
            (b0 + FB - 1) / (c.bs_l as int) == g,
            g < c.lk_bases@.len(),
            kb == c.lk_bases@[g as int],
            mb == c.lm_bases@[g as int],
            keys@.len() == FB,
            modes@.len() == FB,
            nq == qn(*c, *w, b0 as int, b0 + FB),
            rows_ok(*c, *w, b0 as int, b0 + FB, nq as int, rows, keys@, modes@),
            q <= nq,
            b0 <= e <= b0 + FB,
            qn(*c, *w, b0 as int, e) == q,
            cursor_ok(*c, *cur, jp, e),
            counts_at(*c, *w, km as int, hi_cnt@, lo_cnt@, j0, e),
        decreases nq - q,
    {
        let ghost j = rows[q as int];
        proof {
            assert(b0 <= j < b0 + FB && lqual(*c, *w, j) && qn(*c, *w, b0 as int, j) == q);
            if j < e {
                lemma_qn_step(*c, *w, b0 as int, j);
                lemma_qn_mono(*c, *w, b0 as int, j + 1, e);
            }
            lemma_qn_flat(*c, *w, b0 as int, e, j);
            lemma_counts_skip(*c, *w, km as int, hi_cnt@, lo_cnt@, j0, e, j);
            lemma_same_group(b0 as int, j, b0 + FB - 1, c.bs_l as int);
            assert(0 <= lmode(*c, j) < km);
            lemma_qn_step(*c, *w, b0 as int, j);
        }
        let kc = keys[q];
        let m = (mb + modes[q] as u64) as usize;
        let jpg = count_line(c, tab, w, Ghost(kp), km, clustered, kb, kc, Ghost(j), m, cur, Ghost(jp), hi_cnt, lo_cnt,
            Ghost(j0));
        proof {
            jp = jpg@;
            e = j + 1;
        }
        q = q + 1;
    }
    proof {
        lemma_qn_flat(*c, *w, b0 as int, e, b0 + FB);
        lemma_counts_skip(*c, *w, km as int, hi_cnt@, lo_cnt@, j0, e, b0 + FB);
    }
    Ghost(jp)
}

/// Scans rows `[start, end)` of lineitem group `g` block by block: whole blocks of a small group by the run-start
/// join when the runs match the orders (`runs`), else by the gathered cursor walk; the rest by the general path.
fn scan_rows(c: &Cols, tab: &[u8; 64], w: &Win, Ghost(kp): Ghost<int>, km: usize, clustered: bool, g: usize, start: usize, end: usize,
    flags: &mut [u8], masks: &mut [u64], keys: &mut [u32], modes: &mut [u8], cur: &mut Cursor, Ghost(jp): Ghost<int>, hi_cnt: &mut Vec<usize>, lo_cnt: &mut Vec<usize>,
    Ghost(j0): Ghost<int>, st: &[u32], b: &Bits, sel: &Sel, fast: bool, base: &mut usize, valid: &mut bool)
    -> (jp2: Ghost<int>)
    requires
        fast ==> fast_ok(*c, *w, st@, *b, *sel),
        fast && *old(valid) ==> *old(base) as int == nst(*c, start as int),
        start == g * c.bs_l,
        tz_table_ok(*tab),
        cols_ok(*c, kp, km as int),
        keys_distinct(*c),
        clustered ==> lines_clustered(*c),
        win_ok(*w),
        0 <= j0 <= start < end <= c.n_l,
        old(flags)@.len() == FB,
        old(masks)@.len() == 64,
        old(keys)@.len() == FB,
        old(modes)@.len() == FB,
        g * c.bs_l <= start,
        end <= g * c.bs_l + c.bs_l,
        cursor_ok(*c, *old(cur), jp, start as int),
        counts_at(*c, *w, km as int, old(hi_cnt)@, old(lo_cnt)@, j0, start as int),
    ensures
        final(flags)@.len() == FB,
        final(masks)@.len() == 64,
        final(keys)@.len() == FB,
        final(modes)@.len() == FB,
        cursor_ok(*c, *final(cur), jp2@, end as int),
        counts_at(*c, *w, km as int, final(hi_cnt)@, final(lo_cnt)@, j0, end as int),
        fast && *final(valid) ==> *final(base) as int == nst(*c, end as int),
    no_unwind
{
    let ghost mut jp = jp;
    proof {
        lemma_div_group(start as int, c.bs_l as int, g as int);
        lemma_div_below(start as int, c.bs_l as int, c.lk_bases@.len() as int);
    }
    let t = group_thr(c, w, g);
    let t16 = group_thr16(c, w, g);
    let mut b0 = start;
    let mut wg = start / 64;
    proof {
        if fast {
            lemma_word_start(g as int, c.bs_l as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(start as int, 64);
        }
    }
    // Fast path of a small group: whole blocks.
    if t16.fast {
        while end - b0 >= FB
            invariant
                tz_table_ok(*tab),
                cols_ok(*c, kp, km as int),
                keys_distinct(*c),
                clustered ==> lines_clustered(*c),
                win_ok(*w),
                0 <= j0 <= start <= b0 <= end <= c.n_l,
                g * c.bs_l <= start,
                end <= g * c.bs_l + c.bs_l,
                g < c.lk_bases@.len(),
                flags@.len() == FB,
                masks@.len() == 64,
                keys@.len() == FB,
                modes@.len() == FB,
                thr_ok(*c, *w, g as int, t),
                thr16_ok(*c, *w, g as int, t16),
                t16.fast,
                cursor_ok(*c, *cur, jp, b0 as int),
                counts_at(*c, *w, km as int, hi_cnt@, lo_cnt@, j0, b0 as int),
                fast ==> fast_ok(*c, *w, st@, *b, *sel),
                fast && *valid ==> *base as int == nst(*c, b0 as int),
                fast ==> b0 == 64 * wg,
            decreases end - b0,
        {
            if fast {
                if !*valid {
                    *base = rank_at(c, st, b, Ghost(*w), Ghost(*sel), b0);
                    *valid = true;
                }
                *base = scan_block_bits(c, w, b, sel, tab, Ghost(st@), Ghost(kp), km, g, &t16, wg, *base, hi_cnt, lo_cnt,
                    Ghost(j0));
                proof {
                    lemma_cursor_later(*c, *cur, jp, b0 as int, b0 + FB);
                }
                wg = wg + 64;
            } else {
                let jpg = scan_block_fast(c, tab, w, Ghost(kp), km, clustered, g, &t16, b0, masks, keys, modes, cur, Ghost(jp),
                    hi_cnt, lo_cnt, Ghost(j0));
                proof {
                    jp = jpg@;
                }
            }
            b0 = b0 + FB;
        }
    }
    // General path: blocks of the two-phase scan.
    if b0 < end {
        *valid = false;
    }
    while b0 < end
        invariant
            tz_table_ok(*tab),
            cols_ok(*c, kp, km as int),
            keys_distinct(*c),
            clustered ==> lines_clustered(*c),
            win_ok(*w),
            0 <= j0 <= start <= b0 <= end <= c.n_l,
            flags@.len() == FB,
            masks@.len() == 64,
            keys@.len() == FB,
            modes@.len() == FB,
            g * c.bs_l <= start,
            end <= g * c.bs_l + c.bs_l,
            g < c.lk_bases@.len(),
            thr_ok(*c, *w, g as int, t),
            cursor_ok(*c, *cur, jp, b0 as int),
            counts_at(*c, *w, km as int, hi_cnt@, lo_cnt@, j0, b0 as int),
            fast ==> fast_ok(*c, *w, st@, *b, *sel),
            b0 < end ==> !*valid,
            fast && *valid ==> *base as int == nst(*c, b0 as int),
        decreases end - b0,
    {
        let n = if end - b0 < FB { end - b0 } else { FB };
        let jpg = scan_block(c, tab, w, Ghost(kp), km, clustered, g, &t, b0, n, flags, cur, Ghost(jp), hi_cnt, lo_cnt,
            Ghost(j0));
        proof {
            jp = jpg@;
        }
        b0 = b0 + n;
    }
    Ghost(jp)
}

/// A group of a size that is a multiple of 64 starts at a word boundary.
proof fn lemma_word_start(g: int, bs: int)
    requires g >= 0, bs >= 1, bs % 64 == 0,
    ensures (g * bs) % 64 == 0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(bs, 64);
    let q = bs / 64;
    assert(g * bs == 64 * (g * q)) by (nonlinear_arith) requires bs == 64 * q;
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(g * q, 64);
    assert((g * q) * 64 == 64 * (g * q)) by (nonlinear_arith);
}

/// The first stored row of group `g` (`row_of`), computed without overflow.
fn group_start(c: &Cols, g: usize) -> (r: usize)
    requires c.bs_l >= 1,
    ensures
        r as int == row_of(*c, g as int),
        r <= c.n_l,
    no_unwind
{
    match g.checked_mul(c.bs_l) {
        Some(x) => if x >= c.n_l { c.n_l } else { x },
        None => {
            proof {
                assert(g * c.bs_l > usize::MAX);
            }
            c.n_l
        },
    }
}

/// Consecutive group starts: `row_of(g + 1)` is `row_of(g)` plus at most one group, and the rows in between belong
/// to group `g`.
proof fn lemma_row_of_next(c: Cols, g: int)
    requires g >= 0, c.bs_l >= 1,
    ensures
        row_of(c, g) <= row_of(c, g + 1),
        row_of(c, g) < row_of(c, g + 1) ==> g * c.bs_l == row_of(c, g),
        row_of(c, g + 1) <= g * c.bs_l + c.bs_l || row_of(c, g) == row_of(c, g + 1),
{
    lemma_next_group(g, c.bs_l as int);
    assert(g * c.bs_l <= (g + 1) * c.bs_l) by (nonlinear_arith) requires c.bs_l >= 1;
}

/// Rows of group `g` whose receipt-date zone misses `[lo, hi]` never qualify.
proof fn lemma_zone_skip(c: Cols, w: Win, kp: int, km: int, g: int, a: int, b: int)
    requires
        cols_ok(c, kp, km),
        0 <= g < c.lk_bases@.len(),
        g * c.bs_l <= a <= b <= c.n_l,
        b <= g * c.bs_l + c.bs_l,
        c.lr_bases@[g] > w.hi || c.lr_zmax@[g] < w.lo || c.lc_bases@[g] >= w.hi,
    ensures forall|j: int| a <= j < b ==> !#[trigger] lqual(c, w, j),
{
    assert forall|j: int| a <= j < b implies !#[trigger] lqual(c, w, j) by {
        lemma_div_group(j, c.bs_l as int, g);
        assert(lrcp(c, j) <= c.lr_zmax@[j / c.bs_l as int]);
        assert(lrcp(c, j) >= c.lr_bases@[g]);
        assert(lcmt(c, j) >= c.lc_bases@[g]);
    }
}

impl WorkerTask for ScanTask {
    type Output = (Vec<usize>, Vec<usize>);

    open spec fn pre(&self) -> bool {
        &&& cols_ok(self.cols, self.kp as int, self.km as int)
        &&& keys_distinct(self.cols)
        &&& self.clustered ==> lines_clustered(self.cols)
        &&& win_ok(self.win)
        &&& self.g0 <= self.g1 <= self.cols.lk_bases@.len()
        &&& self.hi_cnt@ == zeros(self.km as nat)
        &&& self.lo_cnt@ == zeros(self.km as nat)
        &&& tz_table_ok(self.tab)
        &&& self.fast ==> fast_ok(self.cols, self.win, self.st@, self.bits, self.sel)
    }

    open spec fn post(&self, out: (Vec<usize>, Vec<usize>)) -> bool {
        counts_at(self.cols, self.win, self.km as int, out.0@, out.1@,
            row_of(self.cols, self.g0 as int), row_of(self.cols, self.g1 as int))
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.g0 as u64, self.g1 as u64)
    }

    fn run(self) -> (out: (Vec<usize>, Vec<usize>)) {
        let c = self.cols;
        let w = self.win;
        let ghost kp = self.kp as int;
        let km = self.km;
        let g0 = self.g0;
        let g1 = self.g1;
        let clustered = self.clustered;
        let mut hi_cnt = self.hi_cnt;
        let mut lo_cnt = self.lo_cnt;
        let mut flags_arr = self.flags;
        let flags: &mut [u8] = &mut flags_arr;
        let mut masks_arr = self.masks;
        let masks: &mut [u64] = &mut masks_arr;
        let mut keys_arr = self.keys;
        let keys: &mut [u32] = &mut keys_arr;
        let mut modes_arr = self.modes;
        let modes: &mut [u8] = &mut modes_arr;
        let tab = self.tab;
        let st = self.st;
        let bits = self.bits;
        let sel = self.sel;
        let fast = self.fast;
        let mut base: usize = 0;
        let mut valid = false;
        let mut cur = Cursor { p: 0, gp: 0, rem: c.bs_o, valid: false };
        let ghost mut jp: int = 0;
        let j0 = group_start(&c, g0);
        proof {
            assert(0 * c.bs_o == 0);
            assert(counts_at(c, w, km as int, hi_cnt@, lo_cnt@, j0 as int, j0 as int));
        }
        let mut g = g0;
        let mut start = j0;
        while g < g1
            invariant
                tz_table_ok(tab),
                cols_ok(c, kp, km as int),
                keys_distinct(c),
                clustered ==> lines_clustered(c),
                win_ok(w),
                flags@.len() == FB,
                masks@.len() == 64,
                keys@.len() == FB,
                modes@.len() == FB,
                g0 <= g <= g1 <= c.lk_bases@.len(),
                j0 as int == row_of(c, g0 as int),
                start as int == row_of(c, g as int),
                j0 <= start <= c.n_l,
                cursor_ok(c, cur, jp, start as int),
                counts_at(c, w, km as int, hi_cnt@, lo_cnt@, j0 as int, start as int),
                fast ==> fast_ok(c, w, st@, bits, sel),
                fast && valid ==> base as int == nst(c, start as int),
            decreases g1 - g,
        {
            let end = group_start(&c, g + 1);
            proof {
                lemma_row_of_next(c, g as int);
            }
            if start < end {
                if c.lr_bases[g] > w.hi || c.lr_zmax[g] < w.lo || c.lc_bases[g] >= w.hi {
                    valid = false;
                    proof {
                        lemma_zone_skip(c, w, kp, km as int, g as int, start as int, end as int);
                        lemma_counts_skip(c, w, km as int, hi_cnt@, lo_cnt@, j0 as int, start as int, end as int);
                    }
                } else {
                    let jpg = scan_rows(&c, &tab, &w, Ghost(kp), km, clustered, g, start, end, flags, masks, keys, modes, &mut cur, Ghost(jp),
                        &mut hi_cnt, &mut lo_cnt, Ghost(j0 as int), st, &bits, &sel, fast, &mut base, &mut valid);
                    proof {
                        jp = jpg@;
                    }
                }
            }
            g = g + 1;
            start = end;
        }
        (hi_cnt, lo_cnt)
    }
}

} // verus!
