//! The lineitem scan of one row range `[lo, hi)` (`ScanTask`, one worker task per range): per selected supplier
//! (`SupMap`, compact index `ci`), the count of its key over the range's waiting rows.
//!
//! The rows are read in windows of at most 64 (`scan_range`). One pass over a window (`window_masks`, a simple loop
//! the compiler vectorizes) builds two bit masks: bit `u` of `sm` is a change of `l_orderkey` at row `p + u`, bit `u`
//! of `lm` is row `p + u` late (`l_receiptdate > l_commitdate`); it also checks that the keys do not decrease. The
//! runs of equal keys that end inside the window end at the highest key change `an` (`window_runs`). Per run only
//! its first late row matters: when the supplier of that row is not selected (`may_select`, a bitmap test), no row
//! of the run waits for a selected supplier (that late row is a late row of another supplier for every other late
//! row of its order; `lemma_window_skip`), so the run adds nothing. The first late rows of all runs are the bits of
//! one mask computed with a carry-propagating addition (`common::segmask::first_marks`), so a run costs one bit scan,
//! one `l_suppkey` load and one bitmap test. The few runs whose first late row has a selected supplier are evaluated
//! row by row (`run_exact`, `runs::st_ok`), and a candidate looks up its order (`find_order`) and status `F`. The
//! window's last unfinished run starts the next window; a run longer than a window is scanned to its end. Proof:
//! under the hypothesis that `l_orderkey` is sorted every visited run is complete (`runs::lemma_run_complete`); the
//! counts are the counts of the rows before the current run (`cnt_ok`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::{text_at, text_wf};
use crate::agent::cols::*;
use crate::agent::nf::*;
use crate::agent::runs::*;
use crate::agent::common::bits64::*;
use crate::agent::common::segmask::*;

verus! {

/// Rows per window of the mask pass (the bits of one `u64`).
pub const WIN: usize = 64;

// ------------------------------------------------------------------------------------------------ selected suppliers

/// The selected supplier rows `sel` (ascending; compact index `ci` is `sel[ci]`) and two lookups. With dense keys
/// (`s_suppkey[s] == base + s`, as dbgen writes them) `cmap[s]` is `ci + 1` for the selected row `s` and 0 for the
/// others, and bit `s` of the bitmap `nb` (64 rows per word) is set exactly for the selected rows; otherwise the
/// lookup scans `sel` and every key may be selected. `tab` is the table of `bits64::low_bit`.
pub struct SupMap {
    pub dense: bool,
    pub cmap: Vec<u32>,
    pub nb: Vec<u64>,
    pub tab: Vec<u8>,
    pub base: i64,
    pub sel: Vec<usize>,
    pub skey: &'static [i64],
    pub ns: usize,
    pub nsel: usize,
}

/// Bit `d` of a bitmap of 64-bit words.
pub open spec fn nbit(nb: Seq<u64>, d: int) -> bool { bit(nb[d / 64], (d % 64) as u64) }

/// The bitmap `nb` marks exactly the rows with a compact index in `cmap` (opaque: only `may_select` and the builder
/// look inside).
#[verifier::opaque]
pub open spec fn bitmap_ok(m: SupMap) -> bool {
    &&& m.nb@.len() == m.ns / 64 + 1
    &&& forall|s: int| 0 <= s < m.ns ==> #[trigger] nbit(m.nb@, s) == (m.cmap@[s] != 0)
}

/// Ascending rows below `ns`.
pub open spec fn sel_ok(sel: Seq<usize>, ns: int) -> bool {
    &&& forall|c: int| 0 <= c < sel.len() ==> (#[trigger] sel[c]) < ns
    &&& forall|c: int, d: int| 0 <= c < d < sel.len() ==> #[trigger] sel[c] < #[trigger] sel[d]
}

pub open spec fn sup_ok(m: SupMap, sv: StoresView) -> bool {
    &&& m.skey@ == skey(sv)
    &&& m.ns as int == n_s(sv)
    &&& keys_unique(skey(sv))
    &&& m.nsel == m.sel@.len()
    &&& sel_ok(m.sel@, m.ns as int)
    &&& m.tab@.len() == 64
    &&& m.dense ==> {
        &&& m.nsel < u32::MAX
        &&& m.cmap@.len() == m.ns
        &&& forall|s: int| 0 <= s < m.ns ==> #[trigger] skey(sv)[s] as int == m.base as int + s
        &&& forall|s: int| 0 <= s < m.ns && #[trigger] m.cmap@[s] != 0 ==> m.cmap@[s] - 1 < m.nsel && m.sel@[m.cmap@[s] - 1] == s
        &&& forall|c: int| 0 <= c < m.nsel ==> m.cmap@[#[trigger] m.sel@[c] as int] == c + 1
        &&& bitmap_ok(m)
    }
}

/// The supplier key of compact index `ci`.
pub open spec fn ckey(m: SupMap, ci: int) -> int { m.skey@[m.sel@[ci] as int] as int }

/// Different compact indices have different keys.
pub proof fn lemma_ckey_unique(m: SupMap, sv: StoresView, c1: int, c2: int)
    requires sup_ok(m, sv), 0 <= c1 < m.nsel, 0 <= c2 < m.nsel, ckey(m, c1) == ckey(m, c2),
    ensures c1 == c2,
{
    let (s1, s2) = (m.sel@[c1] as int, m.sel@[c2] as int);
    assert(skey(sv)[s1] == skey(sv)[s2]);
    assert(s1 == s2);
    if c1 < c2 { assert(m.sel@[c1] < m.sel@[c2]); }
    if c2 < c1 { assert(m.sel@[c2] < m.sel@[c1]); }
}

/// The compact index of the selected supplier with key `v`, if any.
pub fn lookup(m: &SupMap, v: i64, Ghost(sv): Ghost<StoresView>) -> (r: Option<usize>)
    requires sup_ok(*m, sv),
    ensures
        r matches Some(ci) ==> ci < m.nsel && ckey(*m, ci as int) == v as int,
        r is None ==> forall|ci: int| 0 <= ci < m.nsel ==> ckey(*m, ci) != v as int,
    no_unwind
{
    if m.dense {
        let d: i128 = v as i128 - m.base as i128;
        if d >= 0 && d < m.ns as i128 {
            let du = d as usize;
            let cv = m.cmap[du];
            if cv != 0 {
                proof {
                    assert(m.sel@[cv - 1] == du);
                    assert(skey(sv)[du as int] as int == m.base as int + du);
                }
                return Some((cv - 1) as usize);
            }
            proof {
                assert forall|ci: int| 0 <= ci < m.nsel implies ckey(*m, ci) != v as int by {
                    let s = m.sel@[ci] as int;
                    if ckey(*m, ci) == v as int {
                        assert(skey(sv)[s] as int == m.base as int + s);
                        assert(s == du);
                        assert(m.cmap@[m.sel@[ci] as int] == ci + 1);
                    }
                }
            }
            return None;
        }
        proof {
            assert forall|ci: int| 0 <= ci < m.nsel implies ckey(*m, ci) != v as int by {
                let s = m.sel@[ci] as int;
                assert(skey(sv)[s] as int == m.base as int + s);
            }
        }
        return None;
    }
    let mut ci: usize = 0;
    while ci < m.nsel
        invariant
            sup_ok(*m, sv), ci <= m.nsel,
            forall|c: int| 0 <= c < ci ==> ckey(*m, c) != v as int,
        decreases m.nsel - ci,
    {
        if m.skey[m.sel[ci]] == v {
            return Some(ci);
        }
        ci = ci + 1;
    }
    None
}

// ------------------------------------------------------------------------------------------------ orders

/// A row of `ok` holding key `k`, or `no` when no row does. The search starts at the cursor `cur` and gallops forward
/// (the keys ascend in dbgen order); any answer is checked, and a miss falls back to a scan of every row.
pub fn find_order(ok: &'static [i64], no: usize, k: i64, cur: usize) -> (r: usize)
    requires ok@.len() == no,
    ensures
        r <= no,
        r < no ==> ok@[r as int] == k,
        r == no ==> forall|o: int| 0 <= o < no ==> ok@[o] != k,
    no_unwind
{
    let mut lo: usize = if cur < no { cur } else { 0 };
    if lo < no && ok[lo] == k {
        return lo;
    }
    if lo < no && ok[lo] < k {
        let mut step: usize = 1;
        while step < no - lo && ok[lo + step] < k
            invariant ok@.len() == no, lo < no, 1 <= step,
            decreases no - lo,
        {
            lo = lo + step;
            if step <= (no - lo) / 2 {
                step = step * 2;
            }
        }
        let mut a: usize = lo + 1;
        let mut b: usize = if step < no - lo { lo + step } else { no - 1 };
        while a < b
            invariant ok@.len() == no, lo < no, a <= b + 1, b < no,
            decreases b - a,
        {
            let mid = a + (b - a) / 2;
            if ok[mid] < k {
                a = mid + 1;
            } else {
                b = mid;
            }
        }
        if a < no && ok[a] == k {
            return a;
        }
    }
    let mut i: usize = 0;
    while i < no
        invariant ok@.len() == no, i <= no, forall|o: int| 0 <= o < i ==> ok@[o] != k,
        decreases no - i,
    {
        if ok[i] == k {
            return i;
        }
        i = i + 1;
    }
    no
}

/// Whether orders row `o` has status `F` (`o_orderstatus = 'F'`).
pub fn status_f(c: &Cols, o: usize, Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires cols_ok(*c, sv), o < c.no,
    ensures r == fstat(sv, o as int),
    no_unwind
{
    let a = c.soff[o];
    let b = c.soff[o + 1];
    proof {
        assert(text_wf(ostat_col(sv), n_o(sv)));
        assert(0 <= c.soff@[o as int] <= c.soff@[o + 1] <= c.sb@.len());
    }
    if b - a == 1 {
        let x = c.sb[a as usize];
        proof {
            let t = ostat(sv, o as int);
            assert(t == c.sb@.subrange(a as int, b as int));
            assert(t.len() == 1 && t[0] == x);
            if x == 70u8 { assert(t =~= seq![70u8]); }
        }
        x == 70u8
    } else {
        proof {
            assert(ostat(sv, o as int).len() != 1);
        }
        false
    }
}

/// Whether supplier key `v` may be selected: `false` only when no selected supplier has key `v` (a bitmap test with
/// dense keys; always `true` otherwise).
pub fn may_select(m: &SupMap, v: i64, Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires sup_ok(*m, sv),
    ensures !r ==> forall|ci: int| 0 <= ci < m.nsel ==> ckey(*m, ci) != v as int,
    no_unwind
{
    reveal(bitmap_ok);
    if !m.dense {
        return true;
    }
    let d: i128 = v as i128 - m.base as i128;
    if d < 0 || d >= m.ns as i128 {
        proof {
            assert forall|ci: int| 0 <= ci < m.nsel implies ckey(*m, ci) != v as int by {
                let s = m.sel@[ci] as int;
                assert(skey(sv)[s] as int == m.base as int + s);
            }
        }
        return false;
    }
    let du = d as usize;
    proof {
        assert(du / 64 <= m.ns / 64) by (nonlinear_arith) requires du < m.ns;
    }
    let wd = m.nb[du / 64];
    let r = (wd >> ((du % 64) as u64)) & 1u64 == 1u64;
    proof {
        if !r {
            assert(!nbit(m.nb@, du as int));
            assert(m.cmap@[du as int] == 0);
            assert forall|ci: int| 0 <= ci < m.nsel implies ckey(*m, ci) != v as int by {
                let s = m.sel@[ci] as int;
                assert(skey(sv)[s] as int == m.base as int + s);
                if ckey(*m, ci) == v as int {
                    assert(s == du);
                    assert(m.cmap@[m.sel@[ci] as int] == ci + 1);
                }
            }
        }
    }
    r
}

// ------------------------------------------------------------------------------------------------ counts so far

/// The counts after the rows `[lo, x)`: when the keys are sorted, each count is its key's count over the rows; each
/// count is at most the number of rows.
pub open spec fn cnt_ok(m: SupMap, sv: StoresView, lo: int, x: int, cnt: Seq<u64>) -> bool {
    &&& cnt.len() == m.nsel
    &&& sorted(sv) ==> forall|ci: int| 0 <= ci < m.nsel ==> #[trigger] cnt[ci] as int == ksum(sv, ckey(m, ci), lo, x)
    &&& forall|ci: int| 0 <= ci < m.nsel ==> #[trigger] cnt[ci] as int <= x - lo
}

/// A run that adds nothing for any selected key keeps the counts.
proof fn lemma_cnt_skip(m: SupMap, sv: StoresView, lo: int, ra: int, re: int, cnt: Seq<u64>)
    requires
        cnt_ok(m, sv, lo, ra, cnt), lo <= ra <= re,
        forall|ci: int| 0 <= ci < m.nsel ==> ksum(sv, #[trigger] ckey(m, ci), ra, re) == 0,
    ensures cnt_ok(m, sv, lo, re, cnt),
{
    assert forall|ci: int| 0 <= ci < m.nsel implies #[trigger] cnt[ci] as int <= re - lo by {}
    if sorted(sv) {
        assert forall|ci: int| 0 <= ci < m.nsel implies #[trigger] cnt[ci] as int == ksum(sv, ckey(m, ci), lo, re) by {
            lemma_ksum_split(sv, ckey(m, ci), lo, ra, re);
        }
    }
}

// ------------------------------------------------------------------------------------------------ runs that add nothing

/// Equal adjacent keys over `(a, b)`: every key of `[a, b)` is row `a`'s.
proof fn lemma_adjacent_eq(sv: StoresView, a: int, b: int)
    requires 0 <= a < b <= n_l(sv), forall|t: int| a < t < b ==> #[trigger] lk(sv)[t] == lk(sv)[t - 1],
    ensures forall|t: int| a <= t < b ==> #[trigger] lk(sv)[t] == lk(sv)[a],
    decreases b - a,
{
    if b - 1 > a {
        lemma_adjacent_eq(sv, a, b - 1);
        assert(lk(sv)[b - 1] == lk(sv)[b - 2]);
    }
}

// ------------------------------------------------------------------------------------------------ the exact path

/// The counts of the complete run `[ra, re)`, row by row: its late rows, the supplier `ll` of the last one, whether
/// two late rows have different suppliers (`mb`) and whether two rows do (`db`); a candidate run (`runs::cand`) adds
/// its late count to `ll`'s count when its order has status `F`.
#[inline(never)]
fn run_exact(c: &Cols, m: &SupMap, cnt: &mut Vec<u64>, ra: usize, re: usize, cur: usize, Ghost(sv): Ghost<StoresView>,
    Ghost(lo): Ghost<int>) -> (cur2: usize)
    requires
        cols_ok(*c, sv), sup_ok(*m, sv), run_ok(sv, ra as int, re as int), 0 <= lo <= ra,
        cnt_ok(*m, sv, lo, ra as int, old(cnt)@),
    ensures cnt_ok(*m, sv, lo, re as int, final(cnt)@),
    no_unwind
{
    let ghost c0 = cnt@;
    let key = c.lk[ra];
    let mut ll: i64 = 0;
    let mut nlate: u64 = 0;
    let mut mb = false;
    let mut db = false;
    let mut ps: i64 = c.ls[ra];
    let mut t: usize = ra;
    proof { lemma_st_empty(sv, ra as int, ll); }
    while t < re
        invariant
            cols_ok(*c, sv), run_ok(sv, ra as int, re as int), ra <= t <= re,
            st_ok(sv, ra as int, t as int, mb, db, ll, nlate),
            t > ra ==> ps == ls(sv)[t - 1],
            t == ra ==> ps == ls(sv)[ra as int],
        decreases re - t,
    {
        let s = c.ls[t];
        let lt = c.lr[t] > c.lc[t];
        proof {
            lemma_nlr(sv, ra as int, t as int);
            lemma_step(sv, ra as int, t as int, mb, db, ll, nlate, ps);
        }
        if lt && nlate > 0 && s != ll {
            mb = true;
        }
        if s != ps {
            db = true;
        }
        if lt {
            ll = s;
            nlate = nlate + 1;
        }
        ps = s;
        t = t + 1;
    }
    proof { lemma_nlr(sv, ra as int, re as int); }
    let mut cur2 = cur;
    if nlate > 0 && !mb && db {
        match lookup(m, ll, Ghost(sv)) {
            Some(ci0) => {
                let o = find_order(c.ok, c.no, key, cur);
                let mut add = false;
                if o < c.no {
                    cur2 = o;
                    add = status_f(c, o, Ghost(sv));
                    proof { lemma_ofs_found(sv, key as int, o as int); }
                } else {
                    proof { lemma_ofs_none(sv, key as int); }
                }
                if add {
                    cnt[ci0] = cnt[ci0] + nlate;
                }
                proof {
                    let w = ofs(sv, key as int) as int;
                    assert(nlate as int * w == if add { nlate as int } else { 0 }) by (nonlinear_arith)
                        requires w == if add { 1int } else { 0int };
                    assert forall|ci: int| 0 <= ci < m.nsel implies #[trigger] cnt@[ci] as int <= re - lo by {}
                    if sorted(sv) {
                        assert forall|ci: int| 0 <= ci < m.nsel implies #[trigger] cnt@[ci] as int
                            == ksum(sv, ckey(*m, ci), lo, re as int) by {
                            lemma_run_contrib(sv, ra as int, re as int, mb, db, ll, nlate, ckey(*m, ci));
                            lemma_ksum_split(sv, ckey(*m, ci), lo, ra as int, re as int);
                            if ci != ci0 as int && ckey(*m, ci) == ll as int {
                                lemma_ckey_unique(*m, sv, ci, ci0 as int);
                            }
                        }
                    }
                }
            },
            None => {
                proof {
                    assert forall|ci: int| 0 <= ci < m.nsel implies #[trigger] cnt@[ci] as int <= re - lo by {}
                    if sorted(sv) {
                        assert forall|ci: int| 0 <= ci < m.nsel implies #[trigger] cnt@[ci] as int
                            == ksum(sv, ckey(*m, ci), lo, re as int) by {
                            lemma_run_contrib(sv, ra as int, re as int, mb, db, ll, nlate, ckey(*m, ci));
                            lemma_ksum_split(sv, ckey(*m, ci), lo, ra as int, re as int);
                        }
                    }
                }
            },
        }
    } else {
        proof {
            assert forall|ci: int| 0 <= ci < m.nsel implies #[trigger] cnt@[ci] as int <= re - lo by {}
            if sorted(sv) {
                assert forall|ci: int| 0 <= ci < m.nsel implies #[trigger] cnt@[ci] as int
                    == ksum(sv, ckey(*m, ci), lo, re as int) by {
                    lemma_run_contrib(sv, ra as int, re as int, mb, db, ll, nlate, ckey(*m, ci));
                    lemma_ksum_split(sv, ckey(*m, ci), lo, ra as int, re as int);
                }
            }
        }
    }
    cur2
}

// ------------------------------------------------------------------------------------------------ the window masks

/// The masks of the window `[p, p + w)`: bit `u` of `sm` is a key change at row `p + u` (never at `u == 0`), bit `u`
/// of `lm` is row `p + u` late; no bit at or above `w` is set.
pub open spec fn masks_ok(sv: StoresView, p: int, w: int, sm: u64, lm: u64) -> bool {
    &&& forall|u: u64| u < 64 ==> #[trigger] bit(sm, u) == (u < w && u > 0 && lk(sv)[p + u] != lk(sv)[p + u - 1])
    &&& forall|u: u64| u < 64 ==> #[trigger] bit(lm, u) == (u < w && late(sv, p + u))
}

/// The masks of one window and whether its adjacent keys are ordered (one simple pass over the rows; no branches).
#[inline(always)]
fn window_masks(lkw: &[i64], lcw: &[i32], lrw: &[i32], w: usize, Ghost(sv): Ghost<StoresView>, Ghost(p): Ghost<int>)
    -> (r: (u64, u64, bool))
    requires
        1 <= w <= WIN, lkw@.len() == w, lcw@.len() == w, lrw@.len() == w, 0 <= p, p + w <= n_l(sv),
        lc(sv).len() == n_l(sv), lr(sv).len() == n_l(sv),
        lkw@ == lk(sv).subrange(p, p + w), lcw@ == lc(sv).subrange(p, p + w), lrw@ == lr(sv).subrange(p, p + w),
    ensures
        masks_ok(sv, p, w as int, r.0, r.1),
        r.2 ==> forall|t: int| p < t < p + w ==> #[trigger] pair_ok(sv, t),
    no_unwind
{
    let mut sm: u64 = 0;
    let mut lm: u64 = 0;
    let mut bad = false;
    let mut prev: i64 = lkw[0];
    let mut t: usize = 0;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bit(0u64, u) by { lemma_bit_zero(u); }
    }
    while t < w
        invariant
            1 <= w <= WIN, lkw@.len() == w, lcw@.len() == w, lrw@.len() == w, 0 <= p, p + w <= n_l(sv),
            lc(sv).len() == n_l(sv), lr(sv).len() == n_l(sv),
            lkw@ == lk(sv).subrange(p, p + w), lcw@ == lc(sv).subrange(p, p + w), lrw@ == lr(sv).subrange(p, p + w),
            t <= w,
            t == 0 ==> prev == lkw@[0],
            t > 0 ==> prev == lkw@[t - 1],
            forall|u: u64| u < 64 ==> #[trigger] bit(sm, u) == (u < t && u > 0 && lkw@[u as int] != lkw@[u - 1]),
            forall|u: u64| u < 64 ==> #[trigger] bit(lm, u) == (u < t && lrw@[u as int] > lcw@[u as int]),
            !bad ==> forall|v: int| 0 < v < t ==> lkw@[v - 1] <= #[trigger] lkw@[v],
        decreases w - t,
    {
        let k = lkw[t];
        let sb: u64 = if k != prev { 1 } else { 0 };
        let lb: u64 = if lrw[t] > lcw[t] { 1 } else { 0 };
        let ghost (sm0, lm0) = (sm, lm);
        sm = sm | (sb << (t as u64));
        lm = lm | (lb << (t as u64));
        bad = bad || k < prev;
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(sm, u) == (u < t + 1 && u > 0 && lkw@[u as int] != lkw@[u - 1]) by {
                lemma_bit_or(sm0, sb, t as u64, u);
                if u == t && t == 0 {
                    assert(k == prev);
                }
            }
            assert forall|u: u64| u < 64 implies #[trigger] bit(lm, u) == (u < t + 1 && lrw@[u as int] > lcw@[u as int]) by {
                lemma_bit_or(lm0, lb, t as u64, u);
            }
        }
        prev = k;
        t = t + 1;
    }
    proof {
        assert forall|u: u64| u < 64 implies #[trigger] bit(sm, u) == (u < w && u > 0 && lk(sv)[p + u] != lk(sv)[p + u - 1]) by {
            if u < w && u > 0 {
                assert(lkw@[u as int] == lk(sv)[p + u]);
                assert(lkw@[u - 1] == lk(sv)[p + u - 1]);
            }
        }
        assert forall|u: u64| u < 64 implies #[trigger] bit(lm, u) == (u < w && late(sv, p + u)) by {
            if u < w {
                assert(lrw@[u as int] == lr(sv)[p + u]);
                assert(lcw@[u as int] == lc(sv)[p + u]);
            }
        }
        if !bad {
            assert forall|t: int| p < t < p + w implies #[trigger] pair_ok(sv, t) by {
                assert(lkw@[t - p] == lk(sv)[t]);
                assert(lkw@[t - p - 1] == lk(sv)[t - 1]);
            }
        }
    }
    (sm, lm, !bad)
}

// ------------------------------------------------------------------------------------------------ the runs of a window

/// Supplier key `v` belongs to no selected supplier.
pub open spec fn unsel(m: SupMap, v: int) -> bool { forall|ci: int| 0 <= ci < m.nsel ==> ckey(m, ci) != v }

/// The run starts `s` of a window of `w` rows with key-change mask `sm`: bit 0, the key changes, and `w` when the
/// window is short (the end of the scanned range).
pub open spec fn starts_ok(s: u64, sm: u64, w: int) -> bool {
    forall|u: u64| u < 64 ==> #[trigger] bit(s, u) == (u == 0 || bit(sm, u) || (w < WIN && u == w))
}

/// Rows `[p + x, p + y)` of a window add nothing to any selected key when `x` starts a run and every first late row
/// of a run (a bit of `first_marks`) in `[x, y)` has an unselected supplier: a late row `i` of a selected supplier
/// has the first late row `f` of its run in `[x, i]`, a late row of another supplier in its order.
proof fn lemma_window_skip(c: Cols, m: SupMap, sv: StoresView, p: int, w: int, sm: u64, lm: u64, s: u64, an: u64,
    x: u64, y: u64)
    requires
        cols_ok(c, sv), sup_ok(m, sv), 0 <= p, 1 <= w <= WIN, p + w <= n_l(sv),
        masks_ok(sv, p, w, sm, lm), starts_ok(s, sm, w),
        an < 64, an <= w, bit(s, x), x <= y <= an,
        forall|g: u64| g < 64 && #[trigger] bit(first_marks(s, lm, an), g) && x <= g < y
            ==> unsel(m, ls(sv)[p + g] as int),
    ensures forall|ci: int| 0 <= ci < m.nsel ==> ksum(sv, #[trigger] ckey(m, ci), p + x, p + y) == 0,
{
    assert forall|ci: int| 0 <= ci < m.nsel implies ksum(sv, #[trigger] ckey(m, ci), p + x, p + y) == 0 by {
        let v = ckey(m, ci);
        assert forall|i: int| p + x <= i < p + y implies #[trigger] lterm(sv, v, i) == 0 by {
            if late(sv, i) && ls(sv)[i] as int == v {
                let u = (i - p) as u64;
                assert(bit(lm, u));
                assert(bit(s, 0u64));
                lemma_mark_covered(s, lm, an, u);
                let a = seg_start(s, u);
                let f = first_from(lm, a, u);
                assert(x <= a);
                assert(unsel(m, ls(sv)[p + f] as int));
                assert(ls(sv)[p + f] as int != v);
                // `f` and `i` are in one run: no key change in `(f, u]`
                assert forall|t: int| p + f < t < i + 1 implies #[trigger] lk(sv)[t] == lk(sv)[t - 1] by {
                    let tu = (t - p) as u64;
                    assert(!bit(s, tu));
                    assert(!bit(sm, tu));
                }
                lemma_adjacent_eq(sv, p + f, i + 1);
                assert(late(sv, p + f));
                assert(other_at(sv, i, p + f));
                assert(ex3(sv, i));
            }
        }
        lemma_ksum_zero(sv, v, p + x, p + y);
    }
}

/// The complete runs of the window `[p, p + w)` (key changes `sm`, late rows `lm`, run ends `full`, `rest` without
/// bit 0): they end at `an`, the highest bit of `rest`, which the result returns with the order cursor. The first
/// late row of every run is a bit of `first_marks` (one carry-propagating addition); only a run whose first late row
/// has a selected supplier is evaluated row by row (`run_exact`), every other run adds nothing (`lemma_window_skip`).
#[inline(always)]
fn window_runs(c: &Cols, m: &SupMap, cnt: &mut Vec<u64>, p: usize, w: usize, sm: u64, lm: u64, full: u64, rest: u64,
    cur: usize, Ghost(sv): Ghost<StoresView>, Ghost(lo): Ghost<int>) -> (r: (u64, usize))
    requires
        cols_ok(*c, sv), sup_ok(*m, sv), 0 <= lo <= p, 1 <= w <= WIN, p + w <= c.nl,
        p == 0 || lk(sv)[p - 1] != lk(sv)[p as int],
        w < WIN ==> (p + w == c.nl || lk(sv)[p + w] != lk(sv)[p + w - 1]),
        masks_ok(sv, p as int, w as int, sm, lm),
        forall|u: u64| u < 64 ==> #[trigger] bit(full, u) == (bit(sm, u) || (w < WIN && u == w)),
        forall|u: u64| u < 64 ==> #[trigger] bit(rest, u) == (0 < u && bit(full, u)),
        rest != 0,
        cnt_ok(*m, sv, lo, p as int, old(cnt)@),
    ensures
        0 < r.0 <= w, r.0 < 64, bit(full, r.0),
        cnt_ok(*m, sv, lo, p + r.0, final(cnt)@),
    no_unwind
{
    let an = high_bit(rest, &m.tab);
    proof {
        assert(bit(rest, an));
        assert(an > 0 && bit(full, an));
        assert(an <= w);
    }
    let s: u64 = full | 1u64;
    proof {
        assert forall|u: u64| u < 64 implies #[trigger] bit(s, u) == (u == 0 || bit(sm, u) || (w < WIN && u == w)) by {
            assert(bit(full, u) == (bit(sm, u) || (w < WIN && u == w)));
            assert((((full | 1u64) >> u) & 1u64 == 1u64) <==> (u == 0 || (full >> u) & 1u64 == 1u64)) by (bit_vector)
                requires u < 64;
        }
        assert(starts_ok(s, sm, w as int));
        assert(bit(s, an));
        assert((1u64 << an) >= 1 && sub(1u64 << an, 1u64) == (1u64 << an) - 1) by (bit_vector) requires an < 64;
    }
    let b: u64 = (1u64 << an) - 1u64;
    let z: u64 = !lm & !s & b;
    let cy: u64 = ((s & !lm) << 1u64) & b;
    proof {
        assert(z <= b && cy <= b && b < 0x8000_0000_0000_0000u64) by (bit_vector)
            requires an < 64, b == sub(1u64 << an, 1u64), z == !lm & !s & b, cy == ((s & !lm) << 1u64) & b;
        assert(add(z, cy) == z + cy) by (bit_vector) requires z <= b, cy <= b, b < 0x8000_0000_0000_0000u64;
    }
    let fm: u64 = (((z + cy) & !z) | s) & lm & b;
    proof {
        assert(fm == first_marks(s, lm, an));
        assert forall|u: u64| u < 64 && #[trigger] bit(fm, u) implies u < an && bit(lm, u) by {
            let q: u64 = (add(z, cy) & !z) | s;
            assert((((fm >> u) & 1u64 == 1u64) ==> (u < an && (lm >> u) & 1u64 == 1u64))) by (bit_vector)
                requires an < 64, u < 64, b == sub(1u64 << an, 1u64), fm == q & lm & b;
        }
    }
    let mut fr: u64 = fm;
    let mut cur2: usize = cur;
    let ghost mut x: u64 = 0;
    let ghost mut pos: u64 = 0;
    while fr != 0
        invariant
            cols_ok(*c, sv), sup_ok(*m, sv), 0 <= lo <= p, 1 <= w <= WIN, p + w <= c.nl,
            p == 0 || lk(sv)[p - 1] != lk(sv)[p as int],
            w < WIN ==> (p + w == c.nl || lk(sv)[p + w] != lk(sv)[p + w - 1]),
            masks_ok(sv, p as int, w as int, sm, lm), starts_ok(s, sm, w as int),
            0 < an <= w, an < 64, bit(s, an),
            fm == first_marks(s, lm, an),
            forall|u: u64| u < 64 ==> #[trigger] bit(fm, u) ==> u < an && bit(lm, u),
            x <= pos <= an, bit(s, x),
            forall|u: u64| u < 64 ==> #[trigger] bit(fr, u) == (bit(fm, u) && u >= pos),
            forall|g: u64| g < 64 && #[trigger] bit(fm, g) && x <= g < pos ==> unsel(*m, ls(sv)[p + g] as int),
            cnt_ok(*m, sv, lo, p + x, cnt@),
        decreases 64 - pos,
    {
        let u = low_bit(fr, &m.tab);
        proof {
            assert(bit(fr, u));
            assert(bit(fm, u) && u >= pos && u < an);
        }
        let sf = c.ls[p + u as usize];
        if may_select(m, sf, Ghost(sv)) {
            // the run `[a, e)` of row `p + u`: the highest start at or below `u` and the lowest one above it (bit
            // scans, no loops: a loop here is vectorized with 512-bit registers, which slows the whole scan down)
            proof {
                assert((2u64 << u) >= 1 && sub(2u64 << u, 1u64) == (2u64 << u) - 1) by (bit_vector) requires u < 63;
            }
            let upto: u64 = (2u64 << u) - 1u64;
            let sa: u64 = s & upto;
            let se: u64 = s & !upto;
            proof {
                assert forall|t: u64| t < 64 implies #[trigger] bit(sa, t) == (bit(s, t) && t <= u) by {
                    assert((((s & upto) >> t) & 1u64 == 1u64) <==> ((s >> t) & 1u64 == 1u64 && t <= u))
                        by (bit_vector) requires u < 63, t < 64, upto == sub(2u64 << u, 1u64);
                }
                assert forall|t: u64| t < 64 implies #[trigger] bit(se, t) == (bit(s, t) && t > u) by {
                    assert((((s & !upto) >> t) & 1u64 == 1u64) <==> ((s >> t) & 1u64 == 1u64 && t > u))
                        by (bit_vector) requires u < 63, t < 64, upto == sub(2u64 << u, 1u64);
                }
                assert(bit(s, 0u64));
                assert(bit(sa, 0u64));
                assert(bit(se, an));
                if sa == 0 { lemma_bit_zero(0u64); }
                if se == 0 { lemma_bit_zero(an); }
            }
            let a = high_bit(sa, &m.tab);
            let e = low_bit(se, &m.tab);
            proof {
                assert forall|t: u64| a < t <= u implies !#[trigger] bit(s, t) by {
                    assert(!bit(sa, t));
                }
                assert forall|t: u64| u < t < e implies !#[trigger] bit(s, t) by {
                    assert(!bit(se, t));
                }
                assert(bit(sa, a) && bit(se, e));
                assert(a <= u && u < e);
                if e > an { assert(!bit(se, an)); }
            }
            proof {
                assert(bit(s, 0u64));
                assert(bit(s, a));
                assert(bit(s, e));
                if x > a { assert(!bit(s, x)); }
                // the rows before the run add nothing
                assert forall|g: u64| g < 64 && #[trigger] bit(fm, g) && x <= g < a implies unsel(*m, ls(sv)[p + g] as int) by {
                    if g >= pos { assert(bit(fr, g)); }
                }
                lemma_window_skip(*c, *m, sv, p as int, w as int, sm, lm, s, an, x, a);
                lemma_cnt_skip(*m, sv, lo, p + x, p + a, cnt@);
                // `[p + a, p + e)` is a complete run
                let (ra, re) = (p + a, p + e);
                assert forall|t: int| ra < t < re implies #[trigger] lk(sv)[t] == lk(sv)[t - 1] by {
                    let tu = (t - p) as u64;
                    assert(!bit(s, tu));
                    assert(!bit(sm, tu));
                }
                lemma_adjacent_eq(sv, ra, re);
                if a > 0 { assert(bit(sm, a)); }
                if e < w { assert(bit(sm, e)); } else { assert(!bit(sm, e)); }
                assert(run_ok(sv, ra, re));
            }
            cur2 = run_exact(c, m, cnt, p + a as usize, p + e as usize, cur2, Ghost(sv), Ghost(lo));
            let ghost fr0 = fr;
            proof { assert((1u64 << e) >= 1) by (bit_vector) requires e < 64; }
            fr = fr & !((1u64 << e) - 1u64);
            proof {
                assert forall|t: u64| t < 64 implies #[trigger] bit(fr, t) == (bit(fm, t) && t >= e) by {
                    lemma_clear_below(fr0, e, t);
                    assert(sub(1u64 << e, 1u64) == (1u64 << e) - 1u64);
                }
                x = e;
                pos = e;
            }
        } else {
            proof { assert(unsel(*m, ls(sv)[p + u] as int)); }
            let ghost fr0 = fr;
            fr = fr & !(1u64 << u);
            proof {
                assert forall|t: u64| t < 64 implies #[trigger] bit(fr, t) == (bit(fm, t) && t >= u + 1) by {
                    lemma_clear_bit(fr0, u, t);
                    if pos <= t < u { assert(!bit(fr0, t)); }
                }
                assert forall|g: u64| g < 64 && #[trigger] bit(fm, g) && x <= g < u + 1 implies unsel(*m, ls(sv)[p + g] as int) by {
                    if pos <= g < u { assert(bit(fr0, g)); }
                }
                pos = (u + 1) as u64;
            }
        }
    }
    proof {
        assert forall|g: u64| g < 64 && #[trigger] bit(fm, g) && x <= g < an implies unsel(*m, ls(sv)[p + g] as int) by {
            if g >= pos {
                assert(bit(fr, g));
                lemma_bit_zero(g);
            }
        }
        lemma_window_skip(*c, *m, sv, p as int, w as int, sm, lm, s, an, x, an);
        lemma_cnt_skip(*m, sv, lo, p + x, p + an, cnt@);
    }
    (an, cur2)
}

// ------------------------------------------------------------------------------------------------ the scan

/// The inputs of a scan of `[lo, hi)`: the columns, the supplier map, and the range starting and ending at key
/// changes (or at the column's ends).
pub open spec fn scan_pre(c: Cols, m: SupMap, lo: int, hi: int, sv: StoresView) -> bool {
    &&& cols_ok(c, sv)
    &&& sup_ok(m, sv)
    &&& 0 <= lo <= hi <= c.nl
    &&& (lo == 0 || lo == hi || lk(sv)[lo - 1] != lk(sv)[lo])
    &&& (hi == c.nl || lo == hi || lk(sv)[hi] != lk(sv)[hi - 1])
}

/// The result of a scan: when the keys were in order, the adjacent pairs of the range are ordered and, if the whole
/// column is sorted, each count is its supplier key's count over the range.
pub open spec fn scan_post(m: SupMap, lo: int, hi: int, sv: StoresView, cnt: Seq<u64>, ok_sorted: bool) -> bool {
    &&& cnt.len() == m.nsel
    &&& ok_sorted ==> pairs_ok(sv, lo, hi)
    &&& ok_sorted && sorted(sv) ==> forall|ci: int| 0 <= ci < m.nsel ==> #[trigger] cnt[ci] as int == ksum(sv, ckey(m, ci), lo, hi)
}

/// The loop state of `scan_range` at window start `p`: `p` starts a run, the counts cover `[lo, p)`, and unless a
/// pair was out of order every pair up to `p` is ordered.
pub open spec fn scan_inv(c: Cols, m: SupMap, lo: int, hi: int, sv: StoresView, p: int, cnt: Seq<u64>, bad: bool) -> bool {
    &&& scan_pre(c, m, lo, hi, sv)
    &&& lo < hi
    &&& lo <= p <= hi
    &&& (p < hi ==> (p == lo || lk(sv)[p - 1] != lk(sv)[p]))
    &&& cnt_ok(m, sv, lo, p, cnt)
    &&& (!bad ==> pairs_ok(sv, lo, p))
    &&& (!bad && lo < p < hi ==> pair_ok(sv, p))
}

/// The run `[p, e)` of a run start `p`, scanned to its end (a run longer than a window).
fn long_run(c: &Cols, p: usize, hi: usize, Ghost(sv): Ghost<StoresView>) -> (e: usize)
    requires cols_ok(*c, sv), p < hi <= c.nl,
        forall|t: int| p <= t < p + WIN && t < hi ==> #[trigger] lk(sv)[t] == lk(sv)[p as int],
    ensures p < e <= hi, e == hi || lk(sv)[e as int] != lk(sv)[p as int],
        forall|t: int| p <= t < e ==> #[trigger] lk(sv)[t] == lk(sv)[p as int],
    no_unwind
{
    let key = c.lk[p];
    let mut e: usize = p + 1;
    while e < hi && c.lk[e] == key
        invariant cols_ok(*c, sv), p < e <= hi, hi <= c.nl, key == lk(sv)[p as int],
            forall|t: int| p <= t < e ==> #[trigger] lk(sv)[t] == key,
        decreases hi - e,
    {
        e = e + 1;
    }
    e
}

/// A window in which no run ends (`rest == 0`): the run from `p` is longer than the window. It is scanned to its end
/// `e` (`long_run`) and evaluated row by row; the result is `e`, the order cursor and the out-of-order flag.
fn long_window(c: &Cols, m: &SupMap, cnt: &mut Vec<u64>, lo: usize, hi: usize, p: usize, w: usize, sm: u64, lm: u64,
    full: u64, rest: u64, cur: usize, bad: bool, Ghost(sv): Ghost<StoresView>) -> (r: (usize, usize, bool))
    requires
        scan_inv(*c, *m, lo as int, hi as int, sv, p as int, old(cnt)@, bad),
        p < hi,
        w as int == if hi - p < WIN { hi - p } else { WIN as int },
        masks_ok(sv, p as int, w as int, sm, lm),
        forall|u: u64| u < 64 ==> #[trigger] bit(full, u) == (bit(sm, u) || (w < WIN && u == w)),
        forall|u: u64| u < 64 ==> #[trigger] bit(rest, u) == (0 < u && bit(full, u)),
        rest == 0,
    ensures
        p < r.0 <= hi,
        scan_inv(*c, *m, lo as int, hi as int, sv, r.0 as int, final(cnt)@, r.2),
    no_unwind
{
    let mut bad = bad;
    proof {
        if w < WIN {
            assert(bit(rest, w as u64));
            lemma_bit_zero(w as u64);
        }
        assert forall|t: int| p < t < p + WIN && t < hi implies #[trigger] lk(sv)[t] == lk(sv)[t - 1] by {
            let u = (t - p) as u64;
            lemma_bit_zero(u);
            assert(!bit(rest, u));
            assert(!bit(sm, u));
        }
        lemma_adjacent_eq(sv, p as int, p + WIN);
    }
    let e = long_run(c, p, hi, Ghost(sv));
    if e < hi && c.lk[e] < c.lk[p] {
        bad = true;
    }
    proof {
        assert(run_ok(sv, p as int, e as int));
        if !bad {
            assert forall|t: int| lo < t < e implies #[trigger] pair_ok(sv, t) by {
                if t <= p {
                    if t < p { assert(pairs_ok(sv, lo as int, p as int)); }
                } else {
                    assert(lk(sv)[t] == lk(sv)[p as int]);
                    assert(lk(sv)[t - 1] == lk(sv)[p as int]);
                }
            }
            if e < hi {
                assert(lk(sv)[e - 1] == lk(sv)[p as int]);
            }
        }
    }
    let cur2 = run_exact(c, m, cnt, p, e, cur, Ghost(sv), Ghost(lo as int));
    (e, cur2, bad)
}

/// The counts of every selected supplier key over the waiting rows of `[lo, hi)` (see the module header).
pub fn scan_range(c: &Cols, m: &SupMap, lo: usize, hi: usize, cnt: &mut Vec<u64>, cur0: usize, Ghost(sv): Ghost<StoresView>)
    -> (ok_sorted: bool)
    requires
        scan_pre(*c, *m, lo as int, hi as int, sv),
        old(cnt)@.len() == m.nsel,
        forall|ci: int| 0 <= ci < m.nsel ==> old(cnt)@[ci] == 0,
    ensures
        scan_post(*m, lo as int, hi as int, sv, final(cnt)@, ok_sorted),
    no_unwind
{
    if lo >= hi {
        proof {
            assert forall|ci: int| 0 <= ci < m.nsel implies #[trigger] cnt@[ci] as int == ksum(sv, ckey(*m, ci), lo as int, hi as int) by {}
        }
        return true;
    }
    let mut p: usize = lo;
    let mut bad = false;
    let mut cur: usize = cur0;
    proof {
        assert forall|ci: int| 0 <= ci < m.nsel implies #[trigger] cnt@[ci] as int == ksum(sv, ckey(*m, ci), lo as int, lo as int) by {}
    }
    while p < hi
        invariant scan_inv(*c, *m, lo as int, hi as int, sv, p as int, cnt@, bad),
        decreases hi - p,
    {
        let w: usize = if hi - p < WIN { hi - p } else { WIN };
        let (_, lk1) = c.lk.split_at(p);
        let (lkw, _) = lk1.split_at(w);
        let (_, lc1) = c.lc.split_at(p);
        let (lcw, _) = lc1.split_at(w);
        let (_, lr1) = c.lr.split_at(p);
        let (lrw, _) = lr1.split_at(w);
        proof {
            assert(lkw@ =~= lk(sv).subrange(p as int, p + w));
            assert(lcw@ =~= lc(sv).subrange(p as int, p + w));
            assert(lrw@ =~= lr(sv).subrange(p as int, p + w));
        }
        let (sm, lm, wok) = window_masks(lkw, lcw, lrw, w, Ghost(sv), Ghost(p as int));
        let ghost bad0 = bad;
        if !wok {
            bad = true;
        }
        // `full`: `sm` and, when the window reaches `hi`, the end of the last run at bit `w`
        let full: u64 = if w < WIN { sm | (1u64 << (w as u64)) } else { sm };
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(full, u) == (bit(sm, u) || (w < WIN && u == w)) by {
                if w < WIN { lemma_bit_or(sm, 1, w as u64, u); }
            }
        }
        let mut rest: u64 = full & !1u64;
        proof {
            assert forall|u: u64| u < 64 implies #[trigger] bit(rest, u) == (0 < u && bit(full, u)) by {
                lemma_bit_clear0(full, u);
            }
        }
        if rest == 0 {
            let (e, cur2, bad2) = long_window(c, m, cnt, lo, hi, p, w, sm, lm, full, rest, cur, bad, Ghost(sv));
            cur = cur2;
            bad = bad2;
            p = e;
        } else {
            proof {
                if p as int == lo as int && lo > 0 { assert(lk(sv)[lo - 1] != lk(sv)[lo as int]); }
                if w < WIN { assert(p + w == hi); }
            }
            let (an, cur2) = window_runs(c, m, cnt, p, w, sm, lm, full, rest, cur, Ghost(sv), Ghost(lo as int));
            cur = cur2;
            // the window's last unfinished run starts the next window (or the window ends at `hi`)
            proof {
                let pa = p + an;
                if pa < hi {
                    assert(an < w);
                    assert(bit(sm, an));
                }
                if !bad {
                    assert(!bad0 && wok);
                    assert forall|t: int| lo < t < pa implies #[trigger] pair_ok(sv, t) by {
                        if t < p { assert(pairs_ok(sv, lo as int, p as int)); }
                    }
                }
            }
            p = p + an as usize;
        }
    }
    !bad
}

// ------------------------------------------------------------------------------------------------ the task

/// One scan task: the rows `[lo, hi)`.
pub struct ScanTask {
    pub c: Cols,
    pub m: Arc<SupMap>,
    pub lo: usize,
    pub hi: usize,
    pub cur: usize,
    pub cnt: Vec<u64>,
    pub sv: Ghost<StoresView>,
}

/// The task's counts, and whether its keys were in order.
pub struct ScanOut {
    pub cnt: Vec<u64>,
    pub sorted: bool,
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        &&& scan_pre(self.c, *self.m, self.lo as int, self.hi as int, self.sv@)
        &&& self.cnt@.len() == self.m.nsel
        &&& forall|ci: int| 0 <= ci < self.m.nsel ==> self.cnt@[ci] == 0
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        scan_post(*self.m, self.lo as int, self.hi as int, self.sv@, out.cnt@, out.sorted)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: ScanOut) {
        let ScanTask { c, m, lo, hi, cur, cnt, sv } = self;
        let mut cnt = cnt;
        let sorted = scan_range(&c, &*m, lo, hi, &mut cnt, cur, sv);
        ScanOut { cnt, sorted }
    }
}

} // verus!
