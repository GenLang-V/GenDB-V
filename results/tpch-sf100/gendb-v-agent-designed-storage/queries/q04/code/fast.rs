//! Fast Q4 scan of stored orders rows `[q0, q1)` over the run lengths of storage `li_ordruns` (model: `super::model`,
//! `runs_model` and `runs_aligned`: the lines of order `p` are run `p`, rows `rstart(p) .. rstart(p + 1)`). No
//! l_orderkey is read. Orders are taken in batches of at most `OB` rows inside one orders group:
//! 1. `batch_lines`: the batch's lines and longest run (vectorized sum and max over the run lengths);
//! 2. `batch_flags` alternates two steps until every order of the batch has its flag in `t`:
//!    - `late_segment`: one byte per line (`late_u8`: 1 when `l_commitdate < l_receiptdate`) for the next `STEP`
//!      lines (never across a lineitem group), one vectorized compare loop over the two code columns
//!      (`compare_codes`, which takes the code slices as parameters so the compiler needs no overlap checks);
//!    - `run_ready`: per order whose lines are flagged, the bytes of its run read as one little-endian `u64` window and
//!      shifted so only the run's bytes remain (`lemma_window`): nonzero exactly when some line is late (`run_late`);
//!      groups of 8 orders need no readiness test while 64 flagged lines lie ahead (runs of at most 8 lines).
//!    Alternating keeps the per-order work inside the stream of the two date columns from memory.
//! 3. `count_batch`: per o_orderpriority dictionary index, the orders of the batch with a late line, a date in
//!    `[lo, hi]` and that index (vectorized compares, u32 sums), added to the counts. Keys are computed without a
//!    select of the code load (`key_of`), so the code column is read with plain (not masked) vector loads.
//! The batch's lines number at most `OB * 255` (`MAX_RUN`), so the flag buffer (`FLAGS_LEN` bytes, offsets masked by
//! `FLAG_MASK`) always holds them.
use vstd::prelude::*;
use super::model::*;

verus! {

/// Orders rows per batch.
pub const OB: usize = 1024;
/// Flag offsets of a batch lie below `FLAG_SPAN` (`OB * 255 <= FLAG_SPAN`, a power of two).
pub const FLAG_SPAN: usize = 262144;
/// `FLAG_SPAN - 1`: masking an offset below `FLAG_SPAN` keeps it.
pub const FLAG_MASK: usize = 262143;
/// Flag buffer length: `FLAG_SPAN` plus 8 bytes of window slack.
pub const FLAGS_LEN: usize = 262152;

/// Rows `[a, b)` of a slice, without copying (two `split_at`s; usable in worker bodies).
pub fn sub_slice<T>(s: &[T], a: usize, b: usize) -> (r: &[T])
    requires a <= b <= s@.len(),
    ensures r@ == s@.subrange(a as int, b as int),
    no_unwind
{
    let (head, _tail) = s.split_at(b);
    let (_skip, mid) = head.split_at(a);
    proof {
        assert(mid@ =~= s@.subrange(a as int, b as int));
    }
    mid
}

/// The flag byte of line `j`.
pub open spec fn late_u8(c: Cols, j: int) -> u8 {
    if late(c, j) { 1u8 } else { 0u8 }
}

/// Facts the fast scan relies on.
pub open spec fn fast_ok(c: Cols, k: int) -> bool {
    &&& cols_ok(c, k)
    &&& keys_distinct(c)
    &&& lines_clustered(c)
    &&& runs_model(c)
    &&& runs_aligned(c)
}

/// Some of the first `len` (at most 8) rows from `s` is late, spelled out.
pub open spec fn any8(c: Cols, s: int, len: int) -> bool {
    late(c, s) || (1 < len && late(c, s + 1)) || (2 < len && late(c, s + 2)) || (3 < len && late(c, s + 3))
        || (4 < len && late(c, s + 4)) || (5 < len && late(c, s + 5)) || (6 < len && late(c, s + 6))
        || (7 < len && late(c, s + 7))
}

/// `any8` is the existence of a late row in `[s, s + len)`.
proof fn lemma_any8(c: Cols, s: int, len: int)
    requires 1 <= len <= 8,
    ensures any8(c, s, len) == exists|j: int| s <= j < s + len && #[trigger] late(c, j),
{
    if exists|j: int| s <= j < s + len && #[trigger] late(c, j) {
        let j = choose|j: int| s <= j < s + len && #[trigger] late(c, j);
        assert(j == s || j == s + 1 || j == s + 2 || j == s + 3 || j == s + 4 || j == s + 5 || j == s + 6 || j == s + 7);
    }
    if any8(c, s, len) {
        if late(c, s) {
            assert(s <= s < s + len && late(c, s));
        } else if 1 < len && late(c, s + 1) {
            assert(late(c, s + 1));
        } else if 2 < len && late(c, s + 2) {
            assert(late(c, s + 2));
        } else if 3 < len && late(c, s + 3) {
            assert(late(c, s + 3));
        } else if 4 < len && late(c, s + 4) {
            assert(late(c, s + 4));
        } else if 5 < len && late(c, s + 5) {
            assert(late(c, s + 5));
        } else if 6 < len && late(c, s + 6) {
            assert(late(c, s + 6));
        } else {
            assert(late(c, s + 7));
        }
    }
}

/// Eight bytes as a little-endian word, shifted left so only the first `len` bytes remain: nonzero exactly when one
/// of those bytes is nonzero.
proof fn lemma_window(b0: u64, b1: u64, b2: u64, b3: u64, b4: u64, b5: u64, b6: u64, b7: u64, len: u64)
    requires
        b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256,
        1 <= len <= 8,
    ensures
        (((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64)
            | (b7 << 56u64)) << ((64u64 - 8u64 * len) as u64)) != 0)
        == (b0 != 0 || (1 < len && b1 != 0) || (2 < len && b2 != 0) || (3 < len && b3 != 0) || (4 < len && b4 != 0)
            || (5 < len && b5 != 0) || (6 < len && b6 != 0) || (7 < len && b7 != 0)),
{
    let w = b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64);
    if len == 1 {
        assert((w << 56u64 != 0) == (b0 != 0)) by (bit_vector)
            requires w == b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64),
                b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
    } else if len == 2 {
        assert((w << 48u64 != 0) == (b0 != 0 || b1 != 0)) by (bit_vector)
            requires w == b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64),
                b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
    } else if len == 3 {
        assert((w << 40u64 != 0) == (b0 != 0 || b1 != 0 || b2 != 0)) by (bit_vector)
            requires w == b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64),
                b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
    } else if len == 4 {
        assert((w << 32u64 != 0) == (b0 != 0 || b1 != 0 || b2 != 0 || b3 != 0)) by (bit_vector)
            requires w == b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64),
                b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
    } else if len == 5 {
        assert((w << 24u64 != 0) == (b0 != 0 || b1 != 0 || b2 != 0 || b3 != 0 || b4 != 0)) by (bit_vector)
            requires w == b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64),
                b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
    } else if len == 6 {
        assert((w << 16u64 != 0) == (b0 != 0 || b1 != 0 || b2 != 0 || b3 != 0 || b4 != 0 || b5 != 0)) by (bit_vector)
            requires w == b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64),
                b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
    } else if len == 7 {
        assert((w << 8u64 != 0) == (b0 != 0 || b1 != 0 || b2 != 0 || b3 != 0 || b4 != 0 || b5 != 0 || b6 != 0)) by (bit_vector)
            requires w == b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64),
                b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
    } else {
        assert((w << 0u64 != 0) == (b0 != 0 || b1 != 0 || b2 != 0 || b3 != 0 || b4 != 0 || b5 != 0 || b6 != 0 || b7 != 0)) by (bit_vector)
            requires w == b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64),
                b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
    }
}

/// Masking an offset below `FLAG_SPAN` keeps it.
proof fn lemma_mask(x: usize)
    requires x < FLAG_SPAN,
    ensures x & FLAG_MASK == x,
{
    assert(x & 262143usize == x) by (bit_vector) requires x < 262144usize;
}

/// `l_commitdate < l_receiptdate` of a row of group `g`: the code difference against the base difference, clamped to
/// `[-65536, 65536]` (code differences lie in `[-65535, 65535]`).
pub open spec fn clamp_diff(rb: int, cb: int) -> int {
    let dd = rb - cb;
    if dd > 65536 { 65536 } else if dd < -65536 { -65536 } else { dd }
}

/// The flag byte of a code pair: 1 when `lc - lr < d`.
pub open spec fn below_u8(lc: u16, lr: u16, d: i32) -> u8 {
    if (lc as int) - (lr as int) < d as int { 1u8 } else { 0u8 }
}

/// `flags[o + i] = below_u8(lcs[i], lrs[i], d)` for every `i`. The code slices are parameters (not read through
/// `Cols`) so the compiler knows the flag stores cannot change them and vectorizes the loop without overlap checks.
#[inline(always)]
fn compare_codes(lcs: &[u16], lrs: &[u16], len: usize, d: i32, flags: &mut Vec<u8>, o: usize)
    requires
        lcs@.len() == len,
        lrs@.len() == len,
        o + lcs@.len() <= old(flags)@.len(),
    ensures
        final(flags)@.len() == old(flags)@.len(),
        forall|x: int| 0 <= x < o ==> final(flags)@[x] == old(flags)@[x],
        forall|i: int| 0 <= i < lcs@.len() ==> #[trigger] final(flags)@[o + i] == below_u8(lcs@[i], lrs@[i], d),
    no_unwind
{
    // The test always holds (precondition); it lets the compiler drop the bounds checks of the flag stores.
    let m = len;
    let ghost f0 = flags@;
    let lim = flags.len();
    if o > lim || m > lim - o {
        return;
    }
    let mut i: usize = 0;
    while i < m
        invariant
            lim == flags@.len(),
            m == lcs@.len(),
            lcs@.len() == lrs@.len(),
            o + m <= flags@.len(),
            flags@.len() == f0.len(),
            i <= m,
            forall|x: int| 0 <= x < o ==> flags@[x] == f0[x],
            forall|i2: int| 0 <= i2 < i ==> #[trigger] flags@[o + i2] == below_u8(lcs@[i2], lrs@[i2], d),
        decreases m - i,
    {
        let x: i32 = lcs[i] as i32 - lrs[i] as i32;
        let v: u8 = if x < d { 1 } else { 0 };
        flags[o + i] = v;
        i = i + 1;
    }
}

/// Flags of lines `[j0, j1)` of lineitem group `g` into `flags[o ..]`.
#[inline(always)]
fn late_segment(c: &Cols, Ghost(k): Ghost<int>, g: usize, j0: usize, j1: usize, flags: &mut Vec<u8>, o: usize)
    requires
        cols_ok(*c, k),
        j0 < j1 <= c.n_l,
        g * c.bs_l <= j0,
        j1 <= g * c.bs_l + c.bs_l,
        o + (j1 - j0) <= old(flags)@.len(),
    ensures
        final(flags)@.len() == old(flags)@.len(),
        forall|x: int| 0 <= x < o ==> final(flags)@[x] == old(flags)@[x],
        forall|x: int| o <= x < o + (j1 - j0) ==> #[trigger] final(flags)@[x] == late_u8(*c, j0 + (x - o)),
    no_unwind
{
    let bs = c.bs_l;
    proof {
        lemma_div_group(j0 as int, bs as int, g as int);
        lemma_div_below(j0 as int, bs as int, c.lk_bases@.len() as int);
    }
    let lcs = sub_slice(c.lc_codes, j0, j1);
    let lrs = sub_slice(c.lr_codes, j0, j1);
    let cb = c.lc_bases[g];
    let rb = c.lr_bases[g];
    let dd: i128 = rb as i128 - cb as i128;
    let d: i32 = if dd > 65536 { 65536 } else if dd < -65536 { -65536 } else { dd as i32 };
    compare_codes(lcs, lrs, j1 - j0, d, flags, o);
    proof {
        assert forall|x: int| o <= x < o + (j1 - j0) implies #[trigger] flags@[x] == late_u8(*c, j0 + (x - o)) by {
            let i = x - o;
            let j = j0 + i;
            assert(flags@[o + i] == below_u8(lcs@[i], lrs@[i], d));
            lemma_div_group(j, bs as int, g as int);
            assert(lcmt(*c, j) == cb + lcs@[i]);
            assert(lrcp(*c, j) == rb + lrs@[i]);
        }
    }
}

/// One order's window: the 8 flag bytes from offset `off` (masked) read as a little-endian word, shifted so only the
/// first `len` bytes remain; 1 when some line of the run from `cur + off` (`len` lines, flagged) is late, else 0.
fn window_flag(c: &Cols, Ghost(cur): Ghost<int>, Ghost(lines): Ghost<int>, flags: &Vec<u8>, off: usize, len: usize) -> (r: u16)
    requires
        1 <= len <= 8,
        off + len <= lines <= FLAG_SPAN,
        flags@.len() == FLAGS_LEN,
        forall|x: int| 0 <= x < lines ==> #[trigger] flags@[x] == late_u8(*c, cur + x),
    ensures
        (r != 0) == exists|j: int| cur + off <= j < cur + off + len && #[trigger] late(*c, j),
    no_unwind
{
    let o = off & FLAG_MASK;
    proof {
        lemma_mask(off);
    }
    let b0 = flags[o] as u64;
    let b1 = flags[o + 1] as u64;
    let b2 = flags[o + 2] as u64;
    let b3 = flags[o + 3] as u64;
    let b4 = flags[o + 4] as u64;
    let b5 = flags[o + 5] as u64;
    let b6 = flags[o + 6] as u64;
    let b7 = flags[o + 7] as u64;
    let w = b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64);
    let lw = len as u64;
    let sh: u64 = 64 - 8 * lw;
    let r = w << sh;
    proof {
        let s = cur + off;
        lemma_window(b0, b1, b2, b3, b4, b5, b6, b7, lw);
        assert((b0 != 0) == late(*c, s));
        assert(1 < len ==> (b1 != 0) == late(*c, s + 1));
        assert(2 < len ==> (b2 != 0) == late(*c, s + 2));
        assert(3 < len ==> (b3 != 0) == late(*c, s + 3));
        assert(4 < len ==> (b4 != 0) == late(*c, s + 4));
        assert(5 < len ==> (b5 != 0) == late(*c, s + 5));
        assert(6 < len ==> (b6 != 0) == late(*c, s + 6));
        assert(7 < len ==> (b7 != 0) == late(*c, s + 7));
        lemma_any8(*c, s, len as int);
    }
    if r != 0 { 1 } else { 0 }
}

/// One order's flag by scanning its `len` flag bytes from `off` (any run length).
fn scan_flag(c: &Cols, Ghost(cur): Ghost<int>, Ghost(lines): Ghost<int>, flags: &Vec<u8>, off: usize, len: usize) -> (r: u16)
    requires
        off + len <= lines <= FLAG_SPAN,
        flags@.len() == FLAGS_LEN,
        forall|x: int| 0 <= x < lines ==> #[trigger] flags@[x] == late_u8(*c, cur + x),
    ensures
        (r != 0) == exists|j: int| cur + off <= j < cur + off + len && #[trigger] late(*c, j),
    no_unwind
{
    let mut found: u16 = 0;
    let mut j: usize = 0;
    while j < len
        invariant
            j <= len,
            off + len <= lines <= FLAG_SPAN,
            flags@.len() == FLAGS_LEN,
            forall|x: int| 0 <= x < lines ==> #[trigger] flags@[x] == late_u8(*c, cur + x),
            (found != 0) == exists|x: int| cur + off <= x < cur + off + j && #[trigger] late(*c, x),
        decreases len - j,
    {
        let b = flags[off + j];
        proof {
            assert((b != 0) == late(*c, cur + off + j));
            if found != 0 {
                let x = choose|x: int| cur + off <= x < cur + off + j && #[trigger] late(*c, x);
                assert(cur + off <= x < cur + off + j + 1);
            }
            if b != 0 {
                assert(late(*c, cur + off + j));
            }
        }
        if b != 0 {
            found = 1;
        }
        j = j + 1;
    }
    found
}

/// Per order of the batch `[p, p + m)` from `i0` on (lines from `cur == rstart(p)`, flagged in `flags[0 .. a)`): the
/// orders whose lines are all flagged get `t[i]` nonzero exactly when order `p + i` has a late line. Returns the next
/// order and its line offset; when every line of the batch is flagged (`a == lines`) it reaches `m`. `short`: every
/// run of the batch has at most 8 lines (one window each).
fn run_ready(c: &Cols, Ghost(k): Ghost<int>, p: usize, m: usize, cur: usize, lines: usize, short: bool,
    flags: &Vec<u8>, a: usize, i0: usize, off0: usize, t: &mut Vec<u16>) -> (r: (usize, usize))
    requires
        fast_ok(*c, k),
        p + m <= c.n_o,
        m <= OB,
        cur as int == rstart(*c, p as int),
        lines as int == rstart(*c, (p + m) as int) - cur,
        rstart(*c, (p + m) as int) - cur <= FLAG_SPAN,
        a <= rstart(*c, (p + m) as int) - cur,
        short ==> forall|i: int| 0 <= i < m ==> #[trigger] c.rl@[p + i] <= 8,
        flags@.len() == FLAGS_LEN,
        old(t)@.len() == OB,
        forall|x: int| 0 <= x < a ==> #[trigger] flags@[x] == late_u8(*c, cur + x),
        i0 <= m,
        off0 as int == rstart(*c, (p + i0) as int) - cur,
        off0 <= a,
        forall|i: int| 0 <= i < i0 ==> (#[trigger] old(t)@[i] != 0) == run_late(*c, p + i),
    ensures
        final(t)@.len() == OB,
        i0 <= r.0 <= m,
        r.1 as int == rstart(*c, (p + r.0) as int) - cur,
        r.1 <= a,
        a == rstart(*c, (p + m) as int) - cur ==> r.0 == m,
        forall|i: int| 0 <= i < r.0 ==> (#[trigger] final(t)@[i] != 0) == run_late(*c, p + i),
    no_unwind
{
    let rlb = sub_slice(c.rl, p, p + m);
    let mut off: usize = off0;
    let mut i: usize = i0;
    // Always true (preconditions); the tests let the compiler drop bounds checks.
    if flags.len() != FLAGS_LEN || t.len() != OB {
        return (i, off);
    }
    let n = if m < t.len() { m } else { t.len() };
    proof {
        lemma_rstart_bounds(*c, (p + i) as int);
        lemma_rstart_le(*c, (p + i) as int, (p + m) as int);
    }
    if short {
        // Groups of 8 orders while 64 flagged lines lie ahead: every run has at most 8 lines, so the group's lines are
        // flagged and its orders need no readiness test.
        while i + 8 <= n && off + 64 <= a
            invariant
                fast_ok(*c, k),
                short,
                p + m <= c.n_o,
                m <= OB,
                n == m,
                rlb@ == c.rl@.subrange(p as int, (p + m) as int),
                cur as int == rstart(*c, p as int),
                lines == rstart(*c, (p + m) as int) - cur,
                lines <= FLAG_SPAN,
                a <= lines,
                forall|i2: int| 0 <= i2 < m ==> #[trigger] c.rl@[p + i2] <= 8,
                flags@.len() == FLAGS_LEN,
                t@.len() == OB,
                forall|x: int| 0 <= x < a ==> #[trigger] flags@[x] == late_u8(*c, cur + x),
                i0 <= i <= m,
                off as int == rstart(*c, (p + i) as int) - cur,
                off <= a,
                forall|i2: int| 0 <= i2 < i ==> (#[trigger] t@[i2] != 0) == run_late(*c, p + i2),
            decreases m - i,
        {
            let ig = i;
            while i < ig + 8
                invariant
                    fast_ok(*c, k),
                    short,
                    p + m <= c.n_o,
                    m <= OB,
                    n == m,
                    ig + 8 <= m,
                    ig <= i <= ig + 8,
                    rlb@ == c.rl@.subrange(p as int, (p + m) as int),
                    cur as int == rstart(*c, p as int),
                    lines == rstart(*c, (p + m) as int) - cur,
                    lines <= FLAG_SPAN,
                    a <= lines,
                    forall|i2: int| 0 <= i2 < m ==> #[trigger] c.rl@[p + i2] <= 8,
                    flags@.len() == FLAGS_LEN,
                    t@.len() == OB,
                    forall|x: int| 0 <= x < a ==> #[trigger] flags@[x] == late_u8(*c, cur + x),
                    i0 <= i <= m,
                    off as int == rstart(*c, (p + i) as int) - cur,
                    off + 8 * (ig + 8 - i) <= a,
                    forall|i2: int| 0 <= i2 < i ==> (#[trigger] t@[i2] != 0) == run_late(*c, p + i2),
                decreases ig + 8 - i,
            {
                let len = rlb[i] as usize;
                let q = p + i;
                proof {
                    lemma_rstart_bounds(*c, q as int);
                    assert(len == c.rl@[q as int]);
                    assert(c.rl@[q as int] >= 1);
                    assert(c.rl@[p + i] <= 8);
                }
                let v = window_flag(c, Ghost(cur as int), Ghost(a as int), flags, off, len);
                proof {
                    lemma_run_late(*c, q as int);
                }
                t[i] = v;
                off = off + len;
                i = i + 1;
            }
        }
        if a < lines {
            // The orders left wait for more flagged lines.
            return (i, off);
        }
    }
    proof {
        lemma_rstart_bounds(*c, (p + i) as int);
        lemma_rstart_le(*c, (p + i) as int, (p + m) as int);
    }
    while i < n && off + rlb[i] as usize <= a
        invariant
            fast_ok(*c, k),
            p + m <= c.n_o,
            m <= OB,
            n == m,
            rlb@ == c.rl@.subrange(p as int, (p + m) as int),
            cur as int == rstart(*c, p as int),
            lines == rstart(*c, (p + m) as int) - cur,
            lines <= FLAG_SPAN,
            a <= lines,
            short ==> forall|i2: int| 0 <= i2 < m ==> #[trigger] c.rl@[p + i2] <= 8,
            flags@.len() == FLAGS_LEN,
            t@.len() == OB,
            forall|x: int| 0 <= x < a ==> #[trigger] flags@[x] == late_u8(*c, cur + x),
            i0 <= i <= m,
            off as int == rstart(*c, (p + i) as int) - cur,
            off <= a,
            forall|i2: int| 0 <= i2 < i ==> (#[trigger] t@[i2] != 0) == run_late(*c, p + i2),
        decreases m - i,
    {
        let len = rlb[i] as usize;
        let q = p + i;
        proof {
            lemma_rstart_bounds(*c, q as int);
            lemma_rstart_le(*c, (q + 1) as int, (p + m) as int);
            assert(len == c.rl@[q as int]);
            assert(c.rl@[q as int] >= 1);
        }
        let v: u16 = if short {
            proof {
                assert(c.rl@[p + i] <= 8);
            }
            window_flag(c, Ghost(cur as int), Ghost(a as int), flags, off, len)
        } else {
            scan_flag(c, Ghost(cur as int), Ghost(a as int), flags, off, len)
        };
        proof {
            lemma_run_late(*c, q as int);
        }
        t[i] = v;
        off = off + len;
        i = i + 1;
    }
    proof {
        if a == lines && i < m {
            lemma_rstart_bounds(*c, (p + i) as int);
            lemma_rstart_le(*c, (p + i + 1) as int, (p + m) as int);
            assert(off + c.rl@[(p + i) as int] <= a);
            assert(rlb@[i as int] == c.rl@[(p + i) as int]);
        }
    }
    (i, off)
}

/// Lines flagged per step of `batch_flags` (one fixed-size, vectorized compare loop when a step is full).
pub const STEP: usize = 256;

/// Per order of the batch `[p, p + m)` (its `lines` lines from `cur == rstart(p)`): `t[i]` is nonzero exactly when
/// order `p + i` has a late line. Flagging the lines (`late_segment`, `STEP` lines a step, never across a lineitem
/// group) alternates with the windows of the orders whose lines are flagged (`run_ready`), so the window work
/// overlaps the stream of the two date columns from memory. `room`: lines left in lineitem group `g` from the next
/// line to flag (0: not yet known).
fn batch_flags(c: &Cols, Ghost(k): Ghost<int>, p: usize, m: usize, cur: usize, lines: usize, short: bool,
    flags: &mut Vec<u8>, t: &mut Vec<u16>)
    requires
        fast_ok(*c, k),
        p + m <= c.n_o,
        m <= OB,
        cur as int == rstart(*c, p as int),
        lines as int == rstart(*c, (p + m) as int) - cur,
        lines <= FLAG_SPAN,
        short ==> forall|i: int| 0 <= i < m ==> #[trigger] c.rl@[p + i] <= 8,
        old(flags)@.len() == FLAGS_LEN,
        old(t)@.len() == OB,
    ensures
        final(flags)@.len() == FLAGS_LEN,
        final(t)@.len() == OB,
        forall|i: int| 0 <= i < m ==> (#[trigger] final(t)@[i] != 0) == run_late(*c, p + i),
    no_unwind
{
    let bs = c.bs_l;
    let mut a: usize = 0;
    let mut i: usize = 0;
    let mut off: usize = 0;
    let mut g: usize = 0;
    let mut room: usize = 0;
    proof {
        lemma_rstart_bounds(*c, (p + m) as int);
        lemma_rstart_bounds(*c, p as int);
    }
    while i < m
        invariant
            fast_ok(*c, k),
            p + m <= c.n_o,
            m <= OB,
            bs == c.bs_l,
            cur as int == rstart(*c, p as int),
            lines as int == rstart(*c, (p + m) as int) - cur,
            cur + lines <= c.n_l,
            lines <= FLAG_SPAN,
            short ==> forall|i2: int| 0 <= i2 < m ==> #[trigger] c.rl@[p + i2] <= 8,
            flags@.len() == FLAGS_LEN,
            t@.len() == OB,
            a <= lines,
            forall|x: int| 0 <= x < a ==> #[trigger] flags@[x] == late_u8(*c, cur + x),
            room >= 1 ==> g * bs <= cur + a && cur + a + room == g * bs + bs && g < c.lk_bases@.len(),
            i <= m,
            off as int == rstart(*c, (p + i) as int) - cur,
            off <= a,
            forall|i2: int| 0 <= i2 < i ==> (#[trigger] t@[i2] != 0) == run_late(*c, p + i2),
        decreases (lines - a) + (m - i),
    {
        if a < lines {
            let j = cur + a;
            if room == 0 {
                g = j / bs;
                room = bs - j % bs;
                proof {
                    lemma_group_of_row(j as int, bs as int);
                    lemma_div_below(j as int, bs as int, c.lk_bases@.len() as int);
                }
            }
            let mut seg = lines - a;
            if seg > STEP {
                seg = STEP;
            }
            if seg > room {
                seg = room;
            }
            let ghost fb = flags@;
            if seg == STEP {
                late_segment(c, Ghost(k), g, j, j + STEP, flags, a);
            } else {
                late_segment(c, Ghost(k), g, j, j + seg, flags, a);
            }
            proof {
                assert forall|x: int| 0 <= x < a + seg implies #[trigger] flags@[x] == late_u8(*c, cur + x) by {
                    if x < a {
                        assert(flags@[x] == fb[x]);
                    } else {
                        assert(flags@[x] == late_u8(*c, j + (x - a)));
                    }
                }
            }
            a = a + seg;
            room = room - seg;
        }
        let r = run_ready(c, Ghost(k), p, m, cur, lines, short, flags, a, i, off, t);
        i = r.0;
        off = r.1;
    }
}

/// A range whose rows all have another priority index than `d` counts nothing for `d`.
proof fn lemma_count_other_prio(c: Cols, lo: int, hi: int, d: int, q0: int, q1: int)
    requires forall|q: int| q0 <= q < q1 ==> #[trigger] oprio(c, q) != d,
    ensures count_raw(c, lo, hi, d, q0, q1) == 0,
    decreases q1 - q0,
{
    if q0 < q1 {
        lemma_count_other_prio(c, lo, hi, d, q0, q1 - 1);
    }
}

/// The group key of order `p + i` of a batch: its priority code when it qualifies, else the code plus 256 (no code
/// below 256 matches it). Computed without a select of the code load, so the compiler keeps the code load plain
/// (masked vector loads from mapped storage pages are several times slower).
pub open spec fn key_of(c: Cols, lo: int, hi: int, q: int) -> u16 {
    if qual_raw(c, lo, hi, q) { c.op_codes@[q] as u16 } else { (c.op_codes@[q] as u16 + 256) as u16 }
}

/// Batch facts shared by the key and count passes: orders `[p, p + m)` inside orders group `g`.
pub open spec fn batch_ok(c: Cols, k: int, p: int, m: int, g: int) -> bool {
    &&& fast_ok(c, k)
    &&& 1 <= m <= OB
    &&& p + m <= c.n_o
    &&& g * c.bs_o <= p
    &&& p + m <= g * c.bs_o + c.bs_o
    &&& 0 <= g < c.ok_bases@.len()
}

/// Keys of the batch: `key[i] == key_of(p + i)`. `all_in`: every date of the group lies in `[lo, hi]` (no date read);
/// else the date codes are compared with the window relative to the group base (`[lo16, hi16]`, nonempty).
fn batch_keys(c: &Cols, Ghost(k): Ghost<int>, p: usize, m: usize, g: usize, lo: i64, hi: i64, all_in: bool, lo16: u16,
    hi16: u16, t: &Vec<u16>, key: &mut Vec<u16>)
    requires
        batch_ok(*c, k, p as int, m as int, g as int),
        t@.len() == OB,
        old(key)@.len() == OB,
        forall|i: int| 0 <= i < m ==> (#[trigger] t@[i] != 0) == run_late(*c, p + i),
        all_in ==> forall|q: int| p <= q < p + m ==> lo <= #[trigger] odate(*c, q) <= hi,
        !all_in ==> forall|q: int| p <= q < p + m ==>
            (lo <= #[trigger] odate(*c, q) <= hi) == (lo16 <= c.od_codes@[q] <= hi16),
    ensures
        final(key)@.len() == OB,
        forall|i: int| 0 <= i < m ==> #[trigger] final(key)@[i] == key_of(*c, lo as int, hi as int, p + i),
    no_unwind
{
    let opc = sub_slice(c.op_codes, p, p + m);
    let odc = sub_slice(c.od_codes, p, p + m);
    let n0 = if m < t.len() { m } else { t.len() };
    let n = if n0 < key.len() { n0 } else { key.len() };
    let mut i: usize = 0;
    while i < n
        invariant
            batch_ok(*c, k, p as int, m as int, g as int),
            n == m,
            t@.len() == OB,
            key@.len() == OB,
            opc@ == c.op_codes@.subrange(p as int, (p + m) as int),
            odc@ == c.od_codes@.subrange(p as int, (p + m) as int),
            forall|i2: int| 0 <= i2 < m ==> (#[trigger] t@[i2] != 0) == run_late(*c, p + i2),
            all_in ==> forall|q: int| p <= q < p + m ==> lo <= #[trigger] odate(*c, q) <= hi,
            !all_in ==> forall|q: int| p <= q < p + m ==>
                (lo <= #[trigger] odate(*c, q) <= hi) == (lo16 <= c.od_codes@[q] <= hi16),
            i <= m,
            forall|i2: int| 0 <= i2 < i ==> #[trigger] key@[i2] == key_of(*c, lo as int, hi as int, p + i2),
        decreases m - i,
    {
        let tv = t[i];
        let pc = opc[i] as u16;
        let late_one: u16 = if tv != 0 { 1 } else { 0 };
        let v: u16 = if all_in {
            pc + if late_one == 1 { 0u16 } else { 256u16 }
        } else {
            let oc = odc[i];
            let lo_one: u16 = if lo16 <= oc { 1 } else { 0 };
            let hi_one: u16 = if oc <= hi16 { 1 } else { 0 };
            pc + if late_one + lo_one + hi_one == 3 { 0u16 } else { 256u16 }
        };
        proof {
            let q = (p + i) as int;
            lemma_run_late(*c, q);
            assert(lo <= odate(*c, q) <= hi || !(lo <= odate(*c, q) <= hi));
            assert(t@[i as int] == tv);
            assert(opc@[i as int] == c.op_codes@[q]);
            assert(odc@[i as int] == c.od_codes@[q]);
            assert(v == key_of(*c, lo as int, hi as int, q));
        }
        key[i] = v;
        i = i + 1;
    }
}

/// Adds the batch `[p, p + m)` (inside orders group `g`; `t` marks the orders with a late line) to the counts of
/// every priority index: orders with a late line, a date in `[lo, hi]` and that index.
fn count_batch(c: &Cols, Ghost(k): Ghost<int>, kk: usize, zmax: &[i64], p: usize, m: usize, g: usize, lo: i64, hi: i64,
    t: &Vec<u16>, key: &mut Vec<u16>, counts: &mut Vec<usize>, Ghost(q0): Ghost<int>)
    requires
        batch_ok(*c, k, p as int, m as int, g as int),
        kk == k,
        0 <= q0 <= p,
        zmax@.len() == c.od_bases@.len(),
        forall|q: int| 0 <= q < c.n_o ==> #[trigger] odate(*c, q) <= zmax@[q / c.bs_o as int],
        t@.len() == OB,
        old(key)@.len() == OB,
        forall|i: int| 0 <= i < m ==> (#[trigger] t@[i] != 0) == run_late(*c, p + i),
        old(counts)@.len() == k,
        forall|d: int| 0 <= d < k ==> #[trigger] old(counts)@[d] as int == count_raw(*c, lo as int, hi as int, d, q0, p as int),
    ensures
        final(key)@.len() == OB,
        final(counts)@.len() == k,
        forall|d: int| 0 <= d < k ==> #[trigger] final(counts)@[d] as int == count_raw(*c, lo as int, hi as int, d, q0, (p + m) as int),
    no_unwind
{
    let bs = c.bs_o;
    let ob = c.od_bases[g];
    let zm = zmax[g];
    let pb = c.op_bases[g];
    let lo_r: i128 = lo as i128 - ob as i128;
    let hi_r: i128 = hi as i128 - ob as i128;
    let all_in = lo <= ob && zm <= hi;
    let empty = lo_r > 65535 || hi_r < 0 || lo_r > hi_r;
    let lo16: u16 = if lo_r < 0 { 0 } else if lo_r > 65535 { 65535 } else { lo_r as u16 };
    let hi16: u16 = if hi_r < 0 { 0 } else if hi_r > 65535 { 65535 } else { hi_r as u16 };
    proof {
        assert forall|q: int| p <= q < p + m implies #[trigger] odate(*c, q) == ob + c.od_codes@[q]
            && zm >= odate(*c, q) by {
            lemma_div_group(q, bs as int, g as int);
        }
        assert forall|q: int| p <= q < p + m implies #[trigger] oprio(*c, q) == pb + c.op_codes@[q] by {
            lemma_div_group(q, bs as int, g as int);
        }
    }
    if !all_in && empty {
        // No date of the batch lies in the window: nothing to add.
        proof {
            assert forall|d: int| 0 <= d < k implies #[trigger] counts@[d] as int
                == count_raw(*c, lo as int, hi as int, d, q0, (p + m) as int) by {
                assert forall|q: int| p <= q < p + m implies !#[trigger] qual_raw(*c, lo as int, hi as int, q) by {
                    assert(odate(*c, q) == ob + c.od_codes@[q]);
                }
                lemma_count_none(*c, lo as int, hi as int, d, p as int, (p + m) as int);
                lemma_count_split(*c, lo as int, hi as int, d, q0, p as int, (p + m) as int);
            }
        }
        return;
    }
    proof {
        if all_in {
            assert forall|q: int| p <= q < p + m implies lo <= #[trigger] odate(*c, q) <= hi by {
                assert(odate(*c, q) == ob + c.od_codes@[q]);
            }
        } else {
            assert forall|q: int| p <= q < p + m implies
                (lo <= #[trigger] odate(*c, q) <= hi) == (lo16 <= c.od_codes@[q] <= hi16) by {
                assert(odate(*c, q) == ob + c.od_codes@[q]);
            }
        }
    }
    batch_keys(c, Ghost(k), p, m, g, lo, hi, all_in, lo16, hi16, t, key);
    let ghost c0 = counts@;
    let mut d: usize = 0;
    while d < kk
        invariant
            batch_ok(*c, k, p as int, m as int, g as int),
            kk == k,
            0 <= q0 <= p,
            bs == c.bs_o,
            pb == c.op_bases@[g as int],
            forall|q: int| p <= q < p + m ==> #[trigger] oprio(*c, q) == pb + c.op_codes@[q],
            key@.len() == OB,
            forall|i: int| 0 <= i < m ==> #[trigger] key@[i] == key_of(*c, lo as int, hi as int, p + i),
            d <= kk,
            counts@.len() == k,
            forall|e: int| 0 <= e < d ==> #[trigger] counts@[e] as int == count_raw(*c, lo as int, hi as int, e, q0, (p + m) as int),
            forall|e: int| d <= e < k ==> #[trigger] counts@[e] as int == count_raw(*c, lo as int, hi as int, e, q0, p as int),
        decreases kk - d,
    {
        let s: usize = if (d as u64) < pb || (d as u64) - pb > 255 {
            proof {
                assert forall|q: int| p <= q < p + m implies #[trigger] oprio(*c, q) != d by {
                    assert(oprio(*c, q) == pb + c.op_codes@[q]);
                }
                lemma_count_other_prio(*c, lo as int, hi as int, d as int, p as int, (p + m) as int);
            }
            0
        } else {
            let cc: u16 = ((d as u64) - pb) as u16;
            let mut s: u32 = 0;
            let mut i: usize = 0;
            let n = if m < key.len() { m } else { key.len() };
            while i < n
                invariant
                    batch_ok(*c, k, p as int, m as int, g as int),
                    n == m,
                    pb == c.op_bases@[g as int],
                    cc as int == d - pb,
                    cc <= 255,
                    forall|q: int| p <= q < p + m ==> #[trigger] oprio(*c, q) == pb + c.op_codes@[q],
                    key@.len() == OB,
                    forall|i2: int| 0 <= i2 < m ==> #[trigger] key@[i2] == key_of(*c, lo as int, hi as int, p + i2),
                    i <= m,
                    s <= i,
                    s as int == count_raw(*c, lo as int, hi as int, d as int, p as int, (p + i) as int),
                decreases m - i,
            {
                proof {
                    let q = (p + i) as int;
                    assert(key@[i as int] == key_of(*c, lo as int, hi as int, q));
                    assert(oprio(*c, q) == pb + c.op_codes@[q]);
                    if qual_raw(*c, lo as int, hi as int, q) {
                        assert((key@[i as int] == cc) == (oprio(*c, q) == d));
                    } else {
                        assert(key@[i as int] != cc);
                    }
                    lemma_count_step(*c, lo as int, hi as int, d as int, p as int, q);
                }
                s = s + if key[i] == cc { 1u32 } else { 0u32 };
                i = i + 1;
            }
            s as usize
        };
        proof {
            lemma_count_split(*c, lo as int, hi as int, d as int, q0, p as int, (p + m) as int);
            lemma_count_bound(*c, lo as int, hi as int, d as int, q0, (p + m) as int);
            lemma_count_bound(*c, lo as int, hi as int, d as int, p as int, (p + m) as int);
        }
        let nv = counts[d] + s;
        counts[d] = nv;
        d = d + 1;
    }
}

/// The lines of the orders batch `[p, p + m)` (`rstart(p + m) - rstart(p)`) and its longest run.
#[inline(always)]
fn batch_lines(c: &Cols, Ghost(k): Ghost<int>, p: usize, m: usize) -> (r: (usize, u8))
    requires
        fast_ok(*c, k),
        p + m <= c.n_o,
        m <= OB,
    ensures
        r.0 as int == rstart(*c, (p + m) as int) - rstart(*c, p as int),
        r.0 <= 255 * m,
        forall|i: int| 0 <= i < m ==> #[trigger] c.rl@[p + i] <= r.1,
    no_unwind
{
    let rlb = sub_slice(c.rl, p, p + m);
    let mut lines: usize = 0;
    let mut longest: u8 = 0;
    let mut i: usize = 0;
    while i < m
        invariant
            fast_ok(*c, k),
            p + m <= c.n_o,
            m <= OB,
            rlb@ == c.rl@.subrange(p as int, (p + m) as int),
            i <= m,
            lines as int == rstart(*c, (p + i) as int) - rstart(*c, p as int),
            lines <= 255 * i,
            forall|i2: int| 0 <= i2 < i ==> #[trigger] c.rl@[p + i2] <= longest,
        decreases m - i,
    {
        proof {
            lemma_rstart_bounds(*c, (p + i) as int);
        }
        let l = rlb[i];
        lines = lines + l as usize;
        longest = if l > longest { l } else { longest };
        i = i + 1;
    }
    (lines, longest)
}

/// The counts of stored orders rows `[q0, q1)` per priority index (`counts`: `kk` zeros; `flags`, `t`, `key`:
/// scratch).
pub fn run_fast(c: Cols, kk: usize, zmax: &[i64], q0: usize, q1: usize, lo: i64, hi: i64, counts: Vec<usize>,
    flags: Vec<u8>, t: Vec<u16>, key: Vec<u16>) -> (out: Vec<usize>)
    requires
        fast_ok(c, kk as int),
        zmax@.len() == c.od_bases@.len(),
        forall|q: int| 0 <= q < c.n_o ==> #[trigger] odate(c, q) <= zmax@[q / c.bs_o as int],
        q0 <= q1 <= c.n_o,
        counts@.len() == kk,
        forall|d: int| 0 <= d < kk ==> #[trigger] counts@[d] == 0,
        flags@.len() == FLAGS_LEN,
        t@.len() == OB,
        key@.len() == OB,
    ensures
        out@.len() == kk,
        forall|d: int| 0 <= d < kk ==> #[trigger] out@[d] as int == count_raw(c, lo as int, hi as int, d, q0 as int, q1 as int),
    no_unwind
{
    let ghost k = kk as int;
    let mut counts = counts;
    let mut flags = flags;
    let mut t = t;
    let mut key = key;
    proof {
        assert forall|d: int| 0 <= d < kk implies #[trigger] counts@[d] as int
            == count_raw(c, lo as int, hi as int, d, q0 as int, q0 as int) by {}
    }
    if q0 >= q1 {
        return counts;
    }
    let cur0 = super::kernel::lineitem_start(&c, Ghost(k), q0);
    proof {
        lemma_run_lines(c, q0 as int);
        lemma_merge_unique(c, q0 as int, cur0 as int, rstart(c, q0 as int));
    }
    let bs = c.bs_o;
    let mut cur = cur0;
    let mut p = q0;
    while p < q1
        invariant
            fast_ok(c, k),
            kk == k,
            bs == c.bs_o,
            zmax@.len() == c.od_bases@.len(),
            forall|q: int| 0 <= q < c.n_o ==> #[trigger] odate(c, q) <= zmax@[q / c.bs_o as int],
            q0 <= p <= q1 <= c.n_o,
            cur as int == rstart(c, p as int),
            flags@.len() == FLAGS_LEN,
            t@.len() == OB,
            key@.len() == OB,
            counts@.len() == k,
            forall|d: int| 0 <= d < k ==> #[trigger] counts@[d] as int == count_raw(c, lo as int, hi as int, d, q0 as int, p as int),
        decreases q1 - p,
    {
        let rem = bs - p % bs;
        let g = p / bs;
        let mut m = q1 - p;
        if m > OB {
            m = OB;
        }
        if m > rem {
            m = rem;
        }
        proof {
            lemma_group_of_row(p as int, bs as int);
            lemma_div_below(p as int, bs as int, c.ok_bases@.len() as int);
        }
        let (lines, longest) = batch_lines(&c, Ghost(k), p, m);
        proof {
            lemma_rstart_bounds(c, (p + m) as int);
            lemma_rstart_le(c, p as int, (p + m) as int);
            assert(255 * m <= 255 * OB) by (nonlinear_arith) requires m <= OB;
        }
        batch_flags(&c, Ghost(k), p, m, cur, lines, longest <= 8, &mut flags, &mut t);
        count_batch(&c, Ghost(k), kk, zmax, p, m, g, lo, hi, &t, &mut key, &mut counts, Ghost(q0 as int));
        cur = cur + lines;
        p = p + m;
    }
    counts
}

} // verus!
