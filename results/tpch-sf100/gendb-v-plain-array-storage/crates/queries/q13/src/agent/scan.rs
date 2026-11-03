//! Phase 1 of the fast path: one task per range of orders rows `lo..hi`, in two passes.
//! 1. `mark_range`: in blocks of `BLOCK` rows, the rows whose comment holds the pattern's segments in order
//!    (`text_rows::match_flags`, a windowed byte scan for the filter literal `g`) set their bit in the task's match
//!    bitmap (`bits_ok`: bit `x - lo` of `bits` for row `x`), and the block's comment bytes are tested for ASCII.
//! 2. `scatter_range`: one tight pass over `o_custkey` appends the customer index `o_custkey - base` of every row
//!    whose bit is clear and that is a customer row (`0 <= index < nc`) to the bucket of that index: bucket
//!    `index / SPAN`, stored as `index % SPAN` (u16). Keeping the scatter out of the byte scan keeps its `nb`
//!    write streams in the first-level cache.
//!
//! Layout of a task's output: one flat `u16` buffer of `nb` regions of `cap` slots (bucket `b` is
//! `buf[b * cap .. b * cap + fill[b]]`, `region`). A full region, or a non-ASCII comment byte, stops the task
//! (`ok == false`). The contract (`bucket_ok`): every entry of bucket `b` is a customer index `b * SPAN + entry`
//! below `nc`, and for every customer index `i` the number of copies of `i % SPAN` in bucket `i / SPAN` is the number
//! of rows of the task's range that count for `i` (`crange`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::common::segments::*;
use crate::agent::common::text_rows::*;
use crate::agent::tables::Cols;

verus! {

/// Rows per block of the scan (the flags of one block stay in the first-level cache).
pub const BLOCK: usize = 4096;

/// Customer indices per bucket (a bucket entry is the index's offset in its bucket, a `u16`).
pub const SPAN: usize = 65536;

// ------------------------------------------------------------------------------------------------ the count spec

/// The shape of the columns a task reads: well-formed comment offsets, one customer key per row.
pub open spec fn cols_wf(c: Cols) -> bool {
    &&& offs_wf(c.offs@, c.no as int, c.nbytes as int)
    &&& c.nbytes as int == c.bytes@.len()
    &&& c.ock@.len() == c.no
    &&& c.cck@.len() == c.nc
}

/// Orders row `j` matches the pattern (byte level).
pub open spec fn matched(c: Cols, ss: Seq<Seq<u8>>, j: int) -> bool {
    row_match(c.offs@, c.bytes@, ss, j)
}

/// The customer index orders row `j` counts for: `o_custkey - base` when the row does not match and the index is a
/// customer row, else -1.
pub open spec fn kidx(c: Cols, ss: Seq<Seq<u8>>, base: int, j: int) -> int {
    let k = c.ock@[j] as int - base;
    if !matched(c, ss, j) && 0 <= k < c.nc { k } else { -1 }
}

/// Number of orders rows in `[lo, hi)` counting for customer index `i`.
pub open spec fn crange(c: Cols, ss: Seq<Seq<u8>>, base: int, i: int, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo { 0 } else { crange(c, ss, base, i, lo, hi - 1) + if kidx(c, ss, base, hi - 1) == i { 1nat } else { 0nat } }
}

/// The bucket of customer index `i`, and its entry in that bucket.
pub open spec fn bucket(i: int) -> int { i / (SPAN as int) }
pub open spec fn boff(i: int) -> int { i % (SPAN as int) }

/// Number of copies of `x` in `s`.
pub open spec fn occ_of(s: Seq<u16>, x: int) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { occ_of(s.drop_last(), x) + if s.last() as int == x { 1nat } else { 0nat } }
}

/// Region `b` of a bucket buffer.
pub open spec fn region(buf: Seq<u16>, fill: Seq<usize>, cap: int, b: int) -> Seq<u16> {
    buf.subrange(b * cap, b * cap + fill[b] as int)
}

/// A task's buckets hold its counting rows `[lo, hi)`.
pub open spec fn bucket_ok(c: Cols, ss: Seq<Seq<u8>>, base: int, nb: int, cap: int, buf: Seq<u16>, fill: Seq<usize>,
    lo: int, hi: int) -> bool
{
    &&& fill.len() == nb && nb * cap <= buf.len() && cap >= 0
    &&& forall|b: int| 0 <= b < nb ==> #[trigger] fill[b] as int <= cap
    &&& forall|b: int, s: int| 0 <= b < nb && 0 <= s < fill[b] ==>
            b * (SPAN as int) + ((#[trigger] buf[b * cap + s]) as int) < c.nc
    &&& forall|i: int| 0 <= i < c.nc ==> #[trigger] occ_of(region(buf, fill, cap, bucket(i)), boff(i))
            == crange(c, ss, base, i, lo, hi)
}

// ------------------------------------------------------------------------------------------------ lemmas

/// One more row of the range.
proof fn lemma_crange_step(c: Cols, ss: Seq<Seq<u8>>, base: int, i: int, lo: int, x: int)
    requires lo <= x,
    ensures crange(c, ss, base, i, lo, x + 1) == crange(c, ss, base, i, lo, x) + if kidx(c, ss, base, x) == i { 1nat } else { 0nat },
{
}

/// Pushing `e` counts one more copy of `e`.
proof fn lemma_occ_push(s: Seq<u16>, e: u16, x: int)
    ensures occ_of(s.push(e), x) == occ_of(s, x) + if e as int == x { 1nat } else { 0nat },
{
    assert(s.push(e).drop_last() =~= s);
}

/// An index is its bucket and entry.
pub proof fn lemma_bucket(i: int)
    requires i >= 0,
    ensures i == bucket(i) * (SPAN as int) + boff(i), 0 <= boff(i) < SPAN, bucket(i) >= 0,
{
}

/// Two indices with the same bucket and entry are equal.
proof fn lemma_bucket_eq(i: int, k: int)
    requires i >= 0, k >= 0, bucket(i) == bucket(k), boff(i) == boff(k),
    ensures i == k,
{
    lemma_bucket(i);
    lemma_bucket(k);
}

/// Slot `b * cap + s` of region `b` (`s < cap`) lies before region `b + 1` and inside the buffer.
pub proof fn lemma_slot(b: int, s: int, cap: int, nb: int)
    requires 0 <= b < nb, 0 <= s < cap,
    ensures
        0 <= b * cap + s < nb * cap,
        b * cap + s < (b + 1) * cap,
        b * cap <= b * cap + s,
{
    assert(b * cap + s < (b + 1) * cap) by (nonlinear_arith) requires 0 <= s < cap;
    assert((b + 1) * cap <= nb * cap) by (nonlinear_arith) requires b + 1 <= nb, cap >= 0;
    assert(0 <= b * cap) by (nonlinear_arith) requires b >= 0, cap >= 0;
}

/// Region `b` has `fill[b]` entries, entry `s` at slot `b * cap + s`.
pub proof fn lemma_region(buf: Seq<u16>, fill: Seq<usize>, cap: int, nb: int, b: int)
    requires 0 <= b < nb, nb * cap <= buf.len(), fill.len() == nb, 0 <= fill[b] <= cap,
    ensures
        region(buf, fill, cap, b).len() == fill[b],
        forall|s: int| 0 <= s < fill[b] ==> #[trigger] region(buf, fill, cap, b)[s] == buf[b * cap + s],
{
    if fill[b] > 0 {
        lemma_slot(b, fill[b] - 1, cap, nb);
    } else {
        assert(0 <= b * cap <= nb * cap) by (nonlinear_arith) requires 0 <= b < nb, cap >= 0;
    }
}

/// Regions of different buckets are disjoint: slot `t` of region `b2` is not slot `f` of region `b`.
proof fn lemma_slots_apart(b: int, f: int, b2: int, t: int, cap: int)
    requires 0 <= b, 0 <= b2, b != b2, 0 <= f < cap, 0 <= t < cap,
    ensures b2 * cap + t != b * cap + f,
{
    if b2 < b {
        assert(b2 * cap + t < (b2 + 1) * cap) by (nonlinear_arith) requires 0 <= t < cap;
        assert((b2 + 1) * cap <= b * cap) by (nonlinear_arith) requires b2 + 1 <= b, cap >= 0;
    } else {
        assert(b * cap + f < (b + 1) * cap) by (nonlinear_arith) requires 0 <= f < cap;
        assert((b + 1) * cap <= b2 * cap) by (nonlinear_arith) requires b + 1 <= b2, cap >= 0;
    }
}

/// Splitting a 64-bit index into bucket and entry with a shift and a mask.
proof fn lemma_split_bits(k: u64)
    ensures (k >> 16u64) as int == bucket(k as int), (k & 0xffffu64) as int == boff(k as int),
{
    assert((k >> 16u64) == k / 65536u64 && (k & 0xffffu64) == k % 65536u64) by (bit_vector);
}

/// One row `x` of the scatter: the buckets of `[lo, x)` with row `x`'s index appended (when it counts) hold
/// `[lo, x + 1)`.
proof fn lemma_scatter_row(c: Cols, ss: Seq<Seq<u8>>, base: int, nb: int, cap: int, buf: Seq<u16>, fill: Seq<usize>,
    buf2: Seq<u16>, fill2: Seq<usize>, lo: int, x: int)
    requires
        bucket_ok(c, ss, base, nb, cap, buf, fill, lo, x), lo <= x, cap <= usize::MAX,
        forall|i: int| 0 <= i < c.nc ==> bucket(i) < nb,
        kidx(c, ss, base, x) == -1 ==> buf2 == buf && fill2 == fill,
        kidx(c, ss, base, x) >= 0 ==> ({
            let k = kidx(c, ss, base, x);
            let b = bucket(k);
            &&& fill[b] < cap
            &&& buf2 == buf.update(b * cap + fill[b] as int, boff(k) as u16)
            &&& fill2 == fill.update(b, (fill[b] + 1) as usize)
        }),
    ensures bucket_ok(c, ss, base, nb, cap, buf2, fill2, lo, x + 1),
{
    let k = kidx(c, ss, base, x);
    if k >= 0 {
        let b = bucket(k);
        let f = fill[b] as int;
        lemma_bucket(k);
        lemma_slot(b, f, cap, nb);
        assert(fill2[b] as int == f + 1);
        // region b gains the entry; the other regions keep theirs
        assert forall|b2: int| 0 <= b2 < nb implies #[trigger] region(buf2, fill2, cap, b2)
            == if b2 == b { region(buf, fill, cap, b).push(boff(k) as u16) } else { region(buf, fill, cap, b2) } by {
            if b2 == b {
                let r2 = region(buf2, fill2, cap, b);
                let r1 = region(buf, fill, cap, b).push(boff(k) as u16);
                assert(r2.len() == r1.len());
                assert forall|t: int| 0 <= t < r2.len() implies r2[t] == r1[t] by {
                    lemma_slot(b, t, cap, nb);
                }
                assert(r2 =~= r1);
            } else {
                let r2 = region(buf2, fill2, cap, b2);
                let r1 = region(buf, fill, cap, b2);
                assert(fill2[b2] == fill[b2]);
                if fill[b2] > 0 { lemma_slot(b2, fill[b2] - 1, cap, nb); } else { lemma_slot(b2, 0, cap, nb); }
                assert(r2.len() == r1.len());
                assert forall|t: int| 0 <= t < r2.len() implies r2[t] == r1[t] by {
                    lemma_slots_apart(b, f, b2, t, cap);
                    lemma_slot(b2, t, cap, nb);
                }
                assert(r2 =~= r1);
            }
        }
    }
    assert forall|i: int| 0 <= i < c.nc implies #[trigger] occ_of(region(buf2, fill2, cap, bucket(i)), boff(i))
        == crange(c, ss, base, i, lo, x + 1) by {
        lemma_crange_step(c, ss, base, i, lo, x);
        lemma_bucket(i);
        if k >= 0 {
            let b = bucket(k);
            if bucket(i) == b {
                lemma_occ_push(region(buf, fill, cap, b), boff(k) as u16, boff(i));
                lemma_bucket(k);
                if boff(i) == boff(k) { lemma_bucket_eq(i, k); }
            } else {
                assert(i != k);
            }
        }
    }
    assert forall|b2: int, t: int| 0 <= b2 < nb && 0 <= t < fill2[b2] implies
        b2 * (SPAN as int) + ((#[trigger] buf2[b2 * cap + t]) as int) < c.nc by {
        if k >= 0 {
            let b = bucket(k);
            let f = fill[b] as int;
            lemma_bucket(k);
            if b2 == b && t == f {
                lemma_slot(b, f, cap, nb);
            } else if b2 == b {
                lemma_slot(b, t, cap, nb);
            } else {
                lemma_slots_apart(b, f, b2, t, cap);
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ the match bitmap

/// Bit `i` of a bitmap of `u64` words (bit `i % 64` of word `i / 64`).
pub open spec fn bit_of(bits: Seq<u64>, i: int) -> bool {
    (bits[i / 64] >> ((i % 64) as u64)) & 1u64 == 1u64
}

/// The bitmap of a task's rows `lo..` up to row `x`: bit `y - lo` says whether row `y < x` matches, and every bit
/// from `x - lo` on is clear.
pub open spec fn bits_ok(c: Cols, ss: Seq<Seq<u8>>, bits: Seq<u64>, lo: int, x: int) -> bool {
    &&& lo <= x <= lo + 64 * bits.len()
    &&& forall|y: int| lo <= y < x ==> #[trigger] bit_of(bits, y - lo) == matched(c, ss, y)
    &&& forall|i: int| x - lo <= i < 64 * bits.len() ==> !#[trigger] bit_of(bits, i)
}

/// Setting bit `k` of a word: bit `k` is set, every other bit keeps its value.
proof fn lemma_set_bit(a: u64, k: u64, j: u64)
    requires k < 64, j < 64,
    ensures ((a | (1u64 << k)) >> j) & 1u64 == (if j == k { 1u64 } else { (a >> j) & 1u64 }),
{
    assert(((a | (1u64 << k)) >> j) & 1u64 == (if j == k { 1u64 } else { (a >> j) & 1u64 })) by (bit_vector)
        requires k < 64, j < 64;
}

/// A bit of a word is 0 or 1.
proof fn lemma_bit_01(a: u64, j: u64)
    ensures (a >> j) & 1u64 == 0u64 || (a >> j) & 1u64 == 1u64,
{
    assert((a >> j) & 1u64 == 0u64 || (a >> j) & 1u64 == 1u64) by (bit_vector);
}

/// A zero word has no bit set.
proof fn lemma_zero_bit(j: u64)
    ensures (0u64 >> j) & 1u64 == 0u64,
{
    assert((0u64 >> j) & 1u64 == 0u64) by (bit_vector);
}

/// A word index and bit index of `i` (`i` below `64 * len`).
proof fn lemma_word(i: int, len: int)
    requires 0 <= i < 64 * len,
    ensures 0 <= i / 64 < len, 0 <= i % 64 < 64, i == 64 * (i / 64) + i % 64,
{
}

/// Setting bit `i` of a bitmap: bit `i` is set, every other bit keeps its value.
proof fn lemma_set_bit_of(bits: Seq<u64>, i: int)
    requires 0 <= i < 64 * bits.len(),
    ensures ({
        let w = i / 64;
        let bits2 = bits.update(w, bits[w] | (1u64 << ((i % 64) as u64)));
        &&& bit_of(bits2, i)
        &&& forall|i2: int| 0 <= i2 < 64 * bits.len() && i2 != i ==> #[trigger] bit_of(bits2, i2) == bit_of(bits, i2)
    }),
{
    let w = i / 64;
    let k = (i % 64) as u64;
    let bits2 = bits.update(w, bits[w] | (1u64 << k));
    lemma_word(i, bits.len() as int);
    lemma_set_bit(bits[w], k, k);
    assert forall|i2: int| 0 <= i2 < 64 * bits.len() && i2 != i implies #[trigger] bit_of(bits2, i2) == bit_of(bits, i2) by {
        lemma_word(i2, bits.len() as int);
        if i2 / 64 == w {
            lemma_set_bit(bits[w], k, (i2 % 64) as u64);
        }
    }
}

/// A zeroed bitmap is `bits_ok` with no row yet.
proof fn lemma_bits_empty(c: Cols, ss: Seq<Seq<u8>>, bits: Seq<u64>, lo: int)
    requires forall|w: int| 0 <= w < bits.len() ==> #[trigger] bits[w] == 0u64,
    ensures bits_ok(c, ss, bits, lo, lo),
{
    assert forall|i: int| 0 <= i < 64 * bits.len() implies !#[trigger] bit_of(bits, i) by {
        lemma_word(i, bits.len() as int);
        lemma_zero_bit((i % 64) as u64);
    }
}

// ------------------------------------------------------------------------------------------------ the task

/// One task of phase 1: orders rows `lo..hi`.
pub struct ScanTask {
    pub c: Cols,
    pub segs: Arc<Segs>,
    pub gram: Gram,
    pub lo: usize,
    pub hi: usize,
    pub base: i64,
    pub nb: usize,
    pub cap: usize,
    pub buf: Vec<u16>,
    pub fill: Vec<usize>,
    pub flags: Vec<u8>,
    pub bits: Vec<u64>,
    pub g: Ghost<Seq<u8>>,
    pub ss: Ghost<Seq<Seq<u8>>>,
}

/// A task's result: its buckets when `ok`.
pub struct ScanOut {
    pub buf: Vec<u16>,
    pub fill: Vec<usize>,
    pub cap: usize,
    pub ok: bool,
}

/// The phase-1 preconditions shared by every task (the columns, the segments and the bucket layout).
pub open spec fn scan_pre(c: Cols, segs: &Segs, ss: Seq<Seq<u8>>, base: i64, nb: usize) -> bool {
    &&& cols_wf(c)
    &&& segs_view_ok(segs, ss)
    &&& 1 <= nb && c.nc <= u32::MAX
    &&& base as int + c.nc as int <= i64::MAX as int + 1
    &&& forall|i: int| 0 <= i < c.nc ==> bucket(i) < nb
}

/// The rows of a task's range: buckets and ASCII comments.
pub open spec fn scan_post(c: Cols, ss: Seq<Seq<u8>>, base: i64, nb: usize, cap: usize, out: ScanOut, lo: int, hi: int) -> bool {
    &&& out.cap == cap
    &&& out.ok ==> {
        &&& bucket_ok(c, ss, base as int, nb as int, cap as int, out.buf@, out.fill@, lo, hi)
        &&& forall|x: int| lo <= x < hi ==> #[trigger] ascii(val(c.offs@, c.bytes@, x))
    }
}

/// Zero every flag of a block.
fn zero_flags(flags: &mut Vec<u8>, n: usize)
    requires old(flags)@.len() == n,
    ensures final(flags)@.len() == n, forall|i: int| 0 <= i < n ==> #[trigger] final(flags)@[i] == 0u8,
    no_unwind
{
    let mut z: usize = 0;
    while z < n
        invariant z <= n, flags@.len() == n, forall|i: int| 0 <= i < z ==> #[trigger] flags@[i] == 0u8,
        decreases n - z,
    {
        flags[z] = 0u8;
        z = z + 1;
    }
}

/// One block `b0..b1` of a task's rows `lo..`: the matching rows (`text_rows::match_flags`) set their bits, and
/// the block's comment bytes are tested for ASCII. `false` when a comment byte is not ASCII.
fn mark_block(c: &Cols, segs: &Segs, gr: &Gram, flags: &mut Vec<u8>, bits: &mut Vec<u64>, lo: usize, b0: usize,
    b1: usize, Ghost(g): Ghost<Seq<u8>>, Ghost(ss): Ghost<Seq<Seq<u8>>>) -> (ok: bool)
    requires
        cols_wf(*c), segs_view_ok(segs, ss), gram_view_ok(*gr, ss, g),
        lo <= b0 < b1 <= c.no, b1 - b0 <= BLOCK, old(flags)@.len() == BLOCK,
        bits_ok(*c, ss, old(bits)@, lo as int, b0 as int), b1 <= lo + 64 * old(bits)@.len(),
    ensures
        final(flags)@.len() == BLOCK, final(bits)@.len() == old(bits)@.len(),
        ok ==> bits_ok(*c, ss, final(bits)@, lo as int, b1 as int),
        ok ==> forall|x: int| b0 <= x < b1 ==> #[trigger] ascii(val(c.offs@, c.bytes@, x)),
    no_unwind
{
    zero_flags(flags, BLOCK);
    match_flags(c.offs, c.bytes, c.nbytes, c.no, b0, b1, segs, gr, flags, Ghost(g), Ghost(ss));
    proof { lemma_offs_mono(c.offs@, c.no as int, c.nbytes as int, b0 as int, b1 as int); }
    let a = or_range(c.bytes, c.offs[b0] as usize, c.offs[b1] as usize);
    if a >= 0x80u8 {
        return false;
    }
    proof { lemma_rows_ascii(c.offs@, c.bytes@, c.no as int, b0 as int, b1 as int); }
    let ghost nw = bits@.len();
    let mut x = b0;
    while x < b1
        invariant
            lo <= b0 <= x <= b1 <= c.no, b1 - b0 <= BLOCK, flags@.len() == BLOCK, bits@.len() == nw,
            b1 <= lo + 64 * nw,
            forall|y: int| b0 <= y < b1 ==> (#[trigger] flags@[y - b0] != 0u8) == matched(*c, ss, y),
            bits_ok(*c, ss, bits@, lo as int, x as int),
        decreases b1 - x,
    {
        let i = x - lo;
        if flags[x - b0] != 0u8 {
            proof { lemma_set_bit_of(bits@, i as int); lemma_word(i as int, nw as int); }
            let w = i / 64;
            let k = (i % 64) as u64;
            bits[w] = bits[w] | (1u64 << k);
            proof {
                assert forall|y: int| lo <= y < x + 1 implies #[trigger] bit_of(bits@, y - lo) == matched(*c, ss, y) by {
                    if y < x { assert(y - lo != i); }
                }
            }
        } else {
            proof { assert(!bit_of(bits@, i as int)); }
        }
        x = x + 1;
    }
    true
}

/// The blocks of rows `lo..hi`: the bitmap of the matching rows, or `false` when a comment byte is not ASCII.
fn mark_range(c: &Cols, segs: &Segs, gr: &Gram, flags: &mut Vec<u8>, bits: &mut Vec<u64>, lo: usize, hi: usize,
    Ghost(g): Ghost<Seq<u8>>, Ghost(ss): Ghost<Seq<Seq<u8>>>) -> (ok: bool)
    requires
        cols_wf(*c), segs_view_ok(segs, ss), gram_view_ok(*gr, ss, g), lo <= hi <= c.no,
        old(flags)@.len() == BLOCK,
        bits_ok(*c, ss, old(bits)@, lo as int, lo as int), hi <= lo + 64 * old(bits)@.len(),
    ensures
        final(bits)@.len() == old(bits)@.len(),
        ok ==> bits_ok(*c, ss, final(bits)@, lo as int, hi as int),
        ok ==> forall|x: int| lo <= x < hi ==> #[trigger] ascii(val(c.offs@, c.bytes@, x)),
    no_unwind
{
    let ghost nw = bits@.len();
    let mut b0 = lo;
    while b0 < hi
        invariant
            cols_wf(*c), segs_view_ok(segs, ss), gram_view_ok(*gr, ss, g),
            lo <= b0 <= hi <= c.no, flags@.len() == BLOCK, bits@.len() == nw, nw == old(bits)@.len(),
            hi <= lo + 64 * nw,
            bits_ok(*c, ss, bits@, lo as int, b0 as int),
            forall|x: int| lo <= x < b0 ==> #[trigger] ascii(val(c.offs@, c.bytes@, x)),
        decreases hi - b0,
    {
        let b1 = if hi - b0 > BLOCK { b0 + BLOCK } else { hi };
        if !mark_block(c, segs, gr, flags, bits, lo, b0, b1, Ghost(g), Ghost(ss)) {
            return false;
        }
        b0 = b1;
    }
    true
}

/// The scatter of rows `lo..hi` (the bitmap marks the matching rows), from empty buckets, in one tight pass over
/// `o_custkey`: `false` when a region is full.
fn scatter_range(c: &Cols, base: i64, nb: usize, cap: usize, buf: &mut Vec<u16>, fill: &mut Vec<usize>, bits: &Vec<u64>,
    lo: usize, hi: usize, Ghost(ss): Ghost<Seq<Seq<u8>>>) -> (ok: bool)
    requires
        cols_wf(*c), 1 <= nb, c.nc <= u32::MAX, base as int + c.nc as int <= i64::MAX as int + 1,
        forall|i: int| 0 <= i < c.nc ==> bucket(i) < nb,
        lo <= hi <= c.no, bits_ok(*c, ss, bits@, lo as int, hi as int),
        bucket_ok(*c, ss, base as int, nb as int, cap as int, old(buf)@, old(fill)@, lo as int, lo as int),
    ensures
        final(buf)@.len() == old(buf)@.len(),
        ok ==> bucket_ok(*c, ss, base as int, nb as int, cap as int, final(buf)@, final(fill)@, lo as int, hi as int),
    no_unwind
{
    let nc = c.nc;
    if nc == 0 {
        return true;
    }
    // the largest customer key `base + nc - 1` (it fits: `base + nc <= i64::MAX + 1`)
    let hi_key: i64 = base + (nc - 1) as i64;
    let ghost nw = bits@.len();
    let blen = buf.len();
    let mut x = lo;
    while x < hi
        invariant
            cols_wf(*c), 1 <= nb, nc == c.nc, nc <= u32::MAX, base as int + nc as int <= i64::MAX as int + 1,
            forall|i: int| 0 <= i < c.nc ==> bucket(i) < nb,
            lo <= x <= hi <= c.no, bits@.len() == nw, bits_ok(*c, ss, bits@, lo as int, hi as int),
            buf@.len() == old(buf)@.len(), blen == buf@.len(), nc >= 1, hi_key as int == base as int + nc as int - 1,
            bucket_ok(*c, ss, base as int, nb as int, cap as int, buf@, fill@, lo as int, x as int),
        decreases hi - x,
    {
        let ghost (buf0, fill0) = (buf@, fill@);
        let ghost kx = kidx(*c, ss, base as int, x as int);
        let i = x - lo;
        proof { lemma_word(i as int, nw as int); }
        let m = (bits[i / 64] >> ((i % 64) as u64)) & 1u64;
        proof {
            lemma_bit_01(bits@[(i / 64) as int], (i % 64) as u64);
            assert(bit_of(bits@, x - lo) == matched(*c, ss, x as int));
        }
        if m == 0u64 {
            let o = c.ock[x];
            if base <= o && o <= hi_key {
                let k = (o - base) as u64;
                proof { lemma_split_bits(k); }
                let b = (k >> 16u64) as usize;
                let f = fill[b];
                if f >= cap {
                    return false;
                }
                proof { lemma_slot(b as int, f as int, cap as int, nb as int); }
                buf[b * cap + f] = (k & 0xffffu64) as u16;
                fill[b] = f + 1;
                proof {
                    assert(kx == k as int);
                    lemma_scatter_row(*c, ss, base as int, nb as int, cap as int, buf0, fill0, buf@, fill@, lo as int, x as int);
                }
            } else {
                proof {
                    assert(kx == -1);
                    lemma_scatter_row(*c, ss, base as int, nb as int, cap as int, buf0, fill0, buf@, fill@, lo as int, x as int);
                }
            }
        } else {
            proof {
                assert(kx == -1);
                lemma_scatter_row(*c, ss, base as int, nb as int, cap as int, buf0, fill0, buf@, fill@, lo as int, x as int);
            }
        }
        x = x + 1;
    }
    true
}

/// The empty buckets hold the empty row range.
proof fn lemma_buckets_empty(c: Cols, ss: Seq<Seq<u8>>, base: int, nb: int, cap: int, buf: Seq<u16>, fill: Seq<usize>, lo: int)
    requires
        fill == Seq::new(nb as nat, |_i: int| 0usize), nb * cap <= buf.len(), cap >= 0, nb >= 1,
        forall|i: int| 0 <= i < c.nc ==> bucket(i) < nb,
    ensures bucket_ok(c, ss, base, nb, cap, buf, fill, lo, lo),
{
    assert forall|i: int| 0 <= i < c.nc implies #[trigger] occ_of(region(buf, fill, cap, bucket(i)), boff(i))
        == crange(c, ss, base, i, lo, lo) by {
        lemma_bucket(i);
        lemma_slot(bucket(i), 0, cap + 1, nb);
        assert(bucket(i) * cap <= nb * cap) by (nonlinear_arith) requires bucket(i) <= nb, cap >= 0;
        assert(fill[bucket(i)] == 0usize);
        assert(region(buf, fill, cap, bucket(i)).len() == 0);
    }
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        &&& scan_pre(self.c, &*self.segs, self.ss@, self.base, self.nb)
        &&& gram_view_ok(self.gram, self.ss@, self.g@)
        &&& self.lo <= self.hi <= self.c.no
        &&& self.nb * self.cap <= self.buf@.len()
        &&& self.fill@ == Seq::new(self.nb as nat, |_i: int| 0usize)
        &&& self.flags@.len() == BLOCK
        &&& self.bits@ == Seq::new(self.bits@.len(), |_i: int| 0u64)
        &&& self.hi <= self.lo + 64 * self.bits@.len()
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        scan_post(self.c, self.ss@, self.base, self.nb, self.cap, out, self.lo as int, self.hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: ScanOut) {
        let ScanTask { c, segs, gram, lo, hi, base, nb, cap, buf, fill, flags, bits, g, ss } = self;
        let mut buf = buf;
        let mut fill = fill;
        let mut flags = flags;
        let mut bits = bits;
        proof {
            lemma_bits_empty(c, ss@, bits@, lo as int);
            lemma_buckets_empty(c, ss@, base as int, nb as int, cap as int, buf@, fill@, lo as int);
        }
        let ok = mark_range(&c, &*segs, &gram, &mut flags, &mut bits, lo, hi, Ghost(g@), Ghost(ss@))
            && scatter_range(&c, base, nb, cap, &mut buf, &mut fill, &bits, lo, hi, Ghost(ss@));
        ScanOut { buf, fill, cap, ok }
    }
}

} // verus!
