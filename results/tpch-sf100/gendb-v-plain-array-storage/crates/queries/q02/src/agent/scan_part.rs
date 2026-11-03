//! Phase-1 worker task: one range of the part scan and one range of the supplier scan.
//!
//! Part scan: the keys of the part rows of `[lo, hi)` with `p_size = target` whose `p_type` ends with `suffix`
//! (the `LIKE '%<suffix>'` fast path). Rows are processed in batches of `BATCH`: a first pass collects the rows of
//! the batch with the requested size (a sequential read of `sizes`), a second pass tests their types, so the
//! random reads of the type offsets and bytes of different rows overlap. The keys go into a preallocated
//! `SlotBuffer` whose capacity is a guess: when it is too small the task reports `complete == false` and the
//! caller rescans the range with room for every row.
//!
//! Supplier scan: for each supplier row of `[slo, shi)` whether it lies in a nation of the requested region
//! (`flags[b - slo]`), and whether the supplier keys of the range are `base + b` (`dense`), which lets the
//! partsupp scan find a supplier row by arithmetic.
//!
//! Column layout (the flat storage's): `sizes[a]`, `keys[a]` for rows `0..n`; text `p_type` of row `a` is
//! `tbytes[toff[a] - toff[0] .. toff[a + 1] - toff[0]]` (`n + 1` monotone offsets).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::common::slot_buffer::SlotBuffer;
use crate::agent::common::key_lookup::find_key;
use crate::agent::common::collect::{collect_equal, collect_equal4, eq_collected, EQ_BLOCK};
use crate::agent::common::like_suffix::ends_with;

verus! {

/// Rows per batch of the part scan.
pub const BATCH: usize = 4096;

/// Bytes of text row `a` of a column given by `n + 1` offsets and the bytes they address.
pub open spec fn text_row(toff: Seq<i64>, tbytes: Seq<u8>, a: int) -> Seq<u8> {
    tbytes.subrange(toff[a] - toff[0], toff[a + 1] - toff[0])
}

/// Well-formed text column of `n` rows: monotone offsets addressing exactly `tbytes`.
pub open spec fn text_col_wf(toff: Seq<i64>, tbytes: Seq<u8>, n: int) -> bool {
    &&& toff.len() == n + 1
    &&& 0 <= toff[0]
    &&& forall|a: int, b: int| 0 <= a <= b <= n ==> toff[a] <= toff[b]
    &&& tbytes.len() == toff[n] - toff[0]
}

/// The part-row condition of the scan.
pub open spec fn part_hit(sizes: Seq<i64>, toff: Seq<i64>, tbytes: Seq<u8>, target: i64, suffix: Seq<u8>, a: int) -> bool {
    sizes[a] == target && ends_with(text_row(toff, tbytes, a), suffix)
}

/// The part-scan inputs of one task.
pub struct PartScan {
    pub sizes: &'static [i64],
    pub keys: &'static [i64],
    pub toff: &'static [i64],
    pub tbytes: &'static [u8],
    pub tlen: usize,
    pub n: usize,
    pub lo: usize,
    pub hi: usize,
    pub target: i64,
    pub suffix: &'static [u8],
    pub slen: usize,
}

impl PartScan {
    pub open spec fn wf(&self) -> bool {
        &&& self.sizes@.len() == self.n
        &&& self.keys@.len() == self.n
        &&& text_col_wf(self.toff@, self.tbytes@, self.n as int)
        &&& self.tlen == self.tbytes@.len()
        &&& self.lo <= self.hi <= self.n
        &&& self.slen == self.suffix@.len()
    }

    pub open spec fn hit(&self, a: int) -> bool {
        part_hit(self.sizes@, self.toff@, self.tbytes@, self.target, self.suffix@, a)
    }

    /// Key `k` is the key of a hit row of `[lo, end)`.
    pub open spec fn sourced(&self, end: int, k: i64) -> bool {
        exists|x: int| self.lo <= x < end && #[trigger] self.hit(x) && self.keys@[x] == k
    }

    /// `out` lists exactly the keys of the hit rows of `[lo, end)` (every listed key comes from a hit row, every hit
    /// row's key is listed).
    pub open spec fn covers(&self, end: int, out: Seq<i64>) -> bool {
        &&& forall|j: int| 0 <= j < out.len() ==> self.sourced(end, #[trigger] out[j])
        &&& forall|x: int| self.lo <= x < end && #[trigger] self.hit(x) ==> listed(out, self.keys@[x])
    }
}

/// `k` occurs in `out`.
pub open spec fn listed(out: Seq<i64>, k: i64) -> bool {
    exists|j: int| 0 <= j < out.len() && out[j] == k
}

/// Rows of `[p, q)` that are not hits do not change the coverage.
proof fn lemma_covers_skip(s: PartScan, p: int, q: int, out: Seq<i64>)
    requires
        s.covers(p, out),
        p <= q,
        forall|x: int| p <= x < q ==> !#[trigger] s.hit(x),
    ensures s.covers(q, out),
{
    assert forall|j: int| 0 <= j < out.len() implies s.sourced(q, #[trigger] out[j]) by {
        let x = choose|x: int| s.lo <= x < p && #[trigger] s.hit(x) && s.keys@[x] == out[j];
    }
}

/// A hit row at `p` extends the coverage by its key.
proof fn lemma_covers_push(s: PartScan, p: int, out: Seq<i64>)
    requires
        s.covers(p, out),
        s.lo <= p,
        s.hit(p),
    ensures s.covers(p + 1, out.push(s.keys@[p])),
{
    let v = out.push(s.keys@[p]);
    assert forall|j: int| 0 <= j < v.len() implies s.sourced(p + 1, #[trigger] v[j]) by {
        if j < out.len() {
            assert(v[j] == out[j]);
            let x = choose|x: int| s.lo <= x < p && #[trigger] s.hit(x) && s.keys@[x] == out[j];
        } else {
            assert(s.hit(p) && s.keys@[p] == v[j]);
        }
    }
    assert forall|x: int| s.lo <= x < p + 1 && #[trigger] s.hit(x) implies listed(v, s.keys@[x]) by {
        if x < p {
            let j = choose|j: int| 0 <= j < out.len() && out[j] == s.keys@[x];
            assert(v[j] == out[j]);
        } else {
            assert(v[out.len() as int] == s.keys@[x]);
        }
    }
}

/// Two scans over the same columns with adjacent ranges: the concatenation of their keys covers the union.
pub proof fn lemma_covers_concat(s0: PartScan, s1: PartScan, mid: int, end: int, out0: Seq<i64>, out1: Seq<i64>)
    requires
        s0.covers(mid, out0),
        s1.covers(end, out1),
        s1.lo == mid,
        s0.lo <= mid <= end,
        s0.sizes == s1.sizes, s0.keys == s1.keys, s0.toff == s1.toff, s0.tbytes == s1.tbytes,
        s0.target == s1.target, s0.suffix == s1.suffix,
    ensures s0.covers(end, out0 + out1),
{
    let v = out0 + out1;
    assert forall|j: int| 0 <= j < v.len() implies s0.sourced(end, #[trigger] v[j]) by {
        if j < out0.len() {
            assert(v[j] == out0[j]);
            assert(s0.sourced(mid, out0[j]));
            let x = choose|x: int| s0.lo <= x < mid && #[trigger] s0.hit(x) && s0.keys@[x] == out0[j];
        } else {
            assert(v[j] == out1[j - out0.len()]);
            assert(s1.sourced(end, out1[j - out0.len()]));
            let x = choose|x: int| s1.lo <= x < end && #[trigger] s1.hit(x) && s1.keys@[x] == out1[j - out0.len()];
            assert(s0.hit(x));
        }
    }
    assert forall|x: int| s0.lo <= x < end && #[trigger] s0.hit(x) implies listed(v, s0.keys@[x]) by {
        if x < mid {
            let j = choose|j: int| 0 <= j < out0.len() && out0[j] == s0.keys@[x];
            assert(v[j] == out0[j]);
        } else {
            assert(s1.hit(x));
            let j = choose|j: int| 0 <= j < out1.len() && out1[j] == s1.keys@[x];
            assert(v[out0.len() + j] == out1[j]);
        }
    }
}

/// Byte position (in `tbytes`) where text row `a` starts and ends.
pub open spec fn row_start(toff: Seq<i64>, a: int) -> int { toff[a] - toff[0] }
pub open spec fn row_end(toff: Seq<i64>, a: int) -> int { toff[a + 1] - toff[0] }

/// `(ok, from)` locates the last `slen` bytes of text row `a`: `ok` exactly when the row has at least `slen` bytes,
/// and then they are `tbytes[from .. from + slen]`.
pub open spec fn window_of(toff: Seq<i64>, a: int, slen: int, ok: bool, from: int) -> bool {
    &&& ok == (row_end(toff, a) - row_start(toff, a) >= slen)
    &&& ok ==> from == row_end(toff, a) - slen && row_start(toff, a) <= from
}

/// The window of the last `slen` bytes of text row `a` (`window_of`); reads the row's two offsets.
fn row_window(toff: &[i64], tlen: usize, n: usize, a: usize, slen: usize, Ghost(tbytes): Ghost<Seq<u8>>) -> (r: (bool, usize))
    requires
        text_col_wf(toff@, tbytes, n as int),
        tlen == tbytes.len(),
        a < n,
    ensures
        window_of(toff@, a as int, slen as int, r.0, r.1 as int),
        r.0 ==> r.1 + slen <= tlen,
    no_unwind
{
    let base = toff[0];
    let s0 = toff[a];
    let e0 = toff[a + 1];
    proof {
        assert(toff@[0] <= toff@[a as int]);
        assert(toff@[a as int] <= toff@[a + 1]);
        assert(toff@[a + 1] <= toff@[n as int]);
    }
    let start = (s0 - base) as usize;
    let end = (e0 - base) as usize;
    if end - start >= slen {
        (true, end - slen)
    } else {
        (false, 0)
    }
}

/// Whether `tbytes[from .. from + slen] == suffix`, given its first byte `first` (already loaded); compares
/// without early exit (no data-dependent branch), so the byte loads of different rows overlap.
fn window_matches(tbytes: &[u8], tlen: usize, from: usize, suffix: &[u8], slen: usize, first: u8) -> (r: bool)
    requires
        tlen == tbytes@.len(),
        slen == suffix@.len(),
        from + slen <= tlen,
        slen > 0 ==> first == tbytes@[from as int],
    ensures r == (tbytes@.subrange(from as int, from + slen) == suffix@),
    no_unwind
{
    if slen == 0 {
        proof { assert(tbytes@.subrange(from as int, from + slen) =~= suffix@); }
        return true;
    }
    let mut diff: u8 = first ^ suffix[0];
    proof { lemma_or_xor_zero(0, first, suffix@[0]); assert((0u8 | (first ^ suffix@[0])) == (first ^ suffix@[0])) by (bit_vector); }
    let mut j: usize = 1;
    while j < slen
        invariant
            slen == suffix@.len(),
            from + slen <= tbytes@.len(),
            1 <= j <= slen,
            (diff == 0) <==> forall|q: int| 0 <= q < j ==> tbytes@[from + q] == suffix@[q],
        decreases slen - j,
    {
        let x = tbytes[from + j];
        let y = suffix[j];
        proof { lemma_or_xor_zero(diff, x, y); }
        diff = diff | (x ^ y);
        proof {
            if diff == 0 {
                assert forall|q: int| 0 <= q < j + 1 implies tbytes@[from + q] == suffix@[q] by {}
            }
        }
        j = j + 1;
    }
    let ghost w = tbytes@.subrange(from as int, from + slen);
    if diff == 0 {
        proof { assert(w =~= suffix@); }
        true
    } else {
        proof {
            let q = choose|q: int| 0 <= q < slen && tbytes@[from + q] != suffix@[q];
            assert(w[q] == tbytes@[from + q]);
        }
        false
    }
}

/// The window test is the suffix test of the row.
proof fn lemma_window_ends_with(toff: Seq<i64>, tbytes: Seq<u8>, n: int, a: int, suffix: Seq<u8>, ok: bool, from: int)
    requires
        text_col_wf(toff, tbytes, n),
        0 <= a < n,
        window_of(toff, a, suffix.len() as int, ok, from),
    ensures
        ends_with(text_row(toff, tbytes, a), suffix)
            == (ok && tbytes.subrange(from, from + suffix.len()) == suffix),
{
    assert(toff[0] <= toff[a]);
    assert(toff[a] <= toff[a + 1]);
    assert(toff[a + 1] <= toff[n]);
    let t = text_row(toff, tbytes, a);
    if ok {
        assert(t.subrange(t.len() - suffix.len(), t.len() as int) =~= tbytes.subrange(from, from + suffix.len()));
    }
}

/// `d | (x ^ y)` is zero exactly when `d` is zero and `x == y`.
proof fn lemma_or_xor_zero(d: u8, x: u8, y: u8)
    ensures ((d | (x ^ y)) == 0) <==> (d == 0 && x == y),
{
    assert(((d | (x ^ y)) == 0) <==> (d == 0 && x == y)) by (bit_vector);
}

/// Scratch buffers of the passes 2-3 of one task (each `BATCH` long, shared by its lanes): for each collected row
/// of a batch, its suffix window (`okl`, `from`), the window's first byte and whether the row is a hit.
pub struct PartPass {
    pub keep: Vec<bool>,
    pub from: Vec<usize>,
    pub okl: Vec<bool>,
    pub first: Vec<u8>,
}

impl PartPass {
    pub open spec fn wf(&self) -> bool {
        self.keep@.len() == BATCH && self.from@.len() == BATCH && self.okl@.len() == BATCH && self.first@.len() == BATCH
    }

    /// Fresh buffers (calling thread; allocates).
    pub fn new() -> (s: PartPass)
        ensures s.wf(),
    {
        PartPass { keep: vec![false; BATCH], from: vec![0usize; BATCH], okl: vec![false; BATCH], first: vec![0u8; BATCH] }
    }
}

/// A batch buffer for the rows of `scan` (`BATCH` long, or empty for an empty range).
pub open spec fn part_batch_ok(batch: Seq<usize>, scan: PartScan) -> bool {
    batch.len() == BATCH || scan.lo == scan.hi
}

impl PartScan {
    /// Passes 2-3 of one batch `[a, end)` whose rows with the requested size are `batch[0..k]` (pass 1): append the
    /// keys of the batch's hits to `out`; `false` when `out` had too little room. Pass 2 tests the suffix of each
    /// collected row in three sub-passes whose loads are independent of each other (the row's offsets, the first
    /// byte of its window, the comparison), so the cache misses of different rows overlap.
    pub fn batch_passes(&self, out0: SlotBuffer<i64>, batch: &Vec<usize>, pass: &mut PartPass, a: usize, end: usize, k: usize)
        -> (r: (SlotBuffer<i64>, bool))
        requires
            self.wf(),
            old(pass).wf(),
            out0.wf(),
            self.lo <= a <= end <= self.hi,
            end - a <= BATCH,
            self.covers(a as int, out0.view()),
            out0.view().len() <= a - self.lo,
            eq_collected(self.sizes@, a as int, end as int, self.target, batch@, k as int),
        ensures
            final(pass).wf(),
            r.0.wf(),
            r.0.capacity() == out0.capacity(),
            r.1 ==> self.covers(end as int, r.0.view()) && r.0.view().len() <= end - self.lo,
            out0.capacity() >= self.hi - self.lo ==> r.1,
        no_unwind
    {
        let ghost cap = out0.capacity();
        let mut out = out0;
        proof {
            assert forall|y: int| a <= y < end && self.sizes@[y] == self.target implies exists|i: int| 0 <= i < k && #[trigger] batch@[i] == y by {
                assert(self.sizes@[y] == self.target);
            }
        }
        // Pass 2a: the suffix window of each collected row (its two offsets).
        let mut j: usize = 0;
        while j < k
            invariant
                self.wf(),
                pass.wf(),
                k <= end - a, end <= self.hi, a <= end, end - a <= BATCH, k <= batch@.len(),
                j <= k,
                forall|i: int| 0 <= i < k ==> a <= #[trigger] batch@[i] < end && self.sizes@[batch@[i] as int] == self.target,
                forall|i: int| 0 <= i < j ==> window_of(self.toff@, batch@[i] as int, self.slen as int, #[trigger] pass.okl@[i], pass.from@[i] as int)
                    && (pass.okl@[i] ==> pass.from@[i] + self.slen <= self.tlen),
            decreases k - j,
        {
            let y = batch[j];
            let (ok, f) = row_window(self.toff, self.tlen, self.n, y, self.slen, Ghost(self.tbytes@));
            pass.okl[j] = ok;
            pass.from[j] = f;
            j = j + 1;
        }
        // Pass 2b: the first byte of each window (independent loads of the bytes).
        j = 0;
        while j < k
            invariant
                self.wf(),
                pass.wf(),
                j <= k, k <= BATCH, k <= batch@.len(),
                forall|i: int| 0 <= i < k ==> (#[trigger] pass.okl@[i] ==> pass.from@[i] + self.slen <= self.tlen),
                forall|i: int| 0 <= i < j ==> (pass.okl@[i] && self.slen > 0 ==> #[trigger] pass.first@[i] == self.tbytes@[pass.from@[i] as int]),
            decreases k - j,
        {
            if pass.okl[j] && self.slen > 0 {
                let f = pass.from[j];
                pass.first[j] = self.tbytes[f];
            }
            j = j + 1;
        }
        // Pass 2c: the suffix test of each collected row.
        j = 0;
        while j < k
            invariant
                self.wf(),
                pass.wf(),
                k <= end - a, end <= self.hi, a <= end, end - a <= BATCH, k <= batch@.len(),
                j <= k,
                forall|i: int| 0 <= i < k ==> a <= #[trigger] batch@[i] < end && self.sizes@[batch@[i] as int] == self.target,
                forall|i: int| 0 <= i < k ==> window_of(self.toff@, batch@[i] as int, self.slen as int, #[trigger] pass.okl@[i], pass.from@[i] as int)
                    && (pass.okl@[i] ==> pass.from@[i] + self.slen <= self.tlen),
                forall|i: int| 0 <= i < k ==> (pass.okl@[i] && self.slen > 0 ==> #[trigger] pass.first@[i] == self.tbytes@[pass.from@[i] as int]),
                forall|i: int| 0 <= i < j ==> #[trigger] pass.keep@[i] == self.hit(batch@[i] as int),
            decreases k - j,
        {
            let ok = pass.okl[j];
            let f = if ok { window_matches(self.tbytes, self.tlen, pass.from[j], self.suffix, self.slen, pass.first[j]) } else { false };
            proof {
                let y = batch@[j as int] as int;
                assert(pass.okl@[j as int] == ok);
                lemma_window_ends_with(self.toff@, self.tbytes@, self.n as int, y, self.suffix@, ok, pass.from@[j as int] as int);
            }
            pass.keep[j] = f;
            j = j + 1;
        }
        // Pass 3: the keys of the hits.
        proof {
            let next = if 0 < k { batch@[0] as int } else { end as int };
            assert forall|y: int| a <= y < next implies !#[trigger] self.hit(y) by {
                if self.sizes@[y] == self.target {
                    let i = choose|i: int| 0 <= i < k && #[trigger] batch@[i] == y;
                    if i > 0 { assert(batch@[0] < batch@[i]); }
                }
            }
            lemma_covers_skip(*self, a as int, next, out.view());
        }
        j = 0;
        while j < k
            invariant
                self.wf(),
                pass.wf(),
                self.lo <= a <= end <= self.hi,
                end - a <= BATCH,
                k <= end - a,
                k <= batch@.len(),
                j <= k,
                out.wf(),
                out.capacity() == cap,
                cap == out0.capacity(),
                out.view().len() <= (a - self.lo) + j,
                forall|i: int| 0 <= i < k ==> a <= #[trigger] batch@[i] < end && self.sizes@[batch@[i] as int] == self.target,
                forall|i: int, i2: int| 0 <= i < i2 < k ==> batch@[i] < batch@[i2],
                forall|y: int| a <= y < end && self.sizes@[y] == self.target ==> exists|i: int| 0 <= i < k && #[trigger] batch@[i] == y,
                forall|i: int| 0 <= i < k ==> #[trigger] pass.keep@[i] == self.hit(batch@[i] as int),
                self.covers(if j < k { batch@[j as int] as int } else { end as int }, out.view()),
            decreases k - j,
        {
            let y = batch[j];
            let ghost before = out.view();
            if pass.keep[j] {
                if !out.has_room() {
                    proof { assert(out.view().len() < self.hi - self.lo); }
                    return (out, false);
                }
                out.push(self.keys[y]);
                proof { lemma_covers_push(*self, y as int, before); }
            } else {
                proof { lemma_covers_skip(*self, y as int, y + 1, before); }
            }
            proof {
                let next = if j + 1 < k { batch@[j + 1] as int } else { end as int };
                assert forall|z: int| y + 1 <= z < next implies !#[trigger] self.hit(z) by {
                    if self.sizes@[z] == self.target {
                        let i = choose|i: int| 0 <= i < k && #[trigger] batch@[i] == z;
                        if i <= j { assert(batch@[i] <= batch@[j as int]); }
                        if i > j + 1 { assert(batch@[j + 1] < batch@[i]); }
                    }
                }
                lemma_covers_skip(*self, y + 1, next, out.view());
            }
            j = j + 1;
        }
        (out, true)
    }

    /// Scan `[a0, hi)` after `[lo, a0)`, whose keys `out0` holds; `false` when `out0` had too little room.
    pub fn run_from(&self, out0: SlotBuffer<i64>, batch: &mut Vec<usize>, pass: &mut PartPass, a0: usize) -> (r: (SlotBuffer<i64>, bool))
        requires
            self.wf(),
            out0.wf(),
            part_batch_ok(old(batch)@, *self),
            old(pass).wf(),
            self.lo <= a0 <= self.hi,
            self.covers(a0 as int, out0.view()),
            out0.view().len() <= a0 - self.lo,
        ensures
            part_batch_ok(final(batch)@, *self),
            final(pass).wf(),
            r.0.wf(),
            r.0.capacity() == out0.capacity(),
            r.1 ==> self.covers(self.hi as int, r.0.view()),
            out0.capacity() >= self.hi - self.lo ==> r.1,
        no_unwind
    {
        let mut out = out0;
        let mut a = a0;
        while a < self.hi
            invariant
                self.wf(),
                self.lo <= a <= self.hi,
                part_batch_ok(batch@, *self),
                pass.wf(),
                out.wf(),
                self.covers(a as int, out.view()),
                out.capacity() == out0.capacity(),
                out.view().len() <= a - self.lo,
            decreases self.hi - a,
        {
            let end = if self.hi - a > BATCH { a + BATCH } else { self.hi };
            // Pass 1: the rows of the batch with the requested size, in increasing order.
            let k = collect_equal(self.sizes, self.n, a, end, self.target, batch);
            let (o, ok) = self.batch_passes(out, batch, pass, a, end, k);
            if !ok {
                return (o, false);
            }
            out = o;
            a = end;
        }
        (out, true)
    }

    /// Scan `[lo, hi)`: the keys of the hit rows; `false` when `out0` had too little room.
    pub fn run_scan(&self, out0: SlotBuffer<i64>) -> (r: (SlotBuffer<i64>, bool))
        requires
            self.wf(),
            out0.wf(),
            out0.view() == Seq::<i64>::empty(),
        ensures
            r.0.wf(),
            r.1 ==> self.covers(self.hi as int, r.0.view()),
            out0.capacity() >= self.hi - self.lo ==> r.1,
    {
        let mut batch = vec![0usize; BATCH];
        let mut pass = PartPass::new();
        self.run_from(out0, &mut batch, &mut pass, self.lo)
    }
}

/// One lane of a phase-1 task: a part row range, its key buffer and its batch buffer.
pub struct PartLane {
    pub scan: PartScan,
    pub out: SlotBuffer<i64>,
    pub batch: Vec<usize>,
}

impl PartLane {
    pub open spec fn pre(&self) -> bool {
        &&& self.scan.wf()
        &&& self.out.wf()
        &&& self.out.view() == Seq::<i64>::empty()
        &&& part_batch_ok(self.batch@, self.scan)
    }
}

/// The keys of one lane and whether they are complete (`false`: the buffer was too small).
pub struct PartLaneOut {
    pub keys: SlotBuffer<i64>,
    pub complete: bool,
}

pub open spec fn part_lane_post(l: PartLane, o: PartLaneOut) -> bool {
    o.keys.wf() && (o.complete ==> l.scan.covers(l.scan.hi as int, o.keys.view()))
}

/// Lanes `l` and `m` select from the same size column with the same target.
pub open spec fn same_select(l: PartLane, m: PartLane) -> bool {
    l.scan.sizes == m.scan.sizes && l.scan.n == m.scan.n && l.scan.target == m.scan.target
}

/// The smaller of two counts.
fn min_usize(x: usize, y: usize) -> (r: usize)
    ensures r <= x, r <= y,
    no_unwind
{
    if x < y { x } else { y }
}

/// The supplier-scan inputs of one task.
pub struct SuppScan {
    pub skeys: &'static [i64],
    pub snk: &'static [i64],
    pub ns: usize,
    pub slo: usize,
    pub shi: usize,
    pub base: i64,
    pub nat_keys: &'static [i64],
    pub nn: usize,
    pub nat_ok: Arc<Vec<bool>>,
}

/// No key occurs twice.
pub open spec fn keys_unique(keys: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i < keys.len() && 0 <= j < keys.len() && i != j ==> keys[i] != keys[j]
}

/// Supplier row `b` lies in a nation of the requested region.
pub open spec fn supp_in_region(supp_nk: Seq<i64>, nat_keys: Seq<i64>, nat_ok: Seq<bool>, b: int) -> bool {
    exists|d: int| 0 <= d < nat_keys.len() && nat_keys[d] == supp_nk[b] && #[trigger] nat_ok[d]
}

/// Whether supplier row `b` lies in a nation of the region.
pub fn supplier_in_region(supp_nk: &[i64], ns: usize, nat_keys: &[i64], nn: usize, nat_ok: &Vec<bool>, b: usize) -> (r: bool)
    requires
        ns == supp_nk@.len(),
        b < ns,
        nn == nat_keys@.len(),
        nat_ok@.len() == nn,
        keys_unique(nat_keys@),
    ensures r == supp_in_region(supp_nk@, nat_keys@, nat_ok@, b as int),
    no_unwind
{
    match find_key(nat_keys, nn, supp_nk[b]) {
        Some(d) => {
            proof {
                if supp_in_region(supp_nk@, nat_keys@, nat_ok@, b as int) {
                    let d2 = choose|d2: int| 0 <= d2 < nat_keys@.len() && nat_keys@[d2] == supp_nk@[b as int] && #[trigger] nat_ok@[d2];
                    assert(d2 == d as int);
                }
            }
            nat_ok[d]
        },
        None => false,
    }
}

impl SuppScan {
    pub open spec fn wf(&self) -> bool {
        &&& self.skeys@.len() == self.ns
        &&& self.snk@.len() == self.ns
        &&& self.slo <= self.shi <= self.ns
        &&& self.nat_keys@.len() == self.nn
        &&& self.nat_ok@.len() == self.nn
        &&& keys_unique(self.nat_keys@)
    }

    /// `flags[b - slo]` is the region test of supplier row `b`; `dense` means the keys of the range are `base + b`.
    pub open spec fn done(&self, flags: Seq<bool>, dense: bool) -> bool {
        &&& flags.len() == self.shi - self.slo
        &&& forall|b: int| self.slo <= b < self.shi ==>
            #[trigger] flags[b - self.slo] == supp_in_region(self.snk@, self.nat_keys@, self.nat_ok@, b)
        &&& dense ==> forall|b: int| self.slo <= b < self.shi ==> #[trigger] self.skeys@[b] == self.base + b
    }

    /// Also returns the number of flagged suppliers (a capacity hint for the partsupp scan).
    pub fn run_scan(&self, flags: Vec<bool>) -> (r: (Vec<bool>, bool, usize))
        requires self.wf(), flags@.len() == self.shi - self.slo,
        ensures self.done(r.0@, r.1), r.2 <= self.shi - self.slo,
        no_unwind
    {
        let nat_ok: &Vec<bool> = &*self.nat_ok;
        let mut flags = flags;
        let mut dense = true;
        let mut cnt: usize = 0;
        let mut b = self.slo;
        while b < self.shi
            invariant
                self.wf(),
                cnt <= b - self.slo,
                *nat_ok == *self.nat_ok,
                self.slo <= b <= self.shi,
                flags@.len() == self.shi - self.slo,
                forall|x: int| self.slo <= x < b ==>
                    #[trigger] flags@[x - self.slo] == supp_in_region(self.snk@, self.nat_keys@, self.nat_ok@, x),
                dense ==> forall|x: int| self.slo <= x < b ==> #[trigger] self.skeys@[x] == self.base + x,
            decreases self.shi - b,
        {
            let ok = supplier_in_region(self.snk, self.ns, self.nat_keys, self.nn, nat_ok, b);
            flags[b - self.slo] = ok;
            if ok {
                cnt = cnt + 1;
            }
            if self.skeys[b] as i128 != self.base as i128 + b as i128 {
                dense = false;
            }
            b = b + 1;
        }
        (flags, dense, cnt)
    }
}

/// One phase-1 task: four lanes of adjacent part row ranges (scanned together on one thread: while every lane has a
/// whole batch left, pass 1 runs on the four at once with `collect_equal4`) and a supplier range.
pub struct ScanTask1 {
    pub p0: PartLane,
    pub p1: PartLane,
    pub p2: PartLane,
    pub p3: PartLane,
    pub pass: PartPass,
    pub supp: SuppScan,
    pub flags: Vec<bool>,
}

/// Output: the keys of each lane; the supplier flags, the dense-key test and the number of flagged suppliers.
pub struct ScanOut1 {
    pub o0: PartLaneOut,
    pub o1: PartLaneOut,
    pub o2: PartLaneOut,
    pub o3: PartLaneOut,
    pub flags: Vec<bool>,
    pub dense: bool,
    pub nflag: usize,
}

impl WorkerTask for ScanTask1 {
    type Output = ScanOut1;

    open spec fn pre(&self) -> bool {
        &&& self.p0.pre() && self.p1.pre() && self.p2.pre() && self.p3.pre()
        &&& same_select(self.p0, self.p1) && same_select(self.p0, self.p2) && same_select(self.p0, self.p3)
        &&& self.pass.wf()
        &&& self.supp.wf()
        &&& self.flags@.len() == self.supp.shi - self.supp.slo
    }

    open spec fn post(&self, r: ScanOut1) -> bool {
        &&& part_lane_post(self.p0, r.o0) && part_lane_post(self.p1, r.o1)
        &&& part_lane_post(self.p2, r.o2) && part_lane_post(self.p3, r.o3)
        &&& self.supp.done(r.flags@, r.dense)
        &&& r.nflag <= self.supp.shi - self.supp.slo
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.p0.scan.lo as u64, self.p3.scan.hi as u64)
    }

    fn run(self) -> (r: ScanOut1) {
        let ghost (g0, g1, g2, g3) = (self.p0, self.p1, self.p2, self.p3);
        let ScanTask1 { p0, p1, p2, p3, pass, supp, flags } = self;
        let mut pass = pass;
        let PartLane { scan: sc0, out: mut o0, batch: mut s0 } = p0;
        let PartLane { scan: sc1, out: mut o1, batch: mut s1 } = p1;
        let PartLane { scan: sc2, out: mut o2, batch: mut s2 } = p2;
        let PartLane { scan: sc3, out: mut o3, batch: mut s3 } = p3;
        // Rows per lane scanned together: the shortest lane, down to whole batches.
        let m = min_usize(min_usize(sc0.hi - sc0.lo, sc1.hi - sc1.lo), min_usize(sc2.hi - sc2.lo, sc3.hi - sc3.lo));
        let len = m - m % BATCH;
        let (mut c0, mut c1, mut c2, mut c3) = (true, true, true, true);
        let mut a: usize = 0;
        while a < len
            invariant
                sc0 == g0.scan, sc1 == g1.scan, sc2 == g2.scan, sc3 == g3.scan,
                sc0.wf(), sc1.wf(), sc2.wf(), sc3.wf(),
                same_select(g0, g1), same_select(g0, g2), same_select(g0, g3),
                len <= sc0.hi - sc0.lo, len <= sc1.hi - sc1.lo, len <= sc2.hi - sc2.lo, len <= sc3.hi - sc3.lo,
                len % BATCH == 0,
                a % BATCH == 0,
                a <= len,
                part_batch_ok(s0@, sc0), part_batch_ok(s1@, sc1), part_batch_ok(s2@, sc2), part_batch_ok(s3@, sc3),
                pass.wf(),
                o0.wf(), o1.wf(), o2.wf(), o3.wf(),
                o0.capacity() == g0.out.capacity(), o1.capacity() == g1.out.capacity(),
                o2.capacity() == g2.out.capacity(), o3.capacity() == g3.out.capacity(),
                c0 ==> sc0.covers(sc0.lo + a, o0.view()) && o0.view().len() <= a,
                c1 ==> sc1.covers(sc1.lo + a, o1.view()) && o1.view().len() <= a,
                c2 ==> sc2.covers(sc2.lo + a, o2.view()) && o2.view().len() <= a,
                c3 ==> sc3.covers(sc3.lo + a, o3.view()) && o3.view().len() <= a,
                g0.out.capacity() >= sc0.hi - sc0.lo ==> c0,
                g1.out.capacity() >= sc1.hi - sc1.lo ==> c1,
                g2.out.capacity() >= sc2.hi - sc2.lo ==> c2,
                g3.out.capacity() >= sc3.hi - sc3.lo ==> c3,
            decreases len - a,
        {
            assert(a + BATCH <= len) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, BATCH as int);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(len as int, BATCH as int);
            }
            assert(BATCH % EQ_BLOCK == 0);
            let (k0, k1, k2, k3) = collect_equal4(sc0.sizes, sc0.n, sc0.lo + a, sc1.lo + a, sc2.lo + a, sc3.lo + a, BATCH,
                sc0.target, &mut s0, &mut s1, &mut s2, &mut s3);
            if c0 {
                let (o, ok) = sc0.batch_passes(o0, &s0, &mut pass, sc0.lo + a, sc0.lo + a + BATCH, k0);
                o0 = o;
                c0 = ok;
            }
            if c1 {
                let (o, ok) = sc1.batch_passes(o1, &s1, &mut pass, sc1.lo + a, sc1.lo + a + BATCH, k1);
                o1 = o;
                c1 = ok;
            }
            if c2 {
                let (o, ok) = sc2.batch_passes(o2, &s2, &mut pass, sc2.lo + a, sc2.lo + a + BATCH, k2);
                o2 = o;
                c2 = ok;
            }
            if c3 {
                let (o, ok) = sc3.batch_passes(o3, &s3, &mut pass, sc3.lo + a, sc3.lo + a + BATCH, k3);
                o3 = o;
                c3 = ok;
            }
            a = a + BATCH;
        }
        if c0 {
            let (o, ok) = sc0.run_from(o0, &mut s0, &mut pass, sc0.lo + a);
            o0 = o;
            c0 = ok;
        }
        if c1 {
            let (o, ok) = sc1.run_from(o1, &mut s1, &mut pass, sc1.lo + a);
            o1 = o;
            c1 = ok;
        }
        if c2 {
            let (o, ok) = sc2.run_from(o2, &mut s2, &mut pass, sc2.lo + a);
            o2 = o;
            c2 = ok;
        }
        if c3 {
            let (o, ok) = sc3.run_from(o3, &mut s3, &mut pass, sc3.lo + a);
            o3 = o;
            c3 = ok;
        }
        let (flags, dense, nflag) = supp.run_scan(flags);
        ScanOut1 {
            o0: PartLaneOut { keys: o0, complete: c0 },
            o1: PartLaneOut { keys: o1, complete: c1 },
            o2: PartLaneOut { keys: o2, complete: c2 },
            o3: PartLaneOut { keys: o3, complete: c3 },
            flags, dense, nflag,
        }
    }
}

} // verus!
