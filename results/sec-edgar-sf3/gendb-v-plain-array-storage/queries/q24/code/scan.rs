//! Phase 3 worker: the kept `num` rows (`spec::keep`: `uom = $1`, `ddate` in range, no `pre` row with the same
//! `(tag, version, adsh)`) of the task's chunks, in row order, one output segment per chunk.
//!
//! Fast mode (the phase-2 sets): a qualifying row probes the set of its key hash pair's partition. Under the foreign
//! keys and the hash separations a stored pair is the pair of a `pre` row with the same key, and every `pre` row's
//! pair is stored in its partition's set, so membership decides `matched` exactly (`lemma_probe`). Exact mode (a
//! phase-2 check failed): compare the key texts with every `pre` row.
use vstd::prelude::*;
use std::sync::Arc;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::TaskBuffer;
use crate::stores::flat_num::interface as ni;
use crate::agent::spec::*;
use crate::agent::txt::*;
use crate::agent::build::{pre_set_ok, set_sound, pre_pair};
use crate::agent::common::partition::*;
use crate::agent::common::pairset::*;
use crate::agent::hash::hash_text;

verus! {

/// The kept rows of `lo..hi` as row numbers.
pub open spec fn kept(c: Ctx, lo: int, hi: int) -> Seq<usize> {
    as_rows(keep_range(c, lo, hi))
}

/// Row numbers as `usize`.
pub open spec fn as_rows(s: Seq<int>) -> Seq<usize> {
    s.map_values(|i: int| i as usize)
}

/// The phase-2 sets decide `matched` exactly: one complete and sound set per partition, the foreign keys, and the
/// two hash separations.
pub open spec fn fast_ok(c: Ctx, sets: Seq<PairSet>) -> bool {
    &&& sets.len() == PARTS
    &&& forall|p: int| #![trigger sets[p]] 0 <= p < PARTS ==> pre_set_ok(sets[p], c, p)
    &&& fk_ok(c)
    &&& tv_injective(c)
    &&& ad_injective(c)
}

/// The membership answer of a qualifying row's probe is `matched`.
pub proof fn lemma_probe(c: Ctx, sets: Seq<PairSet>, i: int, found: bool)
    requires
        ctx_ok(c), fast_ok(c, sets), 0 <= i < c.n,
        found == has(sets[part_of(num_ad(c, i))], num_tv(c, i), num_ad(c, i)),
    ensures found == matched(c, i),
{
    let p = part_of(num_ad(c, i));
    assert(0 <= p < PARTS) by {
        let k = num_ad(c, i);
        assert((k >> 56u64) < 256u64) by (bit_vector);
    }
    assert(pre_set_ok(sets[p], c, p));
    if found {
        assert(pre_pair(c, num_tv(c, i), num_ad(c, i)));
        let j = choose|j: int| 0 <= j < c.m && #[trigger] pre_tv(c, j) == num_tv(c, i) && pre_ad(c, j) == num_ad(c, i);
        lemma_pair_eq_key(c, i, j);
        assert(same_key(c, i, j));
    }
    if matched(c, i) {
        let j = choose|j: int| 0 <= j < c.m && #[trigger] same_key(c, i, j);
        assert(pre_tv(c, j) == num_tv(c, i) && pre_ad(c, j) == num_ad(c, i));
        assert(has(sets[p], pre_tv(c, j), pre_ad(c, j)));
    }
}

// ------------------------------------------------------------------------------------------------ chunks

/// Rows per chunk. The `num` rows are cut into chunks `g` of rows `chunk_lo(g) .. chunk_hi(g)`; the chunks are dealt
/// to the tasks round-robin (`rr`), so rows that cluster by date spread over every task.
pub const CHUNK: usize = 0x4000;

/// The first row of chunk `g` (`n` when the chunk is past the end).
pub open spec fn chunk_lo(g: int, n: int) -> int {
    if g * CHUNK < n { g * CHUNK } else { n }
}

/// The end of chunk `g`.
pub open spec fn chunk_hi(g: int, n: int) -> int {
    chunk_lo(g + 1, n)
}

/// The kept rows of chunk `g`.
pub open spec fn chunk_kept(c: Ctx, g: int) -> Seq<usize> {
    kept(c, chunk_lo(g, c.n), chunk_hi(g, c.n))
}

/// The start of segment `j` of a task's output (segment `j` holds the kept rows of the task's chunk `j`).
pub open spec fn seg_start(ends: Seq<usize>, j: int) -> int {
    if j == 0 { 0 } else { ends[j - 1] as int }
}

/// Segments `0..nj` of `rows` (bounded by `ends`) hold the kept rows of the chunks `gs[0..nj]`.
pub open spec fn segs_hold(c: Ctx, rows: Seq<usize>, ends: Seq<usize>, gs: Seq<usize>, nj: int) -> bool {
    &&& nj <= ends.len() && nj <= gs.len()
    &&& forall|j: int| 0 <= j < nj ==> #[trigger] seg_ok(c, rows, ends, gs, j)
}

pub open spec fn seg_ok(c: Ctx, rows: Seq<usize>, ends: Seq<usize>, gs: Seq<usize>, j: int) -> bool {
    &&& 0 <= seg_start(ends, j) <= ends[j] <= rows.len()
    &&& rows.subrange(seg_start(ends, j), ends[j] as int) == chunk_kept(c, gs[j] as int)
}

/// The chunk ids of a task increase and are below `nch`, the number of chunks (`nch * CHUNK <= n + CHUNK`).
pub open spec fn chunks_ok(gs: Seq<usize>, nch: int, n: int) -> bool {
    &&& nch * CHUNK <= n + CHUNK
    &&& forall|j: int| 0 <= j < gs.len() ==> #[trigger] gs[j] < nch
    &&& forall|j: int| 0 < j < gs.len() ==> #[trigger] gs[j - 1] < gs[j]
}

/// The round-robin deal of chunk `g` over `w` tasks: (task, position in the task's list).
pub open spec fn rr(g: nat, w: int) -> (int, int)
    decreases g,
{
    if g == 0 {
        (0, 0)
    } else {
        let p = rr((g - 1) as nat, w);
        if p.0 + 1 >= w { (0, p.1 + 1) } else { (p.0 + 1, p.1) }
    }
}

pub struct ScanTask {
    pub c: Ghost<Ctx>,
    pub gs: Vec<usize>,
    pub nch: usize,
    pub n: usize,
    pub ntag: TextCol,
    pub nver: TextCol,
    pub nadsh: TextCol,
    pub nuom: TextCol,
    pub ddate: &'static [i32],
    pub pv: &'static [u8],
    pub plen: usize,
    pub dlo: i64,
    pub dhi: i64,
    pub sets: Option<Arc<Vec<PairSet>>>,
    pub ptag: TextCol,
    pub pver: TextCol,
    pub padsh: TextCol,
    pub m: usize,
    pub out: TaskBuffer<usize>,
    pub ends: Vec<usize>,
    pub bk: Vec<u64>,
    pub bx: Vec<u64>,
    pub brow: Vec<usize>,
    pub bh: Vec<u64>,
}

pub open spec fn scan_pre(t: ScanTask) -> bool {
    let c = t.c@;
    &&& ctx_ok(c)
    &&& t.n as int == c.n
    &&& chunks_ok(t.gs@, t.nch as int, c.n)
    &&& t.ends@.len() == t.gs@.len()
    &&& t.ntag@ == ntag_v(c) && t.nver@ == nver_v(c) && t.nadsh@ == nadsh_v(c) && t.nuom@ == nuom_v(c)
    &&& t.ptag@ == ptag_v(c) && t.pver@ == pver_v(c) && t.padsh@ == padsh_v(c)
    &&& t.ddate@ == ni::i32s(c.np[ni::DDATE as int])
    &&& t.pv@ == c.pv && t.plen == t.pv@.len()
    &&& t.dlo as int == c.dlo && t.dhi as int == c.dhi
    &&& t.m as int == c.m
    &&& t.out.wf() && t.out.view() == Seq::<usize>::empty()
    &&& (t.sets matches Some(s) ==> fast_ok(c, s@))
    &&& t.bk@.len() == BATCH && t.bx@.len() == BATCH && t.brow@.len() == BATCH && t.bh@.len() == BATCH
}

/// The kept rows of a scan task's chunks, one segment per chunk, or `full`: its buffer filled up.
pub struct ScanOut {
    pub rows: TaskBuffer<usize>,
    pub ends: Vec<usize>,
    pub full: bool,
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        scan_pre(*self)
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        &&& out.rows.wf()
        &&& !out.full ==> segs_hold(self.c@, out.rows.view(), out.ends@, self.gs@, self.gs@.len() as int)
        &&& self.out.capacity() >= self.n ==> !out.full
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.nch as u64, self.n as u64)
    }

    #[verifier::spinoff_prover]
    fn run(self) -> (out: ScanOut) {
        let ghost me = self;
        let ScanTask { c, gs, nch, n, ntag, nver, nadsh, nuom, ddate, pv, plen, dlo, dhi, sets, ptag, pver, padsh, m,
            out, ends, bk, bx, brow, bh } = self;
        let ghost cc = c@;
        let k = ScanCols { ntag, nver, nadsh, nuom, ddate, pv, plen, dlo, dhi, ptag, pver, padsh, m };
        proof {
            lemma_scan_ready(me);
            assert(k == scan_cols_of(me));
        }
        scan_chunks(&k, &sets, &gs, nch, n, out, ends, bk, bx, brow, bh, Ghost(cc))
    }
}

/// The rows of the chunks `gs`, chunk after chunk; `ends[j]` is the output length after chunk `j`.
#[verifier::spinoff_prover]
fn scan_chunks(k: &ScanCols, sets: &Option<Arc<Vec<PairSet>>>, gs: &Vec<usize>, nch: usize, n: usize,
    out: TaskBuffer<usize>, ends: Vec<usize>, bk: Vec<u64>, bx: Vec<u64>, brow: Vec<usize>, bh: Vec<u64>,
    Ghost(cc): Ghost<Ctx>) -> (r: ScanOut)
    requires
        ctx_ok(cc), n as int == cc.n, scan_cols_ok(*k, cc), chunks_ok(gs@, nch as int, cc.n),
        sets matches Some(s) ==> fast_ok(cc, s@),
        out.wf(), out.view() == Seq::<usize>::empty(), ends@.len() == gs@.len(),
        bk@.len() == BATCH, bx@.len() == BATCH, brow@.len() == BATCH, bh@.len() == BATCH,
    ensures
        r.rows.wf(),
        !r.full ==> segs_hold(cc, r.rows.view(), r.ends@, gs@, gs@.len() as int),
        out.capacity() >= n ==> !r.full,
    no_unwind
{
    hide(kept);
    hide(chunk_kept);
    let mut out = out;
    let mut ends = ends;
    let mut bk = bk;
    let mut bx = bx;
    let mut brow = brow;
    let mut bh = bh;
    let ghost cap0 = out.capacity();
    let len = gs.len();
    let mut full = false;
    let mut j: usize = 0;
    while j < len && !full
        invariant
            j <= len, len == gs@.len(), ends@.len() == len, ctx_ok(cc), n as int == cc.n, scan_cols_ok(*k, cc),
            chunks_ok(gs@, nch as int, cc.n),
            sets matches Some(s) ==> fast_ok(cc, s@),
            out.wf(), out.capacity() == cap0,
            bk@.len() == BATCH, bx@.len() == BATCH, brow@.len() == BATCH, bh@.len() == BATCH,
            full ==> cap0 < n,
            !full ==> segs_hold(cc, out.view(), ends@, gs@, j as int),
            !full && j > 0 ==> out.view().len() <= chunk_hi(gs@[j - 1] as int, cc.n),
            !full && j > 0 ==> ends@[j - 1] == out.view().len(),
            !full && j == 0 ==> out.view().len() == 0,
        decreases len - j + (if full { 0int } else { 1int }),
    {
        let g = gs[j];
        proof {
            assert(g < nch);
            if j > 0 {
                assert(gs@[j - 1] < gs@[j as int]);
            }
        }
        let (lo, hi) = chunk_bounds(g, n);
        proof {
            if j > 0 {
                lemma_chunk_order(gs@[j - 1] as int, g as int, cc.n);
            }
        }
        let ghost before = out.view();
        let ghost ends0 = ends@;
        let f = match sets {
            Some(s) => scan_range_fast(k, &**s, lo, hi, &mut out, &mut bk, &mut bx, &mut brow, &mut bh, Ghost(cc)),
            None => scan_range_exact(k, lo, hi, &mut out, Ghost(cc)),
        };
        if f {
            full = true;
        } else {
            let e = out.len();
            ends[j] = e;
            proof {
                lemma_seg_step(cc, before, out.view(), ends0, ends@, gs@, j as int, lo as int, hi as int, e);
                lemma_kept_len(cc, lo as int, hi as int);
            }
            j = j + 1;
        }
    }
    ScanOut { rows: out, ends, full }
}

/// `kept(c, lo, hi)` has at most `hi - lo` rows.
proof fn lemma_kept_len(c: Ctx, lo: int, hi: int)
    requires lo <= hi,
    ensures kept(c, lo, hi).len() <= hi - lo,
{
    lemma_keep_range_len(c, lo, hi);
}

/// The rows `lo..hi` of chunk `g`.
fn chunk_bounds(g: usize, n: usize) -> (r: (usize, usize))
    ensures r.0 as int == chunk_lo(g as int, n as int), r.1 as int == chunk_hi(g as int, n as int), r.0 <= r.1 <= n,
    no_unwind
{
    proof {
        lemma_chunk_bounds(g as int, n as int, CHUNK as int);
    }
    let lo = if g <= n / CHUNK { g * CHUNK } else { n };
    let hi = if g < n / CHUNK { g * CHUNK + CHUNK } else { n };
    (lo, hi)
}

/// An earlier chunk ends before a later one starts.
proof fn lemma_chunk_order(g1: int, g2: int, n: int)
    requires 0 <= g1 < g2, 0 <= n,
    ensures chunk_hi(g1, n) <= chunk_lo(g2, n),
{
    assert((g1 + 1) * CHUNK <= g2 * CHUNK) by (nonlinear_arith) requires g1 + 1 <= g2;
}

/// The chunk bounds without overflow: below `n / CHUNK` a chunk is whole, past it the chunk starts at `n`.
proof fn lemma_chunk_bounds(g: int, n: int, k: int)
    requires 0 <= g, 0 <= n, k == CHUNK as int,
    ensures
        (n / k) * k <= n < (n / k + 1) * k,
        g <= n / k ==> g * k <= n,
        g > n / k ==> g * k > n,
        g < n / k ==> (g + 1) * k <= n,
        g >= n / k ==> (g + 1) * k > n,
{
    let d = n / (CHUNK as int);
    assert(d * k <= n < (d + 1) * k) by (nonlinear_arith) requires d == n / k, 0 <= n, k == 0x4000;
    if g <= d {
        assert(g * k <= d * k) by (nonlinear_arith) requires g <= d, 0 <= g, 0 < k;
    } else {
        assert(g * k >= (d + 1) * k) by (nonlinear_arith) requires g >= d + 1, 0 < k;
    }
    if g < d {
        assert((g + 1) * k <= d * k) by (nonlinear_arith) requires g + 1 <= d, 0 <= g, 0 < k;
    } else {
        assert((g + 1) * k >= (d + 1) * k) by (nonlinear_arith) requires g >= d, 0 < k;
    }
}

/// Appending chunk `j`'s kept rows keeps segments `0..j` and adds segment `j`.
proof fn lemma_seg_step(c: Ctx, before: Seq<usize>, after: Seq<usize>, ends0: Seq<usize>, ends: Seq<usize>,
    gs: Seq<usize>, j: int, lo: int, hi: int, e: usize)
    requires
        0 <= j < ends0.len(), j < gs.len(), segs_hold(c, before, ends0, gs, j),
        lo == chunk_lo(gs[j] as int, c.n), hi == chunk_hi(gs[j] as int, c.n),
        after == before + kept(c, lo, hi),
        e as int == after.len(), ends == ends0.update(j, e),
        j > 0 ==> ends0[j - 1] == before.len(),
        j == 0 ==> before.len() == 0,
    ensures segs_hold(c, after, ends, gs, j + 1),
{
    assert(ends.len() == ends0.len());
    assert forall|j2: int| 0 <= j2 < j implies #[trigger] seg_ok(c, after, ends, gs, j2) by {
        assert(seg_ok(c, before, ends0, gs, j2));
        assert(ends[j2] == ends0[j2]);
        if j2 > 0 {
            assert(ends[j2 - 1] == ends0[j2 - 1]);
        }
        assert(seg_start(ends, j2) == seg_start(ends0, j2));
        assert(after.subrange(seg_start(ends, j2), ends[j2] as int)
            =~= before.subrange(seg_start(ends0, j2), ends0[j2] as int));
    }
    assert(seg_ok(c, after, ends, gs, j)) by {
        if j > 0 {
            assert(ends[j - 1] == ends0[j - 1]);
        }
        assert(seg_start(ends, j) == before.len());
        assert(ends[j] as int == after.len());
        assert(after.subrange(before.len() as int, after.len() as int) =~= kept(c, lo, hi));
        assert(chunk_kept(c, gs[j] as int) == kept(c, lo, hi));
    }
    assert forall|j2: int| 0 <= j2 < j + 1 implies #[trigger] seg_ok(c, after, ends, gs, j2) by {
        if j2 < j {
            assert(seg_ok(c, after, ends, gs, j2));
        }
    }
}

/// Fast mode, rows `lo..hi`: append their kept rows to `out`. The rows are taken in batches of up to `BATCH`
/// qualifying rows; a batch first computes the key hash pairs of its qualifying rows and reads their bucket slots
/// (independent loads, so the cache misses overlap), then probes them one after the other.
#[verifier::spinoff_prover]
fn scan_range_fast(k: &ScanCols, sv: &Vec<PairSet>, lo: usize, hi: usize, out: &mut TaskBuffer<usize>,
    bk: &mut Vec<u64>, bx: &mut Vec<u64>, brow: &mut Vec<usize>, bh: &mut Vec<u64>, Ghost(cc): Ghost<Ctx>)
    -> (full: bool)
    requires
        ctx_ok(cc), lo <= hi <= cc.n, scan_cols_ok(*k, cc), fast_ok(cc, sv@), old(out).wf(),
        old(bk)@.len() == BATCH, old(bx)@.len() == BATCH, old(brow)@.len() == BATCH, old(bh)@.len() == BATCH,
    ensures
        final(out).wf(), final(out).capacity() == old(out).capacity(),
        final(bk)@.len() == BATCH, final(bx)@.len() == BATCH, final(brow)@.len() == BATCH, final(bh)@.len() == BATCH,
        !full ==> final(out).view() == old(out).view() + kept(cc, lo as int, hi as int),
        old(out).view().len() + (hi - lo) <= old(out).capacity() ==> !full,
    no_unwind
{
    proof {
        reveal(scan_cols_ok);
        assert(kept(cc, lo as int, lo as int) =~= Seq::<usize>::empty());
        assert(old(out).view() + kept(cc, lo as int, lo as int) =~= old(out).view());
    }
    let ghost v0 = out.view();
    let ghost cap0 = out.capacity();
    let cap = out.slots();
    let mut full = false;
    let mut i = lo;
    while i < hi && !full
        invariant
            lo <= i <= hi <= cc.n, ctx_ok(cc), scan_cols_ok(*k, cc), fast_ok(cc, sv@),
            bk@.len() == BATCH, bx@.len() == BATCH, brow@.len() == BATCH, bh@.len() == BATCH,
            out.wf(), out.capacity() == cap0, cap == cap0,
            full ==> v0.len() + (hi - lo) > cap0,
            !full ==> out.view() == v0 + kept(cc, lo as int, i as int),
            !full ==> out.view().len() <= v0.len() + (i - lo),
        decreases hi - i + (if full { 0int } else { 1int }),
    {
        // Batch: the qualifying rows of `i0..i` (at most `BATCH`) with their key hash pairs.
        let i0 = i;
        let mut nq: usize = 0;
        while i < hi && nq < BATCH
            invariant
                lo <= i0 <= i <= hi <= cc.n, ctx_ok(cc), scan_cols_ok(*k, cc), nq <= BATCH,
                bk@.len() == BATCH, bx@.len() == BATCH, brow@.len() == BATCH,
                batch_ok(cc, qual_range(cc, i0 as int, i as int), nq as int, bk@, bx@, brow@),
            decreases hi - i,
        {
            let ghost (bk0, bx0, brow0) = (bk@, bx@, brow@);
            if row_qualifies_k(k, i, Ghost(cc)) {
                let (tv, ad) = pair_at_k(k, i, Ghost(cc));
                bk[nq] = tv;
                bx[nq] = ad;
                brow[nq] = i;
                proof {
                    lemma_batch_push(cc, i0 as int, i as int, nq as int, bk0, bx0, brow0, bk@, bx@, brow@);
                }
                nq = nq + 1;
            } else {
                proof {
                    lemma_batch_skip(cc, i0 as int, i as int, nq as int, bk@, bx@, brow@);
                }
            }
            i = i + 1;
        }
        let ghost qs = qual_range(cc, i0 as int, i as int);
        proof {
            lemma_qual_range_len(cc, i0 as int, i as int);
            lemma_batch_start(cc, lo as int, i0 as int, qs);
        }
        // Read the bucket slot of every batch pair (independent loads: their cache misses overlap).
        let mut q: usize = 0;
        while q < nq
            invariant
                q <= nq <= BATCH, fast_ok(cc, sv@),
                bk@.len() == BATCH, bx@.len() == BATCH, bh@.len() == BATCH,
                forall|q2: int| 0 <= q2 < q ==> #[trigger] hinted(sv@, bk@[q2], bx@[q2], bh@[q2]),
            decreases nq - q,
        {
            let tv = bk[q];
            let p = part_exec(bx[q]);
            proof {
                assert(pre_set_ok(sv@[p as int], cc, p as int));
            }
            let w = bucket_key(&sv[p], tv, bx[q]);
            let ghost bh0 = bh@;
            bh[q] = w;
            proof {
                assert forall|q2: int| 0 <= q2 < q + 1 implies #[trigger] hinted(sv@, bk@[q2], bx@[q2], bh@[q2]) by {
                    if q2 < q {
                        assert(hinted(sv@, bk@[q2], bx@[q2], bh0[q2]));
                    }
                }
            }
            q = q + 1;
        }
        // Probe the batch.
        let mut q: usize = 0;
        while q < nq && !full
            invariant
                lo <= i0 <= i <= hi <= cc.n, ctx_ok(cc), fast_ok(cc, sv@), nq <= BATCH, q <= nq,
                bk@.len() == BATCH, bx@.len() == BATCH, brow@.len() == BATCH, bh@.len() == BATCH,
                forall|q2: int| 0 <= q2 < nq ==> #[trigger] hinted(sv@, bk@[q2], bx@[q2], bh@[q2]),
                batch_ok(cc, qs, nq as int, bk@, bx@, brow@), nq as int <= i - i0,
                out.wf(), out.capacity() == cap0, cap == cap0,
                full ==> v0.len() + (hi - lo) > cap0,
                !full ==> out.view() == v0 + batch_out(cc, lo as int, i0 as int, qs, q as int),
                !full ==> out.view().len() <= v0.len() + (i0 - lo) + q,
            decreases nq - q + (if full { 0int } else { 1int }),
        {
            let tv = bk[q];
            let ad = bx[q];
            let row = brow[q];
            proof {
                lemma_batch_at(cc, qs, nq as int, bk@, bx@, brow@, q as int);
            }
            let p = part_exec(ad);
            proof {
                assert(pre_set_ok(sv@[p as int], cc, p as int));
                assert(hinted(sv@, bk@[q as int], bx@[q as int], bh@[q as int]));
                lemma_tv_nonzero(cc, row as int);
            }
            let found = lookup_hinted(&sv[p], tv, ad, bh[q]);
            proof {
                lemma_probe(cc, sv@, row as int, found);
                lemma_unmatched_take(cc, qs, q as int);
            }
            if !found && out.len() >= cap {
                full = true;
            } else {
                let ghost ov = out.view();
                if !found {
                    out.push(row);
                }
                proof {
                    lemma_batch_out_step(cc, lo as int, i0 as int, qs, q as int);
                    if !found {
                        assert(v0 + batch_out(cc, lo as int, i0 as int, qs, q + 1)
                            =~= (v0 + batch_out(cc, lo as int, i0 as int, qs, q as int)).push(row));
                    }
                }
                q = q + 1;
            }
        }
        proof {
            if !full {
                lemma_batch_done(cc, lo as int, i0 as int, i as int, qs, nq as int);
            }
        }
    }
    full
}

/// Exact mode (a phase-2 check failed), rows `lo..hi`: append their kept rows to `out`, deciding every row by
/// comparing key texts with every `pre` row.
#[verifier::spinoff_prover]
fn scan_range_exact(k: &ScanCols, lo: usize, hi: usize, out: &mut TaskBuffer<usize>, Ghost(cc): Ghost<Ctx>)
    -> (full: bool)
    requires ctx_ok(cc), lo <= hi <= cc.n, scan_cols_ok(*k, cc), old(out).wf(),
    ensures
        final(out).wf(), final(out).capacity() == old(out).capacity(),
        !full ==> final(out).view() == old(out).view() + kept(cc, lo as int, hi as int),
        old(out).view().len() + (hi - lo) <= old(out).capacity() ==> !full,
    no_unwind
{
    proof {
        assert(kept(cc, lo as int, lo as int) =~= Seq::<usize>::empty());
        assert(old(out).view() + kept(cc, lo as int, lo as int) =~= old(out).view());
    }
    let ghost v0 = out.view();
    let ghost cap0 = out.capacity();
    let cap = out.slots();
    let mut full = false;
    let mut i = lo;
    while i < hi && !full
        invariant
            lo <= i <= hi <= cc.n, ctx_ok(cc),
            scan_cols_ok(*k, cc),
            out.wf(), out.capacity() == cap0, cap == cap0,
            full ==> v0.len() + (hi - lo) > cap0,
            !full ==> out.view() == v0 + kept(cc, lo as int, i as int),
            !full ==> out.view().len() <= v0.len() + (i - lo),
        decreases hi - i + (if full { 0int } else { 1int }),
    {
        let keep_row = decide(k, i, Ghost(cc));
        proof {
            lemma_keep_range_len(cc, lo as int, i as int);
        }
        if keep_row && out.len() >= cap {
            full = true;
        } else {
            if keep_row {
                out.push(i);
            }
            proof {
                assert(kept(cc, lo as int, i + 1) =~= if keep(cc, i as int) {
                    kept(cc, lo as int, i as int).push(i)
                } else {
                    kept(cc, lo as int, i as int)
                });
                assert(v0 + kept(cc, lo as int, i + 1) =~= if keep(cc, i as int) {
                    (v0 + kept(cc, lo as int, i as int)).push(i)
                } else {
                    v0 + kept(cc, lo as int, i as int)
                });
            }
            i = i + 1;
        }
    }
    full
}

// ------------------------------------------------------------------------------------------------ batches

/// Qualifying rows per probe batch.
pub const BATCH: usize = 32;

/// The qualifying rows of `lo..hi`, in row order.
pub open spec fn qual_range(c: Ctx, lo: int, hi: int) -> Seq<int>
    decreases hi - lo,
{
    if hi <= lo {
        Seq::empty()
    } else if qual(c, hi - 1) {
        qual_range(c, lo, hi - 1).push(hi - 1)
    } else {
        qual_range(c, lo, hi - 1)
    }
}

/// The rows of `qs` without a `pre` partner, in order.
pub open spec fn unmatched(c: Ctx, qs: Seq<int>) -> Seq<int>
    decreases qs.len(),
{
    if qs.len() == 0 {
        Seq::empty()
    } else if matched(c, qs.last()) {
        unmatched(c, qs.drop_last())
    } else {
        unmatched(c, qs.drop_last()).push(qs.last())
    }
}

/// `w` is the key in the bucket slot of `(k, x)` in the set of `x`'s partition.
pub open spec fn hinted(sets: Seq<PairSet>, k: u64, x: u64, w: u64) -> bool {
    w == key_at(sets[part_of(x)], bucket(k, x, sets[part_of(x)].mask))
}

/// A `num` row's `tv_hash` is not 0.
proof fn lemma_tv_nonzero(c: Ctx, i: int)
    ensures num_tv(c, i) != 0,
{
    crate::agent::build::lemma_or_one_nonzero(hash_text(nver(c, i), hash_text(ntag(c, i), crate::agent::hash::SEED_TAG)));
}

/// `(k, x)` is the key hash pair of `num` row `r` (opaque: the hashes are not unfolded in batch proofs).
#[verifier::opaque]
pub open spec fn row_pair(c: Ctx, r: int, k: u64, x: u64) -> bool {
    k == num_tv(c, r) && x == num_ad(c, r)
}

/// Batch slot `q` holds row `qs[q]` and its key hash pair.
pub open spec fn slot_ok(c: Ctx, qs: Seq<int>, bk: Seq<u64>, bx: Seq<u64>, brow: Seq<usize>, q: int) -> bool {
    brow[q] as int == qs[q] && row_pair(c, qs[q], bk[q], bx[q]) && 0 <= qs[q] < c.n
}

/// Batch slot `q < nq` holds qualifying row `qs[q]` and its key hash pair; `qs` has `nq` rows.
pub open spec fn batch_ok(c: Ctx, qs: Seq<int>, nq: int, bk: Seq<u64>, bx: Seq<u64>, brow: Seq<usize>) -> bool {
    &&& qs.len() == nq
    &&& forall|q: int| 0 <= q < nq ==> #[trigger] slot_ok(c, qs, bk, bx, brow, q)
}

/// The kept rows before the batch, then the unmatched rows of the first `q` batch rows.
pub open spec fn batch_out(c: Ctx, lo: int, i0: int, qs: Seq<int>, q: int) -> Seq<usize> {
    as_rows(keep_range(c, lo, i0) + unmatched(c, qs.take(q)))
}

/// Row `i` qualifies: it becomes batch slot `nq`.
proof fn lemma_batch_push(c: Ctx, i0: int, i: int, nq: int, bk0: Seq<u64>, bx0: Seq<u64>, brow0: Seq<usize>,
    bk: Seq<u64>, bx: Seq<u64>, brow: Seq<usize>)
    requires
        0 <= i0 <= i < c.n, i <= usize::MAX, qual(c, i), 0 <= nq < bk0.len(), nq < bx0.len(), nq < brow0.len(),
        batch_ok(c, qual_range(c, i0, i), nq, bk0, bx0, brow0),
        bk == bk0.update(nq, num_tv(c, i)), bx == bx0.update(nq, num_ad(c, i)), brow == brow0.update(nq, i as usize),
    ensures batch_ok(c, qual_range(c, i0, i + 1), nq + 1, bk, bx, brow),
{
    let qs = qual_range(c, i0, i);
    let qs2 = qual_range(c, i0, i + 1);
    assert(qs2 == qs.push(i));
    assert(row_pair(c, i, bk[nq], bx[nq])) by {
        reveal(row_pair);
    }
    assert forall|q: int| 0 <= q < nq + 1 implies #[trigger] slot_ok(c, qs2, bk, bx, brow, q) by {
        if q < nq {
            assert(slot_ok(c, qs, bk0, bx0, brow0, q));
            assert(brow[q] == brow0[q] && bk[q] == bk0[q] && bx[q] == bx0[q]);
            assert(qs2[q] == qs[q]);
        } else {
            assert(qs2[q] == i);
        }
    }
}

/// Row `i` does not qualify: the batch is unchanged.
proof fn lemma_batch_skip(c: Ctx, i0: int, i: int, nq: int, bk: Seq<u64>, bx: Seq<u64>, brow: Seq<usize>)
    requires i0 <= i, !qual(c, i), batch_ok(c, qual_range(c, i0, i), nq, bk, bx, brow),
    ensures batch_ok(c, qual_range(c, i0, i + 1), nq, bk, bx, brow),
{
    assert(qual_range(c, i0, i + 1) == qual_range(c, i0, i));
}

/// Before the probes: the kept rows before the batch.
proof fn lemma_batch_start(c: Ctx, lo: int, i0: int, qs: Seq<int>)
    ensures batch_out(c, lo, i0, qs, 0) == kept(c, lo, i0),
{
    assert(qs.take(0) =~= Seq::<int>::empty());
    assert(unmatched(c, qs.take(0)) =~= Seq::<int>::empty());
    assert(keep_range(c, lo, i0) + unmatched(c, qs.take(0)) =~= keep_range(c, lo, i0));
    assert(batch_out(c, lo, i0, qs, 0) =~= kept(c, lo, i0));
}

proof fn lemma_batch_at(c: Ctx, qs: Seq<int>, nq: int, bk: Seq<u64>, bx: Seq<u64>, brow: Seq<usize>, q: int)
    requires batch_ok(c, qs, nq, bk, bx, brow), 0 <= q < nq,
    ensures brow[q] as int == qs[q], bk[q] == num_tv(c, qs[q]), bx[q] == num_ad(c, qs[q]), 0 <= qs[q] < c.n,
{
    assert(slot_ok(c, qs, bk, bx, brow, q));
    reveal(row_pair);
}

/// `qual_range(c, lo, hi)` has at most `hi - lo` rows.
pub proof fn lemma_qual_range_len(c: Ctx, lo: int, hi: int)
    requires lo <= hi,
    ensures qual_range(c, lo, hi).len() <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_qual_range_len(c, lo, hi - 1);
    }
}

/// `unmatched` of the first `q + 1` rows: that of the first `q`, then row `qs[q]` when it has no partner; it has
/// at most `q` rows.
proof fn lemma_unmatched_take(c: Ctx, qs: Seq<int>, q: int)
    requires 0 <= q < qs.len(),
    ensures
        unmatched(c, qs.take(q + 1)) == if matched(c, qs[q]) { unmatched(c, qs.take(q)) } else {
            unmatched(c, qs.take(q)).push(qs[q])
        },
        unmatched(c, qs.take(q)).len() <= q,
{
    assert(qs.take(q + 1).drop_last() =~= qs.take(q));
    assert(qs.take(q + 1).last() == qs[q]);
    lemma_unmatched_len(c, qs.take(q));
}

proof fn lemma_unmatched_len(c: Ctx, qs: Seq<int>)
    ensures unmatched(c, qs).len() <= qs.len(),
    decreases qs.len(),
{
    if qs.len() > 0 {
        lemma_unmatched_len(c, qs.drop_last());
    }
}

proof fn lemma_batch_out_step(c: Ctx, lo: int, i0: int, qs: Seq<int>, q: int)
    requires 0 <= q < qs.len(),
    ensures
        batch_out(c, lo, i0, qs, q + 1) == if matched(c, qs[q]) { batch_out(c, lo, i0, qs, q) } else {
            batch_out(c, lo, i0, qs, q).push(qs[q] as usize)
        },
{
    lemma_unmatched_take(c, qs, q);
    let a = keep_range(c, lo, i0);
    let u = unmatched(c, qs.take(q));
    if !matched(c, qs[q]) {
        assert(as_rows(a + u.push(qs[q])) =~= as_rows(a + u).push(qs[q] as usize));
    }
}

/// `keep_range` is `unmatched` of `qual_range`.
pub proof fn lemma_keep_qual(c: Ctx, lo: int, hi: int)
    requires lo <= hi,
    ensures keep_range(c, lo, hi) == unmatched(c, qual_range(c, lo, hi)),
    decreases hi - lo,
{
    if hi > lo {
        lemma_keep_qual(c, lo, hi - 1);
        let prev = qual_range(c, lo, hi - 1);
        if qual(c, hi - 1) {
            assert(prev.push(hi - 1).drop_last() =~= prev);
        }
    } else {
        assert(keep_range(c, lo, hi) =~= Seq::<int>::empty());
        assert(qual_range(c, lo, hi) =~= Seq::<int>::empty());
    }
}

/// After the whole batch: the kept rows of `lo..i`.
proof fn lemma_batch_done(c: Ctx, lo: int, i0: int, i: int, qs: Seq<int>, nq: int)
    requires lo <= i0 <= i, qs == qual_range(c, i0, i), qs.len() == nq,
    ensures batch_out(c, lo, i0, qs, nq) == kept(c, lo, i), kept(c, lo, i).len() <= i - lo,
{
    lemma_keep_qual(c, i0, i);
    lemma_keep_range_split(c, lo, i0, i);
    lemma_keep_range_len(c, lo, i);
    assert(qs.take(nq) =~= qs);
    assert(batch_out(c, lo, i0, qs, nq) =~= kept(c, lo, i));
}

/// The columns and binding a scan reads.
pub struct ScanCols {
    pub ntag: TextCol,
    pub nver: TextCol,
    pub nadsh: TextCol,
    pub nuom: TextCol,
    pub ddate: &'static [i32],
    pub pv: &'static [u8],
    pub plen: usize,
    pub dlo: i64,
    pub dhi: i64,
    pub ptag: TextCol,
    pub pver: TextCol,
    pub padsh: TextCol,
    pub m: usize,
}

#[verifier::opaque]
pub open spec fn scan_cols_ok(k: ScanCols, c: Ctx) -> bool {
    &&& k.ntag@ == ntag_v(c) && k.nver@ == nver_v(c) && k.nadsh@ == nadsh_v(c) && k.nuom@ == nuom_v(c)
    &&& k.ptag@ == ptag_v(c) && k.pver@ == pver_v(c) && k.padsh@ == padsh_v(c)
    &&& text_wf(k.ntag@, c.n) && text_wf(k.nver@, c.n) && text_wf(k.nadsh@, c.n) && text_wf(k.nuom@, c.n)
    &&& text_wf(k.ptag@, c.m) && text_wf(k.pver@, c.m) && text_wf(k.padsh@, c.m)
    &&& k.ddate@ == ni::i32s(c.np[ni::DDATE as int]) && k.ddate@.len() == c.n
    &&& k.pv@ == c.pv && k.plen == k.pv@.len() && k.dlo as int == c.dlo && k.dhi as int == c.dhi
    &&& k.m as int == c.m
}

pub open spec fn scan_cols_of(t: ScanTask) -> ScanCols {
    ScanCols { ntag: t.ntag, nver: t.nver, nadsh: t.nadsh, nuom: t.nuom, ddate: t.ddate, pv: t.pv, plen: t.plen,
        dlo: t.dlo, dhi: t.dhi, ptag: t.ptag, pver: t.pver, padsh: t.padsh, m: t.m }
}

pub proof fn lemma_scan_ready(t: ScanTask)
    requires scan_pre(t),
    ensures
        scan_cols_ok(scan_cols_of(t), t.c@),
        ctx_ok(t.c@),
        t.sets matches Some(s) ==> fast_ok(t.c@, s@),
        t.out.wf(), t.out.view() == Seq::<usize>::empty(),
{
    reveal(scan_cols_ok);
    lemma_text_cols_wf(t.c@);
}

/// `keep(c, i)` for one row, by comparing key texts with every `pre` row (exact mode).
#[verifier::spinoff_prover]
fn decide(k: &ScanCols, i: usize, Ghost(c): Ghost<Ctx>) -> (r: bool)
    requires ctx_ok(c), (i as int) < c.n, scan_cols_ok(*k, c),
    ensures r == keep(c, i as int),
    no_unwind
{
    proof {
        reveal(scan_cols_ok);
    }
    let q = row_qualifies(&k.nuom, k.ddate, k.pv, k.plen, k.dlo, k.dhi, i, Ghost(c));
    if !q {
        return false;
    }
    let matched_row = scan_pre_rows(&k.ntag, &k.nver, &k.nadsh, &k.ptag, &k.pver, &k.padsh, k.m, i, Ghost(c));
    !matched_row
}

/// `keep_range(c, lo, hi)` has at most `hi - lo` rows.
pub proof fn lemma_keep_range_len(c: Ctx, lo: int, hi: int)
    requires lo <= hi,
    ensures keep_range(c, lo, hi).len() <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_keep_range_len(c, lo, hi - 1);
    }
}

/// `qual(c, i)`, from the scan columns.
fn row_qualifies_k(k: &ScanCols, i: usize, Ghost(c): Ghost<Ctx>) -> (r: bool)
    requires ctx_ok(c), (i as int) < c.n, scan_cols_ok(*k, c),
    ensures r == qual(c, i as int),
    no_unwind
{
    proof {
        reveal(scan_cols_ok);
    }
    row_qualifies(&k.nuom, k.ddate, k.pv, k.plen, k.dlo, k.dhi, i, Ghost(c))
}

/// The key hash pair of `num` row `i`.
fn pair_at_k(k: &ScanCols, i: usize, Ghost(c): Ghost<Ctx>) -> (r: (u64, u64))
    requires ctx_ok(c), (i as int) < c.n, scan_cols_ok(*k, c),
    ensures r.0 == num_tv(c, i as int), r.1 == num_ad(c, i as int), r.0 != 0,
    no_unwind
{
    proof {
        reveal(scan_cols_ok);
    }
    let tv = tv_hash_at(&k.ntag, &k.nver, i, Ghost(c.n));
    let ad = ad_hash_at(&k.nadsh, i, Ghost(c.n));
    (tv, ad)
}

/// `qual(c, i)`.
fn row_qualifies(nuom: &TextCol, ddate: &'static [i32], pv: &'static [u8], plen: usize, dlo: i64, dhi: i64, i: usize,
    Ghost(c): Ghost<Ctx>) -> (r: bool)
    requires
        ctx_ok(c), (i as int) < c.n, nuom@ == nuom_v(c), text_wf(nuom@, c.n),
        ddate@ == ni::i32s(c.np[ni::DDATE as int]), ddate@.len() == c.n,
        pv@ == c.pv, plen == pv@.len(), dlo as int == c.dlo, dhi as int == c.dhi,
    ensures r == qual(c, i as int),
    no_unwind
{
    let d = ddate[i] as i64;
    if d < dlo || d > dhi {
        return false;
    }
    text_is(nuom, i, Ghost(c.n), pv, plen)
}

/// Exact mode: compare the row's key texts with every `pre` row.
fn scan_pre_rows(ntag: &TextCol, nver: &TextCol, nadsh: &TextCol, ptag: &TextCol, pver: &TextCol, padsh: &TextCol,
    m: usize, i: usize, Ghost(c): Ghost<Ctx>) -> (r: bool)
    requires
        ctx_ok(c), (i as int) < c.n, m as int == c.m,
        ntag@ == ntag_v(c), nver@ == nver_v(c), nadsh@ == nadsh_v(c),
        ptag@ == ptag_v(c), pver@ == pver_v(c), padsh@ == padsh_v(c),
        text_wf(ntag@, c.n), text_wf(nver@, c.n), text_wf(nadsh@, c.n),
        text_wf(ptag@, c.m), text_wf(pver@, c.m), text_wf(padsh@, c.m),
    ensures r == matched(c, i as int),
    no_unwind
{
    let mut j: usize = 0;
    while j < m
        invariant
            j <= m, m as int == c.m, (i as int) < c.n,
            ntag@ == ntag_v(c), nver@ == nver_v(c), nadsh@ == nadsh_v(c),
            ptag@ == ptag_v(c), pver@ == pver_v(c), padsh@ == padsh_v(c),
            text_wf(ntag@, c.n), text_wf(nver@, c.n), text_wf(nadsh@, c.n),
            text_wf(ptag@, c.m), text_wf(pver@, c.m), text_wf(padsh@, c.m),
            forall|j2: int| 0 <= j2 < j ==> !#[trigger] same_key(c, i as int, j2),
        decreases m - j,
    {
        if text_same(ptag, j, Ghost(c.m), ntag, i, Ghost(c.n)) && text_same(pver, j, Ghost(c.m), nver, i, Ghost(c.n))
            && text_same(padsh, j, Ghost(c.m), nadsh, i, Ghost(c.n)) {
            proof {
                assert(same_key(c, i as int, j as int));
            }
            return true;
        }
        j = j + 1;
    }
    false
}

} // verus!
