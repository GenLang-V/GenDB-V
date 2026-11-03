//! Phase 2 of the fast path: one task per range of buckets `b0..b1`, i.e. of customer indices
//! `cust_lo(b0) .. cust_lo(b1)`. For each bucket it counts the entries of that bucket of every phase-1 task into a
//! local count array of `SPAN` slots (one bucket's customers stay in the second-level cache), then tallies every
//! customer's count into a histogram of counts below `HMAX`, and checks that the customer's key is `base + index`.
//! A count of `HMAX` or more, or another key, stops the task (`ok == false`).
//!
//! Contract (`count_post`): `hist[v]` is the number of customers of the range whose number of counting orders
//! (`tot`) is `v`, every such number is below `HMAX`, and the range's keys are dense.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::common::split::{split, lemma_split};
use crate::agent::tables::Cols;
use crate::agent::scan::*;

verus! {

/// Histogram size: numbers of orders per customer below it are tallied.
pub const HMAX: usize = 256;

/// Number of orders counting for customer index `i`.
pub open spec fn tot(c: Cols, ss: Seq<Seq<u8>>, base: int, i: int) -> nat {
    crange(c, ss, base, i, 0, c.no as int)
}

/// Number of customer indices in `[lo, hi)` with exactly `v` counting orders.
pub open spec fn hcnt(c: Cols, ss: Seq<Seq<u8>>, base: int, v: int, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo { 0 } else { hcnt(c, ss, base, v, lo, hi - 1) + if tot(c, ss, base, hi - 1) == v { 1nat } else { 0nat } }
}

/// The histogram of the customer indices `[lo, hi)`, every count below `HMAX`.
pub open spec fn hist_ok(c: Cols, ss: Seq<Seq<u8>>, base: int, hist: Seq<u64>, lo: int, hi: int) -> bool {
    &&& hist.len() == HMAX
    &&& forall|v: int| 0 <= v < HMAX ==> #[trigger] hist[v] as int == hcnt(c, ss, base, v, lo, hi)
    &&& forall|i: int| lo <= i < hi ==> #[trigger] tot(c, ss, base, i) < HMAX
}

/// The customer keys of `[lo, hi)` are `base + index`.
pub open spec fn dense_ok(c: Cols, base: int, lo: int, hi: int) -> bool {
    forall|i: int| lo <= i < hi ==> #[trigger] c.cck@[i] as int == base + i
}

/// The first customer index of bucket `b` (or `nc`).
pub open spec fn cust_lo(b: int, nc: int) -> int {
    if b * (SPAN as int) < nc { b * (SPAN as int) } else { nc }
}

/// Every phase-1 output holds the buckets of its row range (task `t` covers `split(no, nt, t) .. split(no, nt, t + 1)`).
pub open spec fn outs_ok(c: Cols, ss: Seq<Seq<u8>>, base: int, nb: int, outs: Seq<ScanOut>, nt: int) -> bool {
    &&& outs.len() == nt && nt >= 1
    &&& forall|t: int| 0 <= t < nt ==> (#[trigger] outs[t]).ok && bucket_ok(c, ss, base, nb, outs[t].cap as int,
            outs[t].buf@, outs[t].fill@, split(c.no as int, nt, t), split(c.no as int, nt, t + 1))
}

/// What a phase-2 task establishes for its customer range.
pub open spec fn count_post(c: Cols, ss: Seq<Seq<u8>>, base: int, hist: Seq<u64>, lo: int, hi: int) -> bool {
    hist_ok(c, ss, base, hist, lo, hi) && dense_ok(c, base, lo, hi)
}

// ------------------------------------------------------------------------------------------------ lemmas

/// Counts of consecutive row ranges add up.
pub proof fn lemma_crange_add(c: Cols, ss: Seq<Seq<u8>>, base: int, i: int, a: int, b: int, d: int)
    requires a <= b <= d,
    ensures crange(c, ss, base, i, a, d) == crange(c, ss, base, i, a, b) + crange(c, ss, base, i, b, d),
    decreases d - b,
{
    if b < d {
        lemma_crange_add(c, ss, base, i, a, b, d - 1);
    }
}

/// A count of a row range is at most its length.
pub proof fn lemma_crange_bound(c: Cols, ss: Seq<Seq<u8>>, base: int, i: int, a: int, b: int)
    requires a <= b,
    ensures crange(c, ss, base, i, a, b) <= b - a,
    decreases b - a,
{
    if a < b {
        lemma_crange_bound(c, ss, base, i, a, b - 1);
    }
}

/// One more customer of the histogram's range.
proof fn lemma_hcnt_step(c: Cols, ss: Seq<Seq<u8>>, base: int, v: int, lo: int, i: int)
    requires lo <= i,
    ensures hcnt(c, ss, base, v, lo, i + 1) == hcnt(c, ss, base, v, lo, i) + if tot(c, ss, base, i) == v { 1nat } else { 0nat },
{
}

/// A histogram count of a range is at most its length.
pub proof fn lemma_hcnt_bound(c: Cols, ss: Seq<Seq<u8>>, base: int, v: int, lo: int, hi: int)
    requires lo <= hi,
    ensures hcnt(c, ss, base, v, lo, hi) <= hi - lo,
    decreases hi - lo,
{
    if lo < hi {
        lemma_hcnt_bound(c, ss, base, v, lo, hi - 1);
    }
}

/// Histogram counts of consecutive customer ranges add up.
pub proof fn lemma_hcnt_add(c: Cols, ss: Seq<Seq<u8>>, base: int, v: int, a: int, b: int, d: int)
    requires a <= b <= d,
    ensures hcnt(c, ss, base, v, a, d) == hcnt(c, ss, base, v, a, b) + hcnt(c, ss, base, v, b, d),
    decreases d - b,
{
    if b < d {
        lemma_hcnt_add(c, ss, base, v, a, b, d - 1);
    }
}

/// One more entry of a region prefix.
proof fn lemma_occ_prefix(r: Seq<u16>, s: int, x: int)
    requires 0 <= s < r.len(),
    ensures occ_of(r.subrange(0, s + 1), x) == occ_of(r.subrange(0, s), x) + if r[s] as int == x { 1nat } else { 0nat },
{
    assert(r.subrange(0, s + 1).drop_last() =~= r.subrange(0, s));
}

/// A prefix holds at most the copies of the whole.
proof fn lemma_occ_prefix_le(r: Seq<u16>, s: int, x: int)
    requires 0 <= s <= r.len(),
    ensures occ_of(r.subrange(0, s), x) <= occ_of(r, x),
    decreases r.len() - s,
{
    if s < r.len() {
        lemma_occ_prefix(r, s, x);
        lemma_occ_prefix_le(r, s + 1, x);
    } else {
        assert(r.subrange(0, s) =~= r);
    }
}

/// The customers of bucket `b` that exist: `cust_lo(b) .. cust_lo(b + 1)`, all of bucket `b`.
proof fn lemma_bucket_range(b: int, nc: int, i: int)
    requires b >= 0, nc >= 0, cust_lo(b, nc) <= i < cust_lo(b + 1, nc),
    ensures bucket(i) == b, boff(i) == i - b * (SPAN as int), i < nc,
{
    assert(b * (SPAN as int) <= i < (b + 1) * (SPAN as int));
}

// ------------------------------------------------------------------------------------------------ the task

/// One task of phase 2: buckets `b0..b1`.
pub struct CountTask {
    pub c: Cols,
    pub outs: Arc<Vec<ScanOut>>,
    pub nt: usize,
    pub b0: usize,
    pub b1: usize,
    pub nb: usize,
    pub base: i64,
    pub cnt: Vec<u32>,
    pub hist: Vec<u64>,
    pub ss: Ghost<Seq<Seq<u8>>>,
}

/// A task's result: its histogram when `ok`.
pub struct CountOut {
    pub hist: Vec<u64>,
    pub ok: bool,
}

/// The counts of bucket `b` (customers `blo .. bhi`) after the regions of tasks `0..t`: every customer's number of
/// counting rows among `0 .. split(no, nt, t)`.
pub open spec fn counts_ok(c: Cols, ss: Seq<Seq<u8>>, base: int, cnt: Seq<u32>, blo: int, bhi: int, upto: int) -> bool {
    forall|i: int| blo <= i < bhi ==> #[trigger] cnt[i - blo] as int == crange(c, ss, base, i, 0, upto)
}

/// Count the entries of bucket `b` (customers `blo .. bhi`, `blo = b * SPAN`) of every phase-1 output.
fn count_bucket(c: &Cols, outs: &Vec<ScanOut>, nt: usize, nb: usize, b: usize, blo: usize, bhi: usize, cnt: &mut Vec<u32>,
    Ghost(ss): Ghost<Seq<Seq<u8>>>, Ghost(base): Ghost<int>)
    requires
        outs_ok(*c, ss, base, nb as int, outs@, nt as int), c.no <= u32::MAX,
        b < nb, blo == b * SPAN, blo < bhi <= blo + SPAN, bhi <= c.nc, bhi == cust_lo(b as int + 1, c.nc as int),
        old(cnt)@.len() == SPAN,
    ensures
        final(cnt)@.len() == SPAN,
        counts_ok(*c, ss, base, final(cnt)@, blo as int, bhi as int, c.no as int),
    no_unwind
{
    // zero the bucket's counts
    let mut z: usize = 0;
    while z < bhi - blo
        invariant z <= bhi - blo <= SPAN, cnt@.len() == SPAN, forall|k: int| 0 <= k < z ==> #[trigger] cnt@[k] == 0u32,
        decreases bhi - blo - z,
    {
        cnt[z] = 0u32;
        z = z + 1;
    }
    proof {
        lemma_split(c.no as int, nt as int, 0, nt as int);
    }
    let mut t: usize = 0;
    while t < nt
        invariant
            outs_ok(*c, ss, base, nb as int, outs@, nt as int), c.no <= u32::MAX,
            b < nb, blo == b * SPAN, blo < bhi <= blo + SPAN, bhi <= c.nc, bhi == cust_lo(b as int + 1, c.nc as int),
            cnt@.len() == SPAN, t <= nt,
            counts_ok(*c, ss, base, cnt@, blo as int, bhi as int, split(c.no as int, nt as int, t as int)),
        decreases nt - t,
    {
        let o = &outs[t];
        let ghost lo_t = split(c.no as int, nt as int, t as int);
        let ghost hi_t = split(c.no as int, nt as int, t + 1);
        proof {
            assert(o.ok && bucket_ok(*c, ss, base, nb as int, o.cap as int, o.buf@, o.fill@, lo_t, hi_t));
            lemma_split(c.no as int, nt as int, t as int, t + 1);
            lemma_split(c.no as int, nt as int, t + 1, nt as int);
        }
        let cap = o.cap;
        let n = o.fill[b];
        proof { assert(n as int <= cap as int); }
        let blen = o.buf.len();
        proof {
            assert(b as int * cap as int <= nb as int * cap as int) by (nonlinear_arith) requires b < nb;
            assert(nb as int * cap as int <= blen);
        }
        let start = b * cap;
        let ghost reg = region(o.buf@, o.fill@, cap as int, b as int);
        proof {
            lemma_region(o.buf@, o.fill@, cap as int, nb as int, b as int);
            assert forall|i: int| blo <= i < bhi implies #[trigger] cnt@[i - blo] as int
                == crange(*c, ss, base, i, 0, lo_t) + occ_of(reg.subrange(0, 0), boff(i)) by {
                assert(reg.subrange(0, 0).len() == 0);
            }
        }
        let mut s: usize = 0;
        while s < n
            invariant
                outs_ok(*c, ss, base, nb as int, outs@, nt as int), c.no <= u32::MAX,
                b < nb, blo == b * SPAN, blo < bhi <= blo + SPAN, bhi <= c.nc, bhi == cust_lo(b as int + 1, c.nc as int),
                cnt@.len() == SPAN, t < nt, s <= n, n == o.fill@[b as int], cap == o.cap, start == b * cap,
                blen == o.buf@.len(),
                o == outs@[t as int],
                bucket_ok(*c, ss, base, nb as int, cap as int, o.buf@, o.fill@, lo_t, hi_t),
                0 <= lo_t <= hi_t <= c.no,
                reg == region(o.buf@, o.fill@, cap as int, b as int),
                forall|i: int| blo <= i < bhi ==> #[trigger] cnt@[i - blo] as int
                    == crange(*c, ss, base, i, 0, lo_t) + occ_of(reg.subrange(0, s as int), boff(i)),
            decreases n - s,
        {
            proof {
                lemma_slot(b as int, s as int, cap as int, nb as int);
                lemma_region(o.buf@, o.fill@, cap as int, nb as int, b as int);
            }
            let e = o.buf[start + s] as usize;
            proof {
                assert(reg[s as int] == o.buf@[b * cap + s]);
                assert(b * SPAN + e < c.nc);
                let i0 = blo + e;
                assert(bucket(i0) == b && boff(i0) == e) by {
                    assert(i0 == b * 65536 + e);
                }
                assert(i0 < bhi) by {
                    if i0 >= bhi {
                        assert(bhi == c.nc || bhi == blo + SPAN);
                    }
                }
                // the count of `i0` stays below the number of rows
                assert(cnt@[i0 - blo] as int == crange(*c, ss, base, i0, 0, lo_t) + occ_of(reg.subrange(0, s as int), boff(i0)));
                assert(i0 - blo == e);
                lemma_occ_prefix(reg, s as int, e as int);
                lemma_occ_prefix_le(reg, s + 1, e as int);
                assert(occ_of(reg, boff(i0)) == crange(*c, ss, base, i0, lo_t, hi_t));
                lemma_crange_add(*c, ss, base, i0, 0, lo_t, hi_t);
                lemma_crange_bound(*c, ss, base, i0, 0, hi_t);
                assert(cnt@[e as int] + 1 <= hi_t);
            }
            cnt[e] = cnt[e] + 1;
            proof {
                assert forall|i: int| blo <= i < bhi implies #[trigger] cnt@[i - blo] as int
                    == crange(*c, ss, base, i, 0, lo_t) + occ_of(reg.subrange(0, s + 1), boff(i)) by {
                    lemma_occ_prefix(reg, s as int, boff(i));
                    lemma_bucket_range(b as int, c.nc as int, i);
                }
            }
            s = s + 1;
        }
        proof {
            lemma_region(o.buf@, o.fill@, cap as int, nb as int, b as int);
            assert(reg.subrange(0, n as int) =~= reg);
            assert forall|i: int| blo <= i < bhi implies #[trigger] cnt@[i - blo] as int
                == crange(*c, ss, base, i, 0, hi_t) by {
                lemma_bucket_range(b as int, c.nc as int, i);
                assert(occ_of(reg, boff(i)) == crange(*c, ss, base, i, lo_t, hi_t));
                lemma_crange_add(*c, ss, base, i, 0, lo_t, hi_t);
            }
        }
        t = t + 1;
    }
    proof {
        lemma_split(c.no as int, nt as int, nt as int, nt as int);
    }
}

/// Tally the customers `blo .. bhi` of a bucket (their counts in `cnt`) into the histogram, checking their keys.
fn tally_bucket(c: &Cols, base: i64, blo: usize, bhi: usize, cnt: &Vec<u32>, hist: &mut Vec<u64>,
    Ghost(ss): Ghost<Seq<Seq<u8>>>, Ghost(clo): Ghost<int>) -> (ok: bool)
    requires
        0 <= clo <= blo <= bhi <= blo + SPAN, bhi <= c.nc, c.cck@.len() == c.nc, cnt@.len() == SPAN,
        counts_ok(*c, ss, base as int, cnt@, blo as int, bhi as int, c.no as int),
        count_post(*c, ss, base as int, old(hist)@, clo, blo as int),
    ensures
        ok ==> count_post(*c, ss, base as int, final(hist)@, clo, bhi as int),
    no_unwind
{
    let mut i = blo;
    while i < bhi
        invariant
            0 <= clo <= blo <= i <= bhi <= blo + SPAN, bhi <= c.nc, c.cck@.len() == c.nc, cnt@.len() == SPAN,
            counts_ok(*c, ss, base as int, cnt@, blo as int, bhi as int, c.no as int),
            count_post(*c, ss, base as int, hist@, clo, i as int),
        decreases bhi - i,
    {
        let v = cnt[i - blo] as usize;
        if v >= HMAX {
            return false;
        }
        if (c.cck[i] as i128) != (base as i128) + (i as i128) {
            return false;
        }
        proof {
            lemma_hcnt_bound(*c, ss, base as int, v as int, clo, i as int);
            assert(hist@[v as int] as int == hcnt(*c, ss, base as int, v as int, clo, i as int));
        }
        let ghost h0 = hist@;
        hist[v] = hist[v] + 1;
        proof {
            assert forall|w: int| 0 <= w < HMAX implies #[trigger] hist@[w] as int == hcnt(*c, ss, base as int, w, clo, i + 1) by {
                lemma_hcnt_step(*c, ss, base as int, w, clo, i as int);
                assert(h0[w] as int == hcnt(*c, ss, base as int, w, clo, i as int));
            }
        }
        i = i + 1;
    }
    true
}

impl WorkerTask for CountTask {
    type Output = CountOut;

    open spec fn pre(&self) -> bool {
        &&& outs_ok(self.c, self.ss@, self.base as int, self.nb as int, self.outs@, self.nt as int)
        &&& self.c.no <= u32::MAX && self.c.cck@.len() == self.c.nc
        &&& self.b0 <= self.b1 <= self.nb
        &&& self.cnt@.len() == SPAN
        &&& self.hist@ == Seq::new(HMAX as nat, |_i: int| 0u64)
    }

    open spec fn post(&self, out: CountOut) -> bool {
        out.ok ==> count_post(self.c, self.ss@, self.base as int, out.hist@, cust_lo(self.b0 as int, self.c.nc as int),
            cust_lo(self.b1 as int, self.c.nc as int))
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.b0 as u64, self.b1 as u64)
    }

    fn run(self) -> (out: CountOut) {
        let CountTask { c, outs, nt, b0, b1, nb, base, cnt, hist, ss } = self;
        let mut cnt = cnt;
        let mut hist = hist;
        let ok = count_range(&c, &*outs, nt, nb, b0, b1, base, &mut cnt, &mut hist, Ghost(ss@));
        CountOut { hist, ok }
    }
}

/// The buckets `b0..b1`, from an empty histogram: `false` when a customer stops the task.
fn count_range(c: &Cols, outs: &Vec<ScanOut>, nt: usize, nb: usize, b0: usize, b1: usize, base: i64, cnt: &mut Vec<u32>,
    hist: &mut Vec<u64>, Ghost(ss): Ghost<Seq<Seq<u8>>>) -> (ok: bool)
    requires
        outs_ok(*c, ss, base as int, nb as int, outs@, nt as int),
        c.no <= u32::MAX && c.cck@.len() == c.nc,
        b0 <= b1 <= nb, old(cnt)@.len() == SPAN, old(hist)@ == Seq::new(HMAX as nat, |_i: int| 0u64),
    ensures
        ok ==> count_post(*c, ss, base as int, final(hist)@, cust_lo(b0 as int, c.nc as int), cust_lo(b1 as int, c.nc as int)),
    no_unwind
{
    let nc = c.nc;
    let ghost clo = cust_lo(b0 as int, nc as int);
    proof {
        assert forall|v: int| 0 <= v < HMAX implies #[trigger] hist@[v] as int == hcnt(*c, ss, base as int, v, clo, clo) by {}
    }
    let mut b = b0;
    while b < b1
        invariant
            outs_ok(*c, ss, base as int, nb as int, outs@, nt as int), c.no <= u32::MAX, c.cck@.len() == c.nc,
            nc == c.nc, b0 <= b <= b1 <= nb, cnt@.len() == SPAN, clo == cust_lo(b0 as int, nc as int),
            clo <= cust_lo(b as int, nc as int),
            count_post(*c, ss, base as int, hist@, clo, cust_lo(b as int, nc as int)),
        decreases b1 - b,
    {
        if nc / SPAN < b {
            // bucket `b` and the later ones hold no customer
            proof {
                assert(cust_lo(b as int, nc as int) == nc);
                assert(cust_lo(b1 as int, nc as int) == nc) by {
                    assert(b1 as int * 65536 >= b as int * 65536) by (nonlinear_arith) requires b1 >= b;
                }
            }
            return true;
        }
        let blo = b * SPAN;
        if blo >= nc {
            proof {
                assert(cust_lo(b as int, nc as int) == nc);
                assert(cust_lo(b1 as int, nc as int) == nc) by {
                    assert(b1 as int * 65536 >= b as int * 65536) by (nonlinear_arith) requires b1 >= b;
                }
            }
            return true;
        }
        let bhi = if nc - blo > SPAN { blo + SPAN } else { nc };
        proof {
            assert(cust_lo(b as int, nc as int) == blo);
            assert(bhi == cust_lo(b as int + 1, nc as int));
        }
        count_bucket(c, outs, nt, nb, b, blo, bhi, cnt, Ghost(ss), Ghost(base as int));
        if !tally_bucket(c, base, blo, bhi, cnt, hist, Ghost(ss), Ghost(clo)) {
            return false;
        }
        b = b + 1;
    }
    true
}

} // verus!
