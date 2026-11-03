//! Phase-2 worker task: the partsupp rows `c` of one row range whose part key is in the qualifying key set and
//! whose supplier lies in the requested region (`flags`, from phase 1). For each such row the task records the
//! row, its supplier row `b`, part key, supply cost and the supplier's account balance (coefficients at scale 2),
//! in increasing `c`, in preallocated buffers (`complete == false` when they were too small).
//!
//! Rows are processed in batches: a first pass collects the rows of the batch whose part key is in the set (a
//! sequential read of the part keys and a probe of the key set), a second pass looks up their suppliers, so the
//! random reads of different rows overlap. A supplier row is found by arithmetic when phase 1 saw the keys
//! `base + b` (`dense`), otherwise by `find_key`; supplier keys are unique (primary key), so it is the only row
//! with that key.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::common::slot_buffer::SlotBuffer;
use crate::agent::common::key_set::{KeySet, BLOCK};
use crate::agent::common::key_lookup::find_key;
use crate::agent::scan_part::keys_unique;

verus! {

/// Rows per batch of the partsupp scan when a call has several tasks (and of the caller's rescan of a lane).
pub const PS_BATCH: usize = 4096;

/// Rows per batch when one task scans every row: longer batches interrupt the four memory streams less often
/// and give the random reads of passes 2-4 more independent rows (the buffers are allocated once per call).
pub const PS_BATCH_SOLO: usize = 16384;

/// The partsupp-row condition the scan decides: the part key is in the set and some supplier row with the row's
/// supplier key is flagged.
pub open spec fn ps_hit(set: Seq<i64>, pkeys: Seq<i64>, skeys: Seq<i64>, supp_keys: Seq<i64>, flags: Seq<bool>, c: int) -> bool {
    &&& exists|j: int| 0 <= j < set.len() && #[trigger] set[j] == pkeys[c]
    &&& exists|b: int| 0 <= b < supp_keys.len() && #[trigger] supp_keys[b] == skeys[c] && flags[b]
}

/// The recorded fields of the hits, one buffer per field.
pub struct Hits {
    pub c: SlotBuffer<usize>,
    pub b: SlotBuffer<usize>,
    pub pk: SlotBuffer<i64>,
    pub cost: SlotBuffer<i128>,
    pub acct: SlotBuffer<i128>,
}

impl Hits {
    pub open spec fn wf(&self) -> bool {
        &&& self.c.wf() && self.b.wf() && self.pk.wf() && self.cost.wf() && self.acct.wf()
        &&& self.b.view().len() == self.c.view().len()
        &&& self.pk.view().len() == self.c.view().len()
        &&& self.cost.view().len() == self.c.view().len()
        &&& self.acct.view().len() == self.c.view().len()
        &&& self.b.capacity() == self.c.capacity()
        &&& self.pk.capacity() == self.c.capacity()
        &&& self.cost.capacity() == self.c.capacity()
        &&& self.acct.capacity() == self.c.capacity()
    }

    pub open spec fn len(&self) -> int {
        self.c.view().len() as int
    }

    /// Empty buffers with room for `capacity` hits.
    pub fn new(capacity: usize) -> (h: Hits)
        ensures h.wf(), h.c.view().len() == 0, h.c.capacity() == capacity,
    {
        Hits {
            c: SlotBuffer::new(capacity, 0usize),
            b: SlotBuffer::new(capacity, 0usize),
            pk: SlotBuffer::new(capacity, 0i64),
            cost: SlotBuffer::new(capacity, 0i128),
            acct: SlotBuffer::new(capacity, 0i128),
        }
    }

    fn push(&mut self, c: usize, b: usize, pk: i64, cost: i128, acct: i128)
        requires old(self).wf(), old(self).c.view().len() < old(self).c.capacity(),
        ensures
            final(self).wf(),
            final(self).c.view() == old(self).c.view().push(c),
            final(self).b.view() == old(self).b.view().push(b),
            final(self).pk.view() == old(self).pk.view().push(pk),
            final(self).cost.view() == old(self).cost.view().push(cost),
            final(self).acct.view() == old(self).acct.view().push(acct),
            final(self).c.capacity() == old(self).c.capacity(),
        no_unwind
    {
        self.c.push(c);
        self.b.push(b);
        self.pk.push(pk);
        self.cost.push(cost);
        self.acct.push(acct);
    }
}

/// The partsupp-scan inputs of one task.
pub struct PsScan {
    pub pkeys: &'static [i64],
    pub skeys: &'static [i64],
    pub costs: &'static [i128],
    pub nps: usize,
    pub lo: usize,
    pub hi: usize,
    pub set: Arc<KeySet>,
    pub supp_keys: &'static [i64],
    pub supp_acct: &'static [i128],
    pub ns: usize,
    pub sbase: i64,
    pub dense: bool,
    pub flags: Arc<Vec<bool>>,
}

impl PsScan {
    pub open spec fn wf(&self) -> bool {
        &&& self.pkeys@.len() == self.nps
        &&& self.skeys@.len() == self.nps
        &&& self.costs@.len() == self.nps
        &&& self.lo <= self.hi <= self.nps
        &&& self.set.wf()
        &&& self.supp_keys@.len() == self.ns
        &&& self.supp_acct@.len() == self.ns
        &&& keys_unique(self.supp_keys@)
        &&& self.flags@.len() == self.ns
        &&& self.dense ==> forall|b: int| 0 <= b < self.ns ==> #[trigger] self.supp_keys@[b] == self.sbase + b
    }

    pub open spec fn hit(&self, c: int) -> bool {
        ps_hit(self.set.keys(), self.pkeys@, self.skeys@, self.supp_keys@, self.flags@, c)
    }

    /// The part key of row `c` is in the set (the first conjunct of `hit`).
    pub open spec fn in_set(&self, c: int) -> bool {
        self.set.has(self.pkeys@[c])
    }

    /// Hit `i` of `h` records a hit row below `end`, its supplier row and values.
    pub open spec fn fields_ok(&self, h: Hits, end: int, i: int) -> bool {
        let c = h.c.view()[i] as int;
        let b = h.b.view()[i] as int;
        &&& self.lo <= c < end
        &&& 0 <= b < self.supp_keys@.len()
        &&& self.hit(c)
        &&& self.supp_keys@[b] == self.skeys@[c]
        &&& h.pk.view()[i] == self.pkeys@[c]
        &&& h.cost.view()[i] == self.costs@[c]
        &&& h.acct.view()[i] == self.supp_acct@[b]
    }

    /// `h` lists exactly the hit rows of `[lo, end)`, in increasing order, with their fields.
    pub open spec fn covers(&self, end: int, h: Hits) -> bool {
        &&& h.wf()
        &&& forall|i: int| 0 <= i < h.len() ==> #[trigger] self.fields_ok(h, end, i)
        &&& forall|i: int, j: int| 0 <= i < j < h.len() ==> h.c.view()[i] < h.c.view()[j]
        &&& forall|c: int| self.lo <= c < end && #[trigger] self.hit(c) ==> exists|i: int| 0 <= i < h.len() && h.c.view()[i] == c
    }

    /// Hit `i` of the field sequences records a hit row of `[lo, end)` with its supplier row and values.
    pub open spec fn seq_fields_ok(&self, hs: HitSeqs, end: int, i: int) -> bool {
        let c = hs.c[i] as int;
        let b = hs.b[i] as int;
        &&& self.lo <= c < end
        &&& 0 <= b < self.supp_keys@.len()
        &&& self.hit(c)
        &&& self.supp_keys@[b] == self.skeys@[c]
        &&& hs.pk[i] == self.pkeys@[c]
        &&& hs.cost[i] == self.costs@[c]
        &&& hs.acct[i] == self.supp_acct@[b]
    }

    /// The field sequences list exactly the hit rows of `[lo, end)`, in increasing order.
    pub open spec fn covers_seqs(&self, end: int, hs: HitSeqs) -> bool {
        &&& hs.wf()
        &&& forall|i: int| 0 <= i < hs.c.len() ==> #[trigger] self.seq_fields_ok(hs, end, i)
        &&& forall|i: int, j: int| 0 <= i < j < hs.c.len() ==> hs.c[i] < hs.c[j]
        &&& forall|c: int| self.lo <= c < end && #[trigger] self.hit(c) ==> exists|i: int| 0 <= i < hs.c.len() && hs.c[i] == c
    }
}

/// The fields of the hits as sequences (the merged output of several tasks).
pub struct HitSeqs {
    pub c: Seq<usize>,
    pub b: Seq<usize>,
    pub pk: Seq<i64>,
    pub cost: Seq<i128>,
    pub acct: Seq<i128>,
}

impl HitSeqs {
    pub open spec fn wf(&self) -> bool {
        self.b.len() == self.c.len() && self.pk.len() == self.c.len() && self.cost.len() == self.c.len() && self.acct.len() == self.c.len()
    }

    pub open spec fn concat(self, o: HitSeqs) -> HitSeqs {
        HitSeqs { c: self.c + o.c, b: self.b + o.b, pk: self.pk + o.pk, cost: self.cost + o.cost, acct: self.acct + o.acct }
    }
}

/// The views of a task's hit buffers.
pub open spec fn hit_seqs(h: Hits) -> HitSeqs {
    HitSeqs { c: h.c.view(), b: h.b.view(), pk: h.pk.view(), cost: h.cost.view(), acct: h.acct.view() }
}

/// A task's coverage as sequences.
pub proof fn lemma_covers_seqs(s: PsScan, end: int, h: Hits)
    requires s.covers(end, h),
    ensures s.covers_seqs(end, hit_seqs(h)),
{
    let hs = hit_seqs(h);
    assert forall|i: int| 0 <= i < hs.c.len() implies #[trigger] s.seq_fields_ok(hs, end, i) by {
        assert(s.fields_ok(h, end, i));
    }
}

/// Two scans over the same columns with adjacent ranges: the concatenated fields cover the union.
pub proof fn lemma_ps_concat(s0: PsScan, s1: PsScan, mid: int, end: int, h0: HitSeqs, h1: HitSeqs)
    requires
        s0.covers_seqs(mid, h0),
        s1.covers_seqs(end, h1),
        s1.lo == mid,
        s0.lo <= mid <= end,
        s0.pkeys == s1.pkeys, s0.skeys == s1.skeys, s0.costs == s1.costs, s0.set == s1.set,
        s0.supp_keys == s1.supp_keys, s0.supp_acct == s1.supp_acct, s0.flags == s1.flags,
    ensures s0.covers_seqs(end, h0.concat(h1)),
{
    let h = h0.concat(h1);
    let m = h0.c.len() as int;
    assert forall|i: int| 0 <= i < h.c.len() implies #[trigger] s0.seq_fields_ok(h, end, i) by {
        if i < m {
            assert(s0.seq_fields_ok(h0, mid, i));
            assert(h.c[i] == h0.c[i] && h.b[i] == h0.b[i] && h.pk[i] == h0.pk[i] && h.cost[i] == h0.cost[i] && h.acct[i] == h0.acct[i]);
        } else {
            assert(s1.seq_fields_ok(h1, end, i - m));
            assert(h.c[i] == h1.c[i - m] && h.b[i] == h1.b[i - m] && h.pk[i] == h1.pk[i - m] && h.cost[i] == h1.cost[i - m] && h.acct[i] == h1.acct[i - m]);
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < h.c.len() implies h.c[i] < h.c[j] by {
        if j < m {
            assert(h.c[i] == h0.c[i] && h.c[j] == h0.c[j]);
        } else if i >= m {
            assert(h.c[i] == h1.c[i - m] && h.c[j] == h1.c[j - m]);
        } else {
            assert(s0.seq_fields_ok(h0, mid, i));
            assert(s1.seq_fields_ok(h1, end, j - m));
            assert(h.c[i] == h0.c[i] && h.c[j] == h1.c[j - m]);
        }
    }
    assert forall|c: int| s0.lo <= c < end && #[trigger] s0.hit(c) implies exists|i: int| 0 <= i < h.c.len() && h.c[i] == c by {
        if c < mid {
            let i = choose|i: int| 0 <= i < h0.c.len() && h0.c[i] == c;
            assert(h.c[i] == c);
        } else {
            assert(s1.hit(c));
            let i = choose|i: int| 0 <= i < h1.c.len() && h1.c[i] == c;
            assert(h.c[m + i] == c);
        }
    }
}

/// Rows of `[p, q)` that are not hits do not change the coverage.
proof fn lemma_ps_skip(s: PsScan, p: int, q: int, h: Hits)
    requires
        s.covers(p, h),
        p <= q,
        forall|c: int| p <= c < q ==> !#[trigger] s.hit(c),
    ensures s.covers(q, h),
{
    assert forall|i: int| 0 <= i < h.len() implies #[trigger] s.fields_ok(h, q, i) by {
        assert(s.fields_ok(h, p, i));
    }
}

/// A hit row at `p` (above every listed row) extends the coverage.
proof fn lemma_ps_push(s: PsScan, p: int, h0: Hits, h1: Hits)
    requires
        s.covers(p, h0),
        s.lo <= p,
        h1.wf(),
        h1.len() == h0.len() + 1,
        h1.c.view() == h0.c.view().push(h1.c.view()[h0.len()]),
        h1.b.view() == h0.b.view().push(h1.b.view()[h0.len()]),
        h1.pk.view() == h0.pk.view().push(h1.pk.view()[h0.len()]),
        h1.cost.view() == h0.cost.view().push(h1.cost.view()[h0.len()]),
        h1.acct.view() == h0.acct.view().push(h1.acct.view()[h0.len()]),
        h1.c.view()[h0.len()] == p,
        s.fields_ok(h1, p + 1, h0.len()),
    ensures s.covers(p + 1, h1),
{
    let m = h0.len();
    assert forall|i: int| 0 <= i < h1.len() implies #[trigger] s.fields_ok(h1, p + 1, i) by {
        if i < m {
            assert(s.fields_ok(h0, p, i));
            assert(h1.c.view()[i] == h0.c.view()[i]);
            assert(h1.b.view()[i] == h0.b.view()[i]);
            assert(h1.pk.view()[i] == h0.pk.view()[i]);
            assert(h1.cost.view()[i] == h0.cost.view()[i]);
            assert(h1.acct.view()[i] == h0.acct.view()[i]);
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < h1.len() implies h1.c.view()[i] < h1.c.view()[j] by {
        if j < m {
            assert(h1.c.view()[i] == h0.c.view()[i] && h1.c.view()[j] == h0.c.view()[j]);
        } else {
            assert(s.fields_ok(h0, p, i));
            assert(h1.c.view()[i] == h0.c.view()[i]);
        }
    }
    assert forall|c: int| s.lo <= c < p + 1 && #[trigger] s.hit(c) implies exists|i: int| 0 <= i < h1.len() && h1.c.view()[i] == c by {
        if c < p {
            let i = choose|i: int| 0 <= i < h0.len() && h0.c.view()[i] == c;
            assert(h1.c.view()[i] == c);
        } else {
            assert(h1.c.view()[m] == c);
        }
    }
}

/// The supplier row with key `sk`, if any.
fn supplier_row(supp_keys: &[i64], ns: usize, dense: bool, sbase: i64, sk: i64) -> (r: Option<usize>)
    requires
        supp_keys@.len() == ns,
        dense ==> forall|b: int| 0 <= b < ns ==> #[trigger] supp_keys@[b] == sbase + b,
    ensures
        r matches Some(b) ==> b < ns && supp_keys@[b as int] == sk,
        r is None ==> forall|b: int| 0 <= b < ns ==> supp_keys@[b] != sk,
    no_unwind
{
    if dense {
        let off: i128 = sk as i128 - sbase as i128;
        if 0 <= off && off < ns as i128 {
            proof { assert(supp_keys@[off as int] == sbase + off); }
            Some(off as usize)
        } else {
            proof {
                assert forall|b: int| 0 <= b < ns implies supp_keys@[b] != sk by {
                    assert(supp_keys@[b] == sbase + b);
                }
            }
            None
        }
    } else {
        find_key(supp_keys, ns, sk)
    }
}

/// Scratch buffers of the passes 2-4 of one task (shared by its lanes): the supplier row of each collected row of
/// a batch (`ns` when there is none) and whether it is a hit. Their common length is the task's batch size
/// (`size`, a positive multiple of `BLOCK`).
pub struct PassScratch {
    pub brow: Vec<usize>,
    pub keep: Vec<bool>,
}

impl PassScratch {
    /// The batch size (rows).
    pub open spec fn size(&self) -> int {
        self.brow@.len() as int
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.keep@.len() == self.brow@.len()
        &&& 0 < self.brow@.len()
        &&& self.brow@.len() as int % (BLOCK as int) == 0
    }

    /// Fresh buffers for batches of `bs` rows (calling thread; allocates).
    pub fn new(bs: usize) -> (s: PassScratch)
        requires 0 < bs, bs % BLOCK == 0,
        ensures s.wf(), s.size() == bs,
    {
        PassScratch { brow: vec![0usize; bs], keep: vec![false; bs] }
    }
}

/// A batch buffer for the rows of `scan` (`bs` long, or empty for an empty range).
pub open spec fn batch_ok(batch: Seq<usize>, scan: PsScan, bs: int) -> bool {
    batch.len() == bs || scan.lo == scan.hi
}

/// The next batch start `a + bs` stays a multiple of `bs` within `len`.
proof fn lemma_batch_step(a: int, len: int, bs: int)
    requires 0 < bs, 0 <= a < len, a % bs == 0, len % bs == 0,
    ensures a + bs <= len, (a + bs) % bs == 0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, bs);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(len, bs);
    let qa = a / bs;
    let ql = len / bs;
    assert(qa < ql) by (nonlinear_arith) requires a == bs * qa, len == bs * ql, a < len, bs > 0;
    assert(a + bs <= len) by (nonlinear_arith) requires a == bs * qa, len == bs * ql, qa + 1 <= ql, bs > 0;
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(qa + 1, bs);
    assert(a + bs == (qa + 1) * bs) by (nonlinear_arith) requires a == bs * qa;
}

/// `m` rounded down to a multiple of `bs`.
proof fn lemma_round_down(m: int, bs: int)
    requires 0 < bs, 0 <= m,
    ensures 0 <= m - m % bs <= m, (m - m % bs) % bs == 0, 0int % bs == 0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m, bs);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(m, bs);
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(m / bs, bs);
    assert(m - m % bs == (m / bs) * bs) by (nonlinear_arith) requires m == bs * (m / bs) + m % bs;
    vstd::arithmetic::div_mod::lemma_small_mod(0, bs as nat);
}

impl PsScan {
    /// `b` is the supplier row of partsupp row `c` (`ns` when no supplier has its key).
    pub open spec fn supp_of(&self, c: int, b: int) -> bool {
        &&& 0 <= b <= self.ns
        &&& b < self.ns ==> self.supp_keys@[b] == self.skeys@[c]
        &&& b == self.ns ==> forall|b2: int| 0 <= b2 < self.ns ==> self.supp_keys@[b2] != self.skeys@[c]
    }

    /// Passes 2-4 of one batch `[a, end)` whose rows with a part key in the set are `scr.batch[0..k]` (pass 1):
    /// append the batch's hits to `out`; `false` when `out` had too little room.
    pub fn batch_passes(&self, out0: Hits, batch: &Vec<usize>, pass: &mut PassScratch, a: usize, end: usize, k: usize) -> (r: (Hits, bool))
        requires
            self.wf(),
            old(pass).wf(),
            out0.wf(),
            self.lo <= a <= end <= self.hi,
            end - a <= old(pass).size(),
            self.covers(a as int, out0),
            out0.len() <= a - self.lo,
            self.set.collected(self.pkeys@, a as int, end as int, batch@, k as int),
        ensures
            final(pass).wf(),
            final(pass).size() == old(pass).size(),
            r.0.wf(),
            r.0.c.capacity() == out0.c.capacity(),
            r.1 ==> self.covers(end as int, r.0) && r.0.len() <= end - self.lo,
            out0.c.capacity() >= self.hi - self.lo ==> r.1,
        no_unwind
    {
        let ghost cap = out0.c.capacity();
        let ghost bs = pass.size();
        let flags: &Vec<bool> = &*self.flags;
        let mut out = out0;
        proof {
            assert forall|i: int| 0 <= i < k implies a <= #[trigger] batch@[i] < end && self.in_set(batch@[i] as int) by {}
            assert forall|y: int| a <= y < end && #[trigger] self.in_set(y) implies exists|i: int| 0 <= i < k && batch@[i] == y by {
                assert(self.set.has(self.pkeys@[y]));
            }
        }
        // Pass 2: the supplier row of each collected row.
        let mut j: usize = 0;
        while j < k
            invariant
                self.wf(),
                pass.wf(), pass.size() == bs, bs == old(pass).size(),
                k <= end - a, end <= self.hi, a <= end, end - a <= bs, k <= batch@.len(),
                j <= k,
                forall|i: int| 0 <= i < k ==> a <= #[trigger] batch@[i] < end,
                forall|i: int| 0 <= i < j ==> self.supp_of(batch@[i] as int, #[trigger] pass.brow@[i] as int),
            decreases k - j,
        {
            let c = batch[j];
            let b = match supplier_row(self.supp_keys, self.ns, self.dense, self.sbase, self.skeys[c]) {
                Some(b) => b,
                None => self.ns,
            };
            pass.brow[j] = b;
            j = j + 1;
        }
        // Pass 3: whether each collected row's supplier lies in the region.
        j = 0;
        while j < k
            invariant
                self.wf(),
                *flags == *self.flags,
                pass.wf(), pass.size() == bs, bs == old(pass).size(),
                k <= end - a, end <= self.hi, a <= end, end - a <= bs, k <= batch@.len(),
                j <= k,
                forall|i: int| 0 <= i < k ==> a <= #[trigger] batch@[i] < end && self.in_set(batch@[i] as int),
                forall|i: int| 0 <= i < k ==> self.supp_of(batch@[i] as int, #[trigger] pass.brow@[i] as int),
                forall|i: int| 0 <= i < j ==> #[trigger] pass.keep@[i] == self.hit(batch@[i] as int),
            decreases k - j,
        {
            let b = pass.brow[j];
            let f = if b < self.ns { flags[b] } else { false };
            proof {
                let c = batch@[j as int] as int;
                assert(self.in_set(c));
                if f {
                    assert(self.supp_keys@[b as int] == self.skeys@[c] && self.flags@[b as int]);
                    assert(self.hit(c));
                } else if self.hit(c) {
                    let b2 = choose|b2: int| 0 <= b2 < self.supp_keys@.len() && #[trigger] self.supp_keys@[b2] == self.skeys@[c] && self.flags@[b2];
                    if b < self.ns {
                        assert(keys_unique(self.supp_keys@));
                        assert(b2 == b as int);
                    }
                }
            }
            pass.keep[j] = f;
            j = j + 1;
        }
        // Pass 4: record the hits.
        proof {
            let next = if 0 < k { batch@[0] as int } else { end as int };
            assert forall|y: int| a <= y < next implies !#[trigger] self.hit(y) by {
                if self.hit(y) {
                    assert(self.in_set(y));
                    let i = choose|i: int| 0 <= i < k && batch@[i] == y;
                    if i > 0 { assert(batch@[0] < batch@[i]); }
                }
            }
            lemma_ps_skip(*self, a as int, next, out);
        }
        j = 0;
        while j < k
            invariant
                self.wf(),
                pass.wf(), pass.size() == bs, bs == old(pass).size(),
                self.lo <= a <= end <= self.hi,
                end - a <= bs,
                k <= batch@.len(),
                out.c.capacity() == cap,
                cap == out0.c.capacity(),
                out.len() <= (a - self.lo) + j,
                k <= end - a,
                j <= k,
                forall|i: int| 0 <= i < k ==> a <= #[trigger] batch@[i] < end && self.in_set(batch@[i] as int),
                forall|i: int, i2: int| 0 <= i < i2 < k ==> batch@[i] < batch@[i2],
                forall|y: int| a <= y < end && #[trigger] self.in_set(y) ==> exists|i: int| 0 <= i < k && batch@[i] == y,
                forall|i: int| 0 <= i < k ==> self.supp_of(batch@[i] as int, #[trigger] pass.brow@[i] as int),
                forall|i: int| 0 <= i < k ==> #[trigger] pass.keep@[i] == self.hit(batch@[i] as int),
                self.covers(if j < k { batch@[j as int] as int } else { end as int }, out),
            decreases k - j,
        {
            let c = batch[j];
            let ghost h0 = out;
            if pass.keep[j] {
                let b = pass.brow[j];
                if !out.c.has_room() {
                    proof { assert(out.len() < self.hi - self.lo); }
                    return (out, false);
                }
                proof {
                    assert(self.hit(c as int));
                    assert(b < self.ns) by {
                        if b == self.ns {
                            let b2 = choose|b2: int| 0 <= b2 < self.supp_keys@.len() && #[trigger] self.supp_keys@[b2] == self.skeys@[c as int] && self.flags@[b2];
                        }
                    }
                }
                out.push(c, b, self.pkeys[c], self.costs[c], self.supp_acct[b]);
                proof { lemma_ps_push(*self, c as int, h0, out); }
            } else {
                proof { lemma_ps_skip(*self, c as int, c + 1, h0); }
            }
            proof {
                let next = if j + 1 < k { batch@[j + 1] as int } else { end as int };
                assert forall|z: int| c + 1 <= z < next implies !#[trigger] self.hit(z) by {
                    if self.hit(z) {
                        assert(self.in_set(z));
                        let i = choose|i: int| 0 <= i < k && batch@[i] == z;
                        if i <= j { assert(batch@[i] <= batch@[j as int]); }
                        if i > j + 1 { assert(batch@[j + 1] < batch@[i]); }
                    }
                }
                lemma_ps_skip(*self, c + 1, next, out);
            }
            j = j + 1;
        }
        (out, true)
    }

    /// Scan `[a0, hi)` after `[lo, a0)`, whose hits `out0` holds; `false` when `out0` had too little room.
    pub fn run_from(&self, out0: Hits, batch: &mut Vec<usize>, pass: &mut PassScratch, a0: usize) -> (r: (Hits, bool))
        requires
            self.wf(),
            out0.wf(),
            batch_ok(old(batch)@, *self, old(pass).size()),
            old(pass).wf(),
            self.lo <= a0 <= self.hi,
            self.covers(a0 as int, out0),
            out0.len() <= a0 - self.lo,
        ensures
            batch_ok(final(batch)@, *self, old(pass).size()),
            final(pass).wf(),
            final(pass).size() == old(pass).size(),
            r.0.wf(),
            r.0.c.capacity() == out0.c.capacity(),
            r.1 ==> self.covers(self.hi as int, r.0),
            out0.c.capacity() >= self.hi - self.lo ==> r.1,
        no_unwind
    {
        let set: &KeySet = &*self.set;
        let bs = pass.brow.len();
        let mut out = out0;
        let mut a = a0;
        while a < self.hi
            invariant
                self.wf(),
                *set == *self.set,
                self.lo <= a <= self.hi,
                bs == old(pass).size(),
                batch_ok(batch@, *self, bs as int),
                pass.wf(),
                pass.size() == bs,
                out.wf(),
                self.covers(a as int, out),
                out.c.capacity() == out0.c.capacity(),
                out.len() <= a - self.lo,
            decreases self.hi - a,
        {
            let end = if self.hi - a > bs { a + bs } else { self.hi };
            // Pass 1: the rows of the batch whose part key is in the set, in increasing order.
            let k = set.collect_members_blocked(self.pkeys, self.nps, a, end, batch);
            let (o, ok) = self.batch_passes(out, batch, pass, a, end, k);
            if !ok {
                return (o, false);
            }
            out = o;
            a = end;
        }
        (out, true)
    }

    /// Scan `[lo, hi)` (see the module comment); `false` when `out0` had too little room.
    pub fn run_scan(&self, out0: Hits) -> (r: (Hits, bool))
        requires
            self.wf(),
            out0.wf(),
            out0.len() == 0,
        ensures
            r.0.wf(),
            r.1 ==> self.covers(self.hi as int, r.0),
            out0.c.capacity() >= self.hi - self.lo ==> r.1,
    {
        let mut batch = vec![0usize; PS_BATCH];
        assert(PS_BATCH % BLOCK == 0);
        let mut pass = PassScratch::new(PS_BATCH);
        self.run_from(out0, &mut batch, &mut pass, self.lo)
    }
}

/// One lane of a phase-2 task: a row range, its output buffers and its scratch buffers.
pub struct PsLane {
    pub scan: PsScan,
    pub out: Hits,
    pub batch: Vec<usize>,
}

impl PsLane {
    pub open spec fn pre(&self) -> bool {
        &&& self.scan.wf()
        &&& self.out.wf()
        &&& self.out.len() == 0
    }
}

/// The hits of one lane and whether they are complete (`false`: the buffers were too small).
pub struct PsLaneOut {
    pub hits: Hits,
    pub complete: bool,
}

pub open spec fn lane_post(l: PsLane, o: PsLaneOut) -> bool {
    o.hits.wf() && (o.complete ==> l.scan.covers(l.scan.hi as int, o.hits))
}

/// Lanes `l` and `m` probe the same key set over the same part-key column.
pub open spec fn same_probe(l: PsLane, m: PsLane) -> bool {
    l.scan.set == m.scan.set && l.scan.pkeys == m.scan.pkeys && l.scan.nps == m.scan.nps
}

/// The smaller of two counts.
fn min_usize(x: usize, y: usize) -> (r: usize)
    ensures r <= x, r <= y,
    no_unwind
{
    if x < y { x } else { y }
}

/// One phase-2 task: four lanes of adjacent row ranges, scanned together on one thread. While every lane has a
/// whole batch left, pass 1 runs on the four lanes at once (`KeySet::collect4`, one block of each lane in turn, so
/// four memory streams are in flight), then passes 2-4 run lane by lane; the rest of each lane is scanned alone.
pub struct PsScanTask {
    pub l0: PsLane,
    pub l1: PsLane,
    pub l2: PsLane,
    pub l3: PsLane,
    pub pass: PassScratch,
}

pub struct PsOut4 {
    pub o0: PsLaneOut,
    pub o1: PsLaneOut,
    pub o2: PsLaneOut,
    pub o3: PsLaneOut,
}

impl WorkerTask for PsScanTask {
    type Output = PsOut4;

    open spec fn pre(&self) -> bool {
        &&& self.l0.pre() && self.l1.pre() && self.l2.pre() && self.l3.pre()
        &&& self.pass.wf()
        &&& batch_ok(self.l0.batch@, self.l0.scan, self.pass.size())
        &&& batch_ok(self.l1.batch@, self.l1.scan, self.pass.size())
        &&& batch_ok(self.l2.batch@, self.l2.scan, self.pass.size())
        &&& batch_ok(self.l3.batch@, self.l3.scan, self.pass.size())
        &&& same_probe(self.l0, self.l1) && same_probe(self.l0, self.l2) && same_probe(self.l0, self.l3)
    }

    open spec fn post(&self, r: PsOut4) -> bool {
        lane_post(self.l0, r.o0) && lane_post(self.l1, r.o1) && lane_post(self.l2, r.o2) && lane_post(self.l3, r.o3)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.l0.scan.lo as u64, self.l3.scan.hi as u64)
    }

    fn run(self) -> (r: PsOut4) {
        let ghost (g0, g1, g2, g3) = (self.l0, self.l1, self.l2, self.l3);
        let PsScanTask { l0, l1, l2, l3, pass } = self;
        let mut pass = pass;
        let PsLane { scan: sc0, out: mut o0, batch: mut s0 } = l0;
        let PsLane { scan: sc1, out: mut o1, batch: mut s1 } = l1;
        let PsLane { scan: sc2, out: mut o2, batch: mut s2 } = l2;
        let PsLane { scan: sc3, out: mut o3, batch: mut s3 } = l3;
        let set: &KeySet = &*sc0.set;
        let bs = pass.brow.len();
        // Rows per lane scanned together: the shortest lane, down to whole batches.
        let m = min_usize(min_usize(sc0.hi - sc0.lo, sc1.hi - sc1.lo), min_usize(sc2.hi - sc2.lo, sc3.hi - sc3.lo));
        proof { lemma_round_down(m as int, bs as int); }
        let len = m - m % bs;
        let (mut c0, mut c1, mut c2, mut c3) = (true, true, true, true);
        let mut a: usize = 0;
        proof {
            assert(sc0.covers(sc0.lo as int, o0) && sc1.covers(sc1.lo as int, o1));
            assert(sc2.covers(sc2.lo as int, o2) && sc3.covers(sc3.lo as int, o3));
        }
        while a < len
            invariant
                sc0 == g0.scan, sc1 == g1.scan, sc2 == g2.scan, sc3 == g3.scan,
                sc0.wf(), sc1.wf(), sc2.wf(), sc3.wf(),
                same_probe(g0, g1), same_probe(g0, g2), same_probe(g0, g3),
                *set == *sc0.set,
                len <= sc0.hi - sc0.lo, len <= sc1.hi - sc1.lo, len <= sc2.hi - sc2.lo, len <= sc3.hi - sc3.lo,
                0 < bs, bs % BLOCK == 0,
                len as int % (bs as int) == 0,
                a as int % (bs as int) == 0,
                a <= len,
                batch_ok(s0@, sc0, bs as int), batch_ok(s1@, sc1, bs as int),
                batch_ok(s2@, sc2, bs as int), batch_ok(s3@, sc3, bs as int),
                pass.wf(),
                pass.size() == bs,
                o0.wf(), o1.wf(), o2.wf(), o3.wf(),
                o0.c.capacity() == g0.out.c.capacity(), o1.c.capacity() == g1.out.c.capacity(),
                o2.c.capacity() == g2.out.c.capacity(), o3.c.capacity() == g3.out.c.capacity(),
                c0 ==> sc0.covers(sc0.lo + a, o0) && o0.len() <= a,
                c1 ==> sc1.covers(sc1.lo + a, o1) && o1.len() <= a,
                c2 ==> sc2.covers(sc2.lo + a, o2) && o2.len() <= a,
                c3 ==> sc3.covers(sc3.lo + a, o3) && o3.len() <= a,
                g0.out.c.capacity() >= sc0.hi - sc0.lo ==> c0,
                g1.out.c.capacity() >= sc1.hi - sc1.lo ==> c1,
                g2.out.c.capacity() >= sc2.hi - sc2.lo ==> c2,
                g3.out.c.capacity() >= sc3.hi - sc3.lo ==> c3,
            decreases len - a,
        {
            proof { lemma_batch_step(a as int, len as int, bs as int); }
            let (k0, k1, k2, k3) = set.collect4(sc0.pkeys, sc0.nps, sc0.lo + a, sc1.lo + a, sc2.lo + a, sc3.lo + a, bs,
                &mut s0, &mut s1, &mut s2, &mut s3);
            if c0 {
                let (o, ok) = sc0.batch_passes(o0, &s0, &mut pass, sc0.lo + a, sc0.lo + a + bs, k0);
                o0 = o;
                c0 = ok;
            }
            if c1 {
                let (o, ok) = sc1.batch_passes(o1, &s1, &mut pass, sc1.lo + a, sc1.lo + a + bs, k1);
                o1 = o;
                c1 = ok;
            }
            if c2 {
                let (o, ok) = sc2.batch_passes(o2, &s2, &mut pass, sc2.lo + a, sc2.lo + a + bs, k2);
                o2 = o;
                c2 = ok;
            }
            if c3 {
                let (o, ok) = sc3.batch_passes(o3, &s3, &mut pass, sc3.lo + a, sc3.lo + a + bs, k3);
                o3 = o;
                c3 = ok;
            }
            a = a + bs;
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
        PsOut4 {
            o0: PsLaneOut { hits: o0, complete: c0 },
            o1: PsLaneOut { hits: o1, complete: c1 },
            o2: PsLaneOut { hits: o2, complete: c2 },
            o3: PsLaneOut { hits: o3, complete: c3 },
        }
    }
}

} // verus!
