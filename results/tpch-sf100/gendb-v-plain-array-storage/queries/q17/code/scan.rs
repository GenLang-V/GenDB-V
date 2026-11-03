//! The lineitem scan: for each lineitem row whose part key is listed (`keys::inrow`), a hit record of its slot
//! (the index of its key), quantity and price. One `ScanTask` per even range of rows (`parts::split_at`), or the
//! whole table on the calling thread; each range's hits are its listed rows in ascending order (`hits_ok` with
//! `range_filter(lo, hi, inrow)`).
//!
//! A range is scanned in two phases over one record buffer (one slot per row of the range, allocated zeroed: a
//! large zeroed allocation comes from fresh pages, so only the written prefix costs anything):
//! - phase A (`collect_candidates`): per row, one bit test in the key set's first filter and, for the ~0.5% of
//!   rows that pass, the second filter; the rows passing both (`candp`) go to the buffer as `(row, 0, 0)`. The loop
//!   has no other work, so it runs close to the speed of streaming the part-key column.
//! - phase B (`compact_hits`): per candidate row, the exact slot lookup (`find_slot`) and, for listed keys, the
//!   row's quantity and price; the hit records are written in place over the candidates already read.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::tables::*;
use crate::agent::keys::*;
use crate::agent::parts::{split_at, lemma_split};
use crate::agent::common::selection::*;
use crate::agent::common::keyset::*;

verus! {

/// The lineitem columns the scan reads.
#[derive(Clone, Copy)]
pub struct LineCols {
    pub l_pkey: &'static [i64],
    pub l_qty: &'static [i128],
    pub l_price: &'static [i128],
    pub nl: usize,
}

pub open spec fn line_cols_ok(c: LineCols, sv: StoresView) -> bool {
    &&& c.l_pkey@ == l_pkey(sv) && c.l_qty@ == l_qty(sv) && c.l_price@ == l_price(sv)
    &&& c.nl == n_l(sv)
    &&& l_pkey(sv).len() == n_l(sv) && l_qty(sv).len() == n_l(sv) && l_price(sv).len() == n_l(sv)
}

/// A record: (slot, quantity coefficient, price coefficient) of a hit; during phase A `(row, 0, 0)` of a candidate.
pub type Rec = (usize, i64, i64);

/// Hit records: `used` of them are filled.
pub struct Hits {
    pub recs: Vec<Rec>,
    pub used: usize,
}

/// The buffer has `cap` slots.
pub open spec fn hits_cap(h: &Hits, cap: int) -> bool {
    h.recs@.len() == cap
}

/// The filled records are the rows `rows` (lineitem row numbers).
pub open spec fn hits_ok(h: &Hits, rows: Seq<int>, keys: Seq<i64>, sv: StoresView) -> bool {
    &&& h.used == rows.len()
    &&& h.used <= h.recs@.len()
    &&& forall|j: int| 0 <= j < h.used ==> rec_ok(#[trigger] h.recs@[j], rows[j], keys, sv)
}

/// Record `r` is row `l`: its slot holds the row's part key, and its quantity and price are the row's.
pub open spec fn rec_ok(r: Rec, l: int, keys: Seq<i64>, sv: StoresView) -> bool {
    &&& 0 <= l < n_l(sv)
    &&& r.0 < keys.len()
    &&& keys[r.0 as int] == l_pkey(sv)[l]
    &&& r.1 as int == l_qty(sv)[l] as int
    &&& r.2 as int == l_price(sv)[l] as int
}

/// Row `l`'s part key passes both filters of the key set (`f1`, `f2`): the candidates of phase A.
pub open spec fn candp(f1: Seq<u64>, f2: Seq<u64>, sv: StoresView) -> spec_fn(int) -> bool {
    |l: int| may_have(f1, f2, l_pkey(sv)[l])
}

/// Empty records with `cap` slots (calling thread).
pub fn new_hits(cap: usize) -> (h: Hits)
    ensures hits_cap(&h, cap as int), h.used == 0,
{
    Hits { recs: vec![(0usize, 0i64, 0i64); cap], used: 0 }
}

/// Phase A over rows `lo..hi`: the candidate rows, in ascending order, as `recs[0..nc].0`.
fn collect_candidates(c: &LineCols, ks: &KeySet, lo: usize, hi: usize, recs: &mut Vec<Rec>, Ghost(sv): Ghost<StoresView>)
    -> (nc: usize)
    requires
        line_cols_ok(*c, sv), keyset_wf(ks), lo < hi <= c.nl, old(recs)@.len() >= hi - lo,
    ensures
        final(recs)@.len() == old(recs)@.len(),
        nc == range_filter(lo as int, hi as int, candp(ks.f1@, ks.f2@, sv)).len(),
        forall|t: int| 0 <= t < nc ==> (#[trigger] final(recs)@[t]).0 as int
            == range_filter(lo as int, hi as int, candp(ks.f1@, ks.f2@, sv))[t],
    no_unwind
{
    let ghost cp = candp(ks.f1@, ks.f2@, sv);
    let ghost cap = recs@.len();
    let keys = c.l_pkey;
    let f1 = &ks.f1;
    let f2 = &ks.f2;
    // Reading the last row and the last filter words first lets the compiler drop the bounds checks of the loop.
    let _last_key = keys[hi - 1];
    let _last_f1 = f1[F1_WORDS - 1];
    let _last_f2 = f2[F2_WORDS - 1];
    let mut nc: usize = 0;
    let mut i = lo;
    while i < hi
        invariant
            line_cols_ok(*c, sv), keyset_wf(ks), keys == c.l_pkey, f1 == &ks.f1, f2 == &ks.f2,
            cp == candp(ks.f1@, ks.f2@, sv),
            lo <= i <= hi, hi <= c.nl, recs@.len() == cap, cap >= hi - lo,
            nc == range_filter(lo as int, i as int, cp).len(), nc <= i - lo,
            forall|t: int| 0 <= t < nc ==> (#[trigger] recs@[t]).0 as int == range_filter(lo as int, i as int, cp)[t],
        decreases hi - i,
    {
        let k = keys[i];
        let (w1, b1, w2, m2) = key_probe(k);
        let ghost rf0 = range_filter(lo as int, i as int, cp);
        let pass = (f1[w1] >> b1) & 1u64 == 1u64 && f2[w2] & m2 == m2;
        assert(pass == cp(i as int));
        if pass {
            let ghost r0 = recs@;
            recs[nc] = (i, 0, 0);
            proof {
                assert forall|t: int| 0 <= t < nc + 1 implies (#[trigger] recs@[t]).0 as int
                    == range_filter(lo as int, i + 1, cp)[t] by {
                    if t < nc { assert(recs@[t] == r0[t]); }
                }
            }
            nc = nc + 1;
        }
        i = i + 1;
    }
    nc
}

/// Phase B: the candidates `recs[0..nc].0` (the rows `cands`) replaced, in place and in order, by the hit records
/// of the candidates whose part key is listed.
fn compact_hits(c: &LineCols, ks: &KeySet, h: &mut Hits, nc: usize, Ghost(cands): Ghost<Seq<int>>, Ghost(sv): Ghost<StoresView>)
    requires
        line_cols_ok(*c, sv), keyset_wf(ks), domains_ok(sv), old(h).used == 0,
        nc == cands.len(), nc <= old(h).recs@.len(),
        forall|t: int| 0 <= t < nc ==> 0 <= #[trigger] cands[t] < c.nl,
        forall|t: int| 0 <= t < nc ==> (#[trigger] old(h).recs@[t]).0 as int == cands[t],
    ensures
        hits_ok(final(h), seq_filter(cands, inrow(ks.keys@, sv)), ks.keys@, sv),
        final(h).recs@.len() == old(h).recs@.len(),
    no_unwind
{
    let ghost p = inrow(ks.keys@, sv);
    let ghost cap = h.recs@.len();
    let mut u: usize = 0;
    let mut j: usize = 0;
    while j < nc
        invariant
            line_cols_ok(*c, sv), keyset_wf(ks), domains_ok(sv), p == inrow(ks.keys@, sv),
            nc == cands.len(), nc <= cap, h.recs@.len() == cap, u <= j, j <= nc, h.used == u,
            forall|t: int| 0 <= t < nc ==> 0 <= #[trigger] cands[t] < c.nl,
            forall|t: int| j <= t < nc ==> (#[trigger] h.recs@[t]).0 as int == cands[t],
            u == seq_filter(cands.take(j as int), p).len(),
            forall|t: int| 0 <= t < u ==> rec_ok(#[trigger] h.recs@[t], seq_filter(cands.take(j as int), p)[t], ks.keys@, sv),
        decreases nc - j,
    {
        let ghost hits0 = seq_filter(cands.take(j as int), p);
        let ghost r0 = h.recs@;
        let row = h.recs[j].0;
        assert(row as int == cands[j as int]);
        assert(0 <= cands[j as int] < c.nl);
        assert(row < n_l(sv));
        proof {
            lemma_take_step(cands, j as int);
            lemma_seq_filter_push(cands.take(j as int), row as int, p);
        }
        match find_slot(ks, c.l_pkey[row]) {
            Some(s) => {
                proof {
                    assert(domains_ok(sv));
                    assert(0 <= row < n_l(sv));
                    assert(num15(l_qty(sv)[row as int]));
                    assert(num15(l_price(sv)[row as int]));
                }
                let q = c.l_qty[row] as i64;
                let pr = c.l_price[row] as i64;
                h.recs[u] = (s, q, pr);
                h.used = u + 1;
                proof {
                    assert(p(row as int));
                    let hits1 = hits0.push(row as int);
                    assert forall|t: int| 0 <= t < u + 1 implies rec_ok(#[trigger] h.recs@[t], hits1[t], ks.keys@, sv) by {
                        if t < u {
                            assert(h.recs@[t] == r0[t]);
                            assert(rec_ok(r0[t], hits0[t], ks.keys@, sv));
                        }
                    }
                }
                u = u + 1;
            },
            None => {
                proof { assert(!p(row as int)); }
            },
        }
        j = j + 1;
    }
    proof { assert(cands.take(nc as int) =~= cands); }
}

/// Scan rows `lo..hi` into the empty records `h` (with at least `hi - lo` slots).
pub fn scan_range(c: &LineCols, ks: &KeySet, lo: usize, hi: usize, h: &mut Hits, Ghost(sv): Ghost<StoresView>)
    requires
        line_cols_ok(*c, sv), keyset_wf(ks), domains_ok(sv),
        lo <= hi <= c.nl, old(h).used == 0, old(h).recs@.len() >= hi - lo,
    ensures
        hits_ok(final(h), range_filter(lo as int, hi as int, inrow(ks.keys@, sv)), ks.keys@, sv),
        hits_cap(final(h), old(h).recs@.len() as int),
    no_unwind
{
    let ghost p = inrow(ks.keys@, sv);
    if lo == hi {
        proof { assert(range_filter(lo as int, hi as int, p) =~= Seq::<int>::empty()); }
        return;
    }
    let ghost cp = candp(ks.f1@, ks.f2@, sv);
    let nc = collect_candidates(c, ks, lo, hi, &mut h.recs, Ghost(sv));
    let ghost cands = range_filter(lo as int, hi as int, cp);
    proof { lemma_range_filter_members(lo as int, hi as int, cp); }
    compact_hits(c, ks, h, nc, Ghost(cands), Ghost(sv));
    proof {
        // the listed rows are candidates: a listed key passes both filters
        lemma_filter_range_filter(lo as int, hi as int, cp, p);
        assert forall|l: int| lo <= l < hi implies #[trigger] and_pred(cp, p)(l) == p(l) by {
            if p(l) {
                let s = choose|s: int| 0 <= s < ks.keys@.len() && #[trigger] ks.keys@[s] == l_pkey(sv)[l];
                assert(may_have(ks.f1@, ks.f2@, ks.keys@[s]));
            }
        }
        lemma_range_filter_ext(lo as int, hi as int, and_pred(cp, p), p);
    }
}

/// One task: the rows `lo..hi`.
pub struct ScanTask {
    pub cols: LineCols,
    pub ks: Arc<KeySet>,
    pub lo: usize,
    pub hi: usize,
    pub hits: Hits,
    pub sv: Ghost<StoresView>,
}

impl WorkerTask for ScanTask {
    type Output = Hits;

    open spec fn pre(&self) -> bool {
        &&& line_cols_ok(self.cols, self.sv@)
        &&& keyset_wf(&*self.ks)
        &&& domains_ok(self.sv@)
        &&& self.lo <= self.hi <= self.cols.nl
        &&& self.hits.used == 0
        &&& hits_cap(&self.hits, (self.hi - self.lo) as int)
    }

    open spec fn post(&self, out: Hits) -> bool {
        hits_ok(&out, range_filter(self.lo as int, self.hi as int, inrow(self.ks.keys@, self.sv@)), self.ks.keys@, self.sv@)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: Hits) {
        let c = self.cols;
        let mut h = self.hits;
        scan_range(&c, &*self.ks, self.lo, self.hi, &mut h, self.sv);
        h
    }
}

/// The hit records of every range: `outs[t]` holds the listed rows of `[split_at(nl, nt, t), split_at(nl, nt, t + 1))`.
pub open spec fn scan_ok(outs: Seq<Hits>, nt: int, keys: Seq<i64>, sv: StoresView) -> bool {
    &&& outs.len() == nt
    &&& forall|t: int| 0 <= t < nt ==> hits_ok(&#[trigger] outs[t], range_filter(split_at(n_l(sv) as int, nt, t),
            split_at(n_l(sv) as int, nt, t + 1), inrow(keys, sv)), keys, sv)
}

/// The scan of all lineitem rows, on the calling thread (`nt == 1`) or in `nt` tasks.
pub fn scan_pass(c: LineCols, ks: Arc<KeySet>, nt: usize, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>)
    -> (r: Result<Vec<Hits>, WorkerFailure>)
    requires line_cols_ok(c, sv), keyset_wf(&*ks), domains_ok(sv), 1 <= nt <= MAX_WORKERS,
    ensures r matches Ok(outs) ==> scan_ok(outs@, nt as int, ks.keys@, sv),
{
    let nl = c.nl;
    if nt == 1 {
        let mut h = new_hits(nl);
        scan_range(&c, &*ks, 0, nl, &mut h, Ghost(sv));
        let mut outs: Vec<Hits> = Vec::new();
        outs.push(h);
        proof {
            lemma_split(nl as int, 1, 0);
            assert(outs@[0] == h);
        }
        return Ok(outs);
    }
    let q = nl / nt;
    let rm = nl % nt;
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut lo: usize = 0;
    let mut k: usize = 0;
    while k < nt
        invariant
            line_cols_ok(c, sv), keyset_wf(&*ks), domains_ok(sv), 2 <= nt <= MAX_WORKERS, k <= nt, nl == c.nl,
            q == nl / nt, rm == nl % nt,
            tasks@.len() == k,
            lo == split_at(nl as int, nt as int, k as int),
            forall|t: int| 0 <= t < k ==> (#[trigger] tasks@[t]).pre()
                && tasks@[t].sv@ == sv && tasks@[t].ks == ks
                && tasks@[t].lo == split_at(nl as int, nt as int, t)
                && tasks@[t].hi == split_at(nl as int, nt as int, t + 1),
        decreases nt - k,
    {
        proof { lemma_split(nl as int, nt as int, k as int); }
        let hi = lo + q + if k < rm { 1 } else { 0 };
        let task = ScanTask { cols: c, ks: ks.clone(), lo, hi, hits: new_hits(hi - lo), sv: Ghost(sv) };
        tasks.push(task);
        lo = hi;
        k = k + 1;
    }
    let ghost tasks0 = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => { return Err(e); },
    };
    proof {
        assert forall|t: int| 0 <= t < nt implies hits_ok(&#[trigger] outs@[t], range_filter(split_at(nl as int, nt as int, t),
            split_at(nl as int, nt as int, t + 1), inrow(ks.keys@, sv)), ks.keys@, sv) by {
            assert(tasks0[t].post(outs@[t]));
        }
    }
    Ok(outs)
}

} // verus!
