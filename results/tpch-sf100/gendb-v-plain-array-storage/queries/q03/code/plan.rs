//! The fast path of a call: the customer pass and the lineitem scan, each split into `workers` tasks over
//! consecutive ranges (`split`), then the merge of the scan's runs.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::runs::*;
use crate::agent::scan::*;
use crate::agent::scan_parts::*;
use crate::agent::customers::*;
use crate::agent::merge::*;
use crate::agent::common::bits::*;
use crate::agent::topk::FixTop;
use crate::agent::combine::{combine, fast_ok};
use crate::spec::ast::Literal;

verus! {

/// Start of part `k` when `n` items are split into `w` parts: `k * (n / w) + min(k, n % w)`.
pub open spec fn split_at(n: int, w: int, k: int) -> int {
    k * (n / w) + if k < n % w { k } else { n % w }
}

/// The part boundaries are non-decreasing and end at `n`.
pub proof fn lemma_split(n: int, w: int, k: int)
    requires 0 <= n, 1 <= w, 0 <= k < w,
    ensures
        split_at(n, w, k + 1) == split_at(n, w, k) + n / w + if k < n % w { 1int } else { 0int },
        0 <= split_at(n, w, k) <= split_at(n, w, k + 1) <= n,
        split_at(n, w, 0) == 0,
        split_at(n, w, w) == n,
{
    let (q, r) = (n / w, n % w);
    assert(n == w * q + r && 0 <= r < w && 0 <= q) by (nonlinear_arith) requires q == n / w, r == n % w, 0 <= n, 1 <= w;
    assert((k + 1) * q == k * q + q) by (nonlinear_arith);
    assert(w * q == q * w) by (nonlinear_arith);
    assert(0 <= k * q) by (nonlinear_arith) requires 0 <= k, 0 <= q;
    assert((k + 1) * q <= w * q) by (nonlinear_arith) requires k + 1 <= w, 0 <= q;
    assert(0 * q == 0);
}

/// The customer pass: the segment bitmap of all customer rows, and whether `c_custkey` is positional.
pub fn customer_pass(cc: CustCols, workers: usize, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>)
    -> (r: Result<(Vec<u64>, bool), WorkerFailure>)
    requires cust_cols_ok(cc, sv, seg), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok((bits, pos)) ==> (pos ==> cust_bits_ok(bits@, sv, seg, cc.base as int, cc.nc as int)),
{
    let nw = cc.nc / 64 + if cc.nc % 64 != 0 { 1 } else { 0 };
    let q = nw / workers;
    let rm = nw % workers;
    let mut tasks: Vec<CustTask> = Vec::new();
    let mut w_lo: usize = 0;
    let mut k: usize = 0;
    while k < workers
        invariant
            cust_cols_ok(cc, sv, seg), 1 <= workers <= MAX_WORKERS, k <= workers,
            nw == cc.nc / 64 + if cc.nc % 64 != 0 { 1int } else { 0int }, q == nw / workers, rm == nw % workers,
            tasks@.len() == k,
            w_lo == split_at(nw as int, workers as int, k as int),
            forall|t: int| 0 <= t < k ==> (#[trigger] tasks@[t]).pre()
                && tasks@[t].cols == cc && tasks@[t].sv@ == sv && tasks@[t].seg@ == seg
                && tasks@[t].w_lo == split_at(nw as int, workers as int, t)
                && tasks@[t].w_hi == split_at(nw as int, workers as int, t + 1),
        decreases workers - k,
    {
        proof { lemma_split(nw as int, workers as int, k as int); }
        let w_hi = w_lo + q + if k < rm { 1 } else { 0 };
        assert(64 * w_hi <= cc.nc + 63);
        let task = CustTask { cols: cc, w_lo, w_hi, out: vec![0u64; w_hi - w_lo], sv: Ghost(sv), seg: Ghost(seg) };
        tasks.push(task);
        w_lo = w_hi;
        k = k + 1;
    }
    let ghost tasks0 = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => { return Err(e); },
    };
    let ghost outs0 = outs@;
    proof {
        assert forall|u: int| 0 <= u < workers implies cust_words_ok(#[trigger] outs0[u].0@, outs0[u].1, cc, sv, seg,
            split_at(nw as int, workers as int, u), split_at(nw as int, workers as int, u + 1)) by {
            assert(tasks0[u].post(outs0[u]));
        }
    }
    let mut outs = outs;
    let mut bits: Vec<u64> = Vec::new();
    let mut pos = true;
    let mut t: usize = 0;
    proof { lemma_split(nw as int, workers as int, 0); }
    while t < workers
        invariant
            cust_cols_ok(cc, sv, seg), 1 <= workers, t <= workers, outs0.len() == workers,
            nw == cc.nc / 64 + if cc.nc % 64 != 0 { 1int } else { 0int },
            outs@ == outs0.subrange(t as int, workers as int),
            bits@.len() == split_at(nw as int, workers as int, t as int),
            forall|u: int| 0 <= u < workers ==> cust_words_ok(#[trigger] outs0[u].0@, outs0[u].1, cc, sv, seg,
                split_at(nw as int, workers as int, u), split_at(nw as int, workers as int, u + 1)),
            forall|r: int| 0 <= r < 64 * split_at(nw as int, workers as int, t as int) && r < n_c(sv) ==>
                #[trigger] word_bit(bits@, r) == (cseg(sv, r) == seg),
            pos ==> forall|r: int| 0 <= r < 64 * split_at(nw as int, workers as int, t as int) && r < n_c(sv) ==>
                #[trigger] ck(sv)[r] as int == cc.base + r,
        decreases workers - t,
    {
        proof { lemma_split(nw as int, workers as int, t as int); }
        let ghost (wl, wh) = (split_at(nw as int, workers as int, t as int), split_at(nw as int, workers as int, t + 1));
        let (mut w, p) = outs.remove(0);
        assert((w@, p) == (outs0[t as int].0@, outs0[t as int].1));
        let ghost bits0 = bits@;
        let ghost w0 = w@;
        assert(cust_words_ok(w0, p, cc, sv, seg, wl, wh));
        bits.append(&mut w);
        proof {
            assert(bits@ == bits0 + w0);
            assert forall|r: int| 0 <= r < 64 * wh && r < n_c(sv) implies #[trigger] word_bit(bits@, r) == (cseg(sv, r) == seg) by {
                if r < 64 * wl {
                    assert(word_bit(bits0, r) == (cseg(sv, r) == seg));
                    assert(r / 64 < wl);
                    assert(bits@[r / 64] == bits0[r / 64]);
                } else {
                    assert(r / 64 >= wl);
                    assert(bits@[r / 64] == w0[r / 64 - wl]);
                    assert(bit(w0[r / 64 - wl], (r % 64) as u64) == (cseg(sv, r) == seg));
                }
            }
            if pos && p {
                assert forall|r: int| 0 <= r < 64 * wh && r < n_c(sv) implies #[trigger] ck(sv)[r] as int == cc.base + r by {
                    if r >= 64 * wl {
                        assert(ck(sv)[r] as int == cc.base + r);
                    }
                }
            }
            assert(outs@ == outs0.subrange(t + 1, workers as int));
        }
        pos = pos && p;
        t = t + 1;
    }
    proof {
        lemma_split(nw as int, workers as int, (workers - 1) as int);
        assert(cc.nc <= 64 * nw);
        if pos {
            assert forall|r: int| 0 <= r < cc.nc implies #[trigger] ck(sv)[r] as int == cc.base + r && r / 64 < bits@.len() by {
                assert(r < 64 * nw);
            }
            assert forall|r: int| 0 <= r < cc.nc implies #[trigger] word_bit(bits@, r) == (cseg(sv, r) == seg) by {
                assert(r < 64 * nw);
            }
        }
    }
    Ok((bits, pos))
}

/// The lineitem scan in `workers` tasks (each with the top 10 of its interior runs) and their combination into the
/// top 10 groups: `Some` when every task's checks held and the runs were in order.
pub fn scan_pass(c: ScanCols, bits: Vec<u64>, workers: usize, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>,
    Ghost(seg): Ghost<Seq<u8>>, Ghost(dl): Ghost<int>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Result<Option<(Vec<usize>, Vec<i128>)>, WorkerFailure>)
    requires
        scan_cols_ok(c, sv, seg, dl), cust_bits_ok(bits@, sv, seg, c.cbase as int, c.nc as int),
        1 <= workers <= MAX_WORKERS,
        seg == seg_of(ps), dl == dl_of(ps),
    ensures r matches Ok(Some((sel, ss))) ==> fast_ok(sel@, ss@, sv, ps),
{
    let shared = Arc::new(bits);
    let nl = c.nl;
    let q = nl / workers;
    let rm = nl % workers;
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut lo: usize = 0;
    let mut k: usize = 0;
    while k < workers
        invariant
            scan_cols_ok(c, sv, seg, dl), cust_bits_ok(shared@, sv, seg, c.cbase as int, c.nc as int),
            1 <= workers <= MAX_WORKERS, k <= workers, nl == c.nl, q == nl / workers, rm == nl % workers,
            tasks@.len() == k,
            lo == split_at(nl as int, workers as int, k as int),
            forall|t: int| 0 <= t < k ==> (#[trigger] tasks@[t]).pre()
                && tasks@[t].sv@ == sv && tasks@[t].seg@ == seg && tasks@[t].dl@ == dl
                && tasks@[t].lo == split_at(nl as int, workers as int, t)
                && tasks@[t].hi == split_at(nl as int, workers as int, t + 1),
        decreases workers - k,
    {
        proof { lemma_split(nl as int, workers as int, k as int); }
        let hi = lo + q + if k < rm { 1 } else { 0 };
        let task = ScanTask {
            cols: c, bits: shared.clone(), lo, hi,
            top: FixTop { ti: vec![0usize; 10], ts: vec![0i128; 10], td: vec![0i32; 10], to: vec![0usize; 10], k: 0 },
            // one worker is latency bound: read the customer keys of a block in order; more workers are bandwidth
            // bound: read only the candidates' keys
            seqc: workers == 1, ocb: vec![0i64; 65],
            sv: Ghost(sv), seg: Ghost(seg), dl: Ghost(dl),
        };
        tasks.push(task);
        lo = hi;
        k = k + 1;
    }
    let ghost tasks0 = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => { return Err(e); },
    };
    let ghost bounds = Seq::new((workers + 1) as nat, |t: int| split_at(nl as int, workers as int, t));
    // every task must have passed its checks
    let mut t: usize = 0;
    while t < outs.len()
        invariant t <= outs@.len(), forall|u: int| 0 <= u < t ==> (#[trigger] outs@[u]).ok,
        decreases outs@.len() - t,
    {
        if !outs[t].ok {
            return Ok(None);
        }
        t = t + 1;
    }
    proof {
        lemma_split(nl as int, workers as int, 0);
        assert forall|u: int| 0 <= u < bounds.len() - 1 implies #[trigger] bounds[u] <= bounds[u + 1] by {
            lemma_split(nl as int, workers as int, u);
        }
        assert(bounds.last() == nl as int) by {
            lemma_split(nl as int, workers as int, (workers - 1) as int);
        }
        assert forall|u: int| 0 <= u < outs@.len() implies #[trigger] outs@[u].ok
            && scan_out_ok(outs@[u], sv, seg, dl, bounds[u], bounds[u + 1]) && ltop_ok(outs@[u], sv) by {
            assert(tasks0[u].post(outs@[u]));
        }
    }
    Ok(combine(&outs, c.odate, Ghost(bounds), Ghost(sv), Ghost(seg), Ghost(dl), Ghost(ps)))
}

} // verus!
