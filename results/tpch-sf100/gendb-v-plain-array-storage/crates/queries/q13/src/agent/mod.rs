//! TPC-H Q13 (customer distribution) over the flat `orders` and `customer` storages: per number of orders `c_count`
//! a customer has whose comment is `NOT LIKE $1`, the number of customers (`custdist`), by `custdist DESC,
//! c_count DESC`.
//!
//! Plan of a call (`query`):
//! 1. read `o_custkey`, `o_comment` and `c_custkey` as whole parts (`tables::read_cols`);
//! 2. the fast path (`fast_hist`), when `$1` is `%s1%...%sk%` with plain ASCII segments
//!    (`common::segments::parse_segments`), the tables are below 2^32 rows and the customer keys are
//!    `base, base + 1, ...` (checked by phase 2):
//!    - the scan's filter literal (`common::text_rows::choose_gram`): the 4-byte part of a segment that is rarest
//!      in a sample of the comment bytes;
//!    - phase 1 (`scan`, one task per orders range, at most `P1MAX` tasks): per block of rows, the rows whose
//!      comment holds the segments in order (`common::text_rows::match_flags`, a windowed byte scan for the filter
//!      literal) set their bit in the task's match bitmap and the block's bytes are tested for ASCII; then one
//!      tight pass appends the customer index of every other row to its bucket of `SPAN` customers;
//!    - phase 2 (`count`, one task per range of buckets): per bucket, the number of counted orders of each customer,
//!      tallied into a histogram of counts, with the customer keys checked;
//!    - the histograms of the phase-2 tasks add up (`count::lemma_hcnt_add`);
//! 3. otherwise the general path (`general`): the verified `LIKE` on every row and a hash map of customer keys;
//! 4. the answer rows from the histogram (`answer::finish_rows`), or the statement's SQL error.
//!
//! Proof: the histogram is `hcount` of the normal form (`fast::lemma_fast_facts`), whose rows the statement's
//! meaning is (`denote`, `inner`, `answer`); the errors are `errors`.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS, WorkerTask, fork_join};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::agent::common::segments::*;
use crate::agent::common::text_rows::*;
use crate::agent::common::split::*;
use crate::agent::common::zeroed::*;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::scan::*;
use crate::agent::count::*;
use crate::agent::answer::*;
use crate::agent::fast::*;
use crate::agent::general::*;

pub mod common;
pub mod tables;
pub mod normal;
pub mod denote;
pub mod inner;
pub mod answer;
pub mod errors;
pub mod fast;
pub mod scan;
pub mod count;
pub mod general;

verus! {

/// Smallest bucket buffer of a phase-1 task, in `u16` slots: 33.6 MB, above the C allocator's largest
/// memory-mapping threshold, so the zeroed buffer is fresh mapped memory (no clearing pass on the calling thread).
pub const MIN_BUF: usize = 16_800_000;

/// Most phase-1 tasks (every worker: the byte scan gains from both hardware threads of a core).
pub const P1MAX: usize = 64;

/// The facts the phase-1 tasks share, for task `k` of `nt` over `no` rows.
pub open spec fn scan_task_ok(task: ScanTask, c: Cols, ss: Seq<Seq<u8>>, base: i64, nb: usize, nt: int, k: int) -> bool {
    &&& task.pre()
    &&& task.c == c && task.ss@ == ss && task.base == base && task.nb == nb
    &&& task.lo == split(c.no as int, nt, k) && task.hi == split(c.no as int, nt, k + 1)
}

/// The range `split(n, k, t) .. split(n, k, t + 1)` holding `x < n`.
proof fn lemma_split_find(n: int, k: int, x: int) -> (t: int)
    requires n >= 0, k > 0, 0 <= x < n,
    ensures 0 <= t < k, split(n, k, t) <= x < split(n, k, t + 1),
{
    lemma_split(n, k, 0, k);
    lemma_split_find_from(n, k, x, 0)
}

/// `lemma_split_find`, searching from range `s` (`split(n, k, s) <= x`).
proof fn lemma_split_find_from(n: int, k: int, x: int, s: int) -> (t: int)
    requires n >= 0, k > 0, 0 <= x < n, 0 <= s < k, split(n, k, s) <= x,
    ensures 0 <= t < k, split(n, k, t) <= x < split(n, k, t + 1),
    decreases k - s,
{
    lemma_split(n, k, s, s + 1);
    lemma_split(n, k, s + 1, k);
    if x < split(n, k, s + 1) {
        s
    } else {
        lemma_split_find_from(n, k, x, s + 1)
    }
}

/// Phase 1: the buckets of every orders row, `None` when a task stops.
fn phase1(c: &Cols, segs: &Arc<Segs>, gram: Gram, base: i64, nb: usize, nt: usize, dispatch: &mut Dispatch,
    Ghost(g): Ghost<Seq<u8>>, Ghost(ss): Ghost<Seq<Seq<u8>>>) -> (r: Result<Option<Vec<ScanOut>>, QueryError>)
    requires
        scan_pre(*c, &**segs, ss, base, nb), gram_view_ok(gram, ss, g),
        1 <= nt <= MAX_WORKERS, c.no <= u32::MAX, nb <= 65537,
    ensures
        r matches Ok(Some(outs)) ==> outs_ok(*c, ss, base as int, nb as int, outs@, nt as int)
            && forall|x: int| 0 <= x < c.no ==> #[trigger] ascii(val(c.offs@, c.bytes@, x)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let no = c.no;
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut t: usize = 0;
    while t < nt
        invariant
            t <= nt, 1 <= nt <= MAX_WORKERS, no == c.no, no <= u32::MAX, 1 <= nb <= 65537,
            scan_pre(*c, &**segs, ss, base, nb), gram_view_ok(gram, ss, g), tasks@.len() == t,
            forall|k: int| 0 <= k < t ==> #[trigger] scan_task_ok(tasks@[k], *c, ss, base, nb, nt as int, k),
        decreases nt - t,
    {
        proof { lemma_split(no as int, nt as int, t as int, t + 1); lemma_split(no as int, nt as int, t + 1, nt as int); }
        let lo = split_exec(no, nt, t);
        let hi = split_exec(no, nt, t + 1);
        let rows = hi - lo;
        let per = rows / nb;
        if per > (usize::MAX - 64) / 2 {
            return Ok(None);
        }
        let cap = per + per / 4 + 64;
        if cap > usize::MAX / nb {
            return Ok(None);
        }
        proof {
            assert(nb * cap <= nb * (usize::MAX / nb)) by (nonlinear_arith) requires nb >= 1, cap <= usize::MAX / nb;
            assert(nb * (usize::MAX / nb) <= usize::MAX) by (nonlinear_arith) requires nb >= 1;
        }
        let need = nb * cap;
        let buf = zeros_u16(if need > MIN_BUF { need } else { MIN_BUF });
        let fill = zeros_usize(nb);
        let flags = zeros_u8(BLOCK);
        // one match bit per row of the range
        let bits = zeros_u64(rows / 64 + 1);
        let task = ScanTask { c: *c, segs: segs.clone(), gram, lo, hi, base, nb, cap, buf, fill, flags, bits, g: Ghost(g),
            ss: Ghost(ss) };
        tasks.push(task);
        t = t + 1;
    }
    let ghost tv = tasks@;
    proof {
        assert forall|k: int| 0 <= k < nt implies #[trigger] tasks@[k].pre() by {
            assert(scan_task_ok(tasks@[k], *c, ss, base, nb, nt as int, k));
        }
    }
    let outs = if nt == 1 {
        let task = tasks.pop().unwrap();
        assert(task == tv[0]);
        let o = task.run();
        let mut v: Vec<ScanOut> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, tasks) {
            Ok(o) => o,
            Err(e) => { return Err(QueryError::WorkerFailed(e)); },
        }
    };
    assert(outs@.len() == nt && forall|k: int| 0 <= k < nt ==> #[trigger] tv[k].post(outs@[k]));
    let mut t: usize = 0;
    while t < nt
        invariant
            t <= nt, outs@.len() == nt, no == c.no,
            forall|k: int| 0 <= k < nt ==> #[trigger] tv[k].post(outs@[k]) && scan_task_ok(tv[k], *c, ss, base, nb, nt as int, k),
            forall|k: int| 0 <= k < t ==> (#[trigger] outs@[k]).ok,
        decreases nt - t,
    {
        if !outs[t].ok {
            return Ok(None);
        }
        t = t + 1;
    }
    proof {
        lemma_split(no as int, nt as int, 0, nt as int);
        assert forall|x: int| 0 <= x < c.no implies #[trigger] ascii(val(c.offs@, c.bytes@, x)) by {
            let k = lemma_split_find(no as int, nt as int, x);
            assert(tv[k].post(outs@[k]) && scan_task_ok(tv[k], *c, ss, base, nb, nt as int, k));
        }
        assert forall|k: int| 0 <= k < nt implies (#[trigger] outs@[k]).ok && bucket_ok(*c, ss, base as int, nb as int,
            outs@[k].cap as int, outs@[k].buf@, outs@[k].fill@, split(c.no as int, nt as int, k), split(c.no as int, nt as int, k + 1)) by {
            assert(tv[k].post(outs@[k]) && scan_task_ok(tv[k], *c, ss, base, nb, nt as int, k));
        }
    }
    Ok(Some(outs))
}

/// The facts the phase-2 tasks share, for task `k` of `np` over `nb` buckets.
pub open spec fn count_task_ok(task: CountTask, c: Cols, ss: Seq<Seq<u8>>, base: i64, nb: usize, np: int, k: int) -> bool {
    &&& task.pre()
    &&& task.c == c && task.ss@ == ss && task.base == base
    &&& task.b0 == split(nb as int, np, k) && task.b1 == split(nb as int, np, k + 1)
}

/// Phase 2 and the merge: the histogram of the counts of all customers, `None` when a task stops.
fn phase2(c: &Cols, outs: Vec<ScanOut>, nt: usize, nb: usize, base: i64, workers: usize, dispatch: &mut Dispatch,
    Ghost(ss): Ghost<Seq<Seq<u8>>>) -> (r: Result<Option<Vec<u64>>, QueryError>)
    requires
        outs_ok(*c, ss, base as int, nb as int, outs@, nt as int), c.no <= u32::MAX, c.nc <= u32::MAX,
        c.cck@.len() == c.nc, 1 <= workers <= MAX_WORKERS, 1 <= nb, nb * SPAN >= c.nc,
    ensures
        r matches Ok(Some(hist)) ==> count_post(*c, ss, base as int, hist@, 0, c.nc as int),
        r matches Err(e) ==> e is WorkerFailed,
{
    let nc = c.nc;
    let outs = Arc::new(outs);
    let np = if workers < nb { workers } else { nb };
    let mut tasks: Vec<CountTask> = Vec::new();
    let mut t: usize = 0;
    while t < np
        invariant
            t <= np, 1 <= np <= MAX_WORKERS, np <= nb, tasks@.len() == t,
            outs_ok(*c, ss, base as int, nb as int, outs@, nt as int), c.no <= u32::MAX, c.cck@.len() == c.nc,
            forall|k: int| 0 <= k < t ==> #[trigger] count_task_ok(tasks@[k], *c, ss, base, nb, np as int, k),
        decreases np - t,
    {
        proof { lemma_split(nb as int, np as int, t as int, t + 1); lemma_split(nb as int, np as int, t + 1, np as int); }
        let b0 = split_exec(nb, np, t);
        let b1 = split_exec(nb, np, t + 1);
        let task = CountTask { c: *c, outs: outs.clone(), nt, b0, b1, nb, base, cnt: zeros_u32(SPAN), hist: zeros_u64(HMAX),
            ss: Ghost(ss) };
        tasks.push(task);
        t = t + 1;
    }
    let ghost tv = tasks@;
    proof {
        assert forall|k: int| 0 <= k < np implies #[trigger] tasks@[k].pre() by {
            assert(count_task_ok(tasks@[k], *c, ss, base, nb, np as int, k));
        }
    }
    let couts = if np == 1 {
        let task = tasks.pop().unwrap();
        assert(task == tv[0]);
        let o = task.run();
        let mut v: Vec<CountOut> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, tasks) {
            Ok(o) => o,
            Err(e) => { return Err(QueryError::WorkerFailed(e)); },
        }
    };
    assert(couts@.len() == np && forall|k: int| 0 <= k < np ==> #[trigger] tv[k].post(couts@[k]));
    let mut hist = zeros_u64(HMAX);
    proof {
        lemma_split(nb as int, np as int, 0, np as int);
        assert(cust_lo(0, nc as int) == 0);
        assert forall|v: int| 0 <= v < HMAX implies #[trigger] hist@[v] as int == hcnt(*c, ss, base as int, v, 0, 0) by {}
    }
    let mut t: usize = 0;
    while t < np
        invariant
            t <= np, couts@.len() == np, nc == c.nc, nc <= u32::MAX, hist@.len() == HMAX, np <= nb, 1 <= np, nb * SPAN >= nc,
            forall|k: int| 0 <= k < np ==> #[trigger] tv[k].post(couts@[k]) && count_task_ok(tv[k], *c, ss, base, nb, np as int, k),
            count_post(*c, ss, base as int, hist@, 0, cust_lo(split(nb as int, np as int, t as int), nc as int)),
        decreases np - t,
    {
        let o = &couts[t];
        if !o.ok {
            return Ok(None);
        }
        proof { lemma_split(nb as int, np as int, t as int, t + 1); lemma_split(nb as int, np as int, t + 1, np as int); }
        let ghost mid_c = cust_lo(split(nb as int, np as int, t as int), nc as int);
        let ghost hi_c = cust_lo(split(nb as int, np as int, t + 1), nc as int);
        proof {
            assert(tv[t as int].post(couts@[t as int]) && count_task_ok(tv[t as int], *c, ss, base, nb, np as int, t as int));
            assert(count_post(*c, ss, base as int, o.hist@, mid_c, hi_c));
            assert(mid_c <= hi_c) by {
                assert(split(nb as int, np as int, t as int) * 65536 <= split(nb as int, np as int, t + 1) * 65536) by (nonlinear_arith)
                    requires split(nb as int, np as int, t as int) <= split(nb as int, np as int, t + 1);
            }
            assert(0 <= mid_c);
        }
        let ghost h0 = hist@;
        let mut v: usize = 0;
        while v < HMAX
            invariant
                v <= HMAX, hist@.len() == HMAX, o.hist@.len() == HMAX, nc <= u32::MAX, 0 <= mid_c <= hi_c <= nc,
                forall|w: int| 0 <= w < HMAX ==> #[trigger] h0[w] as int == hcnt(*c, ss, base as int, w, 0, mid_c),
                forall|w: int| 0 <= w < HMAX ==> #[trigger] o.hist@[w] as int == hcnt(*c, ss, base as int, w, mid_c, hi_c),
                forall|w: int| 0 <= w < v ==> #[trigger] hist@[w] as int == hcnt(*c, ss, base as int, w, 0, hi_c),
                forall|w: int| v <= w < HMAX ==> #[trigger] hist@[w] == h0[w],
            decreases HMAX - v,
        {
            proof {
                lemma_hcnt_add(*c, ss, base as int, v as int, 0, mid_c, hi_c);
                lemma_hcnt_bound(*c, ss, base as int, v as int, 0, hi_c);
            }
            hist[v] = hist[v] + o.hist[v];
            v = v + 1;
        }
        proof {
            assert forall|i: int| 0 <= i < hi_c implies #[trigger] tot(*c, ss, base as int, i) < HMAX by {
                if i >= mid_c { assert(o.hist@.len() == HMAX); }
            }
            assert forall|i: int| 0 <= i < hi_c implies #[trigger] c.cck@[i] as int == base as int + i by {}
        }
        t = t + 1;
    }
    proof {
        assert(cust_lo(nb as int, nc as int) == nc);
    }
    Ok(Some(hist))
}

/// The fast path: the histogram of the counts, `None` when one of its conditions fails (checked at run time).
fn fast_hist(c: &Cols, segs: Segs, workers: usize, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>,
    Ghost(ss): Ghost<Seq<Seq<u8>>>, Ghost(pat): Ghost<Seq<u8>>) -> (r: Result<Option<Vec<u64>>, QueryError>)
    requires cols_ok(*c, sv), 1 <= workers <= MAX_WORKERS, segs_view_ok(&segs, ss), seg_pattern(ss) == pat,
    ensures
        r matches Ok(Some(hist)) ==> likes_ok(sv, pat) && hist_facts(sv, pat, hist@),
        r matches Err(e) ==> e is WorkerFailed,
{
    let no = c.no;
    let nc = c.nc;
    if nc == 0 || no > 0xffff_ffff || nc > 0xffff_ffff {
        return Ok(None);
    }
    proof { reveal(parts_shape); }
    let base = c.cck[0];
    if (base as i128) + (nc as i128) > (i64::MAX as i128) + 1 {
        return Ok(None);
    }
    let nb: usize = nc / SPAN + 1;
    proof {
        assert forall|i: int| 0 <= i < nc implies bucket(i) < nb by {}
        assert(nb * SPAN >= nc);
    }
    let (gram, g) = choose_gram(c.bytes, c.nbytes, &segs, Ghost(ss));
    let segs = Arc::new(segs);
    let nt = if workers < P1MAX { workers } else { P1MAX };
    let outs = match phase1(c, &segs, gram, base, nb, nt, dispatch, g, Ghost(ss)) {
        Ok(Some(o)) => o,
        Ok(None) => { return Ok(None); },
        Err(e) => { return Err(e); },
    };
    let hist = match phase2(c, outs, nt, nb, base, workers, dispatch, Ghost(ss)) {
        Ok(Some(h)) => h,
        Ok(None) => { return Ok(None); },
        Err(e) => { return Err(e); },
    };
    proof {
        assert(fast_ok(*c, sv, ss, pat, base as int));
        lemma_fast_facts(*c, sv, ss, pat, base as int);
        assert forall|v: int| 0 <= v < hist@.len() implies #[trigger] hist@[v] <= i64::MAX by {
            lemma_hcnt_bound(*c, ss, base as int, v, 0, nc as int);
        }
        assert forall|v: int| 0 <= v < hist@.len() implies #[trigger] hist@[v] as int == hcount(sv, pat, v, n_c(sv)) by {
            assert(hist@[v] as int == hcnt(*c, ss, base as int, v, 0, nc as int));
        }
        assert forall|i: int| 0 <= i < n_c(sv) implies #[trigger] ccnt(sv, pat, i) < hist@.len() by {
            assert(tot(*c, ss, base as int, i) < HMAX);
        }
    }
    Ok(Some(hist))
}

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost ps = params@;
    let c = read_cols(stores, Ghost(sv));
    proof { assert(params.p0@ == pat_of(ps)); }
    if let Some((segs, ss)) = parse_segments(params.p0) {
        match fast_hist(&c, segs, workers, dispatch, Ghost(sv), ss, Ghost(params.p0@)) {
            Ok(Some(hist)) => {
                let rows = finish_rows(&hist, Ghost(sv), Ghost(ps));
                return Ok(Answer::Rows(rows));
            },
            Ok(None) => {},
            Err(e) => {
                return Err(e);
            },
        }
    }
    let a = general(&c, params.p0, Ghost(sv), Ghost(ps));
    Ok(a)
}

} // verus!
