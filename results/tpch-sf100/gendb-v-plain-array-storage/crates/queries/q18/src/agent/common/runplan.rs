//! The parallel driver of `common::runscan`: split the rows into ranges whose first key differs from the key
//! before them, scan them in parallel (`RunTask`), and join the states in range order (`lemma_join`); a task whose
//! buffer filled up is continued on the calling thread (`continue_serial`). When the keys are not in ascending
//! runs (a task reports `Unsorted`, or a range does not start above its predecessor's last key), the general
//! serial path (`scan_general`) answers instead: for every first occurrence of a key, a pass summing its values.
//! The result is the exact list of keys whose value sum exceeds the threshold (`hits_all`).
//! General: no query, table or column is named.
use vstd::prelude::*;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS, WorkerTask, fork_join};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::TaskBuffer;
use crate::agent::common::keysum::*;
use crate::agent::common::runscan::*;

verus! {

/// Slots of one task's output buffer (a full buffer is continued on the calling thread).
pub const BUF_CAP: usize = 4096;

/// Fewest rows per task worth a thread.
pub const MIN_TASK_ROWS: usize = 1048576;

/// The global state of the rows `0..pos` (the join of the ranges scanned so far).
pub open spec fn global_ok(keys: Seq<i64>, vals: Seq<i128>, thr: int, pos: int, cur: i64, csum: int, res: Seq<Hit>) -> bool {
    scan_inv(keys, vals, thr, 0, pos, cur, csum, res)
}

/// Start of task `t` of `nt` over `n` rows: `t * n / nt` (at least `prev`), moved forward past the rows whose key
/// equals their predecessor's, so that a run of equal keys is not split (a split is detected by the join anyway).
fn task_start(keys: &'static [i64], n: usize, t: usize, nt: usize, prev: usize) -> (s: usize)
    requires keys@.len() == n, 1 <= t < nt <= MAX_WORKERS, prev <= n,
    ensures prev <= s <= n,
{
    let q = n / nt;
    proof {
        assert(q * t <= q * nt) by (nonlinear_arith) requires t < nt, q >= 0;
        assert(q * nt <= n) by (nonlinear_arith) requires q == n / nt, nt > 0, n >= 0;
    }
    let base = q * t;
    let mut s = if base < prev { prev } else { base };
    if s > n {
        s = n;
    }
    while s < n && s > 0 && keys[s] == keys[s - 1]
        invariant prev <= s <= n, keys@.len() == n,
        decreases n - s,
    {
        s = s + 1;
    }
    s
}

/// Continue the global state from `pos` to `hi` on the calling thread, appending to `res`; `None` when the keys
/// are not in ascending runs.
fn continue_serial(keys: &'static [i64], vals: &'static [i128], thr: i128, hi: usize, res: &mut Vec<Hit>,
    pos: usize, cur: i64, csum: i128) -> (r: Option<(i64, i128)>)
    requires
        0 < pos <= hi <= keys@.len(), vals@.len() == keys@.len(), vals_bounded(vals@),
        global_ok(keys@, vals@, thr as int, pos as int, cur, csum as int, old(res)@),
    ensures
        r matches Some(st) ==> global_ok(keys@, vals@, thr as int, hi as int, st.0, st.1 as int, final(res)@),
{
    let mut pos = pos;
    let mut cur = cur;
    let mut csum = csum;
    while pos < hi
        invariant
            0 < pos <= hi <= keys@.len(), vals@.len() == keys@.len(), vals_bounded(vals@),
            global_ok(keys@, vals@, thr as int, pos as int, cur, csum as int, res@),
        decreases hi - pos,
    {
        let task = RunTask {
            keys, vals, start: pos, hi, cur, csum, thr,
            buf: TaskBuffer::new(BUF_CAP, Hit { key: 0, sum: 0 }),
            lo: Ghost(0), hs0: Ghost(res@),
        };
        let out = task.run();
        match out.end {
            ScanEnd::Unsorted => { return None; },
            _ => {},
        }
        let ghost before = res@;
        let mut more = out.buf.into_vec();
        res.append(&mut more);
        proof {
            assert(res@ == before + out.buf.view());
        }
        pos = out.pos;
        cur = out.cur;
        csum = out.csum;
    }
    Some((cur, csum))
}

/// The exact answer over rows `0..n` by the general serial path: for each first occurrence of a key (no earlier
/// row holds it), one pass sums the key's values over all rows. Any row order; quadratic time.
pub fn scan_general(keys: &'static [i64], vals: &'static [i128], n: usize, thr: i128) -> (hs: Vec<Hit>)
    requires keys@.len() == n, vals@.len() == n, vals_bounded(vals@),
    ensures hits_all(keys@, vals@, thr as int, 0, n as int, hs@),
{
    let mut res: Vec<Hit> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            keys@.len() == n, vals@.len() == n, vals_bounded(vals@), i <= n,
            hits_distinct(res@),
            hits_sound(keys@, vals@, thr as int, 0, n as int, res@),
            forall|t: int| 0 <= t < res@.len() ==> kcount(keys@, (#[trigger] res@[t]).key, 0, i as int) > 0,
            forall|v: i64| kcount(keys@, v, 0, i as int) > 0 && ksum(keys@, vals@, v, 0, n as int) > thr
                ==> #[trigger] has_hit(res@, v),
        decreases n - i,
    {
        let k = keys[i];
        // is row i the first occurrence of k?
        let mut j: usize = 0;
        let mut seen = false;
        while j < i
            invariant
                keys@.len() == n, i < n, j <= i, k == keys@[i as int],
                seen ==> exists|q: int| 0 <= q < i && keys@[q] == k,
                !seen ==> forall|q: int| 0 <= q < j ==> keys@[q] != k,
            decreases i - j,
        {
            if keys[j] == k {
                seen = true;
                j = i;
            } else {
                j = j + 1;
            }
        }
        proof {
            assert forall|v: i64| #[trigger] kcount(keys@, v, 0, i as int + 1) == kcount(keys@, v, 0, i as int)
                + if keys@[i as int] == v { 1nat } else { 0nat } by {
                lemma_k_step(keys@, vals@, v, 0, i as int);
            }
        }
        if !seen {
            // the sum of k over all rows
            let mut s: i128 = 0;
            let mut m: usize = 0;
            while m < n
                invariant
                    keys@.len() == n, vals@.len() == n, vals_bounded(vals@), m <= n,
                    s as int == ksum(keys@, vals@, k, 0, m as int),
                decreases n - m,
            {
                proof {
                    assert forall|q: int| 0 <= q < m implies -val_bound() <= #[trigger] vals@[q] <= val_bound() by {}
                    lemma_k_bound(keys@, vals@, k, 0, m as int, val_bound());
                    let c = kcount(keys@, k, 0, m as int) as int;
                    assert(c * val_bound() <= 0x1000_0000_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
                        requires 0 <= c <= m, m <= usize::MAX, val_bound() == 1_000_000_000_000_000;
                    assert(-val_bound() <= vals@[m as int] <= val_bound());
                    lemma_k_step(keys@, vals@, k, 0, m as int);
                }
                if keys[m] == k {
                    s = s + vals[m];
                }
                m = m + 1;
            }
            proof {
                lemma_k_witness(keys@, k, 0, n as int);
                assert(0 <= i < n && keys@[i as int] == k);
                assert forall|q: int| 0 <= q < i implies keys@[q] != k by {}
                lemma_k_absent(keys@, vals@, k, 0, i as int);
            }
            if s > thr {
                let ghost before = res@;
                res.push(Hit { key: k, sum: s });
                proof {
                    let h = Hit { key: k, sum: s };
                    assert(res@ == before.push(h));
                    assert forall|t: int| 0 <= t < before.len() implies (#[trigger] before[t]).key != k by {
                        assert(kcount(keys@, before[t].key, 0, i as int) > 0);
                    }
                    assert forall|a: int, b: int| 0 <= a < b < res@.len() implies res@[a].key != res@[b].key by {
                        if b < before.len() { assert(res@[a] == before[a] && res@[b] == before[b]); } else { assert(res@[a] == before[a]); }
                    }
                    assert forall|t: int| 0 <= t < res@.len() implies {
                        &&& (#[trigger] res@[t]).sum as int == ksum(keys@, vals@, res@[t].key, 0, n as int)
                        &&& res@[t].sum > thr
                        &&& kcount(keys@, res@[t].key, 0, n as int) > 0
                    } by {
                        if t < before.len() { assert(res@[t] == before[t]); }
                    }
                    assert forall|t: int| 0 <= t < res@.len() implies kcount(keys@, (#[trigger] res@[t]).key, 0, i as int + 1) > 0 by {
                        if t < before.len() { assert(res@[t] == before[t]); }
                    }
                    assert forall|v: i64| kcount(keys@, v, 0, i as int + 1) > 0 && ksum(keys@, vals@, v, 0, n as int) > thr
                        implies #[trigger] has_hit(res@, v) by {
                        if v == k {
                            assert(res@[before.len() as int].key == v);
                        } else {
                            assert(has_hit(before, v));
                            let t = choose|t: int| 0 <= t < before.len() && #[trigger] before[t].key == v;
                            assert(res@[t] == before[t]);
                        }
                    }
                }
            } else {
                proof {
                    assert forall|v: i64| kcount(keys@, v, 0, i as int + 1) > 0 && ksum(keys@, vals@, v, 0, n as int) > thr
                        implies #[trigger] has_hit(res@, v) by {
                        if v == k {
                        }
                    }
                }
            }
        } else {
            proof {
                let q = choose|q: int| 0 <= q < i && keys@[q] == k;
                lemma_k_witness(keys@, k, 0, i as int);
                assert forall|v: i64| kcount(keys@, v, 0, i as int + 1) > 0 && ksum(keys@, vals@, v, 0, n as int) > thr
                    implies #[trigger] has_hit(res@, v) by {
                    if v == k {
                        assert(kcount(keys@, v, 0, i as int) > 0);
                    }
                }
            }
        }
        proof {
            assert forall|t: int| 0 <= t < res@.len() implies kcount(keys@, (#[trigger] res@[t]).key, 0, i as int + 1) > 0 by {
                assert(kcount(keys@, res@[t].key, 0, i as int + 1) >= kcount(keys@, res@[t].key, 0, i as int));
            }
        }
        i = i + 1;
    }
    res
}

/// The ranges of the tasks: non-empty, contiguous, covering `0..end`.
pub open spec fn ranges_ok(ranges: Seq<(usize, usize)>, end: int) -> bool {
    &&& (ranges.len() == 0 ==> end == 0)
    &&& (ranges.len() > 0 ==> ranges[0].0 == 0 && ranges.last().1 == end)
    &&& forall|a: int| 0 <= a < ranges.len() ==> (#[trigger] ranges[a]).0 < ranges[a].1
    &&& forall|a: int| 0 < a < ranges.len() ==> #[trigger] ranges[a].0 == ranges[a - 1].1
}

/// Task `a` scans its range from a fresh state.
pub open spec fn task_ok(t: RunTask, r: (usize, usize), keys: Seq<i64>, vals: Seq<i128>, thr: i128) -> bool {
    &&& t.pre()
    &&& t.start == r.0 && t.hi == r.1
    &&& t.lo@ == r.0 as int && t.hs0@ == Seq::<Hit>::empty()
    &&& t.keys@ == keys && t.vals@ == vals && t.thr == thr
}

/// Split `0..n` into at most `nt` non-empty ranges, each starting where its key differs from the previous row's.
fn make_ranges(keys: &'static [i64], n: usize, nt: usize) -> (ranges: Vec<(usize, usize)>)
    requires keys@.len() == n, 1 <= nt <= MAX_WORKERS,
    ensures ranges_ok(ranges@, n as int), ranges@.len() <= nt,
        forall|a: int| 0 <= a < ranges@.len() ==> (#[trigger] ranges@[a]).1 <= n,
{
    let mut ranges: Vec<(usize, usize)> = Vec::new();
    let mut prev: usize = 0;
    let mut t: usize = 1;
    while t <= nt
        invariant
            keys@.len() == n, 1 <= nt <= MAX_WORKERS, 1 <= t <= nt + 1, prev <= n,
            ranges_ok(ranges@, prev as int), ranges@.len() < t,
            t == nt + 1 ==> prev == n,
            forall|a: int| 0 <= a < ranges@.len() ==> (#[trigger] ranges@[a]).1 <= n,
        decreases nt + 1 - t,
    {
        let e = if t == nt { n } else { task_start(keys, n, t, nt, prev) };
        if prev < e {
            let ghost before = ranges@;
            ranges.push((prev, e));
            proof {
                assert(ranges@ == before.push((prev, e)));
                assert forall|a: int| 0 < a < ranges@.len() implies #[trigger] ranges@[a].0 == ranges@[a - 1].1 by {
                    if a < before.len() {
                        assert(ranges@[a] == before[a] && ranges@[a - 1] == before[a - 1]);
                    } else {
                        assert(ranges@[a - 1] == before.last());
                    }
                }
                assert forall|a: int| 0 <= a < ranges@.len() implies (#[trigger] ranges@[a]).0 < ranges@[a].1 by {
                    if a < before.len() { assert(ranges@[a] == before[a]); }
                }
                assert forall|a: int| 0 <= a < ranges@.len() implies (#[trigger] ranges@[a]).1 <= n by {
                    if a < before.len() { assert(ranges@[a] == before[a]); }
                }
            }
            prev = e;
        }
        t = t + 1;
    }
    ranges
}

/// Join the output `o` of the task over `s..e` into the global state of `0..s` (`first`: the task at row 0, whose
/// state is the global state), continuing it on the calling thread when its buffer filled up; `None` when the keys
/// are not in ascending runs.
fn absorb(keys: &'static [i64], vals: &'static [i128], thr: i128, s: usize, e: usize, first: bool, o: RunOut,
    res: &mut Vec<Hit>, cur: i64, csum: i128, Ghost(t): Ghost<RunTask>) -> (r: Option<(i64, i128)>)
    requires
        vals@.len() == keys@.len(), vals_bounded(vals@), s < e <= keys@.len(),
        t.post(o), task_ok(t, (s, e), keys@, vals@, thr),
        first ==> s == 0 && old(res)@.len() == 0,
        !first ==> 0 < s && global_ok(keys@, vals@, thr as int, s as int, cur, csum as int, old(res)@),
    ensures
        r matches Some(st) ==> global_ok(keys@, vals@, thr as int, e as int, st.0, st.1 as int, final(res)@),
{
    match o.end {
        ScanEnd::Unsorted => { return None; },
        _ => {},
    }
    proof {
        assert(scan_inv(keys@, vals@, thr as int, s as int, o.pos as int, o.cur, o.csum as int, Seq::<Hit>::empty() + o.buf.view()));
        assert(Seq::<Hit>::empty() + o.buf.view() =~= o.buf.view());
        assert(o.pos > s);
    }
    if !first {
        // the previous range's last run is complete when this range starts with a larger key
        if keys[s] <= cur {
            return None;
        }
        let ghost res1 = res@;
        if csum > thr {
            res.push(Hit { key: cur, sum: csum });
        }
        let ghost mid = res@;
        let mut more = o.buf.into_vec();
        res.append(&mut more);
        proof {
            assert(mid == if csum > thr { res1.push(Hit { key: cur, sum: csum }) } else { res1 });
            lemma_join(keys@, vals@, thr as int, s as int, o.pos as int, cur, csum as int, res1, o.cur, o.csum as int, o.buf.view());
            assert(res@ == mid + o.buf.view());
        }
    } else {
        let mut more = o.buf.into_vec();
        res.append(&mut more);
        proof {
            assert(res@ =~= o.buf.view());
        }
    }
    match o.end {
        ScanEnd::Full => continue_serial(keys, vals, thr, e, res, o.pos, o.cur, o.csum),
        _ => Some((o.cur, o.csum)),
    }
}

/// The exact answer over rows `0..n`, scanned in at most `workers` parallel ranges (or by the general path when
/// the keys are not in ascending runs).
pub fn scan_all(keys: &'static [i64], vals: &'static [i128], n: usize, thr: i128, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<Vec<Hit>, WorkerFailure>)
    requires keys@.len() == n, vals@.len() == n, vals_bounded(vals@), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(hs) ==> hits_all(keys@, vals@, thr as int, 0, n as int, hs@),
{
    match scan_runs(keys, vals, n, thr, workers, dispatch) {
        Ok(Some(hs)) => Ok(hs),
        Ok(None) => Ok(scan_general(keys, vals, n, thr)),
        Err(e) => Err(e),
    }
}

/// The ascending-runs path: `Some` exact answer, or `None` when the keys are not in ascending runs.
fn scan_runs(keys: &'static [i64], vals: &'static [i128], n: usize, thr: i128, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<Option<Vec<Hit>>, WorkerFailure>)
    requires keys@.len() == n, vals@.len() == n, vals_bounded(vals@), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(Some(hs)) ==> hits_all(keys@, vals@, thr as int, 0, n as int, hs@),
{
    if n == 0 {
        let e: Vec<Hit> = Vec::new();
        proof {
            assert forall|v: i64| kcount(keys@, v, 0, 0) > 0 && ksum(keys@, vals@, v, 0, 0) > thr implies #[trigger] has_hit(e@, v) by {
                lemma_k_empty(keys@, vals@, v, 0);
            }
        }
        return Ok(Some(e));
    }
    // task count: one per worker, at least MIN_TASK_ROWS rows each
    let by_rows = n / MIN_TASK_ROWS;
    let mut nt = if by_rows < workers { by_rows } else { workers };
    if nt == 0 {
        nt = 1;
    }
    let ranges = make_ranges(keys, n, nt);
    let ntasks = ranges.len();
    // one task per range
    let mut tasks: Vec<RunTask> = Vec::new();
    let mut a: usize = 0;
    while a < ntasks
        invariant
            ntasks == ranges@.len(), a <= ntasks, tasks@.len() == a,
            keys@.len() == n, vals@.len() == n, vals_bounded(vals@),
            ranges_ok(ranges@, n as int),
            forall|b: int| 0 <= b < ranges@.len() ==> (#[trigger] ranges@[b]).1 <= n,
            forall|b: int| 0 <= b < a ==> task_ok(#[trigger] tasks@[b], ranges@[b], keys@, vals@, thr),
        decreases ntasks - a,
    {
        let (s, e) = ranges[a];
        proof {
            assert(ranges@[a as int].0 < ranges@[a as int].1);
            lemma_start(keys@, vals@, thr as int, s as int);
        }
        tasks.push(RunTask {
            keys, vals, start: s, hi: e, cur: keys[s], csum: 0, thr,
            buf: TaskBuffer::new(BUF_CAP, Hit { key: 0, sum: 0 }),
            lo: Ghost(s as int), hs0: Ghost(Seq::empty()),
        });
        a = a + 1;
    }
    let ghost specs = tasks@;
    assert(ntasks > 0);
    let outs: Vec<RunOut> = if ntasks == 1 {
        let mut tasks = tasks;
        let task = tasks.pop().unwrap();
        assert(task == specs[0]);
        let out = task.run();
        let mut v: Vec<RunOut> = Vec::new();
        v.push(out);
        v
    } else {
        assert forall|b: int| 0 <= b < tasks@.len() implies #[trigger] tasks@[b].pre() by {
            assert(task_ok(tasks@[b], ranges@[b], keys@, vals@, thr));
        }
        match fork_join(dispatch, tasks) {
            Ok(v) => v,
            Err(e) => { return Err(e); },
        }
    };
    assert(outs@.len() == ntasks);
    assert(forall|b: int| 0 <= b < ntasks ==> #[trigger] specs[b].post(outs@[b]));
    // reverse the outputs, so that popping takes them in range order
    let ghost outs0 = outs@;
    let mut outs = outs;
    let mut rev: Vec<RunOut> = Vec::new();
    while outs.len() > 0
        invariant
            outs@.len() + rev@.len() == ntasks, outs0.len() == ntasks,
            outs@ == outs0.subrange(0, outs@.len() as int),
            forall|j: int| 0 <= j < rev@.len() ==> #[trigger] rev@[j] == outs0[ntasks - 1 - j],
        decreases outs.len(),
    {
        let ghost before = rev@;
        let o = outs.pop().unwrap();
        rev.push(o);
        proof {
            assert forall|j: int| 0 <= j < rev@.len() implies #[trigger] rev@[j] == outs0[ntasks - 1 - j] by {
                if j < before.len() { assert(rev@[j] == before[j]); }
            }
        }
    }
    // join in range order
    let mut res: Vec<Hit> = Vec::new();
    let mut cur: i64 = 0;
    let mut csum: i128 = 0;
    let mut k: usize = 0;
    while k < ntasks
        invariant
            k <= ntasks, ntasks == ranges@.len(), rev@.len() == ntasks - k, outs0.len() == ntasks, specs.len() == ntasks,
            forall|j: int| 0 <= j < rev@.len() ==> #[trigger] rev@[j] == outs0[ntasks - 1 - j],
            forall|b: int| 0 <= b < ntasks ==> #[trigger] specs[b].post(outs0[b]),
            forall|b: int| 0 <= b < ntasks ==> task_ok(#[trigger] specs[b], ranges@[b], keys@, vals@, thr),
            keys@.len() == n, vals@.len() == n, vals_bounded(vals@),
            ranges_ok(ranges@, n as int),
            forall|b: int| 0 <= b < ranges@.len() ==> (#[trigger] ranges@[b]).1 <= n,
            k > 0 ==> global_ok(keys@, vals@, thr as int, ranges@[k - 1].1 as int, cur, csum as int, res@),
            k == 0 ==> res@.len() == 0,
        decreases ntasks - k,
    {
        let o = rev.pop().unwrap();
        let (s, e) = ranges[k];
        proof {
            assert(o == outs0[k as int]);
            assert(specs[k as int].post(o));
            assert(task_ok(specs[k as int], ranges@[k as int], keys@, vals@, thr));
            if k > 0 {
                assert(ranges@[k as int].0 == ranges@[k as int - 1].1);
            }
        }
        match absorb(keys, vals, thr, s, e, k == 0, o, &mut res, cur, csum, Ghost(specs[k as int])) {
            Some(st) => {
                cur = st.0;
                csum = st.1;
            },
            None => { return Ok(None); },
        }
        k = k + 1;
    }
    let last = Hit { key: cur, sum: csum };
    proof {
        assert(ranges@[ntasks - 1].1 == n);
        lemma_finish(keys@, vals@, thr as int, 0, n as int, cur, csum as int, res@, last);
    }
    let ghost res0 = res@;
    if csum > thr {
        res.push(last);
    }
    proof {
        lemma_exact_all(keys@, vals@, thr as int, 0, n as int, res@);
    }
    Ok(Some(res))
}

} // verus!
