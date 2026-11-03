//! The keys whose value sum exceeds a threshold (`SUM(val) > thr` per key), found by one scan over a key column
//! whose rows are grouped into ascending runs of equal keys (the scan checks the order and stops when it fails).
//!
//! State after rows `lo..i` (`scan_inv`): `cur` is the key of the last row (of row `lo` before any row), `csum` the
//! sum of `cur`'s values so far, every key read lies in `[keys[lo], cur]`, and `hits` lists, in strictly ascending
//! key order, every other key of the range whose sum exceeds `thr`, with that sum. When a run ends (the next key is
//! larger), its key and sum are appended if the sum exceeds `thr`. Because the keys ascend, an ended run is
//! complete: its key never comes back. The state of `0..h` and the state of a task over `h..i` whose first key is
//! larger than the first state's `cur` combine into the state of `0..i` (`lemma_join`), so the rows can be split
//! into ranges scanned in parallel (`RunTask`) and the states joined in range order.
//! General: no query, table or column is named.
use vstd::prelude::*;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::TaskBuffer;
use crate::agent::common::keysum::*;

verus! {

/// A key with the sum of its values.
#[derive(Clone, Copy)]
pub struct Hit {
    pub key: i64,
    pub sum: i128,
}

/// Bound of the absolute values (`|val| <= VAL_BOUND`, e.g. numeric(15, p) coefficients are below 10^15).
pub open spec fn val_bound() -> int { 1_000_000_000_000_000 }

/// Every value lies within the bound.
pub open spec fn vals_bounded(vals: Seq<i128>) -> bool {
    forall|j: int| 0 <= j < vals.len() ==> -val_bound() <= #[trigger] vals[j] <= val_bound()
}

/// The keys of `hs` ascend strictly.
pub open spec fn hits_ascending(hs: Seq<Hit>) -> bool {
    forall|a: int, b: int| 0 <= a < b < hs.len() ==> hs[a].key < hs[b].key
}

/// Some entry of `hs` has key `v`.
pub open spec fn has_hit(hs: Seq<Hit>, v: i64) -> bool {
    exists|t: int| 0 <= t < hs.len() && #[trigger] hs[t].key == v
}

/// Every entry is a key of rows `lo..i` with its sum, the sum exceeding `thr`.
pub open spec fn hits_sound(keys: Seq<i64>, vals: Seq<i128>, thr: int, lo: int, i: int, hs: Seq<Hit>) -> bool {
    forall|t: int| 0 <= t < hs.len() ==> {
        &&& (#[trigger] hs[t]).sum as int == ksum(keys, vals, hs[t].key, lo, i)
        &&& hs[t].sum > thr
        &&& kcount(keys, hs[t].key, lo, i) > 0
    }
}

/// The scan state after rows `lo..i` (see the module header).
pub open spec fn scan_inv(keys: Seq<i64>, vals: Seq<i128>, thr: int, lo: int, i: int, cur: i64, csum: int, hs: Seq<Hit>) -> bool {
    &&& 0 <= lo <= i <= keys.len()
    &&& lo < keys.len()
    &&& vals.len() == keys.len()
    &&& cur == keys[if i > lo { i - 1 } else { lo }]
    &&& forall|j: int| lo <= j < i ==> keys[lo] <= #[trigger] keys[j] <= cur
    &&& keys[lo] <= cur
    &&& csum == ksum(keys, vals, cur, lo, i)
    &&& hits_ascending(hs)
    &&& forall|t: int| 0 <= t < hs.len() ==> (#[trigger] hs[t]).key < cur
    &&& hits_sound(keys, vals, thr, lo, i, hs)
    &&& forall|v: i64| v != cur && kcount(keys, v, lo, i) > 0 && ksum(keys, vals, v, lo, i) > thr ==> #[trigger] has_hit(hs, v)
}

/// The exact answer over rows `lo..hi`: `hs` lists, ascending, exactly the keys of the range whose sum exceeds
/// `thr`, each with its sum.
pub open spec fn hits_exact(keys: Seq<i64>, vals: Seq<i128>, thr: int, lo: int, hi: int, hs: Seq<Hit>) -> bool {
    &&& hits_ascending(hs)
    &&& hits_sound(keys, vals, thr, lo, hi, hs)
    &&& forall|v: i64| kcount(keys, v, lo, hi) > 0 && ksum(keys, vals, v, lo, hi) > thr ==> #[trigger] has_hit(hs, v)
}

/// The keys of `hs` are pairwise different.
pub open spec fn hits_distinct(hs: Seq<Hit>) -> bool {
    forall|a: int, b: int| 0 <= a < b < hs.len() ==> hs[a].key != hs[b].key
}

/// The answer over rows `lo..hi` in any order: `hs` lists, once each, exactly the keys of the range whose sum
/// exceeds `thr`, each with its sum.
pub open spec fn hits_all(keys: Seq<i64>, vals: Seq<i128>, thr: int, lo: int, hi: int, hs: Seq<Hit>) -> bool {
    &&& hits_distinct(hs)
    &&& hits_sound(keys, vals, thr, lo, hi, hs)
    &&& forall|v: i64| kcount(keys, v, lo, hi) > 0 && ksum(keys, vals, v, lo, hi) > thr ==> #[trigger] has_hit(hs, v)
}

/// The ascending answer is an answer.
pub proof fn lemma_exact_all(keys: Seq<i64>, vals: Seq<i128>, thr: int, lo: int, hi: int, hs: Seq<Hit>)
    requires hits_exact(keys, vals, thr, lo, hi, hs),
    ensures hits_all(keys, vals, thr, lo, hi, hs),
{
}

/// The start state of a scan from row `lo`.
pub proof fn lemma_start(keys: Seq<i64>, vals: Seq<i128>, thr: int, lo: int)
    requires 0 <= lo < keys.len(), vals.len() == keys.len(),
    ensures scan_inv(keys, vals, thr, lo, lo, keys[lo], 0, Seq::empty()),
{
    assert forall|v: i64| v != keys[lo] && kcount(keys, v, lo, lo) > 0 && ksum(keys, vals, v, lo, lo) > thr
        implies #[trigger] has_hit(Seq::<Hit>::empty(), v) by {
        lemma_k_empty(keys, vals, v, lo);
    }
}

/// The final state, with its last run appended when its sum exceeds `thr`, is the exact answer.
pub proof fn lemma_finish(keys: Seq<i64>, vals: Seq<i128>, thr: int, lo: int, i: int, cur: i64, csum: int, hs: Seq<Hit>, last: Hit)
    requires
        scan_inv(keys, vals, thr, lo, i, cur, csum, hs),
        lo < i,
        last.key == cur, last.sum as int == csum,
    ensures
        hits_exact(keys, vals, thr, lo, i, if csum > thr { hs.push(last) } else { hs }),
{
    let out = if csum > thr { hs.push(last) } else { hs };
    lemma_k_witness(keys, cur, lo, i);
    assert(keys[i - 1] == cur);
    if csum > thr {
        assert forall|t: int| 0 <= t < out.len() implies {
            &&& (#[trigger] out[t]).sum as int == ksum(keys, vals, out[t].key, lo, i)
            &&& out[t].sum > thr
            &&& kcount(keys, out[t].key, lo, i) > 0
        } by {
            if t < hs.len() { assert(out[t] == hs[t]); }
        }
        assert forall|a: int, b: int| 0 <= a < b < out.len() implies out[a].key < out[b].key by {
            if b < hs.len() { assert(out[a] == hs[a] && out[b] == hs[b]); } else { assert(out[a] == hs[a]); }
        }
    }
    assert forall|v: i64| kcount(keys, v, lo, i) > 0 && ksum(keys, vals, v, lo, i) > thr implies #[trigger] has_hit(out, v) by {
        if v == cur {
            assert(out[hs.len() as int].key == v);
        } else {
            assert(has_hit(hs, v));
            let t = choose|t: int| 0 <= t < hs.len() && #[trigger] hs[t].key == v;
            assert(out[t] == hs[t]);
        }
    }
}

/// One row `i`: `keys[i]` continues the run of `cur` or starts a larger one (the ended run is appended to the hits
/// when its sum exceeds `thr`).
pub proof fn lemma_step(keys: Seq<i64>, vals: Seq<i128>, thr: int, lo: int, i: int, cur: i64, csum: int, hs: Seq<Hit>)
    requires
        scan_inv(keys, vals, thr, lo, i, cur, csum, hs),
        i < keys.len(),
        keys[i] >= cur,
        i128::MIN <= csum <= i128::MAX,
    ensures
        keys[i] == cur ==> scan_inv(keys, vals, thr, lo, i + 1, cur, csum + vals[i], hs),
        keys[i] != cur && csum > thr ==>
            scan_inv(keys, vals, thr, lo, i + 1, keys[i], vals[i] as int, hs.push(Hit { key: cur, sum: csum as i128 })),
        keys[i] != cur && csum <= thr ==> scan_inv(keys, vals, thr, lo, i + 1, keys[i], vals[i] as int, hs),
{
    let k = keys[i];
    assert forall|v: i64| #[trigger] ksum(keys, vals, v, lo, i + 1) == ksum(keys, vals, v, lo, i) + if keys[i] == v { vals[i] as int } else { 0 }
        && kcount(keys, v, lo, i + 1) == kcount(keys, v, lo, i) + if keys[i] == v { 1nat } else { 0nat } by {
        lemma_k_step(keys, vals, v, lo, i);
    }
    if k == cur {
        assert forall|t: int| 0 <= t < hs.len() implies {
            &&& (#[trigger] hs[t]).sum as int == ksum(keys, vals, hs[t].key, lo, i + 1)
            &&& hs[t].sum > thr
            &&& kcount(keys, hs[t].key, lo, i + 1) > 0
        } by {
            assert(hs[t].key < cur);
            assert(ksum(keys, vals, hs[t].key, lo, i + 1) == ksum(keys, vals, hs[t].key, lo, i));
            assert(kcount(keys, hs[t].key, lo, i + 1) == kcount(keys, hs[t].key, lo, i));
        }
        assert forall|v: i64| v != cur && kcount(keys, v, lo, i + 1) > 0 && ksum(keys, vals, v, lo, i + 1) > thr
            implies #[trigger] has_hit(hs, v) by {
            assert(ksum(keys, vals, v, lo, i + 1) == ksum(keys, vals, v, lo, i));
            assert(kcount(keys, v, lo, i + 1) == kcount(keys, v, lo, i));
        }
        assert forall|j: int| lo <= j < i + 1 implies keys[lo] <= #[trigger] keys[j] <= cur by {
            if j < i { assert(keys[lo] <= keys[j] <= cur); }
        }
    } else {
        // the run of `cur` ended: row `i - 1` is its last row (row `lo` has key `cur`, so `i > lo`)
        assert(i > lo);
        assert(keys[i - 1] == cur);
        // `k` is larger than every key read so far: none of them is `k`
        assert forall|j: int| lo <= j < i implies keys[j] != k by {
            assert(keys[lo] <= keys[j] <= cur);
        }
        lemma_k_absent(keys, vals, k, lo, i);
        assert forall|j: int| lo <= j < i + 1 implies keys[lo] <= #[trigger] keys[j] <= k by {
            if j < i { assert(keys[lo] <= keys[j] <= cur); }
        }
        lemma_k_witness(keys, cur, lo, i);
        assert(lo <= i - 1 < i && keys[i - 1] == cur);
        assert(kcount(keys, cur, lo, i) > 0);
        if csum > thr {
            let h = Hit { key: cur, sum: csum as i128 };
            let hs2 = hs.push(h);
            assert forall|t: int| 0 <= t < hs2.len() implies {
                &&& (#[trigger] hs2[t]).sum as int == ksum(keys, vals, hs2[t].key, lo, i + 1)
                &&& hs2[t].sum > thr
                &&& kcount(keys, hs2[t].key, lo, i + 1) > 0
            } by {
                if t < hs.len() {
                    assert(hs2[t] == hs[t]);
                    assert(hs[t].key < cur);
                } else {
                    assert(hs2[t] == h);
                }
            }
            assert forall|a: int, b: int| 0 <= a < b < hs2.len() implies hs2[a].key < hs2[b].key by {
                if b < hs.len() { assert(hs2[a] == hs[a] && hs2[b] == hs[b]); } else { assert(hs2[a] == hs[a]); }
            }
            assert forall|t: int| 0 <= t < hs2.len() implies (#[trigger] hs2[t]).key < k by {
                if t < hs.len() { assert(hs2[t] == hs[t]); }
            }
            assert forall|v: i64| v != k && kcount(keys, v, lo, i + 1) > 0 && ksum(keys, vals, v, lo, i + 1) > thr
                implies #[trigger] has_hit(hs2, v) by {
                if v == cur {
                    assert(hs2[hs.len() as int].key == v);
                } else {
                    assert(has_hit(hs, v));
                    let t = choose|t: int| 0 <= t < hs.len() && #[trigger] hs[t].key == v;
                    assert(hs2[t] == hs[t]);
                }
            }
        } else {
            assert forall|t: int| 0 <= t < hs.len() implies {
                &&& (#[trigger] hs[t]).sum as int == ksum(keys, vals, hs[t].key, lo, i + 1)
                &&& hs[t].sum > thr
                &&& kcount(keys, hs[t].key, lo, i + 1) > 0
            } by {
                assert(hs[t].key < cur);
            }
            assert forall|t: int| 0 <= t < hs.len() implies (#[trigger] hs[t]).key < k by {}
            assert forall|v: i64| v != k && kcount(keys, v, lo, i + 1) > 0 && ksum(keys, vals, v, lo, i + 1) > thr
                implies #[trigger] has_hit(hs, v) by {
                if v == cur {
                    assert(ksum(keys, vals, v, lo, i + 1) == csum);
                }
            }
        }
    }
}

/// Joining: the state of `0..h` and the state of a later range `h..i` (started fresh at `h`, `keys[h]` larger than
/// the first state's `cur`) give the state of `0..i`; the first state's last run is complete at `h`.
pub proof fn lemma_join(keys: Seq<i64>, vals: Seq<i128>, thr: int, h: int, i: int, cur1: i64, csum1: int, hs1: Seq<Hit>,
    cur2: i64, csum2: int, hs2: Seq<Hit>)
    requires
        scan_inv(keys, vals, thr, 0, h, cur1, csum1, hs1),
        scan_inv(keys, vals, thr, h, i, cur2, csum2, hs2),
        0 < h < i,
        keys[h] > cur1,
        -0x8000_0000_0000_0000_0000_0000_0000_0000 <= csum1 < 0x8000_0000_0000_0000_0000_0000_0000_0000,
    ensures ({
        let mid = if csum1 > thr { hs1.push(Hit { key: cur1, sum: csum1 as i128 }) } else { hs1 };
        scan_inv(keys, vals, thr, 0, i, cur2, csum2, mid + hs2)
    }),
{
    let last = Hit { key: cur1, sum: csum1 as i128 };
    let mid = if csum1 > thr { hs1.push(last) } else { hs1 };
    lemma_finish(keys, vals, thr, 0, h, cur1, csum1, hs1, last);
    let out = mid + hs2;
    // keys before h are at most cur1, keys from h on are at least keys[h] > cur1
    assert forall|v: i64| #[trigger] ksum(keys, vals, v, 0, i) == ksum(keys, vals, v, 0, h) + ksum(keys, vals, v, h, i)
        && kcount(keys, v, 0, i) == kcount(keys, v, 0, h) + kcount(keys, v, h, i) by {
        lemma_k_split(keys, vals, v, 0, h, i);
    }
    assert forall|t: int| 0 <= t < mid.len() implies (#[trigger] mid[t]).key <= cur1 by {
        if t < hs1.len() { assert(mid[t] == hs1[t]); }
    }
    assert forall|t: int| 0 <= t < mid.len() implies kcount(keys, (#[trigger] mid[t]).key, h, i) == 0
        && ksum(keys, vals, mid[t].key, h, i) == 0 by {
        let v = mid[t].key;
        assert forall|j: int| h <= j < i implies keys[j] != v by {
            assert(keys[h] <= keys[j]);
        }
        lemma_k_absent(keys, vals, v, h, i);
    }
    assert forall|t: int| 0 <= t < hs2.len() implies kcount(keys, (#[trigger] hs2[t]).key, 0, h) == 0
        && ksum(keys, vals, hs2[t].key, 0, h) == 0 by {
        let v = hs2[t].key;
        lemma_k_witness(keys, v, h, i);
        let j = choose|j: int| h <= j < i && keys[j] == v;
        assert(keys[h] <= keys[j]);
        assert forall|j2: int| 0 <= j2 < h implies keys[j2] != v by {
            assert(keys[j2] <= cur1);
        }
        lemma_k_absent(keys, vals, v, 0, h);
    }
    // cur2's sum over 0..i is its sum over h..i
    assert(kcount(keys, cur2, 0, h) == 0 && ksum(keys, vals, cur2, 0, h) == 0) by {
        assert forall|j2: int| 0 <= j2 < h implies keys[j2] != cur2 by {
            assert(keys[j2] <= cur1);
            assert(keys[h] <= cur2);
        }
        lemma_k_absent(keys, vals, cur2, 0, h);
    }
    assert forall|j: int| 0 <= j < i implies keys[0] <= #[trigger] keys[j] <= cur2 by {
        if j < h {
            assert(keys[0] <= keys[j] <= cur1);
        } else {
            assert(keys[h] <= keys[j] <= cur2);
            assert(keys[0] <= cur1);
        }
    }
    assert forall|t: int| 0 <= t < out.len() implies {
        &&& (#[trigger] out[t]).sum as int == ksum(keys, vals, out[t].key, 0, i)
        &&& out[t].sum > thr
        &&& kcount(keys, out[t].key, 0, i) > 0
    } by {
        if t < mid.len() {
            assert(out[t] == mid[t]);
            let v = mid[t].key;
            assert(mid[t].sum as int == ksum(keys, vals, v, 0, h) && mid[t].sum > thr && kcount(keys, v, 0, h) > 0);
            assert(ksum(keys, vals, v, h, i) == 0 && kcount(keys, v, h, i) == 0);
            assert(ksum(keys, vals, v, 0, i) == ksum(keys, vals, v, 0, h) + ksum(keys, vals, v, h, i));
            assert(kcount(keys, v, 0, i) == kcount(keys, v, 0, h) + kcount(keys, v, h, i));
        } else {
            let u = t - mid.len();
            assert(out[t] == hs2[u]);
            let v = hs2[u].key;
            assert(hs2[u].sum as int == ksum(keys, vals, v, h, i) && hs2[u].sum > thr && kcount(keys, v, h, i) > 0);
            assert(ksum(keys, vals, v, 0, h) == 0 && kcount(keys, v, 0, h) == 0);
            assert(ksum(keys, vals, v, 0, i) == ksum(keys, vals, v, 0, h) + ksum(keys, vals, v, h, i));
            assert(kcount(keys, v, 0, i) == kcount(keys, v, 0, h) + kcount(keys, v, h, i));
        }
    }
    assert forall|a: int, b: int| 0 <= a < b < out.len() implies out[a].key < out[b].key by {
        if b < mid.len() {
            assert(out[a] == mid[a] && out[b] == mid[b]);
        } else if a >= mid.len() {
            assert(out[a] == hs2[a - mid.len()] && out[b] == hs2[b - mid.len()]);
        } else {
            assert(out[a] == mid[a] && out[b] == hs2[b - mid.len()]);
            let v = hs2[b - mid.len()].key;
            lemma_k_witness(keys, v, h, i);
            let j = choose|j: int| h <= j < i && keys[j] == v;
            assert(keys[h] <= keys[j]);
        }
    }
    assert forall|t: int| 0 <= t < out.len() implies (#[trigger] out[t]).key < cur2 by {
        if t < mid.len() {
            assert(out[t] == mid[t]);
            assert(keys[h] <= cur2);
        } else {
            assert(out[t] == hs2[t - mid.len()]);
        }
    }
    assert forall|v: i64| v != cur2 && kcount(keys, v, 0, i) > 0 && ksum(keys, vals, v, 0, i) > thr implies #[trigger] has_hit(out, v) by {
        if kcount(keys, v, h, i) > 0 {
            lemma_k_witness(keys, v, h, i);
            let j = choose|j: int| h <= j < i && keys[j] == v;
            assert(keys[h] <= keys[j]);
            assert forall|j2: int| 0 <= j2 < h implies keys[j2] != v by {
                assert(keys[j2] <= cur1);
            }
            lemma_k_absent(keys, vals, v, 0, h);
            assert(has_hit(hs2, v));
            let t = choose|t: int| 0 <= t < hs2.len() && #[trigger] hs2[t].key == v;
            assert(out[mid.len() + t] == hs2[t]);
        } else {
            lemma_k_witness(keys, v, h, i);
            assert forall|j: int| h <= j < i implies keys[j] != v by {}
            lemma_k_absent(keys, vals, v, h, i);
            assert(has_hit(mid, v));
            let t = choose|t: int| 0 <= t < mid.len() && #[trigger] mid[t].key == v;
            assert(out[t] == mid[t]);
        }
    }
}

// ------------------------------------------------------------------------------------------------ the scan task

/// How a scan task ended.
pub enum ScanEnd {
    /// Every row of its range was scanned.
    Done,
    /// Its output buffer was full when a run had to be appended; the state is at `pos < hi`.
    Full,
    /// A key smaller than its predecessor was found (the rows are not in ascending key runs).
    Unsorted,
}

/// A scan of rows `start..hi` continuing a state of rows `lo..start` (ghost `lo` and earlier hits `hs0`).
pub struct RunTask {
    pub keys: &'static [i64],
    pub vals: &'static [i128],
    pub start: usize,
    pub hi: usize,
    pub cur: i64,
    pub csum: i128,
    pub thr: i128,
    pub buf: TaskBuffer<Hit>,
    pub lo: Ghost<int>,
    pub hs0: Ghost<Seq<Hit>>,
}

/// The task's result: the state at `pos` with the hits `hs0 ++ buf`.
pub struct RunOut {
    pub buf: TaskBuffer<Hit>,
    pub pos: usize,
    pub cur: i64,
    pub csum: i128,
    pub end: ScanEnd,
}

/// What a scan task needs: its range inside the columns, bounded values, the continued state, an empty buffer.
pub open spec fn run_pre(t: RunTask) -> bool {
    &&& t.start <= t.hi <= t.keys@.len()
    &&& t.vals@.len() == t.keys@.len()
    &&& vals_bounded(t.vals@)
    &&& scan_inv(t.keys@, t.vals@, t.thr as int, t.lo@, t.start as int, t.cur, t.csum as int, t.hs0@)
    &&& t.buf.wf()
    &&& t.buf.view().len() == 0
    &&& t.buf.capacity() > 0
}

/// What a scan task guarantees: `Done` reaches `hi`, `Full` stops before it; except on `Unsorted`, the state at
/// `pos` holds with the hits `hs0 ++ buf`.
pub open spec fn run_post(t: RunTask, out: RunOut) -> bool {
    &&& out.buf.wf()
    &&& t.start <= out.pos <= t.hi
    &&& (out.end is Done ==> out.pos == t.hi)
    &&& (out.end is Full ==> t.start < out.pos < t.hi)
    &&& (!(out.end is Unsorted) ==> scan_inv(t.keys@, t.vals@, t.thr as int, t.lo@, out.pos as int, out.cur, out.csum as int, t.hs0@ + out.buf.view()))
}

/// `|ksum(.., lo, i)| <= (i - lo) * val_bound()`, which keeps the running sum inside `i128`.
proof fn lemma_csum_bound(keys: Seq<i64>, vals: Seq<i128>, v: i64, lo: int, i: int)
    requires 0 <= lo <= i <= keys.len(), vals.len() == keys.len(), vals_bounded(vals), i <= usize::MAX,
    ensures -0x1000_0000_0000_0000_0000_0000_0000_0000 <= ksum(keys, vals, v, lo, i) <= 0x1000_0000_0000_0000_0000_0000_0000_0000,
{
    assert forall|j: int| lo <= j < i implies -val_bound() <= #[trigger] vals[j] <= val_bound() by {}
    lemma_k_bound(keys, vals, v, lo, i, val_bound());
    let c = kcount(keys, v, lo, i) as int;
    assert(c <= usize::MAX);
    assert(c * val_bound() <= 0x1000_0000_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
        requires 0 <= c <= usize::MAX, val_bound() == 1_000_000_000_000_000;
}

impl WorkerTask for RunTask {
    type Output = RunOut;

    open spec fn pre(&self) -> bool { run_pre(*self) }

    open spec fn post(&self, out: RunOut) -> bool { run_post(*self, out) }

    fn declared_rows(&self) -> (u64, u64) {
        (self.start as u64, self.hi as u64)
    }

    fn run(self) -> (out: RunOut) {
        let keys = self.keys;
        let vals = self.vals;
        let hi = self.hi;
        let thr = self.thr;
        let mut buf = self.buf;
        let mut cur = self.cur;
        let mut csum = self.csum;
        let mut i = self.start;
        let ghost lo = self.lo@;
        let ghost hs0 = self.hs0@;
        let ghost n = keys@.len() as int;
        while i < hi
            invariant
                self.start <= i <= hi, hi <= n, n == keys@.len(), vals@.len() == n,
                keys@ == self.keys@, vals@ == self.vals@, thr == self.thr, hi == self.hi, lo == self.lo@, hs0 == self.hs0@,
                vals_bounded(vals@),
                buf.wf(), buf.capacity() == self.buf.capacity(), buf.capacity() > 0,
                buf.view().len() > 0 ==> i > self.start,
                scan_inv(keys@, vals@, thr as int, lo, i as int, cur, csum as int, hs0 + buf.view()),
            decreases hi - i,
        {
            let k = keys[i];
            let q = vals[i];
            proof {
                lemma_csum_bound(keys@, vals@, cur, lo, i as int);
                assert(-val_bound() <= vals@[i as int] <= val_bound());
            }
            let same = k == cur;
            if !same && (k < cur || csum > thr) {
                if k < cur {
                    return RunOut { buf, pos: i, cur, csum, end: ScanEnd::Unsorted };
                }
                if buf.len() >= buf.slots() {
                    return RunOut { buf, pos: i, cur, csum, end: ScanEnd::Full };
                }
                proof {
                    lemma_step(keys@, vals@, thr as int, lo, i as int, cur, csum as int, hs0 + buf.view());
                }
                let ghost before = buf.view();
                buf.push(Hit { key: cur, sum: csum });
                proof {
                    assert(hs0 + buf.view() =~= (hs0 + before).push(Hit { key: cur, sum: csum }));
                }
            } else {
                proof {
                    lemma_step(keys@, vals@, thr as int, lo, i as int, cur, csum as int, hs0 + buf.view());
                }
            }
            let base: i128 = if same { csum } else { 0 };
            csum = base + q;
            cur = k;
            i = i + 1;
        }
        RunOut { buf, pos: i, cur, csum, end: ScanEnd::Done }
    }
}

} // verus!
