//! The scan of one row range as a `fork_join` task (`ScanTask`), and the completion of a range on the calling
//! thread (`finish_range`): a task whose table filled up resumes there with a larger table, so every range ends
//! with its complete group table or with a row whose charge overflows `i128`.
use vstd::prelude::*;
use crate::link::expr::fits_i128;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::normal::*;
use crate::agent::columns::*;
use crate::agent::accum::*;
use crate::agent::scan::*;
use crate::agent::block::*;

verus! {

/// Group slots each task starts with (Q1 data has 4 groups; more are handled by `finish_range`).
pub const TASK_SLOTS: usize = 64;

/// Scan of rows `[lo, hi)`.
pub struct ScanTask {
    pub c: Cols,
    pub lo: usize,
    pub hi: usize,
    pub limit: i32,
    pub pd: Ghost<int>,
    /// Accumulator mode (`accum`): small (fast) or exact.
    pub small: bool,
    pub slots: Vec<Acc>,
    pub idx: Vec<usize>,
    /// Zero deltas of the fast path (`block`), at least one per slot.
    pub blk: Vec<Delta>,
}

/// A task's table and where its scan stopped.
pub struct ScanOut {
    pub stop: Stop,
    pub at: usize,
    pub slots: Vec<Acc>,
    pub ng: usize,
    pub idx: Vec<usize>,
}

/// The task's input: a range of well-formed columns, the parameter's stored-date limit, an empty index.
pub open spec fn task_pre(c: Cols, lo: usize, hi: usize, limit: i32, pd: int, slots: Seq<Acc>, idx: Seq<usize>, blk: Seq<Delta>) -> bool {
    &&& cols_wf(c)
    &&& slots.len() <= blk.len()
    &&& blk_zero(blk)
    &&& lo <= hi <= c.n
    &&& limit as int == pd + 10957
    &&& idx.len() == IDX_LEN
    &&& forall|code: int| 0 <= code < IDX_LEN ==> #[trigger] idx[code] == 0
}

/// A scan's result: the table of `[lo, at)`, and the reason it stopped at `at`.
pub open spec fn scan_post(c: Cols, lo: usize, hi: usize, pd: int, small: bool, out: ScanOut) -> bool {
    &&& lo <= out.at <= hi
    &&& table_ok(pd, c, lo as int, out.at as int, out.slots@, out.ng as int)
    &&& idx_ok(c, out.slots@, out.ng as int, out.idx@)
    &&& mode_ok(out.slots@, out.ng as int, small)
    &&& out.stop == Stop::NeedExact ==> out.at < hi && small
    &&& out.stop == Stop::Done ==> out.at == hi
    &&& out.stop == Stop::Full ==> out.at < hi && out.ng == out.slots@.len()
    &&& out.stop == Stop::RowOverflow ==> out.at < hi && q1_qual(pd, crow(c, out.at as int)) && !fits_i128(charge(crow(c, out.at as int)))
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        task_pre(self.c, self.lo, self.hi, self.limit, self.pd@, self.slots@, self.idx@, self.blk@)
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        scan_post(self.c, self.lo, self.hi, self.pd@, self.small, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: ScanOut) {
        let ScanTask { c, lo, hi, limit, pd, small, slots, idx, blk } = self;
        let mut slots = slots;
        let mut idx = idx;
        let mut blk = blk;
        let mut ng: usize = 0;
        proof {
            lemma_table_init(pd@, c, lo as int, slots@, idx@);
        }
        let (stop, at) = if small {
            scan_mixed(&c, lo, hi, limit, pd, &mut slots, &mut ng, &mut idx, &mut blk)
        } else {
            scan_range(&c, lo, lo, hi, limit, pd, small, &mut slots, &mut ng, &mut idx)
        };
        ScanOut { stop, at, slots, ng, idx }
    }
}

/// Unused slots beyond `ng` do not matter to the table.
pub proof fn lemma_table_grow(pd: int, c: Cols, lo: int, i: int, slots: Seq<Acc>, ng: int, idx: Seq<usize>, extra: Acc)
    requires table_ok(pd, c, lo, i, slots, ng), idx_ok(c, slots, ng, idx),
    ensures
        table_ok(pd, c, lo, i, slots.push(extra), ng), idx_ok(c, slots.push(extra), ng, idx),
        forall|small: bool| mode_ok(slots, ng, small) ==> #[trigger] mode_ok(slots.push(extra), ng, small),
{
    let s2 = slots.push(extra);
    assert forall|s: int| 0 <= s < ng implies #[trigger] s2[s] == slots[s] by {}
    assert forall|r: int| lo <= r < i && q1_qual(pd, #[trigger] crow(c, r)) implies
        exists|s: int| 0 <= s < ng && key_of(c, r) == slot_key(c, #[trigger] s2[s]) by {
        let s = choose|s: int| 0 <= s < ng && key_of(c, r) == slot_key(c, #[trigger] slots[s]);
        assert(s2[s] == slots[s]);
    }
    assert forall|s: int, t: int| 0 <= s < ng && 0 <= t < ng && s != t implies slot_key(c, #[trigger] s2[s]) != slot_key(c, #[trigger] s2[t]) by {
        assert(s2[s] == slots[s] && s2[t] == slots[t]);
    }
}

pub fn is_full(s: Stop) -> (b: bool)
    ensures b == (s == Stop::Full),
{
    match s {
        Stop::Full => true,
        _ => false,
    }
}

/// Completes a task's range on the calling thread: while its table is full, grow it and resume the scan.
pub fn finish_range(c: &Cols, lo: usize, hi: usize, limit: i32, Ghost(pd): Ghost<int>, small: bool, out: ScanOut) -> (r: ScanOut)
    requires
        cols_wf(*c),
        hi <= c.n,
        limit as int == pd + 10957,
        scan_post(*c, lo, hi, pd, small, out),
    ensures
        scan_post(*c, lo, hi, pd, small, r),
        r.stop != Stop::Full,
{
    let ScanOut { stop, at, slots, ng, idx } = out;
    let mut stop = stop;
    let mut at = at;
    let mut slots = slots;
    let mut ng = ng;
    let mut idx = idx;
    while is_full(stop)
        invariant
            cols_wf(*c),
            hi <= c.n,
            limit as int == pd + 10957,
            scan_post(*c, lo, hi, pd, small, ScanOut { stop, at, slots, ng, idx }),
        decreases (hi - at) * 2 + (if stop == Stop::Full { 1int } else { 0int }),
    {
        // ng == slots.len() and every slot has a distinct representative in [lo, at): room to double.
        proof {
            assert(ng <= at - lo) by {
                lemma_slots_reps(pd, *c, lo as int, at as int, slots@, ng as int);
            }
        }
        let extra = if ng == 0 { 1 } else { ng };
        let mut k: usize = 0;
        while k < extra
            invariant
                cols_wf(*c),
                ng <= at - lo,
                extra <= ng + 1,
                k <= extra,
                slots@.len() == ng + k,
                lo <= at < hi <= c.n,
                table_ok(pd, *c, lo as int, at as int, slots@, ng as int),
                idx_ok(*c, slots@, ng as int, idx@),
                mode_ok(slots@, ng as int, small),
            decreases extra - k,
        {
            proof {
                lemma_table_grow(pd, *c, lo as int, at as int, slots@, ng as int, idx@, acc_zero(0, small));
            }
            slots.push(new_acc(0, small));
            k = k + 1;
        }
        let ghost at0 = at;
        let (st, a) = scan_range(c, lo, at, hi, limit, Ghost(pd), small, &mut slots, &mut ng, &mut idx);
        stop = st;
        at = a;
        proof {
            assert(st == Stop::Full ==> at > at0);
        }
    }
    ScanOut { stop, at, slots, ng, idx }
}

/// The slots of a table have distinct representatives in `[lo, i)`: at most `i - lo` of them.
pub proof fn lemma_slots_reps(pd: int, c: Cols, lo: int, i: int, slots: Seq<Acc>, ng: int)
    requires table_ok(pd, c, lo, i, slots, ng), lo <= i,
    ensures ng <= i - lo,
{
    // Distinct keys have distinct representatives; map slots injectively into [lo, i).
    let reps = Seq::new(ng as nat, |s: int| slots[s].rep as int);
    assert forall|s: int, t: int| 0 <= s < ng && 0 <= t < ng && s != t implies reps[s] != reps[t] by {
        assert(slot_key(c, slots[s]) != slot_key(c, slots[t]));
    }
    assert forall|a: int| 0 <= a < reps.len() implies lo <= #[trigger] reps[a] < i by {
        assert(lo <= slots[a].rep < i);
    }
    lemma_injective_range(reps, lo, i);
}

/// `n` distinct integers in `[lo, hi)`: `n <= hi - lo`.
pub proof fn lemma_injective_range(s: Seq<int>, lo: int, hi: int)
    requires
        forall|a: int| 0 <= a < s.len() ==> lo <= #[trigger] s[a] < hi,
        forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && a != b ==> s[a] != s[b],
    ensures s.len() <= if hi >= lo { hi - lo } else { 0 },
    decreases s.len(),
{
    if s.len() > 0 {
        // Remove the largest value `hi - 1` if present, otherwise shrink the range.
        let top = hi - 1;
        if exists|a: int| 0 <= a < s.len() && s[a] == top {
            let a = choose|a: int| 0 <= a < s.len() && s[a] == top;
            let t = s.remove(a);
            assert forall|x: int| 0 <= x < t.len() implies lo <= #[trigger] t[x] < top by {
                if x < a {
                    assert(t[x] == s[x]);
                } else {
                    assert(t[x] == s[x + 1]);
                }
            }
            assert forall|x: int, y: int| 0 <= x < t.len() && 0 <= y < t.len() && x != y implies t[x] != t[y] by {
                let sx = if x < a { x } else { x + 1 };
                let sy = if y < a { y } else { y + 1 };
                assert(t[x] == s[sx] && t[y] == s[sy]);
            }
            lemma_injective_range(t, lo, top);
        } else {
            assert forall|x: int| 0 <= x < s.len() implies lo <= #[trigger] s[x] < top by {
                assert(s[x] != top);
            }
            lemma_injective_range_shrink(s, lo, top);
        }
    }
}

/// Helper of `lemma_injective_range` (the same statement on a smaller range, by recursion on the range).
pub proof fn lemma_injective_range_shrink(s: Seq<int>, lo: int, hi: int)
    requires
        s.len() > 0,
        forall|a: int| 0 <= a < s.len() ==> lo <= #[trigger] s[a] < hi,
        forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && a != b ==> s[a] != s[b],
    ensures s.len() <= hi - lo,
    decreases hi - lo, s.len(),
{
    assert(lo <= s[0] < hi);
    let top = hi - 1;
    if exists|a: int| 0 <= a < s.len() && s[a] == top {
        let a = choose|a: int| 0 <= a < s.len() && s[a] == top;
        let t = s.remove(a);
        assert forall|x: int| 0 <= x < t.len() implies lo <= #[trigger] t[x] < top by {
            if x < a {
                assert(t[x] == s[x]);
            } else {
                assert(t[x] == s[x + 1]);
            }
        }
        assert forall|x: int, y: int| 0 <= x < t.len() && 0 <= y < t.len() && x != y implies t[x] != t[y] by {
            let sx = if x < a { x } else { x + 1 };
            let sy = if y < a { y } else { y + 1 };
            assert(t[x] == s[sx] && t[y] == s[sy]);
        }
        if t.len() > 0 {
            lemma_injective_range_shrink(t, lo, top);
        }
    } else {
        assert forall|x: int| 0 <= x < s.len() implies lo <= #[trigger] s[x] < top by {
            assert(s[x] != top);
        }
        lemma_injective_range_shrink(s, lo, top);
    }
}

} // verus!
