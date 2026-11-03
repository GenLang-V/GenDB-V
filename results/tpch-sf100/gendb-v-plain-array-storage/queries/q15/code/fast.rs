//! The fast path (`fast_path`), for databases like dbgen's: supplier keys dense from `base` (`keys[i] == base + i`)
//! and every qualifying `lineitem` row meeting the assumptions of `scan` (key a supplier slot, positive term, slot
//! sums inside `i64`; with several tasks, terms below `2^32`). It answers `None` when an assumption fails (the general path then runs).
//!
//! Plan: with one task, the scan runs on the calling thread into one dense `i64` slot table (`scan::scan_range`),
//! which is the one chunk. With more, one task (`part::PartTask`) per contiguous row range (`row_start`) lists the
//! (slot, term) entries of its qualifying rows by slot partition; then one merge task (`part::PMergeTask`) per
//! contiguous slot range (`chunk_start`) sums the entries of its slots over every task's lists and reports its
//! largest slot sum. The calling thread takes the largest of those (`best`) and lists, in slot order, the supplier
//! rows whose slot holds it (`collect_picks`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::link::query::*;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::common::selection::*;
use crate::agent::normal::*;
use crate::agent::cols::*;
use crate::agent::bounds::*;
use crate::agent::scan::*;
use crate::agent::fastspec::*;
use crate::agent::groups::*;
use crate::agent::answer::{pick_of, idxs_ok};
use crate::agent::part::*;

verus! {

/// Rows per scan task below which fewer tasks are used.
pub const MIN_TASK_ROWS: usize = 1048576;

/// `n` zero `i64`s (`vec!`: the allocator hands out zeroed memory).
pub fn zeros_i64(n: usize) -> (v: Vec<i64>)
    ensures v@.len() == n, forall|i: int| 0 <= i < n ==> #[trigger] v@[i] == 0i64,
{
    let v = vec![0i64; n];
    proof {
        assert forall|i: int| 0 <= i < n implies #[trigger] v@[i] == 0i64 by {
            assert(vstd::pervasive::cloned(0i64, v@[i]));
        }
    }
    v
}

/// `n` zero `u32`s.
pub fn zeros_u32(n: usize) -> (v: Vec<u32>)
    ensures v@.len() == n,
{
    vec![0u32; n]
}

/// `n` zero `u64`s (`vec!`: zeroed memory from the allocator; a large one is freshly mapped, touched where written).
pub fn zeros_u64(n: usize) -> (v: Vec<u64>)
    ensures v@.len() == n,
{
    vec![0u64; n]
}

/// `n` zero `usize`s.
pub fn zeros_usize(n: usize) -> (v: Vec<usize>)
    ensures v@.len() == n, forall|i: int| 0 <= i < n ==> #[trigger] v@[i] == 0usize,
{
    let v = vec![0usize; n];
    proof {
        assert forall|i: int| 0 <= i < n implies #[trigger] v@[i] == 0usize by {
            assert(vstd::pervasive::cloned(0usize, v@[i]));
        }
    }
    v
}

/// The base of dense supplier keys: `keys[i] == base + i` for every row (none for an empty table).
pub fn dense_base(k: &SuppKeys) -> (r: Option<i64>)
    requires k.keys@.len() == k.ns,
    ensures r matches Some(base) ==> forall|i: int| 0 <= i < k.ns ==> #[trigger] k.keys@[i] as int == base as int + i,
{
    if k.ns == 0 {
        return None;
    }
    let base = k.keys[0];
    let mut i: usize = 0;
    while i < k.ns
        invariant
            k.keys@.len() == k.ns,
            i <= k.ns,
            forall|r: int| 0 <= r < i ==> #[trigger] k.keys@[r] as int == base as int + r,
        decreases k.ns - i,
    {
        if k.keys[i] as i128 != base as i128 + i as i128 {
            return None;
        }
        i = i + 1;
    }
    Some(base)
}

// ------------------------------------------------------------------------------------------------ ranges

/// First row of scan task `t` of `nt` over `n` rows (`n` for `t == nt`): equal ranges, the last takes the rest.
pub open spec fn row_start(t: int, nt: int, n: int) -> int {
    if t >= nt { n } else { t * (n / nt) }
}

/// The scan ranges start at 0, are ordered and stay inside `[0, n]`.
pub proof fn lemma_row_start(t: int, nt: int, n: int)
    requires 0 <= t < nt, n >= 0,
    ensures
        row_start(0, nt, n) == 0,
        0 <= row_start(t, nt, n) <= row_start(t + 1, nt, n) <= n,
{
    let q = n / nt;
    assert(q * nt <= n) by (nonlinear_arith) requires q == n / nt, nt >= 1, n >= 0;
    assert(0 <= q) by (nonlinear_arith) requires q == n / nt, nt >= 1, n >= 0;
    assert(t * q <= (t + 1) * q) by (nonlinear_arith) requires q >= 0, t >= 0;
    assert((t + 1) * q <= nt * q) by (nonlinear_arith) requires q >= 0, t + 1 <= nt;
    assert(0 <= t * q) by (nonlinear_arith) requires q >= 0, t >= 0;
    assert(nt * q == q * nt) by (nonlinear_arith);
    assert(0 * q == 0);
}

pub fn row_start_exec(t: usize, nt: usize, n: usize) -> (r: usize)
    requires 1 <= nt, t <= nt,
    ensures r as int == row_start(t as int, nt as int, n as int),
{
    if t >= nt {
        n
    } else {
        proof {
            lemma_row_start(t as int, nt as int, n as int);
        }
        t * (n / nt)
    }
}

/// Slots per partition of the parallel path's entries; merge chunks are whole partitions.
pub const PART_SLOTS: usize = 16384;

/// Slots per merge chunk of `nt` chunks over `ns` slots: whole partitions, enough for `nt` chunks to cover `ns`.
pub open spec fn chunk_width(nt: int, ns: int) -> int {
    (PART_SLOTS as int) * ((ns / (PART_SLOTS as int)) / nt + 1)
}

/// The chunk width is positive and `nt` chunks cover the slots.
pub proof fn lemma_chunk_width(nt: int, ns: int)
    requires nt >= 1, ns >= 0,
    ensures chunk_width(nt, ns) >= 1, nt * chunk_width(nt, ns) > ns,
{
    let w = PART_SLOTS as int;
    let a = ns / w;
    let q = a / nt;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ns, w);
    vstd::arithmetic::div_mod::lemma_mod_bound(ns, w);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(ns, w);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, nt);
    vstd::arithmetic::div_mod::lemma_mod_bound(a, nt);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(a, nt);
    assert(nt * (q + 1) >= a + 1) by (nonlinear_arith) requires a == nt * q + a % nt, a % nt < nt;
    assert(w * (nt * (q + 1)) >= w * (a + 1)) by (nonlinear_arith) requires nt * (q + 1) >= a + 1, w >= 1;
    assert(nt * chunk_width(nt, ns) == w * (nt * (q + 1))) by (nonlinear_arith) requires chunk_width(nt, ns) == w * (q + 1);
    assert(chunk_width(nt, ns) >= 1) by (nonlinear_arith) requires chunk_width(nt, ns) == w * (q + 1), q >= 0, w >= 1;
}

/// First slot of merge chunk `t` of `nt` over `ns` slots: chunks of `chunk_width` slots, clipped at `ns`.
pub open spec fn chunk_start(t: int, nt: int, ns: int) -> int {
    if t * chunk_width(nt, ns) < ns { t * chunk_width(nt, ns) } else { ns }
}

/// The chunks start at 0, are ordered, stay inside `[0, ns]` and end at `ns`.
pub proof fn lemma_chunk_start(t: int, nt: int, ns: int)
    requires 0 <= t < nt, ns >= 0,
    ensures
        chunk_start(0, nt, ns) == 0,
        0 <= chunk_start(t, nt, ns) <= chunk_start(t + 1, nt, ns) <= ns,
        chunk_start(nt, nt, ns) == ns,
{
    let m = chunk_width(nt, ns);
    lemma_chunk_width(nt, ns);
    assert(t * m <= (t + 1) * m) by (nonlinear_arith) requires m >= 1, t >= 0;
    assert(0 <= t * m) by (nonlinear_arith) requires m >= 1, t >= 0;
    assert(0 * m == 0);
}

pub fn chunk_start_exec(t: usize, nt: usize, ns: usize) -> (r: usize)
    requires 1 <= nt <= MAX_WORKERS, t <= nt,
    ensures r as int == chunk_start(t as int, nt as int, ns as int),
{
    let qd = ns / PART_SLOTS / nt;
    let m = (PART_SLOTS as u128) * (qd as u128 + 1);
    proof {
        let w = PART_SLOTS as int;
        vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(ns as int, 1, w);
        vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(ns as int / w, 1, nt as int);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(ns as int, w);
        assert(m as int == chunk_width(nt as int, ns as int));
    }
    // `t * m` past `u128` is past `ns` too
    match (t as u128).checked_mul(m) {
        Some(x) => if x < ns as u128 { x as usize } else { ns },
        None => ns,
    }
}

// ------------------------------------------------------------------------------------------------ chunks

/// Slot `s` of `vals` (covering the slots `[a, ..)`) is the SUM of key `base + a + s` over all rows.
pub open spec fn chunk_ok(vals: Seq<i64>, a: int, c: Cols, w: DayWindow, base: int) -> bool {
    forall|s: int| 0 <= s < vals.len() ==> (#[trigger] vals[s]) as int == gs(c, w, base + a + s, 0, c.n as int)
}

/// The largest value of `vals` (0 when none is positive).
pub fn chunk_best(vals: &Vec<i64>) -> (best: i64)
    ensures is_best(vals@, best as int),
    no_unwind
{
    let mut best: i64 = 0;
    let mut j: usize = 0;
    let m = vals.len();
    while j < m
        invariant
            m == vals@.len(),
            j <= m,
            best >= 0,
            forall|u: int| 0 <= u < j ==> (#[trigger] vals@[u]) as int <= best,
            best > 0 ==> exists|u: int| 0 <= u < j && (#[trigger] vals@[u]) as int == best,
        decreases m - j,
    {
        if vals[j] > best {
            best = vals[j];
        }
        j = j + 1;
    }
    best
}

// ------------------------------------------------------------------------------------------------ picks

/// The chunks of the merged slot sums: chunk `t` holds the slots `[chunk_start(t), chunk_start(t + 1))` with their
/// largest value `bests[t]`.
pub open spec fn chunks_ok(chunks: Seq<(Vec<i64>, i64, bool)>, nt: int, c: Cols, w: DayWindow, base: int, ns: int) -> bool {
    &&& chunks.len() == nt
    &&& forall|t: int| 0 <= t < nt ==> {
        let ch = #[trigger] chunks[t];
        &&& ch.0@.len() == chunk_start(t + 1, nt, ns) - chunk_start(t, nt, ns)
        &&& chunk_ok(ch.0@, chunk_start(t, nt, ns), c, w, base)
        &&& is_best(ch.0@, ch.1 as int)
    }
}

/// The merged slot sums as one sequence: slot `s` is the SUM of key `base + s` over all rows.
pub open spec fn all_vals(c: Cols, w: DayWindow, base: int, ns: int) -> Seq<i64> {
    Seq::new(ns as nat, |s: int| gs(c, w, base + s, 0, c.n as int) as i64)
}

/// The supplier rows whose slot holds the positive value `best`, in slot order.
pub open spec fn best_slot(c: Cols, w: DayWindow, base: int, best: int) -> spec_fn(int) -> bool {
    |s: int| gs(c, w, base + s, 0, c.n as int) == best && best > 0
}

/// The largest chunk value, and the slots holding it.
pub fn collect_picks(chunks: &Vec<(Vec<i64>, i64, bool)>, nt: usize, ns: usize, Ghost(c): Ghost<Cols>, Ghost(w): Ghost<DayWindow>,
    Ghost(base): Ghost<int>) -> (r: (Vec<usize>, i64))
    requires
        1 <= nt <= MAX_WORKERS,
        chunks_ok(chunks@, nt as int, c, w, base, ns as int),
    ensures
        table_ok(all_vals(c, w, base, ns as int), c, w, base, ns as int, 0, c.n as int),
        is_best(all_vals(c, w, base, ns as int), r.1 as int),
        idxs_ok(r.0@, range_filter(0, ns as int, best_slot(c, w, base, r.1 as int)), ns),
{
    let ghost vals = all_vals(c, w, base, ns as int);
    // every slot sum fits `i64`: it is a chunk value
    proof {
        assert forall|s: int| 0 <= s < ns implies (#[trigger] vals[s]) as int == gs(c, w, base + s, 0, c.n as int) by {
            let t = s / chunk_width(nt as int, ns as int);
            lemma_slot_chunk(chunks@, nt as int, c, w, base, ns as int, s);
        }
    }
    let mut best: i64 = 0;
    let mut t: usize = 0;
    while t < nt
        invariant
            1 <= nt <= MAX_WORKERS,
            chunks_ok(chunks@, nt as int, c, w, base, ns as int),
            t <= nt,
            best >= 0,
            forall|u: int| 0 <= u < t ==> (#[trigger] chunks@[u]).1 as int <= best,
            best > 0 ==> exists|u: int| 0 <= u < t && (#[trigger] chunks@[u]).1 as int == best,
        decreases nt - t,
    {
        if chunks[t].1 > best {
            best = chunks[t].1;
        }
        t = t + 1;
    }
    let ghost p = best_slot(c, w, base, best as int);
    let mut idxs: Vec<usize> = Vec::new();
    let mut t: usize = 0;
    proof {
        lemma_chunk_start(0, nt as int, ns as int);
    }
    while t < nt
        invariant
            1 <= nt <= MAX_WORKERS,
            chunks_ok(chunks@, nt as int, c, w, base, ns as int),
            t <= nt,
            p == best_slot(c, w, base, best as int),
            idxs_ok(idxs@, range_filter(0, chunk_start(t as int, nt as int, ns as int), p), ns),
        decreases nt - t,
    {
        let a = chunk_start_exec(t, nt, ns);
        proof {
            lemma_chunk_start(t as int, nt as int, ns as int);
        }
        let m = chunks[t].0.len();
        let mut j: usize = 0;
        while j < m
            invariant
                1 <= nt <= MAX_WORKERS,
                chunks_ok(chunks@, nt as int, c, w, base, ns as int),
                t < nt,
                a as int == chunk_start(t as int, nt as int, ns as int),
                m == chunks@[t as int].0@.len(),
                a + m <= ns,
                j <= m,
                p == best_slot(c, w, base, best as int),
                idxs_ok(idxs@, range_filter(0, a + j, p), ns),
            decreases m - j,
        {
            let v = chunks[t].0[j];
            proof {
                lemma_range_filter_step(0, a + j, p);
                assert(v as int == gs(c, w, base + a + j, 0, c.n as int));
                assert(base + (a + j) == base + a + j);
            }
            if v == best && best > 0 {
                let ghost old_idxs = idxs@;
                idxs.push(a + j);
                proof {
                    let sel = range_filter(0, a + j, p);
                    assert(a + j < ns);
                    assert(idxs@.len() == sel.len() + 1);
                    assert(range_filter(0, a + j + 1, p) == sel.push(a + j));
                    assert forall|u: int| 0 <= u < sel.len() + 1 implies (#[trigger] idxs@[u]) as int == sel.push(a + j)[u]
                        && sel.push(a + j)[u] < ns by {
                        if u < sel.len() {
                            assert(idxs@[u] == old_idxs[u]);
                        }
                    }
                    assert(idxs_ok(idxs@, range_filter(0, a + j + 1, p), ns));
                }
            } else {
                proof {
                    assert(!p(a + j));
                    assert(range_filter(0, a + j + 1, p) == range_filter(0, a + j, p));
                }
            }
            j = j + 1;
        }
        t = t + 1;
    }
    proof {
        lemma_chunk_start(nt - 1, nt as int, ns as int);
        // `best` is the largest slot value
        assert forall|s: int| 0 <= s < vals.len() implies (#[trigger] vals[s]) as int <= best by {
            lemma_slot_chunk(chunks@, nt as int, c, w, base, ns as int, s);
        }
        if best > 0 {
            let u = choose|u: int| 0 <= u < nt && (#[trigger] chunks@[u]).1 as int == best;
            let ch = chunks@[u];
            let j = choose|j: int| 0 <= j < ch.0@.len() && (#[trigger] ch.0@[j]) as int == best;
            lemma_chunk_start(u, nt as int, ns as int);
            let s = chunk_start(u, nt as int, ns as int) + j;
            assert(vals[s] as int == gs(c, w, base + s, 0, c.n as int));
            assert(base + chunk_start(u, nt as int, ns as int) + j == base + s);
        }
    }
    (idxs, best)
}

/// Slot `s` lies in chunk `s / chunk_width(nt, ns)`, whose value there is the slot's SUM, bounded by the chunk's best.
pub proof fn lemma_slot_chunk(chunks: Seq<(Vec<i64>, i64, bool)>, nt: int, c: Cols, w: DayWindow, base: int, ns: int, s: int)
    requires 1 <= nt, chunks_ok(chunks, nt, c, w, base, ns), 0 <= s < ns,
    ensures ({
        let t = s / chunk_width(nt, ns);
        let j = s - chunk_start(t, nt, ns);
        &&& 0 <= t < nt
        &&& 0 <= j < chunks[t].0@.len()
        &&& chunks[t].0@[j] as int == gs(c, w, base + s, 0, c.n as int)
        &&& chunks[t].0@[j] as int <= chunks[t].1 as int
        &&& all_vals(c, w, base, ns)[s] as int == gs(c, w, base + s, 0, c.n as int)
    }),
{
    let m = chunk_width(nt, ns);
    let t = s / m;
    lemma_chunk_width(nt, ns);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(s, m);
    vstd::arithmetic::div_mod::lemma_mod_bound(s, m);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(s, m);
    assert(t * m <= s) by (nonlinear_arith) requires s == m * t + s % m, s % m >= 0;
    assert(s < (t + 1) * m) by (nonlinear_arith) requires s == m * t + s % m, s % m < m;
    assert(t < nt) by (nonlinear_arith) requires t * m <= s, s < ns, nt * m > ns, m >= 1;
    lemma_chunk_start(t, nt, ns);
    assert(chunk_start(t, nt, ns) == t * m);
    let j = s - t * m;
    assert(j < chunk_start(t + 1, nt, ns) - t * m);
    let ch = chunks[t];
    assert(ch.0@[j] as int == gs(c, w, base + t * m + j, 0, c.n as int));
    assert(base + t * m + j == base + s);
    // the value fits `i64`, so the cast in `all_vals` keeps it
    assert(all_vals(c, w, base, ns)[s] == gs(c, w, base + s, 0, c.n as int) as i64);
}

// ------------------------------------------------------------------------------------------------ the driver

/// The serial scan on the calling thread: one dense `i64` slot table, which is the one chunk (`None` when a row
/// breaks the fast path's assumptions).
pub fn serial_chunks(c: &Cols, w: DayWindow, blo: u32, span: u32, base: i64, ns: usize)
    -> (r: Option<Vec<(Vec<i64>, i64, bool)>>)
    requires cols_wf(*c), test_ok(w, blo, span),
    ensures
        r matches Some(chunks) ==> chunks_ok(chunks@, 1, *c, w, base as int, ns as int)
            && range_fast(*c, w, base as int, ns as int, 0, c.n as int),
{
    let ghost gb = base as int;
    let mut table = zeros_i64(ns);
    let mut sel = zeros_u32(BLOCK_ROWS);
    let mut slots = zeros_usize(BLOCK_ROWS);
    let mut terms = zeros_i64(BLOCK_ROWS);
    let ok = scan_range(c, w, blo, span, base, ns, 0, c.n, &mut table, &mut sel, &mut slots, &mut terms);
    if !ok {
        return None;
    }
    let best = chunk_best(&table);
    let ghost tv = table@;
    let mut chunks: Vec<(Vec<i64>, i64, bool)> = Vec::new();
    chunks.push((table, best, true));
    proof {
        lemma_chunk_start(0, 1, ns as int);
        assert(chunks@[0].0@ == tv);
        assert(chunk_ok(tv, 0, *c, w, gb)) by {
            assert forall|j: int| 0 <= j < tv.len() implies (#[trigger] tv[j]) as int == gs(*c, w, gb + 0 + j, 0, c.n as int) by {
                assert(gb + 0 + j == gb + j);
            }
        }
    }
    Some(chunks)
}

/// Entries reserved per scan task: one row in 16 of its range, at least `MIN_BUF_ENTRIES` (so the zeroed buffer is
/// large enough for the allocator to map fresh pages instead of clearing reused memory on the calling thread).
pub const MIN_BUF_ENTRIES: usize = 4_400_000;

/// The parallel path over `nt` row ranges and `nt` slot chunks (`None` when a row breaks an assumption or a task's
/// region is full).
pub fn par_chunks(c: &Cols, w: DayWindow, blo: u32, span: u32, base: i64, ns: usize, nt: usize, dispatch: &mut Dispatch)
    -> (r: Result<Option<Vec<(Vec<i64>, i64, bool)>>, WorkerFailure>)
    requires cols_wf(*c), test_ok(w, blo, span), 2 <= nt <= MAX_WORKERS, ns < PAR_MAX_SLOTS,
    ensures
        r matches Ok(Some(chunks)) ==> chunks_ok(chunks@, nt as int, *c, w, base as int, ns as int)
            && range_fast(*c, w, base as int, ns as int, 0, c.n as int),
{
    let ghost gb = base as int;
    let n = c.n;
    let np = ns / PART_SLOTS + 1;
    let mut tasks: Vec<PartTask> = Vec::new();
    let mut t: usize = 0;
    while t < nt
        invariant
            cols_wf(*c),
            test_ok(w, blo, span),
            ns < PAR_MAX_SLOTS,
            n == c.n,
            np == part_count(ns as int),
            2 <= nt <= MAX_WORKERS,
            t <= nt,
            tasks@.len() == t,
            forall|u: int| 0 <= u < t ==> (#[trigger] tasks@[u]).pre(),
            forall|u: int| 0 <= u < t ==> (#[trigger] tasks@[u]).c == *c && tasks@[u].w == w && tasks@[u].base == base
                && tasks@[u].ns == ns
                && tasks@[u].lo as int == row_start(u, nt as int, n as int)
                && tasks@[u].hi as int == row_start(u + 1, nt as int, n as int),
        decreases nt - t,
    {
        proof {
            lemma_row_start(t as int, nt as int, n as int);
        }
        let lo = row_start_exec(t, nt, n);
        let hi = row_start_exec(t + 1, nt, n);
        let want = if (hi - lo) / 16 > MIN_BUF_ENTRIES { (hi - lo) / 16 } else { MIN_BUF_ENTRIES };
        let cap = want / np + 1;
        proof {
            assert(cap >= 1);
            assert(cap as int * np as int <= 0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFFint) by (nonlinear_arith)
                requires cap <= usize::MAX, np <= usize::MAX;
        }
        let total = cap as u128 * np as u128;
        proof {
            assert(total as int == cap as int * np as int);
        }
        if total > 0x40_0000_0000u128 || total > usize::MAX as u128 {
            return Ok(None);
        }
        let buf = zeros_u64(total as usize);
        let cnt = zeros_usize(np);
        let sel = zeros_u32(BLOCK_ROWS);
        proof {
            assert(buf@.len() == total as int);
            assert(np as int * cap as int == cap as int * np as int) by (nonlinear_arith);
            assert(buf@.len() == np as int * cap as int);
        }
        tasks.push(PartTask { c: *c, w, blo, span, base, ns, lo, hi, buf, cnt, cap, sel });
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(f) => return Err(f),
    };
    // every range met the assumptions
    let mut t: usize = 0;
    while t < nt
        invariant
            outs@.len() == nt,
            t <= nt,
            tv.len() == nt,
            forall|u: int| 0 <= u < nt ==> tv[u].post(#[trigger] outs@[u]),
            forall|u: int| 0 <= u < t ==> (#[trigger] outs@[u]).3,
        decreases nt - t,
    {
        if !outs[t].3 {
            return Ok(None);
        }
        t = t + 1;
    }
    proof {
        assert forall|u: int| 0 <= u < nt implies parts_ok(#[trigger] outs@[u], *c, w, gb, ns as int,
            row_start(u, nt as int, n as int), row_start(u + 1, nt as int, n as int)) by {
            assert(tv[u].post(outs@[u]));
        }
        assert(pscans_ok(outs@, nt as int, *c, w, gb, ns as int));
        assert forall|r: int| 0 <= r < n implies #[trigger] row_fast(*c, w, gb, ns as int, r) by {
            lemma_row_index(nt as int, n as int, r);
            let u = choose|u: int| 0 <= u < nt && row_start(u, nt as int, n as int) <= r < #[trigger] row_start(u + 1, nt as int, n as int);
            assert(tv[u].post(outs@[u]));
            assert(outs@[u].3);
        }
    }
    let shared = Arc::new(outs);
    let mut mtasks: Vec<PMergeTask> = Vec::new();
    let mut t: usize = 0;
    while t < nt
        invariant
            cols_wf(*c),
            n == c.n,
            2 <= nt <= MAX_WORKERS,
            ns < PAR_MAX_SLOTS,
            t <= nt,
            pscans_ok(shared@, nt as int, *c, w, gb, ns as int),
            gb == base as int,
            mtasks@.len() == t,
            forall|u: int| 0 <= u < t ==> (#[trigger] mtasks@[u]).pre(),
            forall|u: int| 0 <= u < t ==> (#[trigger] mtasks@[u]).c@ == *c && mtasks@[u].w@ == w && mtasks@[u].base@ == gb
                && mtasks@[u].a as int == chunk_start(u, nt as int, ns as int)
                && mtasks@[u].b as int == chunk_start(u + 1, nt as int, ns as int),
        decreases nt - t,
    {
        proof {
            lemma_chunk_start(t as int, nt as int, ns as int);
        }
        let a = chunk_start_exec(t, nt, ns);
        let b = chunk_start_exec(t + 1, nt, ns);
        let vals = zeros_i64(b - a);
        let task = PMergeTask { outs: shared.clone(), nt, a, b, vals, c: Ghost(*c), w: Ghost(w), base: Ghost(gb), ns };
        proof {
            assert(task.outs@ == shared@);
            assert(task.pre());
        }
        mtasks.push(task);
        t = t + 1;
    }
    let ghost mv = mtasks@;
    let mouts = match fork_join(dispatch, mtasks) {
        Ok(o) => o,
        Err(f) => return Err(f),
    };
    let mut t: usize = 0;
    while t < nt
        invariant
            mouts@.len() == nt,
            t <= nt,
            mv.len() == nt,
            forall|u: int| 0 <= u < nt ==> mv[u].post(#[trigger] mouts@[u]),
            forall|u: int| 0 <= u < t ==> (#[trigger] mouts@[u]).2,
        decreases nt - t,
    {
        if !mouts[t].2 {
            return Ok(None);
        }
        t = t + 1;
    }
    proof {
        assert forall|u: int| 0 <= u < nt implies {
            let ch = #[trigger] mouts@[u];
            &&& ch.0@.len() == chunk_start(u + 1, nt as int, ns as int) - chunk_start(u, nt as int, ns as int)
            &&& chunk_ok(ch.0@, chunk_start(u, nt as int, ns as int), *c, w, gb)
            &&& is_best(ch.0@, ch.1 as int)
        } by {
            assert(mv[u].post(mouts@[u]));
            lemma_chunk_start(u, nt as int, ns as int);
        }
    }
    Ok(Some(mouts))
}

/// The fast path's outcome: the picked supplier rows and the largest SUM (`Some`), or `None` when the database is
/// unlike dbgen's.
pub fn fast_path(c: &Cols, k: &SuppKeys, w: DayWindow, workers: usize, dispatch: &mut Dispatch,
    Ghost(srows): Ghost<Seq<Row>>) -> (r: Result<Option<(Vec<usize>, i64)>, WorkerFailure>)
    requires
        cols_wf(*c),
        keys_match(*k, srows),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some((idxs, best))) ==> {
            &&& group_caps(g_of(w), crows(*c))
            &&& best as int == max_sum(g_of(w), crows(*c))
            &&& idxs_ok(idxs@, range_filter(0, k.ns as int, pick_of(g_of(w), crows(*c), srows, best as int)), k.ns)
        },
{
    let base = match dense_base(k) {
        Some(b) => b,
        None => return Ok(None),
    };
    let ns = k.ns;
    let n = c.n;
    let (blo, span) = make_test(w);
    let mut nt = workers;
    if n / MIN_TASK_ROWS < nt {
        nt = n / MIN_TASK_ROWS;
    }
    let ghost gb = base as int;
    // the scan, then the chunks of merged slot sums: in parallel when there are several tasks, else (or when a
    // parallel task's region filled up) on the calling thread
    let mut got: Option<Vec<(Vec<i64>, i64, bool)>> = None;
    let mut cn: usize = 1;
    if nt >= 2 && ns < PAR_MAX_SLOTS {
        match par_chunks(c, w, blo, span, base, ns, nt, dispatch) {
            Err(f) => return Err(f),
            Ok(Some(ch)) => {
                got = Some(ch);
                cn = nt;
            },
            Ok(None) => {},
        }
    }
    if got.is_none() {
        got = serial_chunks(c, w, blo, span, base, ns);
        cn = 1;
    }
    let chunks = match got {
        Some(ch) => ch,
        None => return Ok(None),
    };
    proof {
        assert(chunks_ok(chunks@, cn as int, *c, w, gb, ns as int));
        assert(range_fast(*c, w, gb, ns as int, 0, c.n as int));
    }
    let (idxs, best) = collect_picks(&chunks, cn, ns, Ghost(*c), Ghost(w), Ghost(gb));
    proof {
        let vals = all_vals(*c, w, gb, ns as int);
        let g = g_of(w);
        lemma_fast_caps(*c, w, gb, ns as int, vals);
        lemma_fast_max(*c, w, gb, ns as int, vals, best as int);
        assert forall|i: int| 0 <= i < ns implies #[trigger] pick_of(g, crows(*c), srows, best as int)(i)
            == best_slot(*c, w, gb, best as int)(i) by {
            lemma_fast_pick(*c, w, gb, ns as int, vals, best as int, *k, srows, i);
        }
        lemma_range_filter_ext(0, ns as int, pick_of(g, crows(*c), srows, best as int), best_slot(*c, w, gb, best as int));
    }
    Ok(Some((idxs, best)))
}

/// Every row lies in one scan range.
pub proof fn lemma_row_index(nt: int, n: int, r: int)
    requires 1 <= nt, 0 <= r < n,
    ensures exists|u: int| 0 <= u < nt && row_start(u, nt, n) <= r < #[trigger] row_start(u + 1, nt, n),
    decreases nt,
{
    // the ranges are ordered and cover `[0, n)`: take the last range starting at or before `r`
    let q = n / nt;
    assert(q * nt <= n) by (nonlinear_arith) requires q == n / nt, nt >= 1, n >= 0;
    assert(q >= 0) by (nonlinear_arith) requires q == n / nt, nt >= 1, n >= 0;
    if q == 0 || r >= (nt - 1) * q {
        lemma_row_start(nt - 1, nt, n);
        assert(row_start(nt, nt, n) == n);
        if q == 0 {
            assert((nt - 1) * q == 0) by (nonlinear_arith) requires q == 0;
        }
        assert(row_start(nt - 1, nt, n) <= r);
    } else {
        let u = r / q;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(r, q);
        vstd::arithmetic::div_mod::lemma_mod_bound(r, q);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(r, q);
        assert(u * q <= r) by (nonlinear_arith) requires r == q * u + r % q, r % q >= 0;
        assert(r < (u + 1) * q) by (nonlinear_arith) requires r == q * u + r % q, r % q < q;
        assert(u < nt - 1) by (nonlinear_arith) requires r < (nt - 1) * q, u * q <= r, q > 0;
        assert(row_start(u, nt, n) == u * q);
        assert(row_start(u + 1, nt, n) == (u + 1) * q);
    }
}

} // verus!
