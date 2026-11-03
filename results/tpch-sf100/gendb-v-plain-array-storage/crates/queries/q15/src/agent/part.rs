//! The parallel fast path's two phases over partitioned (slot, term) entries.
//!
//! Phase 1 (`PartTask`, `scan_parts`): one task per contiguous `lineitem` row range. Each qualifying row of the
//! range becomes one entry `slot * 2^32 + term` (`pack`; slot = key - base, term = price * (100 - discount) in
//! `(0, 2^32)`), appended to the region of the slot's partition `slot / PART_SLOTS` (`part_of`) in the task's flat
//! buffer: region `p` is `buf[p * cap .. p * cap + cnt[p]]` (`reg`), `cap` entries reserved per partition. The buffer
//! is allocated zeroed on the calling thread (worker bodies cannot allocate); it is large enough that the allocator
//! maps fresh pages, which the worker touches only where it writes. A task's regions hold, for every slot `s`, the
//! SUM of key `base + s` over its range in the region of `s`'s partition (`parts_ok`; `psum` sums the entries of one
//! slot in a list). A full region stops the task with `false` (the caller then scans serially).
//!
//! Phase 2 (`PMergeTask`, `merge_parts`): one task per slot chunk `[a, b)` adds, for each partition overlapping the
//! chunk, the entries of every task's region whose slot lies in the chunk into a dense `i64` chunk (checked); the
//! chunk is then the normal form's SUM of every slot over all rows (`fast::chunk_ok`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::link::query::*;
use crate::gendb_entry::parallel::{MAX_WORKERS, WorkerTask};
use crate::agent::common::selection::*;
use crate::agent::normal::*;
use crate::agent::cols::*;
use crate::agent::bounds::*;
use crate::agent::scan::*;
use crate::agent::fastspec::*;
use crate::agent::fast::{row_start, lemma_row_start, chunk_ok, chunk_best, PART_SLOTS};

verus! {

/// The factor of the slot in an entry.
pub const PACK: u64 = 0x1_0000_0000;

/// Fewer supplier slots than this take the parallel path (slot arithmetic stays far inside `usize`).
pub const PAR_MAX_SLOTS: usize = 0x4000_0000;

/// The partition of slot `s`.
pub open spec fn part_of(s: int) -> int {
    s / (PART_SLOTS as int)
}

/// Partitions for `ns` slots.
pub open spec fn part_count(ns: int) -> int {
    ns / (PART_SLOTS as int) + 1
}

/// The slot of an entry.
pub open spec fn e_slot(e: u64) -> int {
    e as int / (PACK as int)
}

/// The term of an entry.
pub open spec fn e_term(e: u64) -> int {
    e as int % (PACK as int)
}

/// The terms of slot `s` summed over the entries of `l`.
pub open spec fn psum(l: Seq<u64>, s: int) -> int
    decreases l.len(),
{
    if l.len() == 0 { 0 } else { psum(l.drop_last(), s) + if e_slot(l.last()) == s { e_term(l.last()) } else { 0 } }
}

/// One more entry at the end of a list.
pub proof fn lemma_psum_push(l: Seq<u64>, e: u64, s: int)
    ensures psum(l.push(e), s) == psum(l, s) + if e_slot(e) == s { e_term(e) } else { 0 },
{
    assert(l.push(e).drop_last() =~= l);
}

/// Sums of a list prefix one entry longer.
pub proof fn lemma_psum_take(l: Seq<u64>, q: int, s: int)
    requires 0 <= q < l.len(),
    ensures psum(l.take(q + 1), s) == psum(l.take(q), s) + if e_slot(l[q]) == s { e_term(l[q]) } else { 0 },
{
    assert(l.take(q + 1) =~= l.take(q).push(l[q]));
    lemma_psum_push(l.take(q), l[q], s);
}

/// Region `p` of a buffer: the `cnt[p]` entries from `p * cap`.
pub open spec fn reg(buf: Seq<u64>, cnt: Seq<usize>, cap: int, p: int) -> Seq<u64> {
    buf.subrange(p * cap, p * cap + cnt[p] as int)
}

/// The buffer holds `np` regions of `cap` entries, each filled at most to `cap`.
pub open spec fn regions_wf(buf: Seq<u64>, cnt: Seq<usize>, cap: int, np: int) -> bool {
    &&& 1 <= cap <= usize::MAX
    &&& cnt.len() == np
    &&& buf.len() == np * cap
    &&& forall|p: int| 0 <= p < np ==> #[trigger] cnt[p] <= cap
}

/// The SUM of slot `s` held by a buffer: the entries of slot `s` in the region of its partition.
pub open spec fn rslot(buf: Seq<u64>, cnt: Seq<usize>, cap: int, s: int) -> int {
    psum(reg(buf, cnt, cap, part_of(s)), s)
}

/// The regions hold, for every slot `s`, the SUM of key `base + s` over `[lo, hi)`.
pub open spec fn regions_ok(buf: Seq<u64>, cnt: Seq<usize>, cap: int, c: Cols, w: DayWindow, base: int, ns: int, lo: int,
    hi: int) -> bool {
    &&& regions_wf(buf, cnt, cap, part_count(ns))
    &&& forall|s: int| 0 <= s < ns ==> #[trigger] rslot(buf, cnt, cap, s) == gs(c, w, base + s, lo, hi)
}

/// The partition of a slot is one of the `part_count(ns)` partitions, and the slot lies in it.
pub proof fn lemma_part_bound(s: int, ns: int)
    requires 0 <= s < ns,
    ensures 0 <= part_of(s) < part_count(ns), part_of(s) * (PART_SLOTS as int) <= s,
        s < (part_of(s) + 1) * (PART_SLOTS as int),
{
    let w = PART_SLOTS as int;
    vstd::arithmetic::div_mod::lemma_div_is_ordered(s, ns, w);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(s, w);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(s, w);
    vstd::arithmetic::div_mod::lemma_mod_bound(s, w);
    assert(part_of(s) * w <= s) by (nonlinear_arith) requires s == w * (s / w) + s % w, s % w >= 0, part_of(s) == s / w;
    assert(s < (part_of(s) + 1) * w) by (nonlinear_arith) requires s == w * (s / w) + s % w, s % w < w, part_of(s) == s / w;
}

/// Partition `p`'s slot range starts inside `[0, ns]` and ends at most one partition beyond.
pub proof fn lemma_part_start(p: int, ns: int)
    requires 0 <= p < part_count(ns), ns >= 0,
    ensures 0 <= p * (PART_SLOTS as int) <= ns, (p + 1) * (PART_SLOTS as int) <= ns + (PART_SLOTS as int),
{
    let w = PART_SLOTS as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ns, w);
    vstd::arithmetic::div_mod::lemma_mod_bound(ns, w);
    assert(p * w <= (ns / w) * w) by (nonlinear_arith) requires p <= ns / w, w >= 1;
    assert(0 <= p * w) by (nonlinear_arith) requires p >= 0, w >= 1;
    assert((ns / w) * w == w * (ns / w));
    assert((p + 1) * w == p * w + w) by (nonlinear_arith);
}

/// A slot inside partition `p`'s slot range belongs to partition `p`.
pub proof fn lemma_part_of_range(s: int, p: int)
    requires 0 <= p, p * (PART_SLOTS as int) <= s < (p + 1) * (PART_SLOTS as int),
    ensures part_of(s) == p,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(s, PART_SLOTS as int, p, s - p * (PART_SLOTS as int));
}

/// Region `p` ends inside the buffer, below every later region.
pub proof fn lemma_region_bounds(cap: int, np: int, p: int, q: int)
    requires cap >= 1, 0 <= p < np, 0 <= q < np,
    ensures
        0 <= p * cap,
        (p + 1) * cap <= np * cap,
        p * cap + cap == (p + 1) * cap,
        p < q ==> (p + 1) * cap <= q * cap,
{
    assert(0 <= p * cap) by (nonlinear_arith) requires p >= 0, cap >= 1;
    assert((p + 1) * cap <= np * cap) by (nonlinear_arith) requires p + 1 <= np, cap >= 1;
    assert(p * cap + cap == (p + 1) * cap) by (nonlinear_arith);
    assert(p < q ==> (p + 1) * cap <= q * cap) by (nonlinear_arith) requires cap >= 1;
}

/// Appending entry `e` to region `p` (writing `buf[p * cap + cnt[p]]`, then counting it) extends region `p` by `e`
/// and leaves the other regions.
pub proof fn lemma_region_push(buf: Seq<u64>, cnt: Seq<usize>, cap: int, np: int, p: int, e: u64)
    requires regions_wf(buf, cnt, cap, np), 0 <= p < np, cnt[p] < cap,
    ensures ({
        let i = p * cap + cnt[p] as int;
        let buf2 = buf.update(i, e);
        let cnt2 = cnt.update(p, (cnt[p] + 1) as usize);
        &&& 0 <= i < buf.len()
        &&& regions_wf(buf2, cnt2, cap, np)
        &&& reg(buf2, cnt2, cap, p) == reg(buf, cnt, cap, p).push(e)
        &&& forall|q: int| 0 <= q < np && q != p ==> #[trigger] reg(buf2, cnt2, cap, q) == reg(buf, cnt, cap, q)
    }),
{
    let i = p * cap + cnt[p] as int;
    let buf2 = buf.update(i, e);
    let cnt2 = cnt.update(p, (cnt[p] + 1) as usize);
    lemma_region_bounds(cap, np, p, p);
    let r1 = reg(buf, cnt, cap, p);
    let r2 = reg(buf2, cnt2, cap, p);
    assert(cnt2[p] as int == cnt[p] as int + 1);
    assert(r2.len() == r1.len() + 1);
    assert forall|k: int| 0 <= k < r1.len() implies r2[k] == r1[k] by {
        assert(p * cap + k != i);
    }
    assert(r2[r1.len() as int] == e);
    assert(r2 =~= r1.push(e));
    assert forall|q: int| 0 <= q < np && q != p implies #[trigger] reg(buf2, cnt2, cap, q) == reg(buf, cnt, cap, q) by {
        lemma_region_bounds(cap, np, q, p);
        lemma_region_bounds(cap, np, p, q);
        assert(cnt[q] <= cap);
        assert(reg(buf2, cnt2, cap, q) =~= reg(buf, cnt, cap, q));
    }
    assert forall|q: int| 0 <= q < np implies #[trigger] cnt2[q] <= cap by {
        assert(cnt[q] <= cap);
    }
}

/// The entry of slot `s` and term `t`.
pub fn pack(s: usize, t: u64) -> (e: u64)
    requires s < PACK, 0 < t < PACK,
    ensures e_slot(e) == s, e_term(e) == t,
    no_unwind
{
    proof {
        assert(s as int * (PACK as int) + t as int <= u64::MAX) by (nonlinear_arith)
            requires s < 0x1_0000_0000int, t < 0x1_0000_0000int;
    }
    let e = s as u64 * PACK + t;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(e as int, PACK as int, s as int, t as int);
    }
    e
}

/// Stage 2 of one block for phase 1: appends the entry of every listed row (offsets `sel[..k]` from `start`, the list
/// `s1`) to its partition's region. On success every listed row meets the assumptions and slot `s` gained the terms
/// of key `base + s`; `false` when a row breaks an assumption or a region is full.
pub fn push_listed(c: &Cols, w: DayWindow, base: i64, ns: usize, start: usize, k: usize, sel: &Vec<u32>,
    Ghost(s1): Ghost<Seq<int>>, buf: &mut Vec<u64>, cnt: &mut Vec<usize>, cap: usize) -> (ok: bool)
    requires
        cols_wf(*c),
        ns < PAR_MAX_SLOTS,
        sel_matches(sel@, k as int, start as int, s1),
        forall|t: int| 0 <= t < s1.len() ==> 0 <= #[trigger] s1[t] < c.n && p_ship(*c, w)(s1[t]),
        regions_wf(old(buf)@, old(cnt)@, cap as int, part_count(ns as int)),
    ensures
        regions_wf(final(buf)@, final(cnt)@, cap as int, part_count(ns as int)),
        ok ==> forall|t: int| 0 <= t < s1.len() ==> row_fast(*c, w, base as int, ns as int, #[trigger] s1[t]),
        ok ==> forall|s: int| 0 <= s < ns ==> #[trigger] rslot(final(buf)@, final(cnt)@, cap as int, s)
            == rslot(old(buf)@, old(cnt)@, cap as int, s) + seq_sum(s1, f_key(*c, base + s)),
    no_unwind
{
    let ghost b0 = buf@;
    let ghost c0 = cnt@;
    let ghost np = part_count(ns as int);
    let blen = buf.len();
    let mut j: usize = 0;
    proof {
        assert(s1.take(0) =~= Seq::<int>::empty());
    }
    while j < k
        invariant
            cols_wf(*c),
            ns < PAR_MAX_SLOTS,
            sel_matches(sel@, k as int, start as int, s1),
            forall|t: int| 0 <= t < s1.len() ==> 0 <= #[trigger] s1[t] < c.n && p_ship(*c, w)(s1[t]),
            np == part_count(ns as int),
            regions_wf(buf@, cnt@, cap as int, np),
            blen == buf@.len(),
            j <= k,
            forall|t: int| 0 <= t < j ==> row_fast(*c, w, base as int, ns as int, #[trigger] s1[t]),
            forall|s: int| 0 <= s < ns ==> #[trigger] rslot(buf@, cnt@, cap as int, s)
                == rslot(b0, c0, cap as int, s) + seq_sum(s1.take(j as int), f_key(*c, base + s)),
        decreases k - j,
    {
        let off = sel[j];
        let ghost r = s1[j as int];
        proof {
            assert(start + off as int == r);
            lemma_rev_bound(*c, r);
        }
        let row = start + off as usize;
        let key = c.supp[row];
        let slot = key as i128 - base as i128;
        if slot < 0 || slot >= ns as i128 {
            return false;
        }
        let t = c.price[row] * (100 - c.disc[row]);
        if t <= 0 || t >= 0x1_0000_0000i128 {
            return false;
        }
        let s = slot as usize;
        let e = pack(s, t as u64);
        let pi = s / PART_SLOTS;
        proof {
            lemma_part_bound(s as int, ns as int);
        }
        let q = cnt[pi];
        if q >= cap {
            return false;
        }
        proof {
            lemma_region_push(buf@, cnt@, cap as int, np, pi as int, e);
            lemma_region_bounds(cap as int, np, pi as int, pi as int);
        }
        let ghost bb = buf@;
        let ghost cb = cnt@;
        buf[pi * cap + q] = e;
        cnt[pi] = q + 1;
        proof {
            assert(buf@ == bb.update(pi * cap + q, e));
            assert(cnt@ == cb.update(pi as int, (q + 1) as usize));
            lemma_take_step(s1, j as int);
            assert forall|s2: int| 0 <= s2 < ns implies #[trigger] rslot(buf@, cnt@, cap as int, s2)
                == rslot(b0, c0, cap as int, s2) + seq_sum(s1.take(j + 1), f_key(*c, base + s2)) by {
                lemma_seq_sum_push(s1.take(j as int), r, f_key(*c, base + s2));
                lemma_part_bound(s2, ns as int);
                assert(rslot(bb, cb, cap as int, s2) == rslot(b0, c0, cap as int, s2) + seq_sum(s1.take(j as int), f_key(*c, base + s2)));
                if part_of(s2) == pi as int {
                    lemma_psum_push(reg(bb, cb, cap as int, pi as int), e, s2);
                    if s2 == s as int {
                        assert(f_key(*c, base + s2)(r) == t);
                    } else {
                        assert(f_key(*c, base + s2)(r) == 0);
                    }
                } else {
                    assert(reg(buf@, cnt@, cap as int, part_of(s2)) == reg(bb, cb, cap as int, part_of(s2)));
                    assert(c.supp@[r] as int != base + s2);
                    assert(f_key(*c, base + s2)(r) == 0);
                }
            }
            assert(row_fast(*c, w, base as int, ns as int, r));
        }
        j = j + 1;
    }
    proof {
        assert(s1.take(k as int) =~= s1);
    }
    true
}

/// Phase 1 over the rows `[lo, hi)` into the regions of `buf` (all counts 0 on entry; `sel`: scratch of at least
/// `BLOCK_ROWS` offsets). On success the regions hold the range's SUMs and every row meets the assumptions.
pub fn scan_parts(c: &Cols, w: DayWindow, blo: u32, span: u32, base: i64, ns: usize, lo: usize, hi: usize,
    buf: &mut Vec<u64>, cnt: &mut Vec<usize>, cap: usize, sel: &mut Vec<u32>) -> (ok: bool)
    requires
        cols_wf(*c),
        test_ok(w, blo, span),
        ns < PAR_MAX_SLOTS,
        lo <= hi <= c.n,
        regions_wf(old(buf)@, old(cnt)@, cap as int, part_count(ns as int)),
        forall|p: int| 0 <= p < part_count(ns as int) ==> #[trigger] old(cnt)@[p] == 0,
        old(sel)@.len() >= BLOCK_ROWS,
    ensures
        regions_wf(final(buf)@, final(cnt)@, cap as int, part_count(ns as int)),
        ok ==> regions_ok(final(buf)@, final(cnt)@, cap as int, *c, w, base as int, ns as int, lo as int, hi as int),
        ok ==> range_fast(*c, w, base as int, ns as int, lo as int, hi as int),
    no_unwind
{
    let ghost p = p_ship(*c, w);
    let ghost g = q_spec(qb_of(w));
    proof {
        assert forall|s: int| 0 <= s < ns implies #[trigger] rslot(buf@, cnt@, cap as int, s) == gs(*c, w, base + s, lo as int, lo as int) by {
            lemma_part_bound(s, ns as int);
            let ps = part_of(s);
            lemma_region_bounds(cap as int, part_count(ns as int), ps, ps);
            assert(cnt@[ps] == 0);
            assert(reg(buf@, cnt@, cap as int, ps) == buf@.subrange(ps * cap, ps * cap + 0));
            assert(reg(buf@, cnt@, cap as int, ps) =~= Seq::<u64>::empty());
            lemma_empty(g, crows(*c), lo as int, seq![Val::Int(base + s)], 0);
        }
    }
    let mut start: usize = lo;
    while start < hi
        invariant
            cols_wf(*c),
            test_ok(w, blo, span),
            ns < PAR_MAX_SLOTS,
            lo <= start <= hi <= c.n,
            sel@.len() >= BLOCK_ROWS,
            p == p_ship(*c, w),
            g == q_spec(qb_of(w)),
            regions_ok(buf@, cnt@, cap as int, *c, w, base as int, ns as int, lo as int, start as int),
            range_fast(*c, w, base as int, ns as int, lo as int, start as int),
        decreases hi - start,
    {
        let end = if hi - start > BLOCK_ROWS { start + BLOCK_ROWS } else { hi };
        let k = select_ship(c, w, blo, span, start, end, sel);
        let ghost s1 = range_filter(start as int, end as int, p);
        proof {
            lemma_range_filter_bounds(start as int, end as int, p);
            assert forall|t: int| 0 <= t < s1.len() implies 0 <= #[trigger] s1[t] < c.n && p(s1[t]) by {
                lemma_range_filter_members(start as int, end as int, p, t);
            }
        }
        let ghost bb = buf@;
        let ghost cb = cnt@;
        let ok = push_listed(c, w, base, ns, start, k, sel, Ghost(s1), buf, cnt, cap);
        if !ok {
            return false;
        }
        proof {
            assert forall|s: int| 0 <= s < ns implies #[trigger] rslot(buf@, cnt@, cap as int, s) == gs(*c, w, base + s, lo as int, end as int) by {
                let f = f_key(*c, base + s);
                assert(rslot(bb, cb, cap as int, s) == gs(*c, w, base + s, lo as int, start as int));
                lemma_sum_range_filter(start as int, end as int, p, f);
                lemma_gs_range(*c, w, base + s, start as int, end as int);
                lemma_split(g, crows(*c), lo as int, start as int, end as int, seq![Val::Int(base + s)], 0);
            }
            assert forall|r: int| lo <= r < end implies #[trigger] row_fast(*c, w, base as int, ns as int, r) by {
                if r >= start && p(r) {
                    lemma_range_filter_has(start as int, end as int, p, r);
                    let t = choose|t: int| 0 <= t < s1.len() && s1[t] == r;
                    assert(row_fast(*c, w, base as int, ns as int, s1[t]));
                }
            }
        }
        start = end;
    }
    true
}

/// Phase 1 of one row range as a `fork_join` task: the buffer and region counts (allocated on the calling thread,
/// filled here) and whether the range met the assumptions.
pub struct PartTask {
    pub c: Cols,
    pub w: DayWindow,
    pub blo: u32,
    pub span: u32,
    pub base: i64,
    pub ns: usize,
    pub lo: usize,
    pub hi: usize,
    pub buf: Vec<u64>,
    pub cnt: Vec<usize>,
    pub cap: usize,
    pub sel: Vec<u32>,
}

/// A phase-1 task's output: buffer, region counts, entries reserved per region, success.
pub type PartOut = (Vec<u64>, Vec<usize>, usize, bool);

/// The regions of a phase-1 output hold the SUMs over `[lo, hi)`.
pub open spec fn parts_ok(o: PartOut, c: Cols, w: DayWindow, base: int, ns: int, lo: int, hi: int) -> bool {
    regions_ok(o.0@, o.1@, o.2 as int, c, w, base, ns, lo, hi)
}

impl WorkerTask for PartTask {
    type Output = PartOut;

    open spec fn pre(&self) -> bool {
        &&& cols_wf(self.c)
        &&& test_ok(self.w, self.blo, self.span)
        &&& self.ns < PAR_MAX_SLOTS
        &&& self.lo <= self.hi <= self.c.n
        &&& regions_wf(self.buf@, self.cnt@, self.cap as int, part_count(self.ns as int))
        &&& forall|p: int| 0 <= p < part_count(self.ns as int) ==> #[trigger] self.cnt@[p] == 0
        &&& self.sel@.len() >= BLOCK_ROWS
    }

    open spec fn post(&self, out: PartOut) -> bool {
        &&& out.2 == self.cap
        &&& regions_wf(out.0@, out.1@, out.2 as int, part_count(self.ns as int))
        &&& out.3 ==> parts_ok(out, self.c, self.w, self.base as int, self.ns as int, self.lo as int, self.hi as int)
        &&& out.3 ==> range_fast(self.c, self.w, self.base as int, self.ns as int, self.lo as int, self.hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: PartOut) {
        let PartTask { c, w, blo, span, base, ns, lo, hi, buf, cnt, cap, sel } = self;
        let mut buf = buf;
        let mut cnt = cnt;
        let mut sel = sel;
        let ok = scan_parts(&c, w, blo, span, base, ns, lo, hi, &mut buf, &mut cnt, cap, &mut sel);
        (buf, cnt, cap, ok)
    }
}

// ------------------------------------------------------------------------------------------------ phase 2

/// The phase-1 outputs of tasks `0..nt`: task `t`'s regions hold the SUMs over its row range.
pub open spec fn pscans_ok(outs: Seq<PartOut>, nt: int, c: Cols, w: DayWindow, base: int, ns: int) -> bool {
    &&& outs.len() == nt
    &&& forall|t: int| 0 <= t < nt ==> parts_ok(#[trigger] outs[t], c, w, base, ns,
            row_start(t, nt, c.n as int), row_start(t + 1, nt, c.n as int))
}

/// Region `p` of task `t`'s output.
pub open spec fn oreg(outs: Seq<PartOut>, t: int, p: int) -> Seq<u64> {
    reg(outs[t].0@, outs[t].1@, outs[t].2 as int, p)
}

/// Slot `s` summed over the outputs of tasks `0..t`.
pub open spec fn ptot(outs: Seq<PartOut>, s: int, t: int) -> int
    decreases t,
{
    if t <= 0 { 0 } else { ptot(outs, s, t - 1) + psum(oreg(outs, t - 1, part_of(s)), s) }
}

/// The outputs of tasks `0..t` together hold the SUM of slot `s` over the rows of those tasks.
pub proof fn lemma_ptot(outs: Seq<PartOut>, nt: int, c: Cols, w: DayWindow, base: int, ns: int, s: int, t: int)
    requires pscans_ok(outs, nt, c, w, base, ns), 1 <= nt, 0 <= s < ns, 0 <= t <= nt,
    ensures ptot(outs, s, t) == gs(c, w, base + s, 0, row_start(t, nt, c.n as int)),
    decreases t,
{
    let n = c.n as int;
    if t == 0 {
        lemma_row_start(0, nt, n);
        lemma_empty(g_of(w), crows(c), 0, seq![Val::Int(base + s)], 0);
    } else {
        lemma_ptot(outs, nt, c, w, base, ns, s, t - 1);
        lemma_row_start(t - 1, nt, n);
        lemma_row_start(0, nt, n);
        assert(parts_ok(outs[t - 1], c, w, base, ns, row_start(t - 1, nt, n), row_start(t, nt, n)));
        assert(rslot(outs[t - 1].0@, outs[t - 1].1@, outs[t - 1].2 as int, s)
            == gs(c, w, base + s, row_start(t - 1, nt, n), row_start(t, nt, n)));
        lemma_split(g_of(w), crows(c), 0, row_start(t - 1, nt, n), row_start(t, nt, n), seq![Val::Int(base + s)], 0);
    }
}

/// The merged value of chunk slot `j` (slot `a + j`) after the partitions before `p`, the regions of tasks before
/// `t` in partition `p`, and the first `q` entries of task `t`'s region there.
pub open spec fn merged(outs: Seq<PartOut>, nt: int, a: int, j: int, p: int, t: int, q: int) -> int {
    let s = a + j;
    if part_of(s) < p {
        ptot(outs, s, nt)
    } else if part_of(s) == p {
        ptot(outs, s, t) + psum(oreg(outs, t, p).take(q), s)
    } else {
        0
    }
}

/// Phase 2 of slots `[a, b)`: the dense chunk of their SUMs over all rows (`false` when a sum leaves `i64`).
pub fn merge_parts(outs: &Vec<PartOut>, nt: usize, a: usize, b: usize, vals: &mut Vec<i64>, Ghost(c): Ghost<Cols>,
    Ghost(w): Ghost<DayWindow>, Ghost(base): Ghost<int>, ns: usize) -> (ok: bool)
    requires
        1 <= nt <= MAX_WORKERS,
        pscans_ok(outs@, nt as int, c, w, base, ns as int),
        ns < PAR_MAX_SLOTS,
        a < b <= ns,
        old(vals)@.len() == b - a,
        forall|j: int| 0 <= j < b - a ==> #[trigger] old(vals)@[j] == 0i64,
    ensures
        final(vals)@.len() == b - a,
        ok ==> chunk_ok(final(vals)@, a as int, c, w, base),
    no_unwind
{
    let ghost os = outs@;
    let pa = a / PART_SLOTS;
    let pz = (b - 1) / PART_SLOTS;
    proof {
        lemma_part_bound(a as int, ns as int);
        lemma_part_bound(b - 1, ns as int);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(a as int, b - 1, PART_SLOTS as int);
        assert forall|j: int| 0 <= j < b - a implies (#[trigger] vals@[j]) as int == merged(os, nt as int, a as int, j, pa as int, 0, 0) by {
            vstd::arithmetic::div_mod::lemma_div_is_ordered(a as int, a + j, PART_SLOTS as int);
            if part_of(a + j) == pa as int {
                assert(oreg(os, 0, pa as int).take(0) =~= Seq::<u64>::empty());
            }
        }
    }
    let mut p = pa;
    while p <= pz
        invariant
            1 <= nt <= MAX_WORKERS,
            pscans_ok(os, nt as int, c, w, base, ns as int),
            os == outs@,
            ns < PAR_MAX_SLOTS,
            a < b <= ns,
            pa as int == part_of(a as int),
            pz as int == part_of(b - 1),
            pz < part_count(ns as int),
            pa <= p <= pz + 1,
            vals@.len() == b - a,
            forall|j: int| 0 <= j < b - a ==> (#[trigger] vals@[j]) as int == merged(os, nt as int, a as int, j, p as int, 0, 0),
        decreases pz + 1 - p,
    {
        // the chunk's slots in partition `p`
        proof {
            lemma_part_start(p as int, ns as int);
        }
        let s_lo = if p * PART_SLOTS > a { p * PART_SLOTS } else { a };
        let s_hi = if (p + 1) * PART_SLOTS < b { (p + 1) * PART_SLOTS } else { b };
        let mut t: usize = 0;
        while t < nt
            invariant
                1 <= nt <= MAX_WORKERS,
                pscans_ok(os, nt as int, c, w, base, ns as int),
                os == outs@,
                ns < PAR_MAX_SLOTS,
                a < b <= ns,
                pz < part_count(ns as int),
                pa as int == part_of(a as int),
                pa <= p <= pz,
                s_lo as int == if p * PART_SLOTS > a { p * PART_SLOTS } else { a as int },
                s_hi as int == if (p + 1) * PART_SLOTS < b { (p + 1) * PART_SLOTS } else { b as int },
                t <= nt,
                vals@.len() == b - a,
                forall|j: int| 0 <= j < b - a ==> (#[trigger] vals@[j]) as int == merged(os, nt as int, a as int, j, p as int, t as int, 0),
            decreases nt - t,
        {
            let o = &outs[t];
            let cap = o.2;
            let len = o.1[p];
            let blen = o.0.len();
            proof {
                assert(parts_ok(os[t as int], c, w, base, ns as int, row_start(t as int, nt as int, c.n as int),
                    row_start(t + 1, nt as int, c.n as int)));
                assert(len <= cap);
                assert(p < part_count(ns as int));
                lemma_region_bounds(cap as int, part_count(ns as int), p as int, p as int);
            }
            let from = p * cap;
            let mut q: usize = 0;
            while q < len
                invariant
                    1 <= nt <= MAX_WORKERS,
                    pscans_ok(os, nt as int, c, w, base, ns as int),
                    os == outs@,
                    a < b <= ns,
                    pz < part_count(ns as int),
                    pa <= p <= pz,
                    t < nt,
                    *o == os[t as int],
                    cap == o.2,
                    len == o.1@[p as int],
                    len <= cap,
                    from == p * cap,
                    from + cap <= o.0@.len(),
                    blen == o.0@.len(),
                    q <= len,
                    s_lo as int == if p * PART_SLOTS > a { p * PART_SLOTS } else { a as int },
                    s_hi as int == if (p + 1) * PART_SLOTS < b { (p + 1) * PART_SLOTS } else { b as int },
                    vals@.len() == b - a,
                    forall|j: int| 0 <= j < b - a ==> (#[trigger] vals@[j]) as int == merged(os, nt as int, a as int, j, p as int, t as int, q as int),
                decreases len - q,
            {
                let e = o.0[from + q];
                let s = (e / PACK) as usize;
                let ghost before = vals@;
                proof {
                    assert(oreg(os, t as int, p as int)[q as int] == e);
                }
                if s_lo <= s && s < s_hi {
                    let cur = vals[s - a];
                    let add = (e % PACK) as i64;
                    if cur > 0x7FFF_FFFF_FFFF_FFFFi64 - add {
                        return false;
                    }
                    vals[s - a] = cur + add;
                }
                proof {
                    assert forall|j: int| 0 <= j < b - a implies (#[trigger] vals@[j]) as int
                        == merged(os, nt as int, a as int, j, p as int, t as int, q + 1) by {
                        lemma_psum_take(oreg(os, t as int, p as int), q as int, a + j);
                        lemma_part_bound(a + j, ns as int);
                        if s_lo <= s && s < s_hi {
                            lemma_part_of_range(s as int, p as int);
                        }
                        if j != s - a {
                            assert(vals@[j] == before[j]);
                        }
                    }
                }
                q = q + 1;
            }
            proof {
                assert(oreg(os, t as int, p as int).take(len as int) =~= oreg(os, t as int, p as int));
                assert forall|j: int| 0 <= j < b - a implies (#[trigger] vals@[j]) as int
                    == merged(os, nt as int, a as int, j, p as int, t + 1, 0) by {
                    if t + 1 < nt {
                        assert(oreg(os, t + 1, p as int).take(0) =~= Seq::<u64>::empty());
                    }
                }
            }
            t = t + 1;
        }
        proof {
            assert forall|j: int| 0 <= j < b - a implies (#[trigger] vals@[j]) as int
                == merged(os, nt as int, a as int, j, p + 1, 0, 0) by {
                if part_of(a + j) == p + 1 {
                    assert(oreg(os, 0, p + 1).take(0) =~= Seq::<u64>::empty());
                }
            }
        }
        p = p + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < b - a implies (#[trigger] vals@[j]) as int == gs(c, w, base + a + j, 0, c.n as int) by {
            lemma_part_bound(a + j, ns as int);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(a + j, b - 1, PART_SLOTS as int);
            lemma_ptot(os, nt as int, c, w, base, ns as int, a + j, nt as int);
            lemma_row_start(nt - 1, nt as int, c.n as int);
            assert(base + (a + j) == base + a + j);
        }
    }
    true
}

/// Phase 2 of one slot chunk as a `fork_join` task: the chunk (allocated zeroed on the calling thread), its largest
/// value, success.
pub struct PMergeTask {
    pub outs: Arc<Vec<PartOut>>,
    pub nt: usize,
    pub a: usize,
    pub b: usize,
    pub vals: Vec<i64>,
    pub c: Ghost<Cols>,
    pub w: Ghost<DayWindow>,
    pub base: Ghost<int>,
    pub ns: usize,
}

impl WorkerTask for PMergeTask {
    type Output = (Vec<i64>, i64, bool);

    open spec fn pre(&self) -> bool {
        &&& 1 <= self.nt <= MAX_WORKERS
        &&& pscans_ok(self.outs@, self.nt as int, self.c@, self.w@, self.base@, self.ns as int)
        &&& self.ns < PAR_MAX_SLOTS
        &&& self.a <= self.b <= self.ns
        &&& self.vals@.len() == self.b - self.a
        &&& forall|j: int| 0 <= j < self.b - self.a ==> #[trigger] self.vals@[j] == 0i64
    }

    open spec fn post(&self, out: (Vec<i64>, i64, bool)) -> bool {
        &&& out.0@.len() == self.b - self.a
        &&& out.2 ==> chunk_ok(out.0@, self.a as int, self.c@, self.w@, self.base@)
        &&& out.2 ==> is_best(out.0@, out.1 as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.a as u64, self.b as u64)
    }

    fn run(self) -> (out: (Vec<i64>, i64, bool)) {
        let PMergeTask { outs, nt, a, b, vals, c, w, base, ns } = self;
        let mut vals = vals;
        let ok = if a < b { merge_parts(&outs, nt, a, b, &mut vals, c, w, base, ns) } else { true };
        let best = chunk_best(&vals);
        (vals, best, ok)
    }
}

} // verus!
