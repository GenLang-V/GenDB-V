//! The fast path's scan of one `lineitem` row range `[lo, hi)` (`scan_range`, on the calling thread): a
//! dense SUM table with one `i64` slot per supplier key `base + s`, `s < ns`.
//!
//! Per block of `BLOCK_ROWS` rows: `select_ship` lists the rows whose shipdate lies in the window (64-row bitmasks
//! whose set bits become offsets in `sel`; only the 4-byte shipdate column is read for every row); then each listed row
//! adds `price * (100 - discount)` to the slot of its key, in two passes: the gathers of the listed rows' columns
//! into (slot, term) entries (`gather_listed`), then the table updates (`add_entries`). Keeping the table out of the
//! gather loop lets the column loads of many rows overlap (~13% faster on one thread than one fused loop). The fast
//! path assumes (and checks, row by row) what dbgen's data satisfies: every qualifying row's key is a slot
//! (`base <= key < base + ns`), its term is positive and the slot sums stay inside `i64`. A row breaking an
//! assumption stops the scan with `false`; the caller then takes the general path.
//!
//! Meaning: slot `s` of a successful scan is the normal form's SUM of key `base + s` over the range (`gs`), and every
//! qualifying row of the range meets the assumptions (`range_fast`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::query::*;
use crate::agent::common::selection::*;
use crate::agent::common::bitsel::*;
use crate::agent::normal::*;
use crate::agent::cols::*;
use crate::agent::bounds::*;

verus! {

/// Rows per block (offsets in a block fit `u32`); also the length of a task's offset buffer.
pub const BLOCK_ROWS: usize = 16384;

/// The shipdate of row `r` lies in the window.
pub open spec fn p_ship(c: Cols, w: DayWindow) -> spec_fn(int) -> bool {
    |r: int| w.lo <= c.ship@[r] && c.ship@[r] < w.hi
}

/// The summed coefficient of row `r` (scale 4).
pub open spec fn rev(c: Cols, r: int) -> int {
    c.price@[r] as int * (100 - c.disc@[r] as int)
}

/// Row `r`'s term for key `k`: its coefficient when its key is `k`, else 0.
pub open spec fn f_key(c: Cols, k: int) -> spec_fn(int) -> int {
    |r: int| if c.supp@[r] as int == k { rev(c, r) } else { 0 }
}

/// The normal form's SUM of key `k` over the rows `[lo, hi)`.
pub open spec fn gs(c: Cols, w: DayWindow, k: int, lo: int, hi: int) -> int {
    gsum(q_spec(qb_of(w)), crows(c).subrange(lo, hi), seq![Val::Int(k)], 0)
}

/// Row `r` meets the fast path's assumptions: when it qualifies, its key is a slot and its term is positive.
pub open spec fn row_fast(c: Cols, w: DayWindow, base: int, ns: int, r: int) -> bool {
    p_ship(c, w)(r) ==> (base <= c.supp@[r] as int && (c.supp@[r] as int) < base + ns && rev(c, r) > 0)
}

/// Every row of `[lo, hi)` meets the fast path's assumptions.
pub open spec fn range_fast(c: Cols, w: DayWindow, base: int, ns: int, lo: int, hi: int) -> bool {
    forall|r: int| lo <= r < hi ==> #[trigger] row_fast(c, w, base, ns, r)
}

/// Slot `s` of `t` is the SUM of key `base + s` over `[lo, hi)`.
pub open spec fn table_ok(t: Seq<i64>, c: Cols, w: DayWindow, base: int, ns: int, lo: int, hi: int) -> bool {
    &&& t.len() == ns
    &&& forall|s: int| 0 <= s < ns ==> (#[trigger] t[s]) as int == gs(c, w, base + s, lo, hi)
}

/// The stage-1 test values: the shipdate `d` is in the window exactly when `(d + 2^31) - blo < span` (wrapping).
pub open spec fn test_ok(w: DayWindow, blo: u32, span: u32) -> bool {
    &&& blo as int == w.lo as int + 0x8000_0000
    &&& span as int == if w.hi > w.lo { w.hi as int - w.lo as int } else { 0 }
}

/// The stage-1 test values of a window.
pub fn make_test(w: DayWindow) -> (r: (u32, u32))
    ensures test_ok(w, r.0, r.1),
{
    let blo = (w.lo as i64 + 0x8000_0000i64) as u32;
    let span: u32 = if w.hi > w.lo { (w.hi as i64 - w.lo as i64) as u32 } else { 0 };
    (blo, span)
}

/// The normal form's SUM of key `k` over a range is the range sum of the guarded terms.
pub proof fn lemma_gs_range(c: Cols, w: DayWindow, k: int, lo: int, hi: int)
    requires 0 <= lo <= hi <= c.n,
    ensures gs(c, w, k, lo, hi) == range_sum(lo, hi, guard(p_ship(c, w), f_key(c, k))),
    decreases hi - lo,
{
    let g = q_spec(qb_of(w));
    let e = seq![Val::Int(k)];
    if hi == lo {
        lemma_empty(g, crows(c), lo, e, 0);
    } else {
        lemma_gs_range(c, w, k, lo, hi - 1);
        lemma_range_step(g, crows(c), lo, hi - 1, e, 0);
        let r = hi - 1;
        assert(crows(c)[r] == crow(c, r));
        let key = seq![Val::Int(c.supp@[r] as int)];
        assert((g.key)(crow(c, r)) == key);
        if c.supp@[r] as int == k {
            assert(key =~= e);
        } else {
            assert(key[0] != e[0]);
        }
        assert(hit(g, crow(c, r), e) == (p_ship(c, w)(r) && c.supp@[r] as int == k));
        assert((g.arg)(0, crow(c, r)) == rev(c, r));
    }
}

/// The coefficient of a row fits `i128` (both factors are numeric(15,2) coefficients).
pub proof fn lemma_rev_bound(c: Cols, r: int)
    requires cols_wf(c), 0 <= r < c.n,
    ensures
        -1_000_000_000_000_000_100 < 100 - (c.disc@[r] as int),
        100 - (c.disc@[r] as int) < 1_000_000_000_000_000_100,
        -1_000_000_000_000_000_000_000_000_000_000_000 < rev(c, r),
        rev(c, r) < 1_000_000_000_000_000_000_000_000_000_000_000,
{
    let p = c.price@[r] as int;
    let f = 100 - c.disc@[r] as int;
    assert(coeff_ok(c.price@[r]) && coeff_ok(c.disc@[r]));
    assert(-1_000_000_000_000_000_000_000_000_000_000_000 < p * f < 1_000_000_000_000_000_000_000_000_000_000_000)
        by (nonlinear_arith)
        requires -1_000_000_000_000_000 < p < 1_000_000_000_000_000, -1_000_000_000_000_000_100 < f < 1_000_000_000_000_000_100;
}

/// The stage-1 test of the 64-row group from row `q`: bit `j` of the mask is set when row `q + j`'s shipdate lies in
/// the window (a fixed-count loop the compiler turns into vector compares).
pub fn ship_mask(c: &Cols, w: DayWindow, blo: u32, span: u32, q: usize) -> (m: u64)
    requires cols_wf(*c), test_ok(w, blo, span), q + 64 <= c.n,
    ensures mask_of(m, q as int, p_ship(*c, w)),
    no_unwind
{
    // A 64-element view of the group: the compiler drops the per-row bounds checks and unrolls the loop.
    let (_, tail) = c.ship.split_at(q);
    let (g, _) = tail.split_at(64);
    proof {
        assert(g@ =~= c.ship@.subrange(q as int, q + 64));
    }
    let mut m: u64 = 0;
    let mut j: usize = 0;
    proof {
        assert forall|i: int| 0 <= i < 64 implies !#[trigger] bit_set(0u64, i) by {
            let x = i as u64;
            assert((0u64 >> x) & 1u64 == 0u64) by (bit_vector);
        }
    }
    while j < 64
        invariant
            cols_wf(*c),
            test_ok(w, blo, span),
            q + 64 <= c.n,
            g@ == c.ship@.subrange(q as int, q + 64),
            j <= 64,
            forall|i: int| 0 <= i < j ==> #[trigger] bit_set(m, i) == p_ship(*c, w)(q + i),
            forall|i: int| j <= i < 64 ==> !#[trigger] bit_set(m, i),
        decreases 64 - j,
    {
        let d = g[j];
        let biased = (d as i64 + 0x8000_0000i64) as u32;
        let keep = biased.wrapping_sub(blo) < span;
        proof {
            assert(d == c.ship@[q + j]);
            assert(keep == (w.lo <= d && d < w.hi));
        }
        m = mask_set_bit(m, j as u64, keep);
        j = j + 1;
    }
    m
}

/// Stage 1: the rows of `[start, end)` whose shipdate is in the window, as offsets from `start` in `sel`: 64-row
/// groups by mask (`ship_mask`, `append_mask`), the last `< 64` rows one by one.
pub fn select_ship(c: &Cols, w: DayWindow, blo: u32, span: u32, start: usize, end: usize, sel: &mut Vec<u32>) -> (k: usize)
    requires
        cols_wf(*c),
        test_ok(w, blo, span),
        start <= end <= c.n,
        end - start <= BLOCK_ROWS,
        end - start <= old(sel)@.len(),
    ensures
        final(sel)@.len() == old(sel)@.len(),
        k <= end - start,
        sel_matches(final(sel)@, k as int, start as int, range_filter(start as int, end as int, p_ship(*c, w))),
    no_unwind
{
    let ghost p = p_ship(*c, w);
    let mut k: usize = 0;
    let mut i: usize = start;
    while end - i >= 64
        invariant
            cols_wf(*c),
            start <= i <= end <= c.n,
            end - start <= BLOCK_ROWS,
            end - start <= sel@.len(),
            sel@.len() == old(sel)@.len(),
            p == p_ship(*c, w),
            test_ok(w, blo, span),
            sel_matches(sel@, k as int, start as int, range_filter(start as int, i as int, p)),
        decreases end - i,
    {
        let m = ship_mask(c, w, blo, span, i);
        k = append_mask(m, Ghost(p), Ghost(start as int), (i - start) as u32, sel, k);
        i = i + 64;
    }
    proof {
        lemma_range_filter_len(start as int, i as int, p);
    }
    while i < end
        invariant
            cols_wf(*c),
            start <= i <= end <= c.n,
            end - start <= BLOCK_ROWS,
            end - start <= sel@.len(),
            sel@.len() == old(sel)@.len(),
            k <= i - start,
            p == p_ship(*c, w),
            test_ok(w, blo, span),
            sel_matches(sel@, k as int, start as int, range_filter(start as int, i as int, p)),
        decreases end - i,
    {
        let d = c.ship[i];
        let biased = (d as i64 + 0x8000_0000i64) as u32;
        let keep = biased.wrapping_sub(blo) < span;
        proof {
            assert(keep == (w.lo <= d && d < w.hi));
        }
        let off = (i - start) as u32;
        proof {
            lemma_sel_write(sel@, k as int, start as int, range_filter(start as int, i as int, p), off, keep);
            assert(range_filter(start as int, i + 1, p)
                == if p(i as int) { range_filter(start as int, i as int, p).push(i as int) } else { range_filter(start as int, i as int, p) });
        }
        sel[k] = off;
        k = k + if keep { 1usize } else { 0usize };
        i = i + 1;
    }
    proof {
        lemma_range_filter_len(start as int, end as int, p);
    }
    k
}

/// Listed row `r` became the entry (`slot`, `term`): it meets the assumptions, its key is `base + slot` and `term`
/// is its (positive) coefficient.
pub open spec fn entry_ok(c: Cols, w: DayWindow, base: int, ns: int, r: int, slot: usize, term: i64) -> bool {
    &&& row_fast(c, w, base, ns, r)
    &&& c.supp@[r] as int == base + slot as int
    &&& 0 <= slot < ns
    &&& 0 < term
    &&& term as int == rev(c, r)
}

/// Stage 2a of one block: the slot and the term of every listed row (offsets `sel[..k]` from `start`, the list
/// `s1`) into `slots[..k]` and `terms[..k]`. Only gathers: the slot table is not touched here, so the column loads
/// of many rows overlap (the table's address depends on a loaded key). `false` when a row breaks an assumption.
pub fn gather_listed(c: &Cols, w: DayWindow, base: i64, ns: usize, start: usize, k: usize, sel: &Vec<u32>,
    Ghost(s1): Ghost<Seq<int>>, slots: &mut Vec<usize>, terms: &mut Vec<i64>) -> (ok: bool)
    requires
        cols_wf(*c),
        sel_matches(sel@, k as int, start as int, s1),
        forall|t: int| 0 <= t < s1.len() ==> 0 <= #[trigger] s1[t] < c.n && p_ship(*c, w)(s1[t]),
        k <= old(slots)@.len(),
        k <= old(terms)@.len(),
    ensures
        final(slots)@.len() == old(slots)@.len(),
        final(terms)@.len() == old(terms)@.len(),
        ok ==> forall|t: int| 0 <= t < k ==> entry_ok(*c, w, base as int, ns as int, #[trigger] s1[t], final(slots)@[t], final(terms)@[t]),
    no_unwind
{
    let mut j: usize = 0;
    while j < k
        invariant
            cols_wf(*c),
            sel_matches(sel@, k as int, start as int, s1),
            forall|t: int| 0 <= t < s1.len() ==> 0 <= #[trigger] s1[t] < c.n && p_ship(*c, w)(s1[t]),
            k <= slots@.len(),
            k <= terms@.len(),
            slots@.len() == old(slots)@.len(),
            terms@.len() == old(terms)@.len(),
            j <= k,
            forall|t: int| 0 <= t < j ==> entry_ok(*c, w, base as int, ns as int, #[trigger] s1[t], slots@[t], terms@[t]),
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
        if t <= 0 || t > 0x7FFF_FFFF_FFFF_FFFFi128 {
            return false;
        }
        slots[j] = slot as usize;
        terms[j] = t as i64;
        proof {
            assert(row_fast(*c, w, base as int, ns as int, r));
            assert(entry_ok(*c, w, base as int, ns as int, s1[j as int], slots@[j as int], terms@[j as int]));
        }
        j = j + 1;
    }
    true
}

/// Stage 2b of one block: adds the entries `(slots[t], terms[t])` of the listed rows `s1` to the slot table. On
/// success slot `s` grew by the terms of key `base + s`.
pub fn add_entries(Ghost(c): Ghost<Cols>, Ghost(w): Ghost<DayWindow>, Ghost(base): Ghost<int>, ns: usize, k: usize,
    slots: &Vec<usize>, terms: &Vec<i64>, Ghost(s1): Ghost<Seq<int>>, table: &mut Vec<i64>, Ghost(t0): Ghost<Seq<i64>>) -> (ok: bool)
    requires
        k == s1.len(),
        k <= slots@.len(),
        k <= terms@.len(),
        forall|t: int| 0 <= t < k ==> entry_ok(c, w, base, ns as int, #[trigger] s1[t], slots@[t], terms@[t]),
        old(table)@ == t0,
        t0.len() == ns,
    ensures
        final(table)@.len() == ns,
        ok ==> forall|s: int| 0 <= s < ns ==> (#[trigger] final(table)@[s]) as int == t0[s] as int + seq_sum(s1, f_key(c, base + s)),
    no_unwind
{
    let mut j: usize = 0;
    proof {
        assert forall|s: int| 0 <= s < ns implies (#[trigger] table@[s]) as int == t0[s] as int + seq_sum(s1.take(0), f_key(c, base + s)) by {
            assert(s1.take(0) =~= Seq::<int>::empty());
        }
    }
    while j < k
        invariant
            k == s1.len(),
            k <= slots@.len(),
            k <= terms@.len(),
            forall|t: int| 0 <= t < k ==> entry_ok(c, w, base, ns as int, #[trigger] s1[t], slots@[t], terms@[t]),
            t0.len() == ns,
            table@.len() == ns,
            j <= k,
            forall|s: int| 0 <= s < ns ==> (#[trigger] table@[s]) as int == t0[s] as int + seq_sum(s1.take(j as int), f_key(c, base + s)),
        decreases k - j,
    {
        let s = slots[j];
        let t = terms[j];
        let ghost r = s1[j as int];
        proof {
            assert(entry_ok(c, w, base, ns as int, s1[j as int], slots@[j as int], terms@[j as int]));
        }
        let cur = table[s];
        if cur > 0x7FFF_FFFF_FFFF_FFFFi64 - t {
            return false;
        }
        let ghost tb = table@;
        table[s] = cur + t;
        proof {
            lemma_take_step(s1, j as int);
            assert forall|s2: int| 0 <= s2 < ns implies (#[trigger] table@[s2]) as int == t0[s2] as int + seq_sum(s1.take(j + 1), f_key(c, base + s2)) by {
                lemma_seq_sum_push(s1.take(j as int), r, f_key(c, base + s2));
                if s2 == s as int {
                    assert(f_key(c, base + s2)(r) == t);
                } else {
                    assert(f_key(c, base + s2)(r) == 0);
                    assert(table@[s2] == tb[s2]);
                }
            }
        }
        j = j + 1;
    }
    proof {
        assert(s1.take(k as int) =~= s1);
    }
    true
}

/// Stage 2 of one block: adds the term of every listed row (offsets `sel[..k]` from `start`, the list `s1`) to its
/// slot, in two passes (`gather_listed`, then `add_entries`; `slots`, `terms`: scratch of at least `k` entries).
/// On success every listed row meets the assumptions and slot `s` grew by the terms of key `base + s`.
pub fn add_listed(c: &Cols, w: DayWindow, base: i64, ns: usize, start: usize, k: usize, sel: &Vec<u32>,
    Ghost(s1): Ghost<Seq<int>>, slots: &mut Vec<usize>, terms: &mut Vec<i64>, table: &mut Vec<i64>,
    Ghost(t0): Ghost<Seq<i64>>) -> (ok: bool)
    requires
        cols_wf(*c),
        sel_matches(sel@, k as int, start as int, s1),
        forall|t: int| 0 <= t < s1.len() ==> 0 <= #[trigger] s1[t] < c.n && p_ship(*c, w)(s1[t]),
        k <= old(slots)@.len(),
        k <= old(terms)@.len(),
        old(table)@ == t0,
        t0.len() == ns,
    ensures
        final(slots)@.len() == old(slots)@.len(),
        final(terms)@.len() == old(terms)@.len(),
        final(table)@.len() == ns,
        ok ==> forall|t: int| 0 <= t < s1.len() ==> row_fast(*c, w, base as int, ns as int, #[trigger] s1[t]),
        ok ==> forall|s: int| 0 <= s < ns ==> (#[trigger] final(table)@[s]) as int == t0[s] as int + seq_sum(s1, f_key(*c, base + s)),
    no_unwind
{
    if !gather_listed(c, w, base, ns, start, k, sel, Ghost(s1), slots, terms) {
        return false;
    }
    proof {
        assert forall|t: int| 0 <= t < s1.len() implies row_fast(*c, w, base as int, ns as int, #[trigger] s1[t]) by {
            assert(entry_ok(*c, w, base as int, ns as int, s1[t], slots@[t], terms@[t]));
        }
    }
    add_entries(Ghost(*c), Ghost(w), Ghost(base as int), ns, k, slots, terms, Ghost(s1), table, Ghost(t0))
}

/// The scan of the rows `[lo, hi)` into `table` (all zero on entry; `sel`: scratch of at least `BLOCK_ROWS`
/// offsets). On success slot `s` is the SUM of key `base + s` over the range and every row meets the assumptions.
pub fn scan_range(c: &Cols, w: DayWindow, blo: u32, span: u32, base: i64, ns: usize, lo: usize, hi: usize,
    table: &mut Vec<i64>, sel: &mut Vec<u32>, slots: &mut Vec<usize>, terms: &mut Vec<i64>) -> (ok: bool)
    requires
        cols_wf(*c),
        test_ok(w, blo, span),
        lo <= hi <= c.n,
        old(table)@.len() == ns,
        forall|s: int| 0 <= s < ns ==> #[trigger] old(table)@[s] == 0i64,
        old(sel)@.len() >= BLOCK_ROWS,
        old(slots)@.len() >= BLOCK_ROWS,
        old(terms)@.len() >= BLOCK_ROWS,
    ensures
        final(table)@.len() == ns,
        final(sel)@.len() == old(sel)@.len(),
        ok ==> table_ok(final(table)@, *c, w, base as int, ns as int, lo as int, hi as int),
        ok ==> range_fast(*c, w, base as int, ns as int, lo as int, hi as int),
    no_unwind
{
    let ghost p = p_ship(*c, w);
    let ghost g = q_spec(qb_of(w));
    proof {
        assert forall|s: int| 0 <= s < ns implies (#[trigger] table@[s]) as int == gs(*c, w, base + s, lo as int, lo as int) by {
            lemma_empty(g, crows(*c), lo as int, seq![Val::Int(base + s)], 0);
        }
    }
    let mut start: usize = lo;
    while start < hi
        invariant
            cols_wf(*c),
            test_ok(w, blo, span),
            lo <= start <= hi <= c.n,
            sel@.len() == old(sel)@.len(),
            sel@.len() >= BLOCK_ROWS,
            slots@.len() >= BLOCK_ROWS,
            terms@.len() >= BLOCK_ROWS,
            p == p_ship(*c, w),
            g == q_spec(qb_of(w)),
            table_ok(table@, *c, w, base as int, ns as int, lo as int, start as int),
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
        let ghost t0 = table@;
        let ok = add_listed(c, w, base, ns, start, k, sel, Ghost(s1), slots, terms, table, Ghost(t0));
        if !ok {
            return false;
        }
        proof {
            assert forall|s: int| 0 <= s < ns implies (#[trigger] table@[s]) as int == gs(*c, w, base + s, lo as int, end as int) by {
                let f = f_key(*c, base + s);
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

} // verus!
