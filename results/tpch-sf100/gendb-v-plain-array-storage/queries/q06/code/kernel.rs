//! The scan of a row range `[lo, hi)` of the four columns (`scan_range`), in blocks of `BLOCK_ROWS` rows. Per block:
//! 1. `select_ship`: branch-free compaction of the rows whose shipdate is in range into `sel` (offsets from the
//!    block start; only the 4-byte shipdate column is read for every row);
//! 2. `select_disc`: branch-free compaction of those rows whose discount is in range into `sel2`;
//! 3. `accumulate`: for those rows, the quantity test and the exact product `price * discount` into an `Acc`.
//! Before stages 2 and 3 a cache-warming pass (`common::touch`) reads the discount (quantity) values of the listed
//! rows: on one thread this keeps many more misses in flight than the stage loops do. Its checksum picks the next
//! block length (`TOUCH_SENTINEL`), which keeps the reads in the compiled code and is correct for every value.
//! Stage 1 lists `range_filter(base, end, p_ship)`, stage 2 `range_filter(base, end, p_ship && p_disc)`
//! (`common::selection`), and stage 3 sums the quantity-guarded terms over that list, which is the normal form's
//! accumulators over the block (`lemma_range_gsum`). `ScanTask` runs one range as a `fork_join` task.
//!
//! With many workers the ranges are scanned by `scan_range_strided` instead: blocks of `STRIDED_BLOCK_ROWS` rows
//! whose stage 2 visits the stage-1 list column by column (`LANES` columns, `common::strided`), so consecutive
//! discount reads fall in different 4 KiB pages. That keeps the hardware stream prefetcher from fetching the
//! unselected discount lines between them, which saves memory bandwidth when every core is reading; stage 3 then
//! follows the same order. The sums do not depend on the visiting order (`lemma_strided_sum`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::query::*;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::common::selection::*;
use crate::agent::common::strided::*;
use crate::agent::common::touch::*;
use crate::agent::columns::*;
use crate::agent::normal::*;
use crate::agent::accum::*;

verus! {

/// Rows per block of `scan_range` (offsets in a block fit `u32`).
pub const BLOCK_ROWS: usize = 4096;

/// The cache-warming checksum value at which `scan_range` takes a one-row block instead (`common::touch`): every
/// block length is correct, and testing the checksum keeps the warming reads in the compiled code.
pub const TOUCH_SENTINEL: u64 = 0x9E37_79B9_7F4A_7C15;

/// Rows per block of `scan_range_strided`; also the scratch buffer length of a task.
pub const STRIDED_BLOCK_ROWS: usize = 8192;

/// Columns of the strided stage-2 visit.
pub const LANES: usize = 32;

/// The WHERE bounds as stored values: shipdate in `[ship_lo, ship_hi)` (days since 1970-01-01), discount coefficient
/// in `[disc_lo, disc_hi]`, quantity coefficient below `qty_lim`.
#[derive(Clone, Copy)]
pub struct Bounds {
    pub ship_lo: i32,
    pub ship_hi: i32,
    /// `ship_lo + 2^31` and the range length `ship_hi - ship_lo` (0 for an empty range): the stage-1 test is the
    /// one unsigned comparison `(d + 2^31) - ship_base < ship_span` (wrapping).
    pub ship_base: u32,
    pub ship_span: u32,
    pub disc_lo: i128,
    pub disc_hi: i128,
    pub qty_lim: i128,
}

/// The precomputed stage-1 fields agree with the shipdate range.
pub open spec fn bounds_wf(b: Bounds) -> bool {
    &&& b.ship_base as int == b.ship_lo as int + 0x8000_0000
    &&& b.ship_span as int == if b.ship_hi > b.ship_lo { b.ship_hi as int - b.ship_lo as int } else { 0 }
}

/// Bounds with the stage-1 fields computed.
pub fn make_bounds(ship_lo: i32, ship_hi: i32, disc_lo: i128, disc_hi: i128, qty_lim: i128) -> (b: Bounds)
    ensures
        bounds_wf(b),
        b.ship_lo == ship_lo && b.ship_hi == ship_hi && b.disc_lo == disc_lo && b.disc_hi == disc_hi && b.qty_lim == qty_lim,
{
    let ship_base = (ship_lo as i64 + 0x8000_0000i64) as u32;
    let ship_span: u32 = if ship_hi > ship_lo { (ship_hi as i64 - ship_lo as i64) as u32 } else { 0 };
    Bounds { ship_lo, ship_hi, ship_base, ship_span, disc_lo, disc_hi, qty_lim }
}

/// The normal form's bounds (days since 2000-01-01).
pub open spec fn qb_of(b: Bounds) -> QBounds {
    QBounds {
        plo: b.ship_lo as int - 10957,
        phi: b.ship_hi as int - 10957,
        dlo: b.disc_lo as int,
        dhi: b.disc_hi as int,
        qlim: b.qty_lim as int,
    }
}

/// The normal form under the bounds `b`.
pub open spec fn g_of(b: Bounds) -> QuerySpec {
    q6_spec(qb_of(b))
}

/// Stage 1 condition: the shipdate of row `r` is in range.
pub open spec fn p_ship(c: Cols, b: Bounds) -> spec_fn(int) -> bool {
    |r: int| b.ship_lo <= c.ship@[r] && c.ship@[r] < b.ship_hi
}

/// Stage 2 condition: the discount of row `r` is in range.
pub open spec fn p_disc(c: Cols, b: Bounds) -> spec_fn(int) -> bool {
    |r: int| b.disc_lo <= c.disc@[r] && c.disc@[r] <= b.disc_hi
}

/// Rows passing stages 1 and 2.
pub open spec fn p_ship_disc(c: Cols, b: Bounds) -> spec_fn(int) -> bool {
    and_pred(p_ship(c, b), p_disc(c, b))
}

/// The summed product of row `r` (scale 4).
pub open spec fn revenue(c: Cols, r: int) -> int {
    c.price@[r] as int * c.disc@[r] as int
}

/// Stage 3 terms: the product, its absolute value, and 1, where the quantity is below the limit (else 0).
pub open spec fn f_sum(c: Cols, b: Bounds) -> spec_fn(int) -> int {
    |r: int| if c.qty@[r] < b.qty_lim { revenue(c, r) } else { 0 }
}

pub open spec fn f_abs(c: Cols, b: Bounds) -> spec_fn(int) -> int {
    |r: int| if c.qty@[r] < b.qty_lim { abs(revenue(c, r)) } else { 0 }
}

pub open spec fn f_cnt(c: Cols, b: Bounds) -> spec_fn(int) -> int {
    |r: int| if c.qty@[r] < b.qty_lim { 1int } else { 0int }
}

/// The normal form's accumulators over the rows `[lo, hi)`: exact sum, absolute mass, count.
pub open spec fn gs(c: Cols, b: Bounds, lo: int, hi: int) -> int {
    gsum(g_of(b), crows(c).subrange(lo, hi), Seq::<Val>::empty(), 0)
}

pub open spec fn ga(c: Cols, b: Bounds, lo: int, hi: int) -> int {
    gabs(g_of(b), crows(c).subrange(lo, hi), Seq::<Val>::empty(), 0)
}

pub open spec fn gc(c: Cols, b: Bounds, lo: int, hi: int) -> int {
    gcount(g_of(b), crows(c).subrange(lo, hi), Seq::<Val>::empty()) as int
}

/// `acc` holds the SUM over the rows `[lo, hi)`.
pub open spec fn range_acc(c: Cols, b: Bounds, lo: int, hi: int, acc: Acc) -> bool {
    acc_ok(acc, gs(c, b, lo, hi), ga(c, b, lo, hi), gc(c, b, lo, hi))
}

/// The normal form's accumulators over a range are the range sums of the guarded stage-3 terms.
pub proof fn lemma_range_gsum(c: Cols, b: Bounds, lo: int, hi: int)
    requires 0 <= lo <= hi <= c.n,
    ensures
        gs(c, b, lo, hi) == range_sum(lo, hi, guard(p_ship_disc(c, b), f_sum(c, b))),
        ga(c, b, lo, hi) == range_sum(lo, hi, guard(p_ship_disc(c, b), f_abs(c, b))),
        gc(c, b, lo, hi) == range_sum(lo, hi, guard(p_ship_disc(c, b), f_cnt(c, b))),
    decreases hi - lo,
{
    let g = g_of(b);
    let e = Seq::<Val>::empty();
    if hi == lo {
        lemma_empty(g, crows(c), lo, e, 0);
    } else {
        lemma_range_gsum(c, b, lo, hi - 1);
        lemma_range_step(g, crows(c), lo, hi - 1, e, 0);
        let r = hi - 1;
        assert(crows(c)[r] == crow(c, r));
        // The normal form's condition on row `r` is the conjunction of the three stage conditions.
        assert(hit(g, crow(c, r), e) == (p_ship_disc(c, b)(r) && c.qty@[r] < b.qty_lim));
        assert((g.arg)(0, crow(c, r)) == revenue(c, r));
    }
}

/// Stage 1: the rows of `[base, end)` whose shipdate is in range, as offsets from `base` in `sel`.
pub fn select_ship(c: &Cols, b: &Bounds, base: usize, end: usize, sel: &mut Vec<u32>) -> (k: usize)
    requires
        cols_wf(*c),
        bounds_wf(*b),
        base <= end <= c.n,
        end - base <= STRIDED_BLOCK_ROWS,
        end - base <= old(sel)@.len(),
    ensures
        final(sel)@.len() == old(sel)@.len(),
        k <= end - base,
        sel_matches(final(sel)@, k as int, base as int, range_filter(base as int, end as int, p_ship(*c, *b))),
    no_unwind
{
    let ghost p = p_ship(*c, *b);
    // Shipdates biased into `u32` (`d + 2^31`): `lo <= d < hi` is the one unsigned comparison
    // `(d + 2^31) - (lo + 2^31) < hi - lo` (wrapping), as `hi - d < 2^32` for 32-bit dates.
    let biased_lo = b.ship_base;
    let span = b.ship_span;
    let mut k: usize = 0;
    let mut i: usize = base;
    if base < end {
        // Reading the block's last shipdate first lets the compiler drop the per-row bounds check.
        let _last = c.ship[end - 1];
    }
    while i < end
        invariant
            cols_wf(*c),
            base <= i <= end <= c.n,
            end - base <= STRIDED_BLOCK_ROWS,
            end - base <= sel@.len(),
            sel@.len() == old(sel)@.len(),
            k <= i - base,
            p == p_ship(*c, *b),
            biased_lo as int == b.ship_lo as int + 0x8000_0000,
            span as int == if b.ship_hi > b.ship_lo { b.ship_hi as int - b.ship_lo as int } else { 0 },
            sel_matches(sel@, k as int, base as int, range_filter(base as int, i as int, p)),
        decreases end - i,
    {
        let d = c.ship[i];
        let biased = (d as i64 + 0x8000_0000i64) as u32;
        let keep = biased.wrapping_sub(biased_lo) < span;
        proof {
            assert(keep == (b.ship_lo <= d && d < b.ship_hi));
        }
        let off = (i - base) as u32;
        proof {
            lemma_sel_write(sel@, k as int, base as int, range_filter(base as int, i as int, p), off, keep);
            assert(range_filter(base as int, i + 1, p)
                == if p(i as int) { range_filter(base as int, i as int, p).push(i as int) } else { range_filter(base as int, i as int, p) });
        }
        sel[k] = off;
        k = k + if keep { 1usize } else { 0usize };
        i = i + 1;
    }
    k
}

/// Stage 2: the rows of the list `s1` (offsets in `sel`) whose discount is in range, as offsets in `sel2`.
pub fn select_disc(c: &Cols, b: &Bounds, base: usize, k: usize, sel: &Vec<u32>, sel2: &mut Vec<u32>,
    Ghost(s1): Ghost<Seq<int>>) -> (k2: usize)
    requires
        cols_wf(*c),
        sel_matches(sel@, k as int, base as int, s1),
        forall|t: int| 0 <= t < s1.len() ==> 0 <= #[trigger] s1[t] < c.n,
        k <= old(sel2)@.len(),
    ensures
        final(sel2)@.len() == old(sel2)@.len(),
        sel_matches(final(sel2)@, k2 as int, base as int, seq_filter(s1, p_disc(*c, *b))),
    no_unwind
{
    let ghost q = p_disc(*c, *b);
    let mut k2: usize = 0;
    let mut j: usize = 0;
    while j < k
        invariant
            cols_wf(*c),
            sel_matches(sel@, k as int, base as int, s1),
            forall|t: int| 0 <= t < s1.len() ==> 0 <= #[trigger] s1[t] < c.n,
            k <= sel2@.len(),
            sel2@.len() == old(sel2)@.len(),
            j <= k,
            k2 <= j,
            q == p_disc(*c, *b),
            sel_matches(sel2@, k2 as int, base as int, seq_filter(s1.take(j as int), q)),
        decreases k - j,
    {
        let off = sel[j];
        proof {
            assert(base + off as int == s1[j as int]);
        }
        let r = base + off as usize;
        let x = c.disc[r];
        // Both comparisons as 0/1 values (no branch on the data).
        let above: usize = if x >= b.disc_lo { 1 } else { 0 };
        let below: usize = if x <= b.disc_hi { 1 } else { 0 };
        let keep = above + below == 2;
        proof {
            lemma_take_step(s1, j as int);
            lemma_seq_filter_push(s1.take(j as int), s1[j as int], q);
            lemma_sel_write(sel2@, k2 as int, base as int, seq_filter(s1.take(j as int), q), off, keep);
        }
        sel2[k2] = off;
        k2 = k2 + (above + below) / 2;
        j = j + 1;
    }
    proof {
        assert(s1.take(k as int) =~= s1);
    }
    k2
}

/// Stage 3: adds the quantity-guarded products of the rows of the list `s` (offsets in `sel2`) to `acc`.
pub fn accumulate(c: &Cols, b: &Bounds, base: usize, k2: usize, sel2: &Vec<u32>, Ghost(s): Ghost<Seq<int>>,
    acc: &mut Acc, Ghost(ts): Ghost<int>, Ghost(ta): Ghost<int>, Ghost(tc): Ghost<int>)
    requires
        cols_wf(*c),
        sel_matches(sel2@, k2 as int, base as int, s),
        forall|t: int| 0 <= t < s.len() ==> 0 <= #[trigger] s[t] < c.n,
        acc_ok(*old(acc), ts, ta, tc),
    ensures
        acc_ok(*final(acc), ts + seq_sum(s, f_sum(*c, *b)), ta + seq_sum(s, f_abs(*c, *b)), tc + seq_sum(s, f_cnt(*c, *b))),
    no_unwind
{
    let ghost (fs, fa, fc) = (f_sum(*c, *b), f_abs(*c, *b), f_cnt(*c, *b));
    let mut t: usize = 0;
    while t < k2
        invariant
            cols_wf(*c),
            sel_matches(sel2@, k2 as int, base as int, s),
            forall|u: int| 0 <= u < s.len() ==> 0 <= #[trigger] s[u] < c.n,
            t <= k2,
            fs == f_sum(*c, *b),
            fa == f_abs(*c, *b),
            fc == f_cnt(*c, *b),
            acc_ok(*acc, ts + seq_sum(s.take(t as int), fs), ta + seq_sum(s.take(t as int), fa), tc + seq_sum(s.take(t as int), fc)),
        decreases k2 - t,
    {
        let off = sel2[t];
        proof {
            assert(base + off as int == s[t as int]);
            lemma_take_step(s, t as int);
            lemma_seq_sum_push(s.take(t as int), s[t as int], fs);
            lemma_seq_sum_push(s.take(t as int), s[t as int], fa);
            lemma_seq_sum_push(s.take(t as int), s[t as int], fc);
        }
        let r = base + off as usize;
        if c.qty[r] < b.qty_lim {
            let pr = c.price[r];
            let x = c.disc[r];
            proof {
                // Both factors are numeric(15,2) coefficients: the product is below 10^30 in absolute value.
                assert(coeff_ok(pr) && coeff_ok(x));
                assert(-1_000_000_000_000_000_000_000_000_000_000 < (pr as int) * (x as int) < 1_000_000_000_000_000_000_000_000_000_000)
                    by (nonlinear_arith)
                    requires -1_000_000_000_000_000 < (pr as int) < 1_000_000_000_000_000,
                        -1_000_000_000_000_000 < (x as int) < 1_000_000_000_000_000;
            }
            let p = pr * x;
            acc_add(acc, p, Ghost(ts + seq_sum(s.take(t as int), fs)), Ghost(ta + seq_sum(s.take(t as int), fa)),
                Ghost(tc + seq_sum(s.take(t as int), fc)));
        }
        t = t + 1;
    }
    proof {
        assert(s.take(k2 as int) =~= s);
    }
}

/// The SUM over the rows `[lo, hi)`, in blocks (`sel`, `sel2`: scratch buffers of at least `BLOCK_ROWS` offsets).
pub fn scan_range(c: &Cols, b: &Bounds, lo: usize, hi: usize, sel: &mut Vec<u32>, sel2: &mut Vec<u32>) -> (acc: Acc)
    requires
        cols_wf(*c),
        bounds_wf(*b),
        lo <= hi <= c.n,
        old(sel)@.len() >= BLOCK_ROWS,
        old(sel2)@.len() >= BLOCK_ROWS,
    ensures range_acc(*c, *b, lo as int, hi as int, acc),
    no_unwind
{
    let ghost (p1, p2) = (p_ship(*c, *b), p_disc(*c, *b));
    let ghost g = g_of(*b);
    let ghost e = Seq::<Val>::empty();
    let mut acc = acc_new();
    proof {
        lemma_empty(g, crows(*c), lo as int, e, 0);
    }
    let mut base: usize = lo;
    // Cache-warming checksum of the reads so far (`common::touch`).
    let mut tt: u64 = 0;
    while base < hi
        invariant
            cols_wf(*c),
            bounds_wf(*b),
            lo <= base <= hi <= c.n,
            sel@.len() >= BLOCK_ROWS,
            sel2@.len() >= BLOCK_ROWS,
            p1 == p_ship(*c, *b),
            p2 == p_disc(*c, *b),
            g == g_of(*b),
            e == Seq::<Val>::empty(),
            range_acc(*c, *b, lo as int, base as int, acc),
        decreases hi - base,
    {
        let len = if tt == TOUCH_SENTINEL { 1 } else { BLOCK_ROWS };
        let end = if hi - base > len { base + len } else { hi };
        let k = select_ship(c, b, base, end, sel);
        let ghost s1 = range_filter(base as int, end as int, p1);
        proof {
            lemma_range_filter_bounds(base as int, end as int, p1);
            assert forall|t: int| 0 <= t < s1.len() implies 0 <= #[trigger] s1[t] < c.n by {}
            assert forall|j: int| 0 <= j < k implies (base + (#[trigger] sel@[j]) as int) < c.n by {
                assert(base + sel@[j] as int == s1[j]);
            }
        }
        // Bring the discount lines of the stage-1 rows in before stage 2 compares them.
        tt = tt.wrapping_add(touch_i128(c.disc, c.n, base, k, sel));
        let k2 = select_disc(c, b, base, k, sel, sel2, Ghost(s1));
        let ghost s12 = range_filter(base as int, end as int, p_ship_disc(*c, *b));
        proof {
            lemma_filter_range_filter(base as int, end as int, p1, p2);
            lemma_range_filter_bounds(base as int, end as int, p_ship_disc(*c, *b));
            assert forall|t: int| 0 <= t < s12.len() implies 0 <= #[trigger] s12[t] < c.n by {}
            assert forall|j: int| 0 <= j < k2 implies (base + (#[trigger] sel2@[j]) as int) < c.n by {
                assert(base + sel2@[j] as int == s12[j]);
            }
        }
        // And the quantity lines of the stage-2 rows before stage 3.
        tt = tt.wrapping_add(touch_i128(c.qty, c.n, base, k2, sel2));
        let ghost (ts, ta, tc) = (gs(*c, *b, lo as int, base as int), ga(*c, *b, lo as int, base as int), gc(*c, *b, lo as int, base as int));
        accumulate(c, b, base, k2, sel2, Ghost(s12), &mut acc, Ghost(ts), Ghost(ta), Ghost(tc));
        proof {
            lemma_sum_range_filter(base as int, end as int, p_ship_disc(*c, *b), f_sum(*c, *b));
            lemma_sum_range_filter(base as int, end as int, p_ship_disc(*c, *b), f_abs(*c, *b));
            lemma_sum_range_filter(base as int, end as int, p_ship_disc(*c, *b), f_cnt(*c, *b));
            lemma_range_gsum(*c, *b, base as int, end as int);
            lemma_split(g, crows(*c), lo as int, base as int, end as int, e, 0);
        }
        base = end;
    }
    acc
}

/// Stage 2 in strided order: the rows of the list `s1` (offsets in `sel`) whose discount is in range, visited
/// column by column (`visit(s1, LANES, LANES)`), as offsets in `sel2`.
pub fn select_disc_strided(c: &Cols, b: &Bounds, base: usize, k: usize, sel: &Vec<u32>, sel2: &mut Vec<u32>,
    Ghost(s1): Ghost<Seq<int>>) -> (k2: usize)
    requires
        cols_wf(*c),
        sel_matches(sel@, k as int, base as int, s1),
        forall|t: int| 0 <= t < s1.len() ==> 0 <= #[trigger] s1[t] < c.n,
        k <= old(sel2)@.len(),
        k <= STRIDED_BLOCK_ROWS,
    ensures
        final(sel2)@.len() == old(sel2)@.len(),
        sel_matches(final(sel2)@, k2 as int, base as int, seq_filter(visit(s1, LANES as int, LANES as int), p_disc(*c, *b))),
        forall|t: int| 0 <= t < k2 ==> base + final(sel2)@[t] < c.n,
    no_unwind
{
    let ghost q = p_disc(*c, *b);
    let ghost l = LANES as int;
    proof {
        lemma_visit_len(s1, l);
    }
    let mut k2: usize = 0;
    let mut lane: usize = 0;
    while lane < LANES
        invariant
            cols_wf(*c),
            sel_matches(sel@, k as int, base as int, s1),
            forall|t: int| 0 <= t < s1.len() ==> 0 <= #[trigger] s1[t] < c.n,
            k <= sel2@.len(),
            sel2@.len() == old(sel2)@.len(),
            k <= STRIDED_BLOCK_ROWS,
            lane <= LANES,
            q == p_disc(*c, *b),
            l == LANES as int,
            visit(s1, l, l).len() == k,
            sel_matches(sel2@, k2 as int, base as int, seq_filter(visit(s1, l, lane as int), q)),
            forall|t: int| 0 <= t < k2 ==> base + sel2@[t] < c.n,
        decreases LANES - lane,
    {
        // `done`: the elements of column `lane` visited so far; the rest of the column is `col(s1, l, j)`.
        let ghost mut done: Seq<int> = Seq::empty();
        let ghost v = visit(s1, l, lane as int);
        proof {
            assert(col(s1, l, lane as int) =~= done + col(s1, l, lane as int));
            assert(v + done =~= v);
            lemma_visit_mono(s1, l, lane + 1, l);
        }
        let mut j: usize = lane;
        while j < k
            invariant
                cols_wf(*c),
                sel_matches(sel@, k as int, base as int, s1),
                forall|t: int| 0 <= t < s1.len() ==> 0 <= #[trigger] s1[t] < c.n,
                k <= sel2@.len(),
                sel2@.len() == old(sel2)@.len(),
                k <= STRIDED_BLOCK_ROWS,
                lane < LANES,
                lane <= j,
                q == p_disc(*c, *b),
                l == LANES as int,
                v == visit(s1, l, lane as int),
                visit(s1, l, lane + 1).len() <= k,
                col(s1, l, lane as int) == done + col(s1, l, j as int),
                sel_matches(sel2@, k2 as int, base as int, seq_filter(v + done, q)),
                forall|t: int| 0 <= t < k2 ==> base + sel2@[t] < c.n,
            decreases if j < k { k - j } else { 0 },
        {
            let off = sel[j];
            let ghost x = s1[j as int];
            proof {
                assert(base + off as int == x);
                // The column from `j` is `x` followed by the column from `j + l`.
                assert(col(s1, l, j as int) == seq![x] + col(s1, l, j + l));
                assert(visit(s1, l, lane + 1) == v + col(s1, l, lane as int));
                assert((v + done).len() + 1 <= visit(s1, l, lane + 1).len());
                lemma_filter_len(v + done, q);
            }
            let r = base + off as usize;
            let xd = c.disc[r];
            let above: usize = if xd >= b.disc_lo { 1 } else { 0 };
            let below: usize = if xd <= b.disc_hi { 1 } else { 0 };
            let keep = above + below == 2;
            proof {
                lemma_seq_filter_push(v + done, x, q);
                assert((v + done).push(x) =~= v + done.push(x));
                lemma_sel_write(sel2@, k2 as int, base as int, seq_filter(v + done, q), off, keep);
            }
            sel2[k2] = off;
            k2 = k2 + (above + below) / 2;
            proof {
                assert(done + (seq![x] + col(s1, l, j + l)) =~= done.push(x) + col(s1, l, j + l));
                done = done.push(x);
            }
            j = j + LANES;
        }
        proof {
            assert(col(s1, l, j as int) =~= Seq::<int>::empty());
            assert(done =~= col(s1, l, lane as int));
            assert(visit(s1, l, lane + 1) == v + col(s1, l, lane as int));
        }
        lane = lane + 1;
    }
    k2
}

/// The strided stage 2 and 3 sum the same terms: a sum over the strided discount filter of the stage-1 list is the
/// range sum of the terms guarded by both conditions.
pub proof fn lemma_strided_sum(c: Cols, b: Bounds, base: int, end: int, f: spec_fn(int) -> int)
    ensures
        seq_sum(seq_filter(visit(range_filter(base, end, p_ship(c, b)), LANES as int, LANES as int), p_disc(c, b)), f)
            == range_sum(base, end, guard(p_ship_disc(c, b), f)),
{
    let s1 = range_filter(base, end, p_ship(c, b));
    let q = p_disc(c, b);
    let v = visit(s1, LANES as int, LANES as int);
    lemma_filter_sum(v, q, f);
    lemma_visit_sum(s1, LANES as int, guard(q, f));
    lemma_filter_sum(s1, q, f);
    lemma_filter_range_filter(base, end, p_ship(c, b), q);
    lemma_sum_range_filter(base, end, p_ship_disc(c, b), f);
}

/// The SUM over the rows `[lo, hi)` with the strided stage 2 (`sel`, `sel2`: scratch buffers of at least
/// `STRIDED_BLOCK_ROWS` offsets).
pub fn scan_range_strided(c: &Cols, b: &Bounds, lo: usize, hi: usize, sel: &mut Vec<u32>, sel2: &mut Vec<u32>) -> (acc: Acc)
    requires
        cols_wf(*c),
        bounds_wf(*b),
        lo <= hi <= c.n,
        old(sel)@.len() >= STRIDED_BLOCK_ROWS,
        old(sel2)@.len() >= STRIDED_BLOCK_ROWS,
    ensures range_acc(*c, *b, lo as int, hi as int, acc),
    no_unwind
{
    let ghost p1 = p_ship(*c, *b);
    let ghost g = g_of(*b);
    let ghost e = Seq::<Val>::empty();
    let mut acc = acc_new();
    proof {
        lemma_empty(g, crows(*c), lo as int, e, 0);
    }
    let mut base: usize = lo;
    while base < hi
        invariant
            cols_wf(*c),
            bounds_wf(*b),
            lo <= base <= hi <= c.n,
            sel@.len() >= STRIDED_BLOCK_ROWS,
            sel2@.len() >= STRIDED_BLOCK_ROWS,
            p1 == p_ship(*c, *b),
            g == g_of(*b),
            e == Seq::<Val>::empty(),
            range_acc(*c, *b, lo as int, base as int, acc),
        decreases hi - base,
    {
        let end = if hi - base > STRIDED_BLOCK_ROWS { base + STRIDED_BLOCK_ROWS } else { hi };
        let k = select_ship(c, b, base, end, sel);
        let ghost s1 = range_filter(base as int, end as int, p1);
        proof {
            lemma_range_filter_bounds(base as int, end as int, p1);
            assert forall|t: int| 0 <= t < s1.len() implies 0 <= #[trigger] s1[t] < c.n by {}
        }
        let k2 = select_disc_strided(c, b, base, k, sel, sel2, Ghost(s1));
        let ghost s12 = seq_filter(visit(s1, LANES as int, LANES as int), p_disc(*c, *b));
        proof {
            assert forall|t: int| 0 <= t < s12.len() implies 0 <= #[trigger] s12[t] < c.n by {
                assert(base + sel2@[t] == s12[t]);
            }
        }
        let ghost (ts, ta, tc) = (gs(*c, *b, lo as int, base as int), ga(*c, *b, lo as int, base as int), gc(*c, *b, lo as int, base as int));
        accumulate(c, b, base, k2, sel2, Ghost(s12), &mut acc, Ghost(ts), Ghost(ta), Ghost(tc));
        proof {
            lemma_strided_sum(*c, *b, base as int, end as int, f_sum(*c, *b));
            lemma_strided_sum(*c, *b, base as int, end as int, f_abs(*c, *b));
            lemma_strided_sum(*c, *b, base as int, end as int, f_cnt(*c, *b));
            lemma_range_gsum(*c, *b, base as int, end as int);
            lemma_split(g, crows(*c), lo as int, base as int, end as int, e, 0);
        }
        base = end;
    }
    acc
}

/// The scan of rows `[lo, hi)` as a `fork_join` task, with its scratch buffers.
pub struct ScanTask {
    pub c: Cols,
    pub b: Bounds,
    pub lo: usize,
    pub hi: usize,
    pub sel: Vec<u32>,
    pub sel2: Vec<u32>,
    /// Scan with `scan_range_strided` (else `scan_range`).
    pub strided: bool,
}

impl WorkerTask for ScanTask {
    type Output = Acc;

    open spec fn pre(&self) -> bool {
        &&& cols_wf(self.c)
        &&& bounds_wf(self.b)
        &&& self.lo <= self.hi <= self.c.n
        &&& self.sel@.len() >= STRIDED_BLOCK_ROWS
        &&& self.sel2@.len() >= STRIDED_BLOCK_ROWS
    }

    open spec fn post(&self, out: Acc) -> bool {
        range_acc(self.c, self.b, self.lo as int, self.hi as int, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: Acc) {
        let ScanTask { c, b, lo, hi, sel, sel2, strided } = self;
        let mut sel = sel;
        let mut sel2 = sel2;
        if strided {
            scan_range_strided(&c, &b, lo, hi, &mut sel, &mut sel2)
        } else {
            scan_range(&c, &b, lo, hi, &mut sel, &mut sel2)
        }
    }
}

} // verus!
