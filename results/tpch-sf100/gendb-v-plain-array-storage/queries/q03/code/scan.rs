//! The lineitem scan of one task: rows `lo..hi` grouped by their order, as runs (`agent::runs`).
//!
//! Every row is mapped to the orders row with its `l_orderkey`. The task starts from the orders row of its first
//! row (`find_key`) and then assumes the next key change starts the next orders row, which holds when both tables
//! are in key order (as dbgen writes them); every such step is *checked* (`o_orderkey` of the assumed row equals
//! the lineitem's key), so with the primary key of `orders` the mapping is exact. A failed check, a value beyond
//! `VMAX` or running out of orders rows ends the task with `ok == false`, and the query then takes the general
//! path (`agent::fallback`).
//!
//! Blocks of 64 rows (`scan_block`): bit masks of key changes and of `l_shipdate > $2` (vectorizable), the walk over
//! the key changes (`block_orders`), the per-row order flag `o_orderdate < $2` by prefix XOR, and only the rows
//! with both flags (`cand`, about 2% of rows) are looked at one by one: customer segment (bitmap, cached per order)
//! and the value `l_extendedprice * (100 - l_discount)`. The rows of the last partial block go one by one
//! (`scan_row`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::runs::*;
use crate::agent::scan_parts::*;
use crate::agent::common::bits::*;
use crate::agent::common::tz::{tz64, tz_table_array};
use crate::agent::common::popc::{pc_ok, pc_table, popc_below};
use crate::agent::topk::*;

verus! {

/// The stored columns a scan reads (whole columns; `&'static` slices of the stored parts).
#[derive(Clone, Copy)]
pub struct ScanCols {
    pub lkey: &'static [i64],
    pub lship: &'static [i32],
    pub lprice: &'static [i128],
    pub ldisc: &'static [i128],
    pub okey: &'static [i64],
    pub ocust: &'static [i64],
    pub odate: &'static [i32],
    pub nl: usize,
    pub no: usize,
    pub nc: usize,
    pub cbase: i64,
    pub dl: i32,
}

/// The slices are the stored columns of `sv`, and the scan facts hold.
pub open spec fn scan_cols_ok(c: ScanCols, sv: StoresView, seg: Seq<u8>, dl: int) -> bool {
    &&& scan_facts(sv, seg, dl)
    &&& c.lkey@ == lk(sv) && c.lship@ == ls(sv) && c.lprice@ == lp(sv) && c.ldisc@ == ld(sv)
    &&& c.okey@ == ok(sv) && c.ocust@ == oc(sv) && c.odate@ == od(sv)
    &&& c.nl as int == n_l(sv) && c.no as int == n_o(sv) && c.nc as int == n_c(sv)
    &&& c.dl as int == dl
}

/// The customer check of the last order looked at.
pub struct CustCache {
    pub j: usize,
    pub ok: bool,
}

pub open spec fn cache_ok(k: CustCache, sv: StoresView, seg: Seq<u8>) -> bool {
    k.j as int != usize::MAX ==> (k.j as int) < n_o(sv) && k.ok == cust_ok(sv, seg, oc(sv)[k.j as int] as int)
}

/// `cust_ok` of order `m`'s customer, through the cache; with `seqc`, its customer key is read from the block's copy
/// `ocb` (orders `j..`) instead of `o_custkey`.
fn cached_cust(c: ScanCols, bits: &Vec<u64>, cache: &mut CustCache, m: usize, seqc: bool, ocb: &Vec<i64>, j: usize,
    Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>, Ghost(dl): Ghost<int>) -> (b: bool)
    requires
        scan_cols_ok(c, sv, seg, dl), cust_bits_ok(bits@, sv, seg, c.cbase as int, c.nc as int),
        cache_ok(*old(cache), sv, seg), m < c.no, (m as int) < usize::MAX,
        seqc ==> j <= m && m - j < ocb@.len() && ocb@[m - j] == oc(sv)[m as int],
    ensures b == cust_ok(sv, seg, oc(sv)[m as int] as int), cache_ok(*final(cache), sv, seg),
    no_unwind
{
    if seqc {
        // the key is in the block's copy: no cache (one fewer unpredictable branch)
        return cust_bit(bits, c.cbase, c.nc, ocb[m - j], Ghost(sv), Ghost(seg));
    }
    if cache.j != m {
        cache.j = m;
        cache.ok = cust_bit(bits, c.cbase, c.nc, c.ocust[m], Ghost(sv), Ghost(seg));
    }
    cache.ok
}

/// `l_extendedprice * (100 - l_discount)` of row `i`, if within `VMAX`.
fn row_value(c: ScanCols, i: usize, Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>, Ghost(dl): Ghost<int>) -> (r: Option<i128>)
    requires scan_cols_ok(c, sv, seg, dl), i < c.nl,
    ensures r matches Some(v) ==> v as int == line_value(sv, i as int) && -VMAX <= v <= VMAX,
    no_unwind
{
    let p = c.lprice[i];
    let d = c.ldisc[i];
    proof {
        assert(num15(lp(sv)[i as int]) && num15(ld(sv)[i as int]));
        let (pi, di) = (p as int, 100 - d as int);
        assert(-1_000_000_000_000_000 < pi < 1_000_000_000_000_000);
        assert(-1_000_000_000_000_100 < di < 1_000_000_000_000_100);
        assert(-1_000_000_000_000_100_000_000_000_000_000 < pi * di < 1_000_000_000_000_100_000_000_000_000_000) by (nonlinear_arith)
            requires -1_000_000_000_000_000 < pi < 1_000_000_000_000_000, -1_000_000_000_000_100 < di < 1_000_000_000_000_100;
    }
    let v = p * (100 - d);
    if -VMAX <= v && v <= VMAX { Some(v) } else { None }
}

/// The state of a scan between rows: the runs over `lo..q`, the order `j` of row `q - 1` (or of row `lo` before
/// any row), whose key is `prev`.
pub open spec fn scan_state(c: ScanCols, runs: Runs, sv: StoresView, seg: Seq<u8>, dl: int, lo: int, q: int, j: int, prev: i64,
    cap: int) -> bool
{
    &&& runs_inv(runs, sv, seg, dl, lo, q, j, cap)
    &&& 0 <= j < n_o(sv)
    &&& ok(sv)[j] == prev
}

/// One row `q` (the tail of a task): map it, account it.
fn scan_row(c: ScanCols, bits: &Vec<u64>, ocb: &Vec<i64>, runs: &mut Runs, cache: &mut CustCache, q: usize, j: usize, prev: i64,
    Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>, Ghost(dl): Ghost<int>, Ghost(lo): Ghost<int>, Ghost(cap): Ghost<int>)
    -> (r: Option<usize>)
    requires
        scan_cols_ok(c, sv, seg, dl), cust_bits_ok(bits@, sv, seg, c.cbase as int, c.nc as int),
        scan_state(c, *old(runs), sv, seg, dl, lo, q as int, j as int, prev, cap),
        cache_ok(*old(cache), sv, seg),
        0 <= lo, q < c.nl, q + 1 - lo <= cap,
    ensures
        r matches Some(j2) ==> j <= j2 && scan_state(c, *final(runs), sv, seg, dl, lo, q + 1, j2 as int, c.lkey@[q as int], cap)
            && cache_ok(*final(cache), sv, seg),
    no_unwind
{
    let k = c.lkey[q];
    let mut m = j;
    if k != prev {
        if j + 1 < c.no && c.okey[j + 1] == k {
            m = j + 1;
        } else {
            return None;
        }
    }
    assert(maps_to(sv, q as int, m as int));
    if c.odate[m] < c.dl && c.lship[q] > c.dl {
        let cok = cached_cust(c, bits, cache, m, false, ocb, 0, Ghost(sv), Ghost(seg), Ghost(dl));
        if cok {
            let v = match row_value(c, q, Ghost(sv), Ghost(seg), Ghost(dl)) {
                Some(v) => v,
                None => { return None; }
            };
            assert(line_hit(sv, seg, dl, q as int, m as int));
            runs_hit(runs, m, v, Ghost(sv), Ghost(seg), Ghost(dl), Ghost(lo), Ghost(q as int), Ghost(j as int), Ghost(cap));
            return Some(m);
        }
    }
    proof {
        assert(!line_hit(sv, seg, dl, q as int, m as int));
        let mf = |i: int| m as int;
        lemma_runs_misses(*old(runs), sv, seg, dl, lo, q as int, q as int + 1, j as int, m as int, cap, mf);
    }
    Some(m)
}

/// Facts about one block of rows `b..b+64` whose preceding row maps to order `j`: row `b + u` maps to order
/// `blk_ord(j, cm, u)`, non-decreasing in `u`, and `cand` marks the rows whose order is dated before `$2` and that
/// ship after it.
pub open spec fn block_facts(sv: StoresView, dl: int, b: int, j: int, cm: u64, cand: u64) -> bool {
    &&& forall|u: u64| u < 64 ==> #[trigger] maps_to(sv, b + u, blk_ord(j, cm, u as int))
    &&& forall|u: u64| u < 64 ==> #[trigger] bit(cand, u)
            == ((od(sv)[blk_ord(j, cm, u as int)] as int) < dl && (ls(sv)[b + u] as int) > dl)
    &&& forall|u: int, w: int| 0 <= u <= w < 64 ==> j <= #[trigger] blk_ord(j, cm, u) <= #[trigger] blk_ord(j, cm, w) <= j + 64
}

/// Rows of the block that are not candidates hit nothing.
pub proof fn lemma_block_misses(sv: StoresView, seg: Seq<u8>, dl: int, b: int, j: int, cm: u64, cand: u64, u: int)
    requires block_facts(sv, dl, b, j, cm, cand), 0 <= u < 64, !bit(cand, u as u64),
    ensures
        maps_to(sv, b + u, blk_ord(j, cm, u)),
        !line_hit(sv, seg, dl, b + u, blk_ord(j, cm, u)),
{
    assert(maps_to(sv, b + (u as u64), blk_ord(j, cm, (u as u64) as int)));
}

/// The orders of a block are monotone.
proof fn lemma_blk_ord_monotone(j: int, cm: u64)
    ensures forall|u: int, w: int| 0 <= u <= w < 64 ==> j <= #[trigger] blk_ord(j, cm, u) <= #[trigger] blk_ord(j, cm, w) <= j + 64,
{
    assert forall|u: int, w: int| 0 <= u <= w < 64 implies j <= #[trigger] blk_ord(j, cm, u) <= #[trigger] blk_ord(j, cm, w) <= j + 64 by {
        lemma_count_bounds(cm, u + 1, w + 1);
        lemma_count_bounds(cm, w + 1, 64);
        lemma_count_nonneg(cm, u + 1);
        lemma_count_nonneg(cm, 64);
    }
}

/// Masks, orders and candidates of the block at `b`; `None` when an assumed order has another key.
fn block_setup(c: ScanCols, table: &[u8; 64], b: usize, j: usize, prev: i64, Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>,
    Ghost(dl): Ghost<int>) -> (r: Option<(u64, u64, usize)>)
    requires
        scan_cols_ok(c, sv, seg, dl), table@.len() == 64,
        b + 64 <= c.nl, j + 64 < c.no, ok(sv)[j as int] == prev,
    ensures
        r matches Some((cm, cand, jj)) ==> {
            &&& block_facts(sv, dl, b as int, j as int, cm, cand)
            &&& jj == blk_ord(j as int, cm, 63)
            &&& (jj as int) < n_o(sv)
            &&& ok(sv)[jj as int] == lk(sv)[b + 63]
        },
    no_unwind
{
    let (_, kt) = c.lkey.split_at(b);
    let (kb, _) = kt.split_at(64);
    let (_, st) = c.lship.split_at(b);
    let (sb, _) = st.split_at(64);
    assert(kb@ =~= lk(sv).subrange(b as int, b + 64));
    assert(sb@ =~= ls(sv).subrange(b as int, b + 64));
    let (cm, sm) = block_masks(kb, sb, prev, c.dl);
    let (tog, jj) = match block_orders(c.okey, c.odate, kb, cm, j, c.dl, table, Ghost(c.no as int)) {
        Some(x) => x,
        None => { return None; }
    };
    let d0: u64 = if c.odate[j] < c.dl { 1 } else { 0 };
    let mut x = tog;
    x = x ^ (x << 1u64);
    x = x ^ (x << 2u64);
    x = x ^ (x << 4u64);
    x = x ^ (x << 8u64);
    x = x ^ (x << 16u64);
    x = x ^ (x << 32u64);
    let om = x ^ 0u64.wrapping_sub(d0);
    let cand = om & sm;
    proof {
        assert(x == prefix_xor(tog));
        assert(om == prefix_xor(tog) ^ 0u64.wrapping_sub(d0));
        lemma_order_flags(od(sv), c.dl, cm, tog, j as int, d0);
        lemma_blk_ord_monotone(j as int, cm);
        assert forall|u: u64| u < 64 implies #[trigger] bit(cand, u)
            == ((od(sv)[blk_ord(j as int, cm, u as int)] as int) < dl && (ls(sv)[b + u] as int) > dl) by {
            lemma_bit_and(om, sm, u);
            lemma_order_flag_at(od(sv), c.dl, cm, tog, j as int, d0, u);
            assert(bit(om, u) == (od(sv)[blk_ord(j as int, cm, u as int)] < c.dl));
            assert(bit(sm, u) == (sb@[u as int] > c.dl));
            assert(sb@[u as int] == ls(sv)[b + u]);
        }
        assert forall|u: u64| u < 64 implies #[trigger] maps_to(sv, b + u, blk_ord(j as int, cm, u as int)) by {
            lemma_block_keys(ok(sv), kb@, prev, cm, j as int, u);
            assert(kb@[u as int] == lk(sv)[b + u]);
        }
        lemma_count_bounds(cm, 0, 64);
        lemma_block_keys(ok(sv), kb@, prev, cm, j as int, 63);
    }
    Some((cm, cand, jj))
}

/// One block `b..b+64`: candidates looked at one by one (each one's order by a bit count), all other rows hit nothing.
fn scan_block(c: ScanCols, bits: &Vec<u64>, table: &[u8; 64], pct: &[u8; 256], seqc: bool, ocb: &mut Vec<i64>, runs: &mut Runs,
    cache: &mut CustCache, b: usize, j: usize, prev: i64, Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>, Ghost(dl): Ghost<int>,
    Ghost(lo): Ghost<int>, Ghost(cap): Ghost<int>) -> (r: Option<usize>)
    requires
        scan_cols_ok(c, sv, seg, dl), cust_bits_ok(bits@, sv, seg, c.cbase as int, c.nc as int), table@.len() == 64, pc_ok(pct@),
        old(ocb)@.len() == 65,
        scan_state(c, *old(runs), sv, seg, dl, lo, b as int, j as int, prev, cap),
        cache_ok(*old(cache), sv, seg),
        0 <= lo <= b, b + 64 <= c.nl, b + 64 - lo <= cap, j + 64 < c.no,
    ensures
        r matches Some(j2) ==> j <= j2 && scan_state(c, *final(runs), sv, seg, dl, lo, b + 64, j2 as int, c.lkey@[b + 63], cap)
            && cache_ok(*final(cache), sv, seg),
        final(ocb)@.len() == 65,
    no_unwind
{
    let (cm, cand, jj) = match block_setup(c, table, b, j, prev, Ghost(sv), Ghost(seg), Ghost(dl)) {
        Some(x) => x,
        None => { return None; }
    };
    let ghost mf = |i: int| blk_ord(j as int, cm, i - b);
    // with `seqc`, the customer keys of the block's orders are read in order (one stream instead of random reads)
    if seqc && cand != 0 {
        let nk = jj - j;
        let mut k: usize = 0;
        while k <= nk
            invariant
                scan_cols_ok(c, sv, seg, dl), nk == jj - j, nk <= 64, (jj as int) < n_o(sv), k <= nk + 1,
                ocb@.len() == 65,
                forall|q: int| 0 <= q < k ==> #[trigger] ocb@[q] == oc(sv)[j + q],
            decreases nk + 1 - k,
        {
            ocb[k] = c.ocust[j + k];
            k = k + 1;
        }
    }
    let mut y = cand;
    let ghost mut py: int = 0;
    let ghost mut jn: int = j as int;
    proof {
        lemma_count_nonneg(cm, 0);
    }
    while y != 0
        invariant
            scan_cols_ok(c, sv, seg, dl), cust_bits_ok(bits@, sv, seg, c.cbase as int, c.nc as int), table@.len() == 64,
            pc_ok(pct@),
            ocb@.len() == 65,
            seqc && y != 0 ==> forall|q: int| 0 <= q <= jj - j ==> #[trigger] ocb@[q] == oc(sv)[j + q],
            jj == blk_ord(j as int, cm, 63),
            cache_ok(*cache, sv, seg),
            block_facts(sv, dl, b as int, j as int, cm, cand),
            0 <= lo <= b, b + 64 <= c.nl, b + 64 - lo <= cap, j + 64 < c.no,
            0 <= py <= 64,
            forall|u: u64| u < 64 ==> #[trigger] bit(y, u) == (bit(cand, u) && u >= py),
            jn == if py == 0 { j as int } else { blk_ord(j as int, cm, py - 1) },
            j <= jn < n_o(sv),
            runs_inv(*runs, sv, seg, dl, lo, b + py, jn, cap),
            mf == (|i: int| blk_ord(j as int, cm, i - b)),
        decreases 64 - py,
    {
        let t = tz64(y, table);
        proof {
            lemma_first_bit(y);
            assert(t as int >= py);
        }
        let ghost y0 = y;
        y = y & (y - 1);
        proof {
            assert(y0 - 1 == sub(y0, 1));
            assert forall|u: u64| u < 64 implies #[trigger] bit(y, u) == (bit(cand, u) && u >= t + 1) by {
                lemma_clear_lowest(y0, t as u64, u);
                if py <= u < t {
                    assert(!bit(y0, u));
                }
            }
        }
        // the order of row b + t: j plus the key changes up to t
        let n = popc_below(cm, t as u64, pct);
        proof {
            lemma_count_nonneg(cm, t as int + 1);
        }
        let jc = j + n as usize;
        proof {
            assert(jc == blk_ord(j as int, cm, t as int));
            assert(blk_ord(j as int, cm, t as int) <= blk_ord(j as int, cm, 63));
            if seqc {
                assert(ocb@[jc - j] == oc(sv)[jc as int]);
            }
            if py > 0 {
                assert(blk_ord(j as int, cm, py - 1) <= blk_ord(j as int, cm, t as int));
            }
            // rows b + py .. b + t are not candidates
            assert forall|i: int| b + py <= i < b + t implies maps_to(sv, i, #[trigger] mf(i)) && !line_hit(sv, seg, dl, i, mf(i)) by {
                let u = i - b;
                assert(!bit(cand, u as u64)) by {
                    assert(!bit(y0, u as u64));
                }
                lemma_block_misses(sv, seg, dl, b as int, j as int, cm, cand, u);
            }
            lemma_runs_misses(*runs, sv, seg, dl, lo, b + py, b + t, jn, jc as int, cap, mf);
            assert(maps_to(sv, b + (t as u64), blk_ord(j as int, cm, (t as u64) as int)));
            assert(bit(cand, t as u64));
        }
        let i = b + t as usize;
        let ghost runs_before = *runs;
        let cok = cached_cust(c, bits, cache, jc, seqc, ocb, j, Ghost(sv), Ghost(seg), Ghost(dl));
        if cok {
            let v = match row_value(c, i, Ghost(sv), Ghost(seg), Ghost(dl)) {
                Some(v) => v,
                None => { return None; }
            };
            assert(line_hit(sv, seg, dl, i as int, jc as int));
            runs_hit(runs, jc, v, Ghost(sv), Ghost(seg), Ghost(dl), Ghost(lo), Ghost(i as int), Ghost(jc as int), Ghost(cap));
        } else {
            proof {
                assert(!line_hit(sv, seg, dl, i as int, jc as int));
                let mfi = |k: int| jc as int;
                lemma_runs_misses(runs_before, sv, seg, dl, lo, i as int, i as int + 1, jc as int, jc as int, cap, mfi);
            }
        }
        proof {
            py = t as int + 1;
            jn = jc as int;
        }
    }
    proof {
        assert forall|i: int| b + py <= i < b + 64 implies maps_to(sv, i, #[trigger] mf(i)) && !line_hit(sv, seg, dl, i, mf(i)) by {
            let u = i - b;
            assert(!bit(cand, u as u64)) by {
                assert(!bit(y, u as u64)) by { lemma_bit_zero(u as u64); }
            }
            lemma_block_misses(sv, seg, dl, b as int, j as int, cm, cand, u);
        }
        if py > 0 {
            assert(blk_ord(j as int, cm, py - 1) <= blk_ord(j as int, cm, 63));
        }
        lemma_runs_misses(*runs, sv, seg, dl, lo, b + py, b + 64, jn, jj as int, cap, mf);
    }
    Some(jj)
}

// ------------------------------------------------------------------------------------------------ the worker task

/// A task's result, valid when `ok`: the runs of rows `lo..hi` (ghost), the first (`fj`, `fs`) and the last (`lj`,
/// `ls`) of them, and the top 10 of the others (`top`, each entry tagged with its order).
pub struct ScanOut {
    pub rj: Ghost<Seq<usize>>,
    pub rsum: Ghost<Seq<i128>>,
    pub n: usize,
    pub ok: bool,
    pub top: FixTop,
    pub fj: usize,
    pub fs: i128,
    pub lj: usize,
    pub ls: i128,
}

/// The runs of rows `lo..hi`: strictly increasing orders, each with its exact sum over the range, every hit order
/// present, and every hit within `VMAX`.
pub open spec fn scan_out_ok(o: ScanOut, sv: StoresView, seg: Seq<u8>, dl: int, lo: int, hi: int) -> bool {
    &&& o.n == o.rj@.len() && o.n == o.rsum@.len()
    &&& o.n > 0 ==> o.fj == o.rj@[0] && o.fs == o.rsum@[0] && o.lj == o.rj@[o.n - 1] && o.ls == o.rsum@[o.n - 1]
    &&& forall|t: int, u: int| 0 <= t < u < o.n ==> o.rj@[t] < o.rj@[u]
    &&& forall|t: int| 0 <= t < o.n ==> (#[trigger] o.rj@[t] as int) < n_o(sv)
    &&& forall|t: int| 0 <= t < o.n ==> #[trigger] o.rsum@[t] as int == order_sum(sv, seg, dl, o.rj@[t] as int, lo, hi)
            && order_count(sv, seg, dl, o.rj@[t] as int, lo, hi) > 0
    &&& forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, lo, hi) > 0 ==>
            exists|t: int| 0 <= t < o.n && o.rj@[t] == j
    &&& mass_bounded(sv, seg, dl, lo, hi)
}

/// The task's selection `o.top` is the top 10 (by sum, then date) of its interior runs, each entry tagged with its
/// order.
pub open spec fn ltop_ok(o: ScanOut, sv: StoresView) -> bool {
    &&& fix_inv(o.top, litems(o.n), lvals(o.n, o.rsum@), lvf(o.rsum@), ldf(o.rj@, sv))
    &&& fix_tags(o.top, lof(o.rj@))
}

/// One task of the lineitem scan: rows `lo..hi`, with the preallocated top 10 of its interior runs.
pub struct ScanTask {
    pub cols: ScanCols,
    pub bits: Arc<Vec<u64>>,
    pub lo: usize,
    pub hi: usize,
    pub top: FixTop,
    pub seqc: bool,
    pub ocb: Vec<i64>,
    pub sv: Ghost<StoresView>,
    pub seg: Ghost<Seq<u8>>,
    pub dl: Ghost<int>,
}

fn scan_fail(runs: Runs) -> (o: ScanOut)
    ensures !o.ok,
    no_unwind
{
    ScanOut { rj: runs.rj, rsum: runs.rsum, n: 0, ok: false, top: runs.top, fj: 0, fs: 0, lj: 0, ls: 0 }
}

/// Close the open run: the accumulator over `lo..hi` becomes the task's result. Its top already holds the top 10
/// of the closed runs after the first; with the open run as the last run, those are exactly the interior runs.
fn scan_finish(runs: Runs, Ghost(sv): Ghost<StoresView>, Ghost(seg): Ghost<Seq<u8>>, Ghost(dl): Ghost<int>, Ghost(lo): Ghost<int>,
    Ghost(hi): Ghost<int>, Ghost(jnow): Ghost<int>, Ghost(cap): Ghost<int>) -> (o: ScanOut)
    requires runs_inv(runs, sv, seg, dl, lo, hi, jnow, cap),
    ensures o.ok, scan_out_ok(o, sv, seg, dl, lo, hi), ltop_ok(o, sv),
    no_unwind
{
    let ghost r0 = runs;
    let Runs { rj, rsum, fj, fs, top, odate, n, open, cur_j, cur_sum, hits } = runs;
    if open {
        let ghost (rj1, rs1) = (rj@.push(cur_j), rsum@.push(cur_sum));
        let first_j = if n == 0 { cur_j } else { fj };
        let first_s = if n == 0 { cur_sum } else { fs };
        proof {
            assert(n + 1 <= cap);
            lemma_rtop_close(top, n, rj@, rsum@, cur_j, cur_sum, sv);
            if n == 0 {
                assert(litems(1) =~= litems(2));
                assert(lvals(1, rs1) =~= lvals(2, rs1));
            } else {
                assert(lvals((n + 1) as usize, rsum@) =~= lvals((n + 1) as usize, rs1));
            }
            assert forall|j: int| 0 <= j < n_o(sv) && #[trigger] order_count(sv, seg, dl, j, lo, hi) > 0 implies
                exists|t: int| 0 <= t < n + 1 && rj1[t] == j by {
                if exists|t: int| 0 <= t < r0.n && r0.rj@[t] == j {
                    let t = choose|t: int| 0 <= t < r0.n && r0.rj@[t] == j;
                    assert(rj1[t] == j);
                } else {
                    assert(rj1[n as int] == j);
                }
            }
            assert forall|t: int| 0 <= t < n + 1 implies #[trigger] rs1[t] as int == order_sum(sv, seg, dl, rj1[t] as int, lo, hi)
                && order_count(sv, seg, dl, rj1[t] as int, lo, hi) > 0 by {
                if t < n {
                    assert(rs1[t] == r0.rsum@[t] && rj1[t] == r0.rj@[t]);
                }
            }
            assert forall|t: int| 0 <= t < n + 1 implies (#[trigger] rj1[t] as int) < n_o(sv) by {
                if t < n {
                    assert(rj1[t] == r0.rj@[t]);
                    assert(r0.rj@[t] < r0.cur_j);
                }
            }
            assert forall|t: int, u: int| 0 <= t < u < n + 1 implies rj1[t] < rj1[u] by {
                if u == n {
                    assert(rj1[t] == r0.rj@[t]);
                } else {
                    assert(rj1[t] == r0.rj@[t] && rj1[u] == r0.rj@[u]);
                }
            }
        }
        ScanOut { rj: Ghost(rj1), rsum: Ghost(rs1), n: n + 1, ok: true, top, fj: first_j, fs: first_s, lj: cur_j, ls: cur_sum }
    } else {
        proof {
            assert(litems(0) =~= litems(1));
            assert(lvals(0, rsum@) =~= lvals(1, rsum@));
        }
        ScanOut { rj, rsum, n, ok: true, top, fj: 0, fs: 0, lj: 0, ls: 0 }
    }
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        &&& scan_cols_ok(self.cols, self.sv@, self.seg@, self.dl@)
        &&& cust_bits_ok(self.bits@, self.sv@, self.seg@, self.cols.cbase as int, self.cols.nc as int)
        &&& self.lo <= self.hi <= self.cols.nl
        &&& fix_wf(self.top) && self.top.k == 0
        &&& self.ocb@.len() == 65
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        out.ok ==> scan_out_ok(out, self.sv@, self.seg@, self.dl@, self.lo as int, self.hi as int) && ltop_ok(out, self.sv@)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: ScanOut) {
        let c = self.cols;
        let lo = self.lo;
        let hi = self.hi;
        let ghost (sv, seg, dl) = (self.sv@, self.seg@, self.dl@);
        let ghost cap: int = hi - lo;
        let bits: &Vec<u64> = &*self.bits;
        let runs = Runs {
            rj: Ghost(Seq::empty()), rsum: Ghost(Seq::empty()), fj: 0, fs: 0, top: self.top, odate: c.odate,
            n: 0, open: false, cur_j: 0, cur_sum: 0, hits: Ghost(0),
        };
        let seqc = self.seqc;
        let mut ocb = self.ocb;
        let mut runs = runs;
        proof {
            lemma_runs_empty(runs, sv, seg, dl, lo as int, 0, cap);
        }
        if lo == hi {
            return scan_finish(runs, Ghost(sv), Ghost(seg), Ghost(dl), Ghost(lo as int), Ghost(hi as int), Ghost(0), Ghost(cap));
        }
        let table = tz_table_array();
        let pct = match pc_table() {
            Some(t) => t,
            None => { return scan_fail(runs); }
        };
        let j0 = match find_key(c.okey, c.no, c.lkey[lo]) {
            Some(x) => x,
            None => { return scan_fail(runs); }
        };
        proof {
            lemma_runs_empty(runs, sv, seg, dl, lo as int, j0 as int, cap);
        }
        let mut j = j0;
        let mut prev = c.lkey[lo];
        let mut cache = CustCache { j: usize::MAX, ok: false };
        let mut b = lo;
        while hi - b >= 64 && c.no - j > 64
            invariant
                scan_cols_ok(c, sv, seg, dl), cust_bits_ok(bits@, sv, seg, c.cbase as int, c.nc as int), table@.len() == 64,
                pc_ok(pct@), ocb@.len() == 65,
                scan_state(c, runs, sv, seg, dl, lo as int, b as int, j as int, prev, cap),
                cache_ok(cache, sv, seg),
                lo <= b <= hi <= c.nl, cap == hi - lo,
            decreases hi - b,
        {
            match scan_block(c, bits, &table, &pct, seqc, &mut ocb, &mut runs, &mut cache, b, j, prev, Ghost(sv), Ghost(seg), Ghost(dl), Ghost(lo as int),
                Ghost(cap)) {
                Some(j2) => {
                    prev = c.lkey[b + 63];
                    j = j2;
                    b = b + 64;
                },
                None => { return scan_fail(runs); },
            }
        }
        while b < hi
            invariant
                scan_cols_ok(c, sv, seg, dl), cust_bits_ok(bits@, sv, seg, c.cbase as int, c.nc as int),
                scan_state(c, runs, sv, seg, dl, lo as int, b as int, j as int, prev, cap),
                cache_ok(cache, sv, seg),
                lo <= b <= hi <= c.nl, cap == hi - lo,
            decreases hi - b,
        {
            match scan_row(c, bits, &ocb, &mut runs, &mut cache, b, j, prev, Ghost(sv), Ghost(seg), Ghost(dl), Ghost(lo as int), Ghost(cap)) {
                Some(j2) => {
                    prev = c.lkey[b];
                    j = j2;
                    b = b + 1;
                },
                None => { return scan_fail(runs); },
            }
        }
        scan_finish(runs, Ghost(sv), Ghost(seg), Ghost(dl), Ghost(lo as int), Ghost(hi as int), Ghost(j as int), Ghost(cap))
    }
}

} // verus!
