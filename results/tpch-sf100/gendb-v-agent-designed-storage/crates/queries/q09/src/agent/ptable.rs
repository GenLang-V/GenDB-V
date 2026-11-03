//! The compact partsupp table of the matching parts (`scan::ents_ok`): one `build::BuildTask` per range of `per` part
//! rows (`per` a power of two, so the range of part row `c` is `c / per`), sized by the matching parts of its range.
//! The ranges' word prefixes (`wpre`, global ranks) are concatenated; each range keeps its own entries (no copy), the
//! part of rank `r` in range `t` owning the entries from `(r - k0s[t]) * SLOTS`. `None` when some range could not
//! build its part (the kernel then reads partsupp directly).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::work::filled;
use super::model::*;
use super::cols::*;
use super::lookups::*;
use super::scan::*;
use super::build::*;
use super::common::popcnt::{cnt_below, count_below};

verus! {

/// `a * 64` (hidden from loop contexts).
#[verifier::opaque]
pub open spec fn x64(a: int) -> int {
    a * 64
}

/// The fields of build task `t` over the part rows of `[0, n)`.
pub open spec fn btask_fields(t: BuildTask, c: Cols, d: Divs, bits: Arc<Vec<u64>>, p_dense: bool, m: M, n: int) -> bool {
    &&& t.cols == c && t.divs == d && t.bits == bits && t.p_dense == p_dense && t.m@ == m
    &&& ntab_ok((*t.ntab)@, true, m) && s_dense_ok(m) && m.n_n < NO_TAG
    &&& t.c_lo <= t.c_hi <= n && t.c_lo % 64 == 0 && t.c_hi + 64 <= usize::MAX
    &&& t.wpre@.len() == (t.c_hi - t.c_lo + 63) / 64
    &&& t.ents@.len() == t.cap * SLOTS
    &&& t.cap * SLOTS <= usize::MAX
}

pub open spec fn bhi_of(ts: Seq<BuildTask>, t: int) -> int {
    ts[t].c_hi as int
}

/// Build tasks over `[0, n)`: task `t` holds the part rows `[t * per, min((t + 1) * per, n))`, its first rank `k0s[t]`.
pub open spec fn btasks_ok(ts: Seq<BuildTask>, k0s: Seq<u64>, per: int, c: Cols, d: Divs, bits: Arc<Vec<u64>>, p_dense: bool, m: M, n: int) -> bool {
    &&& k0s.len() == ts.len()
    &&& per >= 64 && per % 64 == 0
    &&& forall|t: int| 0 <= t < ts.len() ==> btask_fields(#[trigger] ts[t], c, d, bits, p_dense, m, n)
    &&& forall|t: int| 0 <= t < ts.len() ==> (#[trigger] ts[t]).c_lo == t * per && ts[t].k0 == k0s[t]
        && (ts[t].c_hi == (t + 1) * per || ts[t].c_hi == n) && ts[t].c_hi <= (t + 1) * per
    &&& forall|t: int| 0 <= t < ts.len() - 1 ==> #[trigger] bhi_of(ts, t) == ts[t + 1].c_lo
    &&& ts.len() > 0 ==> ts[ts.len() - 1].c_hi == n
    &&& ts.len() == 0 ==> n == 0
}

/// `ceil(k / 64)` without overflow.
fn words_for(k: usize) -> (r: usize)
    ensures r == (k + 63) / 64,
{
    let q = k / 64;
    if k % 64 == 0 { q } else { q + 1 }
}

/// The matching parts among part rows `[lo, hi)` (word aligned), capped at `2^28`.
fn range_hits(bits: &Vec<u64>, lo: usize, hi: usize) -> (r: usize)
    ensures r < 0x1000_0000,
{
    let mut w = lo / 64;
    let we = if hi / 64 < bits.len() { hi / 64 } else { bits.len() };
    let mut cnt: usize = 0;
    while w < we
        invariant cnt < 0x1000_0000 + 64, we <= bits@.len(),
        decreases we - w,
    {
        if cnt >= 0x1000_0000 {
            return 0x0fff_ffff;
        }
        cnt = cnt + count_below(bits[w], 64) as usize;
        w = w + 1;
    }
    if w < bits.len() && hi % 64 != 0 {
        if cnt >= 0x1000_0000 {
            return 0x0fff_ffff;
        }
        cnt = cnt + count_below(bits[w], 64) as usize;
    }
    if cnt >= 0x1000_0000 { 0x0fff_ffff } else { cnt }
}

/// At most `workers` build tasks over the part rows, in ranges of `per` rows (a power of two, at least 64) from 0,
/// each sized by its matching parts; `per` and the ranks of the tasks' first parts.
fn build_tasks(c: Cols, d: Divs, bits: &Arc<Vec<u64>>, ntab: &Arc<Vec<u64>>, p_dense: bool, workers: usize, Ghost(m): Ghost<M>)
    -> (r: Option<(Vec<BuildTask>, Vec<u64>, usize)>)
    requires 1 <= workers <= MAX_WORKERS, c.p_n == m.p_n, ntab_ok((**ntab)@, true, m), s_dense_ok(m), m.n_n < NO_TAG,
    ensures r matches Some((v, k0s, per)) ==> v.len() <= workers && btasks_ok(v@, k0s@, per as int, c, d, *bits, p_dense, m, m.p_n as int),
{
    let n = c.p_n;
    if n >= 0x4000_0000 {
        return None;
    }
    let target = n / workers + 1;
    let mut per: usize = 64;
    while per < target && per <= 0x2000_0000
        invariant per >= 64, per % 64 == 0, per <= 0x4000_0000,
        decreases 0x4000_0000 - per,
    {
        per = per * 2;
    }
    if per < target {
        return None;
    }
    proof {
        assert(per * workers > n) by (nonlinear_arith) requires per >= n / workers + 1, workers >= 1, n >= 0;
    }
    let mut tasks: Vec<BuildTask> = Vec::new();
    let mut k0s: Vec<u64> = Vec::new();
    let mut lo: usize = 0;
    let mut k0: u64 = 0;
    while lo < n
        invariant
            1 <= workers <= MAX_WORKERS, per % 64 == 0, per >= 64, per <= 0x4000_0000, n == m.p_n,
            ntab_ok((**ntab)@, true, m), s_dense_ok(m), m.n_n < NO_TAG,
            n < 0x4000_0000, per * workers > n,
            lo <= n, lo % 64 == 0 || lo == n,
            lo < n ==> lo == tasks.len() * per,
            k0 <= tasks.len() * 0x1000_0000,
            tasks.len() <= workers,
            btasks_ok(tasks@, k0s@, per as int, c, d, *bits, p_dense, m, lo as int),
            tasks.len() > 0 ==> k0 == tasks@[tasks.len() - 1].k0 + tasks@[tasks.len() - 1].cap,
            tasks.len() == 0 ==> k0 == 0 && lo == 0,
        decreases n - lo,
    {
        proof {
            assert(tasks.len() < workers) by (nonlinear_arith) requires lo == tasks.len() * per, lo < n, per * workers > n, per >= 1;
        }
        let hi = if n - lo <= per { n } else { lo + per };
        let cap = range_hits(bits, lo, hi);
        let ev: Vec<u64> = vec![0u64; cap * SLOTS];
        let t = BuildTask { cols: c, divs: d, bits: bits.clone(), ntab: ntab.clone(), p_dense, c_lo: lo, c_hi: hi, k0, cap,
            wpre: filled(words_for(hi - lo), 0u32), ents: ev, m: Ghost(m) };
        proof {
            assert(btask_fields(t, c, d, *bits, p_dense, m, hi as int));
            assert((tasks.len() + 1) * per == tasks.len() * per + per) by (nonlinear_arith);
        }
        let ghost t0 = tasks@;
        let ghost q0 = k0s@;
        let ghost nt0 = tasks.len() as int;
        tasks.push(t);
        k0s.push(k0);
        proof {
            assert(tasks@[nt0] == t);
            assert forall|x: int| 0 <= x < tasks.len() implies btask_fields(#[trigger] tasks@[x], c, d, *bits, p_dense, m, hi as int) by {
                if x < nt0 { assert(tasks@[x] == t0[x]); assert(btask_fields(t0[x], c, d, *bits, p_dense, m, lo as int)); }
            }
            assert forall|x: int| 0 <= x < tasks.len() implies (#[trigger] tasks@[x]).c_lo == x * per && tasks@[x].k0 == k0s@[x]
                && (tasks@[x].c_hi == (x + 1) * per || tasks@[x].c_hi == hi) && tasks@[x].c_hi <= (x + 1) * per by {
                if x < nt0 {
                    assert(tasks@[x] == t0[x] && k0s@[x] == q0[x]);
                    assert(t0[x].c_hi == (x + 1) * per || t0[x].c_hi == lo);
                    if t0[x].c_hi != (x + 1) * per {
                        assert(x == nt0 - 1) by {
                            if x < nt0 - 1 { assert(bhi_of(t0, x) == t0[x + 1].c_lo); }
                        }
                        assert(lo == nt0 * per);
                    }
                }
            }
            assert forall|x: int| 0 <= x < tasks.len() - 1 implies #[trigger] bhi_of(tasks@, x) == tasks@[x + 1].c_lo by {
                assert(tasks@[x] == t0[x]);
                if x + 1 < nt0 { assert(tasks@[x + 1] == t0[x + 1]); assert(bhi_of(t0, x) == t0[x + 1].c_lo); }
                else { assert(t0[x].c_hi == lo); }
            }
            assert(tasks.len() <= 64);
            assert(k0 + cap <= tasks.len() * 0x1000_0000);
        }
        k0 = k0 + cap as u64;
        lo = hi;
    }
    Some((tasks, k0s, per))
}

/// Every matching part row below `hi` has its rank and its entries in its range's table (hidden from loop contexts).
#[verifier::opaque]
pub open spec fn cover_upto(bits: Seq<u64>, wpre: Seq<u32>, tabs: Seq<BuildOut>, k0s: Seq<u64>, per: int, m: M, hi: int) -> bool {
    forall|c: int| 0 <= c < hi && c < m.p_n && #[trigger] bit_of(bits, c) ==> ents_at(bits, wpre, tabs, k0s, per, m, c)
}

/// A build task's output (`build_post`, hidden from loop contexts).
#[verifier::opaque]
pub open spec fn bpost_of(t: BuildTask, o: BuildOut) -> bool {
    build_post(t, o)
}

/// Range `t`'s word prefixes appended: its matching parts have their entries in table `t`.
proof fn lemma_table_step(t: BuildTask, o: BuildOut, ti: int, wp: Seq<u32>, tabs: Seq<BuildOut>, k0s: Seq<u64>, per: int,
    bits: Seq<u64>, m: M)
    requires
        t.c_lo <= t.c_hi, t.c_lo % 64 == 0, t.wpre@.len() == (t.c_hi - t.c_lo + 63) / 64,
        t.ents@.len() == t.cap * SLOTS, t.cap * SLOTS <= usize::MAX, (*t.bits)@ == bits, t.m@ == m,
        bpost_of(t, o), o.ok,
        0 <= ti < tabs.len(), tabs[ti] == o, k0s.len() == tabs.len(), k0s[ti] == t.k0,
        per >= 1, t.c_lo == ti * per, t.c_hi <= (ti + 1) * per,
        x64(wp.len() as int) == t.c_lo,
        cover_upto(bits, wp, tabs, k0s, per, m, t.c_lo as int),
    ensures
        cover_upto(bits, wp + o.wpre@, tabs, k0s, per, m, t.c_hi as int),
        x64((wp + o.wpre@).len() as int) >= t.c_hi,
        (t.c_hi - t.c_lo) % 64 == 0 ==> x64((wp + o.wpre@).len() as int) == t.c_hi,
{
    reveal(x64);
    reveal(bpost_of);
    reveal(cover_upto);
    let wg = wp + o.wpre@;
    let ws = o.wpre@;
    assert(ws.len() == (t.c_hi - t.c_lo + 63) / 64);
    assert((wp.len() + ws.len()) * 64 >= t.c_hi) by (nonlinear_arith)
        requires ws.len() == (t.c_hi - t.c_lo + 63) / 64, wp.len() * 64 == t.c_lo, t.c_lo <= t.c_hi;
    if (t.c_hi - t.c_lo) % 64 == 0 {
        assert((wp.len() + ws.len()) * 64 == t.c_hi) by (nonlinear_arith)
            requires ws.len() == (t.c_hi - t.c_lo + 63) / 64, wp.len() * 64 == t.c_lo, t.c_lo <= t.c_hi, (t.c_hi - t.c_lo) % 64 == 0;
    }
    assert forall|c: int| 0 <= c < t.c_hi && c < m.p_n && #[trigger] bit_of(bits, c) implies
        ents_at(bits, wg, tabs, k0s, per, m, c) by {
        if c < t.c_lo {
            assert(c / 64 < wp.len());
            assert(wg[c / 64] == wp[c / 64]);
            assert(rank_of(bits, wg, c) == rank_of(bits, wp, c));
            assert(ents_at(bits, wp, tabs, k0s, per, m, c));
        } else {
            assert((c - t.c_lo) / 64 == c / 64 - wp.len()) by (nonlinear_arith)
                requires wp.len() * 64 == t.c_lo, c >= t.c_lo;
            assert(wg[c / 64] == ws[(c - t.c_lo) / 64]);
            assert(rank_of(bits, wg, c) == local_rank(bits, ws, t.c_lo as int, c));
            assert(c / per == ti) by (nonlinear_arith) requires ti * per <= c < (ti + 1) * per, per >= 1;
            let r = rank_of(bits, wg, c);
            assert(t.k0 <= r && local_cover(m, o.ents@, r - t.k0, pkey(m, c)));
        }
    }
}

/// The compact partsupp table: the word prefixes of all ranges and each range's table, `None` when it could not be
/// built (also when supplier keys are not dense, a nation key leaves `[0, 256)` or there are `NO_TAG` nations or more:
/// the entries then could not hold the nation tag).
pub fn part_table(c: Cols, d: Divs, bits: &Arc<Vec<u64>>, ntab: &Arc<Vec<u64>>, n_small: bool, s_dense: bool, p_dense: bool,
    workers: usize, dispatch: &mut Dispatch, Ghost(m): Ghost<M>)
    -> (r: Result<Option<(Vec<u32>, Vec<BuildOut>, Vec<u64>, usize)>, QueryError>)
    requires
        look_ok(c, d, m), p_dense ==> p_dense_ok(m), (**bits)@.len() * 64 >= m.p_n,
        ntab_ok((**ntab)@, n_small, m), s_dense ==> s_dense_ok(m),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some((wpre, tabs, k0s, per))) ==> ents_ok((**bits)@, wpre@, tabs@, k0s@, per as int, m),
        r matches Err(e) ==> e is WorkerFailed,
{
    if !(n_small && s_dense && (c.n_n as u64) < NO_TAG) {
        return Ok(None);
    }
    let (tasks, k0s, per) = match build_tasks(c, d, bits, ntab, p_dense, workers, Ghost(m)) {
        Some(t) => t,
        None => { return Ok(None); },
    };
    let ghost ts = tasks@;
    let ghost bv = (**bits)@;
    let wpre_cap: usize = c.p_n / 64 + 1;
    proof {
        assert forall|t: int| 0 <= t < tasks.len() implies #[trigger] tasks@[t].pre() by {
            assert(btask_fields(tasks@[t], c, d, *bits, p_dense, m, m.p_n as int));
        }
    }
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => { return Err(QueryError::WorkerFailed(e)); },
    };
    proof {
        assert forall|t: int| 0 <= t < ts.len() implies bpost_of(#[trigger] ts[t], outs@[t]) by {
            assert(ts[t].post(outs@[t]));
            reveal(bpost_of);
        }
        reveal(cover_upto);
        reveal(x64);
    }
    let mut wpre: Vec<u32> = Vec::with_capacity(wpre_cap);
    let mut k: usize = 0;
    while k < outs.len()
        invariant
            outs.len() == ts.len(), bv == (**bits)@, k0s@.len() == ts.len(),
            forall|t: int| 0 <= t < ts.len() ==> bpost_of(#[trigger] ts[t], outs@[t]),
            btasks_ok(ts, k0s@, per as int, c, d, *bits, p_dense, m, m.p_n as int),
            k <= ts.len(),
            forall|t: int| 0 <= t < k ==> (#[trigger] outs@[t]).ok,
            k < ts.len() ==> x64(wpre@.len() as int) == ts[k as int].c_lo,
            k == ts.len() && k > 0 ==> x64(wpre@.len() as int) >= ts[k - 1].c_hi,
            cover_upto(bv, wpre@, outs@, k0s@, per as int, m, if k == 0 { 0 } else { ts[k - 1].c_hi as int }),
        decreases ts.len() - k,
    {
        if !outs[k].ok {
            return Ok(None);
        }
        let ghost t = ts[k as int];
        let ghost w0 = wpre@;
        let o = &outs[k];
        let mut i: usize = 0;
        while i < o.wpre.len()
            invariant i <= o.wpre@.len(), wpre@ == w0 + o.wpre@.subrange(0, i as int),
            decreases o.wpre@.len() - i,
        {
            wpre.push(o.wpre[i]);
            proof { assert(wpre@ =~= w0 + o.wpre@.subrange(0, i + 1)); }
            i = i + 1;
        }
        proof {
            assert(o.wpre@.subrange(0, o.wpre@.len() as int) =~= o.wpre@);
            assert(bpost_of(t, outs@[k as int]));
            assert(btask_fields(t, c, d, *bits, p_dense, m, m.p_n as int));
            assert(t.c_lo == k * per && t.k0 == k0s@[k as int]);
            if k > 0 { assert(bhi_of(ts, k - 1) == t.c_lo); }
            lemma_table_step(t, *o, k as int, w0, outs@, k0s@, per as int, bv, m);
            if k + 1 < ts.len() {
                assert(bhi_of(ts, k as int) == ts[k + 1].c_lo);
                assert(btask_fields(ts[k + 1], c, d, *bits, p_dense, m, m.p_n as int));
                assert(ts[k + 1].c_lo == (k + 1) * per);
                assert((t.c_hi - t.c_lo) % 64 == 0) by {
                    assert(t.c_hi == (k + 1) * per || t.c_hi == m.p_n);
                    if t.c_hi != (k + 1) * per { assert(t.c_hi == ts[k + 1].c_lo); }
                    assert((per as int) % 64 == 0);
                    assert(((k + 1) * per - k * per) % 64 == 0) by (nonlinear_arith) requires per % 64 == 0, k >= 0;
                }
            }
        }
        k = k + 1;
    }
    proof {
        reveal(cover_upto);
        reveal(x64);
        if ts.len() > 0 { assert(ts[ts.len() - 1].c_hi == m.p_n); }
        assert forall|cc: int| 0 <= cc < m.p_n && #[trigger] bit_of(bv, cc) implies ents_at(bv, wpre@, outs@, k0s@, per as int, m, cc) by {}
    }
    Ok(Some((wpre, outs, k0s, per)))
}

} // verus!
