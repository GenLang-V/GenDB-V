//! Serial scan of the fiscal-year range `[a, a + m)` of `$2` on the calling thread (one worker), in three passes.
//!
//! The per-row path of the parallel task (`scan::ScanTask`) interleaves a chain of dependent lookups with the
//! summation of each filing's run, which visits the runs in fiscal-year order, i.e. at random places of the 16-byte
//! value column. Here the work is split so that each pass is a loop of independent iterations:
//! 1. `pass_match`: every position's run (relative to `r0`, `nr` for none) into `rp`, and per run the position that
//!    claimed it into `dest` (`m` for none);
//! 2. `pass_sums`: the runs of the uom range in increasing order (increasing value addresses); a run claimed by a
//!    position is summed into that position's slots of `ss`/`ms`;
//! 3. `pass_collect`: the entries in position order; a position whose run was claimed by another position (two rows
//!    of one filing) sums its run again, so correctness never depends on `dest` being injective.
//!
//! Contract (`scan_serial`): without `Err` the result lists `filt(c, a, a + m)` and no row of the range is big; `Err`
//! means a big row in the range.
use vstd::prelude::*;
use crate::gendb_entry::work::{filled, put};
use crate::stores::num::interface as num_if;
use crate::stores::num::interface::{u64s, run_count};
use crate::stores::sub_fy::interface as sub_if;
use crate::stores::sub_fy::interface::fy_order;
use crate::stores::sub_fy::interface::common::perm::lemma_permutation_facts;
use crate::agent::common::sort::Filing;
use crate::agent::common::sums::*;
use crate::agent::scan::*;
use crate::agent::numlink::{run_lo, run_hi, run_sum, run_mass, val_term, abs_term_at};
use crate::agent::steps::{NumIn, SubIn, inputs_ok};

verus! {

// ------------------------------------------------------------------------------------------------ specification

/// Pass-1 result `x` of position `a + q`: the row's run `r0 + x` when `x < nr`, no run when `x == nr`.
pub open spec fn match_ok(c: ScanCtx, a: int, q: int, x: u64, nr: int) -> bool {
    &&& x <= nr
    &&& x < nr ==> run_match(c, row_at(c, a + q), c.r0 + x)
    &&& x == nr ==> forall|rr: int| !#[trigger] run_match(c, row_at(c, a + q), rr)
}

/// Exact sum and mass of run `r0 + r`, the mass within `i128`.
pub open spec fn sums_ok(c: ScanCtx, r: int, s: i128, m: u128) -> bool {
    &&& s as int == run_sum(c.np, c.r0 + r)
    &&& m as int == run_mass(c.np, c.r0 + r)
    &&& m <= i128::MAX as u128
}

/// Every position of `[a, a + m)` has `fy = $2`'s sort word.
pub open spec fn range_ok(c: ScanCtx, a: int, m: int) -> bool {
    &&& 0 <= a && a + m <= n_sub(c)
    &&& -0x8000_0000 <= c.p1 < 0x8000_0000
    &&& forall|q: int| a <= q < a + m ==> #[trigger] word_at(c, q) == fy_target(c.p1)
}

// ------------------------------------------------------------------------------------------------ proof steps

/// The row at a position of the range has `fy = $2` and is a sub row.
proof fn lemma_row_fy(c: ScanCtx, a: int, m: int, q: int)
    requires ctx_ok(c), range_ok(c, a, m), 0 <= q < m,
    ensures 0 <= row_at(c, a + q) < n_sub(c), fy_ok(c, row_at(c, a + q)),
{
    lemma_permutation_facts(fy_order(c.sp), n_sub(c) as nat);
    assert(word_at(c, a + q) == fy_target(c.p1));
    lemma_word_fy(c, row_at(c, a + q));
}

/// A run's stored boundaries, relative to the range's first value `v_lo`.
proof fn lemma_run_slots(c: ScanCtx, ni: NumIn, r: int)
    requires
        ctx_ok(c), ni.nr == c.r1 - c.r0, 0 <= r < ni.nr,
        ni.run_start@ == u64s(c.np, num_if::P_RUN_START).subrange(c.r0, c.r1 + 1),
        ni.v_lo as int == run_lo(c.np, c.r0),
        ni.values@.len() == run_lo(c.np, c.r1) - run_lo(c.np, c.r0),
    ensures
        ni.run_start@[r] as int == run_lo(c.np, c.r0 + r),
        ni.run_start@[r + 1] as int == run_hi(c.np, c.r0 + r),
        ni.v_lo <= ni.run_start@[r] <= ni.run_start@[r + 1],
        ni.run_start@[r + 1] - ni.v_lo <= ni.values@.len(),
{
    lemma_range(c);
    lemma_run_bounds(c, c.r0 + r);
    assert(ni.run_start@[r] == u64s(c.np, num_if::P_RUN_START)[c.r0 + r]);
    assert(ni.run_start@[r + 1] == u64s(c.np, num_if::P_RUN_START)[c.r0 + r + 1]);
}

/// A row of the range matched to run `r0 + r` qualifies, `r0 + r` is its run, and its entry carries that run.
proof fn lemma_matched_entry(c: ScanCtx, a: int, m: int, q: int, r: int)
    requires ctx_ok(c), range_ok(c, a, m), 0 <= q < m, run_match(c, row_at(c, a + q), c.r0 + r),
    ensures
        qualifies(c, row_at(c, a + q)),
        the_run(c, row_at(c, a + q)) == c.r0 + r,
{
    let j = row_at(c, a + q);
    lemma_row_fy(c, a, m, q);
    assert(matched(c, j));
    lemma_run_match_unique(c, j, c.r0 + r, the_run(c, j));
}

// ------------------------------------------------------------------------------------------------ pass 1

/// Pass 1: `rp[q]` is the run of position `a + q` (`match_ok`); `dest[r] < m` names a position whose run is `r`.
pub fn pass_match(ni: &NumIn, si: &SubIn, p1: i64, a: usize, m: usize, map: &Vec<u64>, Ghost(c): Ghost<ScanCtx>)
    -> (r: (Vec<u64>, Vec<u64>))
    requires
        inputs_ok(c, *ni, *si, p1), range_ok(c, a as int, m as int), run_map_ok(c, map@),
    ensures
        r.0@.len() == m, r.1@.len() == ni.nr,
        forall|q: int| 0 <= q < m ==> #[trigger] match_ok(c, a as int, q, r.0@[q], ni.nr as int),
        forall|x: int| 0 <= x < ni.nr && (#[trigger] r.1@[x]) < m ==> r.0@[r.1@[x] as int] == x,
{
    let nr = ni.nr;
    let ns = si.ns;
    proof {
        lemma_permutation_facts(fy_order(c.sp), n_sub(c) as nat);
        assert(sub_if::adsh_rank(c.sp).len() == n_sub(c));
    }
    let mut rp: Vec<u64> = filled(m, nr as u64);
    let mut dest: Vec<u64> = filled(nr, m as u64);
    let mut q: usize = 0;
    while q < m
        invariant
            inputs_ok(c, *ni, *si, p1), range_ok(c, a as int, m as int), run_map_ok(c, map@),
            nr == ni.nr, ns == si.ns, q <= m,
            forall|i: int| 0 <= i < n_sub(c) ==> #[trigger] fy_order(c.sp)[i] < n_sub(c),
            fy_order(c.sp).len() == n_sub(c), sub_if::adsh_rank(c.sp).len() == n_sub(c),
            rp@.len() == m, dest@.len() == nr,
            forall|i: int| 0 <= i < q ==> #[trigger] match_ok(c, a as int, i, rp@[i], nr as int),
            forall|x: int| 0 <= x < nr && (#[trigger] dest@[x]) < m ==> dest@[x] < q && rp@[dest@[x] as int] == x,
        decreases m - q,
    {
        let j = si.fy_order[a + q] as usize;
        let hint = si.adsh_rank[j];
        let x = match_run(si.adsh_off, si.adsh_bytes, ns, j, hint, ni.run_adsh, map, nr, ni.dict_off, ni.dict_bytes,
            ni.dict_count, Ghost(c));
        put(&mut rp, q, x as u64);
        if x < nr {
            put(&mut dest, x, q as u64);
        }
        proof {
            assert(row_at(c, a + q) == j);
            assert(match_ok(c, a as int, q as int, rp@[q as int], nr as int));
        }
        q = q + 1;
    }
    (rp, dest)
}

// ------------------------------------------------------------------------------------------------ pass 2

/// Pass 2: every position `q` whose run `rp[q]` names it in `dest` has its run's sums in `ss[q]`, `ms[q]`; `Err`:
/// a big row in the range.
pub fn pass_sums(ni: &NumIn, si: &SubIn, p1: i64, a: usize, m: usize, rp: &Vec<u64>, dest: &Vec<u64>,
    Ghost(c): Ghost<ScanCtx>) -> (r: Result<(Vec<i128>, Vec<u128>), ()>)
    requires
        inputs_ok(c, *ni, *si, p1), range_ok(c, a as int, m as int),
        rp@.len() == m, dest@.len() == ni.nr,
        forall|q: int| 0 <= q < m ==> #[trigger] match_ok(c, a as int, q, rp@[q], ni.nr as int),
        forall|x: int| 0 <= x < ni.nr && (#[trigger] dest@[x]) < m ==> rp@[dest@[x] as int] == x,
    ensures
        r matches Ok((ss, ms)) ==> ss@.len() == m && ms@.len() == m
            && forall|q: int| 0 <= q < m && rp@[q] < ni.nr && #[trigger] dest@[rp@[q] as int] == q
                ==> sums_ok(c, rp@[q] as int, ss@[q], ms@[q]),
        r is Err ==> exists|p: int| a <= p < a + m && #[trigger] big(c, row_at(c, p)),
{
    let nr = ni.nr;
    let v_lo = ni.v_lo;
    let mut ss: Vec<i128> = filled(m, 0i128);
    let mut ms: Vec<u128> = filled(m, 0u128);
    let mut x: usize = 0;
    while x < nr
        invariant
            inputs_ok(c, *ni, *si, p1), range_ok(c, a as int, m as int),
            nr == ni.nr, v_lo == ni.v_lo, x <= nr,
            rp@.len() == m, dest@.len() == nr, ss@.len() == m, ms@.len() == m,
            forall|q: int| 0 <= q < m ==> #[trigger] match_ok(c, a as int, q, rp@[q], nr as int),
            forall|y: int| 0 <= y < nr && (#[trigger] dest@[y]) < m ==> rp@[dest@[y] as int] == y,
            forall|q: int| 0 <= q < m && rp@[q] < x && #[trigger] dest@[rp@[q] as int] == q
                ==> sums_ok(c, rp@[q] as int, ss@[q], ms@[q]),
        decreases nr - x,
    {
        let d = dest[x];
        if d < m as u64 {
            let q = d as usize;
            proof {
                assert(dest@[x as int] < m);
                assert(rp@[q as int] == x);
                lemma_run_slots(c, *ni, x as int);
            }
            let lo = (ni.run_start[x] - v_lo) as usize;
            let hi = (ni.run_start[x + 1] - v_lo) as usize;
            match sum_range(ni.values, lo, hi, Ghost(c.np), Ghost(v_lo as int)) {
                Some((s, mm)) => {
                    let ghost (ss0, ms0) = (ss@, ms@);
                    put(&mut ss, q, s);
                    put(&mut ms, q, mm);
                    proof {
                        assert(v_lo + lo == run_lo(c.np, c.r0 + x));
                        assert(v_lo + hi == run_hi(c.np, c.r0 + x));
                        lemma_rsum_abs(run_lo(c.np, c.r0 + x), run_hi(c.np, c.r0 + x), val_term(c.np), abs_term_at(c.np));
                        assert(sums_ok(c, x as int, s, mm));
                        assert forall|i: int| 0 <= i < m && rp@[i] < x + 1 && #[trigger] dest@[rp@[i] as int] == i
                            implies sums_ok(c, rp@[i] as int, ss@[i], ms@[i]) by {
                            if i != q {
                                assert(ss@[i] == ss0[i] && ms@[i] == ms0[i]);
                                if rp@[i] == x {
                                    assert(dest@[x as int] == i);
                                }
                            }
                        }
                    }
                },
                None => {
                    proof {
                        assert(match_ok(c, a as int, q as int, rp@[q as int], nr as int));
                        lemma_matched_entry(c, a as int, m as int, q as int, x as int);
                        assert(v_lo + lo == run_lo(c.np, c.r0 + x));
                        assert(v_lo + hi == run_hi(c.np, c.r0 + x));
                        assert(run_mass(c.np, c.r0 + x) > i128::MAX as int);
                        assert(big(c, row_at(c, a + q)));
                    }
                    return Err(());
                },
            }
        }
        x = x + 1;
    }
    Ok((ss, ms))
}

// ------------------------------------------------------------------------------------------------ pass 3

/// Pass 3: the entries of the range in position order.
pub fn pass_collect(ni: &NumIn, si: &SubIn, p1: i64, a: usize, m: usize, rp: &Vec<u64>, dest: &Vec<u64>,
    ss: &Vec<i128>, ms: &Vec<u128>, Ghost(c): Ghost<ScanCtx>) -> (r: Result<Vec<Filing>, ()>)
    requires
        inputs_ok(c, *ni, *si, p1), range_ok(c, a as int, m as int),
        rp@.len() == m, dest@.len() == ni.nr, ss@.len() == m, ms@.len() == m,
        forall|q: int| 0 <= q < m ==> #[trigger] match_ok(c, a as int, q, rp@[q], ni.nr as int),
        forall|q: int| 0 <= q < m && rp@[q] < ni.nr && #[trigger] dest@[rp@[q] as int] == q
            ==> sums_ok(c, rp@[q] as int, ss@[q], ms@[q]),
    ensures
        r matches Ok(f) ==> f@ == filt(c, a as int, a + m) && none_big(c, a as int, a + m),
        r is Err ==> exists|p: int| a <= p < a + m && #[trigger] big(c, row_at(c, p)),
{
    let nr = ni.nr;
    let v_lo = ni.v_lo;
    proof {
        lemma_range(c);
        lemma_permutation_facts(fy_order(c.sp), n_sub(c) as nat);
        assert(filt(c, a as int, a as int) =~= Seq::<Filing>::empty());
    }
    let mut out: Vec<Filing> = Vec::with_capacity(m);
    let mut q: usize = 0;
    while q < m
        invariant
            inputs_ok(c, *ni, *si, p1), range_ok(c, a as int, m as int),
            nr == ni.nr, v_lo == ni.v_lo, q <= m,
            0 <= c.r0 <= c.r1 <= run_count(c.np),
            fy_order(c.sp).len() == n_sub(c),
            rp@.len() == m, dest@.len() == nr, ss@.len() == m, ms@.len() == m,
            forall|i: int| 0 <= i < m ==> #[trigger] match_ok(c, a as int, i, rp@[i], nr as int),
            forall|i: int| 0 <= i < m && rp@[i] < nr && #[trigger] dest@[rp@[i] as int] == i
                ==> sums_ok(c, rp@[i] as int, ss@[i], ms@[i]),
            out@ == filt(c, a as int, a + q),
            none_big(c, a as int, a + q),
        decreases m - q,
    {
        let x = rp[q] as usize;
        proof {
            lemma_filt_step(c, a as int, a + q);
            lemma_row_fy(c, a as int, m as int, q as int);
            assert(match_ok(c, a as int, q as int, rp@[q as int], nr as int));
        }
        let j = si.fy_order[a + q] as usize;
        proof { assert(row_at(c, a + q) == j); }
        if x < nr {
            proof { lemma_matched_entry(c, a as int, m as int, q as int, x as int); }
            let (s, mm) = if dest[x] == q as u64 {
                (ss[q], ms[q])
            } else {
                proof { lemma_run_slots(c, *ni, x as int); }
                let lo = (ni.run_start[x] - v_lo) as usize;
                let hi = (ni.run_start[x + 1] - v_lo) as usize;
                match sum_range(ni.values, lo, hi, Ghost(c.np), Ghost(v_lo as int)) {
                    Some((s, mm)) => {
                        proof {
                            assert(v_lo + lo == run_lo(c.np, c.r0 + x));
                            assert(v_lo + hi == run_hi(c.np, c.r0 + x));
                            lemma_rsum_abs(run_lo(c.np, c.r0 + x), run_hi(c.np, c.r0 + x), val_term(c.np),
                                abs_term_at(c.np));
                        }
                        (s, mm)
                    },
                    None => {
                        proof {
                            assert(v_lo + lo == run_lo(c.np, c.r0 + x));
                            assert(v_lo + hi == run_hi(c.np, c.r0 + x));
                            assert(big(c, row_at(c, a + q)));
                        }
                        return Err(());
                    },
                }
            };
            proof { assert(sums_ok(c, x as int, s, mm)); }
            let f = Filing { cik: (si.cik[j] as i64 + 0x8000_0000) as u64, name: si.name_codes[j], sum: s, mass: mm };
            assert(f == entry(c, j as int));
            out.push(f);
        }
        proof {
            assert forall|p: int| a <= p < a + q + 1 implies !#[trigger] big(c, row_at(c, p)) by {
                if p < a + q {
                    assert(!big(c, row_at(c, p)));
                }
            }
        }
        q = q + 1;
    }
    Ok(out)
}

// ------------------------------------------------------------------------------------------------ the scan

/// The serial scan of positions `[a, a + m)` (all with `fy = $2`'s sort word).
pub fn scan_serial(ni: &NumIn, si: &SubIn, p1: i64, a: usize, m: usize, map: &Vec<u64>, Ghost(c): Ghost<ScanCtx>)
    -> (r: Result<Vec<Filing>, ()>)
    requires
        inputs_ok(c, *ni, *si, p1), range_ok(c, a as int, m as int), run_map_ok(c, map@),
    ensures
        r matches Ok(f) ==> f@ == filt(c, a as int, a + m) && none_big(c, a as int, a + m),
        r is Err ==> exists|p: int| a <= p < a + m && #[trigger] big(c, row_at(c, p)),
{
    let (rp, dest) = pass_match(ni, si, p1, a, m, map, Ghost(c));
    let (ss, ms) = match pass_sums(ni, si, p1, a, m, &rp, &dest, Ghost(c)) {
        Ok(x) => x,
        Err(_) => return Err(()),
    };
    pass_collect(ni, si, p1, a, m, &rp, &dest, &ss, &ms, Ghost(c))
}

} // verus!
