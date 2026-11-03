//! The filings: sub rows whose sic is not NULL and inside `[$3, $4]`, sorted by (sic, cik) (`select_filings`), and
//! for each filing its num run of unit `$1`, its pre adsh code and its number of pre rows in sub-runs of stmt `$2`
//! (`LookTask`, in parallel chunks).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::{Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;

use crate::stores::num::interface as N;
use crate::stores::pre::interface as P;
use crate::stores::num::interface::common::text::{text_entry, text_parts_wf, text_strictly_sorted, find_text, text_entry_of,
    u64_part, u8_part, lemma_dict_codes};
use crate::agent::common::sort::*;
use crate::agent::common::sums::*;
use crate::agent::common::dictmap::NONE;
use crate::agent::maps::{Dict, dict_wf, dentry};
use crate::agent::levels::{run_found, uom_entry, gq, pre_u64s, padsh_entry};

verus! {

// ------------------------------------------------------------------------------------------------ selection

/// Sort key of a filing: (sic, cik) lexicographically.
pub open spec fn fkey(sic: i32, cik: i32) -> int { sic as int * 0x1_0000_0000 + (cik as int + 0x8000_0000) }

/// Sub row `i` qualifies: sic not NULL and inside `[lo, hi]`.
pub open spec fn squal(ssic: Seq<i32>, ssicv: Seq<u8>, lo: int, hi: int, i: int) -> bool {
    ssicv[i] != 0 && lo <= ssic[i] as int <= hi
}

pub open spec fn payloads(s: Seq<(i128, u64)>) -> Seq<u64> { s.map_values(|p: (i128, u64)| p.1) }

/// The qualifying sub rows with their keys, sorted by key.
pub fn select_filings(scik: &[i32], ssic: &[i32], ssicv: &[u8], n: usize, lo: i64, hi: i64) -> (r: Vec<(i128, u64)>)
    requires scik@.len() == n, ssic@.len() == n, ssicv@.len() == n,
    ensures
        sorted_k(r@),
        payloads(r@).no_duplicates(),
        forall|i: u64| #[trigger] payloads(r@).contains(i) <==> (i < n && squal(ssic@, ssicv@, lo as int, hi as int, i as int)),
        forall|k: int| 0 <= k < r@.len() ==> (#[trigger] r@[k]).1 < n
            && r@[k].0 == fkey(ssic@[r@[k].1 as int], scik@[r@[k].1 as int]),
{
    let mut orig: Vec<(i128, u64)> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n, scik@.len() == n, ssic@.len() == n, ssicv@.len() == n,
            forall|k: int| 0 <= k < orig@.len() ==> (#[trigger] orig@[k]).1 < i
                && orig@[k].0 == fkey(ssic@[orig@[k].1 as int], scik@[orig@[k].1 as int])
                && squal(ssic@, ssicv@, lo as int, hi as int, orig@[k].1 as int),
            forall|a: int, b: int| 0 <= a < b < orig@.len() ==> (#[trigger] orig@[a]).1 < (#[trigger] orig@[b]).1,
            forall|j: int| 0 <= j < i && squal(ssic@, ssicv@, lo as int, hi as int, j) ==>
                exists|k: int| 0 <= k < orig@.len() && #[trigger] orig@[k].1 == j as u64,
        decreases n - i,
    {
        if ssicv[i] != 0 && lo <= ssic[i] as i64 && ssic[i] as i64 <= hi {
            let key: i128 = (ssic[i] as i128) * 0x1_0000_0000i128 + (scik[i] as i128 + 0x8000_0000i128);
            let ghost old_o = orig@;
            orig.push((key, i as u64));
            proof {
                assert forall|k: int| 0 <= k < old_o.len() implies orig@[k] == old_o[k] by {}
                assert forall|j: int| 0 <= j < i + 1 && squal(ssic@, ssicv@, lo as int, hi as int, j) implies
                    exists|k: int| 0 <= k < orig@.len() && #[trigger] orig@[k].1 == j as u64 by {
                    if j == i {
                        assert(orig@[orig@.len() - 1].1 == j as u64);
                    } else {
                        let k = choose|k: int| 0 <= k < old_o.len() && #[trigger] old_o[k].1 == j as u64;
                        assert(orig@[k].1 == j as u64);
                    }
                }
            }
        }
        i = i + 1;
    }
    let r = merge_sort(&orig);
    proof {
        let po = payloads(orig@);
        let pr = payloads(r@);
        assert forall|a: int, b: int| 0 <= a < po.len() && 0 <= b < po.len() && a != b implies po[a] != po[b] by {
            if a < b { assert(orig@[a].1 < orig@[b].1); } else { assert(orig@[b].1 < orig@[a].1); }
        }
        assert(po.no_duplicates());
        crate::stores::num::interface::common::perm::lemma_multiset_map(r@, orig@, |p: (i128, u64)| p.1);
        assert(pr.to_multiset() == po.to_multiset());
        po.lemma_multiset_has_no_duplicates();
        assert forall|x: u64| pr.to_multiset().contains(x) implies pr.to_multiset().count(x) == 1 by {}
        pr.lemma_multiset_has_no_duplicates_conv();
        assert forall|x: u64| #[trigger] pr.contains(x) <==> po.contains(x) by {
            pr.to_multiset_ensures();
            po.to_multiset_ensures();
            vstd::seq_lib::lemma_seq_contains_after_push::<u64>(pr, 0, x);
            if pr.contains(x) { assert(pr.to_multiset().count(x) > 0); }
            if po.contains(x) { assert(po.to_multiset().count(x) > 0); }
            assert(pr.to_multiset().contains(x) <==> pr.contains(x));
            assert(po.to_multiset().contains(x) <==> po.contains(x));
        }
        assert forall|i: u64| #[trigger] pr.contains(i) <==> (i < n && squal(ssic@, ssicv@, lo as int, hi as int, i as int)) by {
            if po.contains(i) {
                let k = choose|k: int| 0 <= k < po.len() && po[k] == i;
                assert(orig@[k].1 == i);
            }
            if i < n && squal(ssic@, ssicv@, lo as int, hi as int, i as int) {
                let k = choose|k: int| 0 <= k < orig@.len() && #[trigger] orig@[k].1 == i as int as u64;
                assert(po[k] == i);
            }
        }
        assert forall|k: int| 0 <= k < r@.len() implies (#[trigger] r@[k]).1 < n
            && r@[k].0 == fkey(ssic@[r@[k].1 as int], scik@[r@[k].1 as int]) by {
            r@.to_multiset_ensures();
            orig@.to_multiset_ensures();
            assert(r@.contains(r@[k]));
            assert(r@.to_multiset().count(r@[k]) > 0);
            assert(orig@.to_multiset().count(r@[k]) > 0);
            assert(orig@.contains(r@[k]));
            let m = choose|m: int| 0 <= m < orig@.len() && orig@[m] == r@[k];
            assert(orig@[m] == r@[k]);
        }
    }
    r
}

// ------------------------------------------------------------------------------------------------ binary search

/// First position of `[lo, hi)` whose value is not below `key` (values nondecreasing there).
pub fn lower_u64(v: &[u64], lo: usize, hi: usize, key: u64) -> (r: usize)
    requires lo <= hi <= v@.len(), forall|a: int, b: int| lo <= a < b < hi ==> #[trigger] v@[a] <= #[trigger] v@[b],
    ensures
        lo <= r <= hi,
        forall|k: int| lo <= k < r ==> #[trigger] v@[k] < key,
        forall|k: int| r <= k < hi ==> #[trigger] v@[k] >= key,
    no_unwind
{
    let mut a = lo;
    let mut b = hi;
    while a < b
        invariant
            lo <= a <= b <= hi <= v@.len(),
            forall|x: int, y: int| lo <= x < y < hi ==> #[trigger] v@[x] <= #[trigger] v@[y],
            forall|k: int| lo <= k < a ==> #[trigger] v@[k] < key,
            forall|k: int| b <= k < hi ==> #[trigger] v@[k] >= key,
        decreases b - a,
    {
        let m = a + (b - a) / 2;
        if v[m] < key {
            proof { assert forall|k: int| lo <= k <= m implies #[trigger] v@[k] < key by { if k < m { assert(v@[k] <= v@[m as int]); } } }
            a = m + 1;
        } else {
            proof { assert forall|k: int| m <= k < hi implies #[trigger] v@[k] >= key by { if k > m { assert(v@[m as int] <= v@[k]); } } }
            b = m;
        }
    }
    a
}

/// `lower_u64` from a guess `h` of the answer: exponential probes away from `h` (forward when `v[h]` is below
/// `key`, else backward) bracket the answer, then a binary search of the bracket. A good guess touches a few
/// neighbouring cache lines instead of the whole binary search path.
pub fn lower_u64_from(v: &[u64], lo: usize, hi: usize, key: u64, h: usize) -> (r: usize)
    requires lo <= hi <= v@.len(), forall|a: int, b: int| lo <= a < b < hi ==> #[trigger] v@[a] <= #[trigger] v@[b],
    ensures
        lo <= r <= hi,
        forall|k: int| lo <= k < r ==> #[trigger] v@[k] < key,
        forall|k: int| r <= k < hi ==> #[trigger] v@[k] >= key,
    no_unwind
{
    if h < lo || h >= hi {
        return lower_u64(v, lo, hi, key);
    }
    let mut a: usize;
    let mut b: usize;
    let mut step: usize = 1;
    let mut done = false;
    if v[h] < key {
        proof { assert forall|k: int| lo <= k <= h implies #[trigger] v@[k] < key by { if k < h { assert(v@[k] <= v@[h as int]); } } }
        a = h + 1;
        b = hi;
        while !done && a < b
            invariant
                lo <= a <= b <= hi <= v@.len(), step >= 1,
                forall|x: int, y: int| lo <= x < y < hi ==> #[trigger] v@[x] <= #[trigger] v@[y],
                forall|k: int| lo <= k < a ==> #[trigger] v@[k] < key,
                forall|k: int| b <= k < hi ==> #[trigger] v@[k] >= key,
            decreases b - a,
        {
            let p = if b - a > step { a + step - 1 } else { b - 1 };
            if v[p] < key {
                proof { assert forall|k: int| lo <= k <= p implies #[trigger] v@[k] < key by { if k < p { assert(v@[k] <= v@[p as int]); } } }
                a = p + 1;
                if step < 0x4000_0000 { step = step * 2; }
            } else {
                proof { assert forall|k: int| p <= k < hi implies #[trigger] v@[k] >= key by { if k > p { assert(v@[p as int] <= v@[k]); } } }
                b = p;
                done = true;
            }
        }
    } else {
        proof { assert forall|k: int| h <= k < hi implies #[trigger] v@[k] >= key by { if k > h { assert(v@[h as int] <= v@[k]); } } }
        a = lo;
        b = h;
        while !done && a < b
            invariant
                lo <= a <= b <= hi <= v@.len(), step >= 1,
                forall|x: int, y: int| lo <= x < y < hi ==> #[trigger] v@[x] <= #[trigger] v@[y],
                forall|k: int| lo <= k < a ==> #[trigger] v@[k] < key,
                forall|k: int| b <= k < hi ==> #[trigger] v@[k] >= key,
            decreases b - a,
        {
            let p = if b - a > step { b - step } else { a };
            if v[p] >= key {
                proof { assert forall|k: int| p <= k < hi implies #[trigger] v@[k] >= key by { if k > p { assert(v@[p as int] <= v@[k]); } } }
                b = p;
                if step < 0x4000_0000 { step = step * 2; }
            } else {
                proof { assert forall|k: int| lo <= k <= p implies #[trigger] v@[k] < key by { if k < p { assert(v@[k] <= v@[p as int]); } } }
                a = p + 1;
                done = true;
            }
        }
    }
    let r = lower_u64(v, a, b, key);
    r
}

/// First position of `[lo, hi)` whose value is above `key` (values nondecreasing there).
pub fn upper_u64(v: &[u64], lo: usize, hi: usize, key: u64) -> (r: usize)
    requires lo <= hi <= v@.len(), forall|a: int, b: int| lo <= a < b < hi ==> #[trigger] v@[a] <= #[trigger] v@[b],
    ensures
        lo <= r <= hi,
        forall|k: int| lo <= k < r ==> #[trigger] v@[k] <= key,
        forall|k: int| r <= k < hi ==> #[trigger] v@[k] > key,
    no_unwind
{
    let mut a = lo;
    let mut b = hi;
    while a < b
        invariant
            lo <= a <= b <= hi <= v@.len(),
            forall|x: int, y: int| lo <= x < y < hi ==> #[trigger] v@[x] <= #[trigger] v@[y],
            forall|k: int| lo <= k < a ==> #[trigger] v@[k] <= key,
            forall|k: int| b <= k < hi ==> #[trigger] v@[k] > key,
        decreases b - a,
    {
        let m = a + (b - a) / 2;
        if v[m] <= key {
            proof { assert forall|k: int| lo <= k <= m implies #[trigger] v@[k] <= key by { if k < m { assert(v@[k] <= v@[m as int]); } } }
            a = m + 1;
        } else {
            proof { assert forall|k: int| m <= k < hi implies #[trigger] v@[k] > key by { if k > m { assert(v@[m as int] <= v@[k]); } } }
            b = m;
        }
    }
    a
}

// ------------------------------------------------------------------------------------------------ lookups

/// Pre rows of sub-run `s` when its group has stmt `$2`.
pub open spec fn qterm(pre: Seq<PartView>, sc: int) -> spec_fn(int) -> int {
    |s: int| if gq(pre, sc, pre_u64s(pre, P::P_SUB_GROUP)[s] as int) {
        pre_u64s(pre, P::P_SUB_START)[s + 1] - pre_u64s(pre, P::P_SUB_START)[s]
    } else { 0 }
}

/// Qualifying pre rows of pre adsh code `pc`.
pub open spec fn qn_spec(pre: Seq<PartView>, sc: int, pc: int) -> int {
    rsum(pre_u64s(pre, P::P_ADSH_SUBS)[pc] as int, pre_u64s(pre, P::P_ADSH_SUBS)[pc + 1] as int, qterm(pre, sc))
}

/// The lookups of a filing with adsh `a`: run (or `NONE`), pre adsh code (or `NONE`), qualifying pre rows.
pub open spec fn lk_ok(num: Seq<PartView>, pre: Seq<PartView>, b0: Seq<u8>, u: int, sc: int, a: Seq<u8>, lk: (u64, u64, u64)) -> bool {
    let (run, pc, qn) = lk;
    &&& run_found(num, b0, a, u, crate::agent::mapfacts::tvi(run))
    &&& run == NONE ==> pc == NONE
    &&& run != NONE ==> (pc != NONE ==> pc < P::adsh_count(pre) && padsh_entry(pre, pc as int) == a)
    &&& run != NONE ==> (pc == NONE ==> forall|k: int| 0 <= k < P::adsh_count(pre) ==> #[trigger] padsh_entry(pre, k) != a)
    &&& qn == (if run != NONE && pc != NONE { qn_spec(pre, sc, pc as int) } else { 0 })
    &&& qn <= P::row_count(pre)
}

/// The uom code facts and its run range.
pub open spec fn uom_ok(num: Seq<PartView>, b0: Seq<u8>, u: int, r0: int, r1: int) -> bool {
    &&& u >= 0 ==> u < N::uom_count(num) && uom_entry(num, u) == b0
            && r0 == N::u64s(num, N::P_UOM_RUNS)[u] && r1 == N::u64s(num, N::P_UOM_RUNS)[u + 1]
    &&& u < 0 ==> r0 == 0 && r1 == 0 && forall|k: int| 0 <= k < N::uom_count(num) ==> #[trigger] uom_entry(num, k) != b0
}

/// The fixed inputs of the lookup tasks.
#[derive(Clone)]
pub struct LookIn {
    pub fil: Arc<Vec<u64>>,
    pub sadsh_off: &'static [u64],
    pub sadsh_bytes: &'static [u8],
    pub srank: &'static [u64],
    pub sn: usize,
    pub nadsh: Dict,
    pub run_adsh: &'static [u64],
    pub r0: usize,
    pub r1: usize,
    pub padsh: Dict,
    pub adsh_subs: &'static [u64],
    pub sub_group: &'static [u64],
    pub sub_start: &'static [u64],
    pub ns: usize,
    pub gqv: Arc<Vec<bool>>,
    pub num: Ghost<Seq<PartView>>,
    pub pre: Ghost<Seq<PartView>>,
    pub b0: Ghost<Seq<u8>>,
    pub u: Ghost<int>,
    pub sc: Ghost<int>,
}

#[verifier::opaque]
pub open spec fn look_in_ok(li: LookIn) -> bool {
    let (num, pre) = (li.num@, li.pre@);
    &&& forall|k: int| 0 <= k < li.fil@.len() ==> #[trigger] li.fil@[k] < li.sn
    &&& text_parts_wf(li.sadsh_off@, li.sadsh_bytes@, li.sn as int)
    &&& li.srank@.len() == li.sn
    &&& N::num_layout_ok(num)
    &&& li.nadsh.off@ == u64_part(num[N::P_ADSH_OFF as int]) && li.nadsh.bytes@ == u8_part(num[N::P_ADSH_OFF + 1])
    &&& li.nadsh.n == N::adsh_count(num) && dict_wf(li.nadsh)
    &&& li.run_adsh@ == N::u64s(num, N::P_RUN_ADSH)
    &&& uom_ok(num, li.b0@, li.u@, li.r0 as int, li.r1 as int)
    &&& P::pre_layout_ok(pre)
    &&& li.padsh.off@ == u64_part(pre[P::P_ADSH_OFF as int]) && li.padsh.bytes@ == u8_part(pre[P::P_ADSH_OFF + 1])
    &&& li.padsh.n == P::adsh_count(pre) && dict_wf(li.padsh)
    &&& li.adsh_subs@ == pre_u64s(pre, P::P_ADSH_SUBS) && li.sub_group@ == pre_u64s(pre, P::P_SUB_GROUP)
    &&& li.sub_start@ == pre_u64s(pre, P::P_SUB_START)
    &&& li.ns == P::sub_count(pre)
    &&& li.gqv@.len() == P::group_count(pre)
    &&& forall|g: int| 0 <= g < P::group_count(pre) ==> #[trigger] li.gqv@[g] == gq(pre, li.sc@, g)
}

/// Two lookup inputs with the same contents.
pub open spec fn li_eq(a: LookIn, b: LookIn) -> bool {
    &&& a.fil@ == b.fil@ && a.sadsh_off == b.sadsh_off && a.sadsh_bytes == b.sadsh_bytes && a.srank == b.srank && a.sn == b.sn
    &&& a.nadsh == b.nadsh && a.run_adsh == b.run_adsh && a.r0 == b.r0 && a.r1 == b.r1
    &&& a.padsh == b.padsh && a.adsh_subs == b.adsh_subs && a.sub_group == b.sub_group && a.sub_start == b.sub_start
    &&& a.ns == b.ns && a.gqv@ == b.gqv@
    &&& a.num == b.num && a.pre == b.pre && a.b0 == b.b0 && a.u == b.u && a.sc == b.sc
}

pub fn clone_li(li: &LookIn) -> (r: LookIn)
    ensures li_eq(r, *li), look_in_ok(*li) ==> look_in_ok(r),
{
    proof { reveal(look_in_ok); }
    LookIn {
        fil: li.fil.clone(), sadsh_off: li.sadsh_off, sadsh_bytes: li.sadsh_bytes, srank: li.srank, sn: li.sn, nadsh: li.nadsh,
        run_adsh: li.run_adsh, r0: li.r0, r1: li.r1, padsh: li.padsh, adsh_subs: li.adsh_subs, sub_group: li.sub_group,
        sub_start: li.sub_start, ns: li.ns, gqv: li.gqv.clone(), num: li.num, pre: li.pre, b0: li.b0, u: li.u, sc: li.sc,
    }
}

/// The filing's adsh.
pub open spec fn fadsh(li: LookIn, f: int) -> Seq<u8> { text_entry(li.sadsh_off@, li.sadsh_bytes@, li.fil@[f] as int) }

/// One filing's lookups.
pub fn lookup(li: &LookIn, f: usize) -> (lk: (u64, u64, u64))
    requires look_in_ok(*li), f < li.fil@.len(),
    ensures lk_ok(li.num@, li.pre@, li.b0@, li.u@, li.sc@, fadsh(*li, f as int), lk),
    no_unwind
{
    proof { reveal(look_in_ok); }
    let ghost (num, pre) = (li.num@, li.pre@);
    let fil: &Vec<u64> = &*li.fil;
    let srow = fil[f] as usize;
    let (a, an) = text_entry_of(li.sadsh_off, li.sadsh_bytes, li.sn, srow);
    // The row's rank in sub's adsh order: num's and pre's adsh dictionaries nearly coincide with that order.
    let h: usize = li.srank[srow] as usize;
    let ghost av = a@;
    proof {
        let nr = N::run_count(num);
        let ru = N::u64s(num, N::P_RUN_UOM);
        if li.u@ >= 0 { N::lemma_uom_runs(num, li.u@); }
    }
    // The run of (uom, adsh): the adsh code, then its position among the uom's runs (adsh codes increase there).
    let mut run: u64 = NONE;
    match crate::agent::common::dictmap::find_text_hint(li.nadsh.off, li.nadsh.bytes, li.nadsh.n, a, an, h) {
        Some(code) => {
            proof {
                let ra = N::u64s(num, N::P_RUN_ADSH);
                let ru = N::u64s(num, N::P_RUN_UOM);
                assert forall|x: int, y: int| li.r0 <= x < y < li.r1 implies #[trigger] li.run_adsh@[x] <= #[trigger] li.run_adsh@[y] by {
                    assert(ru[x] == li.u@ && ru[y] == li.u@);
                    assert(crate::stores::num::interface::common::runs::pair_lt(ru[x], ra[x], ru[y], ra[y]));
                }
                assert(li.r1 <= N::run_count(num));
            }
            // Guess: the unit's runs cover most filings, so the run's position is about its adsh code's share.
            let span = li.r1 - li.r0;
            let mut guess: usize = li.r0;
            if li.nadsh.n > 0 && span <= 0xffff_ffff && code <= 0xffff_ffff {
                let (c64, s64) = (code as u64, span as u64);
                proof {
                    assert(c64 * s64 <= 0xffff_ffff * 0xffff_ffff) by (nonlinear_arith)
                        requires c64 <= 0xffff_ffff, s64 <= 0xffff_ffff;
                }
                let x = (c64 * s64) / (li.nadsh.n as u64);
                if x < s64 {
                    guess = li.r0 + x as usize;
                }
            }
            let r = lower_u64_from(li.run_adsh, li.r0, li.r1, code as u64, guess);
            if r < li.r1 && li.run_adsh[r] == code as u64 {
                run = r as u64;
            }
            proof {
                if run == NONE {
                    // No run of this unit has the adsh code; a run of the adsh bytes would.
                    assert forall|rr: int| 0 <= rr < N::run_count(num) implies
                        !(#[trigger] N::run_uom_of(num, rr) == li.b0@ && N::run_adsh_of(num, rr) == av) by {
                        let ra = N::u64s(num, N::P_RUN_ADSH);
                        let ru = N::u64s(num, N::P_RUN_UOM);
                        if N::run_uom_of(num, rr) == li.b0@ && N::run_adsh_of(num, rr) == av {
                            assert(ru[rr] < N::uom_count(num) && ra[rr] < N::adsh_count(num));
                            if li.u@ >= 0 {
                                lemma_dict_codes(u64_part(num[N::P_UOM_OFF as int]), u8_part(num[N::P_UOM_OFF + 1]), N::uom_count(num), ru[rr] as int, li.u@);
                                assert(li.r0 <= rr < li.r1);
                            } else {
                                assert(uom_entry(num, ru[rr] as int) != li.b0@);
                            }
                            lemma_dict_codes(li.nadsh.off@, li.nadsh.bytes@, li.nadsh.n as int, ra[rr] as int, code as int);
                        }
                    }
                } else {
                    assert(li.u@ >= 0) by {
                        if li.u@ < 0 { assert(li.r0 == li.r1); }
                    }
                }
            }
        },
        None => {
            proof {
                assert forall|rr: int| 0 <= rr < N::run_count(num) implies
                    !(#[trigger] N::run_uom_of(num, rr) == li.b0@ && N::run_adsh_of(num, rr) == av) by {
                    let ra = N::u64s(num, N::P_RUN_ADSH);
                    let ru = N::u64s(num, N::P_RUN_UOM);
                    assert(ru[rr] < N::uom_count(num) && ra[rr] < N::adsh_count(num));
                }
            }
        },
    }
    let mut pc: u64 = NONE;
    let mut qn: u64 = 0;
    if run != NONE {
        match crate::agent::common::dictmap::find_text_hint(li.padsh.off, li.padsh.bytes, li.padsh.n, a, an, h) {
            Some(p) => {
                pc = p as u64;
                proof {
                    P::lemma_adsh_subs(pre, p as int);
                    assert(li.adsh_subs@[p + 1] <= li.ns);
                }
                let s0 = li.adsh_subs[p] as usize;
                let s1 = li.adsh_subs[p + 1] as usize;
                let gqv: &Vec<bool> = &*li.gqv;
                let gl = gqv.len();
                let ghost st = pre_u64s(pre, P::P_SUB_START);
                let ghost ns = P::sub_count(pre);
                proof {
                    assert(st[0] == 0 && st[ns] == P::row_count(pre));
                }
                let mut s = s0;
                while s < s1
                    invariant
                        look_in_ok(*li), pc == p, p < P::adsh_count(pre), gqv@ == li.gqv@, num == li.num@, pre == li.pre@,
                        gl == gqv@.len(),
                        s0 == pre_u64s(pre, P::P_ADSH_SUBS)[p as int], s1 == pre_u64s(pre, P::P_ADSH_SUBS)[p + 1],
                        s0 <= s <= s1 <= ns, st == pre_u64s(pre, P::P_SUB_START), st[0] == 0, st[ns] == P::row_count(pre),
                        qn == rsum(s0 as int, s as int, qterm(pre, li.sc@)),
                        qn <= st[s as int] - st[s0 as int],
                    decreases s1 - s,
                {
                    proof {
                        reveal(look_in_ok);
                        assert(pre_u64s(pre, P::P_SUB_ADSH)[s as int] < P::adsh_count(pre) && li.sub_group@[s as int] < P::group_count(pre));
                        assert(li.sub_group@[s as int] < gl);
                    }
                    let g = li.sub_group[s] as usize;
                    proof {
                        assert(g < P::group_count(pre));
                        assert(st[s as int] < st[s + 1]);
                        if s0 < s { assert(st[s0 as int] < st[s as int]); }
                    }
                    let ghost qn0 = qn;
                    proof { reveal(look_in_ok); }
                    if gqv[g] {
                        let d = li.sub_start[s + 1] - li.sub_start[s];
                        qn = qn + d;
                    }
                    proof {
                        assert(rsum(s0 as int, s + 1, qterm(pre, li.sc@)) == rsum(s0 as int, s as int, qterm(pre, li.sc@)) + qterm(pre, li.sc@)(s as int));
                        assert(gqv@[g as int] == gq(pre, li.sc@, g as int));
                        assert(g as int == pre_u64s(pre, P::P_SUB_GROUP)[s as int] as int);
                        assert(qterm(pre, li.sc@)(s as int) == if gq(pre, li.sc@, g as int) { st[s + 1] - st[s as int] } else { 0 });
                        assert(qn == qn0 + qterm(pre, li.sc@)(s as int));
                    }
                    s = s + 1;
                }
                proof {
                    if s1 < ns { assert(st[s1 as int] < st[ns]); }
                }
            },
            None => {},
        }
    }
    proof {
        if run != NONE {
            assert(run_found(num, li.b0@, av, li.u@, run as int));
            if pc != NONE {
                assert(qn == qn_spec(pre, li.sc@, pc as int));
                assert(pc < P::adsh_count(pre));
                assert(padsh_entry(pre, pc as int) == dentry(li.padsh, pc as int));
                assert(padsh_entry(pre, pc as int) == av);
            } else {
                assert forall|k: int| 0 <= k < P::adsh_count(pre) implies #[trigger] padsh_entry(pre, k) != av by {
                    assert(padsh_entry(pre, k) == dentry(li.padsh, k));
                }
            }
        } else {
            assert(run_found(num, li.b0@, av, li.u@, -1));
        }
        assert(av == fadsh(*li, f as int));
    }
    (run, pc, qn)
}

/// One chunk of filings' lookups.
pub struct LookTask {
    pub li: LookIn,
    pub f0: usize,
    pub f1: usize,
    pub out: Vec<(u64, u64, u64)>,
}

impl WorkerTask for LookTask {
    type Output = Vec<(u64, u64, u64)>;

    open spec fn pre(&self) -> bool {
        look_in_ok(self.li) && self.f0 <= self.f1 <= self.li.fil@.len() && self.out@.len() == self.f1 - self.f0
    }

    open spec fn post(&self, out: Vec<(u64, u64, u64)>) -> bool {
        &&& out@.len() == self.f1 - self.f0
        &&& forall|f: int| self.f0 <= f < self.f1 ==> lk_ok(self.li.num@, self.li.pre@, self.li.b0@, self.li.u@, self.li.sc@,
                fadsh(self.li, f), #[trigger] out@[f - self.f0])
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.f0 as u64, self.f1 as u64)
    }

    fn run(self) -> (out: Vec<(u64, u64, u64)>) {
        let LookTask { li, f0, f1, out } = self;
        let mut out = out;
        let mut f = f0;
        while f < f1
            invariant
                look_in_ok(li), f0 <= f <= f1 <= li.fil@.len(), out@.len() == f1 - f0,
                forall|g: int| f0 <= g < f ==> lk_ok(li.num@, li.pre@, li.b0@, li.u@, li.sc@, fadsh(li, g), #[trigger] out@[g - f0]),
            decreases f1 - f,
        {
            let lk = lookup(&li, f);
            out[f - f0] = lk;
            f = f + 1;
        }
        out
    }
}

/// The lookups of every filing, in parallel chunks.
pub fn lookups(dispatch: &mut Dispatch, workers: usize, li: LookIn) -> (r: Result<Vec<(u64, u64, u64)>, WorkerFailure>)
    requires look_in_ok(li), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(v) ==> v@.len() == li.fil@.len()
            && forall|f: int| 0 <= f < li.fil@.len() ==> lk_ok(li.num@, li.pre@, li.b0@, li.u@, li.sc@, fadsh(li, f), #[trigger] v@[f]),
{
    let nf = li.fil.len();
    let nt: usize = if nf < 4096 { 1 } else { workers };
    let mut tasks: Vec<LookTask> = Vec::new();
    let mut k: usize = 0;
    while k < nt
        invariant
            look_in_ok(li), nf == li.fil@.len(), 1 <= nt <= MAX_WORKERS, k <= nt,
            tasks@.len() == k,
            forall|j: int| 0 <= j < k ==> (#[trigger] tasks@[j]).pre() && li_eq(tasks@[j].li, li)
                && tasks@[j].f0 == (nf as int * j) / (nt as int) && tasks@[j].f1 == (nf as int * (j + 1)) / (nt as int),
        decreases nt - k,
    {
        proof {
            assert(nf as int * k as int <= 0xffff_ffff_ffff_ffff * 64) by (nonlinear_arith) requires nf <= 0xffff_ffff_ffff_ffff, k <= 64;
            assert(nf as int * (k + 1) as int <= 0xffff_ffff_ffff_ffff * 64) by (nonlinear_arith) requires nf <= 0xffff_ffff_ffff_ffff, k + 1 <= 64;
            assert((nf as int * k as int) / (nt as int) <= (nf as int * (k + 1) as int) / (nt as int)) by (nonlinear_arith)
                requires nt > 0, nf >= 0, k >= 0;
            assert((nf as int * (k + 1) as int) / (nt as int) <= nf) by (nonlinear_arith) requires nt > 0, nf >= 0, k + 1 <= nt;
        }
        let f0w: u128 = (nf as u128 * k as u128) / nt as u128;
        let f1w: u128 = (nf as u128 * (k + 1) as u128) / nt as u128;
        let f0 = f0w as usize;
        let f1 = f1w as usize;
        tasks.push(LookTask { li: clone_li(&li), f0, f1, out: vec![(0u64, 0u64, 0u64); f1 - f0] });
        k = k + 1;
    }
    let ghost ts = tasks@;
    let outs = match crate::agent::common::par::run_tasks(dispatch, workers, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let mut res: Vec<(u64, u64, u64)> = Vec::new();
    let mut outs = outs;
    // Concatenate in task order (popped from the back into `rev`, then forward).
    let mut rev: Vec<Vec<(u64, u64, u64)>> = Vec::new();
    let ghost os = outs@;
    while outs.len() > 0
        invariant
            outs@ == os.subrange(0, outs@.len() as int), rev@.len() + outs@.len() == os.len(),
            forall|j: int| 0 <= j < rev@.len() ==> #[trigger] rev@[j] == os[os.len() - 1 - j],
        decreases outs@.len(),
    {
        let o = outs.pop().unwrap();
        rev.push(o);
    }
    let mut k: usize = 0;
    while rev.len() > 0
        invariant
            look_in_ok(li), nf == li.fil@.len(), os.len() == nt, ts.len() == nt, rev@.len() + k == nt, k <= nt,
            forall|j: int| 0 <= j < rev@.len() ==> #[trigger] rev@[j] == os[os.len() - 1 - j],
            forall|j: int| 0 <= j < nt ==> (#[trigger] ts[j]).post(os[j]) && li_eq(ts[j].li, li)
                && ts[j].f0 == (nf as int * j) / (nt as int) && ts[j].f1 == (nf as int * (j + 1)) / (nt as int),
            res@.len() == (nf as int * k) / (nt as int),
            forall|f: int| 0 <= f < res@.len() ==> lk_ok(li.num@, li.pre@, li.b0@, li.u@, li.sc@, fadsh(li, f), #[trigger] res@[f]),
        decreases rev@.len(),
    {
        let o = rev.pop().unwrap();
        proof { assert(o == os[k as int]); assert(ts[k as int].post(o)); }
        let ghost base = res@.len();
        let mut i: usize = 0;
        let len = o.len();
        while i < len
            invariant
                len == o@.len(), i <= len, res@.len() == base + i, base == ts[k as int].f0, o@.len() == ts[k as int].f1 - ts[k as int].f0,
                ts[k as int].post(o), li_eq(ts[k as int].li, li),
                forall|f: int| 0 <= f < res@.len() ==> lk_ok(li.num@, li.pre@, li.b0@, li.u@, li.sc@, fadsh(li, f), #[trigger] res@[f]),
            decreases len - i,
        {
            proof {
                let tl = ts[k as int].li;
                assert(lk_ok(tl.num@, tl.pre@, tl.b0@, tl.u@, tl.sc@, fadsh(tl, base + i), o@[(base + i) - ts[k as int].f0]));
                assert(fadsh(tl, base + i) == fadsh(li, base + i));
            }
            res.push(o[i]);
            i = i + 1;
        }
        k = k + 1;
    }
    proof { assert((nf as int * nt as int) / (nt as int) == nf) by (nonlinear_arith) requires nt > 0; }
    Ok(res)
}

} // verus!
