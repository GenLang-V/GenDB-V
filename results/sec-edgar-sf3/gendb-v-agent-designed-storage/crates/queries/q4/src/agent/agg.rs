//! Aggregation of the contributions into groups (sic, tlabel slot), one sic block at a time. Contributions arrive
//! sorted by (sic, cik), so a sic's contributions are one contiguous block, and inside a block one slot's ciks are
//! nondecreasing: its distinct cik count is the number of cik changes. Dense per-slot arrays hold the current block;
//! at the end of a block every touched slot is emitted (when it has at least two distinct ciks) and reset.
//!
//! The spec accumulators over contributions `[b, t)` of one (sic, slot) are `acnt`, `asum`, `amass` (sums of the
//! exact fields) and `aciks` (the set of ciks), with `alast` the cik of the last one.
use vstd::prelude::*;
use crate::agent::common::sums::*;
use crate::agent::join::Contrib;
use crate::agent::cbuf::*;
use crate::spec::numeric::abs;
use crate::spec::fns::div::num_div_fits;
use crate::exec::value::EVal;
use crate::link::query::avg_of;
use crate::agent::avg::{avg_eval, lemma_avg_fits_small};
use crate::agent::common::slotmap::SlotMap;

verus! {

/// Contribution `k` has (sic, slot).
pub open spec fn km(fs: Seq<i32>, cs: Seq<Contrib>, k: int, sic: int, sl: int) -> bool {
    fs[cs[k].f as int] as int == sic && cs[k].slot as int == sl
}

pub open spec fn cnt_t(fs: Seq<i32>, cs: Seq<Contrib>, sic: int, sl: int) -> spec_fn(int) -> int {
    |k: int| if km(fs, cs, k, sic, sl) { cs[k].cnt as int } else { 0 }
}
pub open spec fn sum_t(fs: Seq<i32>, cs: Seq<Contrib>, sic: int, sl: int) -> spec_fn(int) -> int {
    |k: int| if km(fs, cs, k, sic, sl) { cs[k].sum as int } else { 0 }
}
pub open spec fn mass_t(fs: Seq<i32>, cs: Seq<Contrib>, sic: int, sl: int) -> spec_fn(int) -> int {
    |k: int| if km(fs, cs, k, sic, sl) { cs[k].mass as int } else { 0 }
}

pub open spec fn acnt(fs: Seq<i32>, cs: Seq<Contrib>, b: int, t: int, sic: int, sl: int) -> int { rsum(b, t, cnt_t(fs, cs, sic, sl)) }
pub open spec fn asum(fs: Seq<i32>, cs: Seq<Contrib>, b: int, t: int, sic: int, sl: int) -> int { rsum(b, t, sum_t(fs, cs, sic, sl)) }
pub open spec fn amass(fs: Seq<i32>, cs: Seq<Contrib>, b: int, t: int, sic: int, sl: int) -> int { rsum(b, t, mass_t(fs, cs, sic, sl)) }

/// The ciks of the contributions `[b, t)` with (sic, slot).
pub open spec fn aciks(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, b: int, t: int, sic: int, sl: int) -> Set<int>
    decreases t - b,
{
    if t <= b {
        Set::empty()
    } else if km(fs, cs, t - 1, sic, sl) {
        aciks(fs, fc, cs, b, t - 1, sic, sl).insert(fc[cs[t - 1].f as int] as int)
    } else {
        aciks(fs, fc, cs, b, t - 1, sic, sl)
    }
}

/// The cik of the last contribution `[b, t)` with (sic, slot), or `i64::MIN`.
pub open spec fn alast(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, b: int, t: int, sic: int, sl: int) -> int
    decreases t - b,
{
    if t <= b {
        i64::MIN as int
    } else if km(fs, cs, t - 1, sic, sl) {
        fc[cs[t - 1].f as int] as int
    } else {
        alast(fs, fc, cs, b, t - 1, sic, sl)
    }
}

/// One slot's accumulators of the current block: (row count, sum, mass, distinct ciks, last cik), 64 bytes, so
/// one contribution touches one entry.
pub type SlotAcc = (u128, i128, u128, u64, i64);

/// The accumulators of a slot that no contribution of the block touched.
pub open spec fn empty_acc() -> SlotAcc { (0u128, 0i128, 0u128, 0u64, i64::MIN) }

/// The per-slot accumulators of the current block (a sparse-set map over the slots, so only the touched slots cost
/// memory) and the slots it touched.
pub struct Agg {
    pub s: SlotMap<SlotAcc>,
    pub touched: Vec<u64>,
}

/// The map's invariant, with untouched slots at the empty accumulators.
pub open spec fn agg_wf(a: Agg) -> bool {
    a.s.wf() && a.s.default_value() == empty_acc()
}

impl Agg {
    pub open spec fn cnt(self) -> Seq<u128> { Seq::new(self.s.view().len(), |i: int| self.s.view()[i].0) }
    pub open spec fn sum(self) -> Seq<i128> { Seq::new(self.s.view().len(), |i: int| self.s.view()[i].1) }
    pub open spec fn mass(self) -> Seq<u128> { Seq::new(self.s.view().len(), |i: int| self.s.view()[i].2) }
    pub open spec fn dcnt(self) -> Seq<u64> { Seq::new(self.s.view().len(), |i: int| self.s.view()[i].3) }
    pub open spec fn last(self) -> Seq<i64> { Seq::new(self.s.view().len(), |i: int| self.s.view()[i].4) }
}

/// Writing slot `sl` updates each accumulator sequence at `sl`.
proof fn lemma_set_slot(oa: Agg, a: Agg, sl: int, x: SlotAcc)
    requires 0 <= sl < oa.s.view().len(), a.s.view() == oa.s.view().update(sl, x),
    ensures
        a.cnt() == oa.cnt().update(sl, x.0), a.sum() == oa.sum().update(sl, x.1), a.mass() == oa.mass().update(sl, x.2),
        a.dcnt() == oa.dcnt().update(sl, x.3), a.last() == oa.last().update(sl, x.4),
{
    assert(a.cnt() =~= oa.cnt().update(sl, x.0));
    assert(a.sum() =~= oa.sum().update(sl, x.1));
    assert(a.mass() =~= oa.mass().update(sl, x.2));
    assert(a.dcnt() =~= oa.dcnt().update(sl, x.3));
    assert(a.last() =~= oa.last().update(sl, x.4));
}

/// The ordering facts of the contributions: (sic, cik) nondecreasing, every one with a positive count, valid slot
/// and filing.
pub open spec fn cs_sorted(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, ns: int) -> bool {
    &&& forall|k: int| 0 <= k < cs.len() ==> (#[trigger] cs[k]).f < fs.len() && cs[k].f < fc.len()
            && cs[k].slot < ns && cs[k].cnt > 0
    &&& forall|k1: int, k2: int| 0 <= k1 < k2 < cs.len() ==>
            fs[(#[trigger] cs[k1]).f as int] < fs[(#[trigger] cs[k2]).f as int]
            || (fs[cs[k1].f as int] == fs[cs[k2].f as int] && fc[cs[k1].f as int] <= fc[cs[k2].f as int])
}

/// The arrays hold block `[b, t)` of sic `sic`.
pub open spec fn blk_ok(a: Agg, fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, b: int, t: int, sic: int, ns: int) -> bool {
    &&& agg_wf(a)
    &&& forall|k: int| 0 <= k < cs.len() ==> (#[trigger] cs[k]).ok ==> abs(cs[k].sum as int) <= cs[k].mass as int
    &&& a.cnt().len() == ns && a.sum().len() == ns && a.mass().len() == ns && a.dcnt().len() == ns && a.last().len() == ns
    &&& 0 <= b <= t <= cs.len()
    &&& forall|k: int| b <= k < t ==> fs[(#[trigger] cs[k]).f as int] as int == sic && cs[k].ok
    &&& forall|sl: int| 0 <= sl < ns ==> {
        &&& #[trigger] a.cnt()[sl] as int == acnt(fs, cs, b, t, sic, sl)
        &&& a.sum()[sl] as int == asum(fs, cs, b, t, sic, sl)
        &&& a.mass()[sl] as int == amass(fs, cs, b, t, sic, sl)
        &&& a.mass()[sl] <= i128::MAX as u128
        &&& a.dcnt()[sl] as int == aciks(fs, fc, cs, b, t, sic, sl).len()
        &&& a.last()[sl] as int == alast(fs, fc, cs, b, t, sic, sl)
        &&& a.cnt()[sl] as int <= (t - b) * (u64::MAX as int)
        &&& a.dcnt()[sl] as int <= t - b
    }
    &&& a.touched@.no_duplicates()
    &&& forall|z: int| 0 <= z < a.touched@.len() ==> (#[trigger] a.touched@[z]) < ns && a.cnt()[a.touched@[z] as int] > 0
    &&& forall|sl: int| 0 <= sl < ns && a.cnt()[sl] > 0 ==> #[trigger] a.touched@.contains(sl as u64)
}

// ------------------------------------------------------------------------------------------------ accumulator laws

/// Some contribution of `[b, t)` has (sic, slot).
pub open spec fn ahas(fs: Seq<i32>, cs: Seq<Contrib>, b: int, t: int, sic: int, sl: int) -> bool {
    exists|k: int| b <= k < t && #[trigger] km(fs, cs, k, sic, sl)
}

/// The cik set and the last cik: inside one sic block the ciks of a slot are nondecreasing, so the last one is the
/// largest; the set has at most one element per contribution; counts and masses are nonnegative and the count is
/// positive exactly when some contribution has the key.
pub proof fn lemma_acc_props(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, ns: int, b: int, t: int, sic: int, sl: int)
    requires
        cs_sorted(fs, fc, cs, ns), 0 <= b <= t <= cs.len(),
        forall|k: int| b <= k < t ==> fs[(#[trigger] cs[k]).f as int] as int == sic,
    ensures
        aciks(fs, fc, cs, b, t, sic, sl).len() <= t - b,
        ahas(fs, cs, b, t, sic, sl) ==> aciks(fs, fc, cs, b, t, sic, sl).contains(alast(fs, fc, cs, b, t, sic, sl)),
        ahas(fs, cs, b, t, sic, sl) ==> forall|x: int| #[trigger] aciks(fs, fc, cs, b, t, sic, sl).contains(x)
            ==> x <= alast(fs, fc, cs, b, t, sic, sl),
        ahas(fs, cs, b, t, sic, sl) ==> alast(fs, fc, cs, b, t, sic, sl) >= i32::MIN as int,
        !ahas(fs, cs, b, t, sic, sl) ==> aciks(fs, fc, cs, b, t, sic, sl) == Set::<int>::empty()
            && alast(fs, fc, cs, b, t, sic, sl) == i64::MIN as int
            && asum(fs, cs, b, t, sic, sl) == 0 && amass(fs, cs, b, t, sic, sl) == 0,
        acnt(fs, cs, b, t, sic, sl) >= 0,
        amass(fs, cs, b, t, sic, sl) >= 0,
        (acnt(fs, cs, b, t, sic, sl) > 0) == ahas(fs, cs, b, t, sic, sl),
        ahas(fs, cs, b, t, sic, sl) ==> forall|k: int| b <= k < t && #[trigger] km(fs, cs, k, sic, sl)
            ==> fc[cs[k].f as int] as int <= alast(fs, fc, cs, b, t, sic, sl),
    decreases t - b,
{
    if t > b {
        lemma_acc_props(fs, fc, cs, ns, b, t - 1, sic, sl);
        let c = cs[t - 1];
        assert(cs[t - 1].cnt > 0);
        if km(fs, cs, t - 1, sic, sl) {
            let s0 = aciks(fs, fc, cs, b, t - 1, sic, sl);
            let x = fc[c.f as int] as int;
            assert(km(fs, cs, t - 1, sic, sl));
            assert(ahas(fs, cs, b, t, sic, sl));
            if ahas(fs, cs, b, t - 1, sic, sl) {
                lemma_alast_witness(fs, fc, cs, b, t - 1, sic, sl);
                let kl = choose|kk: int| b <= kk < t - 1 && #[trigger] km(fs, cs, kk, sic, sl) && fc[cs[kk].f as int] as int == alast(fs, fc, cs, b, t - 1, sic, sl);
                assert(fs[cs[kl].f as int] as int == sic && fs[cs[t - 1].f as int] as int == sic);
                assert(fc[cs[kl].f as int] <= fc[cs[t - 1].f as int]);
                assert(alast(fs, fc, cs, b, t - 1, sic, sl) <= x);
            }
            assert forall|y: int| #[trigger] s0.insert(x).contains(y) implies y <= x by {
                if s0.contains(y) {
                    assert(ahas(fs, cs, b, t - 1, sic, sl));
                }
            }
            assert forall|k: int| b <= k < t && #[trigger] km(fs, cs, k, sic, sl) implies fc[cs[k].f as int] as int <= x by {
                if k < t - 1 {
                    assert(fs[cs[k].f as int] == fs[cs[t - 1].f as int]);
                }
            }
            vstd::set::lemma_set_insert_len(s0, x);
        } else {
            if ahas(fs, cs, b, t, sic, sl) {
                let k = choose|k: int| b <= k < t && #[trigger] km(fs, cs, k, sic, sl);
                assert(k < t - 1);
            }
        }
    } else {
        assert(!ahas(fs, cs, b, t, sic, sl));
    }
}

/// The existence of a last cik when some contribution has the key.
proof fn lemma_alast_witness(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, b: int, t: int, sic: int, sl: int)
    requires ahas(fs, cs, b, t, sic, sl),
    ensures exists|kk: int| b <= kk < t && #[trigger] km(fs, cs, kk, sic, sl) && fc[cs[kk].f as int] as int == alast(fs, fc, cs, b, t, sic, sl),
    decreases t - b,
{
    if !km(fs, cs, t - 1, sic, sl) {
        let k = choose|k: int| b <= k < t && #[trigger] km(fs, cs, k, sic, sl);
        assert(ahas(fs, cs, b, t - 1, sic, sl)) by { assert(k < t - 1); }
        lemma_alast_witness(fs, fc, cs, b, t - 1, sic, sl);
    }
}

// ------------------------------------------------------------------------------------------------ one contribution

/// Adds contribution `t` (of the block's sic) to the arrays.
pub fn add_contrib(a: &mut Agg, c: &Contrib, cik: i32, Ghost(fs): Ghost<Seq<i32>>, Ghost(fc): Ghost<Seq<i32>>,
    Ghost(cs): Ghost<Seq<Contrib>>, Ghost(b): Ghost<int>, Ghost(t): Ghost<int>, Ghost(sic): Ghost<int>, Ghost(ns): Ghost<int>)
    requires
        blk_ok(*old(a), fs, fc, cs, b, t, sic, ns), cs_sorted(fs, fc, cs, ns),
        t < cs.len(), cs[t] == *c, fs[c.f as int] as int == sic, fc[c.f as int] == cik, c.ok,
        cs.len() <= u64::MAX,
        old(a).mass()[c.slot as int] + c.mass <= i128::MAX as int,
        abs(c.sum as int) <= c.mass as int,
    ensures blk_ok(*final(a), fs, fc, cs, b, t + 1, sic, ns),
{
    let nl = a.s.len();
    proof { assert(c.slot < ns); assert(c.slot < nl); }
    let sl = c.slot as usize;
    proof {
        assert(sl as int == c.slot as int);
        lemma_acc_props(fs, fc, cs, ns, b, t, sic, sl as int);
        assert(km(fs, cs, t, sic, sl as int));
        assert(cnt_t(fs, cs, sic, sl as int)(t) == c.cnt as int);
        assert(a.cnt()[sl as int] as int == acnt(fs, cs, b, t, sic, sl as int));
        assert(abs(a.sum()[sl as int] as int) <= a.mass()[sl as int] as int) by {
            lemma_abs_sum_le_mass(fs, cs, b, t, sic, sl as int);
        }
    }
    let ghost oa = *a;
    let ghost old_a_cnt = a.cnt();
    let ghost old_t = a.touched@;
    let (oc, osum, om, od, ol) = a.s.get(sl);
    if oc == 0 {
        proof { assert(!old_t.contains(sl as u64)); }
        a.touched.push(c.slot);
    }
    proof { assert(a.touched@ == if old_a_cnt[sl as int] == 0 { old_t.push(c.slot) } else { old_t }); }
    let nc = oc + c.cnt as u128;
    let nsum = osum + c.sum;
    let nm = om + c.mass;
    let (nd, nl2) = if ol != cik as i64 { (od + 1, cik as i64) } else { (od, ol) };
    let ghost ta = *a;
    a.s.set(sl, (nc, nsum, nm, nd, nl2));
    proof {
        lemma_set_slot(ta, *a, sl as int, (nc, nsum, nm, nd, nl2));
        if ol == cik as i64 {
            assert(a.dcnt() =~= oa.dcnt());
            assert(a.last() =~= oa.last());
        }
    }
    proof {
        let t1 = t + 1;
        assert forall|k: int| b <= k < t1 implies fs[(#[trigger] cs[k]).f as int] as int == sic && cs[k].ok by {}
        assert forall|s2: int| 0 <= s2 < ns implies {
            &&& #[trigger] a.cnt()[s2] as int == acnt(fs, cs, b, t1, sic, s2)
            &&& a.sum()[s2] as int == asum(fs, cs, b, t1, sic, s2)
            &&& a.mass()[s2] as int == amass(fs, cs, b, t1, sic, s2)
            &&& a.mass()[s2] <= i128::MAX as u128
            &&& a.dcnt()[s2] as int == aciks(fs, fc, cs, b, t1, sic, s2).len()
            &&& a.last()[s2] as int == alast(fs, fc, cs, b, t1, sic, s2)
            &&& a.cnt()[s2] as int <= (t1 - b) * (u64::MAX as int)
            &&& a.dcnt()[s2] as int <= t1 - b
        } by {
            lemma_step_slot(oa, *a, fs, fc, cs, ns, b, t, sic, s2, sl as int, cik);
        }
        assert forall|z: int| 0 <= z < a.touched@.len() implies (#[trigger] a.touched@[z]) < ns && a.cnt()[a.touched@[z] as int] > 0 by {
            if z < old_t.len() { assert(a.touched@[z] == old_t[z]); }
            let s3 = a.touched@[z] as int;
            lemma_step_slot(oa, *a, fs, fc, cs, ns, b, t, sic, s3, sl as int, cik);
            if s3 != sl as int { assert(old_a_cnt[s3] > 0); }
        }
        assert forall|s2: int| 0 <= s2 < ns && a.cnt()[s2] > 0 implies #[trigger] a.touched@.contains(s2 as u64) by {
            lemma_step_slot(oa, *a, fs, fc, cs, ns, b, t, sic, s2, sl as int, cik);
            if s2 != sl as int || old_a_cnt[s2] > 0 {
                assert(old_a_cnt[s2] > 0);
                assert(old_t.contains(s2 as u64));
                let z = choose|z: int| 0 <= z < old_t.len() && old_t[z] == s2 as u64;
                assert(a.touched@[z] == s2 as u64);
            } else {
                assert(a.touched@[old_t.len() as int] == s2 as u64);
            }
        }
    }
}

/// One slot after adding contribution `t` at slot `sl`.
proof fn lemma_step_slot(oa: Agg, a: Agg, fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, ns: int, b: int, t: int,
    sic: int, s2: int, sl: int, cik: i32)
    requires
        blk_ok(oa, fs, fc, cs, b, t, sic, ns), cs_sorted(fs, fc, cs, ns), 0 <= s2 < ns,
        t < cs.len(), fs[cs[t].f as int] as int == sic, fc[cs[t].f as int] == cik, cs[t].ok, sl == cs[t].slot as int,
        a.cnt() == oa.cnt().update(sl, (oa.cnt()[sl] + cs[t].cnt) as u128),
        a.sum() == oa.sum().update(sl, (oa.sum()[sl] + cs[t].sum) as i128),
        a.mass() == oa.mass().update(sl, (oa.mass()[sl] + cs[t].mass) as u128),
        oa.mass()[sl] + cs[t].mass <= i128::MAX as int, cs.len() <= u64::MAX,
        oa.last()[sl] != cik as i64 ==> a.dcnt() == oa.dcnt().update(sl, (oa.dcnt()[sl] + 1) as u64)
            && a.last() == oa.last().update(sl, cik as i64),
        oa.last()[sl] == cik as i64 ==> a.dcnt() == oa.dcnt() && a.last() == oa.last(),
    ensures
        a.cnt()[s2] as int == acnt(fs, cs, b, t + 1, sic, s2),
        a.sum()[s2] as int == asum(fs, cs, b, t + 1, sic, s2),
        a.mass()[s2] as int == amass(fs, cs, b, t + 1, sic, s2),
        a.mass()[s2] <= i128::MAX as u128,
        a.dcnt()[s2] as int == aciks(fs, fc, cs, b, t + 1, sic, s2).len(),
        a.last()[s2] as int == alast(fs, fc, cs, b, t + 1, sic, s2),
        a.cnt()[s2] as int <= (t + 1 - b) * (u64::MAX as int),
        a.dcnt()[s2] as int <= t + 1 - b,
        (a.cnt()[s2] > 0) == (s2 == sl || oa.cnt()[s2] > 0),
{
    let t1 = t + 1;
    lemma_acc_props(fs, fc, cs, ns, b, t, sic, s2);
    assert(oa.cnt()[s2] as int == acnt(fs, cs, b, t, sic, s2));
    assert(acnt(fs, cs, b, t1, sic, s2) == acnt(fs, cs, b, t, sic, s2) + cnt_t(fs, cs, sic, s2)(t));
    assert(asum(fs, cs, b, t1, sic, s2) == asum(fs, cs, b, t, sic, s2) + sum_t(fs, cs, sic, s2)(t));
    assert(amass(fs, cs, b, t1, sic, s2) == amass(fs, cs, b, t, sic, s2) + mass_t(fs, cs, sic, s2)(t));
    assert(cs[t].cnt > 0);
    assert(cs[t].cnt <= u64::MAX);
    if s2 == sl {
        assert(km(fs, cs, t, sic, s2));
        assert(oa.cnt()[s2] as int <= (t - b) * (u64::MAX as int));
        assert((t - b) * (u64::MAX as int) <= (u64::MAX as int) * (u64::MAX as int)) by (nonlinear_arith)
            requires 0 <= t - b <= u64::MAX;
        assert((u64::MAX as int) * (u64::MAX as int) + u64::MAX < u128::MAX) by (compute);
        assert(oa.cnt()[sl] + cs[t].cnt <= u128::MAX);
        lemma_abs_sum_le_mass(fs, cs, b, t, sic, s2);
        assert(oa.sum()[s2] as int == asum(fs, cs, b, t, sic, s2));
        assert(oa.mass()[s2] as int == amass(fs, cs, b, t, sic, s2));
        assert(abs(cs[t].sum as int) <= cs[t].mass as int);
        assert(i128::MIN <= oa.sum()[sl] + cs[t].sum <= i128::MAX);
        assert(alast(fs, fc, cs, b, t1, sic, s2) == cik as int);
        assert(aciks(fs, fc, cs, b, t1, sic, s2) == aciks(fs, fc, cs, b, t, sic, s2).insert(cik as int));
        if ahas(fs, cs, b, t, sic, s2) {
            lemma_alast_witness(fs, fc, cs, b, t, sic, s2);
            let kl = choose|kk: int| b <= kk < t && #[trigger] km(fs, cs, kk, sic, s2) && fc[cs[kk].f as int] as int == alast(fs, fc, cs, b, t, sic, s2);
            assert(fc[cs[kl].f as int] <= fc[cs[t].f as int]);
            if alast(fs, fc, cs, b, t, sic, s2) != cik as int {
                assert(!aciks(fs, fc, cs, b, t, sic, s2).contains(cik as int));
            } else {
                assert(aciks(fs, fc, cs, b, t, sic, s2).contains(cik as int));
            }
        }
        vstd::set::lemma_set_insert_len(aciks(fs, fc, cs, b, t, sic, s2), cik as int);
        assert(i64::MIN as int != cik as int);
        assert(oa.last()[s2] as int == alast(fs, fc, cs, b, t, sic, s2));
        assert((t1 - b) * (u64::MAX as int) == (t - b) * (u64::MAX as int) + u64::MAX as int) by (nonlinear_arith) requires t1 == t + 1;
    } else {
        assert(!km(fs, cs, t, sic, s2));
        assert((t1 - b) * (u64::MAX as int) >= (t - b) * (u64::MAX as int)) by (nonlinear_arith) requires t1 > t;
    }
}

/// `|sum| <= mass` for a block's slot (every contribution's sum is bounded by its mass).
pub proof fn lemma_abs_sum_le_mass(fs: Seq<i32>, cs: Seq<Contrib>, b: int, t: int, sic: int, sl: int)
    requires forall|k: int| b <= k < t ==> (#[trigger] cs[k]).ok ==> abs(cs[k].sum as int) <= cs[k].mass as int,
        forall|k: int| b <= k < t ==> (#[trigger] cs[k]).ok,
    ensures abs(asum(fs, cs, b, t, sic, sl)) <= amass(fs, cs, b, t, sic, sl),
    decreases t - b,
{
    if t > b {
        lemma_abs_sum_le_mass(fs, cs, b, t - 1, sic, sl);
        assert(cs[t - 1].ok);
    }
}

// ------------------------------------------------------------------------------------------------ windows

/// No contribution of `[lo, hi)` has (sic, slot) outside `[b, e)`: the accumulators over both are equal.
pub proof fn lemma_window(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, lo: int, b: int, e: int, hi: int, sic: int, sl: int)
    requires lo <= b <= e <= hi, forall|k: int| lo <= k < hi && !(b <= k < e) ==> !#[trigger] km(fs, cs, k, sic, sl),
    ensures
        acnt(fs, cs, lo, hi, sic, sl) == acnt(fs, cs, b, e, sic, sl),
        asum(fs, cs, lo, hi, sic, sl) == asum(fs, cs, b, e, sic, sl),
        amass(fs, cs, lo, hi, sic, sl) == amass(fs, cs, b, e, sic, sl),
        aciks(fs, fc, cs, lo, hi, sic, sl) == aciks(fs, fc, cs, b, e, sic, sl),
        ahas(fs, cs, lo, hi, sic, sl) == ahas(fs, cs, b, e, sic, sl),
{
    assert forall|k: int| lo <= k < hi && !(b <= k < e) implies #[trigger] cnt_t(fs, cs, sic, sl)(k) == 0 by { assert(!km(fs, cs, k, sic, sl)); }
    assert forall|k: int| lo <= k < hi && !(b <= k < e) implies #[trigger] sum_t(fs, cs, sic, sl)(k) == 0 by { assert(!km(fs, cs, k, sic, sl)); }
    assert forall|k: int| lo <= k < hi && !(b <= k < e) implies #[trigger] mass_t(fs, cs, sic, sl)(k) == 0 by { assert(!km(fs, cs, k, sic, sl)); }
    lemma_rsum_window(lo, b, e, hi, cnt_t(fs, cs, sic, sl));
    lemma_rsum_window(lo, b, e, hi, sum_t(fs, cs, sic, sl));
    lemma_rsum_window(lo, b, e, hi, mass_t(fs, cs, sic, sl));
    lemma_aciks_tail(fs, fc, cs, lo, e, hi, sic, sl);
    lemma_aciks_head(fs, fc, cs, lo, b, e, sic, sl);
    if ahas(fs, cs, lo, hi, sic, sl) {
        let k = choose|k: int| lo <= k < hi && #[trigger] km(fs, cs, k, sic, sl);
        assert(b <= k < e);
    }
    if ahas(fs, cs, b, e, sic, sl) {
        let k = choose|k: int| b <= k < e && #[trigger] km(fs, cs, k, sic, sl);
        assert(lo <= k < hi);
    }
}

proof fn lemma_aciks_tail(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, lo: int, e: int, hi: int, sic: int, sl: int)
    requires lo <= e <= hi, forall|k: int| e <= k < hi ==> !#[trigger] km(fs, cs, k, sic, sl),
    ensures aciks(fs, fc, cs, lo, hi, sic, sl) == aciks(fs, fc, cs, lo, e, sic, sl),
    decreases hi - e,
{
    if hi > e {
        assert(!km(fs, cs, hi - 1, sic, sl));
        lemma_aciks_tail(fs, fc, cs, lo, e, hi - 1, sic, sl);
    }
}

proof fn lemma_aciks_head(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, lo: int, b: int, t: int, sic: int, sl: int)
    requires lo <= b <= t, forall|k: int| lo <= k < b ==> !#[trigger] km(fs, cs, k, sic, sl),
    ensures aciks(fs, fc, cs, lo, t, sic, sl) == aciks(fs, fc, cs, b, t, sic, sl),
    decreases t - b,
{
    if t > b {
        lemma_aciks_head(fs, fc, cs, lo, b, t - 1, sic, sl);
    } else {
        lemma_aciks_none(fs, fc, cs, lo, b, sic, sl);
    }
}

proof fn lemma_aciks_none(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, lo: int, t: int, sic: int, sl: int)
    requires forall|k: int| lo <= k < t ==> !#[trigger] km(fs, cs, k, sic, sl),
    ensures aciks(fs, fc, cs, lo, t, sic, sl) == Set::<int>::empty(),
    decreases t - lo,
{
    if t > lo {
        assert(!km(fs, cs, t - 1, sic, sl));
        lemma_aciks_none(fs, fc, cs, lo, t - 1, sic, sl);
    }
}

/// Membership in the cik set.
pub proof fn lemma_aciks_mem(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, b: int, t: int, sic: int, sl: int, x: int)
    ensures aciks(fs, fc, cs, b, t, sic, sl).contains(x)
        <==> exists|k: int| b <= k < t && #[trigger] km(fs, cs, k, sic, sl) && fc[cs[k].f as int] as int == x,
    decreases t - b,
{
    if t > b {
        lemma_aciks_mem(fs, fc, cs, b, t - 1, sic, sl, x);
        if exists|k: int| b <= k < t && #[trigger] km(fs, cs, k, sic, sl) && fc[cs[k].f as int] as int == x {
            let k = choose|k: int| b <= k < t && #[trigger] km(fs, cs, k, sic, sl) && fc[cs[k].f as int] as int == x;
            if k < t - 1 {
                assert(exists|k2: int| b <= k2 < t - 1 && #[trigger] km(fs, cs, k2, sic, sl) && fc[cs[k2].f as int] as int == x);
            }
        }
        if aciks(fs, fc, cs, b, t - 1, sic, sl).contains(x) {
            let k = choose|k: int| b <= k < t - 1 && #[trigger] km(fs, cs, k, sic, sl) && fc[cs[k].f as int] as int == x;
            assert(b <= k < t);
        }
    }
}

/// The cik set is finite with at most 2^32 (int4) elements.
pub proof fn lemma_aciks_bound(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, b: int, t: int, sic: int, sl: int)
    ensures aciks(fs, fc, cs, b, t, sic, sl).finite(), aciks(fs, fc, cs, b, t, sic, sl).len() <= 0x1_0000_0000,
{
    lemma_aciks_finite(fs, fc, cs, b, t, sic, sl);
    let a = aciks(fs, fc, cs, b, t, sic, sl);
    let r = vstd::set_lib::set_int_range(-0x8000_0000, 0x8000_0000);
    vstd::set_lib::lemma_int_range(-0x8000_0000, 0x8000_0000);
    assert forall|x: int| a.contains(x) implies r.contains(x) by {
        lemma_aciks_mem(fs, fc, cs, b, t, sic, sl, x);
        let k = choose|k: int| b <= k < t && #[trigger] km(fs, cs, k, sic, sl) && fc[cs[k].f as int] as int == x;
    }
    vstd::set_lib::lemma_len_subset(a, r);
}

proof fn lemma_aciks_finite(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, b: int, t: int, sic: int, sl: int)
    ensures aciks(fs, fc, cs, b, t, sic, sl).finite(),
    decreases t - b,
{
    if t > b { lemma_aciks_finite(fs, fc, cs, b, t - 1, sic, sl); }
}

// ------------------------------------------------------------------------------------------------ groups

/// An output group: (sic, tlabel slot) with its row count, exact sum, distinct ciks and AVG.
pub struct Grp {
    pub sic: i32,
    pub slot: u64,
    pub cnt: u128,
    pub sum: i128,
    pub dcnt: u64,
    pub avg: EVal,
}

/// A group of the contributions (every one of them ok) that fits and has at least two ciks.
pub open spec fn grp_ok(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, ns: int, g: Grp) -> bool {
    let n = cs.len() as int;
    let (s, sl) = (g.sic as int, g.slot as int);
    &&& g.slot < ns
    &&& ahas(fs, cs, 0, n, s, sl)
    &&& g.cnt as int == acnt(fs, cs, 0, n, s, sl)
    &&& g.sum as int == asum(fs, cs, 0, n, s, sl)
    &&& amass(fs, cs, 0, n, s, sl) <= i128::MAX as int
    &&& g.dcnt as int == aciks(fs, fc, cs, 0, n, s, sl).len()
    &&& g.dcnt >= 2
    &&& g.sum > i128::MIN
    &&& num_div_fits(asum(fs, cs, 0, n, s, sl), 4, acnt(fs, cs, 0, n, s, sl), 0)
    &&& g.avg@ == avg_of(asum(fs, cs, 0, n, s, sl), 4, acnt(fs, cs, 0, n, s, sl) as nat)
}

/// Key (sic, slot) is finished: when it has contributions it fits and, with two ciks, is emitted.
pub open spec fn key_done(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, gs: Seq<Grp>, s: int, sl: int) -> bool {
    let n = cs.len() as int;
    ahas(fs, cs, 0, n, s, sl) ==> {
        &&& amass(fs, cs, 0, n, s, sl) <= i128::MAX as int
        &&& num_div_fits(asum(fs, cs, 0, n, s, sl), 4, acnt(fs, cs, 0, n, s, sl), 0)
        &&& (aciks(fs, fc, cs, 0, n, s, sl).len() >= 2 ==>
                exists|i: int| 0 <= i < gs.len() && (#[trigger] gs[i]).sic as int == s && gs[i].slot as int == sl)
    }
}

pub open spec fn gkeys_distinct(gs: Seq<Grp>) -> bool {
    forall|i: int, j: int| 0 <= i < j < gs.len() ==> (#[trigger] gs[i]).sic != (#[trigger] gs[j]).sic || gs[i].slot != gs[j].slot
}

proof fn lemma_key_done_grow(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, g0: Seq<Grp>, g1: Seq<Grp>, s: int, sl: int)
    requires key_done(fs, fc, cs, g0, s, sl), g0.len() <= g1.len(), forall|i: int| 0 <= i < g0.len() ==> #[trigger] g1[i] == g0[i],
    ensures key_done(fs, fc, cs, g1, s, sl),
{
    let n = cs.len() as int;
    if ahas(fs, cs, 0, n, s, sl) && aciks(fs, fc, cs, 0, n, s, sl).len() >= 2 {
        let i = choose|i: int| 0 <= i < g0.len() && (#[trigger] g0[i]).sic as int == s && g0[i].slot as int == sl;
        assert(g1[i] == g0[i]);
    }
}

/// A capacity witness: contribution `k` is not exact (its mass leaves `i128`), or its key's contributions in the
/// block `[b, e)` (all exact, all of sic) have a mass beyond `i128` (kind 1), or (kind 2: `[b, e)` holds every
/// contribution of the sic) a mass inside `i128` and an AVG outside its domain.
pub struct Cap {
    pub k: Ghost<int>,
    pub kind: Ghost<int>,
    pub b: Ghost<int>,
    pub e: Ghost<int>,
}

pub open spec fn cap_ok(fs: Seq<i32>, cs: Seq<Contrib>, cap: Cap) -> bool {
    let n = cs.len() as int;
    let (k, b, e) = (cap.k@, cap.b@, cap.e@);
    &&& 0 <= k < n
    &&& cap.kind@ == 0 ==> !cs[k].ok
    &&& cap.kind@ != 0 ==> {
        let s = fs[cs[k].f as int] as int;
        let sl = cs[k].slot as int;
        &&& 0 <= b <= k < e <= n
        &&& forall|j: int| b <= j < e ==> fs[(#[trigger] cs[j]).f as int] as int == s && cs[j].ok
        &&& cap.kind@ == 1 ==> amass(fs, cs, b, e, s, sl) > i128::MAX as int
        &&& cap.kind@ != 1 ==> {
            &&& forall|j: int| 0 <= j < n && !(b <= j < e) ==> fs[(#[trigger] cs[j]).f as int] as int != s
            &&& amass(fs, cs, b, e, s, sl) <= i128::MAX as int
            &&& !num_div_fits(asum(fs, cs, b, e, s, sl), 4, acnt(fs, cs, b, e, s, sl), 0)
        }
    }
}

/// The arrays of no block.
pub open spec fn agg_empty(a: Agg, ns: int) -> bool {
    &&& agg_wf(a)
    &&& a.cnt().len() == ns && a.sum().len() == ns && a.mass().len() == ns && a.dcnt().len() == ns && a.last().len() == ns
    &&& a.touched@.len() == 0
    &&& forall|sl: int| 0 <= sl < ns ==> #[trigger] a.cnt()[sl] == 0 && a.sum()[sl] == 0 && a.mass()[sl] == 0
            && a.dcnt()[sl] == 0 && a.last()[sl] == i64::MIN
}

proof fn lemma_empty_blk(a: Agg, fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, e: int, s: int, ns: int)
    requires agg_empty(a, ns), 0 <= e <= cs.len(),
        forall|k: int| 0 <= k < cs.len() ==> (#[trigger] cs[k]).ok ==> abs(cs[k].sum as int) <= cs[k].mass as int,
    ensures blk_ok(a, fs, fc, cs, e, e, s, ns),
{
    assert forall|sl: int| 0 <= sl < ns implies {
        &&& #[trigger] a.cnt()[sl] as int == acnt(fs, cs, e, e, s, sl)
        &&& a.sum()[sl] as int == asum(fs, cs, e, e, s, sl)
        &&& a.mass()[sl] as int == amass(fs, cs, e, e, s, sl)
        &&& a.mass()[sl] <= i128::MAX as u128
        &&& a.dcnt()[sl] as int == aciks(fs, fc, cs, e, e, s, sl).len()
        &&& a.last()[sl] as int == alast(fs, fc, cs, e, e, s, sl)
        &&& a.cnt()[sl] as int <= (e - e) * (u64::MAX as int)
        &&& a.dcnt()[sl] as int <= e - e
    } by {
        assert(aciks(fs, fc, cs, e, e, s, sl) == Set::<int>::empty());
        assert((e - e) * (u64::MAX as int) == 0);
    }
    assert(a.touched@ =~= Seq::<u64>::empty());
}

fn new_agg(ns: usize) -> (a: Agg)
    ensures agg_empty(a, ns as int),
{
    let a = Agg { s: SlotMap::new(ns, (0u128, 0i128, 0u128, 0u64, i64::MIN)), touched: Vec::new() };
    proof {
        assert forall|sl: int| 0 <= sl < ns implies #[trigger] a.cnt()[sl] == 0 && a.sum()[sl] == 0 && a.mass()[sl] == 0
            && a.dcnt()[sl] == 0 && a.last()[sl] == i64::MIN by {
            assert(a.s.view()[sl] == (0u128, 0i128, 0u128, 0u64, i64::MIN));
        }
    }
    a
}

// ------------------------------------------------------------------------------------------------ flush

/// Slot `sl` during a flush: reset when done, else as in the block's arrays `oa`.
pub open spec fn slot_state(a: Agg, oa: Agg, done: Seq<u64>, sl: int) -> bool {
    if done.contains(sl as u64) {
        a.cnt()[sl] == 0 && a.sum()[sl] == 0 && a.mass()[sl] == 0 && a.dcnt()[sl] == 0 && a.last()[sl] == i64::MIN
    } else {
        a.cnt()[sl] == oa.cnt()[sl] && a.sum()[sl] == oa.sum()[sl] && a.mass()[sl] == oa.mass()[sl]
            && a.dcnt()[sl] == oa.dcnt()[sl] && a.last()[sl] == oa.last()[sl]
    }
}

/// Emits slot `sl` of the block `[b, e)` (arrays `oa`) and resets it.
fn flush_slot(a: &mut Agg, gs: &mut Vec<Grp>, sic: i32, sl: usize, Ghost(fs): Ghost<Seq<i32>>, Ghost(fc): Ghost<Seq<i32>>,
    Ghost(cs): Ghost<Seq<Contrib>>, Ghost(b): Ghost<int>, Ghost(e): Ghost<int>, Ghost(ns): Ghost<int>, Ghost(oa): Ghost<Agg>)
    -> (r: Result<(), Cap>)
    requires
        blk_ok(oa, fs, fc, cs, b, e, sic as int, ns), cs_sorted(fs, fc, cs, ns), cs.len() <= u64::MAX,
        forall|k: int| 0 <= k < cs.len() && !(b <= k < e) ==> fs[(#[trigger] cs[k]).f as int] != sic,
        sl < ns, oa.cnt()[sl as int] > 0,
        agg_wf(*old(a)),
        old(a).cnt().len() == ns && old(a).sum().len() == ns && old(a).mass().len() == ns && old(a).dcnt().len() == ns && old(a).last().len() == ns,
        old(a).cnt()[sl as int] == oa.cnt()[sl as int], old(a).sum()[sl as int] == oa.sum()[sl as int],
        old(a).mass()[sl as int] == oa.mass()[sl as int], old(a).dcnt()[sl as int] == oa.dcnt()[sl as int],
        forall|i: int| 0 <= i < old(gs)@.len() ==> grp_ok(fs, fc, cs, ns, #[trigger] old(gs)@[i]),
        forall|i: int| 0 <= i < old(gs)@.len() ==> !((#[trigger] old(gs)@[i]).sic == sic && old(gs)@[i].slot == sl as u64),
        gkeys_distinct(old(gs)@),
    ensures
        r is Ok ==> {
            &&& agg_wf(*final(a))
            &&& final(a).cnt() == old(a).cnt().update(sl as int, 0)
            &&& final(a).sum() == old(a).sum().update(sl as int, 0)
            &&& final(a).mass() == old(a).mass().update(sl as int, 0)
            &&& final(a).dcnt() == old(a).dcnt().update(sl as int, 0)
            &&& final(a).last() == old(a).last().update(sl as int, i64::MIN)
            &&& final(a).touched@ == old(a).touched@
            &&& old(gs)@.len() <= final(gs)@.len() <= old(gs)@.len() + 1
            &&& forall|i: int| 0 <= i < old(gs)@.len() ==> #[trigger] final(gs)@[i] == old(gs)@[i]
            &&& forall|i: int| old(gs)@.len() <= i < final(gs)@.len() ==> grp_ok(fs, fc, cs, ns, #[trigger] final(gs)@[i])
                    && final(gs)@[i].sic == sic && final(gs)@[i].slot == sl as u64
            &&& gkeys_distinct(final(gs)@)
            &&& key_done(fs, fc, cs, final(gs)@, sic as int, sl as int)
        },
        r matches Err(cap) ==> cap_ok(fs, cs, cap),
{
    let ghost n = cs.len() as int;
    let ghost sli = sl as int;
    let ghost s_ = sic as int;
    proof {
        lemma_acc_props(fs, fc, cs, ns, b, e, s_, sli);
        assert(oa.cnt()[sli] as int == acnt(fs, cs, b, e, s_, sli));
        lemma_abs_sum_le_mass(fs, cs, b, e, s_, sli);
        assert forall|k: int| 0 <= k < n && !(b <= k < e) implies !#[trigger] km(fs, cs, k, s_, sli) by {}
        lemma_window(fs, fc, cs, 0, b, e, n, s_, sli);
    }
    let (cnt, sum, _mass, dcnt, _last) = a.s.get(sl);
    if dcnt < 2 && cnt < 1_000_000_000_000u128 {
        // Not emitted (HAVING): only the AVG's domain matters, and a count below 10^12 always fits.
        proof { lemma_avg_fits_small(sum as int, cnt as int); }
    } else {
        match avg_eval(sum, cnt) {
            Err(_) => {
                proof {
                    assert(ahas(fs, cs, b, e, s_, sli));
                }
                let ghost k = choose|k: int| b <= k < e && #[trigger] km(fs, cs, k, s_, sli);
                proof { assert(fs[cs[k].f as int] as int == s_); }
                return Err(Cap { k: Ghost(k), kind: Ghost(2), b: Ghost(b), e: Ghost(e) });
            },
            Ok(v) => {
                let ghost before = gs@;
                if dcnt >= 2 {
                    gs.push(Grp { sic, slot: sl as u64, cnt, sum, dcnt, avg: v });
                    proof {
                        assert forall|i: int, j: int| 0 <= i < j < gs@.len() implies (#[trigger] gs@[i]).sic != (#[trigger] gs@[j]).sic || gs@[i].slot != gs@[j].slot by {
                            assert(gs@[i] == before[i]);
                            if j < before.len() { assert(gs@[j] == before[j]); }
                        }
                        assert(gs@[gs@.len() - 1].sic as int == s_ && gs@[gs@.len() - 1].slot as int == sli);
                    }
                }
                proof {
                    assert forall|i: int| 0 <= i < before.len() implies #[trigger] gs@[i] == before[i] by {}
                }
            },
        }
    }
    let ghost ta = *a;
    a.s.set(sl, (0u128, 0i128, 0u128, 0u64, i64::MIN));
    proof { lemma_set_slot(ta, *a, sl as int, (0u128, 0i128, 0u128, 0u64, i64::MIN)); }
    Ok(())
}

/// Emits the block `[b, e)` of sic `sic` (every contribution of that sic) and resets the arrays.
pub fn flush(a: &mut Agg, gs: &mut Vec<Grp>, sic: i32, Ghost(fs): Ghost<Seq<i32>>, Ghost(fc): Ghost<Seq<i32>>,
    Ghost(cs): Ghost<Seq<Contrib>>, Ghost(b): Ghost<int>, Ghost(e): Ghost<int>, Ghost(ns): Ghost<int>) -> (r: Result<(), Cap>)
    requires
        blk_ok(*old(a), fs, fc, cs, b, e, sic as int, ns), cs_sorted(fs, fc, cs, ns), cs.len() <= u64::MAX,
        forall|k: int| 0 <= k < cs.len() && !(b <= k < e) ==> fs[(#[trigger] cs[k]).f as int] != sic,
        forall|i: int| 0 <= i < old(gs)@.len() ==> grp_ok(fs, fc, cs, ns, #[trigger] old(gs)@[i]) && old(gs)@[i].sic < sic,
        gkeys_distinct(old(gs)@),
    ensures
        r is Ok ==> {
            &&& agg_empty(*final(a), ns)
            &&& old(gs)@.len() <= final(gs)@.len()
            &&& forall|i: int| 0 <= i < old(gs)@.len() ==> #[trigger] final(gs)@[i] == old(gs)@[i]
            &&& forall|i: int| 0 <= i < final(gs)@.len() ==> grp_ok(fs, fc, cs, ns, #[trigger] final(gs)@[i]) && final(gs)@[i].sic <= sic
            &&& gkeys_distinct(final(gs)@)
            &&& forall|sl: int| 0 <= sl < ns ==> #[trigger] key_done(fs, fc, cs, final(gs)@, sic as int, sl)
        },
        r matches Err(cap) ==> cap_ok(fs, cs, cap),
{
    let ghost oa = *a;
    let ghost g0 = gs@;
    let ghost n = cs.len() as int;
    let ghost tt = a.touched@;
    let nt = a.touched.len();
    let nl = a.s.len();
    let mut z: usize = 0;
    while z < nt
        invariant
            blk_ok(oa, fs, fc, cs, b, e, sic as int, ns), cs_sorted(fs, fc, cs, ns), cs.len() <= u64::MAX, n == cs.len(),
            forall|k: int| 0 <= k < cs.len() && !(b <= k < e) ==> fs[(#[trigger] cs[k]).f as int] != sic,
            a.touched@ == tt, tt == oa.touched@, nt == tt.len(), z <= nt, nl == ns, agg_wf(*a),
            a.cnt().len() == ns && a.sum().len() == ns && a.mass().len() == ns && a.dcnt().len() == ns && a.last().len() == ns,
            forall|sl: int| 0 <= sl < ns ==> #[trigger] slot_state(*a, oa, tt.subrange(0, z as int), sl),
            g0.len() <= gs@.len(),
            forall|i: int| 0 <= i < g0.len() ==> #[trigger] gs@[i] == g0[i],
            forall|i: int| 0 <= i < g0.len() ==> grp_ok(fs, fc, cs, ns, #[trigger] g0[i]) && g0[i].sic < sic,
            forall|i: int| g0.len() <= i < gs@.len() ==> grp_ok(fs, fc, cs, ns, #[trigger] gs@[i]) && gs@[i].sic == sic
                && tt.subrange(0, z as int).contains(gs@[i].slot),
            gkeys_distinct(gs@),
            forall|y: int| 0 <= y < z ==> #[trigger] key_done(fs, fc, cs, gs@, sic as int, tt[y] as int),
        decreases nt - z,
    {
        proof { assert(tt[z as int] < ns && oa.cnt()[tt[z as int] as int] > 0); }
        let sl = a.touched[z] as usize;
        let ghost sli = sl as int;
        let ghost before = gs@;
        let ghost ba = *a;
        proof {
            assert(sli == tt[z as int] as int);
            assert(!tt.subrange(0, z as int).contains(sl as u64)) by {
                if tt.subrange(0, z as int).contains(sl as u64) {
                    let y = choose|y: int| 0 <= y < z && #[trigger] tt.subrange(0, z as int)[y] == sl as u64;
                    assert(tt[y] == tt[z as int]);
                }
            }
            assert(slot_state(*a, oa, tt.subrange(0, z as int), sli));
            assert(a.cnt()[sli] == oa.cnt()[sli]);
            assert forall|i: int| 0 <= i < gs@.len() implies !((#[trigger] gs@[i]).sic == sic && gs@[i].slot == sl as u64) by {
                if i >= g0.len() {
                    let y = choose|y: int| 0 <= y < z && #[trigger] tt.subrange(0, z as int)[y] == gs@[i].slot;
                    assert(tt[y] == gs@[i].slot);
                } else {
                    assert(gs@[i] == g0[i]);
                }
            }
            assert forall|i: int| 0 <= i < gs@.len() implies grp_ok(fs, fc, cs, ns, #[trigger] gs@[i]) by {
                if i < g0.len() { assert(gs@[i] == g0[i]); }
            }
        }
        flush_slot(a, gs, sic, sl, Ghost(fs), Ghost(fc), Ghost(cs), Ghost(b), Ghost(e), Ghost(ns), Ghost(oa))?;
        proof {
            assert(tt.subrange(0, z as int + 1) == tt.subrange(0, z as int).push(tt[z as int]));
            assert forall|i: int| g0.len() <= i < gs@.len() implies grp_ok(fs, fc, cs, ns, #[trigger] gs@[i]) && gs@[i].sic == sic
                && tt.subrange(0, z as int + 1).contains(gs@[i].slot) by {
                if i < before.len() {
                    assert(gs@[i] == before[i]);
                    let y = choose|y: int| 0 <= y < z && #[trigger] tt.subrange(0, z as int)[y] == gs@[i].slot;
                    assert(tt.subrange(0, z as int + 1)[y] == gs@[i].slot);
                } else {
                    assert(tt.subrange(0, z as int + 1)[z as int] == gs@[i].slot);
                }
            }
            assert forall|i: int| 0 <= i < g0.len() implies #[trigger] gs@[i] == g0[i] by {
                assert(gs@[i] == before[i]);
            }
            assert forall|y: int| 0 <= y < z + 1 implies #[trigger] key_done(fs, fc, cs, gs@, sic as int, tt[y] as int) by {
                if y < z {
                    lemma_key_done_grow(fs, fc, cs, before, gs@, sic as int, tt[y] as int);
                }
            }
            assert forall|s2: int| 0 <= s2 < ns implies #[trigger] slot_state(*a, oa, tt.subrange(0, z as int + 1), s2) by {
                assert(slot_state(ba, oa, tt.subrange(0, z as int), s2));
                if s2 != sli {
                    assert(a.cnt()[s2] == ba.cnt()[s2] && a.sum()[s2] == ba.sum()[s2] && a.mass()[s2] == ba.mass()[s2]
                        && a.dcnt()[s2] == ba.dcnt()[s2] && a.last()[s2] == ba.last()[s2]);
                    if tt.subrange(0, z as int + 1).contains(s2 as u64) {
                        let y = choose|y: int| 0 <= y < z + 1 && #[trigger] tt.subrange(0, z as int + 1)[y] == s2 as u64;
                        assert(y != z as int);
                        assert(tt.subrange(0, z as int)[y] == s2 as u64);
                    }
                    if tt.subrange(0, z as int).contains(s2 as u64) {
                        let y = choose|y: int| 0 <= y < z && #[trigger] tt.subrange(0, z as int)[y] == s2 as u64;
                        assert(tt.subrange(0, z as int + 1)[y] == s2 as u64);
                    }
                } else {
                    assert(tt.subrange(0, z as int + 1)[z as int] == s2 as u64);
                }
            }
        }
        z = z + 1;
    }
    let ghost la = *a;
    proof { assert forall|sl: int| 0 <= sl < ns implies #[trigger] slot_state(la, oa, tt.subrange(0, nt as int), sl) by {} }
    a.touched.clear();
    // Every slot is back at the empty accumulators: drop the dense entries (O(1)).
    a.s.reset();
    proof {
        assert(a.s.view() =~= Seq::new(ns as nat, |_k: int| empty_acc()));
    }
    proof {
        assert(tt.subrange(0, nt as int) == tt);
        assert forall|sl: int| 0 <= sl < ns implies #[trigger] a.cnt()[sl] == 0 && a.sum()[sl] == 0 && a.mass()[sl] == 0
            && a.dcnt()[sl] == 0 && a.last()[sl] == i64::MIN by {
            assert(tt.subrange(0, nt as int).contains(sl as u64) == tt.contains(sl as u64));
            assert(slot_state(la, oa, tt.subrange(0, nt as int), sl));
            if !tt.contains(sl as u64) {
                assert(oa.cnt()[sl] as int == acnt(fs, cs, b, e, sic as int, sl));
                lemma_acc_props(fs, fc, cs, ns, b, e, sic as int, sl);
                assert(oa.cnt()[sl] == 0);
                assert(aciks(fs, fc, cs, b, e, sic as int, sl).len() == 0);
            }
        }
        assert forall|sl: int| 0 <= sl < ns implies #[trigger] key_done(fs, fc, cs, gs@, sic as int, sl) by {
            if tt.contains(sl as u64) {
                let y = choose|y: int| 0 <= y < tt.len() && tt[y] == sl as u64;
                assert(key_done(fs, fc, cs, gs@, sic as int, tt[y] as int));
            } else {
                assert(oa.cnt()[sl] as int == acnt(fs, cs, b, e, sic as int, sl));
                lemma_acc_props(fs, fc, cs, ns, b, e, sic as int, sl);
                assert forall|k: int| 0 <= k < n && !(b <= k < e) implies !#[trigger] km(fs, cs, k, sic as int, sl) by {}
                lemma_window(fs, fc, cs, 0, b, e, n, sic as int, sl);
            }
        }
        assert forall|i: int| 0 <= i < gs@.len() implies grp_ok(fs, fc, cs, ns, #[trigger] gs@[i]) && gs@[i].sic <= sic by {
            if i < g0.len() { assert(gs@[i] == g0[i]); }
        }
    }
    Ok(())
}

// ------------------------------------------------------------------------------------------------ all blocks

proof fn lemma_no_key(fs: Seq<i32>, fc: Seq<i32>, cs: Seq<Contrib>, gs: Seq<Grp>, s: int, sl: int)
    requires forall|k: int| 0 <= k < cs.len() ==> fs[(#[trigger] cs[k]).f as int] as int != s,
    ensures key_done(fs, fc, cs, gs, s, sl),
{
    if ahas(fs, cs, 0, cs.len() as int, s, sl) {
        let k = choose|k: int| 0 <= k < cs.len() && #[trigger] km(fs, cs, k, s, sl);
    }
}

/// The groups of the contributions (sorted by (sic, cik)), or a capacity witness.
/// The next contribution's place `(i, j)` in the task vectors: skips exhausted vectors.
fn next_place(bufs: &Vec<CBuf>, i: usize, j: usize, Ghost(t): Ghost<int>) -> (r: (usize, usize))
    requires
        i <= bufs@.len(), i < bufs@.len() ==> j <= bufs@[i as int].view().len(), i == bufs@.len() ==> j == 0,
        t == cflat(bufs@.take(i as int)).len() + j, t < cflat(bufs@).len(),
    ensures
        r.0 < bufs@.len(), r.1 < bufs@[r.0 as int].view().len(), t == cflat(bufs@.take(r.0 as int)).len() + r.1,
{
    let nb = bufs.len();
    let mut i = i;
    let mut j = j;
    proof {
        if i == nb { lemma_cflat_all(bufs@); }
    }
    while j >= bufs[i].len()
        invariant
            nb == bufs@.len(), i < nb, j <= bufs@[i as int].view().len(),
            t == cflat(bufs@.take(i as int)).len() + j, t < cflat(bufs@).len(),
        decreases nb - i,
    {
        proof {
            lemma_cflat_take(bufs@, i as int);
            if i + 1 == nb { lemma_cflat_all(bufs@); }
        }
        i = i + 1;
        j = 0;
    }
    (i, j)
}

pub fn aggregate(bufs: &Vec<CBuf>, fsv: &Vec<i32>, fcv: &Vec<i32>, ns: usize) -> (r: Result<Vec<Grp>, Cap>)
    requires
        cs_sorted(fsv@, fcv@, cflat(bufs@), ns as int), cflat(bufs@).len() <= usize::MAX,
        forall|k: int| 0 <= k < cflat(bufs@).len() ==> (#[trigger] cflat(bufs@)[k]).ok
            ==> abs(cflat(bufs@)[k].sum as int) <= cflat(bufs@)[k].mass as int && cflat(bufs@)[k].mass <= i128::MAX as u128,
    ensures
        r matches Ok(gs) ==> {
            &&& forall|k: int| 0 <= k < cflat(bufs@).len() ==> (#[trigger] cflat(bufs@)[k]).ok
            &&& forall|i: int| 0 <= i < gs@.len() ==> grp_ok(fsv@, fcv@, cflat(bufs@), ns as int, #[trigger] gs@[i])
            &&& gkeys_distinct(gs@)
            &&& forall|s: int, sl: int| 0 <= sl < ns ==> #[trigger] key_done(fsv@, fcv@, cflat(bufs@), gs@, s, sl)
        },
        r matches Err(cap) ==> cap_ok(fsv@, cflat(bufs@), cap),
{
    let ghost fs = fsv@;
    let ghost fc = fcv@;
    let ghost csv = cflat(bufs@);
    let ghost nsi = ns as int;
    // The number of contributions.
    let nb = bufs.len();
    let mut n: usize = 0;
    let mut i: usize = 0;
    while i < nb
        invariant nb == bufs@.len(), i <= nb, n == cflat(bufs@.take(i as int)).len(), csv == cflat(bufs@), csv.len() <= usize::MAX,
        decreases nb - i,
    {
        proof { lemma_cflat_take(bufs@, i as int); lemma_cflat_prefix(bufs@, i + 1); }
        n = n + bufs[i].len();
        i = i + 1;
    }
    proof { lemma_cflat_all(bufs@); assert(csv.len() <= u64::MAX); }
    let mut a = new_agg(ns);
    let mut gs: Vec<Grp> = Vec::new();
    let mut t: usize = 0;
    let mut b: usize = 0;
    let mut cur: i32 = 0;
    // The place of contribution `t`: vector `bi`, index `bj`.
    let mut bi: usize = 0;
    let mut bj: usize = 0;
    proof { assert(bufs@.take(0) =~= Seq::<CBuf>::empty()); }
    proof { assert forall|k: int| 0 <= k < csv.len() ==> (#[trigger] csv[k]).ok ==> abs(csv[k].sum as int) <= csv[k].mass as int by {} }
    while t < n
        invariant
            fs == fsv@, fc == fcv@, csv == cflat(bufs@), nsi == ns as int, n == csv.len(),
            bi <= bufs@.len(), bi < bufs@.len() ==> bj <= bufs@[bi as int]@.len(), bi == bufs@.len() ==> bj == 0,
            t == cflat(bufs@.take(bi as int)).len() + bj,
            cs_sorted(fs, fc, csv, nsi), csv.len() <= u64::MAX,
            forall|k: int| 0 <= k < csv.len() ==> (#[trigger] csv[k]).ok ==> abs(csv[k].sum as int) <= csv[k].mass as int
                && csv[k].mass <= i128::MAX as u128,
            t <= n, b <= t,
            t == 0 ==> agg_empty(a, nsi) && gs@.len() == 0,
            t > 0 ==> blk_ok(a, fs, fc, csv, b as int, t as int, cur as int, nsi) && b < t,
            t > 0 ==> forall|k: int| 0 <= k < b ==> fs[(#[trigger] csv[k]).f as int] < cur,
            forall|k: int| 0 <= k < t ==> (#[trigger] csv[k]).ok,
            forall|i: int| 0 <= i < gs@.len() ==> grp_ok(fs, fc, csv, nsi, #[trigger] gs@[i]) && gs@[i].sic < cur,
            gkeys_distinct(gs@),
            t > 0 ==> forall|s: int, sl: int| s < cur && 0 <= sl < nsi ==> #[trigger] key_done(fs, fc, csv, gs@, s, sl),
        decreases n - t,
    {
        let (pi, pj) = next_place(bufs, bi, bj, Ghost(t as int));
        bi = pi;
        bj = pj;
        let c = bufs[bi].get(bj);
        proof { lemma_cflat_index(bufs@, bi as int, bj as int); assert(csv[t as int] == c); assert(c.f < fs.len() && c.slot < nsi); }
        let sic = fsv[c.f];
        if t == 0 {
            b = 0;
            cur = sic;
            proof { lemma_empty_blk(a, fs, fc, csv, 0, sic as int, nsi); }
        } else if sic != cur {
            proof {
                let tp = t - 1;
                assert(fs[csv[tp].f as int] == cur);
                assert(fs[csv[tp].f as int] <= fs[csv[t as int].f as int]);
                assert forall|k: int| 0 <= k < csv.len() && !(b <= k < t) implies fs[(#[trigger] csv[k]).f as int] != cur by {
                    if k >= t {
                        if k > t { assert(fs[csv[t as int].f as int] <= fs[csv[k].f as int]); }
                    }
                }
            }
            let ghost g0 = gs@;
            let ghost oc = cur;
            let ghost ob = b;
            flush(&mut a, &mut gs, cur, Ghost(fs), Ghost(fc), Ghost(csv), Ghost(b as int), Ghost(t as int), Ghost(nsi))?;
            proof {
                assert forall|s: int, sl: int| s < sic && 0 <= sl < nsi implies #[trigger] key_done(fs, fc, csv, gs@, s, sl) by {
                    if s < oc {
                        lemma_key_done_grow(fs, fc, csv, g0, gs@, s, sl);
                    } else if s > oc {
                        assert forall|k: int| 0 <= k < csv.len() implies fs[(#[trigger] csv[k]).f as int] as int != s by {
                            if k >= t && k > t { assert(fs[csv[t as int].f as int] <= fs[csv[k].f as int]); }
                            if ob <= k < t { assert(fs[csv[k].f as int] == oc); }
                        }
                        lemma_no_key(fs, fc, csv, gs@, s, sl);
                    }
                }
                lemma_empty_blk(a, fs, fc, csv, t as int, sic as int, nsi);
                assert forall|k: int| 0 <= k < t implies fs[(#[trigger] csv[k]).f as int] < sic by {
                    if ob <= k { assert(fs[csv[k].f as int] == oc); }
                }
            }
            b = t;
            cur = sic;
        }
        if !c.ok {
            return Err(Cap { k: Ghost(t as int), kind: Ghost(0), b: Ghost(0), e: Ghost(0) });
        }
        let nl = a.s.len();
        proof { assert(c.slot < nl); }
        let sl = c.slot as usize;
        proof {
            assert(blk_ok(a, fs, fc, csv, b as int, t as int, cur as int, nsi));
            assert(a.cnt()[sl as int] as int == acnt(fs, csv, b as int, t as int, cur as int, sl as int));
            assert(a.mass()[sl as int] <= i128::MAX as u128);
        }
        let m = a.s.get(sl).2 + c.mass;
        if m > i128::MAX as u128 {
            proof {
                assert(a.mass()[sl as int] as int == amass(fs, csv, b as int, t as int, cur as int, sl as int));
                assert(km(fs, csv, t as int, cur as int, sl as int));
                assert(amass(fs, csv, b as int, t + 1, cur as int, sl as int)
                    == amass(fs, csv, b as int, t as int, cur as int, sl as int) + mass_t(fs, csv, cur as int, sl as int)(t as int));
            }
            return Err(Cap { k: Ghost(t as int), kind: Ghost(1), b: Ghost(b as int), e: Ghost(t + 1) });
        }
        let cik = fcv[c.f];
        add_contrib(&mut a, &c, cik, Ghost(fs), Ghost(fc), Ghost(csv), Ghost(b as int), Ghost(t as int), Ghost(cur as int), Ghost(nsi));
        t = t + 1;
        bj = bj + 1;
    }
    if n > 0 {
        let ghost g0 = gs@;
        proof {
            assert forall|k: int| 0 <= k < csv.len() && !(b <= k < n) implies fs[(#[trigger] csv[k]).f as int] != cur by {}
        }
        flush(&mut a, &mut gs, cur, Ghost(fs), Ghost(fc), Ghost(csv), Ghost(b as int), Ghost(n as int), Ghost(nsi))?;
        proof {
            assert forall|s: int, sl: int| 0 <= sl < nsi implies #[trigger] key_done(fs, fc, csv, gs@, s, sl) by {
                if s < cur {
                    lemma_key_done_grow(fs, fc, csv, g0, gs@, s, sl);
                } else if s > cur {
                    assert forall|k: int| 0 <= k < csv.len() implies fs[(#[trigger] csv[k]).f as int] as int != s by {
                        if b <= k { assert(fs[csv[k].f as int] == cur); }
                    }
                    lemma_no_key(fs, fc, csv, gs@, s, sl);
                }
            }
        }
    } else {
        proof {
            assert forall|s: int, sl: int| 0 <= sl < nsi implies #[trigger] key_done(fs, fc, csv, gs@, s, sl) by {
                lemma_no_key(fs, fc, csv, gs@, s, sl);
            }
        }
    }
    Ok(gs)
}

} // verus!
