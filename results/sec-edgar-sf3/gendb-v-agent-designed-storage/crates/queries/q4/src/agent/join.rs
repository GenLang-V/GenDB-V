//! The join: for every filing (in order), every pre row of its sub-runs of stmt `$2`, the tag row (not abstract) and
//! the num rows of the pre row's (tag, version) in the filing's run (an equal range by binary search, num rows of a
//! run being sorted by pair code). One contribution per such pre row: tlabel slot, matched row count, exact value
//! sum (with an overflow flag when the matched values' absolute sum leaves `i128`). The emitted list is exactly
//! `filing::all_cs` (`join_par`): worker tasks over contiguous filing ranges, balanced by qualifying pre rows, each
//! filling a preallocated buffer (at most one contribution per qualifying pre row), concatenated in range order.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::numeric::abs;
use crate::gendb_entry::parallel::{Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::cbuf::*;
use crate::agent::common::flat::*;
use crate::agent::common::par::run_tasks;
use crate::agent::filings::{qn_spec, qterm};
use crate::gendb_entry::layout::PartView;
use crate::stores::num::interface as N;
use crate::stores::pre::interface as P;
use crate::stores::tag_tv::interface as T;
use crate::agent::common::sums::*;
use crate::agent::common::dictmap::NONE;
use crate::agent::mapfacts::tvi;
use crate::agent::pairs::*;
use crate::agent::levels::*;
use crate::agent::filing::*;
use crate::agent::filings::{lower_u64, upper_u64};
use crate::agent::group::{num4, coeff};

verus! {

/// One emitted contribution (exec), with its spec coordinates as ghost fields.
#[derive(Clone, Copy)]
pub struct Contrib {
    pub f: usize,
    pub slot: u64,
    pub cnt: u64,
    pub sum: i128,
    /// The matched values' absolute sum (exact when `ok`).
    pub mass: u128,
    /// The matched values' absolute sum fits `i128` (then `sum` and `mass` are exact).
    pub ok: bool,
    pub rs: Ghost<int>,
    pub re: Ghost<int>,
    pub nq: Ghost<int>,
}

pub open spec fn cs_of(c: Contrib) -> CS { CS { f: c.f as int, slot: c.slot as int, rs: c.rs@, re: c.re@, nq: c.nq@ } }

pub open spec fn cs_seq(s: Seq<Contrib>) -> Seq<CS> { s.map_values(|c: Contrib| cs_of(c)) }

pub open spec fn coeff_phi() -> spec_fn(Val) -> int { |v: Val| coeff(v) }
pub open spec fn abs_phi() -> spec_fn(Val) -> int { |v: Val| abs(coeff(v)) }

/// Matched values' sum and absolute sum of a contribution.
pub open spec fn c_sum(num: Seq<PartView>, c: CS) -> int { run_pair_sum(num, c.rs, c.re, c.nq, coeff_phi()) }
pub open spec fn c_mass(num: Seq<PartView>, c: CS) -> int { run_pair_sum(num, c.rs, c.re, c.nq, abs_phi()) }

/// The exec fields of a contribution are its spec values.
pub open spec fn contrib_ok(num: Seq<PartView>, c: Contrib) -> bool {
    &&& c.cnt as int == run_pair_cnt(num, c.rs@, c.re@, c.nq@)
    &&& c.cnt > 0
    &&& c.ok ==> c.sum as int == c_sum(num, cs_of(c)) && c.mass as int == c_mass(num, cs_of(c)) && c.mass <= i128::MAX as u128
    &&& !c.ok ==> c_mass(num, cs_of(c)) > i128::MAX as int
}

use crate::spec::value::Val;

/// The value of stored num row `i` as a coefficient.
pub open spec fn vterm(vals: Seq<i128>) -> spec_fn(int) -> int { |i: int| vals[i] as int }
pub open spec fn aterm(vals: Seq<i128>) -> spec_fn(int) -> int { |i: int| abs(vals[i] as int) }

/// Exact sum of `vals[lo, hi)` while its absolute sum fits `i128`.
fn range_sum(vals: &[i128], lo: usize, hi: usize) -> (r: (i128, u128, bool))
    requires lo <= hi <= vals@.len(),
    ensures
        r.2 ==> r.0 as int == rsum(lo as int, hi as int, vterm(vals@)) && r.1 as int == rsum(lo as int, hi as int, aterm(vals@))
            && r.1 <= i128::MAX as u128,
        !r.2 ==> rsum(lo as int, hi as int, aterm(vals@)) > i128::MAX as int,
    no_unwind
{
    let mut sum: i128 = 0;
    let mut mass: u128 = 0;
    let mut k = lo;
    while k < hi
        invariant
            lo <= k <= hi <= vals@.len(),
            sum as int == rsum(lo as int, k as int, vterm(vals@)),
            mass as int == rsum(lo as int, k as int, aterm(vals@)),
            mass <= i128::MAX as u128,
            abs(sum as int) <= mass as int,
        decreases hi - k,
    {
        let v = vals[k];
        let a: u128 = if v >= 0 { v as u128 } else { ((-(v + 1)) as u128) + 1 };
        proof { assert(a as int == abs(v as int)); }
        if a > (i128::MAX as u128) - mass {
            proof {
                // The absolute sum so far already exceeds i128; the remaining terms are nonnegative.
                assert(rsum(lo as int, k + 1, aterm(vals@)) > i128::MAX as int);
                assert forall|i: int| k + 1 <= i < hi implies #[trigger] aterm(vals@)(i) >= 0 by {}
                lemma_rsum_nonneg(k + 1, hi as int, aterm(vals@));
                lemma_rsum_split(lo as int, k + 1, hi as int, aterm(vals@));
            }
            return (sum, mass, false);
        }
        mass = mass + a;
        sum = sum + v;
        k = k + 1;
    }
    (sum, mass, true)
}

/// Inside a run, the rows of one pair code form `[lo, hi)`: the contribution's sums are range sums.
proof fn lemma_equal_range(num: Seq<PartView>, rs: int, re: int, nq: int, lo: int, hi: int, phi: spec_fn(Val) -> int)
    requires
        rs <= lo <= hi <= re,
        forall|i: int| rs <= i < re ==> (#[trigger] N::u64s(num, N::P_TV)[i] == nq) == (lo <= i < hi),
    ensures
        run_pair_sum(num, rs, re, nq, phi)
            == rsum(lo, hi, |i: int| phi(num4(crate::stores::num::interface::common::cols::i128_part(num[N::P_VALUE as int])[i] as int))),
{
    let t = run_pair_term(num, nq, phi);
    let g = |i: int| phi(num4(crate::stores::num::interface::common::cols::i128_part(num[N::P_VALUE as int])[i] as int));
    assert forall|i: int| rs <= i < re && !(lo <= i < hi) implies #[trigger] t(i) == 0 by {}
    lemma_rsum_window(rs, lo, hi, re, t);
    assert forall|i: int| lo <= i < hi implies #[trigger] t(i) == g(i) by {}
    lemma_rsum_ext(lo, hi, t, g);
}

/// First position of `[lo, hi)` whose value is not below `key` (values nondecreasing there), searched from the hint
/// `h` (the end of the previous pre row's rows: pre rows of a sub-run and num rows of a run share the pair-code
/// order): a short forward scan when everything before `h` is below `key`, else (or when the scan runs out) a
/// binary search.
fn lower_hint(v: &[u64], lo: usize, hi: usize, key: u64, h: usize) -> (r: usize)
    requires lo <= hi <= v@.len(), forall|a: int, b: int| lo <= a < b < hi ==> #[trigger] v@[a] <= #[trigger] v@[b],
    ensures
        lo <= r <= hi,
        forall|k: int| lo <= k < r ==> #[trigger] v@[k] < key,
        forall|k: int| r <= k < hi ==> #[trigger] v@[k] >= key,
    no_unwind
{
    if h < lo || h > hi || (h > lo && v[h - 1] >= key) {
        return lower_u64(v, lo, hi, key);
    }
    proof {
        assert forall|k: int| lo <= k < h implies #[trigger] v@[k] < key by {
            if k < h - 1 { assert(v@[k] <= v@[h - 1]); }
        }
    }
    let mut k = h;
    let mut steps: usize = 0;
    while k < hi && v[k] < key && steps < 32
        invariant lo <= h <= k <= hi <= v@.len(), forall|x: int| lo <= x < k ==> #[trigger] v@[x] < key,
        decreases hi - k,
    {
        k = k + 1;
        steps = steps + 1;
    }
    if k == hi || v[k] >= key {
        proof {
            assert forall|x: int| k <= x < hi implies #[trigger] v@[x] >= key by {
                if x > k { assert(v@[k as int] <= v@[x]); }
            }
        }
        return k;
    }
    let r = lower_u64(v, k, hi, key);
    r
}

/// First position of `[lo, hi)` whose value is above `key` (values nondecreasing there): a short scan, then a
/// binary search.
fn upper_scan(v: &[u64], lo: usize, hi: usize, key: u64) -> (r: usize)
    requires lo <= hi <= v@.len(), forall|a: int, b: int| lo <= a < b < hi ==> #[trigger] v@[a] <= #[trigger] v@[b],
    ensures
        lo <= r <= hi,
        forall|k: int| lo <= k < r ==> #[trigger] v@[k] <= key,
        forall|k: int| r <= k < hi ==> #[trigger] v@[k] > key,
    no_unwind
{
    let mut k = lo;
    let mut steps: usize = 0;
    while k < hi && v[k] <= key && steps < 8
        invariant lo <= k <= hi <= v@.len(), forall|x: int| lo <= x < k ==> #[trigger] v@[x] <= key,
        decreases hi - k,
    {
        k = k + 1;
        steps = steps + 1;
    }
    if k == hi || v[k] > key {
        proof {
            assert forall|x: int| k <= x < hi implies #[trigger] v@[x] > key by {
                if x > k { assert(v@[k as int] <= v@[x]); }
            }
        }
        return k;
    }
    let r = upper_u64(v, k, hi, key);
    r
}

/// The executable inputs of the join (shared by the worker tasks).
pub struct JoinIn {
    pub look: Arc<Vec<(u64, u64, u64)>>,
    pub run_start: &'static [u64],
    pub nrun1: usize,
    pub ntv: &'static [u64],
    pub nval: &'static [i128],
    pub nrows: usize,
    pub adsh_subs: &'static [u64],
    pub sub_group: &'static [u64],
    pub sub_start: &'static [u64],
    pub ns: usize,
    pub gqv: Arc<Vec<bool>>,
    pub ptv: &'static [u64],
    pub prows: usize,
    pub info: Arc<Vec<(u64, u64, u64)>>,
    pub bits: Arc<Vec<u64>>,
    pub pref: Arc<Vec<u64>>,
    pub lk: LkIn,
    pub ntl: u64,
}

#[verifier::opaque]
pub open spec fn join_in_ok(cx: Cx, ji: JoinIn) -> bool {
    let (num, pre, tag) = (cx.num, cx.pre, cx.tag);
    &&& N::num_layout_ok(num) && P::pre_layout_ok(pre) && T::tag_layout_ok(tag)
    &&& ji.run_start@ == N::u64s(num, N::P_RUN_START) && ji.nrun1 == ji.run_start@.len()
    &&& ji.ntv@ == N::u64s(num, N::P_TV) && ji.nval@ == nvals(num) && ji.nrows == N::row_count(num)
    &&& ji.adsh_subs@ == pre_u64s(pre, P::P_ADSH_SUBS) && ji.sub_group@ == pre_u64s(pre, P::P_SUB_GROUP)
    &&& ji.sub_start@ == pre_u64s(pre, P::P_SUB_START) && ji.ns == P::sub_count(pre)
    &&& ji.ptv@ == pre_u64s(pre, P::P_TV) && ji.prows == P::row_count(pre)
    &&& ji.gqv@.len() == P::group_count(pre)
    &&& forall|g: int| 0 <= g < P::group_count(pre) ==> #[trigger] ji.gqv@[g] == gq(pre, cx.sc, g)
    &&& lk_in_ok(num, pre, tag, ji.lk) && ji.lk.ntl == ji.ntl
    &&& forall|d: int| 0 <= d < ji.info@.len() ==> info_ok(num, pre, tag, ji.ntl as int, #[trigger] ji.info@[d])
    &&& cx.t3.len() == P::pair_count(pre) && cx.t6.len() == P::pair_count(pre)
    &&& forall|q: int| 0 <= q < P::pair_count(pre) ==> #[trigger] cx.t3[q] == t3c(num, pq_tag(pre, q), pq_ver(pre, q))
            && cx.t6[q] == t6c(tag, pq_tag(pre, q), pq_ver(pre, q))
    &&& ji.ntl == ntl(cx) && ji.ntl < NONE
    &&& ji.look@.len() == cx.fil.len() && cx.runs.len() == cx.fil.len() && cx.pcs.len() == cx.fil.len()
    &&& forall|f: int| 0 <= f < cx.fil.len() ==> #[trigger] cx.runs[f] == tvi(ji.look@[f].0) && cx.pcs[f] == tvi(ji.look@[f].1)
            && cx.runs[f] < N::run_count(num) && cx.pcs[f] < P::adsh_count(pre)
            && ji.look@[f].2 as int == (if cx.runs[f] >= 0 && cx.pcs[f] >= 0 { qn_spec(pre, cx.sc, cx.pcs[f]) } else { 0 })
            && ji.look@[f].2 <= ji.prows
}

/// The same inputs (shared `Arc`s, same slices).
pub open spec fn ji_eq(a: JoinIn, b: JoinIn) -> bool {
    &&& a.look@ == b.look@ && a.gqv@ == b.gqv@ && a.info@ == b.info@ && a.bits@ == b.bits@ && a.pref@ == b.pref@
    &&& a.run_start == b.run_start && a.nrun1 == b.nrun1 && a.ntv == b.ntv && a.nval == b.nval && a.nrows == b.nrows
    &&& a.adsh_subs == b.adsh_subs && a.sub_group == b.sub_group && a.sub_start == b.sub_start && a.ns == b.ns
    &&& a.ptv == b.ptv && a.prows == b.prows && a.lk == b.lk && a.ntl == b.ntl
}

pub fn clone_ji(ji: &JoinIn) -> (r: JoinIn)
    ensures ji_eq(r, *ji),
{
    JoinIn {
        look: ji.look.clone(), run_start: ji.run_start, nrun1: ji.nrun1, ntv: ji.ntv, nval: ji.nval, nrows: ji.nrows,
        adsh_subs: ji.adsh_subs, sub_group: ji.sub_group, sub_start: ji.sub_start, ns: ji.ns, gqv: ji.gqv.clone(),
        ptv: ji.ptv, prows: ji.prows, info: ji.info.clone(), bits: ji.bits.clone(), pref: ji.pref.clone(), lk: ji.lk,
        ntl: ji.ntl,
    }
}

proof fn lemma_ji_eq(cx: Cx, a: JoinIn, b: JoinIn)
    requires join_in_ok(cx, a), ji_eq(b, a),
    ensures join_in_ok(cx, b),
{
    reveal(join_in_ok);
}

/// The lookup of pre pair `q`: its entry in the pair list (found by rank, key checked), else a direct lookup.
fn pair_of(cx: Ghost<Cx>, ji: &JoinIn, q: usize) -> (r: (u64, u64))
    requires join_in_ok(cx@, *ji), q < P::pair_count(cx@.pre),
    ensures
        cx@.t3[q as int] == tvi(r.0),
        r.1 == tslot(cx@.tag, ji.ntl as int, cx@.t6[q as int]),
    no_unwind
{
    proof { reveal(join_in_ok); }
    let ghost (num, pre, tag) = (cx@.num, cx@.pre, cx@.tag);
    proof {
        assert(cx@.t3[q as int] == t3c(num, pq_tag(pre, q as int), pq_ver(pre, q as int)));
        assert(cx@.t6[q as int] == t6c(tag, pq_tag(pre, q as int), pq_ver(pre, q as int)));
    }
    let bits: &Vec<u64> = &*ji.bits;
    let pref: &Vec<u64> = &*ji.pref;
    let info: &Vec<(u64, u64, u64)> = &*ji.info;
    let w = q / 64;
    if w < bits.len() && w < pref.len() {
        let below: u64 = (1u64 << ((q % 64) as u64)).wrapping_sub(1);
        let d = pref[w].wrapping_add(popcount(bits[w] & below));
        if d < info.len() as u64 {
            let e = info[d as usize];
            if e.0 == q as u64 {
                proof { assert(info_ok(num, pre, tag, ji.ntl as int, info@[d as int])); }
                return (e.1, e.2);
            }
        }
    }
    proof { assert(ji.lk.ppt@.len() == P::pair_count(pre)); }
    lookup_pair(&ji.lk, q, Ghost(num), Ghost(pre), Ghost(tag))
}

/// The contribution of stored pre row `j` of filing `f`, appended when it has one.
fn join_row(cx: Ghost<Cx>, ji: &JoinIn, f: usize, rs: usize, re: usize, j: usize, h: usize, out: &mut CBuf) -> (nh: usize)
    requires
        join_in_ok(cx@, *ji), f < cx@.fil.len(), cx@.runs[f as int] >= 0,
        rs as int == rs_of(cx@, f as int), re as int == re_of(cx@, f as int), rs <= re <= ji.nrows,
        forall|a: int, b: int| rs <= a < b < re ==> #[trigger] ji.ntv@[a] <= #[trigger] ji.ntv@[b],
        j < ji.prows,
        old(out).wf(), old(out).view().len() < old(out).capacity(),
    ensures
        final(out).wf(), final(out).capacity() == old(out).capacity(),
        final(out).view().len() <= old(out).view().len() + 1,
        cs_seq(final(out).view()) == cs_seq(old(out).view()) + row_cs(cx@, f as int, j as int),
        forall|k: int| 0 <= k < old(out).view().len() ==> #[trigger] final(out).view()[k] == old(out).view()[k],
        forall|k: int| old(out).view().len() <= k < final(out).view().len() ==> contrib_ok(cx@.num, #[trigger] final(out).view()[k]),
        forall|k: int| old(out).view().len() <= k < final(out).view().len() ==> (#[trigger] final(out).view()[k]).f == f && final(out).view()[k].slot <= ji.ntl,
    no_unwind
{
    proof { reveal(join_in_ok); }
    let ghost cxv = cx@;
    let ghost (num, pre, tag) = (cxv.num, cxv.pre, cxv.tag);
    let ghost before = out.view();
    proof {
        assert(pre_u64s(pre, P::P_TV)[j as int] < P::pair_count(pre));
    }
    let q = ji.ptv[j];
    proof {
        assert(q < P::pair_count(pre));
        assert(ji.lk.ppt@ == pre_u64s(pre, P::P_PAIR_TAG));
        assert(q < ji.lk.ppn);
        assert(q as usize as int == q as int);
    }
    let qu = q as usize;
    let (nq, slot) = pair_of(cx, ji, qu);
    proof {
        assert(qu as int == q as int);
        assert(cxv.t3[qu as int] == tvi(nq));
        assert(cxv.t3[q as int] == tvi(nq));
        lemma_t3c_found(num, pq_tag(pre, q as int), pq_ver(pre, q as int));
        lemma_t6c_found(tag, pq_tag(pre, q as int), pq_ver(pre, q as int));
    }
    if nq == NONE {
        proof { assert(row_cs(cxv, f as int, j as int) =~= Seq::<CS>::empty()); assert(cs_seq(out.view()) =~= cs_seq(before) + Seq::<CS>::empty()); }
        return h;
    }
    proof { assert(nq < N::pair_count(num)); }
    let lo = lower_hint(ji.ntv, rs, re, nq, h);
    let hi = upper_scan(ji.ntv, lo, re, nq);
    proof {
        assert forall|i: int| rs <= i < re implies (#[trigger] N::u64s(num, N::P_TV)[i] == nq as int) == (lo <= i < hi) by {
            if i < lo { assert(ji.ntv@[i] < nq); }
            if lo <= i && i >= hi { assert(ji.ntv@[i] > nq); }
        }
        lemma_equal_range(num, rs as int, re as int, nq as int, lo as int, hi as int, const1());
        let one = |i: int| const1()(num4(nvals(num)[i] as int));
        assert forall|i: int| lo <= i < hi implies #[trigger] one(i) == 1 by {}
        lemma_rsum_const1(lo as int, hi as int, one);
        assert(run_pair_cnt(num, rs as int, re as int, nq as int) == hi - lo);
    }
    if lo >= hi {
        proof { assert(row_cs(cxv, f as int, j as int) =~= Seq::<CS>::empty()); assert(cs_seq(out.view()) =~= cs_seq(before) + Seq::<CS>::empty()); }
        return hi;
    }
    let ghost tr = cxv.t6[q as int];
    if slot == NONE {
        proof {
            assert(!(tr >= 0 && tag_abstract(tag, tr) == 0)) by {
                if tr >= 0 && tag_abstract(tag, tr) == 0 {
                    assert(tr < T::row_count(tag));
                    if crate::stores::tag_tv::interface::common::text::u8_part(tag[T::P_TLABEL_VALID as int])[tr] != 0 {
                        assert(tu64s(cxv, T::P_TLABEL_CODES)[tr] < crate::stores::tag_tv::interface::common::cols::text_count(tag, T::P_TLABEL_OFF as int));
                    }
                }
            }
            assert(row_cs(cxv, f as int, j as int) =~= Seq::<CS>::empty());
            assert(cs_seq(out.view()) =~= cs_seq(before) + Seq::<CS>::empty());
        }
        return hi;
    }
    proof {
        assert(tr >= 0 && tag_abstract(tag, tr) == 0);
        assert(tr < T::row_count(tag));
        assert(slot as int == slot_of(cxv, tr));
        if crate::stores::tag_tv::interface::common::text::u8_part(tag[T::P_TLABEL_VALID as int])[tr] != 0 {
            assert(tu64s(cxv, T::P_TLABEL_CODES)[tr] < crate::stores::tag_tv::interface::common::cols::text_count(tag, T::P_TLABEL_OFF as int));
        }
        assert(slot <= ji.ntl);
    }
    let (sum, mass, ok) = range_sum(ji.nval, lo, hi);
    proof {
        lemma_equal_range(num, rs as int, re as int, nq as int, lo as int, hi as int, coeff_phi());
        lemma_equal_range(num, rs as int, re as int, nq as int, lo as int, hi as int, abs_phi());
        lemma_rsum_ext(lo as int, hi as int, |i: int| coeff_phi()(num4(nvals(num)[i] as int)), vterm(ji.nval@));
        lemma_rsum_ext(lo as int, hi as int, |i: int| abs_phi()(num4(nvals(num)[i] as int)), aterm(ji.nval@));
    }
    let c = Contrib { f, slot, cnt: (hi - lo) as u64, sum, mass, ok, rs: Ghost(rs as int), re: Ghost(re as int), nq: Ghost(nq as int) };
    out.push(c);
    proof {
        assert(row_cs(cxv, f as int, j as int) == seq![cs_of(c)]);
        assert(cs_seq(out.view()) =~= cs_seq(before) + seq![cs_of(c)]);
    }
    hi
}

/// Contributions of the stored pre rows `[j0, j1)` of filing `f`, appended.
fn join_rows(cx: Ghost<Cx>, ji: &JoinIn, f: usize, rs: usize, re: usize, j0: usize, j1: usize, out: &mut CBuf)
    requires
        join_in_ok(cx@, *ji), f < cx@.fil.len(), cx@.runs[f as int] >= 0,
        rs as int == rs_of(cx@, f as int), re as int == re_of(cx@, f as int), rs <= re <= ji.nrows,
        forall|a: int, b: int| rs <= a < b < re ==> #[trigger] ji.ntv@[a] <= #[trigger] ji.ntv@[b],
        j0 <= j1 <= ji.prows,
        old(out).wf(), old(out).view().len() + (j1 - j0) <= old(out).capacity(),
    ensures
        final(out).wf(), final(out).capacity() == old(out).capacity(),
        final(out).view().len() <= old(out).view().len() + (j1 - j0),
        cs_seq(final(out).view()) == cs_seq(old(out).view()) + rows_cs(cx@, f as int, j0 as int, j1 as int),
        forall|k: int| 0 <= k < old(out).view().len() ==> #[trigger] final(out).view()[k] == old(out).view()[k],
        forall|k: int| old(out).view().len() <= k < final(out).view().len() ==> contrib_ok(cx@.num, #[trigger] final(out).view()[k]),
        forall|k: int| old(out).view().len() <= k < final(out).view().len() ==> (#[trigger] final(out).view()[k]).f == f && final(out).view()[k].slot <= ji.ntl,
    no_unwind
{
    let ghost o0 = out.view();
    let ghost cap = out.capacity();
    let mut j = j0;
    // The search hint: the end of the previous pre row's num rows.
    let mut h = rs;
    proof { assert(cs_seq(out.view()) =~= cs_seq(o0) + Seq::<CS>::empty()); }
    while j < j1
        invariant
            join_in_ok(cx@, *ji), f < cx@.fil.len(), cx@.runs[f as int] >= 0,
            rs as int == rs_of(cx@, f as int), re as int == re_of(cx@, f as int), rs <= re <= ji.nrows,
            forall|a: int, b: int| rs <= a < b < re ==> #[trigger] ji.ntv@[a] <= #[trigger] ji.ntv@[b],
            j0 <= j <= j1 <= ji.prows,
            out.wf(), out.capacity() == cap, o0.len() + (j1 - j0) <= cap, out.view().len() <= o0.len() + (j - j0),
            cs_seq(out.view()) == cs_seq(o0) + rows_cs(cx@, f as int, j0 as int, j as int),
            out.view().len() >= o0.len(),
            forall|k: int| 0 <= k < o0.len() ==> #[trigger] out.view()[k] == o0[k],
            forall|k: int| o0.len() <= k < out.view().len() ==> contrib_ok(cx@.num, #[trigger] out.view()[k]),
            forall|k: int| o0.len() <= k < out.view().len() ==> (#[trigger] out.view()[k]).f == f && out.view()[k].slot <= ji.ntl,
        decreases j1 - j,
    {
        let ghost before = out.view();
        h = join_row(cx, ji, f, rs, re, j, h, out);
        proof {
            assert(rows_cs(cx@, f as int, j0 as int, j + 1) == rows_cs(cx@, f as int, j0 as int, j as int) + row_cs(cx@, f as int, j as int));
            assert(cs_seq(out.view()) =~= cs_seq(o0) + rows_cs(cx@, f as int, j0 as int, j + 1));
            assert forall|k: int| 0 <= k < o0.len() implies #[trigger] out.view()[k] == o0[k] by { assert(out.view()[k] == before[k]); }
            assert forall|k: int| o0.len() <= k < out.view().len() implies contrib_ok(cx@.num, #[trigger] out.view()[k]) by {
                if k < before.len() { assert(out.view()[k] == before[k]); }
            }
            assert forall|k: int| o0.len() <= k < out.view().len() implies (#[trigger] out.view()[k]).f == f && out.view()[k].slot <= ji.ntl by {
                if k < before.len() { assert(out.view()[k] == before[k]); }
            }
        }
        j = j + 1;
    }
}

/// The contributions of filing `f`, appended.
fn join_filing(cx: Ghost<Cx>, ji: &JoinIn, f: usize, out: &mut CBuf)
    requires
        join_in_ok(cx@, *ji), f < cx@.fil.len(),
        old(out).wf(), old(out).view().len() + ji.look@[f as int].2 <= old(out).capacity(),
    ensures
        final(out).wf(), final(out).capacity() == old(out).capacity(),
        final(out).view().len() <= old(out).view().len() + ji.look@[f as int].2,
        cs_seq(final(out).view()) == cs_seq(old(out).view()) + filing_cs(cx@, f as int),
        forall|k: int| 0 <= k < old(out).view().len() ==> #[trigger] final(out).view()[k] == old(out).view()[k],
        forall|k: int| old(out).view().len() <= k < final(out).view().len() ==> contrib_ok(cx@.num, #[trigger] final(out).view()[k]),
        forall|k: int| old(out).view().len() <= k < final(out).view().len() ==> (#[trigger] final(out).view()[k]).f == f && final(out).view()[k].slot <= ji.ntl,
    no_unwind
{
    let ghost o0 = out.view();
    let ghost cap = out.capacity();
    let ghost cxv = cx@;
    proof { reveal(join_in_ok); }
    let look: &Vec<(u64, u64, u64)> = &*ji.look;
    let (run, pc, qn) = look[f];
    if run == NONE || pc == NONE {
        proof {
            assert(filing_cs(cxv, f as int) =~= Seq::<CS>::empty());
            assert(cs_seq(out.view()) =~= cs_seq(o0) + Seq::<CS>::empty());
        }
        return;
    }
    let ghost num = cxv.num;
    let ghost pre = cxv.pre;
    proof {
        assert(cxv.runs[f as int] == run as int && cxv.pcs[f as int] == pc as int);
        assert(run < N::run_count(num) && pc < P::adsh_count(pre));
        P::lemma_adsh_subs(pre, pc as int);
        let st = N::u64s(num, N::P_RUN_START);
        let nr = N::run_count(num);
        assert(st[0] == 0 && st[nr] == N::row_count(num));
        assert(st[run as int] < st[run + 1]);
        if run > 0 { assert(st[0] < st[run as int]); }
        if run + 1 < nr { assert(st[run + 1] < st[nr]); }
        assert(ji.adsh_subs@[pc + 1] <= ji.ns);
    }
    let ru = run as usize;
    let rs = ji.run_start[ru] as usize;
    let re = ji.run_start[ru + 1] as usize;
    proof {
        let st = N::u64s(num, N::P_RUN_START);
        assert forall|a: int, b: int| rs <= a < b < re implies #[trigger] ji.ntv@[a] <= #[trigger] ji.ntv@[b] by {
            assert(st[run as int] <= a < b < st[run + 1]);
        }
    }
    let pcu = pc as usize;
    let s0 = ji.adsh_subs[pcu] as usize;
    let s1 = ji.adsh_subs[pcu + 1] as usize;
    let gqv: &Vec<bool> = &*ji.gqv;
    let mut s = s0;
    proof { assert(cs_seq(out.view()) =~= cs_seq(o0) + Seq::<CS>::empty()); }
    while s < s1
        invariant
            join_in_ok(cx@, *ji), cxv == cx@, f < cx@.fil.len(), cx@.runs[f as int] >= 0, cx@.pcs[f as int] == pc as int,
            pc as int >= 0, pc < P::adsh_count(cx@.pre),
            rs as int == rs_of(cx@, f as int), re as int == re_of(cx@, f as int), rs <= re <= ji.nrows,
            forall|a: int, b: int| rs <= a < b < re ==> #[trigger] ji.ntv@[a] <= #[trigger] ji.ntv@[b],
            s0 == pre_u64s(cx@.pre, P::P_ADSH_SUBS)[pc as int], s1 == pre_u64s(cx@.pre, P::P_ADSH_SUBS)[pc + 1],
            s0 <= s <= s1 <= ji.ns,
            gqv@ == ji.gqv@,
            out.wf(), out.capacity() == cap, o0.len() + qn <= cap, qn as int == rsum(s0 as int, s1 as int, qterm(cx@.pre, cx@.sc)),
            out.view().len() <= o0.len() + rsum(s0 as int, s as int, qterm(cx@.pre, cx@.sc)),
            cs_seq(out.view()) == cs_seq(o0) + subs_cs(cx@, f as int, s0 as int, s as int),
            out.view().len() >= o0.len(),
            forall|k: int| 0 <= k < o0.len() ==> #[trigger] out.view()[k] == o0[k],
            forall|k: int| o0.len() <= k < out.view().len() ==> contrib_ok(cx@.num, #[trigger] out.view()[k]),
            forall|k: int| o0.len() <= k < out.view().len() ==> (#[trigger] out.view()[k]).f == f && out.view()[k].slot <= ji.ntl,
        decreases s1 - s,
    {
        let ghost before = out.view();
        proof {
            reveal(join_in_ok);
            let pre = cx@.pre;
            assert(pre_u64s(pre, P::P_SUB_ADSH)[s as int] < P::adsh_count(pre) && ji.sub_group@[s as int] < P::group_count(pre));
            let st = pre_u64s(pre, P::P_SUB_START);
            let ns = P::sub_count(pre);
            assert(st[0] == 0 && st[ns] == P::row_count(pre));
            assert(st[s as int] < st[s + 1]);
            if s > 0 { assert(st[0] < st[s as int]); }
            if s + 1 < ns { assert(st[s + 1] < st[ns]); }
            assert(ji.sub_group@[s as int] < ji.gqv@.len());
        }
        let gl = gqv.len();
        proof { assert(ji.sub_group@[s as int] < gl); }
        let g = ji.sub_group[s] as usize;
        proof {
            reveal(join_in_ok);
            assert(g as int == ji.sub_group@[s as int]);
            assert(ji.gqv@[g as int] == gq(cx@.pre, cx@.sc, g as int));
            assert(pu64s(cx@, P::P_SUB_GROUP)[s as int] as int == g as int);
        }
        proof {
            // This sub-run's qualifying rows fit the remaining budget: the later sub-runs' terms are nonnegative.
            lemma_qterm_nonneg(cx@.pre, cx@.sc, s0 as int, s1 as int);
            lemma_rsum_split(s0 as int, s + 1, s1 as int, qterm(cx@.pre, cx@.sc));
            lemma_rsum_nonneg(s + 1, s1 as int, qterm(cx@.pre, cx@.sc));
            assert(rsum(s0 as int, s + 1, qterm(cx@.pre, cx@.sc)) == rsum(s0 as int, s as int, qterm(cx@.pre, cx@.sc)) + qterm(cx@.pre, cx@.sc)(s as int));
        }
        if gqv[g] {
            let j0 = ji.sub_start[s] as usize;
            let j1 = ji.sub_start[s + 1] as usize;
            proof { assert(qterm(cx@.pre, cx@.sc)(s as int) == j1 - j0); }
            join_rows(cx, ji, f, rs, re, j0, j1, out);
            proof { reveal(join_in_ok); assert(sub_cs(cx@, f as int, s as int) == rows_cs(cx@, f as int, j0 as int, j1 as int)); }
        } else {
            proof { reveal(join_in_ok); assert(sub_cs(cx@, f as int, s as int) =~= Seq::<CS>::empty()); }
        }
        proof {
            assert(subs_cs(cx@, f as int, s0 as int, s + 1) == subs_cs(cx@, f as int, s0 as int, s as int) + sub_cs(cx@, f as int, s as int));
            assert(cs_seq(out.view()) =~= cs_seq(o0) + subs_cs(cx@, f as int, s0 as int, s + 1));
            assert forall|k: int| 0 <= k < o0.len() implies #[trigger] out.view()[k] == o0[k] by { assert(out.view()[k] == before[k]); }
            assert forall|k: int| o0.len() <= k < out.view().len() implies contrib_ok(cx@.num, #[trigger] out.view()[k]) by {
                if k < before.len() { assert(out.view()[k] == before[k]); }
            }
            assert forall|k: int| o0.len() <= k < out.view().len() implies (#[trigger] out.view()[k]).f == f && out.view()[k].slot <= ji.ntl by {
                if k < before.len() { assert(out.view()[k] == before[k]); }
            }
        }
        s = s + 1;
    }
    proof { reveal(join_in_ok); assert(filing_cs(cx@, f as int) == subs_cs(cx@, f as int, s0 as int, s1 as int)); }
}

/// Every sub-run's qualifying row count is nonnegative (sub-run starts increase).
proof fn lemma_qterm_nonneg(pre: Seq<PartView>, sc: int, s0: int, s1: int)
    requires P::pre_layout_ok(pre), 0 <= s0 <= s1 <= P::sub_count(pre),
    ensures forall|i: int| s0 <= i < s1 ==> #[trigger] qterm(pre, sc)(i) >= 0,
{
    assert forall|i: int| s0 <= i < s1 implies #[trigger] qterm(pre, sc)(i) >= 0 by {
        let st = pre_u64s(pre, P::P_SUB_START);
        let ns = P::sub_count(pre);
        assert(st[0] == 0 && st[ns] == P::row_count(pre));
        assert(st[i] < st[i + 1]);
    }
}

/// Contributions of filings `[f0, f1)`, in order.
pub open spec fn seg_cs(cx: Cx, f0: int, f1: int) -> Seq<CS>
    decreases f1 - f0,
{
    if f1 <= f0 { Seq::empty() } else { seg_cs(cx, f0, f1 - 1) + filing_cs(cx, f1 - 1) }
}

/// The contributions of filings `[0, f1)` are those of `[0, f0)` followed by those of `[f0, f1)`.
pub proof fn lemma_all_seg(cx: Cx, f0: int, f1: int)
    requires 0 <= f0 <= f1,
    ensures all_cs(cx, f1) == all_cs(cx, f0) + seg_cs(cx, f0, f1),
    decreases f1 - f0,
{
    if f1 > f0 {
        lemma_all_seg(cx, f0, f1 - 1);
        assert(all_cs(cx, f1) =~= all_cs(cx, f0) + seg_cs(cx, f0, f1));
    } else {
        assert(all_cs(cx, f1) =~= all_cs(cx, f0) + seg_cs(cx, f0, f1));
    }
}

pub proof fn lemma_cs_seq_append(a: Seq<Contrib>, b: Seq<Contrib>)
    ensures cs_seq(a + b) == cs_seq(a) + cs_seq(b),
{
    assert(cs_seq(a + b) =~= cs_seq(a) + cs_seq(b));
}

/// Qualifying pre rows of filings `[f0, f1)` (the contribution budget of a task).
pub open spec fn qsum(look: Seq<(u64, u64, u64)>, f0: int, f1: int) -> int {
    rsum(f0, f1, qof(look))
}

pub open spec fn qof(look: Seq<(u64, u64, u64)>) -> spec_fn(int) -> int { |f: int| look[f].2 as int }

proof fn lemma_qsum_step(look: Seq<(u64, u64, u64)>, f0: int, f: int, f1: int)
    requires f0 <= f < f1,
    ensures qsum(look, f0, f) + look[f].2 <= qsum(look, f0, f1), qsum(look, f0, f + 1) == qsum(look, f0, f) + look[f].2,
{
    let h = qof(look);
    lemma_rsum_split(f0, f + 1, f1, h);
    assert forall|g: int| f + 1 <= g < f1 implies #[trigger] h(g) >= 0 by {}
    lemma_rsum_nonneg(f + 1, f1, h);
}

/// The facts of a run of contributions of filings `[f0, f1)`.
pub open spec fn seg_ok(cx: Cx, ntl: u64, f0: int, f1: int, v: Seq<Contrib>) -> bool {
    &&& cs_seq(v) == seg_cs(cx, f0, f1)
    &&& forall|k: int| 0 <= k < v.len() ==> contrib_ok(cx.num, #[trigger] v[k])
    &&& forall|k: int| 0 <= k < v.len() ==> f0 <= (#[trigger] v[k]).f < f1 && v[k].slot <= ntl
    &&& forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> (#[trigger] v[k1]).f <= (#[trigger] v[k2]).f
}

/// One worker task: the contributions of filings `[f0, f1)` into a buffer sized by their qualifying pre rows.
pub struct JoinTask {
    pub cx: Ghost<Cx>,
    pub ji: JoinIn,
    pub f0: usize,
    pub f1: usize,
    pub buf: CBuf,
}

impl WorkerTask for JoinTask {
    type Output = CBuf;

    open spec fn pre(&self) -> bool {
        &&& join_in_ok(self.cx@, self.ji)
        &&& self.f0 <= self.f1 <= self.cx@.fil.len()
        &&& self.buf.wf() && self.buf.view().len() == 0 && qsum(self.ji.look@, self.f0 as int, self.f1 as int) <= self.buf.capacity()
    }

    open spec fn post(&self, out: CBuf) -> bool {
        &&& out.wf() && seg_ok(self.cx@, self.ji.ntl, self.f0 as int, self.f1 as int, out.view())
        &&& out.view().len() <= qsum(self.ji.look@, self.f0 as int, self.f1 as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.f0 as u64, self.f1 as u64)
    }

    fn run(self) -> (out: CBuf) {
        let JoinTask { cx, ji, f0, f1, buf } = self;
        let mut buf = buf;
        let ghost cap = buf.capacity();
        proof { reveal(join_in_ok); assert(cs_seq(buf.view()) =~= Seq::<CS>::empty()); }
        let mut f = f0;
        while f < f1
            invariant
                join_in_ok(cx@, ji), f0 <= f <= f1 <= cx@.fil.len(),
                buf.wf(), buf.capacity() == cap, qsum(ji.look@, f0 as int, f1 as int) <= cap,
                buf.view().len() <= qsum(ji.look@, f0 as int, f as int),
                seg_ok(cx@, ji.ntl, f0 as int, f as int, buf.view()),
            decreases f1 - f,
        {
            let ghost before = buf.view();
            proof { lemma_qsum_step(ji.look@, f0 as int, f as int, f1 as int); }
            join_filing(cx, &ji, f, &mut buf);
            proof {
                let v = buf.view();
                assert(seg_cs(cx@, f0 as int, f + 1) == seg_cs(cx@, f0 as int, f as int) + filing_cs(cx@, f as int));
                assert forall|k: int| 0 <= k < v.len() implies contrib_ok(cx@.num, #[trigger] v[k]) by {
                    if k < before.len() { assert(v[k] == before[k]); }
                }
                assert forall|k: int| 0 <= k < v.len() implies f0 <= (#[trigger] v[k]).f < f + 1 && v[k].slot <= ji.ntl by {
                    if k < before.len() { assert(v[k] == before[k]); }
                }
                assert forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() implies (#[trigger] v[k1]).f <= (#[trigger] v[k2]).f by {
                    if k2 < before.len() { assert(v[k1] == before[k1] && v[k2] == before[k2]); }
                    else if k1 < before.len() { assert(v[k1] == before[k1]); }
                }
            }
            f = f + 1;
        }
        buf
    }
}

/// The facts of the join's output: exactly the contributions of every filing, each exact, in filing order.
pub open spec fn join_out_ok(cx: Cx, ntl: u64, out: Seq<Contrib>) -> bool {
    &&& cs_seq(out) == all_cs(cx, cx.fil.len() as int)
    &&& forall|k: int| 0 <= k < out.len() ==> contrib_ok(cx.num, #[trigger] out[k])
    &&& forall|k: int| 0 <= k < out.len() ==> (#[trigger] out[k]).f < cx.fil.len() && out[k].slot <= ntl
    &&& forall|k1: int, k2: int| 0 <= k1 < k2 < out.len() ==> (#[trigger] out[k1]).f <= (#[trigger] out[k2]).f
}

/// Adjacent runs of filings `[f0, f1)` and `[f1, f2)` concatenate to the run of `[f0, f2)`.
proof fn lemma_seg_append(cx: Cx, ntl: u64, f0: int, f1: int, f2: int, a: Seq<Contrib>, b: Seq<Contrib>)
    requires 0 <= f0 <= f1 <= f2, seg_ok(cx, ntl, f0, f1, a), seg_ok(cx, ntl, f1, f2, b),
    ensures seg_ok(cx, ntl, f0, f2, a + b),
{
    lemma_cs_seq_append(a, b);
    lemma_seg_split(cx, f0, f1, f2);
    let v = a + b;
    assert forall|k: int| 0 <= k < v.len() implies contrib_ok(cx.num, #[trigger] v[k]) && f0 <= v[k].f < f2 && v[k].slot <= ntl by {
        if k < a.len() { assert(v[k] == a[k]); } else { assert(v[k] == b[k - a.len()]); }
    }
    assert forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() implies (#[trigger] v[k1]).f <= (#[trigger] v[k2]).f by {
        if k2 < a.len() { assert(v[k1] == a[k1] && v[k2] == a[k2]); }
        else if k1 < a.len() { assert(v[k1] == a[k1] && v[k2] == b[k2 - a.len()]); }
        else { assert(v[k1] == b[k1 - a.len()] && v[k2] == b[k2 - a.len()]); }
    }
}

/// `seg_cs(f0, f2) == seg_cs(f0, f1) + seg_cs(f1, f2)`.
proof fn lemma_seg_split(cx: Cx, f0: int, f1: int, f2: int)
    requires f0 <= f1 <= f2,
    ensures seg_cs(cx, f0, f2) == seg_cs(cx, f0, f1) + seg_cs(cx, f1, f2),
    decreases f2 - f1,
{
    if f2 > f1 {
        lemma_seg_split(cx, f0, f1, f2 - 1);
        assert(seg_cs(cx, f0, f2) =~= seg_cs(cx, f0, f1) + seg_cs(cx, f1, f2));
    } else {
        assert(seg_cs(cx, f0, f2) =~= seg_cs(cx, f0, f1) + seg_cs(cx, f1, f2));
    }
}

/// A filing's budget is at most the pre row count.
proof fn lemma_look_bound(cx: Cx, ji: JoinIn, f: int)
    requires join_in_ok(cx, ji), 0 <= f < cx.fil.len(),
    ensures ji.look@[f].2 <= ji.prows, ji.look@.len() == cx.fil.len(),
{
    reveal(join_in_ok);
    assert(cx.runs[f] == tvi(ji.look@[f].0));
}

/// The contributions of every filing, in order: worker tasks over contiguous filing ranges balanced by qualifying
/// pre rows (one range per worker), or one range per filing in the (never expected) case that the total budget
/// does not fit `usize`; the buffers are concatenated in range order.
pub fn join_par(dispatch: &mut Dispatch, workers: usize, cx: Ghost<Cx>, ji: JoinIn) -> (r: Result<Vec<CBuf>, WorkerFailure>)
    requires join_in_ok(cx@, ji), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(out) ==> join_out_ok(cx@, ji.ntl, cflat(out@)) && cflat(out@).len() <= usize::MAX,
{
    proof { reveal(join_in_ok); }
    let look: &Vec<(u64, u64, u64)> = &*ji.look;
    let nf = look.len();
    let ghost lk = ji.look@;
    // The total budget: at most nf terms, each below 2^64, so it fits u128.
    let mut total: u128 = 0;
    let mut f: usize = 0;
    while f < nf
        invariant nf == lk.len(), look@ == lk, f <= nf, total as int == qsum(lk, 0, f as int), total <= f as int * 0x1_0000_0000_0000_0000,
        decreases nf - f,
    {
        proof {
            lemma_qsum_step(lk, 0, f as int, f + 1);
            assert(f as int * 0x1_0000_0000_0000_0000 <= 0xffff_ffff_ffff_ffff * 0x1_0000_0000_0000_0000) by (nonlinear_arith)
                requires f <= 0xffff_ffff_ffff_ffff;
        }
        total = total + look[f].2 as u128;
        f = f + 1;
    }
    // Task ranges: starts[k] is the first filing of task k; the ranges tile [0, nf).
    let mut tasks: Vec<JoinTask> = Vec::new();
    let ghost mut starts: Seq<int> = Seq::empty();
    let mut f0: usize = 0;
    let mut acc: u128 = 0;
    if total <= usize::MAX as u128 {
        let nt: usize = if total < 16384 { 1 } else { workers };
        let mut k: usize = 0;
        while k < nt
            invariant
                join_in_ok(cx@, ji), nf == lk.len(), look@ == lk, lk == ji.look@, 1 <= nt <= MAX_WORKERS, k <= nt,
                nf == cx@.fil.len(), k == 0 ==> f0 == 0,
                total as int == qsum(lk, 0, nf as int), total <= usize::MAX,
                f0 <= nf, acc as int == qsum(lk, 0, f0 as int), acc <= total,
                k == nt ==> f0 == nf,
                tasks@.len() == k, starts.len() == k,
                forall|j: int| 0 <= j < k ==> (#[trigger] tasks@[j]).pre() && tasks@[j].cx == cx && ji_eq(tasks@[j].ji, ji)
                    && tasks@[j].f0 == starts[j] && tasks@[j].f1 == (if j + 1 < k { starts[j + 1] } else { f0 as int }),
                k > 0 ==> starts[0] == 0,
            decreases nt - k,
        {
            proof {
                assert(total as int * (k + 1) as int <= usize::MAX as int * 64) by (nonlinear_arith)
                    requires total <= usize::MAX, k + 1 <= 64;
            }
            let last = k + 1 == nt;
            let target: u128 = if last { total } else { (total * (k + 1) as u128) / nt as u128 };
            let mut f1 = f0;
            let mut a1 = acc;
            while f1 < nf && (a1 < target || last)
                invariant
                    nf == lk.len(), look@ == lk, f0 <= f1 <= nf, a1 as int == qsum(lk, 0, f1 as int), acc <= a1,
                    total as int == qsum(lk, 0, nf as int), acc as int == qsum(lk, 0, f0 as int),
                decreases nf - f1,
            {
                proof {
                    lemma_qsum_step(lk, 0, f1 as int, nf as int);
                }
                a1 = a1 + look[f1].2 as u128;
                f1 = f1 + 1;
            }
            proof {
                if f1 < nf { lemma_qsum_step(lk, 0, f1 as int, nf as int); }
                assert(a1 <= total) by {
                    lemma_rsum_split(0, f1 as int, nf as int, qof(lk));
                    assert forall|g: int| f1 <= g < nf implies #[trigger] qof(lk)(g) >= 0 by {}
                    lemma_rsum_nonneg(f1 as int, nf as int, qof(lk));
                }
                lemma_rsum_split(0, f0 as int, f1 as int, qof(lk));
            }
            let cap = (a1 - acc) as usize;
            let task = JoinTask { cx, ji: clone_ji(&ji), f0, f1, buf: CBuf::new(cap) };
            proof { lemma_ji_eq(cx@, ji, task.ji); }
            tasks.push(task);
            proof { starts = starts.push(f0 as int); }
            f0 = f1;
            acc = a1;
            k = k + 1;
        }
    } else {
        // One range per filing: each budget is one filing's qualifying pre rows (at most the pre row count).
        while f0 < nf
            invariant
                join_in_ok(cx@, ji), nf == lk.len(), look@ == lk, lk == ji.look@, f0 <= nf, nf == cx@.fil.len(),
                tasks@.len() == starts.len(),
                forall|j: int| 0 <= j < tasks@.len() ==> (#[trigger] tasks@[j]).pre() && tasks@[j].cx == cx && ji_eq(tasks@[j].ji, ji)
                    && tasks@[j].f0 == starts[j] && tasks@[j].f1 == (if j + 1 < tasks@.len() { starts[j + 1] } else { f0 as int }),
                tasks@.len() > 0 ==> starts[0] == 0,
                tasks@.len() == 0 ==> f0 == 0,
            decreases nf - f0,
        {
            proof {
                lemma_look_bound(cx@, ji, f0 as int);
                assert(qsum(lk, f0 as int, f0 + 1) == lk[f0 as int].2) by {
                    assert(qsum(lk, f0 as int, f0 as int) == 0);
                }
            }
            let cap = look[f0].2 as usize;
            let task = JoinTask { cx, ji: clone_ji(&ji), f0, f1: f0 + 1, buf: CBuf::new(cap) };
            proof { lemma_ji_eq(cx@, ji, task.ji); }
            tasks.push(task);
            proof { starts = starts.push(f0 as int); }
            f0 = f0 + 1;
        }
    }
    let nt = tasks.len();
    let ghost ts = tasks@;
    let outs = match run_tasks(dispatch, workers, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    // Concatenate in task order (popped from the back into `rev`, then forward).
    let mut outs = outs;
    let ghost os = outs@;
    let mut rev: Vec<CBuf> = Vec::new();
    while outs.len() > 0
        invariant
            outs@ == os.subrange(0, outs@.len() as int), rev@.len() + outs@.len() == os.len(),
            forall|j: int| 0 <= j < rev@.len() ==> #[trigger] rev@[j] == os[os.len() - 1 - j],
        decreases outs@.len(),
    {
        let o = outs.pop().unwrap();
        rev.push(o);
    }
    // The task outputs in task order (no copy): their concatenation is the contributions of filings [0, nf).
    let mut out: Vec<CBuf> = Vec::new();
    let mut k: usize = 0;
    proof { assert(cflat(out@) =~= Seq::<Contrib>::empty()); assert(cs_seq(cflat(out@)) =~= Seq::<CS>::empty()); }
    while rev.len() > 0
        invariant
            join_in_ok(cx@, ji), nf == cx@.fil.len(), os.len() == nt, ts.len() == nt, rev@.len() + k == nt, k <= nt,
            forall|j: int| 0 <= j < rev@.len() ==> #[trigger] rev@[j] == os[os.len() - 1 - j],
            forall|j: int| 0 <= j < nt ==> (#[trigger] ts[j]).post(os[j]) && ts[j].pre() && ts[j].cx == cx && ji_eq(ts[j].ji, ji)
                && ts[j].f0 == starts[j] && ts[j].f1 == (if j + 1 < nt { starts[j + 1] } else { nf as int }),
            starts.len() == nt, nt > 0 ==> starts[0] == 0, nt == 0 ==> nf == 0,
            k < nt ==> seg_ok(cx@, ji.ntl, 0, starts[k as int], cflat(out@)),
            k < nt ==> cflat(out@).len() <= qsum(lk, 0, starts[k as int]),
            k == nt ==> seg_ok(cx@, ji.ntl, 0, nf as int, cflat(out@)),
            k == nt ==> cflat(out@).len() <= qsum(lk, 0, nf as int),
            lk == ji.look@,
        decreases rev@.len(),
    {
        let b = rev.pop().unwrap();
        proof { assert(b == os[k as int]); assert(ts[k as int].post(b)); }
        let v = b;
        let ghost before = cflat(out@);
        let ghost vv = v.view();
        let ghost (a0, a1) = (ts[k as int].f0 as int, ts[k as int].f1 as int);
        proof {
            assert(a0 <= a1 <= nf);
            if k == 0 { assert(seg_ok(cx@, ji.ntl, 0, 0, before)) by { assert(before =~= Seq::<Contrib>::empty()); } }
            lemma_seg_append(cx@, ji.ntl, 0, a0, a1, before, vv);
            lemma_cflat_push(out@, v);
            lemma_rsum_split(0, a0, a1, qof(lk));
        }
        out.push(v);
        k = k + 1;
    }
    proof {
        if nt == 0 { assert(cflat(out@) =~= Seq::<Contrib>::empty()); }
        assert(total as int == qsum(lk, 0, nf as int));
    }
    if total > usize::MAX as u128 {
        // (Never expected.) One vector, whose length is a vector length.
        let one = CBuf::merge_all(out);
        let _len = one.len();
        out = Vec::new();
        proof { lemma_cflat_push(out@, one); assert(cflat(out@.push(one)) =~= one.view()); assert(Seq::<CBuf>::empty().push(one) == seq![one]); }
        out.push(one);
        proof { assert(out@ =~= Seq::<CBuf>::empty().push(one)); }
    }
    proof {
        if nt == 0 { assert(cflat(out@) =~= Seq::<Contrib>::empty()); assert(seg_ok(cx@, ji.ntl, 0, 0, cflat(out@))) by { assert(cs_seq(cflat(out@)) =~= Seq::<CS>::empty()); } }
        lemma_all_seg(cx@, 0, nf as int);
        assert(all_cs(cx@, 0) =~= Seq::<CS>::empty());
        assert(seg_cs(cx@, 0, nf as int) =~= all_cs(cx@, nf as int));
    }
    Ok(out)
}

/// The value sum of a contribution is at most its absolute sum.
pub proof fn lemma_triangle(num: Seq<PartView>, rs: int, re: int, nq: int)
    ensures abs(run_pair_sum(num, rs, re, nq, coeff_phi())) <= run_pair_sum(num, rs, re, nq, abs_phi()),
    decreases re - rs,
{
    if re > rs {
        lemma_triangle(num, rs, re - 1, nq);
    }
}

/// A constant-one range sum is the range length.
proof fn lemma_rsum_const1(lo: int, hi: int, h: spec_fn(int) -> int)
    requires lo <= hi, forall|i: int| lo <= i < hi ==> #[trigger] h(i) == 1,
    ensures rsum(lo, hi, h) == hi - lo,
    decreases hi - lo,
{
    if hi > lo { lemma_rsum_const1(lo, hi - 1, h); }
}

} // verus!
