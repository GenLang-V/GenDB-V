//! Per-call (tag, version) lookups of the pre pairs that the binding's pre rows use.
//!
//! For pre pair `q` with bytes `(tg, vr)`: its num pair code `t3c` (the one num pair with these bytes, or -1) and its
//! tag row `t6c` (the row at the first tag_tv `tv_order` position with these bytes, or -1), with the tlabel slot the
//! join needs (`tslot`: NONE for no row or an abstract one). Both are canonical (functions of the stored parts), so
//! every way of computing them agrees (`lemma_t3c_unique`, `lemma_t6c_first`).
//!
//! Only the pairs of the qualifying pre rows are looked up: a touch pass marks them in a bitmap (one bit per pre pair
//! code, one bitmap per task, OR-merged), the marked codes are listed in increasing order with a per-word prefix count
//! (the rank directory), and parallel tasks look up chunks of the list; consecutive codes share their tag-level
//! searches (one cached `TagLv`). The join finds a row's entry by rank and checks its key; a missed key (never, when
//! the bitmap covers the row) falls back to a direct lookup, so correctness never depends on the bitmap or the rank.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::{Dispatch, WorkerTask, fork_join, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::spec::text::lex_cmp;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::bridge::order::lemma_lex_cmp_antisym;
use crate::stores::num::interface as N;
use crate::stores::pre::interface as P;
use crate::stores::tag_tv::interface as T;
use crate::stores::num::interface::common::text::{text_entry, text_parts_wf, text_strictly_sorted, text_entry_of, lemma_dict_codes, lemma_lex_cmp_lt_trans};
use crate::agent::maps::{Dict, dict_wf, dentry};
use crate::agent::inputs::{dict_is, u64v, u8v, i32v};
use crate::agent::common::dictmap::{NONE, find_text_fast};
use crate::agent::common::bytecmp::fast_cmp;
use crate::agent::filings::lower_u64;
use crate::agent::mapfacts::tvi;
use crate::agent::levels::*;

verus! {

// ------------------------------------------------------------------------------------------------ canonical lookups

pub open spec fn tu64(tag: Seq<PartView>, k: usize) -> Seq<u64> { crate::stores::tag_tv::interface::common::cols::u64s(tag, k) }

/// Bytes of pre pair `q`.
pub open spec fn pq_tag(pre: Seq<PartView>, q: int) -> Seq<u8> {
    crate::stores::pre::interface::common::cols::list_entry(pre, P::P_TAG_OFF, pre_u64s(pre, P::P_PAIR_TAG)[q] as int)
}
pub open spec fn pq_ver(pre: Seq<PartView>, q: int) -> Seq<u8> {
    crate::stores::pre::interface::common::cols::list_entry(pre, P::P_VERSION_OFF, pre_u64s(pre, P::P_PAIR_VERSION)[q] as int)
}

/// Num pair `c` has the bytes `(tg, vr)`.
pub open spec fn npair_match(num: Seq<PartView>, tg: Seq<u8>, vr: Seq<u8>, c: int) -> bool {
    0 <= c < N::pair_count(num) && ntag_entry(num, c) == tg && nver_entry(num, c) == vr
}

/// The num pair code of `(tg, vr)`, -1 when absent.
pub open spec fn t3c(num: Seq<PartView>, tg: Seq<u8>, vr: Seq<u8>) -> int {
    if exists|c: int| npair_match(num, tg, vr, c) { choose|c: int| npair_match(num, tg, vr, c) } else { -1 }
}

/// `tv_order` position `k` of tag_tv holds a row with the bytes `(tg, vr)`.
pub open spec fn tpos_match(tag: Seq<PartView>, tg: Seq<u8>, vr: Seq<u8>, k: int) -> bool {
    &&& 0 <= k < T::row_count(tag)
    &&& ttag_entry(tag, tu64(tag, T::P_TV_ORDER)[k] as int) == tg
    &&& tver_entry(tag, tu64(tag, T::P_TV_ORDER)[k] as int) == vr
}

/// `k` is the first such position.
pub open spec fn tpos_first(tag: Seq<PartView>, tg: Seq<u8>, vr: Seq<u8>, k: int) -> bool {
    tpos_match(tag, tg, vr, k) && forall|j: int| 0 <= j < k ==> !#[trigger] tpos_match(tag, tg, vr, j)
}

/// The tag row of `(tg, vr)`: the row at its first position, -1 when absent.
pub open spec fn t6c(tag: Seq<PartView>, tg: Seq<u8>, vr: Seq<u8>) -> int {
    if exists|k: int| tpos_first(tag, tg, vr, k) {
        tu64(tag, T::P_TV_ORDER)[choose|k: int| tpos_first(tag, tg, vr, k)] as int
    } else {
        -1
    }
}

/// The tlabel slot a tag row contributes to (its tlabel code, or `ntl` for NULL), NONE for no row or an abstract one.
pub open spec fn tslot(tag: Seq<PartView>, ntl: int, tr: int) -> u64 {
    if tr >= 0 && tag_abstract(tag, tr) == 0 {
        if crate::stores::tag_tv::interface::common::text::u8_part(tag[T::P_TLABEL_VALID as int])[tr] == 0 {
            ntl as u64
        } else {
            tu64(tag, T::P_TLABEL_CODES)[tr]
        }
    } else {
        NONE
    }
}

/// The lookup result of pre pair `q`: num pair code and slot.
pub open spec fn pinfo_ok(num: Seq<PartView>, pre: Seq<PartView>, tag: Seq<PartView>, ntl: int, q: int, nq: u64, slot: u64) -> bool {
    &&& tvi(nq) == t3c(num, pq_tag(pre, q), pq_ver(pre, q))
    &&& slot == tslot(tag, ntl, t6c(tag, pq_tag(pre, q), pq_ver(pre, q)))
}

/// Two num pairs with the same bytes are the same pair.
proof fn lemma_npair_same(num: Seq<PartView>, a: int, b: int)
    requires
        N::num_layout_ok(num), 0 <= a < N::pair_count(num), 0 <= b < N::pair_count(num),
        ntag_entry(num, a) == ntag_entry(num, b), nver_entry(num, a) == nver_entry(num, b),
    ensures a == b,
{
    let pt = N::u64s(num, N::P_PAIR_TAG);
    let pv = N::u64s(num, N::P_PAIR_VERSION);
    assert(pt[a] < N::tag_count(num) && pv[a] < N::version_count(num));
    assert(pt[b] < N::tag_count(num) && pv[b] < N::version_count(num));
    lemma_dict_codes(crate::stores::num::interface::common::text::u64_part(num[N::P_TAG_OFF as int]),
        crate::stores::num::interface::common::text::u8_part(num[N::P_TAG_OFF + 1]), N::tag_count(num), pt[a] as int, pt[b] as int);
    lemma_dict_codes(crate::stores::num::interface::common::text::u64_part(num[N::P_VERSION_OFF as int]),
        crate::stores::num::interface::common::text::u8_part(num[N::P_VERSION_OFF + 1]), N::version_count(num), pv[a] as int, pv[b] as int);
    if a < b {
        assert(crate::stores::num::interface::common::runs::pair_lt(pt[a], pv[a], pt[b], pv[b]));
    }
    if b < a {
        assert(crate::stores::num::interface::common::runs::pair_lt(pt[b], pv[b], pt[a], pv[a]));
    }
}

/// `t3c` is the lookup `pair_found` describes.
pub proof fn lemma_t3c_found(num: Seq<PartView>, tg: Seq<u8>, vr: Seq<u8>)
    requires N::num_layout_ok(num),
    ensures pair_found(num, tg, vr, t3c(num, tg, vr)), t3c(num, tg, vr) < N::pair_count(num),
{
    if exists|c: int| npair_match(num, tg, vr, c) {
        let c = choose|c: int| npair_match(num, tg, vr, c);
        assert(npair_match(num, tg, vr, c));
    } else {
        assert forall|c: int| 0 <= c < N::pair_count(num) implies !(#[trigger] ntag_entry(num, c) == tg && nver_entry(num, c) == vr) by {
            if ntag_entry(num, c) == tg && nver_entry(num, c) == vr {
                assert(npair_match(num, tg, vr, c));
            }
        }
    }
}

/// Every lookup `pair_found` describes is `t3c`.
pub proof fn lemma_t3c_unique(num: Seq<PartView>, tg: Seq<u8>, vr: Seq<u8>, x: int)
    requires N::num_layout_ok(num), pair_found(num, tg, vr, x), x >= -1,
    ensures x == t3c(num, tg, vr),
{
    if x >= 0 {
        assert(npair_match(num, tg, vr, x));
        let c = choose|c: int| npair_match(num, tg, vr, c);
        lemma_npair_same(num, c, x);
    } else {
        assert forall|c: int| !npair_match(num, tg, vr, c) by {
            if npair_match(num, tg, vr, c) {
                assert(!(ntag_entry(num, c) == tg && nver_entry(num, c) == vr));
            }
        }
    }
}

/// A matching position has a first matching position.
proof fn lemma_first_exists(tag: Seq<PartView>, tg: Seq<u8>, vr: Seq<u8>, p: int)
    requires tpos_match(tag, tg, vr, p),
    ensures exists|k: int| tpos_first(tag, tg, vr, k),
    decreases p,
{
    if exists|j: int| 0 <= j < p && tpos_match(tag, tg, vr, j) {
        let j = choose|j: int| 0 <= j < p && tpos_match(tag, tg, vr, j);
        lemma_first_exists(tag, tg, vr, j);
    } else {
        assert(tpos_first(tag, tg, vr, p));
    }
}

/// `t6c` is a lookup `tag_found` describes.
pub proof fn lemma_t6c_found(tag: Seq<PartView>, tg: Seq<u8>, vr: Seq<u8>)
    requires T::tag_layout_ok(tag),
    ensures tag_found(tag, tg, vr, t6c(tag, tg, vr)), t6c(tag, tg, vr) < T::row_count(tag),
{
    let order = tu64(tag, T::P_TV_ORDER);
    let n = T::row_count(tag);
    crate::stores::tag_tv::interface::common::perm::lemma_permutation_facts(order, n as nat);
    if exists|k: int| tpos_first(tag, tg, vr, k) {
        let k = choose|k: int| tpos_first(tag, tg, vr, k);
        assert(order[k] < n);
    } else {
        assert forall|r: int| 0 <= r < n implies !(#[trigger] ttag_entry(tag, r) == tg && tver_entry(tag, r) == vr) by {
            if ttag_entry(tag, r) == tg && tver_entry(tag, r) == vr {
                let p = crate::stores::tag_tv::interface::common::perm::position_of(order, r);
                assert(tpos_match(tag, tg, vr, p));
                lemma_first_exists(tag, tg, vr, p);
            }
        }
    }
}

/// The first matching position determines `t6c`.
pub proof fn lemma_t6c_first(tag: Seq<PartView>, tg: Seq<u8>, vr: Seq<u8>, k: int)
    requires tpos_first(tag, tg, vr, k),
    ensures t6c(tag, tg, vr) == tu64(tag, T::P_TV_ORDER)[k] as int,
{
    let k2 = choose|k2: int| tpos_first(tag, tg, vr, k2);
    if k2 < k {
        assert(!tpos_match(tag, tg, vr, k2));
    }
    if k < k2 {
        assert(!tpos_match(tag, tg, vr, k));
    }
}

/// No matching position: `t6c` is -1.
pub proof fn lemma_t6c_none(tag: Seq<PartView>, tg: Seq<u8>, vr: Seq<u8>)
    requires forall|k: int| !#[trigger] tpos_match(tag, tg, vr, k),
    ensures t6c(tag, tg, vr) == -1,
{
}

// ------------------------------------------------------------------------------------------------ lookup inputs

/// The read-only inputs of a pair lookup.
#[derive(Clone, Copy)]
pub struct LkIn {
    pub ptag: Dict,
    pub pver: Dict,
    pub ppt: &'static [u64],
    pub ppv: &'static [u64],
    pub ppn: usize,
    pub ntag: Dict,
    pub nver: Dict,
    pub npt: &'static [u64],
    pub npv: &'static [u64],
    pub npn: usize,
    pub ttag: Dict,
    pub tver: Dict,
    pub tfirst: &'static [u64],
    pub tvver: &'static [u64],
    pub tord: &'static [u64],
    pub tabs: &'static [i32],
    pub tlv: &'static [u8],
    pub tlc: &'static [u64],
    pub tn: usize,
    pub ntl: u64,
}

pub open spec fn lk_in_ok(num: Seq<PartView>, pre: Seq<PartView>, tag: Seq<PartView>, x: LkIn) -> bool {
    &&& N::num_layout_ok(num) && P::pre_layout_ok(pre) && T::tag_layout_ok(tag)
    &&& dict_is(x.ptag, pre, P::P_TAG_OFF as int) && dict_is(x.pver, pre, P::P_VERSION_OFF as int)
    &&& x.ppt@ == pre_u64s(pre, P::P_PAIR_TAG) && x.ppv@ == pre_u64s(pre, P::P_PAIR_VERSION) && x.ppn == x.ppt@.len()
    &&& dict_is(x.ntag, num, N::P_TAG_OFF as int) && dict_is(x.nver, num, N::P_VERSION_OFF as int)
    &&& x.npt@ == N::u64s(num, N::P_PAIR_TAG) && x.npv@ == N::u64s(num, N::P_PAIR_VERSION) && x.npn == x.npt@.len()
    &&& dict_is(x.ttag, tag, T::P_TAG_OFF as int) && dict_is(x.tver, tag, T::P_VERSION_OFF as int)
    &&& x.tfirst@ == tu64(tag, T::P_TAG_FIRST) && x.tvver@ == tu64(tag, T::P_TV_VERSION) && x.tord@ == tu64(tag, T::P_TV_ORDER)
    &&& x.tabs@ == crate::stores::tag_tv::interface::common::cols::i32_part(tag[T::P_ABSTRACT as int])
    &&& x.tlv@ == crate::stores::tag_tv::interface::common::text::u8_part(tag[T::P_TLABEL_VALID as int])
    &&& x.tlc@ == tu64(tag, T::P_TLABEL_CODES)
    &&& x.tn == T::row_count(tag)
    &&& x.ntl as int == crate::stores::tag_tv::interface::common::cols::text_count(tag, T::P_TLABEL_OFF as int)
}

/// The dictionaries' entries are the interfaces' entries.
proof fn lemma_entries(num: Seq<PartView>, pre: Seq<PartView>, tag: Seq<PartView>, x: LkIn)
    requires lk_in_ok(num, pre, tag, x),
    ensures
        forall|q: int| #[trigger] pq_tag(pre, q) == dentry(x.ptag, x.ppt@[q] as int),
        forall|q: int| #[trigger] pq_ver(pre, q) == dentry(x.pver, x.ppv@[q] as int),
        forall|c: int| #[trigger] ntag_entry(num, c) == dentry(x.ntag, x.npt@[c] as int),
        forall|c: int| #[trigger] nver_entry(num, c) == dentry(x.nver, x.npv@[c] as int),
        forall|r: int| #[trigger] ttag_entry(tag, r) == dentry(x.ttag, tu64(tag, T::P_TAG_CODES)[r] as int),
        forall|r: int| #[trigger] tver_entry(tag, r) == dentry(x.tver, tu64(tag, T::P_VERSION_CODES)[r] as int),
{
}

// ------------------------------------------------------------------------------------------------ tag level

/// The searches shared by the pairs of one pre tag code `ptc` (bytes `tg`): the position `npos` of `tg` in num's tag
/// dictionary (the number of entries below it; its code `ntc` when present) and the first num pair `na` of a tag code
/// at least `npos` (with `nb`, the pairs of `ntc` are `[na, nb)`); its tag_tv tag code and `tv_order` range. The
/// positions only grow with `tg`, so the next (larger) pre tag searches forward from them (`tag_level_from`).
#[derive(Clone, Copy)]
pub struct TagLv {
    pub ptc: u64,
    pub npos: usize,
    pub ntc: u64,
    pub na: usize,
    pub nb: usize,
    pub ttc: u64,
    pub ta: usize,
    pub tb: usize,
}

/// Search start positions for tag bytes `tg`: num tag entries below `npos` sort before `tg`, num pairs below `na` have a
/// tag code below `npos`.
pub open spec fn from_ok(x: LkIn, tg: Seq<u8>, npos: int, na: int) -> bool {
    &&& 0 <= npos <= x.ntag.n && 0 <= na <= x.npt@.len()
    &&& forall|k: int| 0 <= k < npos ==> lex_cmp(#[trigger] dentry(x.ntag, k), tg) < 0
    &&& forall|c: int| 0 <= c < na ==> #[trigger] x.npt@[c] < npos
}

pub open spec fn taglv_ok(x: LkIn, t: TagLv) -> bool {
    let tg = dentry(x.ptag, t.ptc as int);
    &&& t.ptc < x.ptag.n
    &&& from_ok(x, tg, t.npos as int, t.na as int)
    &&& t.ntc == NONE ==> forall|c: int| 0 <= c < x.ntag.n ==> #[trigger] dentry(x.ntag, c) != tg
    &&& t.ntc != NONE ==> {
        &&& t.ntc == t.npos && t.ntc < x.ntag.n && dentry(x.ntag, t.ntc as int) == tg
        &&& t.na <= t.nb <= x.npt@.len()
        &&& forall|c: int| 0 <= c < x.npt@.len() ==> (#[trigger] x.npt@[c] == t.ntc <==> t.na <= c < t.nb)
    }
    &&& t.ttc == NONE ==> forall|c: int| 0 <= c < x.ttag.n ==> #[trigger] dentry(x.ttag, c) != tg
    &&& t.ttc != NONE ==> {
        &&& t.ttc < x.ttag.n && dentry(x.ttag, t.ttc as int) == tg
        &&& t.ta as int == x.tfirst@[t.ttc as int] && t.tb as int == x.tfirst@[t.ttc + 1]
    }
}

/// The tag_tv part of a tag level (all that `tag_row` reads): tag_tv's code of the pre tag and its `tv_order` range.
pub open spec fn taglv_tag_ok(x: LkIn, t: TagLv) -> bool {
    let tg = dentry(x.ptag, t.ptc as int);
    &&& t.ptc < x.ptag.n
    &&& t.ttc == NONE ==> forall|c: int| 0 <= c < x.ttag.n ==> #[trigger] dentry(x.ttag, c) != tg
    &&& t.ttc != NONE ==> {
        &&& t.ttc < x.ttag.n && dentry(x.ttag, t.ttc as int) == tg
        &&& t.ta as int == x.tfirst@[t.ttc as int] && t.tb as int == x.tfirst@[t.ttc + 1]
    }
}

/// Value `k` of a dictionary equals `key`.
fn entry_is(d: &Dict, k: usize, key: &[u8], key_len: usize) -> (r: bool)
    requires dict_wf(*d), key_len == key@.len(),
    ensures r == (k < d.n && dentry(*d, k as int) == key@),
    no_unwind
{
    if k >= d.n {
        return false;
    }
    let (e, en) = text_entry_of(d.off, d.bytes, d.n, k);
    let c = fast_cmp(e, en, key, key_len);
    proof { lemma_lex_cmp_zero(e@, key@); }
    c == 0
}

/// The code of `key` in a dictionary, trying `h` first.
fn code_hint(d: &Dict, h: usize, key: &[u8], key_len: usize) -> (r: u64)
    requires dict_wf(*d), key_len == key@.len(),
    ensures
        r == NONE ==> forall|c: int| 0 <= c < d.n ==> #[trigger] dentry(*d, c) != key@,
        r != NONE ==> r < d.n && dentry(*d, r as int) == key@,
    no_unwind
{
    if entry_is(d, h, key, key_len) {
        return h as u64;
    }
    match find_text_fast(d.off, d.bytes, d.n, key, key_len) {
        Some(c) => c as u64,
        None => NONE,
    }
}

/// In a sorted dictionary, entries from a position whose entry is not below `key` are not below it.
proof fn lemma_above_from(d: Dict, key: Seq<u8>, p: int)
    requires dict_wf(d), 0 <= p < d.n, lex_cmp(dentry(d, p), key) >= 0,
    ensures forall|k: int| p <= k < d.n ==> lex_cmp(#[trigger] dentry(d, k), key) >= 0,
{
    assert forall|k: int| p <= k < d.n implies lex_cmp(#[trigger] dentry(d, k), key) >= 0 by {
        if k > p {
            let (e, f) = (dentry(d, p), dentry(d, k));
            assert(lex_cmp(e, f) < 0);
            lemma_lex_cmp_antisym(e, f);
            lemma_lex_cmp_antisym(key, e);
            lemma_lex_cmp_antisym(key, f);
            if lex_cmp(f, key) < 0 {
                lemma_lex_cmp_lt_trans(e, f, key);
            }
        }
    }
}

/// The first position at or after `from` whose entry is not below `key` (every entry before `from` is below it):
/// exponential probes forward, then a binary search.
fn gallop_text(d: &Dict, from: usize, key: &[u8], key_len: usize) -> (r: usize)
    requires
        dict_wf(*d), key_len == key@.len(), from <= d.n,
        forall|k: int| 0 <= k < from ==> lex_cmp(#[trigger] dentry(*d, k), key@) < 0,
    ensures
        from <= r <= d.n,
        forall|k: int| 0 <= k < r ==> lex_cmp(#[trigger] dentry(*d, k), key@) < 0,
        forall|k: int| r <= k < d.n ==> lex_cmp(#[trigger] dentry(*d, k), key@) >= 0,
    no_unwind
{
    let n = d.n;
    let mut lo = from;
    let mut hi = n;
    let mut step: usize = 1;
    // Probe `lo + step - 1` with doubling steps until an entry not below `key` (or the end).
    while lo < hi
        invariant
            dict_wf(*d), key_len == key@.len(), from <= lo <= hi <= n, n == d.n, step >= 1,
            forall|k: int| 0 <= k < lo ==> lex_cmp(#[trigger] dentry(*d, k), key@) < 0,
            forall|k: int| hi <= k < n ==> lex_cmp(#[trigger] dentry(*d, k), key@) >= 0,
        decreases hi - lo,
    {
        let p = if step <= hi - lo { lo + step - 1 } else { hi - 1 };
        let (e, en) = text_entry_of(d.off, d.bytes, n, p);
        let c = fast_cmp(e, en, key, key_len);
        if c < 0 {
            proof {
                assert forall|k: int| 0 <= k <= p implies lex_cmp(#[trigger] dentry(*d, k), key@) < 0 by {
                    if lo <= k < p {
                        assert(lex_cmp(dentry(*d, k), dentry(*d, p as int)) < 0);
                        lemma_lex_cmp_lt_trans(dentry(*d, k), dentry(*d, p as int), key@);
                    }
                }
            }
            lo = p + 1;
            if step < 0x1000_0000 { step = step * 2; }
        } else {
            proof { lemma_above_from(*d, key@, p as int); }
            hi = p;
            // Binary search what is left.
            step = 1;
            while lo < hi
                invariant
                    dict_wf(*d), key_len == key@.len(), from <= lo <= hi <= n, n == d.n,
                    forall|k: int| 0 <= k < lo ==> lex_cmp(#[trigger] dentry(*d, k), key@) < 0,
                    forall|k: int| hi <= k < n ==> lex_cmp(#[trigger] dentry(*d, k), key@) >= 0,
                decreases hi - lo,
            {
                let m = lo + (hi - lo) / 2;
                let (e2, en2) = text_entry_of(d.off, d.bytes, n, m);
                let c2 = fast_cmp(e2, en2, key, key_len);
                if c2 < 0 {
                    proof {
                        assert forall|k: int| 0 <= k <= m implies lex_cmp(#[trigger] dentry(*d, k), key@) < 0 by {
                            if lo <= k < m {
                                assert(lex_cmp(dentry(*d, k), dentry(*d, m as int)) < 0);
                                lemma_lex_cmp_lt_trans(dentry(*d, k), dentry(*d, m as int), key@);
                            }
                        }
                    }
                    lo = m + 1;
                } else {
                    proof { lemma_above_from(*d, key@, m as int); }
                    hi = m;
                }
            }
            return lo;
        }
    }
    lo
}

/// The first position at or after `from` whose value is at least `key` in a nondecreasing array (every value before
/// `from` is below `key`): exponential probes forward, then a binary search.
fn gallop_u64(v: &[u64], n: usize, from: usize, key: u64) -> (r: usize)
    requires
        n == v@.len(), from <= v@.len(),
        forall|a: int, b: int| 0 <= a < b < v@.len() ==> #[trigger] v@[a] <= #[trigger] v@[b],
        forall|k: int| 0 <= k < from ==> #[trigger] v@[k] < key,
    ensures
        from <= r <= v@.len(),
        forall|k: int| 0 <= k < r ==> #[trigger] v@[k] < key,
        forall|k: int| r <= k < v@.len() ==> #[trigger] v@[k] >= key,
    no_unwind
{
    let mut lo = from;
    let mut hi = n;
    let mut step: usize = 1;
    while lo < hi
        invariant
            from <= lo <= hi <= n, n == v@.len(), step >= 1,
            forall|a: int, b: int| 0 <= a < b < v@.len() ==> #[trigger] v@[a] <= #[trigger] v@[b],
            forall|k: int| 0 <= k < lo ==> #[trigger] v@[k] < key,
            forall|k: int| hi <= k < n ==> #[trigger] v@[k] >= key,
        decreases hi - lo,
    {
        let p = if step <= hi - lo { lo + step - 1 } else { hi - 1 };
        if v[p] < key {
            proof { assert forall|k: int| 0 <= k <= p implies #[trigger] v@[k] < key by { if k < p { assert(v@[k] <= v@[p as int]); } } }
            lo = p + 1;
            if step < 0x1000_0000 { step = step * 2; }
        } else {
            proof { assert forall|k: int| p <= k < n implies #[trigger] v@[k] >= key by { if k > p { assert(v@[p as int] <= v@[k]); } } }
            hi = p;
            let r = lower_u64(v, lo, hi, key);
            return r;
        }
    }
    lo
}

/// The tag-level searches of pre tag code `ptc`, from start positions valid for its bytes.
pub fn tag_level_from(x: &LkIn, ptc: u64, npos0: usize, na0: usize, Ghost(num): Ghost<Seq<PartView>>,
    Ghost(pre): Ghost<Seq<PartView>>, Ghost(tag): Ghost<Seq<PartView>>) -> (t: TagLv)
    requires lk_in_ok(num, pre, tag, *x), ptc < x.ptag.n, from_ok(*x, dentry(x.ptag, ptc as int), npos0 as int, na0 as int),
    ensures taglv_ok(*x, t), t.ptc == ptc,
    no_unwind
{
    let (tg, tgn) = text_entry_of(x.ptag.off, x.ptag.bytes, x.ptag.n, ptc as usize);
    let ghost npt = x.npt@;
    proof {
        // Num pair tag codes are nondecreasing.
        assert forall|a: int, b: int| 0 <= a < b < npt.len() implies #[trigger] npt[a] <= #[trigger] npt[b] by {
            assert(crate::stores::num::interface::common::runs::pair_lt(npt[a], x.npv@[a], npt[b], x.npv@[b]));
        }
    }
    let npos = gallop_text(&x.ntag, npos0, tg, tgn);
    let found = npos < x.ntag.n && entry_is(&x.ntag, npos, tg, tgn);
    proof {
        if !found {
            assert forall|c: int| 0 <= c < x.ntag.n implies #[trigger] dentry(x.ntag, c) != tg@ by {
                lemma_lex_cmp_zero(dentry(x.ntag, c), tg@);
                if c > npos {
                    assert(lex_cmp(dentry(x.ntag, npos as int), dentry(x.ntag, c)) < 0);
                    lemma_lex_cmp_antisym(dentry(x.ntag, npos as int), dentry(x.ntag, c));
                    lemma_lex_cmp_zero(dentry(x.ntag, npos as int), tg@);
                    lemma_lex_cmp_antisym(tg@, dentry(x.ntag, npos as int));
                    if dentry(x.ntag, c) == tg@ {
                        lemma_lex_cmp_zero(tg@, tg@);
                        lemma_lex_cmp_lt_trans(dentry(x.ntag, npos as int), tg@, tg@);
                    }
                }
            }
        }
    }
    let na = gallop_u64(x.npt, x.npn, na0, npos as u64);
    let mut ntc: u64 = NONE;
    let mut nb: usize = na;
    if found {
        let b = gallop_u64(x.npt, x.npn, na, npos as u64 + 1);
        proof {
            assert forall|k: int| 0 <= k < npt.len() implies (#[trigger] npt[k] == npos as u64 <==> na <= k < b) by {
                if k < na { assert(npt[k] < npos as u64); }
                if k >= b { assert(npt[k] >= npos as u64 + 1); }
            }
        }
        ntc = npos as u64;
        nb = b;
    }
    // tag_tv's tag dictionary is usually pre's: try the same code first.
    let ttc = code_hint(&x.ttag, ptc as usize, tg, tgn);
    let mut ta: usize = 0;
    let mut tb: usize = 0;
    if ttc != NONE {
        proof {
            assert(x.tfirst@.len() == x.ttag.n + 1);
            assert(x.tfirst@[ttc as int] <= x.tn && x.tfirst@[ttc + 1] <= x.tn);
        }
        ta = x.tfirst[ttc as usize] as usize;
        tb = x.tfirst[ttc as usize + 1] as usize;
    }
    TagLv { ptc, npos, ntc, na, nb, ttc, ta, tb }
}

/// Start positions for a larger pre tag code: those of the previous one.
proof fn lemma_from_next(x: LkIn, t: TagLv, ptc: u64)
    requires taglv_ok(x, t), t.ptc < ptc < x.ptag.n, dict_wf(x.ptag), dict_wf(x.ntag),
    ensures from_ok(x, dentry(x.ptag, ptc as int), t.npos as int, t.na as int),
{
    let tg0 = dentry(x.ptag, t.ptc as int);
    let tg = dentry(x.ptag, ptc as int);
    assert(lex_cmp(tg0, tg) < 0);
    assert forall|k: int| 0 <= k < t.npos implies lex_cmp(#[trigger] dentry(x.ntag, k), tg) < 0 by {
        lemma_lex_cmp_lt_trans(dentry(x.ntag, k), tg0, tg);
    }
}

// ------------------------------------------------------------------------------------------------ pair level

/// Num pair code of pre pair bytes `(tg, vb)` from the tag level.
fn num_pair(x: &LkIn, t: &TagLv, vb: &[u8], vbn: usize, Ghost(num): Ghost<Seq<PartView>>, Ghost(pre): Ghost<Seq<PartView>>,
    Ghost(tag): Ghost<Seq<PartView>>) -> (nq: u64)
    requires lk_in_ok(num, pre, tag, *x), taglv_ok(*x, *t), vbn == vb@.len(),
    ensures tvi(nq) == t3c(num, dentry(x.ptag, t.ptc as int), vb@),
    no_unwind
{
    let ghost tg = dentry(x.ptag, t.ptc as int);
    let ghost vr = vb@;
    proof { lemma_entries(num, pre, tag, *x); }
    if t.ntc == NONE {
        proof {
            assert forall|c: int| 0 <= c < N::pair_count(num) implies !(#[trigger] ntag_entry(num, c) == tg && nver_entry(num, c) == vr) by {
                assert(x.npt@[c] < x.ntag.n);
            }
            lemma_t3c_unique(num, tg, vr, -1);
        }
        return NONE;
    }
    let ghost ntc = t.ntc;
    let ghost npv = x.npv@;
    // Inside the tag's pairs the version values strictly increase.
    proof {
        assert forall|a: int, b: int| t.na <= a < b < t.nb implies
            lex_cmp(#[trigger] dentry(x.nver, npv[a] as int), #[trigger] dentry(x.nver, npv[b] as int)) < 0 by {
            assert(x.npt@[a] == ntc && x.npt@[b] == ntc);
            assert(crate::stores::num::interface::common::runs::pair_lt(x.npt@[a], npv[a], x.npt@[b], npv[b]));
            assert(npv[a] < x.nver.n && npv[b] < x.nver.n);
            lemma_dict_codes(x.nver.off@, x.nver.bytes@, x.nver.n as int, npv[a] as int, npv[b] as int);
        }
    }
    let mut lo = t.na;
    let mut hi = t.nb;
    while lo < hi
        invariant
            lk_in_ok(num, pre, tag, *x), taglv_ok(*x, *t), t.ntc == ntc, ntc != NONE, vbn == vb@.len(), vr == vb@,
            tg == dentry(x.ptag, t.ptc as int),
            npv == x.npv@,
            t.na <= lo <= hi <= t.nb,
            forall|a: int, b: int| t.na <= a < b < t.nb ==>
                lex_cmp(#[trigger] dentry(x.nver, npv[a] as int), #[trigger] dentry(x.nver, npv[b] as int)) < 0,
            forall|k: int| t.na <= k < lo ==> lex_cmp(#[trigger] dentry(x.nver, npv[k] as int), vr) < 0,
            forall|k: int| hi <= k < t.nb ==> lex_cmp(#[trigger] dentry(x.nver, npv[k] as int), vr) > 0,
        decreases hi - lo,
    {
        let m = lo + (hi - lo) / 2;
        proof {
            assert(x.npt@[m as int] == ntc);
            assert(x.npt@[m as int] < x.ntag.n && x.npv@[m as int] < x.nver.n);
        }
        let vcode = x.npv[m] as usize;
        let (e, en) = text_entry_of(x.nver.off, x.nver.bytes, x.nver.n, vcode);
        proof {
            assert(vcode as int == npv[m as int] as int);
            assert(e@ == dentry(x.nver, npv[m as int] as int));
        }
        let c = fast_cmp(e, en, vb, vbn);
        if c == 0 {
            proof {
                lemma_lex_cmp_zero(e@, vr);
                assert(t.ntc != NONE);
                assert(dentry(x.ntag, t.ntc as int) == tg);
                assert(dentry(x.ntag, ntc as int) == tg);
                assert(e@ == dentry(x.nver, npv[m as int] as int));
                assert(ntag_entry(num, m as int) == dentry(x.ntag, ntc as int));
                assert(nver_entry(num, m as int) == dentry(x.nver, npv[m as int] as int));
                assert(ntag_entry(num, m as int) == tg && nver_entry(num, m as int) == vr);
                lemma_t3c_unique(num, tg, vr, m as int);
            }
            return m as u64;
        } else if c < 0 {
            proof {
                assert forall|k: int| t.na <= k <= m implies lex_cmp(#[trigger] dentry(x.nver, npv[k] as int), vr) < 0 by {
                    if k < m { lemma_lex_cmp_lt_trans(dentry(x.nver, npv[k] as int), e@, vr); }
                }
            }
            lo = m + 1;
        } else {
            proof {
                assert forall|k: int| m <= k < t.nb implies lex_cmp(#[trigger] dentry(x.nver, npv[k] as int), vr) > 0 by {
                    if k > m {
                        let f = dentry(x.nver, npv[k] as int);
                        lemma_lex_cmp_antisym(e@, f);
                        lemma_lex_cmp_antisym(vr, e@);
                        lemma_lex_cmp_antisym(vr, f);
                        lemma_lex_cmp_lt_trans(vr, e@, f);
                    }
                }
            }
            hi = m;
        }
    }
    proof {
        assert forall|c: int| 0 <= c < N::pair_count(num) implies !(#[trigger] ntag_entry(num, c) == tg && nver_entry(num, c) == vr) by {
            if ntag_entry(num, c) == tg && nver_entry(num, c) == vr {
                assert(x.npt@[c] < x.ntag.n);
                lemma_dict_codes(x.ntag.off@, x.ntag.bytes@, x.ntag.n as int, x.npt@[c] as int, ntc as int);
                assert(t.na <= c < t.nb);
                lemma_lex_cmp_zero(dentry(x.nver, npv[c] as int), vr);
            }
        }
        lemma_t3c_unique(num, tg, vr, -1);
    }
    NONE
}

/// Tag row of pre pair bytes `(tg, vb)` from the tag level (`pvc`: pre's version code, the hint for tag_tv's).
fn tag_row(x: &LkIn, t: &TagLv, pvc: u64, vb: &[u8], vbn: usize, Ghost(num): Ghost<Seq<PartView>>,
    Ghost(pre): Ghost<Seq<PartView>>, Ghost(tag): Ghost<Seq<PartView>>) -> (tr: u64)
    requires lk_in_ok(num, pre, tag, *x), taglv_tag_ok(*x, *t), vbn == vb@.len(),
    ensures tvi(tr) == t6c(tag, dentry(x.ptag, t.ptc as int), vb@), tr == NONE || tr < x.tn,
    no_unwind
{
    let ghost tg = dentry(x.ptag, t.ptc as int);
    let ghost vr = vb@;
    let ghost order = tu64(tag, T::P_TV_ORDER);
    let ghost tcs = tu64(tag, T::P_TAG_CODES);
    let ghost vcs = tu64(tag, T::P_VERSION_CODES);
    let ghost n = T::row_count(tag);
    proof {
        lemma_entries(num, pre, tag, *x);
        crate::stores::tag_tv::interface::common::perm::lemma_permutation_facts(order, n as nat);
    }
    // The tag_tv version code of `vr`: usually pre's code or the next one.
    let tvc0 = code_hint(&x.tver, pvc as usize, vb, vbn);
    let tvc = if tvc0 != NONE { tvc0 } else if (pvc as usize) < usize::MAX { code_hint(&x.tver, pvc as usize + 1, vb, vbn) } else { NONE };
    if t.ttc == NONE || tvc == NONE {
        proof {
            assert forall|k: int| !#[trigger] tpos_match(tag, tg, vr, k) by {
                if tpos_match(tag, tg, vr, k) {
                    assert(order[k] < n);
                    assert(tcs[order[k] as int] < x.ttag.n && vcs[order[k] as int] < x.tver.n);
                }
            }
            lemma_t6c_none(tag, tg, vr);
        }
        return NONE;
    }
    let ghost ttc = t.ttc;
    let ghost tvv = x.tvver@;
    // The positions `[ta, tb)` are those of tag code `ttc`; their version codes are nondecreasing.
    proof {
        assert(x.tfirst@.len() == x.ttag.n + 1);
        assert forall|k: int| 0 <= k < n implies (t.ta <= k < t.tb <==> #[trigger] tcs[order[k] as int] == ttc) by {
            assert(T::tv_tag(tag, k) == tcs[order[k] as int]);
            assert(k < x.tfirst@[ttc as int] <==> T::tv_tag(tag, k) < ttc);
            assert(k < x.tfirst@[ttc + 1] <==> T::tv_tag(tag, k) < ttc + 1);
        }
        assert(t.ta <= x.tfirst@[ttc + 1] || t.ta == t.tb) by {
            if t.ta > t.tb {
                // first is monotone: the position tb would be below ta's cut.
                let k = t.tb as int;
                assert(k < n) by { assert(x.tfirst@[ttc as int] <= n); }
                assert(k < x.tfirst@[ttc as int] <==> T::tv_tag(tag, k) < ttc);
                assert(k < x.tfirst@[ttc + 1] <==> T::tv_tag(tag, k) < ttc + 1);
            }
        }
        assert(t.tb <= n);
        assert forall|a: int, b: int| t.ta <= a < b < t.tb implies #[trigger] tvv[a] <= #[trigger] tvv[b] by {
            assert(tcs[order[a] as int] == ttc && tcs[order[b] as int] == ttc);
            assert(T::pair_le(tcs[order[a] as int], vcs[order[a] as int], tcs[order[b] as int], vcs[order[b] as int]));
        }
    }
    if t.ta > t.tb {
        // Empty range (cannot happen with a monotone directory): nothing matches.
        proof {
            assert forall|k: int| !#[trigger] tpos_match(tag, tg, vr, k) by {
                if tpos_match(tag, tg, vr, k) {
                    assert(order[k] < n);
                    assert(tcs[order[k] as int] < x.ttag.n);
                    lemma_dict_codes(x.ttag.off@, x.ttag.bytes@, x.ttag.n as int, tcs[order[k] as int] as int, ttc as int);
                }
            }
            lemma_t6c_none(tag, tg, vr);
        }
        return NONE;
    }
    let lb = lower_u64(x.tvver, t.ta, t.tb, tvc);
    if lb < t.tb && x.tvver[lb] == tvc {
        proof {
            assert(order[lb as int] < n);
            assert(tvv[lb as int] == vcs[order[lb as int] as int]);
            assert(tpos_match(tag, tg, vr, lb as int));
            assert forall|j: int| 0 <= j < lb implies !#[trigger] tpos_match(tag, tg, vr, j) by {
                if tpos_match(tag, tg, vr, j) {
                    assert(order[j] < n);
                    assert(tcs[order[j] as int] < x.ttag.n && vcs[order[j] as int] < x.tver.n);
                    lemma_dict_codes(x.ttag.off@, x.ttag.bytes@, x.ttag.n as int, tcs[order[j] as int] as int, ttc as int);
                    lemma_dict_codes(x.tver.off@, x.tver.bytes@, x.tver.n as int, vcs[order[j] as int] as int, tvc as int);
                    assert(tvv[j] == vcs[order[j] as int]);
                }
            }
            lemma_t6c_first(tag, tg, vr, lb as int);
        }
        let r = x.tord[lb];
        return r;
    }
    proof {
        assert forall|k: int| !#[trigger] tpos_match(tag, tg, vr, k) by {
            if tpos_match(tag, tg, vr, k) {
                assert(order[k] < n);
                assert(tcs[order[k] as int] < x.ttag.n && vcs[order[k] as int] < x.tver.n);
                lemma_dict_codes(x.ttag.off@, x.ttag.bytes@, x.ttag.n as int, tcs[order[k] as int] as int, ttc as int);
                lemma_dict_codes(x.tver.off@, x.tver.bytes@, x.tver.n as int, vcs[order[k] as int] as int, tvc as int);
                assert(tvv[k] == vcs[order[k] as int]);
                if k > lb { assert(tvv[lb as int] <= tvv[k]); }
            }
        }
        lemma_t6c_none(tag, tg, vr);
    }
    NONE
}

/// The slot of a tag row (NONE for none or an abstract one).
fn slot_for(x: &LkIn, tr: u64, Ghost(tag): Ghost<Seq<PartView>>) -> (s: u64)
    requires T::tag_layout_ok(tag), x.tn == T::row_count(tag), tr == NONE || tr < x.tn,
        x.tabs@ == crate::stores::tag_tv::interface::common::cols::i32_part(tag[T::P_ABSTRACT as int]),
        x.tlv@ == crate::stores::tag_tv::interface::common::text::u8_part(tag[T::P_TLABEL_VALID as int]),
        x.tlc@ == tu64(tag, T::P_TLABEL_CODES),
    ensures s == tslot(tag, x.ntl as int, tvi(tr)),
    no_unwind
{
    if tr == NONE {
        return NONE;
    }
    let r = tr as usize;
    if x.tabs[r] != 0 {
        return NONE;
    }
    if x.tlv[r] == 0 { x.ntl } else { x.tlc[r] }
}

/// The tag_tv part of the tag level of pre tag code `ptc` (bytes `tg`).
fn tag_side(x: &LkIn, ptc: u64, tg: &[u8], tgn: usize, Ghost(num): Ghost<Seq<PartView>>, Ghost(pre): Ghost<Seq<PartView>>,
    Ghost(tag): Ghost<Seq<PartView>>) -> (t: TagLv)
    requires lk_in_ok(num, pre, tag, *x), ptc < x.ptag.n, tgn == tg@.len(), tg@ == dentry(x.ptag, ptc as int),
    ensures taglv_tag_ok(*x, t), t.ptc == ptc,
    no_unwind
{
    // tag_tv's tag dictionary is usually pre's: try the same code first.
    let ttc = code_hint(&x.ttag, ptc as usize, tg, tgn);
    let mut ta: usize = 0;
    let mut tb: usize = 0;
    if ttc != NONE {
        proof {
            assert(x.tfirst@.len() == x.ttag.n + 1);
            assert(x.tfirst@[ttc as int] <= x.tn && x.tfirst@[ttc + 1] <= x.tn);
        }
        ta = x.tfirst[ttc as usize] as usize;
        tb = x.tfirst[ttc as usize + 1] as usize;
    }
    TagLv { ptc, npos: 0, ntc: NONE, na: 0, nb: 0, ttc, ta, tb }
}

// ------------------------------------------------------------------------------------------------ absence at a guess

/// `(t1, v1)` sorts strictly before `(t2, v2)` (tag bytes first, then version bytes).
pub open spec fn ptxt_lt(t1: Seq<u8>, v1: Seq<u8>, t2: Seq<u8>, v2: Seq<u8>) -> bool {
    lex_cmp(t1, t2) < 0 || (t1 == t2 && lex_cmp(v1, v2) < 0)
}

/// The order is asymmetric and irreflexive.
proof fn lemma_ptxt_asym(t1: Seq<u8>, v1: Seq<u8>, t2: Seq<u8>, v2: Seq<u8>)
    requires ptxt_lt(t1, v1, t2, v2),
    ensures !ptxt_lt(t2, v2, t1, v1), !(t1 == t2 && v1 == v2),
{
    lemma_lex_cmp_antisym(t1, t2);
    lemma_lex_cmp_antisym(v1, v2);
    lemma_lex_cmp_zero(t1, t2);
    lemma_lex_cmp_zero(v1, v2);
}

/// Num pairs in code order have strictly increasing bytes: pair codes increase as (tag code, version code), and code
/// order is byte order in both dictionaries.
proof fn lemma_npair_order(num: Seq<PartView>, a: int, b: int)
    requires N::num_layout_ok(num), 0 <= a < b < N::pair_count(num),
    ensures ptxt_lt(ntag_entry(num, a), nver_entry(num, a), ntag_entry(num, b), nver_entry(num, b)),
{
    let pt = N::u64s(num, N::P_PAIR_TAG);
    let pv = N::u64s(num, N::P_PAIR_VERSION);
    assert(pt[a] < N::tag_count(num) && pv[a] < N::version_count(num));
    assert(pt[b] < N::tag_count(num) && pv[b] < N::version_count(num));
    assert(crate::stores::num::interface::common::runs::pair_lt(pt[a], pv[a], pt[b], pv[b]));
    lemma_dict_codes(crate::stores::num::interface::common::text::u64_part(num[N::P_TAG_OFF as int]),
        crate::stores::num::interface::common::text::u8_part(num[N::P_TAG_OFF + 1]), N::tag_count(num), pt[a] as int, pt[b] as int);
    lemma_dict_codes(crate::stores::num::interface::common::text::u64_part(num[N::P_VERSION_OFF as int]),
        crate::stores::num::interface::common::text::u8_part(num[N::P_VERSION_OFF + 1]), N::version_count(num), pv[a] as int, pv[b] as int);
}

/// The order is transitive.
proof fn lemma_ptxt_trans(t1: Seq<u8>, v1: Seq<u8>, t2: Seq<u8>, v2: Seq<u8>, t3: Seq<u8>, v3: Seq<u8>)
    requires ptxt_lt(t1, v1, t2, v2), ptxt_lt(t2, v2, t3, v3),
    ensures ptxt_lt(t1, v1, t3, v3),
{
    if lex_cmp(t1, t2) < 0 {
        if lex_cmp(t2, t3) < 0 { lemma_lex_cmp_lt_trans(t1, t2, t3); }
    } else if lex_cmp(t2, t3) >= 0 {
        lemma_lex_cmp_lt_trans(v1, v2, v3);
    }
}

/// Num pair `c` sorts before `(tg, vr)`.
pub open spec fn nbelow(num: Seq<PartView>, c: int, tg: Seq<u8>, vr: Seq<u8>) -> bool {
    ptxt_lt(ntag_entry(num, c), nver_entry(num, c), tg, vr)
}

/// Num pair `c` sorts at or after `(tg, vr)`.
pub open spec fn natleast(num: Seq<PartView>, c: int, tg: Seq<u8>, vr: Seq<u8>) -> bool {
    ptxt_lt(tg, vr, ntag_entry(num, c), nver_entry(num, c)) || (ntag_entry(num, c) == tg && nver_entry(num, c) == vr)
}

/// A pair below the key has only pairs below the key before it.
proof fn lemma_below_down(num: Seq<PartView>, m: int, tg: Seq<u8>, vr: Seq<u8>)
    requires N::num_layout_ok(num), 0 <= m < N::pair_count(num), nbelow(num, m, tg, vr),
    ensures forall|c: int| 0 <= c <= m ==> #[trigger] nbelow(num, c, tg, vr),
{
    assert forall|c: int| 0 <= c <= m implies #[trigger] nbelow(num, c, tg, vr) by {
        if c < m {
            lemma_npair_order(num, c, m);
            lemma_ptxt_trans(ntag_entry(num, c), nver_entry(num, c), ntag_entry(num, m), nver_entry(num, m), tg, vr);
        }
    }
}

/// A pair at or after the key has only such pairs after it.
proof fn lemma_atleast_up(num: Seq<PartView>, m: int, tg: Seq<u8>, vr: Seq<u8>)
    requires N::num_layout_ok(num), 0 <= m < N::pair_count(num), natleast(num, m, tg, vr),
    ensures forall|c: int| m <= c < N::pair_count(num) ==> #[trigger] natleast(num, c, tg, vr),
{
    assert forall|c: int| m <= c < N::pair_count(num) implies #[trigger] natleast(num, c, tg, vr) by {
        if c > m {
            lemma_npair_order(num, m, c);
            if !(ntag_entry(num, m) == tg && nver_entry(num, m) == vr) {
                lemma_ptxt_trans(tg, vr, ntag_entry(num, m), nver_entry(num, m), ntag_entry(num, c), nver_entry(num, c));
            }
        }
    }
}

/// The byte order of num pair `c` against `(tg, vr)`: negative below, zero equal, positive above (`None` for a code
/// outside its dictionary, which well-formed parts never have).
fn npair_cmp(x: &LkIn, c: usize, tg: &[u8], tgn: usize, vr: &[u8], vrn: usize, Ghost(num): Ghost<Seq<PartView>>,
    Ghost(pre): Ghost<Seq<PartView>>, Ghost(tag): Ghost<Seq<PartView>>) -> (r: Option<i8>)
    requires lk_in_ok(num, pre, tag, *x), c < x.npn, tgn == tg@.len(), vrn == vr@.len(),
    ensures
        r matches Some(s) ==> (s < 0 ==> nbelow(num, c as int, tg@, vr@))
            && (s == 0 ==> ntag_entry(num, c as int) == tg@ && nver_entry(num, c as int) == vr@)
            && (s > 0 ==> ptxt_lt(tg@, vr@, ntag_entry(num, c as int), nver_entry(num, c as int))),
    no_unwind
{
    proof {
        lemma_entries(num, pre, tag, *x);
        assert(x.npv@.len() == N::pair_count(num));
    }
    let tc = x.npt[c] as usize;
    let vc = x.npv[c] as usize;
    if tc >= x.ntag.n || vc >= x.nver.n {
        return None;
    }
    let (e, en) = text_entry_of(x.ntag.off, x.ntag.bytes, x.ntag.n, tc);
    let t = fast_cmp(e, en, tg, tgn);
    proof {
        lemma_lex_cmp_antisym(e@, tg@);
        lemma_lex_cmp_zero(e@, tg@);
        assert(e@ == ntag_entry(num, c as int));
    }
    if t != 0 {
        return Some(t);
    }
    let (f, fln) = text_entry_of(x.nver.off, x.nver.bytes, x.nver.n, vc);
    let v = fast_cmp(f, fln, vr, vrn);
    proof {
        lemma_lex_cmp_antisym(f@, vr@);
        lemma_lex_cmp_zero(f@, vr@);
        assert(f@ == nver_entry(num, c as int));
    }
    Some(v)
}

/// The num pair of the bytes `(tg, vr)` by a search of num's sorted pair list around the guess `h`: an exponential
/// search away from `h` (forward when pair `h` sorts below the key, else backward) brackets the key's position,
/// then a binary search finds it. `Some(code)`, `Some(NONE)` when no num pair has these bytes, `None` only for a
/// code outside its dictionary.
fn npair_search(x: &LkIn, h: usize, tg: &[u8], tgn: usize, vr: &[u8], vrn: usize, Ghost(num): Ghost<Seq<PartView>>,
    Ghost(pre): Ghost<Seq<PartView>>, Ghost(tag): Ghost<Seq<PartView>>) -> (r: Option<u64>)
    requires lk_in_ok(num, pre, tag, *x), tgn == tg@.len(), vrn == vr@.len(),
    ensures
        r matches Some(c) ==> (c != NONE ==> npair_match(num, tg@, vr@, c as int))
            && (c == NONE ==> forall|k: int| !#[trigger] npair_match(num, tg@, vr@, k)),
    no_unwind
{
    let ghost (key_t, key_v) = (tg@, vr@);
    let n = x.npn;
    proof { assert(n == N::pair_count(num)); }
    if n == 0 {
        return Some(NONE);
    }
    let h = if h < n { h } else { n - 1 };
    // Invariant of the search: pairs below `lo` sort below the key, pairs from `hi` on at or after it.
    let mut lo: usize = 0;
    let mut hi: usize = n;
    let mut fwd: bool = true;
    match npair_cmp(x, h, tg, tgn, vr, vrn, Ghost(num), Ghost(pre), Ghost(tag)) {
        None => { return None; },
        Some(s) => {
            if s == 0 {
                return Some(h as u64);
            }
            if s < 0 {
                proof { lemma_below_down(num, h as int, key_t, key_v); }
                lo = h + 1;
                hi = n;
                fwd = true;
            } else {
                proof { lemma_atleast_up(num, h as int, key_t, key_v); }
                lo = 0;
                hi = h;
                fwd = false;
            }
        },
    }
    let mut gallop = true;
    let mut step: usize = 1;
    while lo < hi
        invariant
            lk_in_ok(num, pre, tag, *x), n == x.npn, n == N::pair_count(num), lo <= hi <= n, tg@ == key_t, vr@ == key_v,
            tgn == tg@.len(), vrn == vr@.len(), step >= 1,
            forall|c: int| 0 <= c < lo ==> #[trigger] nbelow(num, c, key_t, key_v),
            forall|c: int| hi <= c < n ==> #[trigger] natleast(num, c, key_t, key_v),
        decreases hi - lo,
    {
        let p = if gallop && hi - lo > step {
            if fwd { lo + step - 1 } else { hi - step }
        } else {
            lo + (hi - lo) / 2
        };
        match npair_cmp(x, p, tg, tgn, vr, vrn, Ghost(num), Ghost(pre), Ghost(tag)) {
            None => { return None; },
            Some(s) => {
                if s < 0 {
                    proof { lemma_below_down(num, p as int, key_t, key_v); }
                    lo = p + 1;
                    if !fwd { gallop = false; }
                } else {
                    proof { lemma_atleast_up(num, p as int, key_t, key_v); }
                    hi = p;
                    if fwd { gallop = false; }
                }
            },
        }
        if gallop && step < 0x1000_0000 {
            step = step * 2;
        }
    }
    // `lo` is the key's position: below it every pair sorts lower, at it the key or a higher pair.
    if lo == n {
        proof {
            assert forall|k: int| !#[trigger] npair_match(num, key_t, key_v, k) by {
                if npair_match(num, key_t, key_v, k) {
                    assert(nbelow(num, k, key_t, key_v));
                    lemma_ptxt_asym(ntag_entry(num, k), nver_entry(num, k), key_t, key_v);
                }
            }
        }
        return Some(NONE);
    }
    match npair_cmp(x, lo, tg, tgn, vr, vrn, Ghost(num), Ghost(pre), Ghost(tag)) {
        Some(s) => {
            if s == 0 {
                Some(lo as u64)
            } else if s > 0 {
                proof {
                    assert forall|k: int| !#[trigger] npair_match(num, key_t, key_v, k) by {
                        if npair_match(num, key_t, key_v, k) {
                            if k < lo {
                                assert(nbelow(num, k, key_t, key_v));
                                lemma_ptxt_asym(ntag_entry(num, k), nver_entry(num, k), key_t, key_v);
                            } else if k == lo {
                                lemma_ptxt_asym(key_t, key_v, ntag_entry(num, k), nver_entry(num, k));
                            } else {
                                lemma_npair_order(num, lo as int, k);
                                lemma_ptxt_trans(key_t, key_v, ntag_entry(num, lo as int), nver_entry(num, lo as int),
                                    ntag_entry(num, k), nver_entry(num, k));
                                lemma_ptxt_asym(key_t, key_v, ntag_entry(num, k), nver_entry(num, k));
                            }
                        }
                    }
                }
                Some(NONE)
            } else {
                None
            }
        },
        None => None,
    }
}

/// The lookup of pre pair `q`, its num pair searched around the guess `h` (`None` only for malformed codes).
pub fn pair_guess(x: &LkIn, q: usize, h: usize, Ghost(num): Ghost<Seq<PartView>>, Ghost(pre): Ghost<Seq<PartView>>,
    Ghost(tag): Ghost<Seq<PartView>>) -> (r: Option<(u64, u64)>)
    requires lk_in_ok(num, pre, tag, *x), q < x.ppt@.len(),
    ensures r matches Some(e) ==> pinfo_ok(num, pre, tag, x.ntl as int, q as int, e.0, e.1),
    no_unwind
{
    proof {
        lemma_entries(num, pre, tag, *x);
        assert(x.ppt@[q as int] < x.ptag.n);
        assert(x.ppv@[q as int] < x.pver.n);
    }
    let ptc = x.ppt[q];
    let (tg, tgn) = text_entry_of(x.ptag.off, x.ptag.bytes, x.ptag.n, ptc as usize);
    let pvc = x.ppv[q];
    let (vb, vbn) = text_entry_of(x.pver.off, x.pver.bytes, x.pver.n, pvc as usize);
    let nq = match npair_search(x, h, tg, tgn, vb, vbn, Ghost(num), Ghost(pre), Ghost(tag)) {
        Some(c) => c,
        None => { return None; },
    };
    proof {
        assert(pq_tag(pre, q as int) == tg@);
        assert(pq_ver(pre, q as int) == vb@);
    }
    if nq == NONE {
        proof { assert(!exists|c: int| npair_match(num, tg@, vb@, c)); }
    } else {
        proof {
            assert(pair_found(num, tg@, vb@, nq as int));
            lemma_t3c_unique(num, tg@, vb@, nq as int);
        }
    }
    let t = tag_side(x, ptc, tg, tgn, Ghost(num), Ghost(pre), Ghost(tag));
    let tr = tag_row(x, &t, pvc, vb, vbn, Ghost(num), Ghost(pre), Ghost(tag));
    let s = slot_for(x, tr, Ghost(tag));
    Some((nq, s))
}

/// The lookup of pre pair `q` with the tag level of its tag code.
pub fn pair_with(x: &LkIn, t: &TagLv, q: usize, Ghost(num): Ghost<Seq<PartView>>, Ghost(pre): Ghost<Seq<PartView>>,
    Ghost(tag): Ghost<Seq<PartView>>) -> (r: (u64, u64))
    requires lk_in_ok(num, pre, tag, *x), taglv_ok(*x, *t), q < x.ppt@.len(), t.ptc == x.ppt@[q as int],
    ensures pinfo_ok(num, pre, tag, x.ntl as int, q as int, r.0, r.1),
    no_unwind
{
    proof {
        lemma_entries(num, pre, tag, *x);
        assert(x.ppv@[q as int] < x.pver.n);
    }
    let pvc = x.ppv[q];
    let (vb, vbn) = text_entry_of(x.pver.off, x.pver.bytes, x.pver.n, pvc as usize);
    let nq = num_pair(x, t, vb, vbn, Ghost(num), Ghost(pre), Ghost(tag));
    let tr = tag_row(x, t, pvc, vb, vbn, Ghost(num), Ghost(pre), Ghost(tag));
    let s = slot_for(x, tr, Ghost(tag));
    (nq, s)
}

/// The lookup of pre pair `q` from scratch.
pub fn lookup_pair(x: &LkIn, q: usize, Ghost(num): Ghost<Seq<PartView>>, Ghost(pre): Ghost<Seq<PartView>>,
    Ghost(tag): Ghost<Seq<PartView>>) -> (r: (u64, u64))
    requires lk_in_ok(num, pre, tag, *x), q < x.ppt@.len(),
    ensures pinfo_ok(num, pre, tag, x.ntl as int, q as int, r.0, r.1),
    no_unwind
{
    proof { assert(x.ppt@[q as int] < x.ptag.n); }
    let t = tag_level_from(x, x.ppt[q], 0, 0, Ghost(num), Ghost(pre), Ghost(tag));
    pair_with(x, &t, q, Ghost(num), Ghost(pre), Ghost(tag))
}

// ------------------------------------------------------------------------------------------------ touch pass

/// Marks the pre pair codes of the qualifying pre rows of filings `[f0, f1)` in a bitmap (`out`, one bit per code).
/// The marks only steer the lookups; nothing is proved about them.
pub struct TouchTask {
    pub look: Arc<Vec<(u64, u64, u64)>>,
    pub f0: usize,
    pub f1: usize,
    pub adsh_subs: &'static [u64],
    pub sub_group: &'static [u64],
    pub sub_start: &'static [u64],
    pub ptv: &'static [u64],
    pub gqv: Arc<Vec<bool>>,
    pub out: Vec<u64>,
    /// The lengths of `adsh_subs`, `sub_group`, `sub_start`, `ptv`.
    pub lens: (usize, usize, usize, usize),
}

impl WorkerTask for TouchTask {
    type Output = Vec<u64>;

    open spec fn pre(&self) -> bool {
        &&& self.lens.0 == self.adsh_subs@.len() && self.lens.1 == self.sub_group@.len()
        &&& self.lens.2 == self.sub_start@.len() && self.lens.3 == self.ptv@.len()
    }

    open spec fn post(&self, out: Vec<u64>) -> bool {
        out@.len() == self.out@.len()
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.f0 as u64, self.f1 as u64)
    }

    fn run(self) -> (out: Vec<u64>) {
        let TouchTask { look, f0, f1, adsh_subs, sub_group, sub_start, ptv, gqv, out, lens } = self;
        let (nas, nsg, nss, nptv) = lens;
        let mut bits = out;
        let nw = bits.len();
        let look: &Vec<(u64, u64, u64)> = &*look;
        let gqv: &Vec<bool> = &*gqv;
        let nl = look.len();
        let mut f = f0;
        while f < f1 && f < nl
            invariant bits@.len() == nw, nl == look@.len(), nas == adsh_subs@.len(), nsg == sub_group@.len(),
                nss == sub_start@.len(), nptv == ptv@.len(),
            decreases f1 - f,
        {
            let (run, pc, _qn) = look[f];
            if run != NONE && pc < nas as u64 && (pc as usize) + 1 < nas {
                let s0 = adsh_subs[pc as usize] as usize;
                let s1 = adsh_subs[pc as usize + 1] as usize;
                let mut s = s0;
                while s < s1 && s < nsg && s + 1 < nss
                    invariant bits@.len() == nw, nas == adsh_subs@.len(), nsg == sub_group@.len(),
                        nss == sub_start@.len(), nptv == ptv@.len(),
                    decreases s1 - s,
                {
                    let g = sub_group[s] as usize;
                    if g < gqv.len() && gqv[g] {
                        let j1 = sub_start[s + 1] as usize;
                        let mut j = sub_start[s] as usize;
                        while j < j1 && j < nptv
                            invariant bits@.len() == nw, nptv == ptv@.len(),
                            decreases j1 - j,
                        {
                            let q = ptv[j];
                            let w = (q / 64) as usize;
                            if w < nw {
                                let b = bits[w] | (1u64 << (q % 64));
                                bits[w] = b;
                            }
                            j = j + 1;
                        }
                    }
                    s = s + 1;
                }
            }
            f = f + 1;
        }
        bits
    }
}

/// The OR of the tasks' bitmaps (each of `nw` words).
fn or_merge(maps: &Vec<Vec<u64>>, nw: usize) -> (r: Vec<u64>)
    ensures r@.len() == nw,
{
    let mut r: Vec<u64> = vec![0u64; nw];
    let nm = maps.len();
    let mut k: usize = 0;
    while k < nm
        invariant r@.len() == nw, nm == maps@.len(),
        decreases nm - k,
    {
        let m: &Vec<u64> = &maps[k];
        let mut w: usize = 0;
        while w < nw && w < m.len()
            invariant r@.len() == nw,
            decreases nw - w,
        {
            let b = r[w] | m[w];
            r[w] = b;
            w = w + 1;
        }
        k = k + 1;
    }
    r
}

/// The marked codes (below `np`) in increasing order, and per word the number of marked codes before it.
fn list_marked(bits: &Vec<u64>, np: usize) -> (r: (Vec<u64>, Vec<u64>))
    ensures
        forall|d: int| 0 <= d < r.0@.len() ==> #[trigger] r.0@[d] < np,
        r.1@.len() == bits@.len() + 1,
{
    let nw = bits.len();
    let mut keys: Vec<u64> = Vec::new();
    let mut pref: Vec<u64> = Vec::new();
    let mut w: usize = 0;
    while w < nw
        invariant
            w <= nw, nw == bits@.len(), pref@.len() == w,
            forall|d: int| 0 <= d < keys@.len() ==> #[trigger] keys@[d] < np,
        decreases nw - w,
    {
        pref.push(keys.len() as u64);
        let mut b = bits[w];
        // Codes beyond 2^58 are never pre pair codes; their words are skipped.
        let base: u64 = if (w as u64) < 0x0100_0000_0000_0000 { (w as u64) * 64 } else { 0 };
        let mut steps: usize = 0;
        if (w as u64) >= 0x0100_0000_0000_0000 { b = 0; }
        while b != 0 && steps < 64
            invariant forall|d: int| 0 <= d < keys@.len() ==> #[trigger] keys@[d] < np,
                base <= 0x4000_0000_0000_0000u64,
            decreases 64 - steps,
        {
            let tz = b.trailing_zeros() as u64;
            if tz < 64 {
                let q = base + tz;
                if q < np as u64 {
                    keys.push(q);
                }
                b = b & !(1u64 << tz);
            } else {
                b = 0;
            }
            steps = steps + 1;
        }
        w = w + 1;
    }
    pref.push(keys.len() as u64);
    (keys, pref)
}

/// Number of set bits of `b` (no specification: only a rank hint).
pub fn popcount(b: u64) -> (r: u64)
    no_unwind
{
    let x = b.wrapping_sub((b >> 1) & 0x5555_5555_5555_5555u64);
    let x = (x & 0x3333_3333_3333_3333u64).wrapping_add((x >> 2) & 0x3333_3333_3333_3333u64);
    let x = x.wrapping_add(x >> 4) & 0x0f0f_0f0f_0f0f_0f0fu64;
    x.wrapping_mul(0x0101_0101_0101_0101u64) >> 56
}

// ------------------------------------------------------------------------------------------------ lookups of the list

/// Looks up the marked codes `keys[d0, d1)` into `out` (key, num pair code, slot).
pub struct InfoTask {
    pub x: LkIn,
    pub keys: Arc<Vec<u64>>,
    pub d0: usize,
    pub d1: usize,
    pub out: Vec<(u64, u64, u64)>,
    pub num: Ghost<Seq<PartView>>,
    pub pre: Ghost<Seq<PartView>>,
    pub tag: Ghost<Seq<PartView>>,
}

pub open spec fn info_ok(num: Seq<PartView>, pre: Seq<PartView>, tag: Seq<PartView>, ntl: int, e: (u64, u64, u64)) -> bool {
    e.0 < P::pair_count(pre) && pinfo_ok(num, pre, tag, ntl, e.0 as int, e.1, e.2)
}

impl WorkerTask for InfoTask {
    type Output = Vec<(u64, u64, u64)>;

    open spec fn pre(&self) -> bool {
        &&& lk_in_ok(self.num@, self.pre@, self.tag@, self.x)
        &&& self.d0 <= self.d1 <= self.keys@.len()
        &&& self.out@.len() == self.d1 - self.d0
        &&& forall|d: int| 0 <= d < self.keys@.len() ==> #[trigger] self.keys@[d] < self.x.ppt@.len()
    }

    open spec fn post(&self, out: Vec<(u64, u64, u64)>) -> bool {
        &&& out@.len() == self.d1 - self.d0
        &&& forall|i: int| 0 <= i < out@.len() ==> info_ok(self.num@, self.pre@, self.tag@, self.x.ntl as int, #[trigger] out@[i])
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.d0 as u64, self.d1 as u64)
    }

    fn run(self) -> (out: Vec<(u64, u64, u64)>) {
        let InfoTask { x, keys, d0, d1, out, num, pre, tag } = self;
        let ghost (nv, pv, tv) = (num@, pre@, tag@);
        let mut out = out;
        let keys: &Vec<u64> = &*keys;
        proof { assert(P::pair_count(pv) == x.ppt@.len()); }
        let mut t = TagLv { ptc: NONE, npos: 0, ntc: NONE, na: 0, nb: 0, ttc: NONE, ta: 0, tb: 0 };
        let mut have = false;
        let mut dn: usize = 0;
        let mut up: usize = 0;
        let mut d = d0;
        while d < d1
            invariant
                lk_in_ok(nv, pv, tv, x), d0 <= d <= d1 <= keys@.len(), out@.len() == d1 - d0,
                forall|e: int| 0 <= e < keys@.len() ==> #[trigger] keys@[e] < x.ppt@.len(),
                P::pair_count(pv) == x.ppt@.len(),
                have ==> taglv_ok(x, t),
                forall|i: int| 0 <= i < d - d0 ==> info_ok(nv, pv, tv, x.ntl as int, #[trigger] out@[i]),
            decreases d1 - d,
        {
            let q = keys[d] as usize;
            // The guess: num pair codes follow pre pair codes up to an offset that changes only where one table has
            // pairs the other lacks (`dn` below, `up` above: the previous found pair's).
            let h: usize = if up > 0 {
                if q <= usize::MAX - up { q + up } else { q }
            } else if q >= dn { q - dn } else { 0 };
            let (nq, s) = match pair_guess(&x, q, h, Ghost(nv), Ghost(pv), Ghost(tv)) {
                Some(e) => e,
                None => {
                    let ptc = x.ppt[q];
                    proof { assert(ptc < x.ptag.n); }
                    if !have || t.ptc != ptc {
                        if have && t.ptc < ptc {
                            proof { lemma_from_next(x, t, ptc); }
                            t = tag_level_from(&x, ptc, t.npos, t.na, Ghost(nv), Ghost(pv), Ghost(tv));
                        } else {
                            t = tag_level_from(&x, ptc, 0, 0, Ghost(nv), Ghost(pv), Ghost(tv));
                        }
                        have = true;
                    }
                    pair_with(&x, &t, q, Ghost(nv), Ghost(pv), Ghost(tv))
                },
            };
            if nq != NONE {
                if (nq as usize) <= q {
                    dn = q - nq as usize;
                    up = 0;
                } else {
                    up = nq as usize - q;
                    dn = 0;
                }
            }
            out[d - d0] = (q as u64, nq, s);
            d = d + 1;
        }
        out
    }
}

/// The lookups of the pre pairs of the qualifying pre rows: per listed code its entry, and the rank directory.
pub struct PairInfo {
    pub info: Vec<(u64, u64, u64)>,
    pub bits: Vec<u64>,
    pub pref: Vec<u64>,
}

pub open spec fn pair_info_ok(num: Seq<PartView>, pre: Seq<PartView>, tag: Seq<PartView>, ntl: int, pi: PairInfo) -> bool {
    &&& forall|d: int| 0 <= d < pi.info@.len() ==> info_ok(num, pre, tag, ntl, #[trigger] pi.info@[d])
    &&& pi.pref@.len() == pi.bits@.len() + 1
}

/// Touch, list and look up (parallel stages; `look` gives each filing's run, pre adsh code and row count).
pub fn pair_lookups(dispatch: &mut Dispatch, workers: usize, x: LkIn, look: Arc<Vec<(u64, u64, u64)>>,
    adsh_subs: &'static [u64], sub_group: &'static [u64], sub_start: &'static [u64], ptv: &'static [u64],
    gqv: Arc<Vec<bool>>, Ghost(num): Ghost<Seq<PartView>>, Ghost(pre): Ghost<Seq<PartView>>,
    Ghost(tag): Ghost<Seq<PartView>>) -> (r: Result<PairInfo, WorkerFailure>)
    requires lk_in_ok(num, pre, tag, x), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(pi) ==> pair_info_ok(num, pre, tag, x.ntl as int, pi),
{
    let np = x.ppt.len();
    let nw = np / 64 + 1;
    let nf = look.len();
    let lens = (adsh_subs.len(), sub_group.len(), sub_start.len(), ptv.len());
    // ---- touch: filing ranges balanced by qualifying pre rows
    let mut total: u64 = 0;
    let mut f: usize = 0;
    while f < nf
        invariant nf == look@.len(),
        decreases nf - f,
    {
        let c = look[f].2;
        total = if total <= u64::MAX - c { total + c } else { u64::MAX };
        f = f + 1;
    }
    let ntask: u64 = if workers <= 1 || total < 20000 { 1 } else { workers as u64 };
    let per0: u64 = total / ntask;
    let per: u64 = if per0 < u64::MAX { per0 + 1 } else { per0 };
    let mut tasks: Vec<TouchTask> = Vec::new();
    let mut f0: usize = 0;
    let mut acc: u64 = 0;
    let mut f: usize = 0;
    while f < nf
        invariant nf == look@.len(), tasks@.len() < ntask, 1 <= ntask <= MAX_WORKERS, f0 <= nf,
            lens.0 == adsh_subs@.len(), lens.1 == sub_group@.len(), lens.2 == sub_start@.len(), lens.3 == ptv@.len(),
            forall|i: int| 0 <= i < tasks@.len() ==> (#[trigger] tasks@[i]).pre(),
        decreases nf - f,
    {
        let c = look[f].2;
        acc = if acc <= u64::MAX - c { acc + c } else { u64::MAX };
        f = f + 1;
        if acc >= per && (tasks.len() as u64) + 1 < ntask {
            tasks.push(TouchTask { look: look.clone(), f0, f1: f, adsh_subs, sub_group, sub_start, ptv, gqv: gqv.clone(),
                out: vec![0u64; nw], lens });
            f0 = f;
            acc = 0;
        }
    }
    tasks.push(TouchTask { look: look.clone(), f0, f1: nf, adsh_subs, sub_group, sub_start, ptv, gqv: gqv.clone(),
        out: vec![0u64; nw], lens });
    let maps = if tasks.len() == 1 {
        let t = tasks.pop().unwrap();
        let mut v: Vec<Vec<u64>> = Vec::new();
        v.push(t.run());
        v
    } else {
        match fork_join(dispatch, tasks) {
            Ok(v) => v,
            Err(e) => return Err(e),
        }
    };
    let bits = if maps.len() == 1 { maps[0].clone() } else { or_merge(&maps, nw) };
    // ---- the marked codes, then their lookups in chunks
    let (keys, pref) = list_marked(&bits, np);
    let nk = keys.len();
    let ka = Arc::new(keys);
    let nchunk: usize = if workers <= 1 || nk < 2048 { 1 } else if nk / 512 < workers { nk / 512 } else { workers };
    let nchunk = if nchunk == 0 { 1 } else { nchunk };
    let csz0 = nk / nchunk;
    let csz = if csz0 < usize::MAX { csz0 + 1 } else { csz0 };
    let mut itasks: Vec<InfoTask> = Vec::new();
    let mut d0: usize = 0;
    while d0 < nk
        invariant
            lk_in_ok(num, pre, tag, x), ka@.len() == nk, d0 <= nk, csz >= 1,
            forall|d: int| 0 <= d < ka@.len() ==> #[trigger] ka@[d] < x.ppt@.len(),
            forall|i: int| 0 <= i < itasks@.len() ==> (#[trigger] itasks@[i]).x == x
                && itasks@[i].num@ == num && itasks@[i].pre@ == pre && itasks@[i].tag@ == tag
                && itasks@[i].keys@ == ka@ && itasks@[i].d0 <= itasks@[i].d1 <= nk
                && itasks@[i].out@.len() == itasks@[i].d1 - itasks@[i].d0,
            itasks@.len() <= MAX_WORKERS, itasks@.len() < MAX_WORKERS || d0 == nk,
        decreases nk - d0,
    {
        let d1 = if nk - d0 <= csz || itasks.len() + 1 >= MAX_WORKERS { nk } else { d0 + csz };
        let t = InfoTask { x, keys: ka.clone(), d0, d1, out: vec![(0u64, 0u64, 0u64); d1 - d0], num: Ghost(num), pre: Ghost(pre), tag: Ghost(tag) };
        itasks.push(t);
        d0 = d1;
    }
    proof {
        assert forall|i: int| 0 <= i < itasks@.len() implies #[trigger] itasks@[i].pre() by {}
    }
    let ghost its = itasks@;
    let outs: Vec<Vec<(u64, u64, u64)>> = if itasks.len() <= 1 {
        let mut v: Vec<Vec<(u64, u64, u64)>> = Vec::new();
        if itasks.len() == 1 {
            let t = itasks.pop().unwrap();
            proof { assert(t == its[0]); }
            v.push(t.run());
        }
        v
    } else {
        match fork_join(dispatch, itasks) {
            Ok(v) => v,
            Err(e) => return Err(e),
        }
    };
    proof {
        assert forall|kk: int, i: int| 0 <= kk < outs@.len() && 0 <= i < outs@[kk]@.len()
            implies info_ok(num, pre, tag, x.ntl as int, #[trigger] outs@[kk]@[i]) by {
            assert(its[kk].post(outs@[kk]));
        }
    }
    let mut info: Vec<(u64, u64, u64)> = Vec::with_capacity(nk);
    let no = outs.len();
    let mut k: usize = 0;
    while k < no
        invariant
            no == outs@.len(),
            forall|kk: int, i: int| 0 <= kk < outs@.len() && 0 <= i < outs@[kk]@.len()
                ==> info_ok(num, pre, tag, x.ntl as int, #[trigger] outs@[kk]@[i]),
            forall|d: int| 0 <= d < info@.len() ==> info_ok(num, pre, tag, x.ntl as int, #[trigger] info@[d]),
        decreases no - k,
    {
        let o: &Vec<(u64, u64, u64)> = &outs[k];
        let mut i: usize = 0;
        while i < o.len()
            invariant
                0 <= k < outs@.len(), o@ == outs@[k as int]@,
                forall|kk: int, i: int| 0 <= kk < outs@.len() && 0 <= i < outs@[kk]@.len()
                    ==> info_ok(num, pre, tag, x.ntl as int, #[trigger] outs@[kk]@[i]),
                forall|d: int| 0 <= d < info@.len() ==> info_ok(num, pre, tag, x.ntl as int, #[trigger] info@[d]),
            decreases o@.len() - i,
        {
            info.push(o[i]);
            i = i + 1;
        }
        k = k + 1;
    }
    Ok(PairInfo { info, bits, pref })
}

} // verus!
