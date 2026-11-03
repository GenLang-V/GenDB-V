//! Pre pair code -> num pair code: the `num` (tag, version) pair with the same tag and version bytes as a `pre` pair
//! (`fspec::pair_of`), or `NONE`. Both pair lists are strictly increasing by (tag code, version code) and both
//! dictionaries are sorted, so a pre pair's tag is found in the num tag dictionary, the num pairs of that tag are
//! one block of the num pair list (nondecreasing tag codes), and its version is found among the block's versions
//! (strictly increasing).
//!
//! `answer_one` answers one code of an increasing sequence: first the guess `last_d + (c - last_c)` from the last
//! answer (the two pair lists are nearly the same list), confirmed by comparing its tag and version bytes; else the
//! searches, galloping forward from the last positions (`Hints`). `answer_marked` (one worker: every marked code) and
//! `answer_list` (several workers: a task's sorted code list) use it. `resolve` maps one code from scratch (phase D's
//! fallback). `build_map` and phase C (`PairTask`, codes routed to one bucket) belong to the unused routed path.
use vstd::prelude::*;
use crate::spec::text::lex_cmp;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use crate::stores::num::interface as ni;
use crate::stores::pre::interface as pi;
use crate::stores::num::interface::common::text as ntext;
use crate::stores::pre::interface::common::text as ptext;
use crate::stores::num::interface::common::text::{compare_bytes, text_entry_of, lemma_lex_cmp_lt_trans};
use crate::stores::num::interface::common::runs::pair_lt;
use crate::stores::pre::interface::common::cols::u64s as pu64s;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::bridge::order::lemma_lex_cmp_antisym;
use crate::agent::fspec::*;
use crate::agent::common::search::*;

verus! {

pub const NONE: u64 = 0xffff_ffff_ffff_ffff;

/// `tag_lookup`'s scaled guess starts this many num tags below the scaled position (the dictionaries drift apart
/// locally), and is used only when it is more than `TAG_GUESS_MIN_JUMP` tags beyond the forward hint.
pub const TAG_GUESS_SLACK: usize = 32;
pub const TAG_GUESS_MIN_JUMP: usize = 8;

/// `d` is the answer for pre pair `c`: its num pair, or `NONE` when it has none.
pub open spec fn pair_ans(sv: StoresView, c: int, d: u64) -> bool {
    if pair_of(sv, c) == -1 { d == NONE } else { d as int == pair_of(sv, c) }
}

/// The dictionaries of both tables (read-only slices of stored parts).
#[derive(Clone, Copy)]
pub struct PairDicts {
    pub ppair_tag: &'static [u64],
    pub ppair_ver: &'static [u64],
    pub npp: usize,
    pub ptag_off: &'static [u64],
    pub ptag_bytes: &'static [u8],
    pub ptag_count: usize,
    pub pver_off: &'static [u64],
    pub pver_bytes: &'static [u8],
    pub pver_count: usize,
    pub ntag_off: &'static [u64],
    pub ntag_bytes: &'static [u8],
    pub ntag_count: usize,
    pub nver_off: &'static [u64],
    pub nver_bytes: &'static [u8],
    pub nver_count: usize,
    pub npair_tag: &'static [u64],
    pub npair_ver: &'static [u64],
    pub nnpairs: usize,
}

/// The slices are the storages' parts.
pub open spec fn pd_ok(d: PairDicts, sv: StoresView) -> bool {
    &&& layouts(sv)
    &&& d.ppair_tag@ == pu64s(sv.pre, pi::P_PAIR_TAG)
    &&& d.ppair_ver@ == pu64s(sv.pre, pi::P_PAIR_VERSION)
    &&& d.npp == pi::pair_count(sv.pre)
    &&& d.ptag_off@ == ptext::u64_part(sv.pre[pi::P_TAG_OFF as int])
    &&& d.ptag_bytes@ == ptext::u8_part(sv.pre[pi::P_TAG_OFF + 1])
    &&& d.ptag_count == pi::tag_count(sv.pre)
    &&& d.pver_off@ == ptext::u64_part(sv.pre[pi::P_VERSION_OFF as int])
    &&& d.pver_bytes@ == ptext::u8_part(sv.pre[pi::P_VERSION_OFF + 1])
    &&& d.pver_count == pi::version_count(sv.pre)
    &&& d.ntag_off@ == ntext::u64_part(sv.num[ni::P_TAG_OFF as int])
    &&& d.ntag_bytes@ == ntext::u8_part(sv.num[ni::P_TAG_OFF + 1])
    &&& d.ntag_count == ni::tag_count(sv.num)
    &&& d.nver_off@ == ntext::u64_part(sv.num[ni::P_VERSION_OFF as int])
    &&& d.nver_bytes@ == ntext::u8_part(sv.num[ni::P_VERSION_OFF + 1])
    &&& d.nver_count == ni::version_count(sv.num)
    &&& d.npair_tag@ == ni::u64s(sv.num, ni::P_PAIR_TAG)
    &&& d.npair_ver@ == ni::u64s(sv.num, ni::P_PAIR_VERSION)
    &&& d.nnpairs == ni::pair_count(sv.num)
}

/// The facts of the dictionaries the searches need.
pub proof fn lemma_pd_facts(d: PairDicts, sv: StoresView)
    requires pd_ok(d, sv),
    ensures
        text_parts_wf_n(d.ptag_off@, d.ptag_bytes@, d.ptag_count as int),
        text_parts_wf_n(d.pver_off@, d.pver_bytes@, d.pver_count as int),
        dict_sorted(d.ntag_off@, d.ntag_bytes@, d.ntag_count as int, 0, d.ntag_count as int),
        text_parts_wf_n(d.nver_off@, d.nver_bytes@, d.nver_count as int),
        sorted_on(d.npair_tag@, 0, d.nnpairs as int),
        d.npair_tag@.len() == d.nnpairs && d.npair_ver@.len() == d.nnpairs,
        d.ppair_tag@.len() == d.npp && d.ppair_ver@.len() == d.npp,
        forall|c: int| 0 <= c < d.npp ==> #[trigger] d.ppair_tag@[c] < d.ptag_count,
        forall|c: int| 0 <= c < d.npp ==> #[trigger] d.ppair_ver@[c] < d.pver_count,
        forall|e: int| 0 <= e < d.nnpairs ==> #[trigger] d.npair_tag@[e] < d.ntag_count,
        forall|e: int| 0 <= e < d.nnpairs ==> #[trigger] d.npair_ver@[e] < d.nver_count,
{
    let pp = sv.pre;
    let np = sv.num;
    assert(pi::pre_layout_ok(pp));
    assert(ni::num_layout_ok(np));
    assert(ptext::text_parts_wf(d.ptag_off@, d.ptag_bytes@, d.ptag_count as int));
    assert(ptext::text_parts_wf(d.pver_off@, d.pver_bytes@, d.pver_count as int));
    assert(ntext::text_parts_wf(d.ntag_off@, d.ntag_bytes@, d.ntag_count as int));
    assert(ntext::text_strictly_sorted(d.ntag_off@, d.ntag_bytes@, d.ntag_count as int));
    assert(ntext::text_parts_wf(d.nver_off@, d.nver_bytes@, d.nver_count as int));
    assert forall|a: int, b: int| 0 <= a < b < d.ntag_count implies
        lex_cmp(#[trigger] dict_at(d.ntag_off@, d.ntag_bytes@, a), #[trigger] dict_at(d.ntag_off@, d.ntag_bytes@, b)) < 0 by {
        assert(lex_cmp(ntext::text_entry(d.ntag_off@, d.ntag_bytes@, a), ntext::text_entry(d.ntag_off@, d.ntag_bytes@, b)) < 0);
    }
    assert forall|c: int| 0 <= c < d.npp implies #[trigger] d.ppair_ver@[c] < d.pver_count by {
        assert(d.ppair_tag@[c] < d.ptag_count);
    }
    assert forall|e: int| 0 <= e < d.nnpairs implies #[trigger] d.npair_ver@[e] < d.nver_count by {
        assert(d.npair_tag@[e] < d.ntag_count);
    }
    let pt = d.npair_tag@;
    let pv = d.npair_ver@;
    assert(pairs_ok(pt, pv)) by {
        assert(crate::stores::num::interface::common::runs::pairs_increasing(pt, pv));
    }
    assert forall|a: int, b: int| 0 <= a <= b < d.nnpairs implies #[trigger] pt[a] <= #[trigger] pt[b] by {
        if a < b { assert(pair_lt(pt[a], pv[a], pt[b], pv[b])); }
    }
}

/// Strictly increasing pairs (the num pair list).
pub open spec fn pairs_ok(first: Seq<u64>, second: Seq<u64>) -> bool {
    crate::stores::num::interface::common::runs::pairs_increasing(first, second)
}

/// `text_parts_wf` of the text module the searches use.
pub open spec fn text_parts_wf_n(off: Seq<u64>, bytes: Seq<u8>, count: int) -> bool {
    ntext::text_parts_wf(off, bytes, count)
}

impl PairDicts {
    /// The tag bytes of pre pair `c`.
    fn pre_tag(&self, c: usize) -> (r: (&'static [u8], usize))
        requires c < self.npp, exists|sv: StoresView| pd_ok(*self, sv),
        ensures forall|sv: StoresView| pd_ok(*self, sv) ==> r.0@ == pre_pair_tag(sv, c as int), r.1 == r.0@.len(),
        no_unwind
    {
        let ghost sv = choose|sv: StoresView| pd_ok(*self, sv);
        proof { lemma_pd_facts(*self, sv); }
        let pt = self.ppair_tag[c];
        let r = text_entry_of(self.ptag_off, self.ptag_bytes, self.ptag_count, pt as usize);
        proof {
            assert forall|sv2: StoresView| pd_ok(*self, sv2) implies r.0@ == pre_pair_tag(sv2, c as int) by {
                lemma_pd_facts(*self, sv2);
            }
        }
        r
    }

    fn pre_ver(&self, c: usize) -> (r: (&'static [u8], usize))
        requires c < self.npp, exists|sv: StoresView| pd_ok(*self, sv),
        ensures forall|sv: StoresView| pd_ok(*self, sv) ==> r.0@ == pre_pair_ver(sv, c as int), r.1 == r.0@.len(),
        no_unwind
    {
        let ghost sv = choose|sv: StoresView| pd_ok(*self, sv);
        proof { lemma_pd_facts(*self, sv); }
        let pv = self.ppair_ver[c];
        let r = text_entry_of(self.pver_off, self.pver_bytes, self.pver_count, pv as usize);
        proof {
            assert forall|sv2: StoresView| pd_ok(*self, sv2) implies r.0@ == pre_pair_ver(sv2, c as int) by {
                lemma_pd_facts(*self, sv2);
            }
        }
        r
    }
}

/// The num pairs of tag code `t` are exactly `[a, b)`, and their versions strictly increase.
pub open spec fn block_of(d: PairDicts, t: int, a: int, b: int) -> bool {
    &&& 0 <= a <= b <= d.nnpairs
    &&& forall|e: int| 0 <= e < d.nnpairs ==> ((a <= e < b) == (#[trigger] d.npair_tag@[e] == t))
    &&& coded_sorted(d.npair_ver@, d.nver_off@, d.nver_bytes@, d.nver_count as int, a, b)
}

/// The version dictionary order of a block of one tag.
proof fn lemma_block_sorted(d: PairDicts, sv: StoresView, t: int, a: int, b: int)
    requires
        pd_ok(d, sv), 0 <= a <= b <= d.nnpairs,
        forall|e: int| a <= e < b ==> #[trigger] d.npair_tag@[e] == t,
    ensures coded_sorted(d.npair_ver@, d.nver_off@, d.nver_bytes@, d.nver_count as int, a, b),
{
    lemma_pd_facts(d, sv);
    let np = sv.num;
    assert(ni::num_layout_ok(np));
    let pt = d.npair_tag@;
    let pv = d.npair_ver@;
    assert forall|e: int| a <= e < b implies #[trigger] pv[e] < d.nver_count by {}
    assert forall|x: int, y: int| a <= x < y < b implies
        lex_cmp(#[trigger] coded_at(pv, d.nver_off@, d.nver_bytes@, x), #[trigger] coded_at(pv, d.nver_off@, d.nver_bytes@, y)) < 0 by {
        assert(pair_lt(pt[x], pv[x], pt[y], pv[y]));
        assert(pt[x] == t && pt[y] == t);
        ntext::lemma_dict_codes(d.nver_off@, d.nver_bytes@, d.nver_count as int, pv[x] as int, pv[y] as int);
    }
}

/// Which num pairs match pre pair `c`: none when the tag is absent; else those of the tag's block with the version.
proof fn lemma_match_in_block(d: PairDicts, sv: StoresView, c: int, t: int, a: int, b: int, e: int)
    requires
        pd_ok(d, sv), 0 <= c < d.npp, 0 <= t < d.ntag_count,
        dict_at(d.ntag_off@, d.ntag_bytes@, t) == pre_pair_tag(sv, c),
        block_of(d, t, a, b), 0 <= e < d.nnpairs,
    ensures pair_match(sv, c, e) == (a <= e < b && coded_at(d.npair_ver@, d.nver_off@, d.nver_bytes@, e) == pre_pair_ver(sv, c)),
{
    lemma_pd_facts(d, sv);
    ntext::lemma_dict_codes(d.ntag_off@, d.ntag_bytes@, d.ntag_count as int, d.npair_tag@[e] as int, t);
}

impl PairDicts {
    /// The num pair of pre pair `c`, or `NONE` (no hints).
    pub fn resolve(&self, c: usize) -> (r: u64)
        requires c < self.npp, exists|sv: StoresView| pd_ok(*self, sv),
        ensures forall|sv: StoresView| pd_ok(*self, sv) ==> pair_ans(sv, c as int, r),
        no_unwind
    {
        let ghost sv = choose|sv: StoresView| pd_ok(*self, sv);
        proof { lemma_pd_facts(*self, sv); }
        let (tkey, tlen) = self.pre_tag(c);
        let (tpos, tfound) = gallop_dict(self.ntag_off, self.ntag_bytes, self.ntag_count, 0, self.ntag_count, tkey, tlen);
        if !tfound {
            proof {
                assert forall|sv2: StoresView| pd_ok(*self, sv2) implies pair_ans(sv2, c as int, NONE) by {
                    lemma_pd_facts(*self, sv2);
                    assert forall|e: int| !pair_match(sv2, c as int, e) by {
                        if 0 <= e < self.nnpairs {
                            assert(dict_at(self.ntag_off@, self.ntag_bytes@, self.npair_tag@[e] as int) != tkey@);
                        }
                    }
                    lemma_pair_none(sv2, c as int);
                }
            }
            return NONE;
        }
        let t = tpos as u64;
        let a = lower_bound(self.npair_tag, 0, self.nnpairs, t);
        let b = lower_bound(self.npair_tag, a, self.nnpairs, t + 1);
        proof {
            assert forall|e: int| a <= e < b implies #[trigger] self.npair_tag@[e] == t by {}
            lemma_block_sorted(*self, sv, t as int, a as int, b as int);
            assert forall|e: int| 0 <= e < self.nnpairs implies ((a <= e < b) == (#[trigger] self.npair_tag@[e] == t)) by {}
        }
        let (vkey, vlen) = self.pre_ver(c);
        let (vpos, vfound) = gallop_coded(self.npair_ver, self.nver_off, self.nver_bytes, self.nver_count, a, b, vkey, vlen);
        proof {
            assert forall|sv2: StoresView| pd_ok(*self, sv2) implies pair_ans(sv2, c as int, if vfound { vpos as u64 } else { NONE }) by {
                lemma_pd_facts(*self, sv2);
                assert forall|e: int| 0 <= e < self.nnpairs implies pair_match(sv2, c as int, e)
                    == (a <= e < b && coded_at(self.npair_ver@, self.nver_off@, self.nver_bytes@, e) == pre_pair_ver(sv2, c as int)) by {
                    lemma_match_in_block(*self, sv2, c as int, t as int, a as int, b as int, e);
                }
                if vfound {
                    assert(pair_match(sv2, c as int, vpos as int));
                    lemma_pair_of(sv2, c as int, vpos as int);
                } else {
                    assert forall|e: int| !pair_match(sv2, c as int, e) by {
                        if 0 <= e < self.nnpairs && a <= e < b {
                            assert(coded_at(self.npair_ver@, self.nver_off@, self.nver_bytes@, e) != vkey@);
                        }
                    }
                    lemma_pair_none(sv2, c as int);
                }
            }
        }
        if vfound { vpos as u64 } else { NONE }
    }
}


/// The answer for pre pair `c` from its tag's block and the version search in it.
proof fn lemma_ans_block(d: PairDicts, sv: StoresView, c: int, t: int, a: int, b: int, vpos: int, vfound: bool)
    requires
        pd_ok(d, sv), 0 <= c < d.npp, 0 <= t < d.ntag_count,
        dict_at(d.ntag_off@, d.ntag_bytes@, t) == pre_pair_tag(sv, c),
        block_of(d, t, a, b),
        is_coded_lb(d.npair_ver@, d.nver_off@, d.nver_bytes@, a, b, pre_pair_ver(sv, c), vpos, vfound),
    ensures pair_ans(sv, c, if vfound { vpos as u64 } else { NONE }),
{
    lemma_pd_facts(d, sv);
    assert forall|e: int| 0 <= e < d.nnpairs implies pair_match(sv, c, e)
        == (a <= e < b && coded_at(d.npair_ver@, d.nver_off@, d.nver_bytes@, e) == pre_pair_ver(sv, c)) by {
        lemma_match_in_block(d, sv, c, t, a, b, e);
    }
    if vfound {
        assert(pair_match(sv, c, vpos));
        lemma_pair_of(sv, c, vpos);
    } else {
        assert forall|e: int| !pair_match(sv, c, e) by {
            if 0 <= e < d.nnpairs && a <= e < b {
                assert(coded_at(d.npair_ver@, d.nver_off@, d.nver_bytes@, e) != pre_pair_ver(sv, c));
            }
        }
        lemma_pair_none(sv, c);
    }
}

/// No num tag has the tag of pre pair `c`: no answer.
proof fn lemma_ans_no_tag(d: PairDicts, sv: StoresView, c: int)
    requires
        pd_ok(d, sv), 0 <= c < d.npp,
        forall|t: int| 0 <= t < d.ntag_count ==> #[trigger] dict_at(d.ntag_off@, d.ntag_bytes@, t) != pre_pair_tag(sv, c),
    ensures pair_ans(sv, c, NONE),
{
    lemma_pd_facts(d, sv);
    assert forall|e: int| !pair_match(sv, c, e) by {
        if 0 <= e < d.nnpairs {
            assert(dict_at(d.ntag_off@, d.ntag_bytes@, d.npair_tag@[e] as int) != pre_pair_tag(sv, c));
        }
    }
    lemma_pair_none(sv, c);
}

impl PairDicts {
    /// The num tag code of pre pair `c`'s tag (lower bound and whether found), searching forward from hint `th`.
    /// Both tag dictionaries hold nearly the same sorted tags, so the pre tag code scaled to the num dictionary
    /// (less a slack of `TAG_GUESS_SLACK` entries) is a second, usually much closer, start: it is taken when it is
    /// beyond `th` and its predecessor still sorts before the key.
    fn tag_lookup(&self, Ghost(sv): Ghost<StoresView>, c: usize, th: usize) -> (r: (usize, bool))
        requires pd_ok(*self, sv), c < self.npp, th <= self.ntag_count,
        ensures
            r.0 <= self.ntag_count,
            r.1 ==> r.0 < self.ntag_count && dict_at(self.ntag_off@, self.ntag_bytes@, r.0 as int) == pre_pair_tag(sv, c as int),
            !r.1 ==> forall|t: int| 0 <= t < self.ntag_count ==> #[trigger] dict_at(self.ntag_off@, self.ntag_bytes@, t) != pre_pair_tag(sv, c as int),
        no_unwind
    {
        proof { lemma_pd_facts(*self, sv); }
        let (tkey, tlen) = self.pre_tag(c);
        let pt = self.ppair_tag[c];
        proof {
            assert((pt as u128) * (self.ntag_count as u128) <= (u64::MAX as u128) * (u64::MAX as u128)) by (nonlinear_arith)
                requires pt <= u64::MAX, self.ntag_count <= u64::MAX;
        }
        let scaled = (pt as u128) * (self.ntag_count as u128) / (if self.ptag_count > 0 { self.ptag_count as u128 } else { 1 });
        let guess: usize = if scaled > TAG_GUESS_SLACK as u128 && scaled < self.ntag_count as u128 {
            (scaled - TAG_GUESS_SLACK as u128) as usize
        } else {
            0
        };
        let mut h = th;
        let mut hinted = false;
        if guess > th && guess - th > TAG_GUESS_MIN_JUMP {
            let (e, el) = text_entry_of(self.ntag_off, self.ntag_bytes, self.ntag_count, guess - 1);
            if compare_bytes(e, el, tkey, tlen) < 0 {
                h = guess;
                hinted = true;
            }
        }
        proof {
            if hinted {
                assert(lex_cmp(dict_at(self.ntag_off@, self.ntag_bytes@, h - 1), tkey@) < 0);
            }
        }
        if !hinted && h > 0 {
            let (e, el) = text_entry_of(self.ntag_off, self.ntag_bytes, self.ntag_count, h - 1);
            if compare_bytes(e, el, tkey, tlen) >= 0 {
                h = 0;
            }
        }
        proof {
            assert forall|t: int| 0 <= t < h implies lex_cmp(#[trigger] dict_at(self.ntag_off@, self.ntag_bytes@, t), tkey@) < 0 by {
                if t < h - 1 {
                    lemma_lex_cmp_lt_trans(dict_at(self.ntag_off@, self.ntag_bytes@, t),
                        dict_at(self.ntag_off@, self.ntag_bytes@, h - 1), tkey@);
                }
            }
            assert forall|x: int, y: int| h <= x < y < self.ntag_count implies
                lex_cmp(#[trigger] dict_at(self.ntag_off@, self.ntag_bytes@, x), #[trigger] dict_at(self.ntag_off@, self.ntag_bytes@, y)) < 0 by {}
        }
        let (tpos, found) = gallop_dict(self.ntag_off, self.ntag_bytes, self.ntag_count, h, self.ntag_count, tkey, tlen);
        proof {
            if !found {
                assert forall|t: int| 0 <= t < self.ntag_count implies #[trigger] dict_at(self.ntag_off@, self.ntag_bytes@, t) != tkey@ by {
                    if t < h {
                        lemma_lex_cmp_zero(dict_at(self.ntag_off@, self.ntag_bytes@, t), tkey@);
                    }
                }
            }
        }
        (tpos, found)
    }

    /// The num pairs of tag code `t`, searching forward from hint `ph`.
    fn pair_block(&self, Ghost(sv): Ghost<StoresView>, t: usize, ph: usize) -> (r: (usize, usize))
        requires pd_ok(*self, sv), t < self.ntag_count, ph <= self.nnpairs,
        ensures block_of(*self, t as int, r.0 as int, r.1 as int),
        no_unwind
    {
        proof { lemma_pd_facts(*self, sv); }
        let tk = t as u64;
        let mut h = ph;
        if h > 0 && self.npair_tag[h - 1] >= tk {
            h = 0;
        }
        proof {
            assert forall|x: int, y: int| h <= x <= y < self.nnpairs implies #[trigger] self.npair_tag@[x] <= #[trigger] self.npair_tag@[y] by {}
        }
        let a = gallop_u64(self.npair_tag, h, self.nnpairs, tk);
        proof {
            assert forall|x: int, y: int| a <= x <= y < self.nnpairs implies #[trigger] self.npair_tag@[x] <= #[trigger] self.npair_tag@[y] by {}
            assert forall|e: int| 0 <= e < h implies #[trigger] self.npair_tag@[e] < tk by {
                assert(self.npair_tag@[e] <= self.npair_tag@[h - 1]);
            }
        }
        let b = gallop_u64(self.npair_tag, a, self.nnpairs, tk + 1);
        proof {
            assert forall|e: int| a <= e < b implies #[trigger] self.npair_tag@[e] == tk by {}
            lemma_block_sorted(*self, sv, t as int, a as int, b as int);
            assert forall|e: int| 0 <= e < self.nnpairs implies ((a <= e < b) == (#[trigger] self.npair_tag@[e] == tk)) by {
                if e < h {
                } else if e < a {
                } else if e >= b {
                }
            }
        }
        (a, b)
    }

    /// The version of pre pair `c` among the block `[a, b)` of its tag, searching forward from hint `vh`.
    fn ver_lookup(&self, Ghost(sv): Ghost<StoresView>, c: usize, t: Ghost<int>, a: usize, b: usize, vh: usize)
        -> (r: (usize, bool))
        requires pd_ok(*self, sv), c < self.npp, block_of(*self, t@, a as int, b as int), a <= vh <= b,
        ensures is_coded_lb(self.npair_ver@, self.nver_off@, self.nver_bytes@, a as int, b as int, pre_pair_ver(sv, c as int),
            r.0 as int, r.1),
        no_unwind
    {
        proof { lemma_pd_facts(*self, sv); }
        let (vkey, vlen) = self.pre_ver(c);
        let mut h = vh;
        if h > a {
            let (e, el) = text_entry_of(self.nver_off, self.nver_bytes, self.nver_count, self.npair_ver[h - 1] as usize);
            if compare_bytes(e, el, vkey, vlen) >= 0 {
                h = a;
            }
        }
        proof {
            let cs = self.npair_ver@;
            assert forall|x: int| a <= x < h implies lex_cmp(#[trigger] coded_at(cs, self.nver_off@, self.nver_bytes@, x), vkey@) < 0 by {
                if x < h - 1 {
                    lemma_lex_cmp_lt_trans(coded_at(cs, self.nver_off@, self.nver_bytes@, x),
                        coded_at(cs, self.nver_off@, self.nver_bytes@, h - 1), vkey@);
                }
            }
            assert forall|x: int, y: int| h <= x < y < b implies
                lex_cmp(#[trigger] coded_at(cs, self.nver_off@, self.nver_bytes@, x), #[trigger] coded_at(cs, self.nver_off@, self.nver_bytes@, y)) < 0 by {}
            assert forall|x: int| h <= x < b implies #[trigger] cs[x] < self.nver_count by {}
        }
        let (vpos, found) = gallop_coded(self.npair_ver, self.nver_off, self.nver_bytes, self.nver_count, h, b, vkey, vlen);
        proof {
            let cs = self.npair_ver@;
            if !found {
                assert forall|x: int| a <= x < b implies #[trigger] coded_at(cs, self.nver_off@, self.nver_bytes@, x) != vkey@ by {
                    if x < h {
                        lemma_lex_cmp_zero(coded_at(cs, self.nver_off@, self.nver_bytes@, x), vkey@);
                    }
                }
            }
        }
        (vpos, found)
    }

    /// `map[c - p_lo]` := the answer for pre pair `c`, for every `c` in `[p_lo, p_hi)` with `need[c - p_lo] != 0`.
    /// Pre pairs are visited in code order, so tags increase and the searches gallop forward from the previous
    /// positions.
    pub fn build_map(&self, Ghost(sv): Ghost<StoresView>, map: &mut Vec<u64>, need: &Vec<u8>, p_lo: usize, p_hi: usize)
        requires pd_ok(*self, sv), p_lo <= p_hi <= self.npp, old(map)@.len() == p_hi - p_lo, need@.len() == p_hi - p_lo,
        ensures
            final(map)@.len() == old(map)@.len(),
            forall|c: int| p_lo <= c < p_hi && need@[c - p_lo] != 0 ==> #[trigger] pair_ans(sv, c, final(map)@[c - p_lo]),
        no_unwind
    {
        proof { lemma_pd_facts(*self, sv); }
        let mut c = p_lo;
        let mut th: usize = 0;
        let mut ph: usize = 0;
        while c < p_hi
            invariant
                pd_ok(*self, sv), p_lo <= c <= p_hi <= self.npp, map@.len() == p_hi - p_lo, need@.len() == p_hi - p_lo,
                th <= self.ntag_count, ph <= self.nnpairs,
                forall|x: int| p_lo <= x < c && need@[x - p_lo] != 0 ==> #[trigger] pair_ans(sv, x, map@[x - p_lo]),
            decreases p_hi - c,
        {
            if need[c - p_lo] == 0 {
                c = c + 1;
            } else {
                let pt = self.ppair_tag[c];
                let ghost c0 = c as int;
                let (tpos, tfound) = self.tag_lookup(Ghost(sv), c, th);
                th = tpos;
                let (a, b) = if tfound { self.pair_block(Ghost(sv), tpos, ph) } else { (0, 0) };
                if tfound {
                    ph = b;
                }
                let mut vh: usize = a;
                while c < p_hi && self.ppair_tag[c] == pt
                    invariant
                        pd_ok(*self, sv), p_lo <= c <= p_hi <= self.npp, map@.len() == p_hi - p_lo, need@.len() == p_hi - p_lo,
                        th <= self.ntag_count, ph <= self.nnpairs,
                        forall|x: int| p_lo <= x < c && need@[x - p_lo] != 0 ==> #[trigger] pair_ans(sv, x, map@[x - p_lo]),
                        0 <= c0 < self.npp, self.ppair_tag@[c0] == pt, c0 < p_hi, c0 <= c,
                        tfound ==> tpos < self.ntag_count && dict_at(self.ntag_off@, self.ntag_bytes@, tpos as int) == pre_pair_tag(sv, c0)
                            && block_of(*self, tpos as int, a as int, b as int) && a <= vh <= b,
                        !tfound ==> forall|t: int| 0 <= t < self.ntag_count ==> #[trigger] dict_at(self.ntag_off@, self.ntag_bytes@, t) != pre_pair_tag(sv, c0),
                    decreases p_hi - c,
                {
                    if need[c - p_lo] != 0 {
                        proof { assert(pre_pair_tag(sv, c as int) == pre_pair_tag(sv, c0)); }
                        let ans: u64 = if tfound {
                            let (vpos, vf) = self.ver_lookup(Ghost(sv), c, Ghost(tpos as int), a, b, vh);
                            vh = vpos;
                            proof { lemma_ans_block(*self, sv, c as int, tpos as int, a as int, b as int, vpos as int, vf); }
                            if vf { vpos as u64 } else { NONE }
                        } else {
                            proof { lemma_ans_no_tag(*self, sv, c as int); }
                            NONE
                        };
                        put(map, c - p_lo, ans);
                    }
                    c = c + 1;
                }
            }
        }
    }
}

/// Search hints for answering pre pair codes in increasing order: the num tag and num pair positions of the last
/// searches (`th`, `ph`), and the last answered code with its num pair (`last_c`, `last_d`). Both pair lists are
/// nearly the same sorted list, so `last_d + (c - last_c)` is usually the num pair of the next code `c`.
#[derive(Clone, Copy)]
pub struct Hints {
    pub th: usize,
    pub ph: usize,
    pub last_c: usize,
    pub last_d: usize,
}

pub open spec fn hints_ok(d: PairDicts, h: Hints) -> bool {
    h.th <= d.ntag_count && h.ph <= d.nnpairs
}

pub fn no_hints() -> (h: Hints)
    ensures h.th == 0 && h.ph == 0,
    no_unwind
{
    Hints { th: 0, ph: 0, last_c: 0, last_d: 0 }
}

impl PairDicts {
    /// Whether num pair `d` has the tag and version of pre pair `c` (an exact check of a guessed answer).
    fn guess_matches(&self, Ghost(sv): Ghost<StoresView>, c: usize, d: usize) -> (r: bool)
        requires pd_ok(*self, sv), c < self.npp,
        ensures r ==> pair_match(sv, c as int, d as int),
        no_unwind
    {
        if d >= self.nnpairs {
            return false;
        }
        proof { lemma_pd_facts(*self, sv); }
        let nt = self.npair_tag[d] as usize;
        let nv = self.npair_ver[d] as usize;
        let (tk, tl) = self.pre_tag(c);
        let (te, tel) = text_entry_of(self.ntag_off, self.ntag_bytes, self.ntag_count, nt);
        if tel != tl || compare_bytes(te, tel, tk, tl) != 0 {
            return false;
        }
        let (vk, vl) = self.pre_ver(c);
        let (ve, vel) = text_entry_of(self.nver_off, self.nver_bytes, self.nver_count, nv);
        if vel != vl || compare_bytes(ve, vel, vk, vl) != 0 {
            return false;
        }
        proof {
            lemma_lex_cmp_zero(te@, tk@);
            lemma_lex_cmp_zero(ve@, vk@);
            assert(num_pair_tag(sv, d as int) == te@);
            assert(num_pair_ver(sv, d as int) == ve@);
        }
        true
    }

    /// The answer for pre pair `c`: the guess from the last answer when it checks out, else the searches from the
    /// hints; and the new hints.
    pub fn answer_one(&self, Ghost(sv): Ghost<StoresView>, c: usize, h: Hints) -> (r: (u64, Hints))
        requires pd_ok(*self, sv), c < self.npp, hints_ok(*self, h),
        ensures pair_ans(sv, c as int, r.0), hints_ok(*self, r.1),
        no_unwind
    {
        if c >= h.last_c && h.last_d <= self.nnpairs && c - h.last_c < self.nnpairs - h.last_d {
            let g = h.last_d + (c - h.last_c);
            if self.guess_matches(Ghost(sv), c, g) {
                proof { lemma_pair_of(sv, c as int, g as int); }
                return (g as u64, Hints { th: h.th, ph: h.ph, last_c: c, last_d: g });
            }
        }
        let (tpos, tfound) = self.tag_lookup(Ghost(sv), c, h.th);
        if tfound {
            let (a, b) = self.pair_block(Ghost(sv), tpos, h.ph);
            let (vpos, vf) = self.ver_lookup(Ghost(sv), c, Ghost(tpos as int), a, b, a);
            proof {
                lemma_ans_block(*self, sv, c as int, tpos as int, a as int, b as int, vpos as int, vf);
                lemma_pd_facts(*self, sv);
            }
            if vf {
                (vpos as u64, Hints { th: tpos, ph: a, last_c: c, last_d: vpos })
            } else {
                (NONE, Hints { th: tpos, ph: a, last_c: h.last_c, last_d: h.last_d })
            }
        } else {
            proof { lemma_ans_no_tag(*self, sv, c as int); }
            (NONE, Hints { th: tpos, ph: h.ph, last_c: h.last_c, last_d: h.last_d })
        }
    }

    /// `ans[i]` := the answer for pre pair `codes[i]`, for every `i < n` with a code below `npp`. Fastest when the
    /// codes are nondecreasing: equal neighbours share one answer, and the searches start from the last ones.
    pub fn answer_list(&self, Ghost(sv): Ghost<StoresView>, codes: &Vec<u64>, n: usize, ans: &mut Vec<u64>)
        requires pd_ok(*self, sv), n <= codes@.len(), n <= old(ans)@.len(),
        ensures
            final(ans)@.len() == old(ans)@.len(),
            forall|i: int| 0 <= i < n && codes@[i] < self.npp ==> #[trigger] pair_ans(sv, codes@[i] as int, final(ans)@[i]),
        no_unwind
    {
        let mut h = no_hints();
        let mut i: usize = 0;
        while i < n
            invariant
                pd_ok(*self, sv), n <= codes@.len(), n <= ans@.len(), ans@.len() == old(ans)@.len(), i <= n,
                hints_ok(*self, h),
                forall|x: int| 0 <= x < i && codes@[x] < self.npp ==> #[trigger] pair_ans(sv, codes@[x] as int, ans@[x]),
            decreases n - i,
        {
            let c = codes[i];
            if c < self.npp as u64 {
                let a0: u64 = if i > 0 && codes[i - 1] == c {
                    ans[i - 1]
                } else {
                    let (a, h2) = self.answer_one(Ghost(sv), c as usize, h);
                    h = h2;
                    a
                };
                let ghost before = ans@;
                put(ans, i, a0);
                proof {
                    assert forall|x: int| 0 <= x < i + 1 && codes@[x] < self.npp implies #[trigger] pair_ans(sv, codes@[x] as int, ans@[x]) by {
                        if x < i { assert(ans@[x] == before[x]); }
                    }
                }
            }
            i = i + 1;
        }
    }

    /// `map[c]` := the answer for pre pair `c`, for every `c < npp` with `need[c] != 0` (codes in increasing order,
    /// so the guesses and searches of `answer_one` move forward).
    pub fn answer_marked(&self, Ghost(sv): Ghost<StoresView>, map: &mut Vec<u64>, need: &Vec<u8>)
        requires pd_ok(*self, sv), old(map)@.len() == self.npp, need@.len() == self.npp,
        ensures
            final(map)@.len() == old(map)@.len(),
            forall|c: int| 0 <= c < self.npp && need@[c] != 0 ==> #[trigger] pair_ans(sv, c, final(map)@[c]),
        no_unwind
    {
        let mut h = no_hints();
        let npp = self.npp;
        let mut c: usize = 0;
        while c < npp
            invariant
                pd_ok(*self, sv), npp == self.npp, map@.len() == npp, need@.len() == npp, c <= npp,
                hints_ok(*self, h),
                forall|x: int| 0 <= x < c && need@[x] != 0 ==> #[trigger] pair_ans(sv, x, map@[x]),
            decreases npp - c,
        {
            if need[c] != 0 {
                let (a, h2) = self.answer_one(Ghost(sv), c, h);
                h = h2;
                let ghost before = map@;
                put(map, c, a);
                proof {
                    assert forall|x: int| 0 <= x < c + 1 && need@[x] != 0 implies #[trigger] pair_ans(sv, x, map@[x]) by {
                        if x < c { assert(map@[x] == before[x]); }
                    }
                }
            }
            c = c + 1;
        }
    }
}

/// Marks of a local need list (one-worker path): a code to answer, and a code answered in the local map.
pub const NEEDED: u8 = 1;
pub const ANSWERED: u8 = 2;

/// Every `ANSWERED` code of a local need list has its answer in `lmap` (opaque: revealed where the list is
/// written or read).
#[verifier::opaque]
pub open spec fn local_ok(sv: StoresView, need: Seq<u8>, lmap: Seq<u64>) -> bool {
    &&& need.len() == lmap.len()
    &&& forall|c: int| 0 <= c < need.len() && #[trigger] need[c] == ANSWERED ==> pair_ans(sv, c, lmap[c])
}

/// Answers every marked (nonzero) code of a need list over all pre pair codes: its num pair goes to `map` and
/// the mark becomes `ANSWERED`.
pub fn answer_needed(dicts: PairDicts, Ghost(sv): Ghost<StoresView>, need: &mut Vec<u8>, map: &mut Vec<u64>)
    requires pd_ok(dicts, sv), old(need)@.len() == dicts.npp, old(map)@.len() == dicts.npp,
    ensures
        final(need)@.len() == old(need)@.len(), final(map)@.len() == old(map)@.len(),
        local_ok(sv, final(need)@, final(map)@),
    no_unwind
{
    let npp = dicts.npp;
    dicts.answer_marked(Ghost(sv), map, need);
    let ghost m = map@;
    let ghost n0 = need@;
    let mut c: usize = 0;
    while c < npp
        invariant
            need@.len() == npp, map@ == m, m.len() == npp, n0.len() == npp, c <= npp,
            forall|x: int| 0 <= x < npp && n0[x] != 0 ==> #[trigger] pair_ans(sv, x, m[x]),
            forall|x: int| c <= x < npp ==> #[trigger] need@[x] == n0[x],
            forall|x: int| 0 <= x < c && #[trigger] need@[x] == ANSWERED ==> pair_ans(sv, x, m[x]),
        decreases npp - c,
    {
        if need[c] != 0 {
            let ghost before = need@;
            put(need, c, ANSWERED);
            proof {
                assert forall|x: int| 0 <= x < c + 1 && #[trigger] need@[x] == ANSWERED implies pair_ans(sv, x, m[x]) by {
                    if x < c {
                        assert(need@[x] == before[x]);
                    } else {
                        assert(n0[x] != 0);
                    }
                }
                assert forall|x: int| c + 1 <= x < npp implies #[trigger] need@[x] == n0[x] by {
                    assert(need@[x] == before[x]);
                }
            }
        } else {
            proof {
                assert forall|x: int| 0 <= x < c + 1 && #[trigger] need@[x] == ANSWERED implies pair_ans(sv, x, m[x]) by {
                    if x == c {
                        assert(need@[x] == n0[x]);
                    }
                }
            }
        }
        c = c + 1;
    }
    proof { reveal(local_ok); }
}

/// Phase C: the pair map of bucket `[p_lo, p_hi)`, then the answers `dbufs[i][k]` for the codes `cbufs[i][k]`
/// routed by each phase-B task `i` (codes outside the bucket are resolved directly).
pub struct PairTask {
    pub dicts: PairDicts,
    pub p_lo: usize,
    pub p_hi: usize,
    pub map: Vec<u64>,
    pub need: Vec<u8>,
    pub cbufs: Vec<Vec<u64>>,
    pub dbufs: Vec<Vec<u64>>,
    pub lens: Vec<usize>,
    pub nw: usize,
    pub sv: Ghost<StoresView>,
}

pub struct PairOut {
    pub cbufs: Vec<Vec<u64>>,
    pub dbufs: Vec<Vec<u64>>,
    pub lens: Vec<usize>,
}

/// The answers of `dbufs` for the codes of `cbufs` (first `lens[i]` of buffer `i`).
pub open spec fn answers_ok(sv: StoresView, npp: int, cbufs: Seq<Vec<u64>>, dbufs: Seq<Vec<u64>>, lens: Seq<usize>) -> bool {
    &&& cbufs.len() == lens.len() && dbufs.len() == lens.len()
    &&& forall|i: int| 0 <= i < lens.len() ==> #[trigger] lens[i] <= cbufs[i]@.len() && lens[i] <= dbufs[i]@.len()
    &&& forall|i: int, k: int| 0 <= i < lens.len() && 0 <= k < lens[i] && cbufs[i]@[k] < npp
        ==> #[trigger] pair_ans(sv, cbufs[i]@[k] as int, dbufs[i]@[k])
}

impl WorkerTask for PairTask {
    type Output = PairOut;

    open spec fn pre(&self) -> bool {
        &&& pd_ok(self.dicts, self.sv@)
        &&& self.p_lo <= self.p_hi <= self.dicts.npp
        &&& self.map@.len() == self.p_hi - self.p_lo
        &&& self.need@.len() == self.p_hi - self.p_lo
        &&& self.cbufs@.len() == self.nw && self.dbufs@.len() == self.nw && self.lens@.len() == self.nw
        &&& forall|i: int| 0 <= i < self.nw ==> #[trigger] self.lens@[i] <= self.cbufs@[i]@.len()
            && self.lens@[i] <= self.dbufs@[i]@.len()
    }

    open spec fn post(&self, out: PairOut) -> bool {
        &&& out.cbufs@ == self.cbufs@
        &&& out.lens@ == self.lens@
        &&& out.dbufs@.len() == self.nw
        &&& forall|i: int| 0 <= i < self.nw ==> #[trigger] out.dbufs@[i]@.len() == self.dbufs@[i]@.len()
        &&& answers_ok(self.sv@, self.dicts.npp as int, out.cbufs@, out.dbufs@, out.lens@)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.p_lo as u64, self.p_hi as u64)
    }

    fn run(self) -> (out: PairOut) {
        let mut t = self;
        let ghost sv = t.sv@;
        let ghost d0 = t.dbufs@;
        // the codes of this bucket that phase B routed here
        let mut i: usize = 0;
        while i < t.nw
            invariant
                t.p_lo <= t.p_hi, t.need@.len() == t.p_hi - t.p_lo, i <= t.nw,
                t.cbufs@.len() == t.nw && t.lens@.len() == t.nw,
                forall|x: int| 0 <= x < t.nw ==> #[trigger] t.lens@[x] <= t.cbufs@[x]@.len(),
                t.cbufs@ == self.cbufs@, t.lens@ == self.lens@, t.dbufs@ == self.dbufs@, t.map@ == self.map@,
                t.dicts == self.dicts, t.p_lo == self.p_lo, t.p_hi == self.p_hi, t.nw == self.nw, t.sv == self.sv,
            decreases t.nw - i,
        {
            let n = t.lens[i];
            let mut k: usize = 0;
            while k < n
                invariant
                    t.p_lo <= t.p_hi, t.need@.len() == t.p_hi - t.p_lo, i < t.nw, k <= n, n == t.lens@[i as int],
                    t.cbufs@.len() == t.nw && t.lens@.len() == t.nw,
                    forall|x: int| 0 <= x < t.nw ==> #[trigger] t.lens@[x] <= t.cbufs@[x]@.len(),
                    t.cbufs@ == self.cbufs@, t.lens@ == self.lens@, t.dbufs@ == self.dbufs@, t.map@ == self.map@,
                    t.dicts == self.dicts, t.p_lo == self.p_lo, t.p_hi == self.p_hi, t.nw == self.nw, t.sv == self.sv,
                decreases n - k,
            {
                let c = t.cbufs[i][k];
                if c >= t.p_lo as u64 && c < t.p_hi as u64 {
                    put(&mut t.need, (c - t.p_lo as u64) as usize, 1u8);
                }
                k = k + 1;
            }
            i = i + 1;
        }
        t.dicts.build_map(Ghost(sv), &mut t.map, &t.need, t.p_lo, t.p_hi);
        let mut i: usize = 0;
        while i < t.nw
            invariant
                pd_ok(t.dicts, sv), t.p_lo <= t.p_hi <= t.dicts.npp, t.map@.len() == t.p_hi - t.p_lo,
                t.need@.len() == t.p_hi - t.p_lo,
                forall|c: int| t.p_lo <= c < t.p_hi && t.need@[c - t.p_lo] != 0 ==> #[trigger] pair_ans(sv, c, t.map@[c - t.p_lo]),
                t.cbufs@.len() == t.nw && t.dbufs@.len() == t.nw && t.lens@.len() == t.nw, i <= t.nw,
                forall|x: int| 0 <= x < t.nw ==> #[trigger] t.lens@[x] <= t.cbufs@[x]@.len() && t.lens@[x] <= t.dbufs@[x]@.len(),
                forall|x: int| 0 <= x < t.nw ==> #[trigger] t.dbufs@[x]@.len() == d0[x]@.len(),
                forall|x: int, k: int| 0 <= x < i && 0 <= k < t.lens@[x] && t.cbufs@[x]@[k] < t.dicts.npp
                    ==> #[trigger] pair_ans(sv, t.cbufs@[x]@[k] as int, t.dbufs@[x]@[k]),
            decreases t.nw - i,
        {
            let n = t.lens[i];
            let mut k: usize = 0;
            while k < n
                invariant
                    pd_ok(t.dicts, sv), t.p_lo <= t.p_hi <= t.dicts.npp, t.map@.len() == t.p_hi - t.p_lo,
                    t.need@.len() == t.p_hi - t.p_lo,
                    forall|c: int| t.p_lo <= c < t.p_hi && t.need@[c - t.p_lo] != 0 ==> #[trigger] pair_ans(sv, c, t.map@[c - t.p_lo]),
                    t.cbufs@.len() == t.nw && t.dbufs@.len() == t.nw && t.lens@.len() == t.nw, i < t.nw,
                    n == t.lens@[i as int], k <= n,
                    forall|x: int| 0 <= x < t.nw ==> #[trigger] t.lens@[x] <= t.cbufs@[x]@.len() && t.lens@[x] <= t.dbufs@[x]@.len(),
                    forall|x: int| 0 <= x < t.nw ==> #[trigger] t.dbufs@[x]@.len() == d0[x]@.len(),
                    forall|x: int, k2: int| 0 <= x < i && 0 <= k2 < t.lens@[x] && t.cbufs@[x]@[k2] < t.dicts.npp
                        ==> #[trigger] pair_ans(sv, t.cbufs@[x]@[k2] as int, t.dbufs@[x]@[k2]),
                    forall|k2: int| 0 <= k2 < k && t.cbufs@[i as int]@[k2] < t.dicts.npp
                        ==> #[trigger] pair_ans(sv, t.cbufs@[i as int]@[k2] as int, t.dbufs@[i as int]@[k2]),
                decreases n - k,
            {
                let c = t.cbufs[i][k];
                let d: u64 = if c >= t.p_lo as u64 && c < t.p_hi as u64 && t.need[(c - t.p_lo as u64) as usize] != 0 {
                    t.map[(c - t.p_lo as u64) as usize]
                } else if c < t.dicts.npp as u64 {
                    t.dicts.resolve(c as usize)
                } else {
                    NONE
                };
                let ghost before = t.dbufs@;
                let b = vstd::std_specs::vec::vec_index_mut(&mut t.dbufs, i);
                put(b, k, d);
                proof {
                    assert forall|x: int| 0 <= x < t.nw && x != i implies #[trigger] t.dbufs@[x] == before[x] by {}
                }
                k = k + 1;
            }
            i = i + 1;
        }
        PairOut { cbufs: t.cbufs, dbufs: t.dbufs, lens: t.lens }
    }
}

} // verus!
