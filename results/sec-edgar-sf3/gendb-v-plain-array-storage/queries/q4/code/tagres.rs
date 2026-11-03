//! P2: the tag row of every candidate pre row (`tag_of`: `abstract = 0` and the candidate's tag and version).
//!
//! 1. `build_slots` (calling thread): the distinct `(tag, version)` hashes of the candidates, one slot each
//!    (`slots_ok`), with a chained index and bitmap over the slot hashes.
//! 2. `TagTask` (parallel over tag rows): every pair `(slot, tag row)` whose hashes meet (`slot_hit`), at most
//!    one per tag row because slot hashes are distinct (`hits_ok`).
//! 3. `slot_rows` (calling thread): one meeting tag row per slot, `NONE` when no tag row meets it (`tvrow_ok`).
//! 4. `VerTask` (parallel over candidates): a candidate's tag row is its slot's row when the bytes are equal; a
//!    slot without a row means no tag row has the candidate's `(tag, version)`; a byte mismatch (a hash
//!    collision) falls back to every pair of the slot (`ver_one`). By the tag key (`tag_key`) the answer is
//!    unique (`tagrow_ok`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::common::buf::Buf;
use crate::agent::common::hash::*;
use crate::agent::common::chains::*;
use crate::agent::common::grow::*;
use crate::agent::common::text::*;
use crate::agent::cols::*;
use crate::agent::nf::*;
use crate::agent::pre::*;

verus! {

/// The candidates (`cands_ok` over all pre rows).
pub struct Cands {
    pub list: Vec<(usize, usize, u64)>,
    pub p_tag: TextCol,
    pub p_ver: TextCol,
}

pub open spec fn cand_l(x: &Cands, e: int) -> int {
    x.list@[e].0 as int
}

pub open spec fn cands_index_ok(x: &Cands, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& cands_ok(c, x.list@, 0, c.npre)
    &&& x.list@.len() < NONE
    &&& x.p_tag@ == p_tag_v(c) && x.p_ver@ == p_ver_v(c)
    &&& text_wf(x.p_tag@, c.npre) && text_wf(x.p_ver@, c.npre)
}

/// Candidate `e` and tag row `k` match: `k` is the tag row of the candidate's `(tag, version)`.
pub open spec fn cand_tag(x: &Cands, c: Ctx, e: int, k: int) -> bool {
    0 <= e < x.list@.len() && tag_of(c, k, p_tag(c, cand_l(x, e)), p_ver(c, cand_l(x, e)))
}

/// The candidate list (calling thread).
pub fn build_cands(list: Vec<(usize, usize, u64)>, p_tag: &TextCol, p_ver: &TextCol, Ghost(c): Ghost<Ctx>) -> (x: Cands)
    requires ctx_ok(c), cands_ok(c, list@, 0, c.npre), p_tag@ == p_tag_v(c), p_ver@ == p_ver_v(c),
    ensures cands_index_ok(&x, c), x.list@ == list@,
{
    proof {
        lemma_views(c);
        lemma_cands_len(c, list@, p_tag);
    }
    Cands { list, p_tag: tc(p_tag), p_ver: tc(p_ver) }
}

/// The candidate list is shorter than `NONE` (at most one entry per pre row, and the pre offsets are a slice of
/// `npre + 1` elements).
proof fn lemma_cands_len(c: Ctx, list: Seq<(usize, usize, u64)>, p_tag: &TextCol)
    requires ctx_ok(c), cands_ok(c, list, 0, c.npre), p_tag@ == p_tag_v(c),
    ensures list.len() < NONE,
{
    lemma_views(c);
    lemma_cands_bound(c, 0, c.npre);
    assert(p_tag.offsets@.len() == p_tag.offsets.len() as int);
}

/// `cands_in(lo, hi)` has at most `hi - lo` rows.
proof fn lemma_cands_bound(c: Ctx, lo: int, hi: int)
    requires lo <= hi,
    ensures cands_in(c, lo, hi).len() <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_cands_bound(c, lo, hi - 1);
    }
}

/// Candidate `e` is a candidate pre row with the `(tag, version)` hash of its list entry.
pub proof fn lemma_cand_row(x: &Cands, c: Ctx, e: int)
    requires cands_index_ok(x, c), 0 <= e < x.list@.len(),
    ensures
        pre_cand(c, cand_l(x, e)), 0 <= cand_l(x, e) < c.npre,
        x.list@[e].2 == pair_hash_spec(1, p_tag(c, cand_l(x, e)), p_ver(c, cand_l(x, e))),
{
    let cs = cands_in(c, 0, c.npre);
    assert(x.list@[e].0 as int == cs[e]);
    lemma_cands_mem(c, 0, c.npre, e);
}

// ------------------------------------------------------------------------------------------------ slots

/// The hashes are pairwise distinct.
pub open spec fn distinct_hashes(hs: Seq<u64>) -> bool {
    forall|s1: int, s2: int| 0 <= s1 < hs.len() && 0 <= s2 < hs.len() && s1 != s2 ==> #[trigger] hs[s1] != #[trigger] hs[s2]
}

/// The distinct candidate hashes (`chains.hashes`, one slot each) and the slot of every candidate.
pub struct Slots {
    pub of: Vec<usize>,
    pub chains: Chains,
}

pub open spec fn slots_ok(sl: &Slots, x: &Cands) -> bool {
    let hs = sl.chains.hashes@;
    &&& chains_wf(&sl.chains)
    &&& distinct_hashes(hs)
    &&& sl.of@.len() == x.list@.len()
    &&& forall|q: int| 0 <= q < x.list@.len() ==> (#[trigger] sl.of@[q] as int) < hs.len() && hs[sl.of@[q] as int] == x.list@[q].2
}

/// The slots of the candidates (calling thread; integer work only).
pub fn build_slots(x: &Cands) -> (sl: Slots)
    requires x.list@.len() < NONE,
    ensures slots_ok(&sl, x),
{
    let n = x.list.len();
    let mut gt = grow_new(n / 8 + 1024);
    let mut of: Vec<usize> = Vec::with_capacity(n);
    let mut q: usize = 0;
    while q < n
        invariant
            n == x.list@.len(), n < NONE, q <= n, grow_wf(&gt), gt.hashes@.len() <= q,
            of@.len() == q, distinct_hashes(gt.hashes@),
            forall|q2: int| 0 <= q2 < q ==> (#[trigger] of@[q2] as int) < gt.hashes@.len() && gt.hashes@[of@[q2] as int] == x.list@[q2].2,
        decreases n - q,
    {
        let h = x.list[q].2;
        let mut s = grow_find(&gt, h);
        let ghost hs0 = gt.hashes@;
        let ghost of0 = of@;
        if s == NONE {
            s = gt.hashes.len();
            grow_insert(&mut gt, h);
            proof {
                lemma_push_distinct(hs0, h);
            }
        }
        of.push(s);
        proof {
            assert forall|q2: int| 0 <= q2 < q + 1 implies (#[trigger] of@[q2] as int) < gt.hashes@.len()
                && gt.hashes@[of@[q2] as int] == x.list@[q2].2 by {
                if q2 < q {
                    assert(of@[q2] == of0[q2]);
                    assert(gt.hashes@[of0[q2] as int] == hs0[of0[q2] as int]);
                }
            }
        }
        q = q + 1;
    }
    let Grow { hashes, head: _, next: _, shift: _ } = gt;
    let chains = build_chains(hashes);
    Slots { of, chains }
}

/// A hash absent from distinct hashes keeps them distinct when appended.
proof fn lemma_push_distinct(hs: Seq<u64>, h: u64)
    requires distinct_hashes(hs), forall|x: int| 0 <= x < hs.len() ==> #[trigger] hs[x] != h,
    ensures distinct_hashes(hs.push(h)),
{
    let hp = hs.push(h);
    assert forall|s1: int, s2: int| 0 <= s1 < hp.len() && 0 <= s2 < hp.len() && s1 != s2
        implies #[trigger] hp[s1] != #[trigger] hp[s2] by {
        if s1 < hs.len() && s2 < hs.len() {
            assert(hp[s1] == hs[s1] && hp[s2] == hs[s2]);
        } else if s1 < hs.len() {
            assert(hp[s1] == hs[s1]);
        } else {
            assert(hp[s2] == hs[s2]);
        }
    }
}

// ------------------------------------------------------------------------------------------------ tag scan

/// Slot `s` and tag row `k` meet: `k` has `abstract = 0` and the `(tag, version)` hash of slot `s`.
pub open spec fn slot_hit(sl: &Slots, c: Ctx, s: int, k: int) -> bool {
    &&& 0 <= s < sl.chains.hashes@.len() && 0 <= k < c.nt && t_abs(c, k) == 0
    &&& sl.chains.hashes@[s] == pair_hash_spec(1, t_tag(c, k), t_ver(c, k))
}

/// Every pair meets and lies in `lo..hi`; every meeting of a tag row in `lo..done` is recorded.
pub open spec fn hits_ok(sl: &Slots, c: Ctx, ps: Seq<(usize, usize)>, lo: int, hi: int, done: int) -> bool {
    &&& forall|q: int| 0 <= q < ps.len() ==> lo <= (#[trigger] ps[q]).1 < hi && slot_hit(sl, c, ps[q].0 as int, ps[q].1 as int)
    &&& forall|s: int, k: int| lo <= k < done && #[trigger] slot_hit(sl, c, s, k) ==> ps.contains((s as usize, k as usize))
}

/// The columns and slots a tag scan reads.
pub struct TagScan {
    pub t_tag: TextCol,
    pub t_ver: TextCol,
    pub t_abs: &'static [i32],
    pub sl: Arc<Slots>,
}

#[verifier::opaque]
pub open spec fn tag_scan_ok(t: &TagScan, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& chains_wf(&t.sl.chains) && distinct_hashes(t.sl.chains.hashes@)
    &&& t.t_tag@ == t_tag_v(c) && t.t_ver@ == t_ver_v(c) && t.t_abs@ == t_abs_s(c)
    &&& text_wf(t.t_tag@, c.nt) && text_wf(t.t_ver@, c.nt) && t.t_abs@.len() == c.nt
}

/// The slot tag row `k` meets (`NONE` when none), its pair pushed onto `out`, which has a free slot. Slot hashes
/// are distinct, so a tag row meets at most one slot.
fn tag_row(t: &TagScan, k: usize, out: &mut Buf<(usize, usize)>, Ghost(c): Ghost<Ctx>) -> (s: usize)
    requires tag_scan_ok(t, c), (k as int) < c.nt, old(out).wf(), old(out).view().len() < old(out).capacity(),
    ensures
        final(out).wf(), final(out).capacity() == old(out).capacity(),
        s == NONE ==> final(out).view() == old(out).view() && forall|s2: int| !#[trigger] slot_hit(&*t.sl, c, s2, k as int),
        s != NONE ==> final(out).view() == old(out).view().push((s, k)) && slot_hit(&*t.sl, c, s as int, k as int)
            && forall|s2: int| #[trigger] slot_hit(&*t.sl, c, s2, k as int) ==> s2 == s as int,
    no_unwind
{
    proof { reveal(tag_scan_ok); }
    if t.t_abs[k] != 0 {
        return NONE;
    }
    let (tg, tgl) = text_val(&t.t_tag, k, Ghost(c.nt));
    let (tv, tvl) = text_val(&t.t_ver, k, Ghost(c.nt));
    let h = pair_hash(1, tg, tgl, tv, tvl);
    proof {
        assert(tg@ == t_tag(c, k as int) && tv@ == t_ver(c, k as int));
    }
    if !may_contain(&t.sl.chains, h) {
        return NONE;
    }
    let s = chains_find(&t.sl.chains, h);
    if s != NONE {
        out.push((s, k));
    }
    s
}

/// Pairs of consecutive tag row ranges concatenate.
pub proof fn lemma_hits_union(sl: &Slots, c: Ctx, a: Seq<(usize, usize)>, b: Seq<(usize, usize)>, lo: int, mid: int, hi: int)
    requires 0 <= lo <= mid <= hi, hits_ok(sl, c, a, lo, mid, mid), hits_ok(sl, c, b, mid, hi, hi),
    ensures hits_ok(sl, c, a + b, lo, hi, hi),
{
    let ab = a + b;
    assert forall|q: int| 0 <= q < ab.len() implies lo <= (#[trigger] ab[q]).1 < hi && slot_hit(sl, c, ab[q].0 as int, ab[q].1 as int) by {
        if q < a.len() {
            assert(ab[q] == a[q]);
        } else {
            assert(ab[q] == b[q - a.len()]);
        }
    }
    assert forall|s: int, k: int| lo <= k < hi && #[trigger] slot_hit(sl, c, s, k) implies ab.contains((s as usize, k as usize)) by {
        if k < mid {
            let w = choose|w: int| 0 <= w < a.len() && a[w] == (s as usize, k as usize);
            assert(ab[w] == a[w]);
        } else {
            let w = choose|w: int| 0 <= w < b.len() && b[w] == (s as usize, k as usize);
            assert(ab[a.len() + w] == b[w]);
        }
    }
}

/// One tag scan task: tag rows `lo..hi` into `out` (room for one pair per row).
pub struct TagTask {
    pub lo: usize,
    pub hi: usize,
    pub scan: TagScan,
    pub out: Buf<(usize, usize)>,
    pub ctx: Ghost<Ctx>,
}

impl WorkerTask for TagTask {
    type Output = Buf<(usize, usize)>;

    open spec fn pre(&self) -> bool {
        &&& tag_scan_ok(&self.scan, self.ctx@)
        &&& self.lo <= self.hi && (self.hi as int) <= self.ctx@.nt
        &&& self.out.wf() && self.out.view().len() == 0 && self.out.capacity() >= self.hi - self.lo
    }

    open spec fn post(&self, r: Buf<(usize, usize)>) -> bool {
        &&& r.wf()
        &&& hits_ok(&*self.scan.sl, self.ctx@, r.view(), self.lo as int, self.hi as int, self.hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (r: Buf<(usize, usize)>) {
        let TagTask { lo, hi, scan, out, ctx } = self;
        let ghost c = ctx@;
        let ghost sl = &*scan.sl;
        let mut out = out;
        let mut k = lo;
        while k < hi
            invariant
                tag_scan_ok(&scan, c), sl == &*scan.sl, lo <= k <= hi, (hi as int) <= c.nt,
                out.wf(), out.capacity() >= hi - lo, out.view().len() <= k - lo,
                hits_ok(sl, c, out.view(), lo as int, hi as int, k as int),
            decreases hi - k,
        {
            let ghost o0 = out.view();
            let s = tag_row(&scan, k, &mut out, Ghost(c));
            proof {
                let o1 = out.view();
                assert forall|q: int| 0 <= q < o1.len() implies lo <= (#[trigger] o1[q]).1 < hi
                    && slot_hit(sl, c, o1[q].0 as int, o1[q].1 as int) by {
                    if q < o0.len() {
                        assert(o1[q] == o0[q]);
                    }
                }
                assert forall|s: int, k2: int| lo <= k2 < k + 1 && #[trigger] slot_hit(sl, c, s, k2) implies
                    o1.contains((s as usize, k2 as usize)) by {
                    if k2 < k {
                        let w = choose|w: int| 0 <= w < o0.len() && o0[w] == (s as usize, k2 as usize);
                        assert(o1[w] == o0[w]);
                    } else {
                        assert(o1[o0.len() as int] == (s as usize, k2 as usize));
                    }
                }
            }
            k = k + 1;
        }
        out
    }
}

// ------------------------------------------------------------------------------------------------ slot rows

/// The meeting tag row of every slot, `NONE` when no tag row meets it.
pub open spec fn tvrow_ok(sl: &Slots, c: Ctx, tvrow: Seq<usize>) -> bool {
    &&& tvrow.len() == sl.chains.hashes@.len()
    &&& forall|s: int| 0 <= s < tvrow.len() ==>
        (#[trigger] tvrow[s] == NONE ==> forall|k: int| !slot_hit(sl, c, s, k))
        && (tvrow[s] != NONE ==> slot_hit(sl, c, s, tvrow[s] as int))
}

/// One meeting tag row per slot, from the pairs of every tag row (calling thread).
pub fn slot_rows(sl: &Slots, hits: &Vec<(usize, usize)>, Ghost(c): Ghost<Ctx>) -> (tvrow: Vec<usize>)
    requires hits_ok(sl, c, hits@, 0, c.nt, c.nt), c.nt < NONE,
    ensures tvrow_ok(sl, c, tvrow@),
{
    let ns = sl.chains.hashes.len();
    let mut tvrow: Vec<usize> = vec![NONE; ns];
    let np = hits.len();
    let mut q: usize = 0;
    while q < np
        invariant
            hits_ok(sl, c, hits@, 0, c.nt, c.nt), c.nt < NONE, ns == sl.chains.hashes@.len(), np == hits@.len(), q <= np,
            tvrow@.len() == ns,
            forall|s: int| 0 <= s < ns ==> #[trigger] tvrow@[s] == NONE || slot_hit(sl, c, s, tvrow@[s] as int),
            forall|w: int| 0 <= w < q ==> tvrow@[(#[trigger] hits@[w]).0 as int] != NONE,
        decreases np - q,
    {
        let (s, k) = hits[q];
        proof {
            assert(slot_hit(sl, c, s as int, k as int));
        }
        let ghost t0 = tvrow@;
        tvrow[s] = k;
        proof {
            assert forall|w: int| 0 <= w < q + 1 implies tvrow@[(#[trigger] hits@[w]).0 as int] != NONE by {
                if w < q && hits@[w].0 != s {
                    assert(tvrow@[hits@[w].0 as int] == t0[hits@[w].0 as int]);
                }
            }
        }
        q = q + 1;
    }
    proof {
        assert forall|s: int| 0 <= s < ns implies
            (#[trigger] tvrow@[s] == NONE ==> forall|k: int| !slot_hit(sl, c, s, k))
            && (tvrow@[s] != NONE ==> slot_hit(sl, c, s, tvrow@[s] as int)) by {
            if tvrow@[s] == NONE {
                assert forall|k: int| !slot_hit(sl, c, s, k) by {
                    if slot_hit(sl, c, s, k) {
                        let w = choose|w: int| 0 <= w < hits@.len() && hits@[w] == (s as usize, k as usize);
                        assert(tvrow@[hits@[w].0 as int] != NONE);
                    }
                }
            }
        }
    }
    tvrow
}

// ------------------------------------------------------------------------------------------------ candidates

/// `k` is the answer for candidate `e`: its tag row, `NONE` exactly when it has none.
pub open spec fn tag_answer(x: &Cands, c: Ctx, e: int, k: usize) -> bool {
    let l = cand_l(x, e);
    &&& (k == NONE) == !has_tag(c, p_tag(c, l), p_ver(c, l))
    &&& k != NONE ==> tag_of(c, k as int, p_tag(c, l), p_ver(c, l))
}

/// The tag row of every candidate, `NONE` when there is none.
pub open spec fn tagrow_ok(x: &Cands, c: Ctx, tagrow: Seq<usize>) -> bool {
    &&& tagrow.len() == x.list@.len()
    &&& forall|e: int| 0 <= e < tagrow.len() ==> tag_answer(x, c, e, #[trigger] tagrow[e])
}

/// What a candidate check reads.
pub struct VerScan {
    pub cx: Arc<Cands>,
    pub sl: Arc<Slots>,
    pub tvrow: Arc<Vec<usize>>,
    pub hits: Arc<Vec<(usize, usize)>>,
    pub t_tag: TextCol,
    pub t_ver: TextCol,
}

#[verifier::opaque]
pub open spec fn ver_scan_ok(v: &VerScan, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& cands_index_ok(&*v.cx, c) && slots_ok(&*v.sl, &*v.cx)
    &&& tvrow_ok(&*v.sl, c, v.tvrow@) && hits_ok(&*v.sl, c, v.hits@, 0, c.nt, c.nt)
    &&& v.t_tag@ == t_tag_v(c) && v.t_ver@ == t_ver_v(c) && text_wf(v.t_tag@, c.nt) && text_wf(v.t_ver@, c.nt)
}

/// Tag row `k` has the tag and version of pre row `l`.
fn same_tv(v: &VerScan, k: usize, l: usize, Ghost(c): Ghost<Ctx>) -> (r: bool)
    requires ver_scan_ok(v, c), (k as int) < c.nt, (l as int) < c.npre,
    ensures r == (t_tag(c, k as int) == p_tag(c, l as int) && t_ver(c, k as int) == p_ver(c, l as int)),
    no_unwind
{
    proof { reveal(ver_scan_ok); lemma_views(c); }
    let x: &Cands = &*v.cx;
    let (a, al) = text_val(&v.t_tag, k, Ghost(c.nt));
    let (b, bl) = text_val(&x.p_tag, l, Ghost(c.npre));
    if !bytes_eq(a, al, b, bl) {
        return false;
    }
    let (a2, al2) = text_val(&v.t_ver, k, Ghost(c.nt));
    let (b2, bl2) = text_val(&x.p_ver, l, Ghost(c.npre));
    bytes_eq(a2, al2, b2, bl2)
}

/// A tag row with candidate `e`'s tag and version meets the candidate's slot.
proof fn lemma_match_slot(v: &VerScan, c: Ctx, e: int, k: int)
    requires ver_scan_ok(v, c), cand_tag(&*v.cx, c, e, k),
    ensures slot_hit(&*v.sl, c, v.sl.of@[e] as int, k),
{
    reveal(ver_scan_ok);
    lemma_cand_row(&*v.cx, c, e);
}

/// The tag row of candidate `e`.
fn ver_one(v: &VerScan, e: usize, Ghost(c): Ghost<Ctx>) -> (k: usize)
    requires ver_scan_ok(v, c), (e as int) < v.cx.list@.len(),
    ensures tag_answer(&*v.cx, c, e as int, k),
    no_unwind
{
    proof { reveal(ver_scan_ok); }
    let x: &Cands = &*v.cx;
    let ghost lg = cand_l(x, e as int);
    proof {
        lemma_cand_row(x, c, e as int);
    }
    let l = x.list[e].0;
    let s = v.sl.of[e];
    let k = v.tvrow[s];
    if k == NONE {
        proof {
            assert forall|k2: int| !#[trigger] tag_of(c, k2, p_tag(c, lg), p_ver(c, lg)) by {
                if tag_of(c, k2, p_tag(c, lg), p_ver(c, lg)) {
                    lemma_match_slot(v, c, e as int, k2);
                }
            }
        }
        return NONE;
    }
    proof {
        assert(slot_hit(&*v.sl, c, s as int, k as int));
        assert(l as int == lg);
    }
    if same_tv(v, k, l, Ghost(c)) {
        proof {
            assert(tag_of(c, k as int, p_tag(c, lg), p_ver(c, lg)));
        }
        return k;
    }
    ver_fallback(v, e, l, s, Ghost(c))
}

/// Candidate `e` (pre row `l`, slot `s`) after a hash collision: the pair of its slot whose tag row has its bytes.
fn ver_fallback(v: &VerScan, e: usize, l: usize, s: usize, Ghost(c): Ghost<Ctx>) -> (k: usize)
    requires
        ver_scan_ok(v, c), (e as int) < v.cx.list@.len(), l as int == cand_l(&*v.cx, e as int), (l as int) < c.npre,
        (e as int) < v.sl.of@.len(), s == v.sl.of@[e as int],
    ensures tag_answer(&*v.cx, c, e as int, k),
    no_unwind
{
    let ghost lg = l as int;
    let hs: &Vec<(usize, usize)> = &*v.hits;
    let nh = hs.len();
    let mut w: usize = 0;
    while w < nh
        invariant
            ver_scan_ok(v, c), hs == &*v.hits, nh == hs@.len(), w <= nh, (e as int) < v.cx.list@.len(),
            l as int == lg, lg == cand_l(&*v.cx, e as int), (e as int) < v.sl.of@.len(), s == v.sl.of@[e as int], 0 <= lg < c.npre,
            forall|w2: int| 0 <= w2 < w ==> !((#[trigger] hs@[w2]).0 == s
                && t_tag(c, hs@[w2].1 as int) == p_tag(c, lg) && t_ver(c, hs@[w2].1 as int) == p_ver(c, lg)),
        decreases nh - w,
    {
        proof { reveal(ver_scan_ok); }
        let (s2, k2) = hs[w];
        proof {
            assert(slot_hit(&*v.sl, c, s2 as int, k2 as int));
        }
        if s2 == s && same_tv(v, k2, l, Ghost(c)) {
            proof {
                assert(tag_of(c, k2 as int, p_tag(c, lg), p_ver(c, lg)));
                lemma_views(c);
                assert(v.t_tag.offsets@.len() == v.t_tag.offsets.len() as int);
                assert(k2 != NONE);
            }
            return k2;
        }
        w = w + 1;
    }
    proof {
        assert forall|k2: int| !#[trigger] tag_of(c, k2, p_tag(c, lg), p_ver(c, lg)) by {
            if tag_of(c, k2, p_tag(c, lg), p_ver(c, lg)) {
                reveal(ver_scan_ok);
                lemma_views(c);
                assert(v.t_tag.offsets@.len() == v.t_tag.offsets.len() as int);
                lemma_match_slot(v, c, e as int, k2);
                assert(hs@.contains((s, k2 as usize)));
                let w2 = choose|w2: int| 0 <= w2 < hs@.len() && hs@[w2] == (s, k2 as usize);
                assert(hs@[w2].0 == s && hs@[w2].1 as int == k2);
            }
        }
    }
    NONE
}

/// One candidate check task: candidates `lo..hi`, answers into `out[e - lo]`.
pub struct VerTask {
    pub lo: usize,
    pub hi: usize,
    pub scan: VerScan,
    pub out: Vec<usize>,
    pub ctx: Ghost<Ctx>,
}

impl WorkerTask for VerTask {
    type Output = Vec<usize>;

    open spec fn pre(&self) -> bool {
        &&& ver_scan_ok(&self.scan, self.ctx@)
        &&& self.lo <= self.hi && (self.hi as int) <= self.scan.cx.list@.len()
        &&& self.out@.len() == self.hi - self.lo
    }

    open spec fn post(&self, r: Vec<usize>) -> bool {
        &&& r@.len() == self.hi - self.lo
        &&& forall|q: int| 0 <= q < r@.len() ==> tag_answer(&*self.scan.cx, self.ctx@, self.lo + q, #[trigger] r@[q])
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (r: Vec<usize>) {
        let VerTask { lo, hi, scan, out, ctx } = self;
        let ghost c = ctx@;
        let mut out = out;
        let mut e = lo;
        while e < hi
            invariant
                ver_scan_ok(&scan, c), lo <= e <= hi, (hi as int) <= scan.cx.list@.len(), out@.len() == hi - lo,
                forall|q: int| 0 <= q < e - lo ==> tag_answer(&*scan.cx, c, lo + q, #[trigger] out@[q]),
            decreases hi - e,
        {
            let k = ver_one(&scan, e, Ghost(c));
            crate::gendb_entry::work::put(&mut out, e - lo, k);
            e = e + 1;
        }
        out
    }
}

/// A copy of the check's handles is a check of the same context.
pub proof fn lemma_ver_scan_copy(v: &VerScan, r: &VerScan, c: Ctx)
    requires
        ver_scan_ok(v, c),
        *r.cx == *v.cx && *r.sl == *v.sl && r.tvrow@ == v.tvrow@ && r.hits@ == v.hits@ && r.t_tag@ == v.t_tag@
            && r.t_ver@ == v.t_ver@,
    ensures ver_scan_ok(r, c),
{
    reveal(ver_scan_ok);
}

/// A copy of the scan's handles is a scan of the same context.
pub proof fn lemma_tag_scan_copy(t: &TagScan, r: &TagScan, c: Ctx)
    requires tag_scan_ok(t, c), r.t_tag@ == t.t_tag@ && r.t_ver@ == t.t_ver@ && r.t_abs@ == t.t_abs@ && *r.sl == *t.sl,
    ensures tag_scan_ok(r, c),
{
    reveal(tag_scan_ok);
}

} // verus!
