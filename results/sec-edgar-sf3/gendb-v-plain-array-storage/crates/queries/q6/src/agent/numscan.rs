//! Scan of `num` rows `lo..hi`: for each row with `uom = $1`, a member for its adsh, and a join key of its
//! partition equal to (member, tag, version), the task writes an item (partition, key id, value) into preallocated
//! buffers (at least `hi - lo` slots: keys are distinct, so a row has at most one item).
//!
//! `hits(i, p, g)`: `num` row `i` matches key `g` of partition `p`. `has_item`/`rowg` name the unique match, and
//! `ilist` lists the rows of a range with an item. For an entry `k` with key `g`, the `num` rows matching `k` are
//! exactly the rows whose item is `(p, g)` (`lemma_nmatch_item`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::common::bytes::*;
use crate::agent::common::chain::*;
use crate::agent::merge::lemma_ilist_append;
use crate::agent::ctx::*;
use crate::agent::keys::*;
use crate::agent::subidx::*;
use crate::agent::kg::*;
use crate::agent::sem::sub_key;

verus! {

/// The join key of `num` row `i` (with the member of its adsh).
pub open spec fn rowkey(c: Ctx, i: int) -> (int, Seq<u8>, Seq<u8>) {
    (sub_for(c, n_adsh(c, i)), n_tag(c, i), n_ver(c, i))
}

/// The partition of `num` row `i`.
pub open spec fn rpart(c: Ctx, pbits: u64, i: int) -> int {
    tpart(n_tag(c, i), pbits)
}

/// The key indexes of all partitions are built from their entries.
pub open spec fn kgs_ok(kgs: Seq<KgPart>, c: Ctx, pbits: u64) -> bool {
    &&& kgs.len() == pow2u(pbits)
    &&& forall|p: int| 0 <= p < kgs.len() ==> kg_wf(#[trigger] kgs[p], c, pbits, p, plist(c, pbits, p, 0, c.q))
}

/// `num` row `i` matches key `g` of partition `p`.
pub open spec fn hits(c: Ctx, pbits: u64, kgs: Seq<KgPart>, i: int, p: int, g: int) -> bool {
    &&& num_ok(c, i)
    &&& has_member(c, n_adsh(c, i))
    &&& rpart(c, pbits, i) == p
    &&& 0 <= p < kgs.len()
    &&& 0 <= g < kgs[p].nkg
    &&& kg_key(kgs[p], c, g) == rowkey(c, i)
}

pub open spec fn has_item(c: Ctx, pbits: u64, kgs: Seq<KgPart>, i: int) -> bool {
    exists|g: int| #[trigger] hits(c, pbits, kgs, i, rpart(c, pbits, i), g)
}

/// The key a row with an item matches.
pub open spec fn rowg(c: Ctx, pbits: u64, kgs: Seq<KgPart>, i: int) -> int {
    choose|g: int| #[trigger] hits(c, pbits, kgs, i, rpart(c, pbits, i), g)
}

/// The rows of `lo..hi` with an item, in row order.
pub open spec fn ilist(c: Ctx, pbits: u64, kgs: Seq<KgPart>, lo: int, hi: int) -> Seq<int>
    decreases hi - lo,
{
    if hi <= lo {
        Seq::empty()
    } else {
        let d = ilist(c, pbits, kgs, lo, hi - 1);
        if has_item(c, pbits, kgs, hi - 1) { d.push(hi - 1) } else { d }
    }
}

/// A row matches one key at most.
pub proof fn lemma_hits_unique(c: Ctx, pbits: u64, kgs: Seq<KgPart>, i: int, g: int)
    requires kgs_ok(kgs, c, pbits), hits(c, pbits, kgs, i, rpart(c, pbits, i), g),
    ensures has_item(c, pbits, kgs, i), rowg(c, pbits, kgs, i) == g,
{
    let p = rpart(c, pbits, i);
    let g2 = rowg(c, pbits, kgs, i);
    assert(kg_wf(kgs[p], c, pbits, p, plist(c, pbits, p, 0, c.q)));
    lemma_kg_facts(kgs[p], c, pbits, p, plist(c, pbits, p, 0, c.q));
    if g2 != g {
        assert(kg_key(kgs[p], c, g) != kg_key(kgs[p], c, g2));
    }
}

/// The `num` rows matching entry `k`, whose key is `g` in partition `p`, are the rows whose item is `(p, g)`.
pub proof fn lemma_nmatch_item(c: Ctx, pbits: u64, kgs: Seq<KgPart>, p: int, g: int, k: int, i: int)
    requires
        kgs_ok(kgs, c, pbits), 0 <= p < kgs.len(),
        pre_ok(c, k), epart(c, pbits, k) == p,
        0 <= g < kgs[p].nkg, kg_key(kgs[p], c, g) == ekey(c, k),
    ensures
        nmatch(c, i, k) == (has_item(c, pbits, kgs, i) && rpart(c, pbits, i) == p && rowg(c, pbits, kgs, i) == g),
{
    lemma_sub_for(c, p_adsh(c, k));
    if nmatch(c, i, k) {
        assert(n_adsh(c, i) == p_adsh(c, k));
        assert(rowkey(c, i) == ekey(c, k));
        assert(hits(c, pbits, kgs, i, p, g));
        lemma_hits_unique(c, pbits, kgs, i, g);
    }
    if has_item(c, pbits, kgs, i) && rpart(c, pbits, i) == p && rowg(c, pbits, kgs, i) == g {
        assert(hits(c, pbits, kgs, i, p, g));
        lemma_sub_for(c, n_adsh(c, i));
        assert(sub_for(c, n_adsh(c, i)) == esub(c, k));
        assert(n_adsh(c, i) == s_adsh(c, esub(c, k)));
        assert(n_adsh(c, i) == p_adsh(c, k));
    }
}

/// Rows per block of the staged scan.
pub const BLK: usize = 512;

/// The read-only inputs of a `num` scan: the columns it reads and the indexes it probes.
pub struct NumScan {
    pub adsh: TextCol,
    pub uom: TextCol,
    pub tag: TextCol,
    pub ver: TextCol,
    pub value: &'static [i128],
    pub p0: &'static [u8],
    pub p0len: usize,
    pub pbits: u64,
    pub sub: Arc<SubIdx>,
    pub kgs: Arc<Vec<KgPart>>,
    pub padsh: TextCol,
    pub ptag: TextCol,
    pub pver: TextCol,
}

/// One task: the rows `lo..hi`, its item buffers (`ip`, `ig`, `iv`) and its block scratch (`bi`, `bp`, `bh`, `bc`).
pub struct NumTask {
    pub lo: usize,
    pub hi: usize,
    pub s: NumScan,
    pub ip: Vec<u8>,
    pub ig: Vec<usize>,
    pub iv: Vec<i128>,
    pub bi: Vec<usize>,
    pub bp: Vec<usize>,
    pub bh: Vec<u64>,
    pub bc: Vec<usize>,
    pub ctx: Ghost<Ctx>,
}

pub struct NumOut {
    pub ip: Vec<u8>,
    pub ig: Vec<usize>,
    pub iv: Vec<i128>,
    pub len: usize,
}

/// The items `o` list the rows `rows` with their partition, key and value.
pub open spec fn items_ok(o: NumOut, c: Ctx, pbits: u64, kgs: Seq<KgPart>, rows: Seq<int>) -> bool {
    &&& o.len as int == rows.len()
    &&& o.len <= o.ip@.len() && o.len <= o.ig@.len() && o.len <= o.iv@.len()
    &&& forall|j: int| 0 <= j < o.len ==> #[trigger] o.ip@[j] as int == rpart(c, pbits, rows[j])
    &&& forall|j: int| 0 <= j < o.len ==> #[trigger] o.ig@[j] as int == rowg(c, pbits, kgs, rows[j])
    &&& forall|j: int| 0 <= j < o.len ==> #[trigger] o.iv@[j] as int == n_val(c, rows[j])
}

/// The output lists the rows of `lo..hi` with an item, with their partition, key and value.
pub open spec fn num_out_ok(o: NumOut, c: Ctx, pbits: u64, kgs: Seq<KgPart>, lo: int, hi: int) -> bool {
    items_ok(o, c, pbits, kgs, ilist(c, pbits, kgs, lo, hi))
}

/// The columns and indexes a `num` scan reads.
#[verifier::opaque]
pub open spec fn scan_ok(s: NumScan, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& sub_key(c)
    &&& s.adsh@ == n_adsh_v(c)
    &&& s.uom@ == n_uom_v(c)
    &&& s.tag@ == n_tag_v(c)
    &&& s.ver@ == n_ver_v(c)
    &&& s.value@ == n_val_s(c)
    &&& s.p0@ == c.uom
    &&& s.p0len as int == c.uom.len()
    &&& s.pbits <= MAX_PBITS
    &&& sub_idx_wf(*s.sub, c)
    &&& kgs_ok((*s.kgs)@, c, s.pbits)
    &&& s.padsh@ == p_adsh_v(c)
    &&& s.ptag@ == p_tag_v(c)
    &&& s.pver@ == p_ver_v(c)
}

pub proof fn lemma_scan_facts(s: NumScan, c: Ctx)
    requires scan_ok(s, c),
    ensures
        ctx_ok(c), sub_key(c),
        s.adsh@ == n_adsh_v(c), s.uom@ == n_uom_v(c), s.tag@ == n_tag_v(c), s.ver@ == n_ver_v(c), s.value@ == n_val_s(c),
        n_val_s(c).len() == c.n,
        text_wf(n_adsh_v(c), c.n), text_wf(n_tag_v(c), c.n), text_wf(n_ver_v(c), c.n), text_wf(n_uom_v(c), c.n),
        s.p0@ == c.uom, s.p0len as int == c.uom.len(), s.pbits <= MAX_PBITS,
        sub_idx_wf(*s.sub, c), kgs_ok((*s.kgs)@, c, s.pbits),
        (*s.kgs)@.len() == pow2u(s.pbits),
        s.padsh@ == p_adsh_v(c), s.ptag@ == p_tag_v(c), s.pver@ == p_ver_v(c),
{
    reveal(scan_ok);
    lemma_views_wf(c);
}

/// The rows with an item.
pub open spec fn itemp(c: Ctx, pbits: u64, kgs: Seq<KgPart>) -> spec_fn(int) -> bool {
    |r: int| has_item(c, pbits, kgs, r)
}

/// `n` slots of a row buffer, as integers.
pub open spec fn crow(b: Seq<usize>, n: int) -> Seq<int> {
    Seq::new(n as nat, |t: int| b[t] as int)
}

/// A candidate: `num` row `r` with `uom = $1`, its partition `p` and the hash `h` of its (tag, adsh, version).
pub open spec fn cand_ok(c: Ctx, pbits: u64, r: int, p: int, h: u64) -> bool {
    &&& 0 <= r < c.n
    &&& num_ok(c, r)
    &&& p == rpart(c, pbits, r)
    &&& 0 <= p < pow2u(pbits)
    &&& h == kh_spec(sig_spec(n_tag(c, r)), sig_spec(n_adsh(c, r)) as int, sig_spec(n_ver(c, r)))
}

/// The walk of candidate `r` (partition `p`, hash `h`) stands at `cur`.
pub open spec fn walk_at(kgs: Seq<KgPart>, c: Ctx, r: int, p: int, h: u64, cur: usize) -> bool {
    walk_ok(cur, all_in(), kg_bkt(kgs[p]), kgs[p].nkg as int, hbkt(kgs[p], h),
        not_has(kgs[p], c, n_adsh(c, r), n_tag(c, r), n_ver(c, r)))
}

/// A candidate none of whose partition's keys has its bytes has no item.
pub proof fn lemma_no_item(c: Ctx, pbits: u64, kgs: Seq<KgPart>, r: int, p: int, h: u64)
    requires
        kgs_ok(kgs, c, pbits), cand_ok(c, pbits, r, p, h),
        forall|g: int| 0 <= g < kgs[p].nkg ==> !#[trigger] node_has(kgs[p], c, g, n_adsh(c, r), n_tag(c, r), n_ver(c, r)),
    ensures !has_item(c, pbits, kgs, r),
{
    if has_item(c, pbits, kgs, r) {
        let g2 = choose|g2: int| #[trigger] hits(c, pbits, kgs, r, rpart(c, pbits, r), g2);
        let x = kgs[p];
        assert(kg_wf(x, c, pbits, p, plist(c, pbits, p, 0, c.q)));
        lemma_kg_facts(x, c, pbits, p, plist(c, pbits, p, 0, c.q));
        assert(kg_key(x, c, g2) == rowkey(c, r));
        lemma_trip_key(c, x.nodes@[g2].2 as int, n_adsh(c, r), n_tag(c, r), n_ver(c, r));
        assert(node_has(x, c, g2, n_adsh(c, r), n_tag(c, r), n_ver(c, r)));
    }
}

/// A candidate whose bytes key `g` of its partition has has the item `(p, g)`.
pub proof fn lemma_item_found(c: Ctx, pbits: u64, kgs: Seq<KgPart>, r: int, p: int, h: u64, g: int)
    requires
        kgs_ok(kgs, c, pbits), cand_ok(c, pbits, r, p, h), 0 <= g < kgs[p].nkg,
        node_has(kgs[p], c, g, n_adsh(c, r), n_tag(c, r), n_ver(c, r)),
    ensures has_item(c, pbits, kgs, r), rowg(c, pbits, kgs, r) == g,
{
    let x = kgs[p];
    assert(kg_wf(x, c, pbits, p, plist(c, pbits, p, 0, c.q)));
    lemma_kg_facts(x, c, pbits, p, plist(c, pbits, p, 0, c.q));
    let k2 = x.nodes@[g].2 as int;
    assert(pre_ok(c, k2));
    assert(has_member(c, n_adsh(c, r)));
    lemma_trip_key(c, k2, n_adsh(c, r), n_tag(c, r), n_ver(c, r));
    assert(hits(c, pbits, kgs, r, p, g));
    lemma_hits_unique(c, pbits, kgs, r, g);
}

/// A candidate whose walk ended at `NONE` has no item.
pub proof fn lemma_walk_none(c: Ctx, pbits: u64, kgs: Seq<KgPart>, r: int, p: int, h: u64)
    requires kgs_ok(kgs, c, pbits), cand_ok(c, pbits, r, p, h), walk_at(kgs, c, r, p, h, NONE),
    ensures !has_item(c, pbits, kgs, r),
{
    let x = kgs[p];
    let pr = not_has(x, c, n_adsh(c, r), n_tag(c, r), n_ver(c, r));
    assert(kg_wf(x, c, pbits, p, plist(c, pbits, p, 0, c.q)));
    lemma_walk_done(all_in(), kg_bkt(x), x.nkg as int, hbkt(x, h), pr);
    assert forall|g: int| 0 <= g < x.nkg implies !#[trigger] node_has(x, c, g, n_adsh(c, r), n_tag(c, r), n_ver(c, r)) by {
        if node_has(x, c, g, n_adsh(c, r), n_tag(c, r), n_ver(c, r)) {
            lemma_node_hash(x, c, pbits, p, plist(c, pbits, p, 0, c.q), g, n_adsh(c, r), n_tag(c, r), n_ver(c, r));
            assert(all_in()(g));
            assert(!pr(g));
        }
    }
    lemma_no_item(c, pbits, kgs, r, p, h);
}

/// Filtering a sequence with one more element.
pub proof fn lemma_filter_push(s: Seq<int>, x: int, f: spec_fn(int) -> bool)
    ensures s.push(x).filter(f) == if f(x) { s.filter(f).push(x) } else { s.filter(f) },
{
    reveal(Seq::filter);
    assert(s.push(x).drop_last() =~= s);
}

/// The empty sequence filters to itself.
pub proof fn lemma_filter_empty(f: spec_fn(int) -> bool)
    ensures Seq::<int>::empty().filter(f) == Seq::<int>::empty(),
{
    reveal(Seq::filter);
}

/// Dropping an element the filter rejects does not change the filtered sequence.
pub proof fn lemma_filter_drop(a: Seq<int>, x: int, b: Seq<int>, f: spec_fn(int) -> bool)
    requires !f(x),
    ensures (a + seq![x] + b).filter(f) == (a + b).filter(f),
{
    Seq::filter_distributes_over_add(a + seq![x], b, f);
    Seq::filter_distributes_over_add(a, seq![x], f);
    Seq::filter_distributes_over_add(a, b, f);
    lemma_filter_push(Seq::<int>::empty(), x, f);
    assert(Seq::<int>::empty().push(x) =~= seq![x]);
    lemma_filter_empty(f);
    assert(a.filter(f) + Seq::<int>::empty() =~= a.filter(f));
}

/// Rows `i..e` as a candidate list in the scratch: `bi[0..nc)` are candidates and filter to `ilist(i, e)`.
pub open spec fn block_ok(c: Ctx, pbits: u64, kgs: Seq<KgPart>, bi: Seq<usize>, bp: Seq<usize>, bh: Seq<u64>, nc: int,
    t0: Seq<int>) -> bool {
    &&& 0 <= nc <= bi.len() && nc <= bp.len() && nc <= bh.len()
    &&& forall|t: int| 0 <= t < nc ==> #[trigger] cand_ok(c, pbits, bi[t] as int, bp[t] as int, bh[t])
    &&& crow(bi, nc).filter(itemp(c, pbits, kgs)) == t0
}

/// Stage A: the candidates among rows `i..e`: a member may have their adsh (the member filter) and `uom = $1`.
fn stage_rows(s: &NumScan, i: usize, e: usize, bi: &mut Vec<usize>, bp: &mut Vec<usize>, bh: &mut Vec<u64>,
    Ghost(c): Ghost<Ctx>) -> (nc: usize)
    requires
        scan_ok(*s, c), i <= e, e as int <= c.n, e - i <= BLK,
        old(bi)@.len() == BLK, old(bp)@.len() == BLK, old(bh)@.len() == BLK,
    ensures
        final(bi)@.len() == BLK, final(bp)@.len() == BLK, final(bh)@.len() == BLK, nc <= e - i,
        block_ok(c, s.pbits, (*s.kgs)@, final(bi)@, final(bp)@, final(bh)@, nc as int, ilist(c, s.pbits, (*s.kgs)@, i as int, e as int)),
    no_unwind
{
    let ghost kv = (*s.kgs)@;
    let ghost f = itemp(c, s.pbits, kv);
    let sub: &SubIdx = &*s.sub;
    proof {
        lemma_scan_facts(*s, c);
        assert(crow(bi@, 0) =~= Seq::<int>::empty());
        lemma_filter_empty(f);
        assert(ilist(c, s.pbits, kv, i as int, i as int) =~= Seq::<int>::empty());
    }
    let mut nc: usize = 0;
    let mut r: usize = i;
    while r < e
        invariant
            scan_ok(*s, c), i <= r <= e, e as int <= c.n, e - i <= BLK, kv == (*s.kgs)@, f == itemp(c, s.pbits, kv),
            sub_idx_wf(*sub, c),
            bi@.len() == BLK, bp@.len() == BLK, bh@.len() == BLK, nc <= r - i,
            block_ok(c, s.pbits, kv, bi@, bp@, bh@, nc as int, ilist(c, s.pbits, kv, i as int, r as int)),
        decreases e - r,
    {
        proof {
            lemma_scan_facts(*s, c);
        }
        let ghost ri = r as int;
        let a = text_of(&s.adsh, r, Ghost(c.n));
        let al = text_len(&s.adsh, r, Ghost(c.n));
        let ah = sig(a, al);
        let cand = sub_maybe(sub, ah, Ghost(c)) && text_is(&s.uom, r, Ghost(c.n), s.p0, s.p0len);
        if cand {
            let tb = text_of(&s.tag, r, Ghost(c.n));
            let tl = text_len(&s.tag, r, Ghost(c.n));
            let th = sig(tb, tl);
            let p = part_of(th, s.pbits, Ghost(n_tag(c, ri)));
            let vb = text_of(&s.ver, r, Ghost(c.n));
            let vl = text_len(&s.ver, r, Ghost(c.n));
            let vh = sig(vb, vl);
            let ghost ob = bi@;
            bi[nc] = r;
            bp[nc] = p;
            bh[nc] = kha(th, ah, vh);
            proof {
                assert(crow(bi@, nc + 1) =~= crow(ob, nc as int).push(ri));
                lemma_filter_push(crow(ob, nc as int), ri, f);
                assert(cand_ok(c, s.pbits, ri, p as int, bh@[nc as int]));
            }
            nc = nc + 1;
        } else {
            proof {
                if has_item(c, s.pbits, kv, ri) {
                    lemma_sub_for(c, n_adsh(c, ri));
                    assert(num_ok(c, ri));
                    assert(member(c, sub_for(c, n_adsh(c, ri))));
                }
            }
        }
        r = r + 1;
    }
    nc
}

/// The item of `num` row `i`: `(partition, key)`, or `None`.
pub fn row_item(i: usize, adsh: &TextCol, uom: &TextCol, tag: &TextCol, ver: &TextCol, p0: &'static [u8], p0len: usize,
    pbits: u64, sub: &SubIdx, kgs: &Vec<KgPart>, padsh: &TextCol, ptag: &TextCol, pver: &TextCol, Ghost(c): Ghost<Ctx>)
    -> (r: (usize, usize))
    requires
        ctx_ok(c), sub_key(c), (i as int) < c.n,
        adsh@ == n_adsh_v(c), uom@ == n_uom_v(c), tag@ == n_tag_v(c), ver@ == n_ver_v(c),
        p0@ == c.uom, p0len as int == c.uom.len(), pbits <= MAX_PBITS,
        sub_idx_wf(*sub, c), kgs_ok(kgs@, c, pbits), padsh@ == p_adsh_v(c), ptag@ == p_tag_v(c), pver@ == p_ver_v(c),
    ensures
        r.1 != NONE ==> r.0 < 64 && has_item(c, pbits, kgs@, i as int) && r.0 as int == rpart(c, pbits, i as int)
            && r.1 as int == rowg(c, pbits, kgs@, i as int),
        r.1 == NONE ==> !has_item(c, pbits, kgs@, i as int),
    no_unwind
{
    proof {
        lemma_views_wf(c);
    }
    let ghost ii = i as int;
    let a = text_of(adsh, i, Ghost(c.n));
    let al = text_len(adsh, i, Ghost(c.n));
    let ah = sig(a, al);
    if !sub_maybe(sub, ah, Ghost(c)) {
        proof {
            if has_member(c, n_adsh(c, ii)) {
                lemma_sub_for(c, n_adsh(c, ii));
            }
        }
        return (0, NONE);
    }
    if !text_is(uom, i, Ghost(c.n), p0, p0len) {
        proof {
            assert(!num_ok(c, ii));
        }
        return (0, NONE);
    }
    let tb = text_of(tag, i, Ghost(c.n));
    let tl = text_len(tag, i, Ghost(c.n));
    let th = sig(tb, tl);
    let p = part_of(th, pbits, Ghost(n_tag(c, ii)));
    proof {
        assert(kgs@.len() == pow2u(pbits));
        assert(kg_wf(kgs@[p as int], c, pbits, p as int, plist(c, pbits, p as int, 0, c.q)));
    }
    if !kg_tag_maybe(&kgs[p], th, Ghost(c), Ghost(pbits), Ghost(p as int), Ghost(plist(c, pbits, p as int, 0, c.q))) {
        proof {
            if has_item(c, pbits, kgs@, ii) {
                let g2 = choose|g2: int| #[trigger] hits(c, pbits, kgs@, ii, rpart(c, pbits, ii), g2);
                assert(kg_key(kgs@[p as int], c, g2) == rowkey(c, ii));
                assert(p_tag(c, kgs@[p as int].nodes@[g2].2 as int) == n_tag(c, ii));
            }
        }
        return (0, NONE);
    }
    let vb = text_of(ver, i, Ghost(c.n));
    let vl = text_len(ver, i, Ghost(c.n));
    let vh = sig(vb, vl);
    let h = kha(th, ah, vh);
    let ghost x = kgs@[p as int];
    let g = kg_find(&kgs[p], a, al, tb, tl, vb, vl, h, padsh, ptag, pver, Ghost(c), Ghost(pbits), Ghost(p as int),
        Ghost(plist(c, pbits, p as int, 0, c.q)));
    proof {
        lemma_kg_facts(x, c, pbits, p as int, plist(c, pbits, p as int, 0, c.q));
    }
    if g == NONE {
        proof {
            if has_item(c, pbits, kgs@, ii) {
                let g2 = choose|g2: int| #[trigger] hits(c, pbits, kgs@, ii, rpart(c, pbits, ii), g2);
                assert(kg_key(x, c, g2) == rowkey(c, ii));
                lemma_trip_key(c, x.nodes@[g2].2 as int, n_adsh(c, ii), n_tag(c, ii), n_ver(c, ii));
                assert(node_has(x, c, g2, a@, tb@, vb@));
            }
        }
        return (0, NONE);
    }
    proof {
        let k2 = x.nodes@[g as int].2 as int;
        assert(pre_ok(c, k2));
        assert(p_adsh(c, k2) == n_adsh(c, ii));
        assert(has_member(c, n_adsh(c, ii)));
        lemma_trip_key(c, k2, n_adsh(c, ii), n_tag(c, ii), n_ver(c, ii));
        assert(kg_key(x, c, g as int) == rowkey(c, ii));
        assert(num_ok(c, ii));
        assert(hits(c, pbits, kgs@, ii, p as int, g as int));
        lemma_hits_unique(c, pbits, kgs@, ii, g as int);
    }
    (p, g)
}


/// Stage B1: keep the candidates whose key hash has its bit in their partition's filter.
fn stage_filter(s: &NumScan, nc: usize, bi: &mut Vec<usize>, bp: &mut Vec<usize>, bh: &mut Vec<u64>, Ghost(c): Ghost<Ctx>,
    Ghost(t0): Ghost<Seq<int>>) -> (ns: usize)
    requires
        scan_ok(*s, c), old(bi)@.len() == BLK, old(bp)@.len() == BLK, old(bh)@.len() == BLK, nc <= BLK,
        block_ok(c, s.pbits, (*s.kgs)@, old(bi)@, old(bp)@, old(bh)@, nc as int, t0),
    ensures
        final(bi)@.len() == BLK, final(bp)@.len() == BLK, final(bh)@.len() == BLK, ns <= nc,
        block_ok(c, s.pbits, (*s.kgs)@, final(bi)@, final(bp)@, final(bh)@, ns as int, t0),
    no_unwind
{
    let ghost kv = (*s.kgs)@;
    let ghost f = itemp(c, s.pbits, kv);
    let ghost ob = bi@;
    let ghost op = bp@;
    let ghost oh = bh@;
    let ghost l0 = crow(ob, nc as int);
    let kgs: &Vec<KgPart> = &*s.kgs;
    proof {
        lemma_scan_facts(*s, c);
        assert(crow(bi@, 0) + l0.subrange(0, nc as int) =~= l0);
    }
    let mut ns: usize = 0;
    let mut j: usize = 0;
    while j < nc
        invariant
            scan_ok(*s, c), kv == (*s.kgs)@, kv == kgs@, f == itemp(c, s.pbits, kv), l0 == crow(ob, nc as int),
            bi@.len() == BLK, bp@.len() == BLK, bh@.len() == BLK, ns <= j <= nc, nc <= BLK,
            ob.len() == BLK, op.len() == BLK, oh.len() == BLK,
            forall|t: int| 0 <= t < nc ==> #[trigger] cand_ok(c, s.pbits, ob[t] as int, op[t] as int, oh[t]),
            forall|t: int| 0 <= t < ns ==> #[trigger] cand_ok(c, s.pbits, bi@[t] as int, bp@[t] as int, bh@[t]),
            forall|t: int| j <= t < nc ==> #[trigger] bi@[t] == ob[t] && bp@[t] == op[t] && bh@[t] == oh[t],
            (crow(bi@, ns as int) + l0.subrange(j as int, nc as int)).filter(f) == t0,
        decreases nc - j,
    {
        proof {
            lemma_scan_facts(*s, c);
        }
        let r = bi[j];
        let p = bp[j];
        let h = bh[j];
        proof {
            assert(cand_ok(c, s.pbits, ob[j as int] as int, op[j as int] as int, oh[j as int]));
            assert(kg_wf(kv[p as int], c, s.pbits, p as int, plist(c, s.pbits, p as int, 0, c.q)));
        }
        let keep = kg_maybe(&kgs[p], h, Ghost(c), Ghost(s.pbits), Ghost(p as int), Ghost(plist(c, s.pbits, p as int, 0, c.q)));
        let ghost pre = crow(bi@, ns as int);
        bi[ns] = r;
        bp[ns] = p;
        bh[ns] = h;
        proof {
            let ri = r as int;
            assert(l0.subrange(j as int, nc as int) =~= seq![ri] + l0.subrange(j + 1, nc as int));
            if keep {
                assert(crow(bi@, ns + 1) =~= pre.push(ri));
                assert(pre.push(ri) + l0.subrange(j + 1, nc as int) =~= pre + seq![ri] + l0.subrange(j + 1, nc as int));
            } else {
                assert(crow(bi@, ns as int) =~= pre);
                if has_item(c, s.pbits, kv, ri) {
                    let x = kv[p as int];
                    lemma_kg_facts(x, c, s.pbits, p as int, plist(c, s.pbits, p as int, 0, c.q));
                    let g2 = choose|g2: int| #[trigger] hits(c, s.pbits, kv, ri, rpart(c, s.pbits, ri), g2);
                    assert(kg_key(x, c, g2) == rowkey(c, ri));
                    lemma_trip_key(c, x.nodes@[g2].2 as int, n_adsh(c, ri), n_tag(c, ri), n_ver(c, ri));
                    assert(node_has(x, c, g2, n_adsh(c, ri), n_tag(c, ri), n_ver(c, ri)));
                }
                lemma_filter_drop(pre, ri, l0.subrange(j + 1, nc as int), f);
                assert(pre + seq![ri] + l0.subrange(j + 1, nc as int) =~= pre + (seq![ri] + l0.subrange(j + 1, nc as int)));
            }
        }
        ns = ns + if keep { 1 } else { 0 };
        j = j + 1;
    }
    proof {
        assert(crow(bi@, ns as int) + l0.subrange(nc as int, nc as int) =~= crow(bi@, ns as int));
    }
    ns
}

/// Candidates with their walk positions `bc[0..n)`.
pub open spec fn walks_ok(c: Ctx, pbits: u64, kgs: Seq<KgPart>, bi: Seq<usize>, bp: Seq<usize>, bh: Seq<u64>, bc: Seq<usize>,
    n: int) -> bool {
    &&& n <= bc.len()
    &&& forall|t: int| 0 <= t < n ==> #[trigger] walk_at(kgs, c, bi[t] as int, bp[t] as int, bh[t], bc[t])
}

/// Stage B2: the head of each candidate's bucket; candidates with an empty bucket are dropped.
fn stage_head(s: &NumScan, nc: usize, bi: &mut Vec<usize>, bp: &mut Vec<usize>, bh: &mut Vec<u64>, bc: &mut Vec<usize>,
    Ghost(c): Ghost<Ctx>, Ghost(t0): Ghost<Seq<int>>) -> (ns: usize)
    requires
        scan_ok(*s, c), old(bi)@.len() == BLK, old(bp)@.len() == BLK, old(bh)@.len() == BLK, old(bc)@.len() == BLK, nc <= BLK,
        block_ok(c, s.pbits, (*s.kgs)@, old(bi)@, old(bp)@, old(bh)@, nc as int, t0),
    ensures
        final(bi)@.len() == BLK, final(bp)@.len() == BLK, final(bh)@.len() == BLK, final(bc)@.len() == BLK, ns <= nc,
        block_ok(c, s.pbits, (*s.kgs)@, final(bi)@, final(bp)@, final(bh)@, ns as int, t0),
        walks_ok(c, s.pbits, (*s.kgs)@, final(bi)@, final(bp)@, final(bh)@, final(bc)@, ns as int),
        forall|t: int| 0 <= t < ns ==> #[trigger] final(bc)@[t] != NONE,
    no_unwind
{
    let ghost kv = (*s.kgs)@;
    let ghost f = itemp(c, s.pbits, kv);
    let ghost ob = bi@;
    let ghost op = bp@;
    let ghost oh = bh@;
    let ghost l0 = crow(ob, nc as int);
    let kgs: &Vec<KgPart> = &*s.kgs;
    proof {
        lemma_scan_facts(*s, c);
        assert(crow(bi@, 0) + l0.subrange(0, nc as int) =~= l0);
    }
    let mut ns: usize = 0;
    let mut j: usize = 0;
    while j < nc
        invariant
            scan_ok(*s, c), kv == (*s.kgs)@, kv == kgs@, f == itemp(c, s.pbits, kv), l0 == crow(ob, nc as int),
            bi@.len() == BLK, bp@.len() == BLK, bh@.len() == BLK, bc@.len() == BLK, ns <= j <= nc, nc <= BLK,
            ob.len() == BLK, op.len() == BLK, oh.len() == BLK,
            forall|t: int| 0 <= t < nc ==> #[trigger] cand_ok(c, s.pbits, ob[t] as int, op[t] as int, oh[t]),
            forall|t: int| 0 <= t < ns ==> #[trigger] cand_ok(c, s.pbits, bi@[t] as int, bp@[t] as int, bh@[t]),
            forall|t: int| 0 <= t < ns ==> #[trigger] walk_at(kv, c, bi@[t] as int, bp@[t] as int, bh@[t], bc@[t]),
            forall|t: int| 0 <= t < ns ==> #[trigger] bc@[t] != NONE,
            forall|t: int| j <= t < nc ==> #[trigger] bi@[t] == ob[t] && bp@[t] == op[t] && bh@[t] == oh[t],
            (crow(bi@, ns as int) + l0.subrange(j as int, nc as int)).filter(f) == t0,
        decreases nc - j,
    {
        proof {
            lemma_scan_facts(*s, c);
        }
        let r = bi[j];
        let p = bp[j];
        let h = bh[j];
        let ghost ri = r as int;
        proof {
            assert(cand_ok(c, s.pbits, ob[j as int] as int, op[j as int] as int, oh[j as int]));
            assert(kg_wf(kv[p as int], c, s.pbits, p as int, plist(c, s.pbits, p as int, 0, c.q)));
        }
        let cur = kg_head(&kgs[p], h, Ghost(c), Ghost(s.pbits), Ghost(p as int), Ghost(plist(c, s.pbits, p as int, 0, c.q)),
            Ghost(n_adsh(c, ri)), Ghost(n_tag(c, ri)), Ghost(n_ver(c, ri)));
        let ghost pre = crow(bi@, ns as int);
        bi[ns] = r;
        bp[ns] = p;
        bh[ns] = h;
        bc[ns] = cur;
        let keep = cur != NONE;
        proof {
            assert(walk_at(kv, c, ri, p as int, h, cur));
            assert(l0.subrange(j as int, nc as int) =~= seq![ri] + l0.subrange(j + 1, nc as int));
            if keep {
                assert(crow(bi@, ns + 1) =~= pre.push(ri));
                assert(pre.push(ri) + l0.subrange(j + 1, nc as int) =~= pre + seq![ri] + l0.subrange(j + 1, nc as int));
            } else {
                assert(crow(bi@, ns as int) =~= pre);
                lemma_walk_none(c, s.pbits, kv, ri, p as int, h);
                lemma_filter_drop(pre, ri, l0.subrange(j + 1, nc as int), f);
                assert(pre + seq![ri] + l0.subrange(j + 1, nc as int) =~= pre + (seq![ri] + l0.subrange(j + 1, nc as int)));
            }
        }
        ns = ns + if keep { 1 } else { 0 };
        j = j + 1;
    }
    proof {
        assert(crow(bi@, ns as int) + l0.subrange(nc as int, nc as int) =~= crow(bi@, ns as int));
    }
    ns
}

/// Stage C: one step of each candidate's walk (past a first node of another hash); `all` steps every candidate,
/// otherwise only those not at `NONE`.
fn stage_step(s: &NumScan, n: usize, bi: &Vec<usize>, bp: &Vec<usize>, bh: &Vec<u64>, bc: &mut Vec<usize>, all: bool,
    Ghost(c): Ghost<Ctx>, Ghost(t0): Ghost<Seq<int>>)
    requires
        scan_ok(*s, c), bi@.len() == BLK, bp@.len() == BLK, bh@.len() == BLK, old(bc)@.len() == BLK, n <= BLK,
        block_ok(c, s.pbits, (*s.kgs)@, bi@, bp@, bh@, n as int, t0),
        walks_ok(c, s.pbits, (*s.kgs)@, bi@, bp@, bh@, old(bc)@, n as int),
        all ==> forall|t: int| 0 <= t < n ==> #[trigger] old(bc)@[t] != NONE,
    ensures
        final(bc)@.len() == BLK,
        walks_ok(c, s.pbits, (*s.kgs)@, bi@, bp@, bh@, final(bc)@, n as int),
    no_unwind
{
    let ghost kv = (*s.kgs)@;
    let ghost oc = bc@;
    let kgs: &Vec<KgPart> = &*s.kgs;
    let mut j: usize = 0;
    while j < n
        invariant
            scan_ok(*s, c), kv == (*s.kgs)@, kv == kgs@, bi@.len() == BLK, bp@.len() == BLK, bh@.len() == BLK,
            bc@.len() == BLK, j <= n, n <= BLK, oc.len() == BLK,
            block_ok(c, s.pbits, kv, bi@, bp@, bh@, n as int, t0),
            forall|t: int| 0 <= t < n ==> #[trigger] walk_at(kv, c, bi@[t] as int, bp@[t] as int, bh@[t], bc@[t]),
            forall|t: int| j <= t < n ==> #[trigger] bc@[t] == oc[t],
            all ==> forall|t: int| 0 <= t < n ==> #[trigger] oc[t] != NONE,
        decreases n - j,
    {
        proof {
            lemma_scan_facts(*s, c);
        }
        let r = bi[j];
        let p = bp[j];
        let h = bh[j];
        let cur = bc[j];
        let ghost ri = r as int;
        proof {
            assert(cand_ok(c, s.pbits, ri, p as int, h));
            assert(walk_at(kv, c, ri, p as int, h, cur));
            assert(kg_wf(kv[p as int], c, s.pbits, p as int, plist(c, s.pbits, p as int, 0, c.q)));
            if all {
                assert(oc[j as int] != NONE);
            }
        }
        if all || cur != NONE {
            let nx = kg_step(&kgs[p], cur, h, Ghost(c), Ghost(s.pbits), Ghost(p as int), Ghost(plist(c, s.pbits, p as int, 0, c.q)),
                Ghost(n_adsh(c, ri)), Ghost(n_tag(c, ri)), Ghost(n_ver(c, ri)));
            bc[j] = nx;
        }
        j = j + 1;
    }
}

/// Stage D: finish each candidate's walk (comparing the bytes) and append the items of the rows found.
fn stage_emit(s: &NumScan, n: usize, bi: &Vec<usize>, bp: &Vec<usize>, bh: &Vec<u64>, bc: &Vec<usize>,
    ip: &mut Vec<u8>, ig: &mut Vec<usize>, iv: &mut Vec<i128>, len0: usize, cap: usize,
    Ghost(c): Ghost<Ctx>, Ghost(prev): Ghost<Seq<int>>, Ghost(t0): Ghost<Seq<int>>) -> (len: usize)
    requires
        scan_ok(*s, c), bi@.len() == BLK, bp@.len() == BLK, bh@.len() == BLK, bc@.len() == BLK, n <= BLK,
        block_ok(c, s.pbits, (*s.kgs)@, bi@, bp@, bh@, n as int, t0),
        walks_ok(c, s.pbits, (*s.kgs)@, bi@, bp@, bh@, bc@, n as int),
        old(ip)@.len() >= cap, old(ig)@.len() >= cap, old(iv)@.len() >= cap,
        len0 + n <= cap,
        items_ok(NumOut { ip: *old(ip), ig: *old(ig), iv: *old(iv), len: len0 }, c, s.pbits, (*s.kgs)@, prev),
    ensures
        final(ip)@.len() == old(ip)@.len(), final(ig)@.len() == old(ig)@.len(), final(iv)@.len() == old(iv)@.len(),
        len <= len0 + n,
        items_ok(NumOut { ip: *final(ip), ig: *final(ig), iv: *final(iv), len }, c, s.pbits, (*s.kgs)@, prev + t0),
    no_unwind
{
    let ghost kv = (*s.kgs)@;
    let ghost f = itemp(c, s.pbits, kv);
    let ghost l0 = crow(bi@, n as int);
    let kgs: &Vec<KgPart> = &*s.kgs;
    proof {
        lemma_scan_facts(*s, c);
        assert(l0.subrange(0, 0) =~= Seq::<int>::empty());
        assert(prev + Seq::<int>::empty() =~= prev);
    }
    let mut len: usize = len0;
    let mut j: usize = 0;
    while j < n
        invariant
            scan_ok(*s, c), kv == (*s.kgs)@, kv == kgs@, f == itemp(c, s.pbits, kv), l0 == crow(bi@, n as int),
            bi@.len() == BLK, bp@.len() == BLK, bh@.len() == BLK, bc@.len() == BLK, j <= n, n <= BLK,
            block_ok(c, s.pbits, kv, bi@, bp@, bh@, n as int, t0),
            walks_ok(c, s.pbits, kv, bi@, bp@, bh@, bc@, n as int),
            ip@.len() >= cap, ig@.len() >= cap, iv@.len() >= cap, ip@.len() == old(ip)@.len(), ig@.len() == old(ig)@.len(),
            iv@.len() == old(iv)@.len(),
            len0 + n <= cap, len <= len0 + j,
            items_ok(NumOut { ip: *ip, ig: *ig, iv: *iv, len }, c, s.pbits, kv, prev + l0.subrange(0, j as int).filter(f)),
        decreases n - j,
    {
        proof {
            lemma_scan_facts(*s, c);
        }
        let r = bi[j];
        let p = bp[j];
        let h = bh[j];
        let cur = bc[j];
        let ghost ri = r as int;
        proof {
            assert(cand_ok(c, s.pbits, ri, p as int, h));
            assert(walk_at(kv, c, ri, p as int, h, cur));
            assert(kg_wf(kv[p as int], c, s.pbits, p as int, plist(c, s.pbits, p as int, 0, c.q)));
            assert(l0.subrange(0, j + 1) =~= l0.subrange(0, j as int).push(ri));
            lemma_filter_push(l0.subrange(0, j as int), ri, f);
            lemma_pow2u(s.pbits);
        }
        let a = text_of(&s.adsh, r, Ghost(c.n));
        let al = text_len(&s.adsh, r, Ghost(c.n));
        let tb = text_of(&s.tag, r, Ghost(c.n));
        let tl = text_len(&s.tag, r, Ghost(c.n));
        let vb = text_of(&s.ver, r, Ghost(c.n));
        let vl = text_len(&s.ver, r, Ghost(c.n));
        let g = kg_find_from(&kgs[p], cur, a, al, tb, tl, vb, vl, h, &s.padsh, &s.ptag, &s.pver, Ghost(c), Ghost(s.pbits),
            Ghost(p as int), Ghost(plist(c, s.pbits, p as int, 0, c.q)));
        let ghost before = prev + l0.subrange(0, j as int).filter(f);
        if g != NONE {
            proof {
                lemma_item_found(c, s.pbits, kv, ri, p as int, h, g as int);
            }
            ip[len] = p as u8;
            ig[len] = g;
            iv[len] = s.value[r];
            proof {
                assert(prev + l0.subrange(0, j + 1).filter(f) =~= before.push(ri));
            }
            len = len + 1;
        } else {
            proof {
                lemma_no_item(c, s.pbits, kv, ri, p as int, h);
            }
        }
        j = j + 1;
    }
    proof {
        assert(l0.subrange(0, n as int) =~= l0);
    }
    len
}

impl WorkerTask for NumTask {
    type Output = NumOut;

    open spec fn pre(&self) -> bool {
        &&& scan_ok(self.s, self.ctx@)
        &&& self.lo <= self.hi
        &&& self.hi as int <= self.ctx@.n
        &&& self.ip@.len() >= self.hi - self.lo
        &&& self.ig@.len() >= self.hi - self.lo
        &&& self.iv@.len() >= self.hi - self.lo
        &&& self.bi@.len() == BLK
        &&& self.bp@.len() == BLK
        &&& self.bh@.len() == BLK
        &&& self.bc@.len() == BLK
    }

    open spec fn post(&self, out: NumOut) -> bool {
        num_out_ok(out, self.ctx@, self.s.pbits, (*self.s.kgs)@, self.lo as int, self.hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: NumOut) {
        let ghost c = self.ctx@;
        let NumTask { lo, hi, s, mut ip, mut ig, mut iv, mut bi, mut bp, mut bh, mut bc, ctx } = self;
        let ghost kv = (*s.kgs)@;
        let cap = hi - lo;
        let mut len: usize = 0;
        let mut i: usize = lo;
        proof {
            assert(ilist(c, s.pbits, kv, lo as int, lo as int) =~= Seq::<int>::empty());
        }
        while i < hi
            invariant
                scan_ok(s, c), kv == (*s.kgs)@, lo <= i <= hi, hi as int <= c.n, cap == hi - lo,
                ip@.len() >= cap, ig@.len() >= cap, iv@.len() >= cap,
                bi@.len() == BLK, bp@.len() == BLK, bh@.len() == BLK, bc@.len() == BLK,
                len <= i - lo,
                items_ok(NumOut { ip, ig, iv, len }, c, s.pbits, kv, ilist(c, s.pbits, kv, lo as int, i as int)),
            decreases hi - i,
        {
            let e = if hi - i > BLK { i + BLK } else { hi };
            let ghost t0 = ilist(c, s.pbits, kv, i as int, e as int);
            let nc = stage_rows(&s, i, e, &mut bi, &mut bp, &mut bh, Ghost(c));
            let nf = stage_filter(&s, nc, &mut bi, &mut bp, &mut bh, Ghost(c), Ghost(t0));
            let nh = stage_head(&s, nf, &mut bi, &mut bp, &mut bh, &mut bc, Ghost(c), Ghost(t0));
            stage_step(&s, nh, &bi, &bp, &bh, &mut bc, true, Ghost(c), Ghost(t0));
            stage_step(&s, nh, &bi, &bp, &bh, &mut bc, false, Ghost(c), Ghost(t0));
            len = stage_emit(&s, nh, &bi, &bp, &bh, &bc, &mut ip, &mut ig, &mut iv, len, cap, Ghost(c),
                Ghost(ilist(c, s.pbits, kv, lo as int, i as int)), Ghost(t0));
            proof {
                lemma_ilist_append(c, s.pbits, kv, lo as int, i as int, e as int);
            }
            i = e;
        }
        NumOut { ip, ig, iv, len }
    }
}

/// At most one item per row.
pub proof fn lemma_ilist_len(c: Ctx, pbits: u64, kgs: Seq<KgPart>, lo: int, hi: int)
    requires lo <= hi,
    ensures ilist(c, pbits, kgs, lo, hi).len() <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_ilist_len(c, pbits, kgs, lo, hi - 1);
    }
}

} // verus!
