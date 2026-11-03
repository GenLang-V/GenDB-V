//! The groups of one partition `p`: the task merges the partition's `num` items into its join keys' accumulators
//! (`merge::merge_items`), then reads the partition's entries in row order and adds each entry with a match to
//! the group of its GROUP BY key (`ctx::gkey`), inserting the key at its first such entry.
//!
//! Layout of the group table: group `x` has representative entry `gk[x]` (its key is `gkey(gk[x])`), member
//! `gs[x]`, key hash `gh[x]` and accumulator `ga[x]`; groups are chained by the top bits of their hash. Keys are
//! distinct, and every entry with a match has its key among the groups (`grp_wf`). At the end each group's
//! accumulator stands for the statement's group accumulators `ctx::gacc` (`grp_out_ok`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::spec::value::{Row, Val};
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::common::bytes::*;
use crate::agent::common::chain::*;
use crate::agent::common::satacc::*;
use crate::agent::common::lazy::*;
use crate::agent::ctx::*;
use crate::agent::keys::*;
use crate::agent::subidx::*;
use crate::agent::prescan::*;
use crate::agent::plists::*;
use crate::agent::kg::*;
use crate::agent::numscan::*;
use crate::agent::merge::*;

verus! {

/// Accumulator `sel` of group `key` over the entries `ents`.
pub open spec fn lsum(c: Ctx, sel: int, key: Row, ents: Seq<int>) -> int
    decreases ents.len(),
{
    if ents.len() == 0 {
        0
    } else {
        lsum(c, sel, key, ents.drop_last()) + if gkey(c, ents.last()) == key { acc(c, sel, ents.last(), c.n) } else { 0 }
    }
}

pub open spec fn lacc_ok(a: Acc, c: Ctx, key: Row, ents: Seq<int>) -> bool {
    &&& acc_ok(a, lsum(c, 0, key, ents), lsum(c, 1, key, ents), lsum(c, 2, key, ents))
    &&& acc_sane(lsum(c, 0, key, ents), lsum(c, 1, key, ents), lsum(c, 2, key, ents))
}

pub struct GrpTab {
    pub ng: usize,
    pub head: Vec<usize>,
    pub shift: u64,
    pub next: Vec<usize>,
    pub gk: Vec<usize>,
    pub gs: Vec<usize>,
    pub gh: Vec<u64>,
    pub ga: Vec<Acc>,
}

pub open spec fn grp_bkt(x: GrpTab) -> spec_fn(int) -> int {
    |g: int| (x.gh@[g] >> x.shift) as int
}

/// The key of group `g`.
pub open spec fn grp_key(x: GrpTab, c: Ctx, g: int) -> Row {
    gkey(c, x.gk@[g] as int)
}

pub open spec fn grp_shape(x: GrpTab) -> bool {
    &&& 1 <= 64 - x.shift <= 30
    &&& x.head@.len() == pow2_64(64 - x.shift)
    &&& x.ng <= x.next@.len() && x.ng <= x.gk@.len() && x.ng <= x.gs@.len() && x.ng <= x.gh@.len() && x.ng <= x.ga@.len()
    &&& x.next@.len() < NONE
}

/// The group table of the entries `ents` of partition `p`.
#[verifier::opaque]
pub open spec fn grp_wf(x: GrpTab, c: Ctx, pbits: u64, p: int, ents: Seq<int>) -> bool {
    &&& grp_shape(x)
    &&& x.ng <= ents.len()
    &&& forall|g: int| 0 <= g < x.ng ==> pre_ok(c, #[trigger] x.gk@[g] as int) && epart(c, pbits, x.gk@[g] as int) == p
    &&& forall|g: int| 0 <= g < x.ng ==> acc(c, 0, #[trigger] x.gk@[g] as int, c.n) > 0
    &&& forall|g: int| 0 <= g < x.ng ==> #[trigger] x.gs@[g] as int == esub(c, x.gk@[g] as int)
    &&& forall|g: int| 0 <= g < x.ng ==> #[trigger] x.gh@[g] == egh(c, x.gk@[g] as int)
    &&& forall|g1: int, g2: int| 0 <= g1 < x.ng && 0 <= g2 < x.ng && g1 != g2 ==>
            #[trigger] grp_key(x, c, g1) != #[trigger] grp_key(x, c, g2)
    &&& forall|g: int| 0 <= g < x.ng ==> lacc_ok(#[trigger] x.ga@[g], c, grp_key(x, c, g), ents)
    &&& forall|j: int| 0 <= j < ents.len() && acc(c, 0, #[trigger] ents[j], c.n) > 0 ==>
            exists|g: int| 0 <= g < x.ng && #[trigger] grp_key(x, c, g) == gkey(c, ents[j])
    &&& chain_wf(x.head@, x.next@, all_in(), grp_bkt(x), x.ng as int)
}

// ------------------------------------------------------------------------------------------------ group sums

pub proof fn lemma_lsum_push(c: Ctx, sel: int, key: Row, ents: Seq<int>, k: int)
    ensures lsum(c, sel, key, ents.push(k)) == lsum(c, sel, key, ents) + if gkey(c, k) == key { acc(c, sel, k, c.n) } else { 0 },
{
    assert(ents.push(k).drop_last() =~= ents);
}

/// A row matching nothing contributes nothing.
pub proof fn lemma_acc_zero(c: Ctx, k: int, hi: int)
    requires acc(c, 0, k, hi) == 0,
    ensures acc(c, 1, k, hi) == 0, acc(c, 2, k, hi) == 0,
    decreases hi,
{
    if hi > 0 {
        lemma_acc_nonneg(c, 0, k, hi - 1);
        lemma_acc_zero(c, k, hi - 1);
    }
}

/// The count, sum and mass of a row are consistent.
pub proof fn lemma_acc_sane(c: Ctx, k: int, hi: int)
    ensures acc_sane(acc(c, 0, k, hi), acc(c, 1, k, hi), acc(c, 2, k, hi)),
    decreases hi,
{
    if hi > 0 {
        lemma_acc_sane(c, k, hi - 1);
    }
}

/// Without an entry of key `key` with a match, its sums are 0.
pub proof fn lemma_lsum_none(c: Ctx, sel: int, key: Row, ents: Seq<int>)
    requires
        0 <= sel <= 2,
        forall|j: int| 0 <= j < ents.len() && gkey(c, #[trigger] ents[j]) == key ==> acc(c, 0, ents[j], c.n) == 0,
    ensures lsum(c, sel, key, ents) == 0,
    decreases ents.len(),
{
    if ents.len() > 0 {
        let d = ents.drop_last();
        assert forall|j: int| 0 <= j < d.len() && gkey(c, #[trigger] d[j]) == key implies acc(c, 0, d[j], c.n) == 0 by {
            assert(d[j] == ents[j]);
        }
        lemma_lsum_none(c, sel, key, d);
        if gkey(c, ents.last()) == key {
            assert(acc(c, 0, ents[ents.len() - 1], c.n) == 0);
            lemma_acc_zero(c, ents.last(), c.n);
        }
    }
}

/// The group sums over the entries of the partition of the group's tag are `gacc`.
pub proof fn lemma_lsum_gacc(c: Ctx, sel: int, pbits: u64, p: int, key: Row, hi: int)
    requires
        key.len() == 4, key[2] is Text, tpart(key[2]->Text_0, pbits) == p, 0 <= hi,
    ensures lsum(c, sel, key, plist(c, pbits, p, 0, hi)) == gacc(c, sel, key, hi),
    decreases hi,
{
    if hi > 0 {
        lemma_lsum_gacc(c, sel, pbits, p, key, hi - 1);
        let k = hi - 1;
        if pre_ok(c, k) && epart(c, pbits, k) == p {
            lemma_lsum_push(c, sel, key, plist(c, pbits, p, 0, hi - 1), k);
        } else if pre_ok(c, k) && gkey(c, k) == key {
            assert(gkey(c, k)[2] == Val::Text(p_tag(c, k)));
        }
    }
}

// ------------------------------------------------------------------------------------------------ the table

/// Two entries have the same group key exactly when their names, tags and plabels agree.
pub proof fn lemma_gkey_eq(c: Ctx, k1: int, k2: int)
    ensures (gkey(c, k1) == gkey(c, k2)) == (s_name(c, esub(c, k1)) == s_name(c, esub(c, k2))
        && p_tag(c, k1) == p_tag(c, k2) && p_plabel_val(c, k1) == p_plabel_val(c, k2)),
{
    let a = gkey(c, k1);
    let b = gkey(c, k2);
    if a == b {
        assert(a[0] == b[0] && a[2] == b[2] && a[3] == b[3]);
    }
    if s_name(c, esub(c, k1)) == s_name(c, esub(c, k2)) && p_tag(c, k1) == p_tag(c, k2) && p_plabel_val(c, k1) == p_plabel_val(c, k2) {
        assert(a =~= b);
    }
}

/// Equal group keys have equal hashes.
pub proof fn lemma_gkey_hash(c: Ctx, k1: int, k2: int)
    requires gkey(c, k1) == gkey(c, k2),
    ensures egh(c, k1) == egh(c, k2),
{
    lemma_gkey_eq(c, k1, k2);
    if p_plabelv_s(c)[k1] != 0 {
        assert(p_plabel_val(c, k1) == Val::Text(p_plabel(c, k1)));
        if p_plabelv_s(c)[k2] == 0 {
            assert(p_plabel_val(c, k2) == Val::Null);
        }
    } else {
        if p_plabelv_s(c)[k2] != 0 {
            assert(p_plabel_val(c, k2) == Val::Text(p_plabel(c, k2)));
        }
    }
}

/// The columns the group keys read.
pub open spec fn gcols_ok(name: TextCol, tag: TextCol, plabel: TextCol, plabelv: &'static [u8], c: Ctx) -> bool {
    &&& name@ == s_name_v(c)
    &&& tag@ == p_tag_v(c)
    &&& plabel@ == p_plabel_v(c)
    &&& plabelv@ == p_plabelv_s(c)
}

/// Entries `k1` and `k2` (members `s1`, `s2`) have the same group key.
fn same_gkey(k1: usize, s1: usize, k2: usize, s2: usize, name: &TextCol, tag: &TextCol, plabel: &TextCol,
    plabelv: &'static [u8], Ghost(c): Ghost<Ctx>) -> (r: bool)
    requires
        ctx_ok(c), gcols_ok(*name, *tag, *plabel, plabelv, c),
        pre_ok(c, k1 as int), pre_ok(c, k2 as int), s1 as int == esub(c, k1 as int), s2 as int == esub(c, k2 as int),
    ensures r == (gkey(c, k1 as int) == gkey(c, k2 as int)),
    no_unwind
{
    proof {
        lemma_views_wf(c);
        lemma_sub_for(c, p_adsh(c, k1 as int));
        lemma_sub_for(c, p_adsh(c, k2 as int));
        lemma_gkey_eq(c, k1 as int, k2 as int);
    }
    let n1 = text_of(name, s1, Ghost(c.m));
    let n1l = text_len(name, s1, Ghost(c.m));
    let n2 = text_of(name, s2, Ghost(c.m));
    let n2l = text_len(name, s2, Ghost(c.m));
    if !text_same(n1, n1l, n2, n2l) {
        return false;
    }
    let t1 = text_of(tag, k1, Ghost(c.q));
    let t1l = text_len(tag, k1, Ghost(c.q));
    let t2 = text_of(tag, k2, Ghost(c.q));
    let t2l = text_len(tag, k2, Ghost(c.q));
    if !text_same(t1, t1l, t2, t2l) {
        return false;
    }
    let v1 = plabelv[k1] != 0;
    let v2 = plabelv[k2] != 0;
    if v1 != v2 {
        return false;
    }
    if !v1 {
        return true;
    }
    let l1 = text_of(plabel, k1, Ghost(c.q));
    let l1l = text_len(plabel, k1, Ghost(c.q));
    let l2 = text_of(plabel, k2, Ghost(c.q));
    let l2l = text_len(plabel, k2, Ghost(c.q));
    text_same(l1, l1l, l2, l2l)
}

/// The group of entry `k` (member `s`, group hash `h`), or `NONE` when no group has its key.
fn grp_find(x: &GrpTab, k: usize, s: usize, h: u64, name: &TextCol, tag: &TextCol, plabel: &TextCol,
    plabelv: &'static [u8], Ghost(c): Ghost<Ctx>, Ghost(pbits): Ghost<u64>, Ghost(p): Ghost<int>, Ghost(ents): Ghost<Seq<int>>) -> (r: usize)
    requires
        grp_wf(*x, c, pbits, p, ents), ctx_ok(c), gcols_ok(*name, *tag, *plabel, plabelv, c),
        pre_ok(c, k as int), s as int == esub(c, k as int), h == egh(c, k as int),
    ensures
        r != NONE ==> r < x.ng && grp_key(*x, c, r as int) == gkey(c, k as int),
        r == NONE ==> forall|g: int| 0 <= g < x.ng ==> #[trigger] grp_key(*x, c, g) != gkey(c, k as int),
    no_unwind
{
    proof {
        reveal(grp_wf);
    }
    let bb = 64 - x.shift;
    proof {
        lemma_top_bits(h, x.shift, bb);
    }
    let ghost key = gkey(c, k as int);
    let ghost inset = all_in();
    let ghost bkt = grp_bkt(*x);
    let b = (h >> x.shift) as usize;
    let ghost pr = |g: int| grp_key(*x, c, g) != key;
    let mut cur = x.head[b];
    proof {
        lemma_walk_start(x.head@, x.next@, inset, bkt, x.ng as int, b as int, pr);
    }
    while cur != NONE
        invariant
            grp_wf(*x, c, pbits, p, ents), ctx_ok(c), gcols_ok(*name, *tag, *plabel, plabelv, c),
            pre_ok(c, k as int), s as int == esub(c, k as int), h == egh(c, k as int),
            key == gkey(c, k as int), inset == all_in(), bkt == grp_bkt(*x),
            pr == (|g: int| grp_key(*x, c, g) != key),
            b as int == (h >> x.shift) as int,
            walk_ok(cur, inset, bkt, x.ng as int, b as int, pr),
        decreases if cur == NONE { 0 } else { cur + 1 },
    {
        proof {
            reveal(grp_wf);
        }
        if x.gh[cur] == h {
            let k2 = x.gk[cur];
            let s2 = x.gs[cur];
            if same_gkey(k2, s2, k, s, name, tag, plabel, plabelv, Ghost(c)) {
                return cur;
            }
        } else {
            proof {
                if grp_key(*x, c, cur as int) == key {
                    lemma_gkey_hash(c, x.gk@[cur as int] as int, k as int);
                }
            }
        }
        proof {
            lemma_walk_step(x.head@, x.next@, inset, bkt, x.ng as int, b as int, pr, cur);
        }
        cur = x.next[cur];
    }
    proof {
        lemma_walk_done(inset, bkt, x.ng as int, b as int, pr);
        assert forall|g: int| 0 <= g < x.ng implies #[trigger] grp_key(*x, c, g) != key by {
            if grp_key(*x, c, g) == key {
                assert(inset(g));
                lemma_gkey_hash(c, x.gk@[g] as int, k as int);
                assert(bkt(g) == b as int);
            }
        }
    }
    NONE
}


/// A group table with room for `cap` groups and about `2 * cap` buckets, not yet cleared: its buffers are lazily
/// zeroed (`common::lazy`), so the calling thread writes none of them; the worker starts with `grp_clear`.
pub fn grp_new(cap: usize) -> (x: GrpTab)
    requires cap < NONE,
    ensures
        grp_shape(x),
        x.next@.len() >= cap, x.gk@.len() >= cap, x.gs@.len() >= cap, x.gh@.len() >= cap, x.ga@.len() >= cap,
{
    let bits = bits_for(cap);
    proof {
        lemma_pow2_shift(bits);
    }
    let nb: usize = 1usize << bits;
    proof {
        assert(nb as int == ((1u64 << bits) as int)) by (bit_vector) requires 4 <= bits <= 27, nb == 1usize << bits;
    }
    // The heads are set to `NONE` by `grp_clear`, on the worker.
    let mut head: Vec<usize> = vec![0usize; lazy_cap(nb, 8)];
    head.truncate(nb);
    let ncap = lazy_cap(cap, 8);
    let x = GrpTab {
        ng: 0,
        head,
        shift: 64 - bits,
        next: vec![0usize; ncap],
        gk: vec![0usize; lazy_cap(cap, 8)],
        gs: vec![0usize; lazy_cap(cap, 8)],
        gh: vec![0u64; lazy_cap(cap, 8)],
        ga: vec![(0u64, 0i128, 0u128); lazy_cap(cap, 48)],
    };
    x
}

/// The empty table: no group and every bucket `NONE` (run on the worker that fills it).
pub fn grp_clear(x: &mut GrpTab)
    requires grp_shape(*old(x)),
    ensures
        forall|c: Ctx, pbits: u64, p: int| #[trigger] grp_wf(*final(x), c, pbits, p, Seq::<int>::empty()),
        final(x).next@.len() == old(x).next@.len(), final(x).gk@.len() == old(x).gk@.len(),
        final(x).gs@.len() == old(x).gs@.len(), final(x).gh@.len() == old(x).gh@.len(),
        final(x).ga@.len() == old(x).ga@.len(),
    no_unwind
{
    x.ng = 0;
    fill(&mut x.head, NONE);
    proof {
        reveal(grp_wf);
        assert forall|c: Ctx, pbits: u64, p: int| #[trigger] grp_wf(*x, c, pbits, p, Seq::<int>::empty()) by {
            lemma_empty(x.head@, x.next@, all_in(), grp_bkt(*x));
        }
    }
}

/// The table after entry `k` with accumulator `a` (count, sum and mass of `acc(.., k, n)`).
fn grp_take(x: &mut GrpTab, k: usize, s: usize, h: u64, a: Acc, name: &TextCol, tag: &TextCol, plabel: &TextCol,
    plabelv: &'static [u8], Ghost(c): Ghost<Ctx>, Ghost(pbits): Ghost<u64>, Ghost(p): Ghost<int>, Ghost(ents): Ghost<Seq<int>>)
    requires
        grp_wf(*old(x), c, pbits, p, ents), ctx_ok(c), gcols_ok(*name, *tag, *plabel, plabelv, c),
        pre_ok(c, k as int), epart(c, pbits, k as int) == p, s as int == esub(c, k as int), h == egh(c, k as int),
        acc_ok(a, acc(c, 0, k as int, c.n), acc(c, 1, k as int, c.n), acc(c, 2, k as int, c.n)),
        ents.len() < old(x).next@.len(), ents.len() < old(x).gk@.len(), ents.len() < old(x).gs@.len(),
        ents.len() < old(x).gh@.len(), ents.len() < old(x).ga@.len(),
    ensures
        grp_wf(*final(x), c, pbits, p, ents.push(k as int)),
        final(x).next@.len() == old(x).next@.len(), final(x).gk@.len() == old(x).gk@.len(),
        final(x).gs@.len() == old(x).gs@.len(), final(x).gh@.len() == old(x).gh@.len(), final(x).ga@.len() == old(x).ga@.len(),
    no_unwind
{
    let ghost x0 = *x;
    let ghost e2 = ents.push(k as int);
    let ghost kk = k as int;
    let ghost key = gkey(c, kk);
    proof {
        lemma_acc_sane(c, kk, c.n);
        lemma_acc_nonneg(c, 0, kk, c.n);
        reveal(grp_wf);
        assert forall|g: int| 0 <= g < x0.ng && grp_key(x0, c, g) != key implies
            #[trigger] lsum(c, 0, grp_key(x0, c, g), e2) == lsum(c, 0, grp_key(x0, c, g), ents)
            && lsum(c, 1, grp_key(x0, c, g), e2) == lsum(c, 1, grp_key(x0, c, g), ents)
            && lsum(c, 2, grp_key(x0, c, g), e2) == lsum(c, 2, grp_key(x0, c, g), ents) by {
            lemma_lsum_push(c, 0, grp_key(x0, c, g), ents, kk);
            lemma_lsum_push(c, 1, grp_key(x0, c, g), ents, kk);
            lemma_lsum_push(c, 2, grp_key(x0, c, g), ents, kk);
        }
        assert forall|j: int| 0 <= j < e2.len() implies #[trigger] e2[j] == if j < ents.len() { ents[j] } else { kk } by {}
    }
    if a.0 == 0 {
        proof {
            lemma_acc_zero(c, kk, c.n);
            assert forall|g: int| 0 <= g < x0.ng implies lacc_ok(#[trigger] x0.ga@[g], c, grp_key(x0, c, g), e2) by {
                lemma_lsum_push(c, 0, grp_key(x0, c, g), ents, kk);
                lemma_lsum_push(c, 1, grp_key(x0, c, g), ents, kk);
                lemma_lsum_push(c, 2, grp_key(x0, c, g), ents, kk);
            }
            assert forall|j: int| 0 <= j < e2.len() && acc(c, 0, #[trigger] e2[j], c.n) > 0 implies
                exists|g: int| 0 <= g < x0.ng && #[trigger] grp_key(x0, c, g) == gkey(c, e2[j]) by {
                assert(j < ents.len());
                assert(e2[j] == ents[j]);
            }
        }
        return;
    }
    let g = grp_find(x, k, s, h, name, tag, plabel, plabelv, Ghost(c), Ghost(pbits), Ghost(p), Ghost(ents));
    if g != NONE {
        let ga0 = x.ga[g];
        let ghost kg = grp_key(x0, c, g as int);
        let merged = acc_merge(ga0, a, Ghost(lsum(c, 0, kg, ents)), Ghost(lsum(c, 1, kg, ents)), Ghost(lsum(c, 2, kg, ents)),
            Ghost(acc(c, 0, kk, c.n)), Ghost(acc(c, 1, kk, c.n)), Ghost(acc(c, 2, kk, c.n)));
        x.ga[g] = merged;
        proof {
            lemma_lsum_push(c, 0, kg, ents, kk);
            lemma_lsum_push(c, 1, kg, ents, kk);
            lemma_lsum_push(c, 2, kg, ents, kk);
            assert(grp_key(*x, c, g as int) == kg);
            assert forall|g2: int| 0 <= g2 < x.ng implies #[trigger] grp_key(*x, c, g2) == grp_key(x0, c, g2) by {}
            assert forall|g2: int| 0 <= g2 < x.ng implies lacc_ok(#[trigger] x.ga@[g2], c, grp_key(*x, c, g2), e2) by {
                if g2 != g as int {
                    assert(grp_key(x0, c, g2) != grp_key(x0, c, g as int));
                    assert(x.ga@[g2] == x0.ga@[g2]);
                }
            }
            assert forall|j: int| 0 <= j < e2.len() && acc(c, 0, #[trigger] e2[j], c.n) > 0 implies
                exists|g2: int| 0 <= g2 < x.ng && #[trigger] grp_key(*x, c, g2) == gkey(c, e2[j]) by {
                if j < ents.len() {
                    assert(e2[j] == ents[j]);
                    let g3 = choose|g3: int| 0 <= g3 < x0.ng && #[trigger] grp_key(x0, c, g3) == gkey(c, ents[j]);
                    assert(grp_key(*x, c, g3) == grp_key(x0, c, g3));
                } else {
                    assert(grp_key(*x, c, g as int) == gkey(c, e2[j]));
                }
            }
            assert(grp_bkt(*x) == grp_bkt(x0));
        }
    } else {
        let g0 = x.ng;
        proof {
            assert forall|j: int| 0 <= j < ents.len() && gkey(c, #[trigger] ents[j]) == key implies acc(c, 0, ents[j], c.n) == 0 by {
                lemma_acc_nonneg(c, 0, ents[j], c.n);
                if acc(c, 0, ents[j], c.n) > 0 {
                    let g3 = choose|g3: int| 0 <= g3 < x0.ng && #[trigger] grp_key(x0, c, g3) == gkey(c, ents[j]);
                    assert(grp_key(x0, c, g3) != key);
                }
            }
            lemma_lsum_none(c, 0, key, ents);
            lemma_lsum_none(c, 1, key, ents);
            lemma_lsum_none(c, 2, key, ents);
            lemma_lsum_push(c, 0, key, ents, kk);
            lemma_lsum_push(c, 1, key, ents, kk);
            lemma_lsum_push(c, 2, key, ents, kk);
            lemma_top_bits(h, x.shift, (64 - x.shift) as u64);
        }
        let b = (h >> x.shift) as usize;
        x.gk[g0] = k;
        x.gs[g0] = s;
        x.gh[g0] = h;
        x.ga[g0] = a;
        let hb = x.head[b];
        x.next[g0] = hb;
        x.head[b] = g0;
        x.ng = g0 + 1;
        proof {
            let gi = g0 as int;
            assert forall|g2: int| 0 <= g2 < gi implies #[trigger] grp_bkt(*x)(g2) == grp_bkt(x0)(g2) by {
                assert(x.gh@[g2] == x0.gh@[g2]);
            }
            lemma_ext(x0.head@, x0.next@, all_in(), grp_bkt(x0), all_in(), grp_bkt(*x), x0.next@, gi);
            lemma_insert(x0.head@, x0.next@, all_in(), grp_bkt(*x), gi, b as int);
            assert forall|g2: int| 0 <= g2 < gi implies #[trigger] grp_key(*x, c, g2) == grp_key(x0, c, g2) by {
                assert(x.gk@[g2] == x0.gk@[g2]);
            }
            assert(grp_key(*x, c, gi) == key);
            assert forall|g1: int, g2: int| 0 <= g1 < x.ng && 0 <= g2 < x.ng && g1 != g2 implies
                #[trigger] grp_key(*x, c, g1) != #[trigger] grp_key(*x, c, g2) by {
                if g1 < gi && g2 < gi {
                    assert(grp_key(x0, c, g1) != grp_key(x0, c, g2));
                }
            }
            assert forall|g2: int| 0 <= g2 < x.ng implies lacc_ok(#[trigger] x.ga@[g2], c, grp_key(*x, c, g2), e2) by {
                if g2 < gi {
                    assert(x.ga@[g2] == x0.ga@[g2]);
                    assert(grp_key(x0, c, g2) != key);
                }
            }
            assert forall|j: int| 0 <= j < e2.len() && acc(c, 0, #[trigger] e2[j], c.n) > 0 implies
                exists|g2: int| 0 <= g2 < x.ng && #[trigger] grp_key(*x, c, g2) == gkey(c, e2[j]) by {
                if j < ents.len() {
                    assert(e2[j] == ents[j]);
                    let g3 = choose|g3: int| 0 <= g3 < x0.ng && #[trigger] grp_key(x0, c, g3) == gkey(c, ents[j]);
                    assert(grp_key(*x, c, g3) == grp_key(x0, c, g3));
                } else {
                    assert(grp_key(*x, c, gi) == gkey(c, e2[j]));
                }
            }
            assert forall|g2: int| 0 <= g2 < x.ng implies pre_ok(c, #[trigger] x.gk@[g2] as int) && epart(c, pbits, x.gk@[g2] as int) == p
                && acc(c, 0, x.gk@[g2] as int, c.n) > 0 && x.gs@[g2] as int == esub(c, x.gk@[g2] as int)
                && x.gh@[g2] == egh(c, x.gk@[g2] as int) by {
                if g2 < gi {
                    assert(x.gk@[g2] == x0.gk@[g2] && x.gs@[g2] == x0.gs@[g2] && x.gh@[g2] == x0.gh@[g2]);
                }
            }
        }
    }
    proof {
        reveal(grp_wf);
    }
}


/// The accumulators of the partition's join keys, after the merge.
pub open spec fn accs_ok(accs: Seq<Acc>, c: Ctx, pbits: u64, kgs: Seq<KgPart>, p: int) -> bool {
    &&& accs.len() == kgs[p].nkg
    &&& forall|g: int| 0 <= g < accs.len() ==> macc_ok(#[trigger] accs[g], c, pbits, kgs, p, g, ilist(c, pbits, kgs, 0, c.n))
}

/// The accumulator of entry `k` at position `jj` of partition `p`.
proof fn lemma_entry_acc(accs: Seq<Acc>, c: Ctx, pbits: u64, kgs: Seq<KgPart>, p: int, jj: int, k: int)
    requires
        ctx_ok(c), kgs_ok(kgs, c, pbits), 0 <= p < kgs.len(), accs_ok(accs, c, pbits, kgs, p),
        0 <= jj < plist(c, pbits, p, 0, c.q).len(), plist(c, pbits, p, 0, c.q)[jj] == k,
    ensures ({
        let g = kgs[p].kof@[jj] as int;
        &&& 0 <= g < accs.len()
        &&& acc_ok(accs[g], acc(c, 0, k, c.n), acc(c, 1, k, c.n), acc(c, 2, k, c.n))
        &&& pre_ok(c, k) && epart(c, pbits, k) == p
    }),
{
    let ents = plist(c, pbits, p, 0, c.q);
    lemma_views_wf(c);
    assert(kg_wf(kgs[p], c, pbits, p, ents));
    lemma_kg_facts(kgs[p], c, pbits, p, ents);
    let g = kgs[p].kof@[jj] as int;
    lemma_acc_msum(c, pbits, kgs, 0, p, g, k, c.n);
    lemma_acc_msum(c, pbits, kgs, 1, p, g, k, c.n);
    lemma_acc_msum(c, pbits, kgs, 2, p, g, k, c.n);
    assert(macc_ok(accs[g], c, pbits, kgs, p, g, ilist(c, pbits, kgs, 0, c.n)));
}

/// Group the entries of partition `p` (read from the pre-scan outputs) with their accumulators.
fn group_entries(x: &mut GrpTab, accs: &Vec<Acc>, pres: &Vec<PreOut>, kgp: &KgPart, p: usize, name: &TextCol, tag: &TextCol,
    plabel: &TextCol, plabelv: &'static [u8],
    Ghost(c): Ghost<Ctx>, Ghost(pbits): Ghost<u64>, Ghost(kgs): Ghost<Seq<KgPart>>, Ghost(bounds): Ghost<Seq<int>>)
    requires
        ctx_ok(c), gcols_ok(*name, *tag, *plabel, plabelv, c),
        kgs_ok(kgs, c, pbits), (p as int) < kgs.len(), *kgp == kgs[p as int],
        accs_ok(accs@, c, pbits, kgs, p as int),
        pres_ok(pres@, c, pbits, bounds),
        grp_wf(*old(x), c, pbits, p as int, Seq::empty()),
        plist(c, pbits, p as int, 0, c.q).len() <= old(x).next@.len(),
        plist(c, pbits, p as int, 0, c.q).len() <= old(x).gk@.len(),
        plist(c, pbits, p as int, 0, c.q).len() <= old(x).gs@.len(),
        plist(c, pbits, p as int, 0, c.q).len() <= old(x).gh@.len(),
        plist(c, pbits, p as int, 0, c.q).len() <= old(x).ga@.len(),
    ensures grp_wf(*final(x), c, pbits, p as int, plist(c, pbits, p as int, 0, c.q)),
    no_unwind
{
    let ghost all = plist(c, pbits, p as int, 0, c.q);
    let ghost cap = all.len();
    proof {
        lemma_pres(pres@, c, pbits, bounds);
        lemma_kg_facts(*kgp, c, pbits, p as int, all);
    }
    let nt = pres.len();
    let mut jj: usize = 0;
    let mut t: usize = 0;
    while t < nt
        invariant
            ctx_ok(c), gcols_ok(*name, *tag, *plabel, plabelv, c),
            kgs_ok(kgs, c, pbits), (p as int) < kgs.len(), *kgp == kgs[p as int], accs_ok(accs@, c, pbits, kgs, p as int),
            pres_ok(pres@, c, pbits, bounds), nt == pres@.len(), t <= nt,
            all == plist(c, pbits, p as int, 0, c.q), cap == all.len(), kgp.nent as int == cap,
            cap <= x.next@.len(), cap <= x.gk@.len(), cap <= x.gs@.len(), cap <= x.gh@.len(), cap <= x.ga@.len(),
            jj as int == plist(c, pbits, p as int, 0, bounds[t as int]).len(),
            grp_wf(*x, c, pbits, p as int, plist(c, pbits, p as int, 0, bounds[t as int])),
        decreases nt - t,
    {
        proof {
            lemma_pres(pres@, c, pbits, bounds);
            lemma_bounds_mono(bounds, nt as int, 0, t as int);
            lemma_pl_start(c, pbits, p as int, bounds, t as int);
        }
        let o = &pres[t];
        let ol = o.len;
        let mut j: usize = 0;
        while j < ol
            invariant
                ctx_ok(c), gcols_ok(*name, *tag, *plabel, plabelv, c),
                kgs_ok(kgs, c, pbits), (p as int) < kgs.len(), *kgp == kgs[p as int], accs_ok(accs@, c, pbits, kgs, p as int),
                pres_ok(pres@, c, pbits, bounds), nt == pres@.len(), t < nt,
                all == plist(c, pbits, p as int, 0, c.q), cap == all.len(), kgp.nent as int == cap,
                cap <= x.next@.len(), cap <= x.gk@.len(), cap <= x.gs@.len(), cap <= x.gh@.len(), cap <= x.ga@.len(),
                o == &pres@[t as int], ol == o.len,
                pre_out_ok(*o, c, pbits, bounds[t as int], bounds[t + 1]),
                0 <= bounds[t as int] <= bounds[t + 1],
                j <= ol,
                jj as int == pl(c, pbits, p as int, bounds, t as int, j as int).len(),
                grp_wf(*x, c, pbits, p as int, pl(c, pbits, p as int, bounds, t as int, j as int)),
            decreases ol - j,
        {
            proof {
                lemma_pres(pres@, c, pbits, bounds);
                lemma_pl_step(c, pbits, p as int, bounds, t as int, j as int);
                lemma_elist_range(c, bounds[t as int], bounds[t + 1], j as int);
            }
            if o.ep[j] as usize == p {
                let k = o.ek[j];
                let s = o.es[j];
                let h = o.egh[j];
                let ghost ents = pl(c, pbits, p as int, bounds, t as int, j as int);
                proof {
                    lemma_pl_room(c, pbits, p as int, bounds, t as int, j as int, nt as int);
                    lemma_pl_prefix(c, pbits, p as int, bounds, t as int, j as int + 1, nt as int);
                    assert(pl(c, pbits, p as int, bounds, t as int, j as int + 1)[jj as int] == k as int);
                    lemma_entry_acc(accs@, c, pbits, kgs, p as int, jj as int, k as int);
                    lemma_kg_facts(*kgp, c, pbits, p as int, all);
                }
                let g = kgp.kof[jj];
                let a = accs[g];
                grp_take(x, k, s, h, a, name, tag, plabel, plabelv, Ghost(c), Ghost(pbits), Ghost(p as int), Ghost(ents));
                jj = jj + 1;
            }
            j = j + 1;
        }
        proof {
            lemma_pl_next(c, pbits, p as int, bounds, t as int);
        }
        t = t + 1;
    }
}

pub struct GroupTask {
    pub p: usize,
    pub pbits: u64,
    pub pres: Arc<Vec<PreOut>>,
    pub pbounds: Ghost<Seq<int>>,
    pub nouts: Arc<Vec<NumOut>>,
    pub nbounds: Ghost<Seq<int>>,
    pub kgs: Arc<Vec<KgPart>>,
    pub name: TextCol,
    pub tag: TextCol,
    pub plabel: TextCol,
    pub plabelv: &'static [u8],
    pub accs: Vec<Acc>,
    pub tab: GrpTab,
    pub ctx: Ghost<Ctx>,
}

impl WorkerTask for GroupTask {
    type Output = GrpTab;

    open spec fn pre(&self) -> bool {
        let c = self.ctx@;
        let all = plist(c, self.pbits, self.p as int, 0, c.q);
        &&& ctx_ok(c)
        &&& gcols_ok(self.name, self.tag, self.plabel, self.plabelv, c)
        &&& kgs_ok((*self.kgs)@, c, self.pbits)
        &&& (self.p as int) < (*self.kgs)@.len()
        &&& pres_ok((*self.pres)@, c, self.pbits, self.pbounds@)
        &&& nouts_ok((*self.nouts)@, c, self.pbits, (*self.kgs)@, self.nbounds@)
        &&& self.accs@.len() == (*self.kgs)@[self.p as int].nkg
        &&& grp_shape(self.tab)
        &&& all.len() <= self.tab.next@.len() && all.len() <= self.tab.gk@.len() && all.len() <= self.tab.gs@.len()
        &&& all.len() <= self.tab.gh@.len() && all.len() <= self.tab.ga@.len()
    }

    open spec fn post(&self, out: GrpTab) -> bool {
        grp_wf(out, self.ctx@, self.pbits, self.p as int, plist(self.ctx@, self.pbits, self.p as int, 0, self.ctx@.q))
    }

    fn declared_rows(&self) -> (u64, u64) {
        (0, 0)
    }

    fn run(self) -> (out: GrpTab) {
        let ghost c = self.ctx@;
        let ghost pbounds = self.pbounds@;
        let ghost nbounds = self.nbounds@;
        let GroupTask { p, pbits, pres, pbounds: _, nouts, nbounds: _, kgs, name, tag, plabel, plabelv, mut accs, mut tab, ctx } = self;
        let pres: &Vec<PreOut> = &*pres;
        let nouts: &Vec<NumOut> = &*nouts;
        let kgs: &Vec<KgPart> = &*kgs;
        // The key accumulators and the table are set up here, on the worker (lazily zeroed pages, `common::lazy`).
        fill(&mut accs, (0u64, 0i128, 0u128));
        grp_clear(&mut tab);
        merge_items(&mut accs, nouts, p, Ghost(c), Ghost(pbits), Ghost(kgs@), Ghost(nbounds));
        let kgp = &kgs[p];
        group_entries(&mut tab, &accs, pres, kgp, p, &name, &tag, &plabel, plabelv, Ghost(c), Ghost(pbits), Ghost(kgs@), Ghost(pbounds));
        tab
    }
}

} // verus!
