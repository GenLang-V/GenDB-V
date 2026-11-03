//! The answer rows in ORDER BY order: `supplier_cnt DESC, p_brand, p_type, p_size`.
//!
//! The groups (`Grp`: brand entry, type entry, size slot, count) come in strictly increasing (brand, type, slot)
//! order (`lex_sorted`), which is the order of `p_brand, p_type, p_size` (sorted dictionaries, ascending sizes). A
//! stable counting sort by descending count (`order_groups`, `common::scatter` with key `maxc - count`) then gives the
//! ORDER BY order (`lemma_rows_sorted`); the result is a permutation of the groups (`perm_ok`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::scalar::compare;
use crate::spec::text::lex_cmp;
use super::common::scatter::*;
use super::tables::*;
use super::sqlq::q_keys;
use super::answer::key_bt;

verus! {

/// One answer group: brand and type dictionary indices, size slot, distinct supplier count.
#[derive(Clone, Copy)]
pub struct Grp {
    pub b: usize,
    pub t: usize,
    pub z: usize,
    pub cnt: u64,
}

/// Strict (brand, type, slot) order.
pub open spec fn grp_lt(x: Grp, y: Grp) -> bool {
    x.b < y.b || (x.b == y.b && (x.t < y.t || (x.t == y.t && x.z < y.z)))
}

pub open spec fn lex_sorted(gs: Seq<Grp>) -> bool {
    forall|a: int, b: int| 0 <= a < b < gs.len() ==> #[trigger] grp_lt(gs[a], gs[b]) && grp_lt(gs[a], gs[b])
}

/// The answer row of a group.
pub open spec fn orow(c: Cols, sizes: Seq<i64>, e: Grp) -> Row {
    key_bt(c, sizes, e.b as int, e.t as int, e.z as int) + seq![Val::Int(e.cnt as int)]
}

/// `perm` lists every group index once, by descending count, ties in increasing index.
pub open spec fn perm_ok(gs: Seq<Grp>, perm: Seq<usize>) -> bool {
    &&& perm.len() == gs.len()
    &&& forall|p: int| 0 <= p < perm.len() ==> #[trigger] perm[p] < gs.len()
    &&& forall|i: int| 0 <= i < gs.len() ==> #[trigger] perm.contains(i as usize)
    &&& forall|p: int, q: int| 0 <= p < q < perm.len() ==>
        gs[#[trigger] perm[p] as int].cnt > gs[#[trigger] perm[q] as int].cnt
        || (gs[perm[p] as int].cnt == gs[perm[q] as int].cnt && perm[p] < perm[q])
}

// ------------------------------------------------------------------------------------------------ the sort

/// With the identity values, element `w` of key `g`'s segment is an index below `n` of key `g`.
proof fn lemma_sel_elem(keys: Seq<usize>, ids: Seq<usize>, n: int, g: int, w: int)
    requires
        0 <= n <= keys.len(), n <= ids.len(),
        forall|i: int| 0 <= i < n ==> #[trigger] ids[i] == i,
        0 <= w < sel(keys, ids, n, g).len(),
    ensures sel(keys, ids, n, g)[w] < n, keys[sel(keys, ids, n, g)[w] as int] == g,
    decreases n,
{
    let s0 = sel(keys, ids, n - 1, g);
    if keys[n - 1].ix() == g {
        if w < s0.len() {
            lemma_sel_elem(keys, ids, n - 1, g, w);
        } else {
            assert(sel(keys, ids, n, g)[w] == ids[n - 1]);
        }
    } else {
        lemma_sel_elem(keys, ids, n - 1, g, w);
    }
}

/// With the identity values, a segment is strictly increasing.
proof fn lemma_sel_incr(keys: Seq<usize>, ids: Seq<usize>, n: int, g: int, a: int, b: int)
    requires
        0 <= n <= keys.len(), n <= ids.len(),
        forall|i: int| 0 <= i < n ==> #[trigger] ids[i] == i,
        0 <= a < b < sel(keys, ids, n, g).len(),
    ensures sel(keys, ids, n, g)[a] < sel(keys, ids, n, g)[b],
    decreases n,
{
    let s0 = sel(keys, ids, n - 1, g);
    if keys[n - 1].ix() == g {
        if b < s0.len() {
            lemma_sel_incr(keys, ids, n - 1, g, a, b);
        } else {
            lemma_sel_elem(keys, ids, n - 1, g, a);
            assert(sel(keys, ids, n, g)[b] == ids[n - 1]);
        }
    } else {
        lemma_sel_incr(keys, ids, n - 1, g, a, b);
    }
}

/// With the identity values, every index of key `g` lies in its segment.
proof fn lemma_sel_has_id(keys: Seq<usize>, ids: Seq<usize>, n: int, g: int, i: int) -> (w: int)
    requires
        0 <= n <= keys.len(), n <= ids.len(),
        forall|k: int| 0 <= k < n ==> #[trigger] ids[k] == k,
        0 <= i < n, keys[i].ix() == g,
    ensures 0 <= w < sel(keys, ids, n, g).len(), sel(keys, ids, n, g)[w] == i,
    decreases n,
{
    let s0 = sel(keys, ids, n - 1, g);
    if i == n - 1 {
        s0.len() as int
    } else {
        let w = lemma_sel_has_id(keys, ids, n - 1, g, i);
        if keys[n - 1].ix() == g {
            assert(sel(keys, ids, n, g)[w] == s0[w]);
        }
        w
    }
}

/// Position `p` of `ot` inside a segment `[a, b)` equal to `sg`.
proof fn lemma_pos_in_seg(ot: Seq<usize>, a: int, b: int, sg: Seq<usize>, p: int)
    requires 0 <= a <= p < b <= ot.len(), ot.subrange(a, b) == sg,
    ensures ot[p] == sg[p - a], sg.len() == b - a,
{
    assert(ot.subrange(a, b)[p - a] == ot[p]);
}

/// Monotone offsets from 0 to `n`: every position lies in a segment.
proof fn lemma_seg_of(offs: Seq<usize>, nk: int, n: int, p: int) -> (g: int)
    requires
        offs.len() == nk + 1, nk >= 0, offs[0] == 0, offs[nk] == n,
        forall|h: int| 0 <= h < nk ==> #[trigger] offs[h] <= offs[h + 1],
        0 <= p < n,
    ensures 0 <= g < nk, offs[g] <= p < offs[g + 1],
    decreases nk,
{
    if nk == 0 {
        assert(false);
        0
    } else if offs[nk - 1] <= p {
        nk - 1
    } else {
        let sub = offs.subrange(0, nk);
        assert forall|h: int| 0 <= h < nk - 1 implies #[trigger] sub[h] <= sub[h + 1] by {
            assert(offs[h] <= offs[h + 1]);
        }
        lemma_seg_of(sub, nk - 1, offs[nk - 1] as int, p)
    }
}

/// Offsets are nondecreasing over any span.
proof fn lemma_offs_mono(offs: Seq<usize>, nk: int, a: int, b: int)
    requires
        offs.len() == nk + 1,
        forall|h: int| 0 <= h < nk ==> #[trigger] offs[h] <= offs[h + 1],
        0 <= a <= b <= nk,
    ensures offs[a] <= offs[b],
    decreases b - a,
{
    if a < b {
        lemma_offs_mono(offs, nk, a, b - 1);
    }
}

/// The group indices by descending count, ties in increasing index (stable counting sort; `maxc` bounds the
/// counts).
pub fn order_groups(gs: &Vec<Grp>, maxc: u64) -> (perm: Vec<usize>)
    requires
        forall|i: int| 0 <= i < gs@.len() ==> (#[trigger] gs@[i]).cnt <= maxc,
        (maxc as int) + 2 < usize::MAX,
    ensures perm_ok(gs@, perm@),
{
    let n = gs.len();
    let mut keys: Vec<usize> = Vec::new();
    let mut ids: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == gs@.len(), i <= n,
            forall|k: int| 0 <= k < n ==> (#[trigger] gs@[k]).cnt <= maxc,
            (maxc as int) + 2 < usize::MAX,
            keys@.len() == i, ids@.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] keys@[k] == (maxc - gs@[k].cnt) as usize,
            forall|k: int| 0 <= k < i ==> #[trigger] ids@[k] == k,
        decreases n - i,
    {
        keys.push((maxc - gs[i].cnt) as usize);
        ids.push(i);
        i = i + 1;
    }
    let nk = maxc as usize + 1;
    let mut offs: Vec<usize> = vec![0usize; nk + 1];
    let mut out: Vec<usize> = vec![0usize; n];
    proof {
        assert forall|k: int| 0 <= k < n implies (#[trigger] keys@[k]).ix() < nk by {}
    }
    scatter(&keys, &ids, n, nk, &mut offs, &mut out);
    proof {
        reveal(sort_facts);
        assert(sort_facts(gs@, maxc, keys@, ids@, offs@, out@));
        lemma_perm(gs@, maxc, keys@, ids@, offs@, out@);
    }
    out
}

/// The facts of the counting sort's inputs and output (opaque: `lemma_facts_basic` and `lemma_facts_seg` read it).
#[verifier::opaque]
pub open spec fn sort_facts(gs: Seq<Grp>, maxc: u64, ks: Seq<usize>, is_: Seq<usize>, os: Seq<usize>, ot: Seq<usize>) -> bool {
    &&& ks.len() == gs.len() && is_.len() == gs.len()
    &&& (maxc as int) + 2 < usize::MAX
    &&& forall|k: int| 0 <= k < gs.len() ==> (#[trigger] gs[k]).cnt <= maxc
    &&& forall|k: int| 0 <= k < gs.len() ==> #[trigger] ks[k] == (maxc - gs[k].cnt) as usize
    &&& forall|k: int| 0 <= k < gs.len() ==> #[trigger] is_[k] == k
    &&& ot.len() == gs.len()
    &&& scattered(ks, is_, gs.len() as int, maxc + 1, os, ot)
}

/// Segment `g` of the sorted output.
proof fn lemma_facts_seg(gs: Seq<Grp>, maxc: u64, ks: Seq<usize>, is_: Seq<usize>, os: Seq<usize>, ot: Seq<usize>, g: int)
    requires sort_facts(gs, maxc, ks, is_, os, ot), 0 <= g < maxc + 1,
    ensures ot.subrange(os[g] as int, os[g + 1] as int) == sel(ks, is_, gs.len() as int, g),
{
    reveal(sort_facts);
}

/// Offsets of the sort.
proof fn lemma_facts_offs(gs: Seq<Grp>, maxc: u64, ks: Seq<usize>, is_: Seq<usize>, os: Seq<usize>, ot: Seq<usize>)
    requires sort_facts(gs, maxc, ks, is_, os, ot),
    ensures
        ks.len() == gs.len(), is_.len() == gs.len(), ot.len() == gs.len(),
        forall|k: int| 0 <= k < gs.len() ==> #[trigger] is_[k] == k,
        os.len() == maxc + 2, os[0] == 0, os[maxc + 1] == gs.len(),
        forall|h: int| 0 <= h < maxc + 1 ==> #[trigger] os[h] <= os[h + 1],
{
    reveal(sort_facts);
}

/// The key of index `k` is `maxc - count`.
proof fn lemma_facts_key(gs: Seq<Grp>, maxc: u64, ks: Seq<usize>, is_: Seq<usize>, os: Seq<usize>, ot: Seq<usize>, k: int)
    requires sort_facts(gs, maxc, ks, is_, os, ot), 0 <= k < gs.len(),
    ensures ks[k] == maxc - gs[k].cnt, gs[k].cnt <= maxc,
{
    reveal(sort_facts);
}

/// Position `p` of the output holds an index below `n` of the key of its segment `g`.
proof fn lemma_at(gs: Seq<Grp>, maxc: u64, ks: Seq<usize>, is_: Seq<usize>, os: Seq<usize>, ot: Seq<usize>, p: int)
    -> (g: int)
    requires sort_facts(gs, maxc, ks, is_, os, ot), 0 <= p < gs.len(),
    ensures
        0 <= g < maxc + 1, os[g] <= p < os[g + 1],
        ot[p] < gs.len(), ks[ot[p] as int] == g,
        ot[p] == sel(ks, is_, gs.len() as int, g)[p - os[g]],
        sel(ks, is_, gs.len() as int, g).len() == os[g + 1] - os[g],
{
    let nn = gs.len() as int;
    lemma_facts_offs(gs, maxc, ks, is_, os, ot);
    let g = lemma_seg_of(os, maxc + 1, nn, p);
    lemma_facts_seg(gs, maxc, ks, is_, os, ot, g);
    lemma_offs_mono(os, maxc + 1, g + 1, maxc + 1);
    let sg = sel(ks, is_, nn, g);
    lemma_pos_in_seg(ot, os[g] as int, os[g + 1] as int, sg, p);
    lemma_sel_elem(ks, is_, nn, g, p - os[g]);
    g
}

/// The output's positions are in descending count, ties in increasing index.
proof fn lemma_order(gs: Seq<Grp>, maxc: u64, ks: Seq<usize>, is_: Seq<usize>, os: Seq<usize>, ot: Seq<usize>,
    p: int, q: int)
    requires sort_facts(gs, maxc, ks, is_, os, ot), 0 <= p < q < gs.len(),
    ensures
        gs[ot[p] as int].cnt > gs[ot[q] as int].cnt || (gs[ot[p] as int].cnt == gs[ot[q] as int].cnt && ot[p] < ot[q]),
{
    let nn = gs.len() as int;
    lemma_facts_offs(gs, maxc, ks, is_, os, ot);
    let gp = lemma_at(gs, maxc, ks, is_, os, ot, p);
    let gq = lemma_at(gs, maxc, ks, is_, os, ot, q);
    if gp > gq {
        lemma_offs_mono(os, maxc + 1, gq + 1, gp);
    }
    if gp == gq {
        lemma_sel_incr(ks, is_, nn, gp, p - os[gp], q - os[gp]);
    }
    lemma_facts_key(gs, maxc, ks, is_, os, ot, ot[p] as int);
    lemma_facts_key(gs, maxc, ks, is_, os, ot, ot[q] as int);
}

/// Every index appears in the output.
proof fn lemma_covers(gs: Seq<Grp>, maxc: u64, ks: Seq<usize>, is_: Seq<usize>, os: Seq<usize>, ot: Seq<usize>, k: int)
    requires sort_facts(gs, maxc, ks, is_, os, ot), 0 <= k < gs.len(),
    ensures ot.contains(k as usize),
{
    let nn = gs.len() as int;
    lemma_facts_offs(gs, maxc, ks, is_, os, ot);
    lemma_facts_key(gs, maxc, ks, is_, os, ot, k);
    let g = ks[k] as int;
    lemma_facts_seg(gs, maxc, ks, is_, os, ot, g);
    let a = lemma_sel_has_id(ks, is_, nn, g, k);
    lemma_offs_mono(os, maxc + 1, g + 1, maxc + 1);
    let sg = sel(ks, is_, nn, g);
    let pos = os[g] + a;
    assert(ot.subrange(os[g] as int, os[g + 1] as int)[a] == ot[pos]);
    assert(ot[pos] == k as usize);
}

/// The counting sort's output is `perm_ok`.
proof fn lemma_perm(gs: Seq<Grp>, maxc: u64, ks: Seq<usize>, is_: Seq<usize>, os: Seq<usize>, ot: Seq<usize>)
    requires sort_facts(gs, maxc, ks, is_, os, ot),
    ensures perm_ok(gs, ot),
{
    lemma_facts_offs(gs, maxc, ks, is_, os, ot);
    assert forall|p: int| 0 <= p < ot.len() implies #[trigger] ot[p] < gs.len() by {
        lemma_at(gs, maxc, ks, is_, os, ot, p);
    }
    assert forall|k: int| 0 <= k < gs.len() implies #[trigger] ot.contains(k as usize) by {
        lemma_covers(gs, maxc, ks, is_, os, ot, k);
    }
    assert forall|p: int, q: int| 0 <= p < q < ot.len() implies
        gs[#[trigger] ot[p] as int].cnt > gs[#[trigger] ot[q] as int].cnt
        || (gs[ot[p] as int].cnt == gs[ot[q] as int].cnt && ot[p] < ot[q]) by {
        lemma_order(gs, maxc, ks, is_, os, ot, p, q);
    }
}

// ------------------------------------------------------------------------------------------------ ORDER BY

/// The ORDER BY keys on two answer rows: count descending, then brand, type and size ascending.
pub proof fn lemma_row_cmp(c: Cols, sizes: Seq<i64>, x: Grp, y: Grp)
    requires
        dict_ok(c.p.brand_o@, c.p.brand_y@), dict_ok(c.p.type_o@, c.p.type_y@),
        crate::stores::custpart::interface::common::colfmt::dict_sorted(c.p.brand_o@, c.p.brand_y@, c.p.brand_o@.len() - 1),
        crate::stores::custpart::interface::common::colfmt::dict_sorted(c.p.type_o@, c.p.type_y@, c.p.type_o@.len() - 1),
        forall|a: int, b: int| 0 <= a < b < sizes.len() ==> #[trigger] sizes[a] < #[trigger] sizes[b],
        x.b < c.p.brand_o@.len() - 1, y.b < c.p.brand_o@.len() - 1,
        x.t < c.p.type_o@.len() - 1, y.t < c.p.type_o@.len() - 1,
        x.z < sizes.len(), y.z < sizes.len(),
        x.cnt > y.cnt || (x.cnt == y.cnt && grp_lt(x, y)),
    ensures keys_cmp(q_keys(), orow(c, sizes, x), orow(c, sizes, y)) <= 0,
{
    let (r1, r2) = (orow(c, sizes, x), orow(c, sizes, y));
    let ks = q_keys();
    reveal_with_fuel(keys_cmp, 5);
    assert(r1.len() == 4 && r2.len() == 4);
    assert(r1[3] == Val::Int(x.cnt as int) && r2[3] == Val::Int(y.cnt as int));
    let (bx, by) = (txt(c.p.brand_o@, c.p.brand_y@, x.b as int), txt(c.p.brand_o@, c.p.brand_y@, y.b as int));
    let (tx, ty) = (txt(c.p.type_o@, c.p.type_y@, x.t as int), txt(c.p.type_o@, c.p.type_y@, y.t as int));
    assert(r1[0] == Val::Text(bx) && r2[0] == Val::Text(by));
    assert(r1[1] == Val::Text(tx) && r2[1] == Val::Text(ty));
    assert(r1[2] == Val::Int(sizes[x.z as int] as int) && r2[2] == Val::Int(sizes[y.z as int] as int));
    let k1 = ks.drop_first();
    let k2 = k1.drop_first();
    let k3 = k2.drop_first();
    assert(k1[0] == ks[1] && k2[0] == ks[2] && k3[0] == ks[3]);
    assert(k3.drop_first().len() == 0);
    if x.cnt > y.cnt {
        assert(key_cmp(ks[0], r1, r2) == -1);
    } else {
        assert(key_cmp(ks[0], r1, r2) == 0);
        crate::bridge::equality::lemma_lex_cmp_zero(bx, by);
        crate::bridge::equality::lemma_lex_cmp_zero(tx, ty);
        if x.b < y.b {
            crate::stores::custpart::interface::common::colfmt::lemma_dict_order(c.p.brand_o@, c.p.brand_y@,
                c.p.brand_o@.len() - 1, x.b as int, y.b as int);
            assert(lex_cmp(bx, by) < 0);
            assert(key_cmp(ks[1], r1, r2) < 0);
        } else {
            assert(x.b == y.b);
            assert(key_cmp(ks[1], r1, r2) == 0);
            if x.t < y.t {
                crate::stores::custpart::interface::common::colfmt::lemma_dict_order(c.p.type_o@, c.p.type_y@,
                    c.p.type_o@.len() - 1, x.t as int, y.t as int);
                assert(key_cmp(ks[2], r1, r2) < 0);
            } else {
                assert(x.t == y.t);
                assert(key_cmp(ks[2], r1, r2) == 0);
                assert(x.z < y.z);
                assert(sizes[x.z as int] < sizes[y.z as int]);
                assert(key_cmp(ks[3], r1, r2) < 0);
            }
        }
    }
}

} // verus!
