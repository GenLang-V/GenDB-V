//! P3 (cont.): the group of every pre entry and the pair `(group, cik)` of every entry, as dense ids
//! (`groups_ok`): two entries have the same group id exactly when their sub rows have the same `sic` and their tag
//! rows the same `tlabel` (NULLs equal: GROUP BY), and the same pair id exactly when moreover their sub rows have
//! the same `cik` (COUNT(DISTINCT cik)). Ids are assigned in entry order with growable hash tables; each group
//! keeps a representative `(sub row, tag row)` for its output row.
//!
//! Labels are compared once per distinct tag row: `Labels` gives every tag row met a label id (`labels_ok`: the
//! representative tag rows of the ids have pairwise different `tlabel` values; `lidc[k]` caches the id of tag row
//! `k`), so the group of an entry is found by the integers `(sic, label id)`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::agent::common::hash::*;
use crate::agent::common::chains::{NONE, bucket_of, enc};
use crate::agent::common::grow::*;
use crate::agent::common::text::*;
use crate::agent::cols::*;
use crate::agent::nf::*;
use crate::agent::ents::*;

verus! {

/// The group key of sub row `j` and tag row `k`: `(sic, tlabel)`.
pub open spec fn gkey(c: Ctx, j: int, k: int) -> (int, Val) {
    (s_sic(c, j), t_label(c, k))
}

/// The hash of a `tlabel` value.
pub open spec fn label_hash(v: Val) -> u64 {
    match v {
        Val::Text(b) => text_hash_spec(3, b),
        _ => 77,
    }
}

/// The hash of a group key `(sic, label id)`.
pub open spec fn gid_hash(sic: i32, lid: usize) -> u64 {
    mix_spec(mix_spec(9, lid as u64), sic as u64)
}

/// The hash of a pair `(group, cik)`.
pub open spec fn pair_key_hash(g: usize, cik: i32) -> u64 {
    mix_spec(mix_spec(5, g as u64), cik as u64)
}

pub struct Groups {
    /// The group id of every entry.
    pub gid: Vec<usize>,
    /// The representative `(sub row, tag row)` of every group.
    pub reps: Vec<(usize, usize)>,
    /// The pair id of every entry.
    pub pid: Vec<usize>,
    /// `(group, cik)` of every pair.
    pub preps: Vec<(usize, i32)>,
}

pub open spec fn groups_ok(c: Ctx, ents: Seq<(usize, usize, usize)>, g: &Groups) -> bool {
    ids_ok(c, ents, g.gid@, g.reps@, g.pid@, g.preps@)
}

pub open spec fn ids_ok(c: Ctx, ents: Seq<(usize, usize, usize)>, gid: Seq<usize>, reps: Seq<(usize, usize)>,
    pid: Seq<usize>, preps: Seq<(usize, i32)>) -> bool
{
    &&& gid.len() == ents.len() && pid.len() == ents.len()
    &&& reps.len() <= ents.len() && preps.len() <= ents.len()
    &&& reps_ok(c, reps)
    &&& forall|e: int| 0 <= e < ents.len() ==> (#[trigger] gid[e] as int) < reps.len()
        && gkey(c, reps[gid[e] as int].0 as int, reps[gid[e] as int].1 as int) == gkey(c, ents[e].1 as int, ents[e].2 as int)
    &&& preps_ok(preps)
    &&& forall|e: int| 0 <= e < ents.len() ==> (#[trigger] pid[e] as int) < preps.len()
        && preps[pid[e] as int] == (gid[e], s_cik_s(c)[ents[e].1 as int])
}

/// Representatives are rows, with distinct keys.
pub open spec fn reps_ok(c: Ctx, reps: Seq<(usize, usize)>) -> bool {
    &&& forall|r: int| 0 <= r < reps.len() ==> (#[trigger] reps[r]).0 < c.m && reps[r].1 < c.nt
    &&& forall|r1: int, r2: int| 0 <= r1 < reps.len() && 0 <= r2 < reps.len() && r1 != r2 ==>
        gkey(c, (#[trigger] reps[r1]).0 as int, reps[r1].1 as int) != gkey(c, (#[trigger] reps[r2]).0 as int, reps[r2].1 as int)
}

/// Pairs are distinct.
pub open spec fn preps_ok(preps: Seq<(usize, i32)>) -> bool {
    forall|p1: int, p2: int| 0 <= p1 < preps.len() && 0 <= p2 < preps.len() && p1 != p2 ==> #[trigger] preps[p1] != #[trigger] preps[p2]
}

/// The columns group keys are read from.
pub struct KeyCols {
    pub s_sic: &'static [i32],
    pub s_cik: &'static [i32],
    pub t_label: TextCol,
    pub t_labelv: &'static [u8],
}

pub open spec fn key_cols_ok(kc: &KeyCols, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& kc.s_sic@ == s_sic_s(c) && kc.s_cik@ == s_cik_s(c) && kc.t_label@ == t_label_v(c) && kc.t_labelv@ == t_labelv_s(c)
    &&& kc.s_sic@.len() == c.m && kc.s_cik@.len() == c.m && text_wf(kc.t_label@, c.nt) && kc.t_labelv@.len() == c.nt
}

fn label_hash_of(kc: &KeyCols, k: usize, Ghost(c): Ghost<Ctx>) -> (h: u64)
    requires key_cols_ok(kc, c), (k as int) < c.nt,
    ensures h == label_hash(t_label(c, k as int)),
{
    if kc.t_labelv[k] == 0 {
        77
    } else {
        let (b, bl) = text_val(&kc.t_label, k, Ghost(c.nt));
        text_hash(3, b, bl)
    }
}

/// `tlabel` of tag rows `k1` and `k2` are the same value (both NULL, or the same text).
fn label_eq(kc: &KeyCols, k1: usize, k2: usize, Ghost(c): Ghost<Ctx>) -> (r: bool)
    requires key_cols_ok(kc, c), (k1 as int) < c.nt, (k2 as int) < c.nt,
    ensures r == (t_label(c, k1 as int) == t_label(c, k2 as int)),
{
    if k1 == k2 {
        return true;
    }
    let v1 = kc.t_labelv[k1] != 0;
    let v2 = kc.t_labelv[k2] != 0;
    if v1 != v2 {
        return false;
    }
    if !v1 {
        return true;
    }
    let (b1, l1) = text_val(&kc.t_label, k1, Ghost(c.nt));
    let (b2, l2) = text_val(&kc.t_label, k2, Ghost(c.nt));
    bytes_eq(b1, l1, b2, l2)
}

/// Label ids (see the module header).
pub struct Labels {
    pub lt: Grow,
    pub lreps: Vec<usize>,
    pub lidc: Vec<usize>,
}

/// The representative tag rows have pairwise different labels.
pub open spec fn labels_distinct(c: Ctx, lreps: Seq<usize>) -> bool {
    forall|x1: int, x2: int| 0 <= x1 < lreps.len() && 0 <= x2 < lreps.len() && x1 != x2 ==>
        t_label(c, #[trigger] lreps[x1] as int) != t_label(c, #[trigger] lreps[x2] as int)
}

pub open spec fn labels_ok(c: Ctx, lb: &Labels) -> bool {
    let lr = lb.lreps@;
    &&& grow_wf(&lb.lt) && lb.lt.hashes@.len() == lr.len()
    &&& lb.lidc@.len() == c.nt
    &&& forall|x: int| 0 <= x < lr.len() ==> (#[trigger] lr[x] as int) < c.nt
        && lb.lt.hashes@[x] == label_hash(t_label(c, lr[x] as int))
    &&& labels_distinct(c, lr)
    &&& forall|k: int| 0 <= k < c.nt && #[trigger] lb.lidc@[k] != 0 ==> (lb.lidc@[k] as int) - 1 < lr.len()
        && t_label(c, lr[lb.lidc@[k] - 1] as int) == t_label(c, k)
}

/// The id of a label with representative row `x` among the labels.
proof fn lemma_label_ids(c: Ctx, lreps: Seq<usize>, x1: int, x2: int, k1: int, k2: int)
    requires
        labels_distinct(c, lreps), 0 <= x1 < lreps.len(), 0 <= x2 < lreps.len(),
        t_label(c, lreps[x1] as int) == t_label(c, k1), t_label(c, lreps[x2] as int) == t_label(c, k2),
    ensures (t_label(c, k1) == t_label(c, k2)) == (x1 == x2),
{
}

/// No label ids yet, for tag rows of `nt` rows.
fn labels_new(nt: usize, n: usize, Ghost(c): Ghost<Ctx>) -> (lb: Labels)
    requires nt as int == c.nt,
    ensures labels_ok(c, &lb), lb.lreps@.len() == 0,
{
    let lt = grow_new(n);
    let lidc: Vec<usize> = vec![0usize; nt];
    let lb = Labels { lt, lreps: Vec::new(), lidc };
    proof {
        assert forall|k: int| 0 <= k < c.nt && #[trigger] lb.lidc@[k] != 0 implies false by {
            assert(lb.lidc@[k] == 0);
        }
    }
    lb
}

/// The label id whose label is that of tag row `k` (label hash `h`), or `NONE`.
fn find_label(lb: &Labels, kc: &KeyCols, k: usize, h: u64, Ghost(c): Ghost<Ctx>) -> (r: usize)
    requires labels_ok(c, lb), key_cols_ok(kc, c), (k as int) < c.nt, h == label_hash(t_label(c, k as int)),
    ensures
        r != NONE ==> (r as int) < lb.lreps@.len() && t_label(c, lb.lreps@[r as int] as int) == t_label(c, k as int),
        r == NONE ==> forall|y: int| 0 <= y < lb.lreps@.len() ==> t_label(c, #[trigger] lb.lreps@[y] as int) != t_label(c, k as int),
{
    let ghost hs = lb.lt.hashes@;
    let ghost lr = lb.lreps@;
    let ghost bk = bucket_of(h, lb.lt.shift);
    let mut r = grow_start(&lb.lt, h);
    let ghost mut pos: int = hs.len() as int;
    while r != NONE
        invariant
            labels_ok(c, lb), key_cols_ok(kc, c), (k as int) < c.nt, hs == lb.lt.hashes@, lr == lb.lreps@,
            h == label_hash(t_label(c, k as int)), bk == bucket_of(h, lb.lt.shift),
            0 <= pos <= hs.len(), r == enc(last_of(hs, lb.lt.shift, bk, pos)),
            forall|y: int| pos <= y < lr.len() ==> t_label(c, #[trigger] lr[y] as int) != t_label(c, k as int),
        decreases pos,
    {
        proof {
            lemma_last_of(hs, lb.lt.shift, bk, pos);
        }
        let rk = lb.lreps[r];
        if lb.lt.hashes[r] == h && label_eq(kc, rk, k, Ghost(c)) {
            return r;
        }
        let ghost r0 = r as int;
        r = grow_next(&lb.lt, r);
        proof {
            assert forall|y: int| r0 <= y < lr.len() implies t_label(c, #[trigger] lr[y] as int) != t_label(c, k as int) by {
                if r0 < y < pos && t_label(c, lr[y] as int) == t_label(c, k as int) {
                    assert(bucket_of(hs[y], lb.lt.shift) != bk);
                }
            }
            pos = r0;
        }
    }
    proof {
        lemma_last_of(hs, lb.lt.shift, bk, pos);
        assert forall|y: int| 0 <= y < lr.len() implies t_label(c, #[trigger] lr[y] as int) != t_label(c, k as int) by {
            if y < pos && t_label(c, lr[y] as int) == t_label(c, k as int) {
                assert(bucket_of(hs[y], lb.lt.shift) != bk);
            }
        }
    }
    NONE
}

/// The label id of tag row `k` (assigning a new one to a new label); old ids keep their representatives.
fn label_id(lb: &mut Labels, kc: &KeyCols, k: usize, Ghost(c): Ghost<Ctx>) -> (x: usize)
    requires labels_ok(c, old(lb)), key_cols_ok(kc, c), (k as int) < c.nt, old(lb).lreps@.len() + 1 < NONE,
    ensures
        labels_ok(c, final(lb)), (x as int) < final(lb).lreps@.len(),
        t_label(c, final(lb).lreps@[x as int] as int) == t_label(c, k as int),
        old(lb).lreps@.len() <= final(lb).lreps@.len() <= old(lb).lreps@.len() + 1,
        forall|y: int| 0 <= y < old(lb).lreps@.len() ==> #[trigger] final(lb).lreps@[y] == old(lb).lreps@[y],
{
    let cached = lb.lidc[k];
    if cached != 0 {
        return cached - 1;
    }
    let h = label_hash_of(kc, k, Ghost(c));
    let found = find_label(lb, kc, k, h, Ghost(c));
    let ghost lr0 = lb.lreps@;
    let ghost lidc0 = lb.lidc@;
    let x = if found != NONE {
        found
    } else {
        let nx = lb.lreps.len();
        grow_insert(&mut lb.lt, h);
        lb.lreps.push(k);
        proof {
            let lr1 = lb.lreps@;
            assert(labels_distinct(c, lr1)) by {
                assert forall|x1: int, x2: int| 0 <= x1 < lr1.len() && 0 <= x2 < lr1.len() && x1 != x2 implies
                    t_label(c, #[trigger] lr1[x1] as int) != t_label(c, #[trigger] lr1[x2] as int) by {
                    if x1 < lr0.len() && x2 < lr0.len() {
                        assert(lr1[x1] == lr0[x1] && lr1[x2] == lr0[x2]);
                    } else if x1 < lr0.len() {
                        assert(lr1[x1] == lr0[x1]);
                    } else {
                        assert(lr1[x2] == lr0[x2]);
                    }
                }
            }
            assert forall|y: int| 0 <= y < lr1.len() implies (#[trigger] lr1[y] as int) < c.nt
                && lb.lt.hashes@[y] == label_hash(t_label(c, lr1[y] as int)) by {
                if y < lr0.len() {
                    assert(lr1[y] == lr0[y]);
                }
            }
        }
        nx
    };
    lb.lidc[k] = x + 1;
    proof {
        let lr1 = lb.lreps@;
        assert forall|k2: int| 0 <= k2 < c.nt && #[trigger] lb.lidc@[k2] != 0 implies (lb.lidc@[k2] as int) - 1 < lr1.len()
            && t_label(c, lr1[lb.lidc@[k2] - 1] as int) == t_label(c, k2) by {
            if k2 != k as int {
                assert(lb.lidc@[k2] == lidc0[k2]);
                assert(lr1[lidc0[k2] - 1] == lr0[lidc0[k2] - 1]);
            }
        }
    }
    x
}

/// Group facts: `glid[r]` is the label id of representative `r`, and `gt` indexes `(sic, label id)`.
pub open spec fn gfacts(c: Ctx, gt: &Grow, reps: Seq<(usize, usize)>, glid: Seq<usize>, gsic: Seq<i32>, lreps: Seq<usize>) -> bool {
    &&& gt.hashes@.len() == reps.len() && glid.len() == reps.len() && gsic.len() == reps.len()
    &&& forall|r: int| 0 <= r < reps.len() ==> (#[trigger] glid[r] as int) < lreps.len()
        && t_label(c, lreps[glid[r] as int] as int) == t_label(c, reps[r].1 as int)
        && gsic[r] == s_sic_s(c)[reps[r].0 as int]
        && gt.hashes@[r] == gid_hash(gsic[r], glid[r])
}

/// The group of key `(sic(j), tlabel(k))` among `reps`, by `(sic, lid)` with `lid` the label id of `k`, or `NONE`.
fn find_group(gt: &Grow, reps: &Vec<(usize, usize)>, glid: &Vec<usize>, gsic: &Vec<i32>, kc: &KeyCols, j: usize, k: usize,
    lid: usize, Ghost(c): Ghost<Ctx>, Ghost(lreps): Ghost<Seq<usize>>) -> (r: usize)
    requires
        key_cols_ok(kc, c), grow_wf(gt), (j as int) < c.m, (k as int) < c.nt, reps_ok(c, reps@),
        gfacts(c, gt, reps@, glid@, gsic@, lreps), labels_distinct(c, lreps),
        (lid as int) < lreps.len(), t_label(c, lreps[lid as int] as int) == t_label(c, k as int),
    ensures
        r != NONE ==> (r as int) < reps@.len() && gkey(c, reps@[r as int].0 as int, reps@[r as int].1 as int) == gkey(c, j as int, k as int),
        r == NONE ==> forall|r2: int| 0 <= r2 < reps@.len() ==> gkey(c, (#[trigger] reps@[r2]).0 as int, reps@[r2].1 as int) != gkey(c, j as int, k as int),
{
    let sic = kc.s_sic[j];
    let h = mix(mix(9, lid as u64), sic as u64);
    let mut r = grow_start(gt, h);
    let ghost mut pos: int = gt.hashes@.len() as int;
    let ghost bk = bucket_of(h, gt.shift);
    while r != NONE
        invariant
            key_cols_ok(kc, c), grow_wf(gt), (j as int) < c.m, (k as int) < c.nt, reps_ok(c, reps@),
            gfacts(c, gt, reps@, glid@, gsic@, lreps), labels_distinct(c, lreps), sic == kc.s_sic@[j as int],
            (lid as int) < lreps.len(), t_label(c, lreps[lid as int] as int) == t_label(c, k as int),
            h == gid_hash(sic, lid), bk == bucket_of(h, gt.shift),
            0 <= pos <= reps@.len(), r == enc(last_of(gt.hashes@, gt.shift, bk, pos)),
            forall|r2: int| pos <= r2 < reps@.len() ==> gkey(c, (#[trigger] reps@[r2]).0 as int, reps@[r2].1 as int) != gkey(c, j as int, k as int),
        decreases pos,
    {
        proof {
            lemma_last_of(gt.hashes@, gt.shift, bk, pos);
        }
        let same = gt.hashes[r] == h && gsic[r] == sic && glid[r] == lid;
        if same {
            proof {
                assert(t_label(c, reps@[r as int].1 as int) == t_label(c, lreps[lid as int] as int));
            }
            return r;
        }
        let ghost r0 = r as int;
        r = grow_next(gt, r);
        proof {
            assert forall|r2: int| r0 <= r2 < reps@.len() implies gkey(c, (#[trigger] reps@[r2]).0 as int, reps@[r2].1 as int) != gkey(c, j as int, k as int) by {
                if gkey(c, reps@[r2].0 as int, reps@[r2].1 as int) == gkey(c, j as int, k as int) {
                    lemma_label_ids(c, lreps, glid@[r2] as int, lid as int, reps@[r2].1 as int, k as int);
                    assert(s_sic_s(c)[reps@[r2].0 as int] == sic);
                    if r2 == r0 {
                        assert(gsic@[r2] == sic);
                    } else if r2 < pos {
                        assert(gt.hashes@[r2] == h);
                        assert(bucket_of(gt.hashes@[r2], gt.shift) != bk);
                    }
                }
            }
            pos = r0;
        }
    }
    proof {
        lemma_last_of(gt.hashes@, gt.shift, bk, pos);
        assert forall|r2: int| 0 <= r2 < reps@.len() implies gkey(c, (#[trigger] reps@[r2]).0 as int, reps@[r2].1 as int) != gkey(c, j as int, k as int) by {
            if r2 < pos && gkey(c, reps@[r2].0 as int, reps@[r2].1 as int) == gkey(c, j as int, k as int) {
                lemma_label_ids(c, lreps, glid@[r2] as int, lid as int, reps@[r2].1 as int, k as int);
                assert(s_sic_s(c)[reps@[r2].0 as int] == sic);
                assert(gt.hashes@[r2] == h);
                assert(bucket_of(gt.hashes@[r2], gt.shift) != bk);
            }
        }
    }
    NONE
}

/// The pair `(g, cik)` among `preps` (hash `h`), or `NONE`.
fn find_pair(pt: &Grow, preps: &Vec<(usize, i32)>, g: usize, cik: i32, h: u64) -> (r: usize)
    requires
        grow_wf(pt), pt.hashes@.len() == preps@.len(),
        forall|p: int| 0 <= p < preps@.len() ==> #[trigger] pt.hashes@[p] == pair_key_hash(preps@[p].0, preps@[p].1),
        h == pair_key_hash(g, cik),
    ensures
        r != NONE ==> (r as int) < preps@.len() && preps@[r as int] == (g, cik),
        r == NONE ==> forall|p: int| 0 <= p < preps@.len() ==> #[trigger] preps@[p] != (g, cik),
{
    let mut r = grow_start(pt, h);
    let ghost mut pos: int = pt.hashes@.len() as int;
    let ghost bk = bucket_of(h, pt.shift);
    while r != NONE
        invariant
            grow_wf(pt), pt.hashes@.len() == preps@.len(),
            forall|p: int| 0 <= p < preps@.len() ==> #[trigger] pt.hashes@[p] == pair_key_hash(preps@[p].0, preps@[p].1),
            h == pair_key_hash(g, cik), bk == bucket_of(h, pt.shift),
            0 <= pos <= preps@.len(), r == enc(last_of(pt.hashes@, pt.shift, bk, pos)),
            forall|p: int| pos <= p < preps@.len() ==> #[trigger] preps@[p] != (g, cik),
        decreases pos,
    {
        proof {
            lemma_last_of(pt.hashes@, pt.shift, bk, pos);
        }
        let (pg, pc) = preps[r];
        if pg == g && pc == cik {
            return r;
        }
        let ghost r0 = r as int;
        r = grow_next(pt, r);
        proof {
            assert forall|p: int| r0 <= p < preps@.len() implies #[trigger] preps@[p] != (g, cik) by {
                if r0 < p < pos {
                    assert(bucket_of(pt.hashes@[p], pt.shift) != bk);
                }
            }
            pos = r0;
        }
    }
    proof {
        lemma_last_of(pt.hashes@, pt.shift, bk, pos);
        assert forall|p: int| 0 <= p < preps@.len() implies #[trigger] preps@[p] != (g, cik) by {
            if p < pos {
                assert(bucket_of(pt.hashes@[p], pt.shift) != bk);
            }
        }
    }
    NONE
}

/// Group and pair ids of the entries.
pub fn build_groups(kc: &KeyCols, ents: &Vec<(usize, usize, usize)>, nt: usize, Ghost(c): Ghost<Ctx>) -> (g: Groups)
    requires key_cols_ok(kc, c), ents_ok(c, ents@), ents@.len() < NONE, nt as int == c.nt,
    ensures groups_ok(c, ents@, &g),
{
    let ne = ents.len();
    let mut lb = labels_new(nt, ne / 16 + 1024, Ghost(c));
    let mut gt = grow_new(ne / 8 + 1024);
    let mut pt = grow_new(ne / 4 + 1024);
    let mut gid: Vec<usize> = Vec::with_capacity(ne);
    let mut reps: Vec<(usize, usize)> = Vec::new();
    let mut glid: Vec<usize> = Vec::new();
    let mut gsic: Vec<i32> = Vec::new();
    let mut pid: Vec<usize> = Vec::with_capacity(ne);
    let mut preps: Vec<(usize, i32)> = Vec::new();
    let mut e: usize = 0;
    proof {
        assert(ents@.subrange(0, 0) =~= Seq::<(usize, usize, usize)>::empty());
    }
    while e < ne
        invariant
            key_cols_ok(kc, c), ents_ok(c, ents@), ne == ents@.len(), ne < NONE, e <= ne,
            labels_ok(c, &lb), lb.lreps@.len() <= e,
            grow_wf(&gt), grow_wf(&pt), gfacts(c, &gt, reps@, glid@, gsic@, lb.lreps@),
            pt.hashes@.len() == preps@.len(), reps@.len() <= e, preps@.len() <= e,
            forall|p: int| 0 <= p < preps@.len() ==> #[trigger] pt.hashes@[p] == pair_key_hash(preps@[p].0, preps@[p].1),
            ids_ok(c, ents@.subrange(0, e as int), gid@, reps@, pid@, preps@),
        decreases ne - e,
    {
        let (_l, j, k) = ents[e];
        proof {
            let ss = sel_in(c, 0, c.npre);
            assert(ents@[e as int].0 as int == ss[e as int]);
            assert(sub_of(c, j as int, p_adsh(c, _l as int)));
            assert(tag_of(c, k as int, p_tag(c, _l as int), p_ver(c, _l as int)));
        }
        let ghost lr0 = lb.lreps@;
        let lid = label_id(&mut lb, kc, k, Ghost(c));
        proof {
            assert forall|r: int| 0 <= r < reps@.len() implies (#[trigger] glid@[r] as int) < lb.lreps@.len()
                && t_label(c, lb.lreps@[glid@[r] as int] as int) == t_label(c, reps@[r].1 as int)
                && gsic@[r] == s_sic_s(c)[reps@[r].0 as int]
                && gt.hashes@[r] == gid_hash(gsic@[r], glid@[r]) by {
                assert(lb.lreps@[glid@[r] as int] == lr0[glid@[r] as int]);
            }
        }
        let ghost reps0 = reps@;
        let ghost gid0 = gid@;
        let ghost glid0 = glid@;
        let ghost gsic0 = gsic@;
        let mut g = find_group(&gt, &reps, &glid, &gsic, kc, j, k, lid, Ghost(c), Ghost(lb.lreps@));
        if g == NONE {
            g = reps.len();
            let sic = kc.s_sic[j];
            let h = mix(mix(9, lid as u64), sic as u64);
            grow_insert(&mut gt, h);
            reps.push((j, k));
            glid.push(lid);
            gsic.push(sic);
            proof {
                assert(reps_ok(c, reps@)) by {
                    assert forall|r1: int, r2: int| 0 <= r1 < reps@.len() && 0 <= r2 < reps@.len() && r1 != r2 implies
                        gkey(c, (#[trigger] reps@[r1]).0 as int, reps@[r1].1 as int) != gkey(c, (#[trigger] reps@[r2]).0 as int, reps@[r2].1 as int) by {
                        if r1 < reps0.len() && r2 < reps0.len() {
                            assert(reps@[r1] == reps0[r1] && reps@[r2] == reps0[r2]);
                        } else if r1 < reps0.len() {
                            assert(reps@[r1] == reps0[r1]);
                        } else {
                            assert(reps@[r2] == reps0[r2]);
                        }
                    }
                }
                assert forall|r: int| 0 <= r < reps@.len() implies (#[trigger] glid@[r] as int) < lb.lreps@.len()
                    && t_label(c, lb.lreps@[glid@[r] as int] as int) == t_label(c, reps@[r].1 as int)
                    && gsic@[r] == s_sic_s(c)[reps@[r].0 as int]
                    && gt.hashes@[r] == gid_hash(gsic@[r], glid@[r]) by {
                    if r < reps0.len() {
                        assert(reps@[r] == reps0[r] && glid@[r] == glid0[r] && gsic@[r] == gsic0[r]);
                    }
                }
            }
        }
        gid.push(g);
        let cik = kc.s_cik[j];
        let ph = mix(mix(5, g as u64), cik as u64);
        let ghost preps0 = preps@;
        let mut p = find_pair(&pt, &preps, g, cik, ph);
        if p == NONE {
            p = preps.len();
            grow_insert(&mut pt, ph);
            preps.push((g, cik));
        }
        pid.push(p);
        proof {
            let es = ents@.subrange(0, e + 1);
            assert(es.drop_last() =~= ents@.subrange(0, e as int));
            assert forall|e2: int| 0 <= e2 < es.len() implies (#[trigger] gid@[e2] as int) < reps@.len()
                && gkey(c, reps@[gid@[e2] as int].0 as int, reps@[gid@[e2] as int].1 as int) == gkey(c, es[e2].1 as int, es[e2].2 as int) by {
                if e2 < e {
                    assert(gid@[e2] == gid0[e2]);
                    assert(es[e2] == ents@.subrange(0, e as int)[e2]);
                    assert(reps@[gid0[e2] as int] == reps0[gid0[e2] as int]);
                }
            }
            assert(preps_ok(preps@)) by {
                assert forall|p1: int, p2: int| 0 <= p1 < preps@.len() && 0 <= p2 < preps@.len() && p1 != p2 implies
                    #[trigger] preps@[p1] != #[trigger] preps@[p2] by {
                    if p1 < preps0.len() && p2 < preps0.len() {
                        assert(preps@[p1] == preps0[p1] && preps@[p2] == preps0[p2]);
                    } else if p1 < preps0.len() {
                        assert(preps@[p1] == preps0[p1]);
                    } else if p2 < preps0.len() {
                        assert(preps@[p2] == preps0[p2]);
                    }
                }
            }
            assert forall|e2: int| 0 <= e2 < es.len() implies (#[trigger] pid@[e2] as int) < preps@.len()
                && preps@[pid@[e2] as int] == (gid@[e2], s_cik_s(c)[es[e2].1 as int]) by {
                if e2 < e {
                    assert(es[e2] == ents@.subrange(0, e as int)[e2]);
                    assert(preps@[pid@[e2] as int] == preps0[pid@[e2] as int]);
                }
            }
        }
        e = e + 1;
    }
    proof {
        assert(ents@.subrange(0, ne as int) =~= ents@);
    }
    Groups { gid, reps, pid, preps }
}

} // verus!
