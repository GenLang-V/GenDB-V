//! The groups of all partitions as one list (partition by partition), with the facts the final answer needs:
//! the keys are distinct, they are exactly the keys with a matching row (`gacc(0, key) > 0`), and each
//! accumulator stands for its key's `gacc` (`flat_ok`).
//!
//! A key lies in the partition of its tag (`kpart`), so keys of different partitions differ, and a key with a
//! match has an entry with a match in its partition, whose group table then holds it (`grp_wf` coverage).
use vstd::prelude::*;
use crate::spec::value::{Row, Val};
use crate::agent::common::satacc::*;
use crate::agent::common::bytes::*;
use crate::agent::ctx::*;
use crate::agent::keys::*;
use crate::agent::groups::*;

verus! {

/// The partition of a group key (of its tag).
pub open spec fn kpart(key: Row, pbits: u64) -> int {
    tpart(key[2]->Text_0, pbits)
}

/// A tag's partition is below `2^pbits`.
pub proof fn lemma_tpart_range(t: Seq<u8>, pbits: u64)
    requires pbits <= MAX_PBITS,
    ensures 0 <= tpart(t, pbits) < pow2u(pbits),
{
    lemma_pow2u(pbits);
    if pbits > 0 {
        let h = sig_spec(t);
        let sh = (64 - pbits) as u64;
        assert(h >> sh < (1u64 << pbits)) by (bit_vector) requires 1 <= pbits <= 6, sh == 64 - pbits;
    }
}

/// The groups of all partitions, flattened.
pub struct Flat {
    pub fk: Vec<usize>,
    pub fs: Vec<usize>,
    pub fa: Vec<Acc>,
}

pub open spec fn elem_ok(f: Flat, c: Ctx, gl: Seq<Row>, i: int) -> bool {
    &&& pre_ok(c, f.fk@[i] as int)
    &&& f.fs@[i] as int == esub(c, f.fk@[i] as int)
    &&& gl[i] == gkey(c, f.fk@[i] as int)
    &&& acc_ok(f.fa@[i], gacc(c, 0, gl[i], c.q), gacc(c, 1, gl[i], c.q), gacc(c, 2, gl[i], c.q))
    &&& gacc(c, 0, gl[i], c.q) > 0
}

/// The flat list is the groups of all keys with a match, once each.
pub open spec fn flat_ok(f: Flat, c: Ctx, gl: Seq<Row>) -> bool {
    &&& f.fk@.len() == gl.len() && f.fs@.len() == gl.len() && f.fa@.len() == gl.len()
    &&& forall|i: int| 0 <= i < gl.len() ==> #[trigger] elem_ok(f, c, gl, i)
    &&& gl.no_duplicates()
    &&& forall|k: Row| #[trigger] gl.contains(k) <==> gacc(c, 0, k, c.q) > 0
}

/// The terms of `gacc` are non-negative, so one term bounds it from below.
pub proof fn lemma_gacc_term(c: Ctx, key: Row, k: int, hi: int)
    requires 0 <= k < hi, pre_ok(c, k), gkey(c, k) == key,
    ensures gacc(c, 0, key, hi) >= acc(c, 0, k, c.n),
    decreases hi,
{
    lemma_gacc_nonneg(c, 0, key, hi - 1);
    if k < hi - 1 {
        lemma_gacc_term(c, key, k, hi - 1);
        lemma_acc_nonneg(c, 0, hi - 1, c.n);
    }
}

/// A key with a match has an entry with a match.
pub proof fn lemma_gacc_witness(c: Ctx, key: Row, hi: int) -> (k: int)
    requires gacc(c, 0, key, hi) > 0,
    ensures 0 <= k < hi, pre_ok(c, k), gkey(c, k) == key, acc(c, 0, k, c.n) > 0,
    decreases hi,
{
    if gacc(c, 0, key, hi - 1) > 0 {
        lemma_gacc_witness(c, key, hi - 1)
    } else {
        lemma_gacc_nonneg(c, 0, key, hi - 1);
        hi - 1
    }
}

/// An entry of partition `p` below `hi` is in `plist(p, 0, hi)`.
pub proof fn lemma_plist_has(c: Ctx, pbits: u64, p: int, k: int, hi: int) -> (j: int)
    requires 0 <= k < hi, pre_ok(c, k), epart(c, pbits, k) == p,
    ensures 0 <= j < plist(c, pbits, p, 0, hi).len(), plist(c, pbits, p, 0, hi)[j] == k,
    decreases hi,
{
    if k == hi - 1 {
        plist(c, pbits, p, 0, hi - 1).len() as int
    } else {
        lemma_plist_has(c, pbits, p, k, hi - 1)
    }
}

/// The group facts of partition `p` (its table over all its entries) in terms of `gacc`.
pub proof fn lemma_part_groups(x: GrpTab, c: Ctx, pbits: u64, p: int)
    requires grp_wf(x, c, pbits, p, plist(c, pbits, p, 0, c.q)), ctx_ok(c),
    ensures
        part_facts(x, c, pbits, p),
        grp_shape(x),
        forall|g: int| 0 <= g < x.ng ==> pre_ok(c, #[trigger] x.gk@[g] as int) && epart(c, pbits, x.gk@[g] as int) == p
            && x.gs@[g] as int == esub(c, x.gk@[g] as int)
            && acc_ok(x.ga@[g], gacc(c, 0, grp_key(x, c, g), c.q), gacc(c, 1, grp_key(x, c, g), c.q), gacc(c, 2, grp_key(x, c, g), c.q))
            && gacc(c, 0, grp_key(x, c, g), c.q) > 0
            && kpart(grp_key(x, c, g), pbits) == p,
        forall|g1: int, g2: int| 0 <= g1 < x.ng && 0 <= g2 < x.ng && g1 != g2 ==>
            #[trigger] grp_key(x, c, g1) != #[trigger] grp_key(x, c, g2),
        forall|key: Row| #[trigger] gacc(c, 0, key, c.q) > 0 && kpart(key, pbits) == p ==>
            exists|g: int| 0 <= g < x.ng && #[trigger] grp_key(x, c, g) == key,
{
    reveal(grp_wf);
    let ents = plist(c, pbits, p, 0, c.q);
    lemma_views_wf(c);
    assert forall|g: int| 0 <= g < x.ng implies pre_ok(c, #[trigger] x.gk@[g] as int) && epart(c, pbits, x.gk@[g] as int) == p
        && x.gs@[g] as int == esub(c, x.gk@[g] as int)
        && acc_ok(x.ga@[g], gacc(c, 0, grp_key(x, c, g), c.q), gacc(c, 1, grp_key(x, c, g), c.q), gacc(c, 2, grp_key(x, c, g), c.q))
        && gacc(c, 0, grp_key(x, c, g), c.q) > 0
        && kpart(grp_key(x, c, g), pbits) == p by {
        let key = grp_key(x, c, g);
        let k = x.gk@[g] as int;
        assert(key[2] == Val::Text(p_tag(c, k)));
        lemma_lsum_gacc(c, 0, pbits, p, key, c.q);
        lemma_lsum_gacc(c, 1, pbits, p, key, c.q);
        lemma_lsum_gacc(c, 2, pbits, p, key, c.q);
        assert(lacc_ok(x.ga@[g], c, key, ents));
        lemma_gacc_term(c, key, k, c.q);
    }
    assert forall|key: Row| #[trigger] gacc(c, 0, key, c.q) > 0 && kpart(key, pbits) == p implies
        exists|g: int| 0 <= g < x.ng && #[trigger] grp_key(x, c, g) == key by {
        let k = lemma_gacc_witness(c, key, c.q);
        assert(key[2] == Val::Text(p_tag(c, k)));
        let j = lemma_plist_has(c, pbits, p, k, c.q);
        assert(acc(c, 0, ents[j], c.n) > 0);
    }
}

/// The facts of one partition's groups that flattening uses.
pub open spec fn part_facts(t: GrpTab, c: Ctx, pbits: u64, p: int) -> bool {
    &&& grp_shape(t)
    &&& forall|g: int| 0 <= g < t.ng ==> pre_ok(c, #[trigger] t.gk@[g] as int) && epart(c, pbits, t.gk@[g] as int) == p
        && t.gs@[g] as int == esub(c, t.gk@[g] as int)
        && acc_ok(t.ga@[g], gacc(c, 0, grp_key(t, c, g), c.q), gacc(c, 1, grp_key(t, c, g), c.q), gacc(c, 2, grp_key(t, c, g), c.q))
        && gacc(c, 0, grp_key(t, c, g), c.q) > 0
        && kpart(grp_key(t, c, g), pbits) == p
    &&& forall|g1: int, g2: int| 0 <= g1 < t.ng && 0 <= g2 < t.ng && g1 != g2 ==>
        #[trigger] grp_key(t, c, g1) != #[trigger] grp_key(t, c, g2)
}

/// Append the groups of partition `p` (whose facts hold) to the flat list of the partitions before it.
fn flatten_part(f: &mut Flat, t: &GrpTab, Ghost(c): Ghost<Ctx>, Ghost(pbits): Ghost<u64>, Ghost(p): Ghost<int>,
    Ghost(gl0): Ghost<Seq<Row>>) -> (gl: Ghost<Seq<Row>>)
    requires
        part_facts(*t, c, pbits, p),
        old(f).fk@.len() == gl0.len() && old(f).fs@.len() == gl0.len() && old(f).fa@.len() == gl0.len(),
        forall|i: int| 0 <= i < gl0.len() ==> #[trigger] elem_ok(*old(f), c, gl0, i),
        forall|i: int| 0 <= i < gl0.len() ==> kpart(#[trigger] gl0[i], pbits) < p,
        gl0.no_duplicates(),
    ensures
        final(f).fk@.len() == gl@.len() && final(f).fs@.len() == gl@.len() && final(f).fa@.len() == gl@.len(),
        forall|i: int| 0 <= i < gl@.len() ==> #[trigger] elem_ok(*final(f), c, gl@, i),
        forall|i: int| 0 <= i < gl@.len() ==> kpart(#[trigger] gl@[i], pbits) < p + 1,
        gl@.no_duplicates(),
        forall|key: Row| #[trigger] gl0.contains(key) ==> gl@.contains(key),
        forall|g: int| 0 <= g < t.ng ==> gl@.contains(#[trigger] grp_key(*t, c, g)),
{
    let ng = t.ng;
    let ghost mut gl = gl0;
    let mut x: usize = 0;
    while x < ng
        invariant
            part_facts(*t, c, pbits, p), ng == t.ng,
            x <= ng,
            gl.len() == gl0.len() + x,
            forall|i: int| 0 <= i < gl0.len() ==> #[trigger] gl[i] == gl0[i],
            forall|i: int| gl0.len() <= i < gl.len() ==> #[trigger] gl[i] == grp_key(*t, c, i - gl0.len()),
            f.fk@.len() == gl.len() && f.fs@.len() == gl.len() && f.fa@.len() == gl.len(),
            forall|i: int| 0 <= i < gl.len() ==> #[trigger] elem_ok(*f, c, gl, i),
            forall|i: int| 0 <= i < gl0.len() ==> kpart(#[trigger] gl0[i], pbits) < p,
            gl0.no_duplicates(),
            gl.no_duplicates(),
        decreases ng - x,
    {
        let k = t.gk[x];
        let s = t.gs[x];
        let a = t.ga[x];
        let ghost key = grp_key(*t, c, x as int);
        let ghost gl1 = gl;
        let ghost f0 = *f;
        proof {
            assert(!gl1.contains(key)) by {
                if gl1.contains(key) {
                    let i = choose|i: int| 0 <= i < gl1.len() && gl1[i] == key;
                    if i < gl0.len() {
                        assert(gl1[i] == gl0[i]);
                        assert(kpart(gl0[i], pbits) < p);
                    } else {
                        assert(gl1[i] == grp_key(*t, c, i - gl0.len()));
                    }
                }
            }
            gl = gl.push(key);
        }
        f.fk.push(k);
        f.fs.push(s);
        f.fa.push(a);
        proof {
            assert forall|i: int| 0 <= i < gl.len() implies #[trigger] elem_ok(*f, c, gl, i) by {
                if i < gl1.len() {
                    assert(elem_ok(f0, c, gl1, i));
                    assert(f.fk@[i] == f0.fk@[i] && f.fs@[i] == f0.fs@[i] && f.fa@[i] == f0.fa@[i] && gl[i] == gl1[i]);
                }
            }
            assert forall|i: int, j: int| 0 <= i < gl.len() && 0 <= j < gl.len() && i != j implies gl[i] != gl[j] by {
                if i < gl1.len() && j < gl1.len() {
                    assert(gl1[i] != gl1[j]);
                }
            }
        }
        x = x + 1;
    }
    proof {
        assert forall|i: int| 0 <= i < gl.len() implies kpart(#[trigger] gl[i], pbits) < p + 1 by {
            if i < gl0.len() {
                assert(gl[i] == gl0[i]);
            } else {
                assert(gl[i] == grp_key(*t, c, i - gl0.len()));
            }
        }
        assert forall|key: Row| #[trigger] gl0.contains(key) implies gl.contains(key) by {
            let i = choose|i: int| 0 <= i < gl0.len() && gl0[i] == key;
            assert(gl[i] == key);
        }
        assert forall|g: int| 0 <= g < t.ng implies gl.contains(#[trigger] grp_key(*t, c, g)) by {
            assert(gl[gl0.len() + g] == grp_key(*t, c, g));
        }
    }
    Ghost(gl)
}

/// The groups of all partitions, partition by partition.
pub fn flatten(tabs: &Vec<GrpTab>, Ghost(c): Ghost<Ctx>, Ghost(pbits): Ghost<u64>) -> (r: (Flat, Ghost<Seq<Row>>))
    requires
        ctx_ok(c), pbits <= MAX_PBITS, tabs@.len() == pow2u(pbits),
        forall|p: int| 0 <= p < tabs@.len() ==> grp_wf(#[trigger] tabs@[p], c, pbits, p, plist(c, pbits, p, 0, c.q)),
    ensures flat_ok(r.0, c, r.1@),
{
    let np = tabs.len();
    // The number of groups (saturated), so the flat vectors are allocated once.
    let mut total: usize = 0;
    let mut q: usize = 0;
    while q < np
        invariant np == tabs@.len(),
        decreases np - q,
    {
        let ng = tabs[q].ng;
        total = if total > usize::MAX - ng { usize::MAX } else { total + ng };
        q = q + 1;
    }
    let mut f = Flat { fk: Vec::with_capacity(total), fs: Vec::with_capacity(total), fa: Vec::with_capacity(total) };
    let ghost mut gl: Seq<Row> = Seq::empty();
    let mut p: usize = 0;
    while p < np
        invariant
            ctx_ok(c), pbits <= MAX_PBITS, np == tabs@.len(), np == pow2u(pbits), p <= np,
            forall|q2: int| 0 <= q2 < tabs@.len() ==> grp_wf(#[trigger] tabs@[q2], c, pbits, q2, plist(c, pbits, q2, 0, c.q)),
            f.fk@.len() == gl.len() && f.fs@.len() == gl.len() && f.fa@.len() == gl.len(),
            forall|i: int| 0 <= i < gl.len() ==> #[trigger] elem_ok(f, c, gl, i),
            forall|i: int| 0 <= i < gl.len() ==> kpart(#[trigger] gl[i], pbits) < p,
            gl.no_duplicates(),
            forall|key: Row| #[trigger] gacc(c, 0, key, c.q) > 0 && kpart(key, pbits) < p ==> gl.contains(key),
        decreases np - p,
    {
        let t = &tabs[p];
        proof {
            lemma_part_groups(*t, c, pbits, p as int);
        }
        let ghost gl0 = gl;
        let Ghost(gl1) = flatten_part(&mut f, t, Ghost(c), Ghost(pbits), Ghost(p as int), Ghost(gl0));
        proof {
            gl = gl1;
            assert forall|key: Row| #[trigger] gacc(c, 0, key, c.q) > 0 && kpart(key, pbits) < p + 1 implies gl.contains(key) by {
                if kpart(key, pbits) < p {
                    assert(gl0.contains(key));
                } else {
                    let g = choose|g: int| 0 <= g < t.ng && #[trigger] grp_key(*t, c, g) == key;
                    assert(gl.contains(grp_key(*t, c, g)));
                }
            }
        }
        p = p + 1;
    }
    proof {
        assert forall|key: Row| #[trigger] gl.contains(key) <==> gacc(c, 0, key, c.q) > 0 by {
            if gl.contains(key) {
                let i = choose|i: int| 0 <= i < gl.len() && gl[i] == key;
                assert(elem_ok(f, c, gl, i));
            }
            if gacc(c, 0, key, c.q) > 0 {
                let k = lemma_gacc_witness(c, key, c.q);
                assert(key[2] == Val::Text(p_tag(c, k)));
                lemma_tpart_range(p_tag(c, k), pbits);
            }
        }
    }
    (f, Ghost(gl))
}

} // verus!
