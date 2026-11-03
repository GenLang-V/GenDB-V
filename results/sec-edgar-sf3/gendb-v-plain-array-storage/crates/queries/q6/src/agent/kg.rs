//! One partition of the join-key index: the distinct join keys (member, tag, version) of the entries of partition
//! `p`, each with a representative entry, and for every entry of the partition (in row order) its key's id.
//!
//! Layout: key `g` is node `nodes[g]`: its hash, member, representative `pre` row, and the place of its adsh, tag
//! and version bytes in the partition's `arena` (`ar`, at `aoff`, `dl` + `tl` + `vl` bytes; a key that found no
//! room in the arena keeps `ar == false` and is compared with its `pre` row's columns). Keys are chained by the top
//! bits of their hash (`common::chain`, `next`) and a filter bitmap holds a bit of every key's hash
//! (`common::bits`). `kg_find` compares the hash and the adsh, tag and version bytes, so it is exact (two entries
//! have the same member iff they have the same adsh, `lemma_trip_key`); with the bytes in the arena, a hit touches
//! the filter, the bucket, the node and one arena range, and needs no lookup of the member. Keys are distinct, so
//! a `num` row matches at most one key.
use vstd::prelude::*;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::agent::common::bytes::*;
use crate::agent::common::chain::*;
use crate::agent::common::bits::*;
use crate::agent::ctx::*;
use crate::agent::keys::*;
use crate::agent::subidx::*;

verus! {

/// The join key of entry `k` and of the key of a `num` row.
pub open spec fn ekey(c: Ctx, k: int) -> (int, Seq<u8>, Seq<u8>) {
    (esub(c, k), p_tag(c, k), p_ver(c, k))
}

/// One join key: `.0` its hash, `.1` its member, `.2` its representative `pre` row, `.3` whether its key bytes are
/// in the arena, at `.4`, with `.5` adsh, `.6` tag and `.7` version bytes. A tuple of integers, so the node vector
/// is allocated zeroed (lazily, by the kernel) instead of being written node by node on the calling thread.
pub type KNode = (u64, usize, usize, bool, usize, usize, usize, usize);

pub struct KgPart {
    pub nkg: usize,
    pub head: Vec<usize>,
    pub shift: u64,
    pub next: Vec<usize>,
    pub nodes: Vec<KNode>,
    pub arena: Vec<u8>,
    pub alen: usize,
    pub filter: Vec<u64>,
    pub fshift: u64,
    pub tfilter: Vec<u64>,
    pub kof: Vec<usize>,
    pub nent: usize,
}

pub open spec fn all_in() -> spec_fn(int) -> bool {
    |g: int| true
}

pub open spec fn kg_bkt(x: KgPart) -> spec_fn(int) -> int {
    |g: int| (x.nodes@[g].0 >> x.shift) as int
}

pub open spec fn kg_fbit(x: KgPart) -> spec_fn(int) -> int {
    |g: int| (x.nodes@[g].0 >> x.fshift) as int
}

/// The tag-filter bit of a tag hash: its low bits.
pub open spec fn tbit(x: KgPart, th: u64) -> int {
    (th & ((x.tfilter@.len() * 64 - 1) as u64)) as int
}

pub open spec fn kg_tbit(x: KgPart, c: Ctx) -> spec_fn(int) -> int {
    |g: int| tbit(x, sig_spec(p_tag(c, x.nodes@[g].2 as int)))
}

/// The key of key id `g`.
pub open spec fn kg_key(x: KgPart, c: Ctx, g: int) -> (int, Seq<u8>, Seq<u8>) {
    ekey(c, x.nodes@[g].2 as int)
}

/// The table shape (independent of the entries).
pub open spec fn kg_shape(x: KgPart) -> bool {
    &&& 1 <= 64 - x.shift <= 30
    &&& x.head@.len() == pow2_64(64 - x.shift)
    &&& 1 <= 64 - x.fshift <= 30
    &&& x.filter@.len() * 64 == pow2_64(64 - x.fshift)
    &&& x.nkg <= x.next@.len() && x.nkg <= x.nodes@.len()
    &&& x.nent <= x.kof@.len()
    &&& x.next@.len() < NONE
    &&& x.alen <= x.arena@.len()
    &&& x.tfilter@.len() == x.filter@.len()
}

/// Node `g`'s arena bytes are its key's adsh, tag and version.
pub open spec fn node_bytes_ok(x: KgPart, c: Ctx, g: int) -> bool {
    let nd = x.nodes@[g];
    nd.3 ==> {
        &&& nd.4 + nd.5 + nd.6 + nd.7 <= x.alen
        &&& x.arena@.subrange(nd.4 as int, nd.4 + nd.5) == p_adsh(c, nd.2 as int)
        &&& x.arena@.subrange(nd.4 + nd.5, nd.4 + nd.5 + nd.6) == p_tag(c, nd.2 as int)
        &&& x.arena@.subrange(nd.4 + nd.5 + nd.6, nd.4 + nd.5 + nd.6 + nd.7) == p_ver(c, nd.2 as int)
    }
}

/// The `pre` row of node `g` has adsh `a`, tag `t` and version `v`.
pub open spec fn node_has(x: KgPart, c: Ctx, g: int, a: Seq<u8>, t: Seq<u8>, v: Seq<u8>) -> bool {
    let k = x.nodes@[g].2 as int;
    p_adsh(c, k) == a && p_tag(c, k) == t && p_ver(c, k) == v
}

/// For an entry `k`, a join key `(sub_for(a), t, v)` with a member's adsh `a` is its key iff its adsh, tag and
/// version are `a`, `t`, `v`.
pub proof fn lemma_trip_key(c: Ctx, k: int, a: Seq<u8>, t: Seq<u8>, v: Seq<u8>)
    requires pre_ok(c, k), has_member(c, a),
    ensures (ekey(c, k) == (sub_for(c, a), t, v)) == (p_adsh(c, k) == a && p_tag(c, k) == t && p_ver(c, k) == v),
{
    lemma_sub_for(c, a);
    lemma_sub_for(c, p_adsh(c, k));
}

/// The index of the entries `ents` (all of partition `p`): `x.nent == ents.len()` entries, distinct keys.
#[verifier::opaque]
pub open spec fn kg_wf(x: KgPart, c: Ctx, pbits: u64, p: int, ents: Seq<int>) -> bool {
    &&& kg_shape(x)
    &&& x.nent as int == ents.len()
    &&& x.nkg <= x.nent
    &&& forall|j: int| 0 <= j < ents.len() ==> pre_ok(c, #[trigger] ents[j]) && epart(c, pbits, ents[j]) == p
    &&& forall|g: int| 0 <= g < x.nkg ==> pre_ok(c, #[trigger] x.nodes@[g].2 as int) && epart(c, pbits, x.nodes@[g].2 as int) == p
    &&& forall|g: int| 0 <= g < x.nkg ==> #[trigger] x.nodes@[g].1 as int == esub(c, x.nodes@[g].2 as int)
    &&& forall|g: int| 0 <= g < x.nkg ==> #[trigger] x.nodes@[g].0 == ekh(c, x.nodes@[g].2 as int)
    &&& forall|g: int| 0 <= g < x.nkg ==> #[trigger] node_bytes_ok(x, c, g)
    &&& forall|g1: int, g2: int| 0 <= g1 < x.nkg && 0 <= g2 < x.nkg && g1 != g2 ==>
            #[trigger] kg_key(x, c, g1) != #[trigger] kg_key(x, c, g2)
    &&& forall|j: int| 0 <= j < x.nent ==> #[trigger] x.kof@[j] < x.nkg
    &&& forall|j: int| 0 <= j < x.nent ==> kg_key(x, c, #[trigger] x.kof@[j] as int) == ekey(c, ents[j])
    &&& chain_wf(x.head@, x.next@, all_in(), kg_bkt(x), x.nkg as int)
    &&& filter_wf(x.filter@, all_in(), kg_fbit(x), x.nkg as int)
    &&& filter_wf(x.tfilter@, all_in(), kg_tbit(x, c), x.nkg as int)
}

/// The little-endian word of vector bytes `v[p..p + 8]` (the highest byte is read first, so one bounds check
/// covers the word).
#[inline(always)]
pub fn vword(v: &Vec<u8>, p: usize) -> (w: u64)
    requires p + 8 <= v@.len(),
    ensures w == word_spec(v@, p as int),
    no_unwind
{
    proof {
        assert(v@.len() == v.len() as int);
    }
    let b7 = v[p + 7];
    let b6 = v[p + 6];
    let b5 = v[p + 5];
    let b4 = v[p + 4];
    let b3 = v[p + 3];
    let b2 = v[p + 2];
    let b1 = v[p + 1];
    let b0 = v[p];
    (b0 as u64) | ((b1 as u64) << 8u64) | ((b2 as u64) << 16u64) | ((b3 as u64) << 24u64)
        | ((b4 as u64) << 32u64) | ((b5 as u64) << 40u64) | ((b6 as u64) << 48u64) | ((b7 as u64) << 56u64)
}

/// Bytes `v[off..off + n]` of a vector are the bytes of `y` (`n` of them), compared eight at a time.
#[inline(always)]
pub fn vec_range_eq(v: &Vec<u8>, off: usize, n: usize, y: &[u8], yn: usize) -> (r: bool)
    requires off + n <= v@.len(), yn == y@.len(),
    ensures r == (v@.subrange(off as int, off + n) == y@),
    no_unwind
{
    if n != yn {
        proof {
            assert(v@.subrange(off as int, off + n).len() != y@.len());
        }
        return false;
    }
    proof {
        assert(v@.len() == v.len() as int);
    }
    let mut j: usize = 0;
    while n - j >= 8
        invariant
            off + n <= v@.len(), v@.len() <= usize::MAX, yn == y@.len(), n == yn, j <= n,
            forall|t: int| 0 <= t < j ==> v@[off + t] == y@[t],
        decreases n - j,
    {
        let wv = vword(v, off + j);
        let wy = word_at(y, j, Ghost(yn as int));
        if wv != wy {
            proof {
                let s = v@.subrange(off as int, off + n);
                if s == y@ {
                    assert forall|t: int| 0 <= t < 8 implies #[trigger] v@[off + j + t] == y@[j + t] by {
                        assert(s[j + t] == v@[off + j + t]);
                    }
                    assert(word_spec(v@, off + j) == word_spec(y@, j as int));
                }
            }
            return false;
        }
        proof {
            lemma_word_eq_at(v@, off + j, y@, j as int);
            assert forall|t: int| 0 <= t < j + 8 implies v@[off + t] == y@[t] by {
                if t >= j {
                    let u = t - j;
                    assert(v@[off + j + u] == y@[j + u]);
                }
            }
        }
        j = j + 8;
    }
    while j < n
        invariant
            off + n <= v@.len(), v@.len() <= usize::MAX, yn == y@.len(), n == yn, j <= n,
            forall|t: int| 0 <= t < j ==> v@[off + t] == y@[t],
        decreases n - j,
    {
        if v[off + j] != y[j] {
            proof {
                assert(v@.subrange(off as int, off + n)[j as int] != y@[j as int]);
            }
            return false;
        }
        j = j + 1;
    }
    proof {
        assert(v@.subrange(off as int, off + n) =~= y@);
    }
    true
}

/// Node `g` has the adsh, tag and version bytes `ab`, `tb`, `vb`.
#[inline(always)]
pub fn node_is(x: &KgPart, g: usize, ab: &[u8], dl: usize, tb: &[u8], tl: usize, vb: &[u8], vl: usize, padsh: &TextCol,
    ptag: &TextCol, pver: &TextCol,
    Ghost(c): Ghost<Ctx>, Ghost(pbits): Ghost<u64>, Ghost(p): Ghost<int>, Ghost(ents): Ghost<Seq<int>>) -> (r: bool)
    requires
        kg_wf(*x, c, pbits, p, ents), ctx_ok(c), g < x.nkg,
        padsh@ == p_adsh_v(c), ptag@ == p_tag_v(c), pver@ == p_ver_v(c),
        dl == ab@.len(), tl == tb@.len(), vl == vb@.len(),
    ensures r == node_has(*x, c, g as int, ab@, tb@, vb@),
    no_unwind
{
    proof {
        reveal(kg_wf);
        lemma_views_wf(c);
        assert(node_bytes_ok(*x, c, g as int));
    }
    let nd = x.nodes[g];
    if nd.3 {
        vec_range_eq(&x.arena, nd.4, nd.5, ab, dl) && vec_range_eq(&x.arena, nd.4 + nd.5, nd.6, tb, tl)
            && vec_range_eq(&x.arena, nd.4 + nd.5 + nd.6, nd.7, vb, vl)
    } else {
        let k = nd.2;
        proof {
            assert(pre_ok(c, k as int));
        }
        let a2 = text_of(padsh, k, Ghost(c.q));
        let a2l = text_len(padsh, k, Ghost(c.q));
        if !text_same(a2, a2l, ab, dl) {
            return false;
        }
        let t2 = text_of(ptag, k, Ghost(c.q));
        let t2l = text_len(ptag, k, Ghost(c.q));
        if !text_same(t2, t2l, tb, tl) {
            return false;
        }
        let v2 = text_of(pver, k, Ghost(c.q));
        let v2l = text_len(pver, k, Ghost(c.q));
        text_same(v2, v2l, vb, vl)
    }
}

/// The probe property of a walk: node `g`'s entry does not have the adsh, tag and version `a`, `t`, `v`.
pub open spec fn not_has(x: KgPart, c: Ctx, a: Seq<u8>, t: Seq<u8>, v: Seq<u8>) -> spec_fn(int) -> bool {
    |g: int| !node_has(x, c, g, a, t, v)
}

/// The bucket of hash `h`.
pub open spec fn hbkt(x: KgPart, h: u64) -> int {
    (h >> x.shift) as int
}

/// A node with the probed bytes has the probed hash, so it lies in the probed bucket and has its filter bit.
pub proof fn lemma_node_hash(x: KgPart, c: Ctx, pbits: u64, p: int, ents: Seq<int>, g: int, a: Seq<u8>, t: Seq<u8>, v: Seq<u8>)
    requires kg_wf(x, c, pbits, p, ents), 0 <= g < x.nkg, node_has(x, c, g, a, t, v),
    ensures
        x.nodes@[g].0 == kh_spec(sig_spec(t), sig_spec(a) as int, sig_spec(v)),
        kg_bkt(x)(g) == hbkt(x, x.nodes@[g].0),
        bit_set(x.filter@, kg_fbit(x)(g)),
{
    reveal(kg_wf);
    assert(all_in()(g));
}

/// Whether some key of the index may have hash `h` (its filter bit): `false` proves that no node has bytes of that
/// hash.
#[inline(always)]
pub fn kg_maybe(x: &KgPart, h: u64, Ghost(c): Ghost<Ctx>, Ghost(pbits): Ghost<u64>, Ghost(p): Ghost<int>,
    Ghost(ents): Ghost<Seq<int>>) -> (r: bool)
    requires kg_wf(*x, c, pbits, p, ents),
    ensures
        !r ==> forall|g: int, a: Seq<u8>, t: Seq<u8>, v: Seq<u8>| 0 <= g < x.nkg && #[trigger] node_has(*x, c, g, a, t, v)
            ==> kh_spec(sig_spec(t), sig_spec(a) as int, sig_spec(v)) != h,
    no_unwind
{
    proof {
        reveal(kg_wf);
        lemma_top_bits(h, x.fshift, (64 - x.fshift) as u64);
    }
    let f = (h >> x.fshift) as usize;
    let nw = x.filter.len();
    let r = test_bit(&x.filter, f, Ghost(nw as int));
    proof {
        assert forall|g: int, a: Seq<u8>, t: Seq<u8>, v: Seq<u8>| 0 <= g < x.nkg && #[trigger] node_has(*x, c, g, a, t, v)
            implies kh_spec(sig_spec(t), sig_spec(a) as int, sig_spec(v)) != h || r by {
            lemma_node_hash(*x, c, pbits, p, ents, g, a, t, v);
        }
    }
    r
}

/// The head of the bucket of hash `h`: a walk of the probed bytes starts there.
#[inline(always)]
pub fn kg_head(x: &KgPart, h: u64, Ghost(c): Ghost<Ctx>, Ghost(pbits): Ghost<u64>, Ghost(p): Ghost<int>,
    Ghost(ents): Ghost<Seq<int>>, Ghost(a): Ghost<Seq<u8>>, Ghost(t): Ghost<Seq<u8>>, Ghost(v): Ghost<Seq<u8>>) -> (cur: usize)
    requires kg_wf(*x, c, pbits, p, ents),
    ensures walk_ok(cur, all_in(), kg_bkt(*x), x.nkg as int, hbkt(*x, h), not_has(*x, c, a, t, v)),
    no_unwind
{
    proof {
        reveal(kg_wf);
        lemma_top_bits(h, x.shift, (64 - x.shift) as u64);
        lemma_walk_start(x.head@, x.next@, all_in(), kg_bkt(*x), x.nkg as int, hbkt(*x, h), not_has(*x, c, a, t, v));
    }
    x.head[(h >> x.shift) as usize]
}

/// One step of a walk of the probed bytes (hash `h`): past `cur` when its hash is not `h`, else `cur` itself.
#[inline(always)]
pub fn kg_step(x: &KgPart, cur: usize, h: u64, Ghost(c): Ghost<Ctx>, Ghost(pbits): Ghost<u64>, Ghost(p): Ghost<int>,
    Ghost(ents): Ghost<Seq<int>>, Ghost(a): Ghost<Seq<u8>>, Ghost(t): Ghost<Seq<u8>>, Ghost(v): Ghost<Seq<u8>>) -> (r: usize)
    requires
        kg_wf(*x, c, pbits, p, ents), cur != NONE,
        h == kh_spec(sig_spec(t), sig_spec(a) as int, sig_spec(v)),
        walk_ok(cur, all_in(), kg_bkt(*x), x.nkg as int, hbkt(*x, h), not_has(*x, c, a, t, v)),
    ensures walk_ok(r, all_in(), kg_bkt(*x), x.nkg as int, hbkt(*x, h), not_has(*x, c, a, t, v)),
    no_unwind
{
    proof {
        reveal(kg_wf);
    }
    let hit = x.nodes[cur].0 == h;
    let nx = x.next[cur];
    proof {
        if !hit {
            if node_has(*x, c, cur as int, a, t, v) {
                lemma_node_hash(*x, c, pbits, p, ents, cur as int, a, t, v);
            }
            lemma_walk_step(x.head@, x.next@, all_in(), kg_bkt(*x), x.nkg as int, hbkt(*x, h), not_has(*x, c, a, t, v), cur);
        }
    }
    if hit { cur } else { nx }
}

/// The id of the key whose entry has the adsh, tag and version bytes `ab`, `tb`, `vb` (hash `h`), or `NONE` when
/// no key of the index has them; the walk of bucket `h` resumes at `cur0`.
pub fn kg_find_from(x: &KgPart, cur0: usize, ab: &[u8], dl: usize, tb: &[u8], tl: usize, vb: &[u8], vl: usize, h: u64,
    padsh: &TextCol, ptag: &TextCol, pver: &TextCol, Ghost(c): Ghost<Ctx>, Ghost(pbits): Ghost<u64>, Ghost(p): Ghost<int>,
    Ghost(ents): Ghost<Seq<int>>) -> (r: usize)
    requires
        kg_wf(*x, c, pbits, p, ents), ctx_ok(c),
        padsh@ == p_adsh_v(c), ptag@ == p_tag_v(c), pver@ == p_ver_v(c),
        dl == ab@.len(), tl == tb@.len(), vl == vb@.len(),
        h == kh_spec(sig_spec(tb@), sig_spec(ab@) as int, sig_spec(vb@)),
        walk_ok(cur0, all_in(), kg_bkt(*x), x.nkg as int, hbkt(*x, h), not_has(*x, c, ab@, tb@, vb@)),
    ensures
        r != NONE ==> r < x.nkg && node_has(*x, c, r as int, ab@, tb@, vb@),
        r == NONE ==> forall|g: int| 0 <= g < x.nkg ==> !#[trigger] node_has(*x, c, g, ab@, tb@, vb@),
    no_unwind
{
    proof {
        lemma_views_wf(c);
        reveal(kg_wf);
    }
    let ghost inset = all_in();
    let ghost bkt = kg_bkt(*x);
    let ghost b = hbkt(*x, h);
    let ghost pr = not_has(*x, c, ab@, tb@, vb@);
    let mut cur = cur0;
    while cur != NONE
        invariant
            kg_wf(*x, c, pbits, p, ents), ctx_ok(c), padsh@ == p_adsh_v(c), ptag@ == p_tag_v(c), pver@ == p_ver_v(c),
            dl == ab@.len(), tl == tb@.len(), vl == vb@.len(), h == kh_spec(sig_spec(tb@), sig_spec(ab@) as int, sig_spec(vb@)),
            inset == all_in(), bkt == kg_bkt(*x), b == hbkt(*x, h),
            pr == not_has(*x, c, ab@, tb@, vb@),
            walk_ok(cur, inset, bkt, x.nkg as int, b, pr),
        decreases if cur == NONE { 0 } else { cur + 1 },
    {
        proof {
            reveal(kg_wf);
        }
        let nd = x.nodes[cur];
        if nd.0 == h {
            if node_is(x, cur, ab, dl, tb, tl, vb, vl, padsh, ptag, pver, Ghost(c), Ghost(pbits), Ghost(p), Ghost(ents)) {
                return cur;
            }
        }
        proof {
            if nd.0 != h {
                if node_has(*x, c, cur as int, ab@, tb@, vb@) {
                    lemma_node_hash(*x, c, pbits, p, ents, cur as int, ab@, tb@, vb@);
                }
            }
            lemma_walk_step(x.head@, x.next@, inset, bkt, x.nkg as int, b, pr, cur);
        }
        cur = x.next[cur];
    }
    proof {
        lemma_walk_done(inset, bkt, x.nkg as int, b, pr);
        assert forall|g: int| 0 <= g < x.nkg implies !#[trigger] node_has(*x, c, g, ab@, tb@, vb@) by {
            if node_has(*x, c, g, ab@, tb@, vb@) {
                lemma_node_hash(*x, c, pbits, p, ents, g, ab@, tb@, vb@);
                assert(inset(g));
                assert(!pr(g));
            }
        }
    }
    NONE
}

/// The id of the key whose entry has the adsh, tag and version bytes `ab`, `tb`, `vb` (hash `h`), or `NONE` when
/// no key of the index has them.
pub fn kg_find(x: &KgPart, ab: &[u8], dl: usize, tb: &[u8], tl: usize, vb: &[u8], vl: usize, h: u64,
    padsh: &TextCol, ptag: &TextCol, pver: &TextCol, Ghost(c): Ghost<Ctx>, Ghost(pbits): Ghost<u64>, Ghost(p): Ghost<int>,
    Ghost(ents): Ghost<Seq<int>>) -> (r: usize)
    requires
        kg_wf(*x, c, pbits, p, ents), ctx_ok(c),
        padsh@ == p_adsh_v(c), ptag@ == p_tag_v(c), pver@ == p_ver_v(c),
        dl == ab@.len(), tl == tb@.len(), vl == vb@.len(),
        h == kh_spec(sig_spec(tb@), sig_spec(ab@) as int, sig_spec(vb@)),
    ensures
        r != NONE ==> r < x.nkg && node_has(*x, c, r as int, ab@, tb@, vb@),
        r == NONE ==> forall|g: int| 0 <= g < x.nkg ==> !#[trigger] node_has(*x, c, g, ab@, tb@, vb@),
    no_unwind
{
    if !kg_maybe(x, h, Ghost(c), Ghost(pbits), Ghost(p), Ghost(ents)) {
        return NONE;
    }
    let cur = kg_head(x, h, Ghost(c), Ghost(pbits), Ghost(p), Ghost(ents), Ghost(ab@), Ghost(tb@), Ghost(vb@));
    kg_find_from(x, cur, ab, dl, tb, tl, vb, vl, h, padsh, ptag, pver, Ghost(c), Ghost(pbits), Ghost(p), Ghost(ents))
}

/// What callers of the index use from `kg_wf`.
pub proof fn lemma_kg_facts(x: KgPart, c: Ctx, pbits: u64, p: int, ents: Seq<int>)
    requires kg_wf(x, c, pbits, p, ents),
    ensures
        kg_shape(x),
        x.nent as int == ents.len(),
        x.nkg <= x.nent,
        forall|j: int| 0 <= j < x.nent ==> #[trigger] x.kof@[j] < x.nkg,
        forall|j: int| 0 <= j < x.nent ==> kg_key(x, c, #[trigger] x.kof@[j] as int) == ekey(c, ents[j]),
        forall|g1: int, g2: int| 0 <= g1 < x.nkg && 0 <= g2 < x.nkg && g1 != g2 ==>
            #[trigger] kg_key(x, c, g1) != #[trigger] kg_key(x, c, g2),
        forall|g: int| 0 <= g < x.nkg ==> pre_ok(c, #[trigger] x.nodes@[g].2 as int) && epart(c, pbits, x.nodes@[g].2 as int) == p,
        forall|j: int| 0 <= j < ents.len() ==> pre_ok(c, #[trigger] ents[j]) && epart(c, pbits, ents[j]) == p,
{
    reveal(kg_wf);
}

/// Whether some key of the index may have tag hash `th`: `false` proves that none has a tag of that hash.
#[inline(always)]
pub fn kg_tag_maybe(x: &KgPart, th: u64, Ghost(c): Ghost<Ctx>, Ghost(pbits): Ghost<u64>, Ghost(p): Ghost<int>,
    Ghost(ents): Ghost<Seq<int>>) -> (r: bool)
    requires kg_wf(*x, c, pbits, p, ents),
    ensures !r ==> forall|g: int| 0 <= g < x.nkg ==> #[trigger] sig_spec(p_tag(c, x.nodes@[g].2 as int)) != th,
    no_unwind
{
    proof {
        reveal(kg_wf);
        lemma_pow2_le((64 - x.fshift) as int);
    }
    let nw = x.tfilter.len();
    proof {
        assert(x.tfilter@.len() == x.tfilter.len());
        assert(nw * 64 >= 1);
        assert(nw >= 1);
        assert(nw * 64 <= 0x4000_0000);
    }
    let mask = (nw * 64 - 1) as u64;
    let b = (th & mask) as usize;
    proof {
        assert(th & mask <= mask) by (bit_vector);
    }
    let r = test_bit(&x.tfilter, b, Ghost(nw as int));
    proof {
        assert forall|g: int| 0 <= g < x.nkg implies #[trigger] sig_spec(p_tag(c, x.nodes@[g].2 as int)) != th || r by {
            if sig_spec(p_tag(c, x.nodes@[g].2 as int)) == th {
                assert(all_in()(g));
                assert(bit_set(x.tfilter@, kg_tbit(*x, c)(g)));
            }
        }
    }
    r
}

} // verus!
