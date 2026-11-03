//! Build of the join-key index of one partition (`kg::KgPart`): the task reads the entries of all pre-scan outputs
//! in task order, keeps those of its partition, and for each one finds its key or inserts it as a new key.
use vstd::prelude::*;
use std::sync::Arc;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::common::bytes::*;
use crate::agent::common::chain::*;
use crate::agent::common::bits::*;
use crate::agent::ctx::*;
use crate::agent::keys::*;
use crate::agent::subidx::*;
use crate::agent::prescan::*;
use crate::agent::plists::*;
use crate::agent::kg::*;
use crate::agent::common::lazy::*;

verus! {

/// An index with room for `cap` entries (about `2 * cap` buckets) and `acap` arena bytes, not yet cleared: its
/// buffers are lazily zeroed (`common::lazy`), so the calling thread writes none of them; the worker that fills the
/// index starts with `kg_clear`.
pub fn kg_new(cap: usize, acap: usize) -> (x: KgPart)
    requires cap < NONE,
    ensures
        kg_shape(x),
        x.next@.len() >= cap, x.nodes@.len() >= cap, x.kof@.len() >= cap,
{
    let bits = bits_for(cap);
    let fbits = bits + 3;
    proof {
        lemma_pow2_shift(bits);
        lemma_pow2_shift(fbits);
        lemma_pow2_shift((fbits - 6) as u64);
        let fb6 = (fbits - 6) as u64;
        assert((1u64 << fbits) == 64 * (1u64 << fb6)) by (bit_vector) requires 7 <= fbits <= 30, fb6 == fbits - 6;
    }
    let nb: usize = 1usize << bits;
    let nw: usize = 1usize << (fbits - 6);
    proof {
        assert(nb as int == ((1u64 << bits) as int)) by (bit_vector) requires 4 <= bits <= 27, nb == 1usize << bits;
        let fb6 = (fbits - 6) as u64;
        assert(nw as int == ((1u64 << fb6) as int)) by (bit_vector) requires 1 <= fb6 <= 24, nw == 1usize << fb6;
    }
    // The heads are set to `NONE` by `kg_clear`, on the worker.
    let mut head: Vec<usize> = vec![0usize; lazy_cap(nb, 8)];
    head.truncate(nb);
    let ncap = lazy_cap(cap, 8);
    let x = KgPart {
        nkg: 0,
        head,
        shift: 64 - bits,
        next: vec![0usize; ncap],
        nodes: vec![(0u64, 0usize, 0usize, false, 0usize, 0usize, 0usize, 0usize); lazy_cap(cap, 64)],
        arena: vec![0u8; acap],
        alen: 0,
        filter: vec![0u64; nw],
        fshift: 64 - fbits,
        tfilter: vec![0u64; nw],
        kof: vec![0usize; lazy_cap(cap, 8)],
        nent: 0,
    };
    x
}

/// The empty index: no key, no entry, an empty arena and every bucket `NONE` (run on the worker that fills it).
pub fn kg_clear(x: &mut KgPart)
    requires kg_shape(*old(x)),
    ensures
        forall|c: Ctx, pbits: u64, p: int| #[trigger] kg_wf(*final(x), c, pbits, p, Seq::<int>::empty()),
        final(x).next@.len() == old(x).next@.len(), final(x).nodes@.len() == old(x).nodes@.len(),
        final(x).kof@.len() == old(x).kof@.len(),
    no_unwind
{
    x.nkg = 0;
    x.nent = 0;
    x.alen = 0;
    fill(&mut x.head, NONE);
    proof {
        reveal(kg_wf);
        assert forall|c: Ctx, pbits: u64, p: int| #[trigger] kg_wf(*x, c, pbits, p, Seq::<int>::empty()) by {
            lemma_empty(x.head@, x.next@, all_in(), kg_bkt(*x));
        }
    }
}

/// Copy `src` (`n` bytes) into `v` at `at`; the other bytes of `v` are kept.
fn copy_into(v: &mut Vec<u8>, at: usize, src: &[u8], n: usize)
    requires at + n <= old(v)@.len(), n == src@.len(),
    ensures
        final(v)@.len() == old(v)@.len(),
        final(v)@.subrange(at as int, at + n) == src@,
        forall|t: int| 0 <= t < at ==> #[trigger] final(v)@[t] == old(v)@[t],
    no_unwind
{
    let ghost v0 = v@;
    proof {
        assert(v@.len() == v.len() as int);
    }
    let mut j: usize = 0;
    while j < n
        invariant
            at + n <= v@.len(), v0.len() <= usize::MAX, n == src@.len(), j <= n, v@.len() == v0.len(),
            forall|t: int| 0 <= t < j ==> #[trigger] v@[at + t] == src@[t],
            forall|t: int| 0 <= t < at ==> #[trigger] v@[t] == v0[t],
        decreases n - j,
    {
        v[at + j] = src[j];
        j = j + 1;
    }
    proof {
        assert forall|t: int| 0 <= t < n implies #[trigger] v@.subrange(at as int, at + n)[t] == src@[t] by {
            assert(v@[at + t] == src@[t]);
        }
        assert(v@.subrange(at as int, at + n) =~= src@);
    }
}

/// A new key for entry `k`, at id `nkg`.
proof fn lemma_kg_insert(x: KgPart, y: KgPart, c: Ctx, pbits: u64, p: int, ents: Seq<int>, k: usize, s: usize, nd: KNode)
    requires
        kg_wf(x, c, pbits, p, ents),
        pre_ok(c, k as int), epart(c, pbits, k as int) == p, s as int == esub(c, k as int),
        forall|g: int| 0 <= g < x.nkg ==> #[trigger] kg_key(x, c, g) != ekey(c, k as int),
        x.nkg < x.next@.len(), x.nkg < x.nodes@.len(), x.nent < x.kof@.len(),
        nd.0 == ekh(c, k as int), nd.1 == s, nd.2 == k,
        y.nkg == x.nkg + 1, y.nent == x.nent + 1, y.shift == x.shift, y.fshift == x.fshift,
        y.nodes@ == x.nodes@.update(x.nkg as int, nd),
        y.head@ == x.head@.update((ekh(c, k as int) >> x.shift) as int, x.nkg),
        y.next@ == x.next@.update(x.nkg as int, x.head@[(ekh(c, k as int) >> x.shift) as int]),
        y.kof@ == x.kof@.update(x.nent as int, x.nkg),
        y.filter@.len() == x.filter@.len(),
        bit_set(y.filter@, (ekh(c, k as int) >> x.fshift) as int),
        forall|j: int| #[trigger] bit_set(x.filter@, j) ==> bit_set(y.filter@, j),
        y.tfilter@.len() == x.tfilter@.len(),
        bit_set(y.tfilter@, tbit(x, sig_spec(p_tag(c, k as int)))),
        forall|j: int| #[trigger] bit_set(x.tfilter@, j) ==> bit_set(y.tfilter@, j),
        x.alen <= y.alen <= y.arena@.len(), y.arena@.len() == x.arena@.len(),
        forall|t: int| 0 <= t < x.alen ==> #[trigger] y.arena@[t] == x.arena@[t],
        nd.3 ==> nd.4 + nd.5 + nd.6 + nd.7 <= y.alen
            && y.arena@.subrange(nd.4 as int, nd.4 + nd.5) == p_adsh(c, k as int)
            && y.arena@.subrange(nd.4 + nd.5, nd.4 + nd.5 + nd.6) == p_tag(c, k as int)
            && y.arena@.subrange(nd.4 + nd.5 + nd.6, nd.4 + nd.5 + nd.6 + nd.7) == p_ver(c, k as int),
    ensures kg_wf(y, c, pbits, p, ents.push(k as int)),
{
    reveal(kg_wf);
    let g0 = x.nkg as int;
    let b = (ekh(c, k as int) >> x.shift) as int;
    lemma_top_bits(ekh(c, k as int), x.shift, (64 - x.shift) as u64);
    lemma_top_bits(ekh(c, k as int), x.fshift, (64 - x.fshift) as u64);
    assert forall|g: int| 0 <= g < g0 implies #[trigger] kg_bkt(y)(g) == kg_bkt(x)(g) by {
        assert(y.nodes@[g] == x.nodes@[g]);
    }
    assert(chain_wf(x.head@, x.next@, all_in(), kg_bkt(x), g0));
    lemma_ext(x.head@, x.next@, all_in(), kg_bkt(x), all_in(), kg_bkt(y), x.next@, g0);
    assert(kg_bkt(y)(g0) == b);
    lemma_insert(x.head@, x.next@, all_in(), kg_bkt(y), g0, b);
    assert(chain_wf(y.head@, y.next@, all_in(), kg_bkt(y), y.nkg as int));
    let e2 = ents.push(k as int);
    assert forall|g: int| 0 <= g < g0 implies #[trigger] kg_key(y, c, g) == kg_key(x, c, g) by {
        assert(y.nodes@[g] == x.nodes@[g]);
    }
    assert(kg_key(y, c, g0) == ekey(c, k as int));
    assert forall|g1: int, g2: int| 0 <= g1 < y.nkg && 0 <= g2 < y.nkg && g1 != g2 implies
        #[trigger] kg_key(y, c, g1) != #[trigger] kg_key(y, c, g2) by {
        if g1 < g0 && g2 < g0 {
            assert(kg_key(x, c, g1) != kg_key(x, c, g2));
        } else if g1 < g0 {
            assert(kg_key(x, c, g1) != ekey(c, k as int));
        } else if g2 < g0 {
            assert(kg_key(x, c, g2) != ekey(c, k as int));
        }
    }
    assert forall|j: int| 0 <= j < y.nent implies #[trigger] y.kof@[j] < y.nkg by {
        if j < x.nent {
            assert(y.kof@[j] == x.kof@[j]);
        }
    }
    assert forall|j: int| 0 <= j < y.nent implies kg_key(y, c, #[trigger] y.kof@[j] as int) == ekey(c, e2[j]) by {
        if j < x.nent {
            assert(y.kof@[j] == x.kof@[j]);
            assert(x.kof@[j] < x.nkg);
            assert(kg_key(x, c, x.kof@[j] as int) == ekey(c, ents[j]));
        }
    }
    assert forall|g: int| 0 <= g < y.nkg && #[trigger] all_in()(g) implies bit_set(y.filter@, kg_fbit(y)(g)) by {
        if g < g0 {
            assert(y.nodes@[g] == x.nodes@[g]);
            assert(bit_set(x.filter@, kg_fbit(x)(g)));
        }
    }
    assert forall|g: int| 0 <= g < y.nkg && #[trigger] all_in()(g) implies bit_set(y.tfilter@, kg_tbit(y, c)(g)) by {
        if g < g0 {
            assert(y.nodes@[g] == x.nodes@[g]);
            assert(bit_set(x.tfilter@, kg_tbit(x, c)(g)));
        }
    }
    assert forall|g: int| 0 <= g < y.nkg implies #[trigger] node_bytes_ok(y, c, g) by {
        if g < g0 {
            assert(y.nodes@[g] == x.nodes@[g]);
            assert(node_bytes_ok(x, c, g));
            let n2 = x.nodes@[g];
            if n2.3 {
                assert(y.arena@.subrange(n2.4 as int, n2.4 + n2.5) =~= x.arena@.subrange(n2.4 as int, n2.4 + n2.5));
                assert(y.arena@.subrange(n2.4 + n2.5, n2.4 + n2.5 + n2.6)
                    =~= x.arena@.subrange(n2.4 + n2.5, n2.4 + n2.5 + n2.6));
                assert(y.arena@.subrange(n2.4 + n2.5 + n2.6, n2.4 + n2.5 + n2.6 + n2.7)
                    =~= x.arena@.subrange(n2.4 + n2.5 + n2.6, n2.4 + n2.5 + n2.6 + n2.7));
            }
        }
    }
    assert forall|g: int| 0 <= g < y.nkg implies pre_ok(c, #[trigger] y.nodes@[g].2 as int) && epart(c, pbits, y.nodes@[g].2 as int) == p by {
        if g < g0 {
            assert(y.nodes@[g] == x.nodes@[g]);
        }
    }
    assert forall|g: int| 0 <= g < y.nkg implies #[trigger] y.nodes@[g].1 as int == esub(c, y.nodes@[g].2 as int) by {
        if g < g0 {
            assert(y.nodes@[g] == x.nodes@[g]);
        }
    }
    assert forall|g: int| 0 <= g < y.nkg implies #[trigger] y.nodes@[g].0 == ekh(c, y.nodes@[g].2 as int) by {
        if g < g0 {
            assert(y.nodes@[g] == x.nodes@[g]);
        }
    }
    assert forall|j: int| 0 <= j < e2.len() implies pre_ok(c, #[trigger] e2[j]) && epart(c, pbits, e2[j]) == p by {
        if j < ents.len() {
            assert(e2[j] == ents[j]);
        }
    }
}

/// Entry `k` has the existing key `g`.
proof fn lemma_kg_hit(x: KgPart, y: KgPart, c: Ctx, pbits: u64, p: int, ents: Seq<int>, k: usize, g: usize)
    requires
        kg_wf(x, c, pbits, p, ents),
        pre_ok(c, k as int), epart(c, pbits, k as int) == p,
        g < x.nkg, kg_key(x, c, g as int) == ekey(c, k as int),
        x.nent < x.kof@.len(),
        y.nent == x.nent + 1, y.nkg == x.nkg, y.head == x.head, y.shift == x.shift, y.next == x.next, y.nodes == x.nodes,
        y.arena == x.arena, y.alen == x.alen, y.filter == x.filter, y.fshift == x.fshift, y.tfilter == x.tfilter,
        y.kof@ == x.kof@.update(x.nent as int, g),
    ensures kg_wf(y, c, pbits, p, ents.push(k as int)),
{
    reveal(kg_wf);
    let e2 = ents.push(k as int);
    assert(kg_bkt(y) == kg_bkt(x));
    assert(kg_fbit(y) == kg_fbit(x));
    assert(kg_tbit(y, c) == kg_tbit(x, c));
    assert forall|g2: int| 0 <= g2 < y.nkg implies #[trigger] kg_key(y, c, g2) == kg_key(x, c, g2) by {}
    assert forall|g2: int| 0 <= g2 < y.nkg implies #[trigger] node_bytes_ok(y, c, g2) by {
        assert(node_bytes_ok(x, c, g2));
    }
    assert forall|j: int| 0 <= j < y.nent implies #[trigger] y.kof@[j] < y.nkg by {
        if j < x.nent {
            assert(y.kof@[j] == x.kof@[j]);
        }
    }
    assert forall|j: int| 0 <= j < y.nent implies kg_key(y, c, #[trigger] y.kof@[j] as int) == ekey(c, e2[j]) by {
        if j < x.nent {
            assert(y.kof@[j] == x.kof@[j]);
            assert(kg_key(x, c, x.kof@[j] as int) == ekey(c, ents[j]));
        }
    }
    assert forall|j: int| 0 <= j < e2.len() implies pre_ok(c, #[trigger] e2[j]) && epart(c, pbits, e2[j]) == p by {
        if j < ents.len() {
            assert(e2[j] == ents[j]);
        }
    }
    assert(chain_wf(y.head@, y.next@, all_in(), kg_bkt(y), y.nkg as int));
}

/// Entry `k` (member `s`, key hash `h`) added to the index of its partition: its key found or inserted (its
/// bytes copied into the arena when there is room).
fn kg_take(part: &mut KgPart, k: usize, s: usize, h: u64, padsh: &TextCol, ptag: &TextCol, pver: &TextCol,
    Ghost(c): Ghost<Ctx>, Ghost(pbits): Ghost<u64>, Ghost(p): Ghost<int>, Ghost(ents): Ghost<Seq<int>>)
    requires
        kg_wf(*old(part), c, pbits, p, ents), ctx_ok(c),
        padsh@ == p_adsh_v(c), ptag@ == p_tag_v(c), pver@ == p_ver_v(c),
        pre_ok(c, k as int), epart(c, pbits, k as int) == p, s as int == esub(c, k as int), h == ekh(c, k as int),
        ents.len() < old(part).next@.len(), ents.len() < old(part).nodes@.len(), ents.len() < old(part).kof@.len(),
    ensures
        kg_wf(*final(part), c, pbits, p, ents.push(k as int)),
        final(part).next@.len() == old(part).next@.len(), final(part).nodes@.len() == old(part).nodes@.len(),
        final(part).kof@.len() == old(part).kof@.len(),
    no_unwind
{
    proof {
        lemma_views_wf(c);
        lemma_kg_facts(*part, c, pbits, p, ents);
    }
    let ab = text_of(padsh, k, Ghost(c.q));
    let dl = text_len(padsh, k, Ghost(c.q));
    let tb = text_of(ptag, k, Ghost(c.q));
    let tl = text_len(ptag, k, Ghost(c.q));
    let vb = text_of(pver, k, Ghost(c.q));
    let vl = text_len(pver, k, Ghost(c.q));
    let g = kg_find(part, ab, dl, tb, tl, vb, vl, h, padsh, ptag, pver, Ghost(c), Ghost(pbits), Ghost(p), Ghost(ents));
    let ghost x0 = *part;
    proof {
        reveal(kg_wf);
        assert forall|g2: int| 0 <= g2 < x0.nkg implies
            (#[trigger] kg_key(x0, c, g2) == ekey(c, k as int)) == node_has(x0, c, g2, ab@, tb@, vb@) by {
            let k2 = x0.nodes@[g2].2 as int;
            assert(pre_ok(c, k2));
            lemma_sub_for(c, p_adsh(c, k as int));
            lemma_trip_key(c, k2, p_adsh(c, k as int), p_tag(c, k as int), p_ver(c, k as int));
        }
    }
    if g == NONE {
        let g0 = part.nkg;
        proof {
            lemma_top_bits(h, part.shift, (64 - part.shift) as u64);
            lemma_top_bits(h, part.fshift, (64 - part.fshift) as u64);
            reveal(kg_wf);
        }
        let b = (h >> part.shift) as usize;
        let f = (h >> part.fshift) as usize;
        let nw = part.filter.len();
        set_bit(&mut part.filter, f, Ghost(nw as int));
        let th = sig(tb, tl);
        let tnw = part.tfilter.len();
        proof {
            lemma_pow2_shift((64 - part.fshift) as u64);
            assert(part.tfilter@.len() == part.tfilter.len());
            assert(tnw * 64 >= 64);
        }
        let tmask = (tnw * 64 - 1) as u64;
        let tbi = (th & tmask) as usize;
        proof {
            assert(th & tmask <= tmask) by (bit_vector);
        }
        set_bit(&mut part.tfilter, tbi, Ghost(tnw as int));
        let al = part.alen;
        let acap = part.arena.len();
        let room = dl <= acap && tl <= acap - dl && vl <= acap - dl - tl && al <= acap - dl - tl - vl;
        let nd = if room {
            copy_into(&mut part.arena, al, ab, dl);
            let ghost a0 = part.arena@;
            copy_into(&mut part.arena, al + dl, tb, tl);
            let ghost a1 = part.arena@;
            copy_into(&mut part.arena, al + dl + tl, vb, vl);
            proof {
                assert(a1.subrange(al as int, al + dl) =~= a0.subrange(al as int, al + dl));
                assert(part.arena@.subrange(al as int, al + dl) =~= a1.subrange(al as int, al + dl));
                assert(part.arena@.subrange(al + dl, al + dl + tl) =~= a1.subrange(al + dl, al + dl + tl));
            }
            part.alen = al + dl + tl + vl;
            (h, s, k, true, al, dl, tl, vl)
        } else {
            (h, s, k, false, 0usize, 0usize, 0usize, 0usize)
        };
        part.nodes[g0] = nd;
        let hb = part.head[b];
        part.next[g0] = hb;
        part.head[b] = g0;
        let ne = part.nent;
        part.kof[ne] = g0;
        part.nkg = g0 + 1;
        part.nent = ne + 1;
        proof {
            lemma_kg_insert(x0, *part, c, pbits, p, ents, k, s, nd);
        }
    } else {
        let ne = part.nent;
        part.kof[ne] = g;
        part.nent = ne + 1;
        proof {
            lemma_kg_hit(x0, *part, c, pbits, p, ents, k, g);
        }
    }
}

pub struct BuildTask {
    pub p: usize,
    pub pbits: u64,
    pub pres: Arc<Vec<PreOut>>,
    pub bounds: Ghost<Seq<int>>,
    pub padsh: TextCol,
    pub ptag: TextCol,
    pub pver: TextCol,
    pub part: KgPart,
    pub ctx: Ghost<Ctx>,
}

impl WorkerTask for BuildTask {
    type Output = KgPart;

    open spec fn pre(&self) -> bool {
        let c = self.ctx@;
        &&& ctx_ok(c)
        &&& pres_ok((*self.pres)@, c, self.pbits, self.bounds@)
        &&& self.pbits <= MAX_PBITS
        &&& (self.p as int) < pow2u(self.pbits)
        &&& self.padsh@ == p_adsh_v(c)
        &&& self.ptag@ == p_tag_v(c)
        &&& self.pver@ == p_ver_v(c)
        &&& kg_shape(self.part)
        &&& plist(c, self.pbits, self.p as int, 0, c.q).len() <= self.part.next@.len()
        &&& plist(c, self.pbits, self.p as int, 0, c.q).len() <= self.part.nodes@.len()
        &&& plist(c, self.pbits, self.p as int, 0, c.q).len() <= self.part.kof@.len()
    }

    open spec fn post(&self, out: KgPart) -> bool {
        kg_wf(out, self.ctx@, self.pbits, self.p as int, plist(self.ctx@, self.pbits, self.p as int, 0, self.ctx@.q))
    }

    fn declared_rows(&self) -> (u64, u64) {
        (0, 0)
    }

    fn run(self) -> (out: KgPart) {
        let ghost c = self.ctx@;
        let ghost bounds = self.bounds@;
        let BuildTask { p, pbits, pres, bounds: _, padsh, ptag, pver, mut part, ctx } = self;
        kg_clear(&mut part);
        let pres: &Vec<PreOut> = &*pres;
        let ghost all = plist(c, pbits, p as int, 0, c.q);
        let ghost cap = all.len();
        proof {
            lemma_pres(pres@, c, pbits, bounds);
        }
        let nt = pres.len();
        let mut t: usize = 0;
        while t < nt
            invariant
                ctx_ok(c), pres_ok(pres@, c, pbits, bounds), nt == pres@.len(), t <= nt,
                pbits <= MAX_PBITS, padsh@ == p_adsh_v(c), ptag@ == p_tag_v(c), pver@ == p_ver_v(c),
                all == plist(c, pbits, p as int, 0, c.q), cap == all.len(),
                cap <= part.next@.len(), cap <= part.nodes@.len(), cap <= part.kof@.len(),
                kg_wf(part, c, pbits, p as int, plist(c, pbits, p as int, 0, bounds[t as int])),
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
                    ctx_ok(c), pres_ok(pres@, c, pbits, bounds), nt == pres@.len(), t < nt,
                    pbits <= MAX_PBITS, padsh@ == p_adsh_v(c), ptag@ == p_tag_v(c), pver@ == p_ver_v(c),
                    all == plist(c, pbits, p as int, 0, c.q), cap == all.len(),
                    cap <= part.next@.len(), cap <= part.nodes@.len(), cap <= part.kof@.len(),
                    o == &pres@[t as int], ol == o.len,
                    pre_out_ok(*o, c, pbits, bounds[t as int], bounds[t + 1]),
                    0 <= bounds[t as int] <= bounds[t + 1],
                    j <= ol,
                    kg_wf(part, c, pbits, p as int, pl(c, pbits, p as int, bounds, t as int, j as int)),
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
                    let h = o.ekh[j];
                    let ghost ents = pl(c, pbits, p as int, bounds, t as int, j as int);
                    proof {
                        lemma_pl_room(c, pbits, p as int, bounds, t as int, j as int, nt as int);
                    }
                    kg_take(&mut part, k, s, h, &padsh, &ptag, &pver, Ghost(c), Ghost(pbits), Ghost(p as int), Ghost(ents));
                }
                j = j + 1;
            }
            proof {
                lemma_pl_next(c, pbits, p as int, bounds, t as int);
            }
            t = t + 1;
        }
        part
    }
}

} // verus!
