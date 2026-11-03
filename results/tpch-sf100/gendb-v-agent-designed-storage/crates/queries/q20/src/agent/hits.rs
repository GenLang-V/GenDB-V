//! The matching part rows as one virtual list (`src_of`) that the calling thread cuts into the tasks' lists
//! (`chunk`): in fast mode the rows at the positions of the two name-order ranges (`fast_src`, read straight from the
//! name order when a task's list is built), in general mode the list of rows whose LIKE is true (`hits_flags`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::stores::part_nameidx::interface as pi;
use super::nf::*;
use super::pfind::*;
use super::bits::*;
use super::common::bitlist::{wbit, set_bits_list};

verus! {

/// The list `l` holds exactly the matching part rows.
pub open spec fn hits_ok(l: Seq<usize>, pp: Seq<PartView>, pat: Seq<u8>) -> bool {
    &&& forall|i: int| 0 <= i < l.len() ==> (#[trigger] l[i]) < pi::n_rows(pp) && hit_row(pp, pat, l[i] as int)
    &&& forall|r: int| 0 <= r < pi::n_rows(pp) && #[trigger] hit_row(pp, pat, r) ==> exists|i: int| 0 <= i < l.len() && l[i] == r
}

/// Name-order position of entry `i` of the two ranges `[a1, b1)` then `[a2, ..)`.
pub open spec fn pos_of(a1: int, b1: int, a2: int, i: int) -> int {
    if i < b1 - a1 { a1 + i } else { a2 + (i - (b1 - a1)) }
}

/// The rows at the positions of the two ranges.
pub open spec fn fast_src(perm: Seq<u32>, a1: int, b1: int, a2: int, b2: int) -> Seq<usize> {
    Seq::new(((b1 - a1) + (b2 - a2)) as nat, |i: int| perm[pos_of(a1, b1, a2, i)] as usize)
}

/// The matching part rows, in one of two forms.
pub struct Hits {
    pub fast: bool,
    pub a1: usize,
    pub b1: usize,
    pub a2: usize,
    pub b2: usize,
    pub len: usize,
    pub hl: Vec<usize>,
}

/// The virtual list of `h`.
pub open spec fn src_of(h: &Hits, perm: Seq<u32>) -> Seq<usize> {
    if h.fast { fast_src(perm, h.a1 as int, h.b1 as int, h.a2 as int, h.b2 as int) } else { h.hl@ }
}

/// The shape of `h` over the name order `perm`.
pub open spec fn hits_wf(h: &Hits, perm: Seq<u32>) -> bool {
    &&& h.len == src_of(h, perm).len()
    &&& h.fast ==> h.a1 <= h.b1 <= perm.len() && h.a2 <= h.b2 <= perm.len()
}

/// Fast mode: the positions of the two ranges hold exactly the matching rows.
pub proof fn lemma_fast_src(pp: Seq<PartView>, pat: Seq<u8>, perm: Seq<u32>, a1: int, b1: int, a2: int, b2: int)
    requires
        super::bind_pl::pp_ok(pp),
        pi::has_perm(pp), perm == pi::perm(pp),
        0 <= a1 <= b1 <= pi::n_rows(pp), 0 <= a2 <= b2 <= pi::n_rows(pp),
        forall|p: int| 0 <= p < pi::n_rows(pp) ==> in_ranges(a1, b1, a2, b2, p) == #[trigger] like_hit(name_pos(pp, p), pat),
    ensures hits_ok(fast_src(perm, a1, b1, a2, b2), pp, pat),
{
    let n = pi::n_rows(pp);
    let l = fast_src(perm, a1, b1, a2, b2);
    let m1 = b1 - a1;
    assert forall|i: int| 0 <= i < l.len() implies (#[trigger] l[i]) < pi::n_rows(pp) && hit_row(pp, pat, l[i] as int) by {
        let p = pos_of(a1, b1, a2, i);
        assert(l[i] == perm[p] as usize);
        assert(pi::perm(pp)[p] < n);
        assert(in_ranges(a1, b1, a2, b2, p));
        assert(like_hit(name_pos(pp, p), pat));
    }
    assert forall|r: int| 0 <= r < pi::n_rows(pp) && #[trigger] hit_row(pp, pat, r)
        implies exists|i: int| 0 <= i < l.len() && l[i] == r by {
        assert(pi::listed(pp, n, r));
        let p = choose|p: int| 0 <= p < n && #[trigger] pi::perm(pp)[p] == r;
        assert(name_pos(pp, p) == pi::name_at(pp, r));
        assert(like_hit(name_pos(pp, p), pat));
        assert(in_ranges(a1, b1, a2, b2, p));
        if a1 <= p < b1 {
            assert(pos_of(a1, b1, a2, p - a1) == p);
            assert(l[p - a1] == r);
        } else {
            assert(pos_of(a1, b1, a2, m1 + (p - a2)) == p);
            assert(l[m1 + (p - a2)] == r);
        }
    }
}

/// Append the rows listed at name-order positions `[a, b)`.
fn push_range(l: &mut Vec<usize>, perm: &[u32], a: usize, b: usize)
    requires a <= b <= perm@.len(),
    ensures final(l)@ == old(l)@ + Seq::new((b - a) as nat, |i: int| perm@[a + i] as usize),
{
    let ghost l0 = l@;
    let mut p = a;
    while p < b
        invariant a <= p <= b <= perm@.len(), l@ == l0 + Seq::new((p - a) as nat, |i: int| perm@[a + i] as usize),
        decreases b - p,
    {
        l.push(perm[p] as usize);
        proof {
            assert(l@ =~= l0 + Seq::new((p + 1 - a) as nat, |i: int| perm@[a + i] as usize));
        }
        p = p + 1;
    }
}

/// Entries `[q0, q1)` of the virtual list.
pub fn chunk(h: &Hits, perm: &[u32], q0: usize, q1: usize) -> (r: Vec<usize>)
    requires hits_wf(h, perm@), q0 <= q1 <= h.len,
    ensures r@ == src_of(h, perm@).subrange(q0 as int, q1 as int),
{
    if h.fast {
        let l1 = h.b1 - h.a1;
        let mut r: Vec<usize> = Vec::with_capacity(q1 - q0);
        let s1 = if q0 < l1 { q0 } else { l1 };
        let e1 = if q1 < l1 { q1 } else { l1 };
        push_range(&mut r, perm, h.a1 + s1, h.a1 + e1);
        let s2 = if q0 > l1 { q0 } else { l1 };
        let e2 = if q1 > l1 { q1 } else { l1 };
        push_range(&mut r, perm, h.a2 + (s2 - l1), h.a2 + (e2 - l1));
        proof {
            let src = src_of(h, perm@);
            assert forall|i: int| 0 <= i < q1 - q0 implies #[trigger] r@[i] == src.subrange(q0 as int, q1 as int)[i] by {
                let k = q0 + i;
                if k < l1 {
                    assert(r@[i] == perm@[h.a1 + s1 + i] as usize);
                } else {
                    assert(r@[i] == perm@[h.a2 + (s2 - l1) + (i - (e1 - s1))] as usize);
                }
            }
            assert(r@ =~= src.subrange(q0 as int, q1 as int));
        }
        r
    } else {
        let mut r: Vec<usize> = Vec::with_capacity(q1 - q0);
        let (_, t) = h.hl.as_slice().split_at(q0);
        let (m, _) = t.split_at(q1 - q0);
        r.extend_from_slice(m);
        proof {
            assert(r@ =~= h.hl@.subrange(q0 as int, q1 as int));
        }
        r
    }
}

/// Fast mode in row order: the rows of the two name-order ranges, marked in a bit set over the part rows, then
/// listed in increasing row order (so the tasks read partsupp and the lineitem index forward).
pub fn sorted_fast(perm: &[u32], a1: usize, b1: usize, a2: usize, b2: usize, np: usize,
    Ghost(pp): Ghost<Seq<PartView>>, Ghost(pat): Ghost<Seq<u8>>) -> (l: Vec<usize>)
    requires
        np == pi::n_rows(pp), np + 64 <= usize::MAX,
        a1 <= b1 <= perm@.len(), a2 <= b2 <= perm@.len(), (b1 - a1) + (b2 - a2) <= usize::MAX,
        hits_ok(fast_src(perm@, a1 as int, b1 as int, a2 as int, b2 as int), pp, pat),
    ensures hits_ok(l@, pp, pat),
{
    let ghost src = fast_src(perm@, a1 as int, b1 as int, a2 as int, b2 as int);
    let nw = np / 64 + 1;
    let mut g: Vec<u64> = vec![0u64; nw];
    proof {
        lemma_zero_bits(g@, (nw * 64) as int);
    }
    let l1 = b1 - a1;
    let len = l1 + (b2 - a2);
    let mut i: usize = 0;
    while i < len
        invariant
            np == pi::n_rows(pp), nw == np / 64 + 1, g@.len() == nw,
            a1 <= b1 <= perm@.len(), a2 <= b2 <= perm@.len(), l1 == b1 - a1, len == l1 + (b2 - a2),
            src == fast_src(perm@, a1 as int, b1 as int, a2 as int, b2 as int),
            hits_ok(src, pp, pat),
            i <= len,
            forall|y: int| 0 <= y < nw * 64 ==> #[trigger] bit(g@, y) == exists|t: int| 0 <= t < i && src[t] == y,
        decreases len - i,
    {
        let r = if i < l1 { perm[a1 + i] as usize } else { perm[a2 + (i - l1)] as usize };
        proof {
            assert(src[i as int] == perm@[pos_of(a1 as int, b1 as int, a2 as int, i as int)] as usize);
            assert(r == src[i as int]);
            assert(r < np);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(r as int, np as int, 64);
        }
        let ghost g0 = g@;
        set_bit(&mut g, r);
        proof {
            assert forall|y: int| 0 <= y < nw * 64 implies #[trigger] bit(g@, y) == exists|t: int| 0 <= t < i + 1 && src[t] == y by {
                if bit(g0, y) {
                    let t = choose|t: int| 0 <= t < i && src[t] == y;
                }
                if y != r && (exists|t: int| 0 <= t < i + 1 && src[t] == y) {
                    let t = choose|t: int| 0 <= t < i + 1 && src[t] == y;
                    assert(t < i);
                }
            }
        }
        i = i + 1;
    }
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(np as int, 64);
    }
    let l = set_bits_list(&g, np, len);
    proof {
        assert forall|k: int| 0 <= k < l@.len() implies (#[trigger] l@[k]) < pi::n_rows(pp) && hit_row(pp, pat, l@[k] as int) by {
            assert(wbit(g@, l@[k] as int));
            assert(bit(g@, l@[k] as int));
            let t = choose|t: int| 0 <= t < len && src[t] == l@[k];
        }
        assert forall|r: int| 0 <= r < pi::n_rows(pp) && #[trigger] hit_row(pp, pat, r)
            implies exists|k: int| 0 <= k < l@.len() && l@[k] == r by {
            let t = choose|t: int| 0 <= t < src.len() && src[t] == r;
            assert(bit(g@, r));
            assert(wbit(g@, r));
        }
    }
    l
}

/// General mode: the rows whose flag is set.
pub fn hits_flags(g: &Vec<u8>, np: usize, Ghost(pp): Ghost<Seq<PartView>>, Ghost(pat): Ghost<Seq<u8>>) -> (l: Vec<usize>)
    requires
        np == pi::n_rows(pp), g@.len() == np,
        forall|q: int| 0 <= q < np ==> (#[trigger] g@[q] != 0) == hit_row(pp, pat, q),
    ensures hits_ok(l@, pp, pat),
{
    let mut l: Vec<usize> = Vec::new();
    let mut r: usize = 0;
    while r < np
        invariant
            r <= np, np == pi::n_rows(pp), g@.len() == np,
            forall|q: int| 0 <= q < np ==> (#[trigger] g@[q] != 0) == hit_row(pp, pat, q),
            forall|i: int| 0 <= i < l@.len() ==> (#[trigger] l@[i]) < r && hit_row(pp, pat, l@[i] as int),
            forall|q: int| 0 <= q < r && #[trigger] hit_row(pp, pat, q) ==> exists|i: int| 0 <= i < l@.len() && l@[i] == q,
        decreases np - r,
    {
        let ghost l0 = l@;
        if g[r] != 0 {
            l.push(r);
        }
        proof {
            assert forall|q: int| 0 <= q < r + 1 && #[trigger] hit_row(pp, pat, q)
                implies exists|i: int| 0 <= i < l@.len() && l@[i] == q by {
                if q < r {
                    let i = choose|i: int| 0 <= i < l0.len() && l0[i] == q;
                    assert(l@[i] == q);
                } else {
                    assert(l@[l0.len() as int] == q);
                }
            }
            assert forall|i: int| 0 <= i < l@.len() implies (#[trigger] l@[i]) < r + 1 && hit_row(pp, pat, l@[i] as int) by {
                if i < l0.len() {
                    assert(l@[i] == l0[i]);
                }
            }
        }
        r = r + 1;
    }
    l
}

} // verus!
