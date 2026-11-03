//! P3: the pre entries, the selected pre rows (`nf::pre_sel`) in row order with their sub row and tag row
//! (`ents_ok`), and a chained index over them keyed by `mix((tag, version) hash, sub row)` (`ents_index_ok`).
//! A num row probes it with its own sub row, tag and version.
use vstd::prelude::*;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::agent::common::hash::*;
use crate::agent::common::chains::*;
use crate::agent::cols::*;
use crate::agent::nf::*;
use crate::agent::pre::*;
use crate::agent::tagres::*;

verus! {

/// The selected pre rows among `lo..hi`, in row order.
pub open spec fn sel_in(c: Ctx, lo: int, hi: int) -> Seq<int>
    decreases hi - lo,
{
    if hi <= lo {
        Seq::empty()
    } else {
        sel_in(c, lo, hi - 1) + if pre_sel(c, hi - 1) { seq![hi - 1] } else { Seq::<int>::empty() }
    }
}

/// The rows of `s` whose `(tag, version)` has a tag row.
pub open spec fn with_tag(c: Ctx, s: Seq<int>) -> Seq<int>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        with_tag(c, s.drop_last()) + if has_tag(c, p_tag(c, s.last()), p_ver(c, s.last())) { seq![s.last()] } else { Seq::<int>::empty() }
    }
}

/// The selected rows are the candidates with a tag row.
pub proof fn lemma_with_tag(c: Ctx, lo: int, hi: int)
    ensures with_tag(c, cands_in(c, lo, hi)) == sel_in(c, lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_with_tag(c, lo, hi - 1);
        let a = cands_in(c, lo, hi - 1);
        if pre_cand(c, hi - 1) {
            assert(cands_in(c, lo, hi) == a.push(hi - 1));
            assert(a.push(hi - 1).drop_last() =~= a);
        } else {
            assert(cands_in(c, lo, hi) =~= a);
        }
        assert(sel_in(c, lo, hi) =~= with_tag(c, cands_in(c, lo, hi)));
    } else {
        assert(cands_in(c, lo, hi) =~= Seq::<int>::empty());
    }
}

/// The selected rows among `lo..hi` are selected rows of that range, in increasing order.
pub proof fn lemma_sel_mem(c: Ctx, lo: int, hi: int, q: int)
    requires 0 <= q < sel_in(c, lo, hi).len(),
    ensures
        lo <= sel_in(c, lo, hi)[q] < hi, pre_sel(c, sel_in(c, lo, hi)[q]),
        forall|q2: int| 0 <= q2 < q ==> sel_in(c, lo, hi)[q2] < sel_in(c, lo, hi)[q],
    decreases hi - lo,
{
    let pre = sel_in(c, lo, hi - 1);
    if q < pre.len() {
        assert(sel_in(c, lo, hi)[q] == pre[q]);
        lemma_sel_mem(c, lo, hi - 1, q);
        assert forall|q2: int| 0 <= q2 < q implies sel_in(c, lo, hi)[q2] < sel_in(c, lo, hi)[q] by {
            assert(sel_in(c, lo, hi)[q2] == pre[q2]);
        }
    } else {
        assert(sel_in(c, lo, hi)[q] == hi - 1);
        assert forall|q2: int| 0 <= q2 < q implies sel_in(c, lo, hi)[q2] < sel_in(c, lo, hi)[q] by {
            assert(sel_in(c, lo, hi)[q2] == pre[q2]);
            lemma_sel_mem(c, lo, hi - 1, q2);
        }
    }
}

/// Every selected row of `lo..hi` is listed.
pub proof fn lemma_sel_complete(c: Ctx, lo: int, hi: int, l: int)
    requires lo <= l < hi, pre_sel(c, l),
    ensures sel_in(c, lo, hi).contains(l),
    decreases hi - lo,
{
    if l < hi - 1 {
        lemma_sel_complete(c, lo, hi - 1, l);
        let pre = sel_in(c, lo, hi - 1);
        let w = choose|w: int| 0 <= w < pre.len() && pre[w] == l;
        assert(sel_in(c, lo, hi)[w] == pre[w]);
    } else {
        assert(sel_in(c, lo, hi)[sel_in(c, lo, hi).len() - 1] == l);
    }
}

/// The probe key hash of pre row `l` with sub row `j`.
pub open spec fn key_hash(tvh: u64, j: usize) -> u64 {
    mix_spec(tvh, j as u64)
}

/// `list` is the selected pre rows with their sub rows and tag rows.
pub open spec fn ents_ok(c: Ctx, list: Seq<(usize, usize, usize)>) -> bool {
    let ss = sel_in(c, 0, c.npre);
    &&& list.len() == ss.len()
    &&& forall|e: int| 0 <= e < ss.len() ==> {
        let (l, j, k) = #[trigger] list[e];
        &&& l as int == ss[e]
        &&& sub_of(c, j as int, p_adsh(c, l as int))
        &&& tag_of(c, k as int, p_tag(c, l as int), p_ver(c, l as int))
    }
}

pub struct Entries {
    pub list: Vec<(usize, usize, usize)>,
    pub chains: Chains,
    pub p_tag: TextCol,
    pub p_ver: TextCol,
    pub t_tag: TextCol,
    pub t_ver: TextCol,
}

pub open spec fn ents_index_ok(x: &Entries, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& ents_ok(c, x.list@)
    &&& chains_wf(&x.chains)
    &&& x.chains.hashes@.len() == x.list@.len()
    &&& forall|e: int| 0 <= e < x.list@.len() ==>
        #[trigger] x.chains.hashes@[e] == key_hash(pre_tv_hash(c, x.list@[e].0 as int), x.list@[e].1)
    &&& x.p_tag@ == p_tag_v(c) && x.p_ver@ == p_ver_v(c)
    &&& text_wf(x.p_tag@, c.npre) && text_wf(x.p_ver@, c.npre)
    &&& x.t_tag@ == t_tag_v(c) && x.t_ver@ == t_ver_v(c)
    &&& text_wf(x.t_tag@, c.nt) && text_wf(x.t_ver@, c.nt)
}

/// The entries: the candidates with a tag row, and their index.
pub fn build_entries(cx: &Cands, tagrow: &Vec<usize>, t_tag: &TextCol, t_ver: &TextCol, Ghost(c): Ghost<Ctx>) -> (x: Entries)
    requires
        cands_index_ok(cx, c), tagrow_ok(cx, c, tagrow@), t_tag@ == t_tag_v(c), t_ver@ == t_ver_v(c),
        text_wf(t_tag@, c.nt), text_wf(t_ver@, c.nt),
    ensures ents_index_ok(&x, c),
{
    let n = cx.list.len();
    let ghost cs = cands_in(c, 0, c.npre);
    let mut list: Vec<(usize, usize, usize)> = Vec::new();
    let mut hs: Vec<u64> = Vec::new();
    let mut q: usize = 0;
    proof {
        assert(cs.take(0) =~= Seq::<int>::empty());
    }
    while q < n
        invariant
            cands_index_ok(cx, c), tagrow_ok(cx, c, tagrow@), n == cx.list@.len(), q <= n, cs == cands_in(c, 0, c.npre),
            list@.len() == hs@.len(), list@.len() <= q,
            list@.len() == with_tag(c, cs.take(q as int)).len(),
            forall|e: int| 0 <= e < list@.len() ==> {
                let (l, j, k) = #[trigger] list@[e];
                &&& l as int == with_tag(c, cs.take(q as int))[e]
                &&& sub_of(c, j as int, p_adsh(c, l as int))
                &&& tag_of(c, k as int, p_tag(c, l as int), p_ver(c, l as int))
                &&& hs@[e] == key_hash(pre_tv_hash(c, l as int), j)
            },
        decreases n - q,
    {
        let (l, j, h) = cx.list[q];
        let k = tagrow[q];
        proof {
            assert(l as int == cs[q as int]);
            assert(cs.take(q + 1) =~= cs.take(q as int).push(cs[q as int]));
            assert(cs.take(q + 1).drop_last() =~= cs.take(q as int));
        }
        let ghost w0 = with_tag(c, cs.take(q as int));
        if k != NONE {
            let kh = mix(h, j as u64);
            list.push((l, j, k));
            hs.push(kh);
            proof {
                assert(with_tag(c, cs.take(q + 1)) == w0.push(l as int));
                assert forall|e: int| 0 <= e < list@.len() implies {
                    let (l2, j2, k2) = #[trigger] list@[e];
                    &&& l2 as int == with_tag(c, cs.take(q + 1))[e]
                    &&& sub_of(c, j2 as int, p_adsh(c, l2 as int))
                    &&& tag_of(c, k2 as int, p_tag(c, l2 as int), p_ver(c, l2 as int))
                    &&& hs@[e] == key_hash(pre_tv_hash(c, l2 as int), j2)
                } by {
                    if e < list@.len() - 1 {
                        assert(with_tag(c, cs.take(q + 1))[e] == w0[e]);
                    }
                }
            }
        } else {
            proof {
                assert(with_tag(c, cs.take(q + 1)) == w0);
            }
        }
        q = q + 1;
    }
    proof {
        assert(cs.take(n as int) =~= cs);
        lemma_with_tag(c, 0, c.npre);
        lemma_views(c);
        lemma_cands_bound2(c);
    }
    let chains = build_chains(hs);
    Entries { list, chains, p_tag: tc(&cx.p_tag), p_ver: tc(&cx.p_ver), t_tag: tc(t_tag), t_ver: tc(t_ver) }
}

/// At most `npre` rows are selected (and `npre < usize::MAX`, from the candidate index's text columns).
proof fn lemma_cands_bound2(c: Ctx)
    ensures sel_in(c, 0, c.npre).len() <= if c.npre < 0 { 0 } else { c.npre },
{
    lemma_sel_bound(c, 0, c.npre);
}

proof fn lemma_sel_bound(c: Ctx, lo: int, hi: int)
    ensures sel_in(c, lo, hi).len() <= if hi < lo { 0 } else { hi - lo },
    decreases hi - lo,
{
    if hi > lo {
        lemma_sel_bound(c, lo, hi - 1);
    }
}

} // verus!
