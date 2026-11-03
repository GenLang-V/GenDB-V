//! The present groups in ORDER BY order (count descending, then rank code) without a comparison sort.
//!
//! 1. `rank_inverse`: the table `rinv` from rank codes back to group ids (`rc_of` is injective on the group ids);
//! 2. `rank_entries`: the present groups in rank-code order, each as an entry with key `maxc - count` and value the
//!    group id (`cent_ok`, `ents_ok`);
//! 3. `common::key_group::group_by_key` groups the entries by key, stably: segment `k` lists the groups of count
//!    `maxc - k` in rank-code order, and the segments follow each other by decreasing count.
//! The result (`og_ok`): every present group exactly once, in strictly ascending sort key (`output::skey`) order.
//! Counting needs `maxc + 1` counters, so counts of `2^20` or more are left to the comparison sort (`None`).
use vstd::prelude::*;
use crate::agent::output::*;
use crate::agent::common::ranks::*;
use crate::agent::common::key_group::*;

verus! {

/// The present groups, each once, in strictly ascending sort key order.
pub open spec fn og_ok(cnt: Seq<u64>, rb: Seq<usize>, rt: Seq<usize>, rs: Seq<usize>, nt: int, ns: int, og: Seq<u32>) -> bool {
    &&& og.len() <= cnt.len()
    &&& forall|x: int| 0 <= x < og.len() ==> #[trigger] present(cnt, og[x] as int)
    &&& forall|x: int, y: int| 0 <= x < y < og.len()
        ==> skey(cnt, rb, rt, rs, nt, ns, #[trigger] og[x] as int) < skey(cnt, rb, rt, rs, nt, ns, #[trigger] og[y] as int)
    &&& forall|g: int| #[trigger] present(cnt, g) ==> og.contains(g as u32)
}

/// Entry `e`: its value is a present group and its key is `maxc` minus the group's count.
pub open spec fn cent_ok(cnt: Seq<u64>, maxc: u64, e: u64) -> bool {
    let g = evalue(e) as int;
    &&& present(cnt, g)
    &&& ekey(e, 0) == maxc - cnt[g]
}

/// The entries `es` are the present groups of rank code below `r`, in increasing rank-code order.
pub open spec fn ents_ok(cnt: Seq<u64>, rb: Seq<usize>, rt: Seq<usize>, rs: Seq<usize>, nt: int, ns: int, maxc: u64,
    es: Seq<u64>, r: int) -> bool {
    &&& es.len() <= r
    &&& forall|i: int| 0 <= i < es.len() ==> #[trigger] cent_ok(cnt, maxc, es[i])
    &&& forall|i: int, j: int| 0 <= i < j < es.len()
        ==> rc_of(rb, rt, rs, nt, ns, evalue(#[trigger] es[i]) as int) < rc_of(rb, rt, rs, nt, ns, evalue(#[trigger] es[j]) as int)
    &&& forall|h: int| #[trigger] present(cnt, h) && rc_of(rb, rt, rs, nt, ns, h) < r
        ==> exists|i: int| 0 <= i < es.len() && evalue(#[trigger] es[i]) as int == h
}

/// Two groups with a larger count, or the same count and a smaller rank code, have a smaller sort key.
proof fn lemma_skey_lt(cnt: Seq<u64>, rb: Seq<usize>, rt: Seq<usize>, rs: Seq<usize>, nt: int, ns: int, g1: int, g2: int)
    requires
        0 <= g1 < cnt.len(), 0 <= g2 < cnt.len(), cnt[g1] < 0xFFFF_FFFF, cnt[g2] < 0xFFFF_FFFF,
        0 <= rc_of(rb, rt, rs, nt, ns, g1) < 0x1_0000_0000, 0 <= rc_of(rb, rt, rs, nt, ns, g2) < 0x1_0000_0000,
        cnt[g1] > cnt[g2] || (cnt[g1] == cnt[g2] && rc_of(rb, rt, rs, nt, ns, g1) < rc_of(rb, rt, rs, nt, ns, g2)),
    ensures skey(cnt, rb, rt, rs, nt, ns, g1) < skey(cnt, rb, rt, rs, nt, ns, g2),
{
    lemma_pack((0xFFFF_FFFFu64 - cnt[g1]) as u64, rc_of(rb, rt, rs, nt, ns, g1) as u64);
    lemma_pack((0xFFFF_FFFFu64 - cnt[g2]) as u64, rc_of(rb, rt, rs, nt, ns, g2) as u64);
}

/// The rank code of group `g` (`rc_of`).
fn rc_exec(cnt: &Vec<u64>, rb: &Vec<usize>, rt: &Vec<usize>, rs: &Vec<usize>, nt: usize, ns: usize, ntns: usize, g: usize,
    Ghost(kb): Ghost<Seq<Seq<u8>>>, Ghost(kt): Ghost<Seq<Seq<u8>>>, Ghost(szl): Ghost<Seq<i64>>) -> (r: usize)
    requires
        tables_ok(kb, kt, szl, cnt@), ranks_ok(kb, kt, szl, rb@, rt@, rs@), nt == kt.len(), ns == szl.len(),
        ntns == nt * ns, g < cnt@.len(),
    ensures r as int == rc_of(rb@, rt@, rs@, nt as int, ns as int, g as int), r < cnt@.len(),
{
    let ghost (crb, crt, crs) = (rb@, rt@, rs@);
    let ghost c = cnt@.len() as int;
    proof {
        lemma_decode(g as int, kb.len() as int, nt as int, ns as int);
        lemma_rc(kb, kt, szl, cnt@, crb, crt, crs, g as int, g as int);
        let (nbi, nti, nsi) = (kb.len() as int, nt as int, ns as int);
        assert(nti * nsi >= 1) by (nonlinear_arith) requires nti >= 1, nsi >= 1;
    }
    let bi = g / ntns;
    let ti = (g / ns) % nt;
    let si = g % ns;
    proof {
        assert(bi as int == bi_of(g as int, nt as int, ns as int));
        lemma_text_ranks(kb, bi as int, bi as int);
        lemma_text_ranks(kt, ti as int, ti as int);
        lemma_int_ranks(szl, si as int, si as int);
        lemma_compose(crb[bi as int] as int, crt[ti as int] as int, crs[si as int] as int, kb.len() as int, nt as int, ns as int);
        let (x, y, z, nbi) = (crb[bi as int] as int, crt[ti as int] as int, crs[si as int] as int, kb.len() as int);
        assert(x * nt <= x * nt + y < nbi * nt && nbi * nt <= c && (x * nt + y) * ns <= (x * nt + y) * ns + z) by (nonlinear_arith)
            requires 0 <= x < nbi, 0 <= y < nt, 0 <= z < ns, c == nbi * nt * ns, ns >= 1, nt >= 1;
    }
    (rb[bi] * nt + rt[ti]) * ns + rs[si]
}

/// The table from rank codes back to group ids: `rinv[rc_of(h)] == h` for every group `h`; every entry is a group id.
fn rank_inverse(cnt: &Vec<u64>, rb: &Vec<usize>, rt: &Vec<usize>, rs: &Vec<usize>, nt: usize, ns: usize, ntns: usize,
    Ghost(kb): Ghost<Seq<Seq<u8>>>, Ghost(kt): Ghost<Seq<Seq<u8>>>, Ghost(szl): Ghost<Seq<i64>>) -> (rinv: Vec<u32>)
    requires
        tables_ok(kb, kt, szl, cnt@), ranks_ok(kb, kt, szl, rb@, rt@, rs@), nt == kt.len(), ns == szl.len(),
        ntns == nt * ns,
    ensures
        rinv@.len() == cnt@.len(),
        forall|r: int| 0 <= r < rinv@.len() ==> (#[trigger] rinv@[r]) < cnt@.len(),
        forall|h: int| 0 <= h < cnt@.len() ==> rinv@[rc_of(rb@, rt@, rs@, nt as int, ns as int, h)] as int == h,
{
    let ghost (crb, crt, crs) = (rb@, rt@, rs@);
    let ghost (nti, nsi) = (nt as int, ns as int);
    let c = cnt.len();
    proof {
        let (nbi, nti, nsi) = (kb.len() as int, kt.len() as int, szl.len() as int);
        assert(c >= 1) by (nonlinear_arith) requires c == nbi * nti * nsi, nbi >= 1, nti >= 1, nsi >= 1;
    }
    let mut rinv: Vec<u32> = vec![0u32; c];
    let mut g: usize = 0;
    while g < c
        invariant
            tables_ok(kb, kt, szl, cnt@), ranks_ok(kb, kt, szl, crb, crt, crs), crb == rb@, crt == rt@, crs == rs@,
            nt == kt.len(), ns == szl.len(), nti == nt as int, nsi == ns as int, ntns == nt * ns,
            c == cnt@.len(), c >= 1, c <= 0x400_0000, g <= c, rinv@.len() == c,
            forall|r: int| 0 <= r < c ==> (#[trigger] rinv@[r]) < c,
            forall|h: int| 0 <= h < g ==> rinv@[rc_of(crb, crt, crs, nti, nsi, h)] as int == h,
        decreases c - g,
    {
        let rcv = rc_exec(cnt, rb, rt, rs, nt, ns, ntns, g, Ghost(kb), Ghost(kt), Ghost(szl));
        let ghost r0 = rinv@;
        rinv[rcv] = g as u32;
        proof {
            assert forall|h: int| 0 <= h < g + 1 implies rinv@[rc_of(crb, crt, crs, nti, nsi, h)] as int == h by {
                lemma_rc(kb, kt, szl, cnt@, crb, crt, crs, h, g as int);
                if h < g {
                    assert(rc_of(crb, crt, crs, nti, nsi, h) != rc_of(crb, crt, crs, nti, nsi, g as int));
                }
            }
            assert forall|r: int| 0 <= r < c implies (#[trigger] rinv@[r]) < c by {
                if r != rcv as int { assert(rinv@[r] == r0[r]); }
            }
        }
        g = g + 1;
    }
    rinv
}

/// The present groups in rank-code order as entries `(maxc - count) << 32 | group`.
fn rank_entries(cnt: &Vec<u64>, rb: &Vec<usize>, rt: &Vec<usize>, rs: &Vec<usize>, nt: usize, ns: usize, ntns: usize,
    rinv: &Vec<u32>, maxc: u64, Ghost(kb): Ghost<Seq<Seq<u8>>>, Ghost(kt): Ghost<Seq<Seq<u8>>>, Ghost(szl): Ghost<Seq<i64>>)
    -> (ent: Vec<u64>)
    requires
        tables_ok(kb, kt, szl, cnt@), ranks_ok(kb, kt, szl, rb@, rt@, rs@), nt == kt.len(), ns == szl.len(),
        ntns == nt * ns, rinv@.len() == cnt@.len(),
        forall|r: int| 0 <= r < rinv@.len() ==> (#[trigger] rinv@[r]) < cnt@.len(),
        forall|h: int| 0 <= h < cnt@.len() ==> rinv@[rc_of(rb@, rt@, rs@, nt as int, ns as int, h)] as int == h,
        maxc < 0x10_0000, forall|h: int| 0 <= h < cnt@.len() ==> #[trigger] cnt@[h] <= maxc,
    ensures ents_ok(cnt@, rb@, rt@, rs@, nt as int, ns as int, maxc, ent@, cnt@.len() as int),
{
    let ghost (crb, crt, crs) = (rb@, rt@, rs@);
    let ghost (nti, nsi) = (nt as int, ns as int);
    let c = cnt.len();
    let mut ent: Vec<u64> = Vec::new();
    let mut r: usize = 0;
    while r < c
        invariant
            tables_ok(kb, kt, szl, cnt@), ranks_ok(kb, kt, szl, crb, crt, crs), crb == rb@, crt == rt@, crs == rs@,
            nt == kt.len(), ns == szl.len(), nti == nt as int, nsi == ns as int, ntns == nt * ns,
            c == cnt@.len(), r <= c, rinv@.len() == c,
            forall|q: int| 0 <= q < c ==> (#[trigger] rinv@[q]) < c,
            forall|h: int| 0 <= h < c ==> rinv@[rc_of(crb, crt, crs, nti, nsi, h)] as int == h,
            maxc < 0x10_0000, forall|h: int| 0 <= h < c ==> #[trigger] cnt@[h] <= maxc,
            ents_ok(cnt@, crb, crt, crs, nti, nsi, maxc, ent@, r as int),
            forall|i: int| 0 <= i < ent@.len() ==> rc_of(crb, crt, crs, nti, nsi, evalue(#[trigger] ent@[i]) as int) < r,
        decreases c - r,
    {
        let g = rinv[r] as usize;
        let rcv = rc_exec(cnt, rb, rt, rs, nt, ns, ntns, g, Ghost(kb), Ghost(kt), Ghost(szl));
        let ghost e0 = ent@;
        if rcv == r && cnt[g] > 0 {
            let hi = maxc - cnt[g];
            let e = (hi << 32u64) | (g as u64);
            proof {
                lemma_pack(hi, g as u64);
            }
            ent.push(e);
            proof {
                assert(ent@[ent@.len() - 1] == e);
                assert(evalue(e) as int == g as int && ekey(e, 0) == hi as int);
                assert forall|i: int| 0 <= i < ent@.len() implies #[trigger] cent_ok(cnt@, maxc, ent@[i]) by {
                    if i < e0.len() { assert(ent@[i] == e0[i]); }
                }
                assert forall|i: int| 0 <= i < ent@.len() implies rc_of(crb, crt, crs, nti, nsi, evalue(#[trigger] ent@[i]) as int) < r + 1 by {
                    if i < e0.len() { assert(ent@[i] == e0[i]); }
                }
                assert forall|i: int, j: int| 0 <= i < j < ent@.len() implies rc_of(crb, crt, crs, nti, nsi, evalue(#[trigger] ent@[i]) as int)
                    < rc_of(crb, crt, crs, nti, nsi, evalue(#[trigger] ent@[j]) as int) by {
                    assert(ent@[i] == e0[i]);
                    if j < e0.len() { assert(ent@[j] == e0[j]); }
                }
            }
        }
        proof {
            // Every present group of rank code at most `r` has an entry: those below `r` already had one, and the
            // group of rank code `r` is `rinv[r]`, which the branch above added when present.
            assert forall|h: int| #[trigger] present(cnt@, h) && rc_of(crb, crt, crs, nti, nsi, h) < r + 1
                implies exists|i: int| 0 <= i < ent@.len() && evalue(#[trigger] ent@[i]) as int == h by {
                if rc_of(crb, crt, crs, nti, nsi, h) < r {
                    let i = choose|i: int| 0 <= i < e0.len() && evalue(#[trigger] e0[i]) as int == h;
                    assert(ent@[i] == e0[i]);
                } else {
                    assert(rinv@[rc_of(crb, crt, crs, nti, nsi, h)] as int == h);
                    assert(g as int == h);
                    assert(evalue(ent@[ent@.len() - 1]) as int == h);
                }
            }
        }
        r = r + 1;
    }
    ent
}

/// Position `x` of segment `k` of the grouped values is position `x - kstart(k)` of `kvals(k)`.
proof fn lemma_og_at(es: Seq<u64>, og: Seq<u32>, ng: int, k: int, x: int)
    requires
        0 <= k < ng, kstart(es, 0, k) <= x < kstart(es, 0, k) + kcount(es, 0, k),
        kstart(es, 0, ng) == og.len(),
        forall|j: int| 0 <= j < ng ==> #[trigger] og.subrange(kstart(es, 0, j) as int, kstart(es, 0, j + 1) as int) == kvals(es, 0, j),
    ensures
        0 <= x < og.len(), 0 <= x - kstart(es, 0, k) < kvals(es, 0, k).len(), og[x] == kvals(es, 0, k)[x - kstart(es, 0, k)],
{
    lemma_kvals_len(es, 0, k);
    lemma_segment_end(es, 0, k, ng);
    assert(kstart(es, 0, k + 1) == kstart(es, 0, k) + kcount(es, 0, k));
    let seg = og.subrange(kstart(es, 0, k) as int, kstart(es, 0, k + 1) as int);
    assert(seg == kvals(es, 0, k));
    assert(seg[x - kstart(es, 0, k)] == og[x]);
}

/// The grouped values: the facts of `group_by_key` over the entries.
pub open spec fn grouped(es: Seq<u64>, og: Seq<u32>, ng: int) -> bool {
    &&& kstart(es, 0, ng) == og.len()
    &&& forall|j: int| 0 <= j < ng ==> #[trigger] og.subrange(kstart(es, 0, j) as int, kstart(es, 0, j + 1) as int) == kvals(es, 0, j)
}

/// Value `x` of the grouped values comes from an entry with the key of its segment.
proof fn lemma_og_src(es: Seq<u64>, og: Seq<u32>, ng: int, x: int) -> (r: (int, int))
    requires grouped(es, og, ng), 0 <= x < og.len(), ng >= 0,
    ensures 0 <= r.0 < ng, kstart(es, 0, r.0) <= x < kstart(es, 0, r.0) + kcount(es, 0, r.0),
        0 <= r.1 < es.len(), ekey(es[r.1], 0) == r.0, evalue(es[r.1]) == og[x],
{
    lemma_segment_of(es, 0, ng, x);
    let k = choose|k: int| 0 <= k < ng && #[trigger] kstart(es, 0, k) <= x < kstart(es, 0, k) + kcount(es, 0, k);
    lemma_og_at(es, og, ng, k, x);
    lemma_kvals_src(es, 0, k, x - kstart(es, 0, k));
    let i = choose|i: int| 0 <= i < es.len() && ekey(es[i], 0) == k && #[trigger] evalue(es[i]) == kvals(es, 0, k)[x - kstart(es, 0, k)];
    (k, i)
}

/// The grouped values of the rank-ordered entries are the present groups in strictly ascending sort key order.
proof fn lemma_order_result(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, cnt: Seq<u64>, rb: Seq<usize>,
    rt: Seq<usize>, rs: Seq<usize>, maxc: u64, es: Seq<u64>, og: Seq<u32>, ng: int)
    requires
        tables_ok(kb, kt, szl, cnt), ranks_ok(kb, kt, szl, rb, rt, rs),
        ents_ok(cnt, rb, rt, rs, kt.len() as int, szl.len() as int, maxc, es, cnt.len() as int),
        ng == maxc + 1, grouped(es, og, ng),
    ensures og_ok(cnt, rb, rt, rs, kt.len() as int, szl.len() as int, og),
{
    let (nt, ns) = (kt.len() as int, szl.len() as int);
    assert forall|i: int| 0 <= i < es.len() implies 0 <= #[trigger] ekey(es[i], 0) < ng by {
        assert(cent_ok(cnt, maxc, es[i]));
    }
    lemma_total_len(es, ng);
    assert forall|x: int| 0 <= x < og.len() implies #[trigger] present(cnt, og[x] as int) by {
        let (k, i) = lemma_og_src(es, og, ng, x);
        assert(cent_ok(cnt, maxc, es[i]));
    }
    assert forall|x: int, y: int| 0 <= x < y < og.len()
        implies skey(cnt, rb, rt, rs, nt, ns, #[trigger] og[x] as int) < skey(cnt, rb, rt, rs, nt, ns, #[trigger] og[y] as int) by {
        let (kx, i) = lemma_og_src(es, og, ng, x);
        let (ky, j) = lemma_og_src(es, og, ng, y);
        lemma_segment_order(es, 0, kx, ky, x, y);
        assert(cent_ok(cnt, maxc, es[i]) && cent_ok(cnt, maxc, es[j]));
        let (gx, gy) = (og[x] as int, og[y] as int);
        lemma_rc(kb, kt, szl, cnt, rb, rt, rs, gx, gy);
        lemma_rc(kb, kt, szl, cnt, rb, rt, rs, gy, gx);
        if kx == ky {
            lemma_og_at(es, og, ng, kx, x);
            lemma_og_at(es, og, ng, kx, y);
            lemma_kvals_increasing(es, 0, kx, |v: u32| rc_of(rb, rt, rs, nt, ns, v as int));
            let (px, py) = (x - kstart(es, 0, kx), y - kstart(es, 0, kx));
            assert(rc_of(rb, rt, rs, nt, ns, kvals(es, 0, kx)[px] as int) < rc_of(rb, rt, rs, nt, ns, kvals(es, 0, kx)[py] as int));
        }
        lemma_skey_lt(cnt, rb, rt, rs, nt, ns, gx, gy);
    }
    assert forall|h: int| #[trigger] present(cnt, h) implies og.contains(h as u32) by {
        lemma_rc(kb, kt, szl, cnt, rb, rt, rs, h, h);
        let i = choose|i: int| 0 <= i < es.len() && evalue(#[trigger] es[i]) as int == h;
        assert(cent_ok(cnt, maxc, es[i]));
        let k = ekey(es[i], 0);
        lemma_kvals_has(es, 0, i);
        let kv = kvals(es, 0, k);
        let p = choose|p: int| 0 <= p < kv.len() && kv[p] == evalue(es[i]);
        lemma_kvals_len(es, 0, k);
        lemma_og_at(es, og, ng, k, kstart(es, 0, k) + p);
        assert(og[kstart(es, 0, k) + p] == evalue(es[i]));
    }
}

/// The grouped values are as many as the entries, at most one per group id.
proof fn lemma_total_len(es: Seq<u64>, ng: int)
    requires ng >= 0, forall|i: int| 0 <= i < es.len() ==> 0 <= #[trigger] ekey(es[i], 0) < ng,
    ensures kstart(es, 0, ng) == es.len(),
{
    assert(keys_in(es, 0, ng));
    lemma_total(es, 0, ng);
}

/// The present groups in ORDER BY order (see the module comment); `None` when a count reaches `2^20`.
pub fn order_by_count(cnt: &Vec<u64>, rb: &Vec<usize>, rt: &Vec<usize>, rs: &Vec<usize>, nt: usize, ns: usize,
    Ghost(kb): Ghost<Seq<Seq<u8>>>, Ghost(kt): Ghost<Seq<Seq<u8>>>, Ghost(szl): Ghost<Seq<i64>>) -> (r: Option<Vec<u32>>)
    requires
        tables_ok(kb, kt, szl, cnt@), ranks_ok(kb, kt, szl, rb@, rt@, rs@), nt == kt.len(), ns == szl.len(),
    ensures r matches Some(og) ==> og_ok(cnt@, rb@, rt@, rs@, nt as int, ns as int, og@),
{
    let c = cnt.len();
    proof {
        let (nbi, nti, nsi) = (kb.len() as int, nt as int, ns as int);
        assert(nti * nsi <= c) by (nonlinear_arith) requires c == nbi * nti * nsi, nbi >= 1, nti >= 1, nsi >= 1;
    }
    let ntns = nt * ns;
    // The largest count.
    let mut maxc: u64 = 0;
    let mut g: usize = 0;
    while g < c
        invariant c == cnt@.len(), g <= c, forall|h: int| 0 <= h < g ==> #[trigger] cnt@[h] <= maxc,
        decreases c - g,
    {
        if cnt[g] > maxc { maxc = cnt[g]; }
        g = g + 1;
    }
    if maxc >= 0x10_0000 {
        return None;
    }
    let rinv = rank_inverse(cnt, rb, rt, rs, nt, ns, ntns, Ghost(kb), Ghost(kt), Ghost(szl));
    let ent = rank_entries(cnt, rb, rt, rs, nt, ns, ntns, &rinv, maxc, Ghost(kb), Ghost(kt), Ghost(szl));
    // Group by `maxc - count`.
    let m = ent.len();
    let ng = (maxc + 1) as usize;
    let mut ends: Vec<usize> = vec![0usize; ng + 1];
    let mut vals: Vec<u32> = vec![0u32; m];
    let ghost es = ent@;
    proof {
        assert(ent@.take(m as int) =~= es);
        assert forall|i: int| 0 <= i < es.len() implies 0 <= #[trigger] ekey(es[i], 0) < ng by {
            assert(cent_ok(cnt@, maxc, es[i]));
        }
        assert forall|k: int| 0 <= k <= ng implies #[trigger] ends@[k] == 0 by {}
    }
    group_by_key(&ent, m, 0, ng, &mut ends, &mut vals);
    proof {
        assert(grouped(es, vals@, ng as int));
        lemma_order_result(kb, kt, szl, cnt@, rb@, rt@, rs@, maxc, es, vals@, ng as int);
    }
    Some(vals)
}

} // verus!
