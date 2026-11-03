//! Phase 2 worker: for each partition `p` of `plo..phi`, build the set of `pre` key hash pairs `(tv_hash, ad_hash)`
//! of the `pre` rows whose `ad_hash` lies in partition `p` from every phase-1 output (`fill_set`; an output item is
//! `(ad_hash, tv_hash)`), and check that `tv_hash` separates the `tag` values of partition `p`
//! (`fill_dt`, `common::distinct`). One task also checks that `ad_hash` separates the `sub` values (`check_sub`).
//!
//! The phase-1 outputs cover their tables in row ranges that tile `0..rows` (`tiles`); with the completeness of each
//! partitioned output, every `pre` row of partition `p` is in the set (`lemma_pre_complete`) and every pair of
//! `tag` rows of one hash is represented by one slot (`lemma_tag_inj`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::spec::*;
use crate::agent::txt::*;
use crate::agent::hash::hash_text;
use crate::agent::split::*;
use crate::agent::common::partition::*;
use crate::agent::common::pairset::*;
use crate::agent::common::distinct::*;

verus! {

/// The row ranges `rng[r] = (lo, hi)` tile `0..total`, in order.
pub open spec fn tiles(rng: Seq<(int, int)>, total: int) -> bool {
    &&& rng.len() >= 1
    &&& rng[0].0 == 0
    &&& rng[rng.len() - 1].1 == total
    &&& forall|r: int| 0 <= r < rng.len() ==> #[trigger] rng[r].0 <= rng[r].1
    &&& forall|r: int| 0 < r < rng.len() ==> #[trigger] rng[r].0 == rng[r - 1].1
}

/// Every row of `0..total` lies in one of the tiling ranges.
pub proof fn lemma_tile_find(rng: Seq<(int, int)>, total: int, j: int)
    requires tiles(rng, total), 0 <= j < total,
    ensures exists|r: int| 0 <= r < rng.len() && #[trigger] rng[r].0 <= j < rng[r].1,
{
    lemma_tile_below(rng, total, j, rng.len() - 1);
}

proof fn lemma_tile_below(rng: Seq<(int, int)>, total: int, j: int, r: int)
    requires tiles(rng, total), 0 <= j < rng[r].1, 0 <= r < rng.len(),
    ensures exists|r2: int| 0 <= r2 <= r && #[trigger] rng[r2].0 <= j < rng[r2].1,
    decreases r,
{
    if j >= rng[r].0 {
        assert(rng[r].0 <= j < rng[r].1);
    } else {
        assert(r > 0);
        assert(rng[r].0 == rng[r - 1].1);
        lemma_tile_below(rng, total, j, r - 1);
    }
}

/// The phase-1 `pre` outputs partition the key hash pairs of their row ranges, which tile `0..m`.
pub open spec fn pre_parts_ok(c: Ctx, outs: Seq<Parted>, rng: Seq<(int, int)>) -> bool {
    &&& outs.len() == rng.len()
    &&& tiles(rng, c.m)
    &&& forall|r: int| 0 <= r < outs.len() ==> #[trigger] parted_ok(outs[r], pre_ks(c, rng[r].0, rng[r].1), pre_xs(c, rng[r].0, rng[r].1))
}

/// The phase-1 `tag` outputs partition the value hashes (with row numbers) of their ranges, which tile `0..nt`.
pub open spec fn tag_parts_ok(c: Ctx, outs: Seq<Parted>, rng: Seq<(int, int)>) -> bool {
    &&& outs.len() == rng.len()
    &&& tiles(rng, c.nt)
    &&& forall|r: int| 0 <= r < outs.len() ==> #[trigger] parted_ok(outs[r], tag_ks(c, rng[r].0, rng[r].1), tag_xs(c, rng[r].0, rng[r].1))
}

/// Some `pre` row has the key hash pair `(k, x)`.
pub open spec fn pre_pair(c: Ctx, k: u64, x: u64) -> bool {
    exists|j: int| 0 <= j < c.m && #[trigger] pre_tv(c, j) == k && pre_ad(c, j) == x
}

/// Every pair of the set is a `pre` row's.
pub open spec fn set_sound(t: PairSet, c: Ctx) -> bool {
    forall|k: u64, x: u64| #[trigger] has(t, k, x) ==> pre_pair(c, k, x)
}

/// The set of partition `p`: the key hash pairs of the `pre` rows whose `ad_hash` lies in partition `p` (and
/// possibly others' pairs; only membership of the partition's rows and soundness matter).
pub open spec fn pre_set_ok(t: PairSet, c: Ctx, p: int) -> bool {
    &&& set_wf(t)
    &&& set_sound(t, c)
    &&& forall|j: int| 0 <= j < c.m && part_of(pre_ad(c, j)) == p ==> #[trigger] has(t, pre_tv(c, j), pre_ad(c, j))
}

/// `tv_hash` separates the `tag` values whose hash lies in partition `p`.
pub open spec fn tag_part_inj(c: Ctx, p: int) -> bool {
    forall|a: int, b: int| 0 <= a < c.nt && 0 <= b < c.nt && part_of(tag_tv(c, a)) == p
        && #[trigger] tag_tv(c, a) == #[trigger] tag_tv(c, b)
        ==> ttag(c, a) == ttag(c, b) && tver(c, a) == tver(c, b)
}

/// An item `(ad, tv)` of a `pre` output segment is a `pre` key hash pair `(tv, ad)` with `tv != 0`.
pub proof fn lemma_pre_item(c: Ctx, outs: Seq<Parted>, rng: Seq<(int, int)>, r: int, p: int, e: int)
    requires pre_parts_ok(c, outs, rng), 0 <= r < outs.len(), in_seg(outs[r], p, e),
    ensures pre_pair(c, outs[r].auxs@[e], outs[r].keys@[e]), outs[r].auxs@[e] != 0,
{
    let (lo, hi) = (rng[r].0, rng[r].1);
    let (k, x) = (outs[r].keys@[e], outs[r].auxs@[e]);
    assert(parted_ok(outs[r], pre_ks(c, lo, hi), pre_xs(c, lo, hi)));
    assert(src_item(pre_ks(c, lo, hi), pre_xs(c, lo, hi), k, x));
    let q = choose|q: int| 0 <= q < pre_ks(c, lo, hi).len() && #[trigger] pre_ks(c, lo, hi)[q] == k && pre_xs(c, lo, hi)[q] == x;
    assert(pre_ad(c, lo + q) == k && pre_tv(c, lo + q) == x);
    lemma_tile_mono(rng, c.m, r, rng.len() - 1);
    lemma_tile_mono(rng, c.m, 0, r);
    assert(0 <= lo + q < c.m);
    assert(pre_pair(c, x, k));
    lemma_or_one_nonzero(hash_text(pver(c, lo + q), hash_text(ptag(c, lo + q), crate::agent::hash::SEED_TAG)));
}

/// An item of a `tag` output segment is a non-zero value hash with the number of a `tag` row that has it.
pub proof fn lemma_tag_item(c: Ctx, outs: Seq<Parted>, rng: Seq<(int, int)>, r: int, p: int, e: int)
    requires tag_parts_ok(c, outs, rng), 0 <= r < outs.len(), in_seg(outs[r], p, e), c.nt <= usize::MAX,
    ensures
        outs[r].keys@[e] != 0,
        (outs[r].auxs@[e] as int) < c.nt,
        outs[r].keys@[e] == tag_tv(c, outs[r].auxs@[e] as int),
{
    let (lo, hi) = (rng[r].0, rng[r].1);
    let (k, x) = (outs[r].keys@[e], outs[r].auxs@[e]);
    assert(parted_ok(outs[r], tag_ks(c, lo, hi), tag_xs(c, lo, hi)));
    assert(src_item(tag_ks(c, lo, hi), tag_xs(c, lo, hi), k, x));
    let q = choose|q: int| 0 <= q < tag_ks(c, lo, hi).len() && #[trigger] tag_ks(c, lo, hi)[q] == k && tag_xs(c, lo, hi)[q] == x;
    lemma_tile_mono(rng, c.nt, r, rng.len() - 1);
    lemma_tile_mono(rng, c.nt, 0, r);
    assert(0 <= lo + q < c.nt);
    assert(x == (lo + q) as u64);
    assert(x as int == lo + q);
    assert(k == tag_tv(c, lo + q));
    lemma_or_one_nonzero(hash_text(crate::agent::spec::tver(c, lo + q), hash_text(crate::agent::spec::ttag(c, lo + q), crate::agent::hash::SEED_TAG)));
}

/// Insert the items `(ad, tv)` of segment `p` of every output into the set, as pairs `(tv, ad)`.
#[verifier::spinoff_prover]
pub fn fill_set(t: &mut PairSet, outs: &Vec<Parted>, p: usize, Ghost(c): Ghost<Ctx>, Ghost(rng): Ghost<Seq<(int, int)>>)
    -> (ok: bool)
    requires
        set_wf(*old(t)), set_sound(*old(t), c), pre_parts_ok(c, outs@, rng), p < PARTS,
    ensures
        set_wf(*final(t)), set_sound(*final(t), c),
        ok ==> forall|r: int, e: int| 0 <= r < outs@.len() && #[trigger] in_seg(outs@[r], p as int, e)
            ==> has(*final(t), outs@[r].auxs@[e], outs@[r].keys@[e]),
    no_unwind
{
    let nouts = outs.len();
    let mut r: usize = 0;
    while r < nouts
        invariant
            r <= nouts, nouts == outs@.len(), p < PARTS,
            set_wf(*t), set_sound(*t, c), pre_parts_ok(c, outs@, rng),
            forall|r2: int, e: int| 0 <= r2 < r && #[trigger] in_seg(outs@[r2], p as int, e)
                ==> has(*t, outs@[r2].auxs@[e], outs@[r2].keys@[e]),
        decreases nouts - r,
    {
        let o = &outs[r];
        proof {
            assert(parted_ok(*o, pre_ks(c, rng[r as int].0, rng[r as int].1), pre_xs(c, rng[r as int].0, rng[r as int].1)));
        }
        let start = o.starts[p];
        let end = o.ends[p];
        let mut e = start;
        while e < end
            invariant
                r < nouts, nouts == outs@.len(), p < PARTS, *o == outs@[r as int],
                start == o.starts@[p as int], end == o.ends@[p as int], start <= e <= end,
                segs_ok(*o),
                parted_ok(*o, pre_ks(c, rng[r as int].0, rng[r as int].1), pre_xs(c, rng[r as int].0, rng[r as int].1)),
                set_wf(*t), set_sound(*t, c), pre_parts_ok(c, outs@, rng),
                forall|r2: int, e2: int| 0 <= r2 < r && #[trigger] in_seg(outs@[r2], p as int, e2)
                    ==> has(*t, outs@[r2].auxs@[e2], outs@[r2].keys@[e2]),
                forall|e2: int| start <= e2 < e ==> #[trigger] has(*t, o.auxs@[e2], o.keys@[e2]),
            decreases end - e,
        {
            let k = o.keys[e];
            let x = o.auxs[e];
            let ghost t0 = *t;
            proof {
                assert(in_seg(*o, p as int, e as int));
                lemma_pre_item(c, outs@, rng, r as int, p as int, e as int);
            }
            let ok = insert(t, x, k);
            if !ok {
                return false;
            }
            proof {
                assert forall|k2: u64, x2: u64| #[trigger] has(*t, k2, x2) implies pre_pair(c, k2, x2) by {
                    if has(t0, k2, x2) {
                    }
                }
            }
            e = e + 1;
        }
        proof {
            assert forall|r2: int, e2: int| 0 <= r2 < r + 1 && #[trigger] in_seg(outs@[r2], p as int, e2)
                implies has(*t, outs@[r2].auxs@[e2], outs@[r2].keys@[e2]) by {
                if r2 == r as int {
                    assert(start <= e2 < end);
                }
            }
        }
        r = r + 1;
    }
    true
}

/// The ends of tiling ranges grow.
pub proof fn lemma_tile_mono(rng: Seq<(int, int)>, total: int, a: int, b: int)
    requires tiles(rng, total), 0 <= a <= b < rng.len(),
    ensures rng[a].1 <= rng[b].1, rng[a].0 <= rng[b].0,
    decreases b - a,
{
    if a < b {
        lemma_tile_mono(rng, total, a, b - 1);
        assert(rng[b].0 == rng[b - 1].1);
        assert(rng[b].0 <= rng[b].1);
        assert(rng[b - 1].0 <= rng[b - 1].1);
    }
}

pub proof fn lemma_or_one_nonzero(h: u64)
    ensures (h | 1u64) != 0,
{
    assert((h | 1u64) != 0) by (bit_vector);
}

/// After all segments `p` were inserted, every `pre` row of partition `p` is in the set.
pub proof fn lemma_pre_complete(c: Ctx, outs: Seq<Parted>, rng: Seq<(int, int)>, t: PairSet, p: int)
    requires
        pre_parts_ok(c, outs, rng), 0 <= p < PARTS,
        forall|r: int, e: int| 0 <= r < outs.len() && #[trigger] in_seg(outs[r], p, e) ==> has(t, outs[r].auxs@[e], outs[r].keys@[e]),
    ensures
        forall|j: int| 0 <= j < c.m && part_of(pre_ad(c, j)) == p ==> #[trigger] has(t, pre_tv(c, j), pre_ad(c, j)),
{
    assert forall|j: int| 0 <= j < c.m && part_of(pre_ad(c, j)) == p implies #[trigger] has(t, pre_tv(c, j), pre_ad(c, j)) by {
        lemma_tile_find(rng, c.m, j);
        let r = choose|r: int| 0 <= r < rng.len() && #[trigger] rng[r].0 <= j < rng[r].1;
        let (lo, hi) = (rng[r].0, rng[r].1);
        let ks = pre_ks(c, lo, hi);
        let xs = pre_xs(c, lo, hi);
        assert(parted_ok(outs[r], ks, xs));
        let q = j - lo;
        assert(ks[q] == pre_ad(c, j) && xs[q] == pre_tv(c, j));
        assert(seg_has(outs[r], part_of(ks[q]), ks[q], xs[q]));
        let e = choose|e: int| #[trigger] in_seg(outs[r], p, e) && outs[r].keys@[e] == ks[q] && outs[r].auxs@[e] == xs[q];
    }
}

/// Add the items (hash, row) of segment `p` of every `tag` output to the distinct-hash table.
#[verifier::spinoff_prover]
pub fn fill_dt(t: &mut DistinctTable, outs: &Vec<Parted>, p: usize, ttag: &TextCol, tver: &TextCol,
    Ghost(c): Ghost<Ctx>, Ghost(rng): Ghost<Seq<(int, int)>>) -> (ok: bool)
    requires
        dt_wf(*old(t), c.nt), tag_parts_ok(c, outs@, rng), p < PARTS, ctx_ok(c),
        ttag@ == ttag_v(c), tver@ == tver_v(c), c.nt <= usize::MAX,
    ensures
        dt_wf(*final(t), c.nt),
        ok ==> forall|r: int, e: int| 0 <= r < outs@.len() && #[trigger] in_seg(outs@[r], p as int, e)
            ==> rep(*final(t), outs@[r].keys@[e], ttag@, tver@, outs@[r].auxs@[e] as int),
    no_unwind
{
    proof {
        lemma_text_cols_wf(c);
    }
    let nouts = outs.len();
    let mut r: usize = 0;
    while r < nouts
        invariant
            r <= nouts, nouts == outs@.len(), p < PARTS, ctx_ok(c), c.nt <= usize::MAX,
            ttag@ == ttag_v(c), tver@ == tver_v(c), text_wf(ttag@, c.nt), text_wf(tver@, c.nt),
            dt_wf(*t, c.nt), tag_parts_ok(c, outs@, rng),
            forall|r2: int, e: int| 0 <= r2 < r && #[trigger] in_seg(outs@[r2], p as int, e)
                ==> rep(*t, outs@[r2].keys@[e], ttag@, tver@, outs@[r2].auxs@[e] as int),
        decreases nouts - r,
    {
        let o = &outs[r];
        proof {
            assert(parted_ok(*o, tag_ks(c, rng[r as int].0, rng[r as int].1), tag_xs(c, rng[r as int].0, rng[r as int].1)));
        }
        let start = o.starts[p];
        let end = o.ends[p];
        let mut e = start;
        while e < end
            invariant
                r < nouts, nouts == outs@.len(), p < PARTS, *o == outs@[r as int], ctx_ok(c), c.nt <= usize::MAX,
                ttag@ == ttag_v(c), tver@ == tver_v(c), text_wf(ttag@, c.nt), text_wf(tver@, c.nt),
                start == o.starts@[p as int], end == o.ends@[p as int], start <= e <= end,
                segs_ok(*o),
                parted_ok(*o, tag_ks(c, rng[r as int].0, rng[r as int].1), tag_xs(c, rng[r as int].0, rng[r as int].1)),
                dt_wf(*t, c.nt), tag_parts_ok(c, outs@, rng),
                forall|r2: int, e2: int| 0 <= r2 < r && #[trigger] in_seg(outs@[r2], p as int, e2)
                    ==> rep(*t, outs@[r2].keys@[e2], ttag@, tver@, outs@[r2].auxs@[e2] as int),
                forall|e2: int| start <= e2 < e ==> #[trigger] rep(*t, o.keys@[e2], ttag@, tver@, o.auxs@[e2] as int),
            decreases end - e,
        {
            let h = o.keys[e];
            let row = o.auxs[e];
            let ghost t0 = *t;
            proof {
                assert(in_seg(*o, p as int, e as int));
                lemma_tag_item(c, outs@, rng, r as int, p as int, e as int);
            }
            let good = crate::agent::common::distinct::add(t, h, row, ttag, tver, Ghost(c.nt));
            if !good {
                return false;
            }
            proof {
                assert forall|e2: int| start <= e2 < e + 1 implies #[trigger] rep(*t, o.keys@[e2], ttag@, tver@, o.auxs@[e2] as int) by {
                    if e2 < e as int {
                        assert(rep(t0, o.keys@[e2], ttag@, tver@, o.auxs@[e2] as int));
                    }
                }
                assert forall|r2: int, e2: int| 0 <= r2 < r && #[trigger] in_seg(outs@[r2], p as int, e2)
                    implies rep(*t, outs@[r2].keys@[e2], ttag@, tver@, outs@[r2].auxs@[e2] as int) by {
                    assert(rep(t0, outs@[r2].keys@[e2], ttag@, tver@, outs@[r2].auxs@[e2] as int));
                }
            }
            e = e + 1;
        }
        proof {
            assert forall|r2: int, e2: int| 0 <= r2 < r + 1 && #[trigger] in_seg(outs@[r2], p as int, e2)
                implies rep(*t, outs@[r2].keys@[e2], ttag@, tver@, outs@[r2].auxs@[e2] as int) by {
                if r2 == r as int {
                    assert(start <= e2 < end);
                }
            }
        }
        r = r + 1;
    }
    true
}

/// After all segments `p` were added, `tv_hash` separates the `tag` values of partition `p`.
pub proof fn lemma_tag_inj(c: Ctx, outs: Seq<Parted>, rng: Seq<(int, int)>, t: DistinctTable, p: int)
    requires
        tag_parts_ok(c, outs, rng), 0 <= p < PARTS, dt_wf(t, c.nt), c.nt <= usize::MAX,
        forall|r: int, e: int| 0 <= r < outs.len() && #[trigger] in_seg(outs[r], p, e)
            ==> rep(t, outs[r].keys@[e], ttag_v(c), tver_v(c), outs[r].auxs@[e] as int),
    ensures tag_part_inj(c, p),
{
    assert forall|a: int, b: int| 0 <= a < c.nt && 0 <= b < c.nt && part_of(tag_tv(c, a)) == p
        && #[trigger] tag_tv(c, a) == #[trigger] tag_tv(c, b)
        implies ttag(c, a) == ttag(c, b) && tver(c, a) == tver(c, b) by {
        lemma_tag_rep(c, outs, rng, t, p, a);
        lemma_tag_rep(c, outs, rng, t, p, b);
        lemma_rep_same(t, c.nt, tag_tv(c, a), ttag_v(c), tver_v(c), a, b);
    }
}

/// A `tag` row of partition `p` is represented under its hash.
proof fn lemma_tag_rep(c: Ctx, outs: Seq<Parted>, rng: Seq<(int, int)>, t: DistinctTable, p: int, a: int)
    requires
        tag_parts_ok(c, outs, rng), 0 <= p < PARTS, 0 <= a < c.nt, part_of(tag_tv(c, a)) == p, c.nt <= usize::MAX,
        forall|r: int, e: int| 0 <= r < outs.len() && #[trigger] in_seg(outs[r], p, e)
            ==> rep(t, outs[r].keys@[e], ttag_v(c), tver_v(c), outs[r].auxs@[e] as int),
    ensures rep(t, tag_tv(c, a), ttag_v(c), tver_v(c), a),
{
    lemma_tile_find(rng, c.nt, a);
    let r = choose|r: int| 0 <= r < rng.len() && #[trigger] rng[r].0 <= a < rng[r].1;
    let (lo, hi) = (rng[r].0, rng[r].1);
    let ks = tag_ks(c, lo, hi);
    let xs = tag_xs(c, lo, hi);
    assert(parted_ok(outs[r], ks, xs));
    let q = a - lo;
    assert(ks[q] == tag_tv(c, a) && xs[q] == a as u64);
    assert(seg_has(outs[r], part_of(ks[q]), ks[q], xs[q]));
    let e = choose|e: int| #[trigger] in_seg(outs[r], p, e) && outs[r].keys@[e] == ks[q] && outs[r].auxs@[e] == xs[q];
    assert(outs[r].auxs@[e] as int == a) by {
        assert(rng[r].1 <= rng[rng.len() - 1].1) by {
            lemma_tile_mono(rng, c.nt, r, rng.len() - 1);
        }
    }
}

/// The `sub` check: `ad_hash` separates the `adsh` values of `sub` (`false`: a collision, or a full table).
pub struct SubJob {
    pub sadsh: TextCol,
    pub ns: usize,
    pub table: DistinctTable,
}

pub open spec fn sub_job_ok(j: SubJob, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& j.sadsh@ == sadsh_v(c)
    &&& j.ns as int == c.ns
    &&& dt_wf(j.table, c.ns)
}

#[verifier::spinoff_prover]
pub fn check_sub(j: SubJob, Ghost(c): Ghost<Ctx>) -> (ok: bool)
    requires sub_job_ok(j, c),
    ensures ok ==> ad_injective(c),
    no_unwind
{
    let SubJob { sadsh, ns, table } = j;
    let mut table = table;
    proof {
        lemma_text_cols_wf(c);
    }
    let mut s: usize = 0;
    while s < ns
        invariant
            s <= ns, ns as int == c.ns, ctx_ok(c), sadsh@ == sadsh_v(c), text_wf(sadsh@, c.ns),
            dt_wf(table, c.ns),
            forall|s2: int| 0 <= s2 < s ==> #[trigger] rep(table, sub_ad(c, s2), sadsh@, sadsh@, s2),
        decreases ns - s,
    {
        let h = ad_hash_at(&sadsh, s, Ghost(c.ns));
        let ghost t0 = table;
        let good = crate::agent::common::distinct::add(&mut table, h, s as u64, &sadsh, &sadsh, Ghost(c.ns));
        if !good {
            return false;
        }
        proof {
            assert forall|s2: int| 0 <= s2 < s + 1 implies #[trigger] rep(table, sub_ad(c, s2), sadsh@, sadsh@, s2) by {
                if s2 < s as int {
                    assert(rep(t0, sub_ad(c, s2), sadsh@, sadsh@, s2));
                }
            }
        }
        s = s + 1;
    }
    proof {
        assert forall|a: int, b: int| 0 <= a < c.ns && 0 <= b < c.ns && #[trigger] sub_ad(c, a) == #[trigger] sub_ad(c, b)
            implies crate::agent::spec::sadsh(c, a) == crate::agent::spec::sadsh(c, b) by {
            assert(rep(table, sub_ad(c, a), sadsh@, sadsh@, a));
            assert(rep(table, sub_ad(c, b), sadsh@, sadsh@, b));
            lemma_rep_same(table, c.ns, sub_ad(c, a), sadsh@, sadsh@, a, b);
        }
    }
    true
}

/// Phase 2 task: partitions `plo..phi` (one empty set and one empty distinct-hash table each), optionally the
/// `sub` check.
pub struct BuildTask {
    pub c: Ghost<Ctx>,
    pub plo: usize,
    pub phi: usize,
    pub pre: Arc<Vec<Parted>>,
    pub prng: Ghost<Seq<(int, int)>>,
    pub tag: Arc<Vec<Parted>>,
    pub trng: Ghost<Seq<(int, int)>>,
    pub ttag: TextCol,
    pub tver: TextCol,
    pub sets: Vec<PairSet>,
    pub dts: Vec<DistinctTable>,
    pub sub: Option<SubJob>,
}

pub struct BuildOut {
    pub sets: Vec<PairSet>,
    pub ok: bool,
}

pub open spec fn build_pre(t: BuildTask) -> bool {
    let c = t.c@;
    &&& ctx_ok(c) && c.nt <= usize::MAX
    &&& t.plo <= t.phi <= PARTS
    &&& pre_parts_ok(c, t.pre@, t.prng@)
    &&& tag_parts_ok(c, t.tag@, t.trng@)
    &&& t.ttag@ == ttag_v(c) && t.tver@ == tver_v(c)
    &&& t.sets@.len() == t.phi - t.plo && t.dts@.len() == t.phi - t.plo
    &&& sets_ready(t.sets@, c)
    &&& dts_ready(t.dts@, c.nt)
    &&& (t.sub matches Some(j) ==> sub_job_ok(j, c))
}

/// Every set is well formed and sound.
pub open spec fn sets_ready(sets: Seq<PairSet>, c: Ctx) -> bool {
    forall|k: int| #![trigger sets[k]] 0 <= k < sets.len() ==> set_wf(sets[k]) && set_sound(sets[k], c)
}

/// Every distinct-hash table is well formed.
pub open spec fn dts_ready(dts: Seq<DistinctTable>, n: int) -> bool {
    forall|k: int| #![trigger dts[k]] 0 <= k < dts.len() ==> dt_wf(dts[k], n)
}

/// The per-slot parts of `build_pre`, stated on the vectors alone.
pub proof fn lemma_build_pre_parts(t: BuildTask)
    requires build_pre(t),
    ensures sets_ready(t.sets@, t.c@), dts_ready(t.dts@, t.c@.nt),
{
}

/// The sets of partitions `plo..` are complete and sound, and `tv_hash` separates the `tag` values of them.
pub open spec fn built_ok(c: Ctx, plo: int, sets: Seq<PairSet>) -> bool {
    forall|k: int| #![trigger sets[k]] 0 <= k < sets.len() ==> pre_set_ok(sets[k], c, plo + k) && tag_part_inj(c, plo + k)
}

impl WorkerTask for BuildTask {
    type Output = BuildOut;

    open spec fn pre(&self) -> bool {
        build_pre(*self)
    }

    open spec fn post(&self, out: BuildOut) -> bool {
        out.ok ==> {
            &&& out.sets@.len() == self.phi - self.plo
            &&& built_ok(self.c@, self.plo as int, out.sets@)
            &&& (self.sub is Some ==> ad_injective(self.c@))
        }
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.plo as u64, self.phi as u64)
    }

    fn run(self) -> (out: BuildOut) {
        proof {
            assert(build_pre(self));
            lemma_build_pre_parts(self);
        }
        let ghost sets_in = self.sets@;
        let ghost dts_in = self.dts@;
        let BuildTask { c, plo, phi, pre, prng, tag, trng, ttag, tver, sets, dts, sub } = self;
        let ghost cc = c@;
        proof {
            assert(sets@ == sets_in);
            assert(sets@.subrange(0, 0) =~= Seq::<PairSet>::empty());
        }
        let has_sub = sub.is_some();
        let mut sets = sets;
        let mut dts = dts;
        let pre_v: &Vec<Parted> = &*pre;
        let tag_v: &Vec<Parted> = &*tag;
        let mut p = plo;
        while p < phi
            invariant
                plo <= p <= phi <= PARTS, ctx_ok(cc), cc.nt <= usize::MAX, cc == c@,
                pre_parts_ok(cc, pre_v@, prng@), tag_parts_ok(cc, tag_v@, trng@),
                ttag@ == ttag_v(cc), tver@ == tver_v(cc),
                sets@.len() == phi - plo, dts@.len() == phi - plo,
                sets_ready(sets@, cc),
                dts_ready(dts@, cc.nt),
                built_ok(cc, plo as int, sets@.subrange(0, p - plo)),
            decreases phi - p,
        {
            let k = p - plo;
            let ghost sets0 = sets@;
            proof {
                assert(built_ok(cc, plo as int, sets0.subrange(0, p - plo)));
                assert(0 <= k < sets@.len());
                assert(set_wf(sets@[k as int]));
                assert(set_sound(sets@[k as int], cc));
                assert(dt_wf(dts@[k as int], cc.nt));
            }
            let ok1 = fill_set(&mut sets[k], pre_v, p, Ghost(cc), prng);
            if !ok1 {
                return BuildOut { sets, ok: false };
            }
            proof {
                lemma_pre_complete(cc, pre_v@, prng@, sets@[k as int], p as int);
                assert(sets@ == sets0.update(k as int, sets@[k as int]));
            }
            let ghost dts0 = dts@;
            let ok2 = fill_dt(&mut dts[k], tag_v, p, &ttag, &tver, Ghost(cc), trng);
            if !ok2 {
                return BuildOut { sets, ok: false };
            }
            proof {
                lemma_tag_inj(cc, tag_v@, trng@, dts@[k as int], p as int);
                assert(dts@ == dts0.update(k as int, dts@[k as int]));
                assert forall|k2: int| #![trigger sets@[k2]] 0 <= k2 < sets@.len() implies set_wf(sets@[k2]) && set_sound(sets@[k2], cc) by {
                    if k2 != k as int {
                        assert(sets@[k2] == sets0[k2]);
                        assert(set_wf(sets0[k2]) && set_sound(sets0[k2], cc));
                    }
                }
                assert forall|k2: int| #![trigger dts@[k2]] 0 <= k2 < dts@.len() implies dt_wf(dts@[k2], cc.nt) by {
                    if k2 != k as int {
                        assert(dts@[k2] == dts0[k2]);
                        assert(dt_wf(dts0[k2], cc.nt));
                    }
                }
                let done = sets@.subrange(0, p + 1 - plo);
                let prev = sets0.subrange(0, p - plo);
                assert(built_ok(cc, plo as int, prev));
                assert(pre_set_ok(sets@[k as int], cc, p as int));
                assert(tag_part_inj(cc, p as int));
                assert forall|k2: int| #![trigger done[k2]] 0 <= k2 < done.len() implies pre_set_ok(done[k2], cc, plo + k2) && tag_part_inj(cc, plo + k2) by {
                    if k2 < k as int {
                        assert(done[k2] == prev[k2]);
                        assert(pre_set_ok(prev[k2], cc, plo + k2) && tag_part_inj(cc, plo + k2));
                    } else {
                        assert(done[k2] == sets@[k as int]);
                    }
                }
                assert(built_ok(cc, plo as int, done));
            }
            p = p + 1;
        }
        match sub {
            Some(j) => {
                if !check_sub(j, c) {
                    return BuildOut { sets, ok: false };
                }
            },
            None => {},
        }
        proof {
            assert(sets@.subrange(0, phi - plo) =~= sets@);
        }
        BuildOut { sets, ok: true }
    }
}

} // verus!
