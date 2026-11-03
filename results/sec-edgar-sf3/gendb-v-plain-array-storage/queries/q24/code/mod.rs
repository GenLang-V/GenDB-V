//! Query: per `(tag, version)`, COUNT(*) and SUM(value) of the `num` rows with `uom = $1` and `ddate` in
//! `[$2, $3]` that have no `pre` row with the same `(tag, version, adsh)` (LEFT JOIN ... IS NULL), groups with
//! COUNT(*) > 10, the 100 largest counts.
//!
//! Plan (`query`):
//! 1. `split` (parallel over row ranges): hash every `pre` row's key to the pair `(tv_hash(tag, version),
//!    ad_hash(adsh))`, partitioned by the top bits of `ad_hash`, and every `tag` row's value to `tv_hash`,
//!    partitioned by the top bits of `tv_hash`;
//! 2. `build` (parallel over partitions): per partition, the set of `pre` key hash pairs, and a check that
//!    `tv_hash` separates the `tag` values; one task checks that `ad_hash` separates the `sub` values;
//! 3. `scan` (parallel over `num` row ranges): filter `uom` and `ddate`, and probe the qualifying rows' pairs.
//!    Under the declared foreign keys (`num`/`pre` keys are `tag`/`sub` values, `bind::lemma_fk`) and the two
//!    separations, a pair is in the set exactly when a `pre` row has the same key (`scan::lemma_probe`). If a
//!    check failed (a hash collision), the scan compares the key texts with every `pre` row instead;
//! 4. on the calling thread: group the kept rows (`group`), HAVING, sort by COUNT(*) descending, first 100
//!    (`answer`). `sem` proves the statement's meaning is exactly that (`answer::lemma_answer`); a group sum
//!    outside `i128` is the capacity case (`cap::lemma_capacity`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::Answer;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::{QueryError, WorkerFailure};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::work::TaskBuffer;
use crate::gendb_params::Params;
use crate::exec::value::EVal;
use crate::link::query::{text_wf, view_rows, TextCol};
use crate::spec::value::*;
use crate::spec::limits::int8_max;
use crate::stores::flat_num::interface as ni;
use crate::stores::flat_pre::interface as pi;
use crate::stores::flat_sub::interface as si;
use crate::stores::flat_tag::interface as ti;

pub mod common;
pub mod hash;
pub mod spec;
pub mod txt;
pub mod split;
pub mod build;
pub mod scan;
pub mod group;
pub mod answer;
pub mod bind;
pub mod sem;
pub mod cap;

use crate::agent::spec::*;
use crate::agent::split::*;
use crate::agent::build::*;
use crate::agent::scan::*;
use crate::agent::group::*;
use crate::agent::answer::*;
use crate::agent::bind::*;
use crate::agent::sem::lits_ok;
use crate::agent::common::partition::*;
use crate::agent::common::pairset::{PairSet, new_set, set_wf};
use crate::agent::common::distinct::{DistinctTable, new_table, dt_wf};

verus! {

/// Largest table size (slots below 2^30, so every size fits any `usize`).
pub const MAX_CAP: usize = 0x4000_0000;

/// The columns the query reads (whole parts).
pub struct Cols {
    pub ntag: TextCol,
    pub nver: TextCol,
    pub nadsh: TextCol,
    pub nuom: TextCol,
    pub ddate: &'static [i32],
    pub value: &'static [i128],
    pub ptag: TextCol,
    pub pver: TextCol,
    pub padsh: TextCol,
    pub sadsh: TextCol,
    pub ttag: TextCol,
    pub tver: TextCol,
}

pub open spec fn cols_ok(k: Cols, c: Ctx) -> bool {
    &&& k.ntag@ == ntag_v(c) && k.nver@ == nver_v(c) && k.nadsh@ == nadsh_v(c) && k.nuom@ == nuom_v(c)
    &&& k.ddate@ == ni::i32s(c.np[ni::DDATE as int])
    &&& k.value@ == ni::i128s(c.np[ni::VALUE as int])
    &&& k.ptag@ == ptag_v(c) && k.pver@ == pver_v(c) && k.padsh@ == padsh_v(c)
    &&& k.sadsh@ == sadsh_v(c) && k.ttag@ == ttag_v(c) && k.tver@ == tver_v(c)
}

fn tc(t: &TextCol) -> (r: TextCol)
    ensures r@ == t@,
{
    TextCol { offsets: t.offsets, bytes: t.bytes }
}

/// A whole text column: offsets part `op`, bytes part `bp`.
fn read_text(s: &mut StoredParts, op: usize, bp: usize) -> (t: TextCol)
    requires op < old(s)@.len(), bp < old(s)@.len(), old(s)@[op as int] is I64, old(s)@[bp as int] is U8,
    ensures final(s)@ == old(s)@, t@.offsets == old(s)@[op as int]->I64_0, t@.bytes == old(s)@[bp as int]->U8_0,
{
    let no = s.part_len(op);
    let offsets = s.extent_i64(op, 0, no);
    let nb = s.part_len(bp);
    let bytes = s.extent_u8(bp, 0, nb);
    proof {
        assert(offsets@ =~= old(s)@[op as int]->I64_0);
        assert(bytes@ =~= old(s)@[bp as int]->U8_0);
    }
    TextCol { offsets, bytes }
}

fn read_cols(stores: &mut Stores, Ghost(c): Ghost<Ctx>) -> (k: Cols)
    requires
        ctx_ok(c),
        c.np == old(stores)@.flat_num, c.pp == old(stores)@.flat_pre,
        c.sp == old(stores)@.flat_sub, c.tp == old(stores)@.flat_tag,
    ensures cols_ok(k, c), final(stores)@ == old(stores)@,
{
    let ntag = read_text(&mut stores.flat_num, ni::TAG_OFFSETS, ni::TAG_BYTES);
    let nver = read_text(&mut stores.flat_num, ni::VERSION_OFFSETS, ni::VERSION_BYTES);
    let nadsh = read_text(&mut stores.flat_num, ni::ADSH_OFFSETS, ni::ADSH_BYTES);
    let nuom = read_text(&mut stores.flat_num, ni::UOM_OFFSETS, ni::UOM_BYTES);
    let nd = stores.flat_num.part_len(ni::DDATE);
    let ddate = stores.flat_num.extent_i32(ni::DDATE, 0, nd);
    let nv = stores.flat_num.part_len(ni::VALUE);
    let value = stores.flat_num.extent_i128(ni::VALUE, 0, nv);
    let ptag = read_text(&mut stores.flat_pre, pi::TAG_OFFSETS, pi::TAG_BYTES);
    let pver = read_text(&mut stores.flat_pre, pi::VERSION_OFFSETS, pi::VERSION_BYTES);
    let padsh = read_text(&mut stores.flat_pre, pi::ADSH_OFFSETS, pi::ADSH_BYTES);
    let sadsh = read_text(&mut stores.flat_sub, si::ADSH_OFFSETS, si::ADSH_BYTES);
    let ttag = read_text(&mut stores.flat_tag, ti::TAG_OFFSETS, ti::TAG_BYTES);
    let tver = read_text(&mut stores.flat_tag, ti::VERSION_OFFSETS, ti::VERSION_BYTES);
    proof {
        assert(ddate@ =~= ni::i32s(c.np[ni::DDATE as int]));
        assert(value@ =~= ni::i128s(c.np[ni::VALUE as int]));
    }
    Cols { ntag, nver, nadsh, nuom, ddate, value, ptag, pver, padsh, sadsh, ttag, tver }
}

/// The end of range `t` of a tiling of `0..total` into `tasks` ranges of `chunk` rows (the last takes the rest).
fn next_hi(lo: usize, total: usize, chunk: usize, t: usize, tasks: usize) -> (hi: usize)
    requires lo <= total, t < tasks,
    ensures lo <= hi <= total, t + 1 == tasks ==> hi == total,
{
    if t + 1 == tasks || chunk >= total - lo { total } else { lo + chunk }
}

/// The table mask for `cnt` items (load at most 3/4, at most `MAX_CAP` slots).
fn mask_for(cnt: usize) -> (mask: u64)
    ensures 2 * (mask as int + 1 + crate::agent::common::pairset::ROOM) <= usize::MAX, mask < MAX_CAP,
{
    let mut cap: usize = 64;
    while cap < MAX_CAP && cap / 4 * 3 < cnt
        invariant 64 <= cap <= MAX_CAP,
        decreases MAX_CAP - cap,
    {
        cap = if cap > MAX_CAP / 2 { MAX_CAP } else { cap * 2 };
    }
    (cap - 1) as u64
}

/// Phase 1: the partitioned `pre` key hash pairs and `tag` value hashes (`None`: a partition overflowed).
fn phase1(k: &Cols, workers: usize, dispatch: &mut Dispatch, Ghost(c): Ghost<Ctx>)
    -> (r: Result<Option<(Vec<Parted>, Vec<Parted>, Ghost<Seq<(int, int)>>, Ghost<Seq<(int, int)>>)>, WorkerFailure>)
    requires ctx_ok(c), cols_ok(*k, c), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(Some((po, to, pr, tr))) ==> pre_parts_ok(c, po@, pr@) && tag_parts_ok(c, to@, tr@),
{
    proof {
        lemma_text_cols_wf(c);
    }
    let m = k.ptag.offsets.len() - 1;
    let nt = k.ttag.offsets.len() - 1;
    let tasks = workers;
    let pchunk = m / tasks + 1;
    let tchunk = nt / tasks + 1;
    let mut list: Vec<SplitTask> = Vec::new();
    let ghost mut prng: Seq<(int, int)> = Seq::empty();
    let ghost mut trng: Seq<(int, int)> = Seq::empty();
    let mut plo: usize = 0;
    let mut tlo: usize = 0;
    let mut t: usize = 0;
    while t < tasks
        invariant
            t <= tasks, tasks == workers, 1 <= workers <= MAX_WORKERS, ctx_ok(c), cols_ok(*k, c),
            m as int == c.m, nt as int == c.nt, plo <= m, tlo <= nt,
            list@.len() == t, prng.len() == t, trng.len() == t,
            forall|q: int| 0 <= q < t ==> (#[trigger] list@[q]).pre() && list@[q].c@ == c
                && list@[q].plo as int == prng[q].0 && list@[q].phi as int == prng[q].1
                && list@[q].tlo as int == trng[q].0 && list@[q].thi as int == trng[q].1,
            t == 0 ==> plo == 0 && tlo == 0,
            t > 0 ==> prng[0].0 == 0 && trng[0].0 == 0 && prng[t - 1].1 == plo && trng[t - 1].1 == tlo,
            forall|q: int| 0 < q < t ==> #[trigger] prng[q].0 == prng[q - 1].1,
            forall|q: int| 0 < q < t ==> #[trigger] trng[q].0 == trng[q - 1].1,
            forall|q: int| 0 <= q < t ==> #[trigger] prng[q].0 <= prng[q].1,
            forall|q: int| 0 <= q < t ==> #[trigger] trng[q].0 <= trng[q].1,
            t == tasks ==> plo == m && tlo == nt,
        decreases tasks - t,
    {
        let phi = next_hi(plo, m, pchunk, t, tasks);
        let thi = next_hi(tlo, nt, tchunk, t, tasks);
        let task = SplitTask {
            c: Ghost(c),
            ptag: tc(&k.ptag), pver: tc(&k.pver), padsh: tc(&k.padsh), plo, phi, pb: new_direct_bufs(phi - plo),
            ttag: tc(&k.ttag), tver: tc(&k.tver), tlo, thi, tb: new_bufs(thi - tlo),
        };
        list.push(task);
        proof {
            prng = prng.push((plo as int, phi as int));
            trng = trng.push((tlo as int, thi as int));
        }
        plo = phi;
        tlo = thi;
        t = t + 1;
    }
    let ghost tl = list@;
    let outs: Vec<SplitOut> = if tasks == 1 {
        let x = list.pop().unwrap();
        proof {
            assert(x == tl[0]);
        }
        let o = x.run();
        let mut v: Vec<SplitOut> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, list) {
            Ok(v) => v,
            Err(e) => return Err(e),
        }
    };
    let mut po: Vec<Parted> = Vec::new();
    let mut to: Vec<Parted> = Vec::new();
    let mut outs = outs;
    let ghost all = outs@;
    let mut q: usize = 0;
    while q < tasks
        invariant
            q <= tasks, tasks == tl.len(), all.len() == tasks,
            outs@ == all.subrange(q as int, tasks as int),
            forall|q2: int| 0 <= q2 < tasks ==> #[trigger] tl[q2].post(all[q2]),
            forall|q2: int| 0 <= q2 < tasks ==> (#[trigger] tl[q2]).c@ == c
                && tl[q2].plo as int == prng[q2].0 && tl[q2].phi as int == prng[q2].1
                && tl[q2].tlo as int == trng[q2].0 && tl[q2].thi as int == trng[q2].1,
            po@.len() == q, to@.len() == q,
            forall|q2: int| 0 <= q2 < q ==> #[trigger] parted_ok(po@[q2], pre_ks(c, prng[q2].0, prng[q2].1), pre_xs(c, prng[q2].0, prng[q2].1)),
            forall|q2: int| 0 <= q2 < q ==> #[trigger] parted_ok(to@[q2], tag_ks(c, trng[q2].0, trng[q2].1), tag_xs(c, trng[q2].0, trng[q2].1)),
        decreases tasks - q,
    {
        let o = outs.remove(0);
        proof {
            assert(o == all[q as int]);
            assert(outs@ =~= all.subrange(q + 1, tasks as int));
            assert(tl[q as int].post(all[q as int]));
        }
        let SplitOut { pre, tag } = o;
        match (pre, tag) {
            (Some(a), Some(b)) => {
                let ghost po0 = po@;
                let ghost to0 = to@;
                po.push(a);
                to.push(b);
                proof {
                    assert forall|q2: int| 0 <= q2 < q + 1 implies #[trigger] parted_ok(po@[q2], pre_ks(c, prng[q2].0, prng[q2].1), pre_xs(c, prng[q2].0, prng[q2].1)) by {
                        if q2 < q as int {
                            assert(po@[q2] == po0[q2]);
                        }
                    }
                    assert forall|q2: int| 0 <= q2 < q + 1 implies #[trigger] parted_ok(to@[q2], tag_ks(c, trng[q2].0, trng[q2].1), tag_xs(c, trng[q2].0, trng[q2].1)) by {
                        if q2 < q as int {
                            assert(to@[q2] == to0[q2]);
                        }
                    }
                }
            },
            _ => {
                return Ok(None);
            },
        }
        q = q + 1;
    }
    proof {
        assert(tiles(prng, c.m));
        assert(tiles(trng, c.nt));
    }
    Ok(Some((po, to, Ghost(prng), Ghost(trng))))
}

/// The number of items of segment `p` over all outputs (saturating).
fn seg_count(outs: &Vec<Parted>, p: usize) -> (n: usize)
    requires p < PARTS, forall|r: int| 0 <= r < outs@.len() ==> #[trigger] segs_ok(outs@[r]),
{
    let mut n: usize = 0;
    let mut r: usize = 0;
    while r < outs.len()
        invariant r <= outs@.len(), p < PARTS, forall|r2: int| 0 <= r2 < outs@.len() ==> #[trigger] segs_ok(outs@[r2]),
        decreases outs@.len() - r,
    {
        let o = &outs[r];
        proof {
            assert(segs_ok(outs@[r as int]));
            assert(o.starts@[p as int] <= o.ends@[p as int]);
        }
        let len = o.ends[p] - o.starts[p];
        n = if n <= usize::MAX - len { n + len } else { usize::MAX };
        r = r + 1;
    }
    n
}

/// Phase 2: the `pre` key hash pair set of every partition (`None`: a check or a table failed).
fn phase2(po: Vec<Parted>, to: Vec<Parted>, prng: Ghost<Seq<(int, int)>>, trng: Ghost<Seq<(int, int)>>, k: &Cols,
    workers: usize, dispatch: &mut Dispatch, Ghost(c): Ghost<Ctx>) -> (r: Result<Option<Vec<PairSet>>, WorkerFailure>)
    requires
        ctx_ok(c), cols_ok(*k, c), 1 <= workers <= MAX_WORKERS, fk_ok(c),
        pre_parts_ok(c, po@, prng@), tag_parts_ok(c, to@, trng@),
    ensures r matches Ok(Some(s)) ==> fast_ok(c, s@),
{
    proof {
        lemma_text_cols_wf(c);
        assert forall|r: int| 0 <= r < po@.len() implies #[trigger] segs_ok(po@[r]) by {
            assert(parted_ok(po@[r], pre_ks(c, prng@[r].0, prng@[r].1), pre_xs(c, prng@[r].0, prng@[r].1)));
        }
        assert forall|r: int| 0 <= r < to@.len() implies #[trigger] segs_ok(to@[r]) by {
            assert(parted_ok(to@[r], tag_ks(c, trng@[r].0, trng@[r].1), tag_xs(c, trng@[r].0, trng@[r].1)));
        }
    }
    let ns = k.sadsh.offsets.len() - 1;
    let nt = k.ttag.offsets.len() - 1;
    let tasks = workers;
    // Partitions per task, rounded up (the `pre` partitions are about equal in size).
    let chunk = (PARTS - 1) / tasks + 1;
    // Table sizes, per partition.
    let mut pmasks: Vec<u64> = Vec::new();
    let mut tmasks: Vec<u64> = Vec::new();
    let mut p: usize = 0;
    while p < PARTS
        invariant
            p <= PARTS, pmasks@.len() == p, tmasks@.len() == p,
            forall|r: int| 0 <= r < po@.len() ==> #[trigger] segs_ok(po@[r]),
            forall|r: int| 0 <= r < to@.len() ==> #[trigger] segs_ok(to@[r]),
            forall|q: int| 0 <= q < p ==> #[trigger] pmasks@[q] < MAX_CAP && tmasks@[q] < MAX_CAP,
        decreases PARTS - p,
    {
        let pm = mask_for(seg_count(&po, p));
        let tm = mask_for(seg_count(&to, p));
        pmasks.push(pm);
        tmasks.push(tm);
        p = p + 1;
    }
    let pre_arc = Arc::new(po);
    let tag_arc = Arc::new(to);
    let mut list: Vec<BuildTask> = Vec::new();
    let mut plo: usize = 0;
    let mut t: usize = 0;
    while t < tasks
        invariant
            t <= tasks, tasks == workers, 1 <= workers <= MAX_WORKERS, ctx_ok(c), cols_ok(*k, c),
            ns as int == c.ns, nt as int == c.nt, plo <= PARTS,
            pre_parts_ok(c, pre_arc@, prng@), tag_parts_ok(c, tag_arc@, trng@),
            pmasks@.len() == PARTS, tmasks@.len() == PARTS,
            forall|q: int| 0 <= q < PARTS ==> #[trigger] pmasks@[q] < MAX_CAP && tmasks@[q] < MAX_CAP,
            list@.len() == t,
            forall|q: int| 0 <= q < t ==> (#[trigger] list@[q]).pre() && list@[q].c@ == c,
            t == 0 ==> plo == 0,
            t > 0 ==> list@[0].plo == 0 && list@[t - 1].phi == plo && list@[0].sub is Some,
            forall|q: int| 0 < q < t ==> #[trigger] list@[q].plo == list@[q - 1].phi,
            t == tasks ==> plo == PARTS,
        decreases tasks - t,
    {
        let phi = next_hi(plo, PARTS, chunk, t, tasks);
        let mut sets: Vec<PairSet> = Vec::new();
        let mut dts: Vec<DistinctTable> = Vec::new();
        let mut q = plo;
        while q < phi
            invariant
                plo <= q <= phi <= PARTS, sets@.len() == q - plo, dts@.len() == q - plo, ctx_ok(c),
                pmasks@.len() == PARTS, tmasks@.len() == PARTS,
                forall|q2: int| 0 <= q2 < PARTS ==> #[trigger] pmasks@[q2] < MAX_CAP && tmasks@[q2] < MAX_CAP,
                sets_ready(sets@, c), dts_ready(dts@, c.nt),
            decreases phi - q,
        {
            proof {
                assert(pmasks@[q as int] < MAX_CAP && tmasks@[q as int] < MAX_CAP);
            }
            let s = new_set(pmasks[q]);
            let d = new_table(tmasks[q], Ghost(c.nt));
            let ghost sets0 = sets@;
            let ghost dts0 = dts@;
            sets.push(s);
            dts.push(d);
            proof {
                assert(set_sound(s, c));
                assert(sets_ready(sets0, c));
                assert(dts_ready(dts0, c.nt));
                assert forall|k2: int| #![trigger sets@[k2]] 0 <= k2 < sets@.len() implies set_wf(sets@[k2]) && set_sound(sets@[k2], c) by {
                    if k2 < sets0.len() {
                        assert(sets@[k2] == sets0[k2]);
                        assert(set_wf(sets0[k2]) && set_sound(sets0[k2], c));
                    }
                }
                assert forall|k2: int| #![trigger dts@[k2]] 0 <= k2 < dts@.len() implies dt_wf(dts@[k2], c.nt) by {
                    if k2 < dts0.len() {
                        assert(dts@[k2] == dts0[k2]);
                        assert(dt_wf(dts0[k2], c.nt));
                    }
                }
            }
            q = q + 1;
        }
        let sub = if t == 0 {
            let sm = mask_for(ns);
            Some(SubJob { sadsh: tc(&k.sadsh), ns, table: new_table(sm, Ghost(c.ns)) })
        } else {
            None
        };
        let task = BuildTask {
            c: Ghost(c), plo, phi, pre: pre_arc.clone(), prng, tag: tag_arc.clone(), trng,
            ttag: tc(&k.ttag), tver: tc(&k.tver), sets, dts, sub,
        };
        let ghost list0 = list@;
        list.push(task);
        proof {
            assert forall|q2: int| 0 <= q2 < t + 1 implies (#[trigger] list@[q2]).pre() && list@[q2].c@ == c by {
                if q2 < t as int {
                    assert(list@[q2] == list0[q2]);
                }
            }
        }
        plo = phi;
        t = t + 1;
    }
    let ghost tl = list@;
    let outs: Vec<BuildOut> = if tasks == 1 {
        let x = list.pop().unwrap();
        proof {
            assert(x == tl[0]);
        }
        let o = x.run();
        let mut v: Vec<BuildOut> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, list) {
            Ok(v) => v,
            Err(e) => return Err(e),
        }
    };
    let mut all: Vec<PairSet> = Vec::new();
    let mut outs = outs;
    let ghost allo = outs@;
    let mut q: usize = 0;
    while q < tasks
        invariant
            q <= tasks, tasks == tl.len(), allo.len() == tasks,
            outs@ == allo.subrange(q as int, tasks as int),
            forall|q2: int| 0 <= q2 < tasks ==> #[trigger] tl[q2].post(allo[q2]),
            forall|q2: int| 0 <= q2 < tasks ==> (#[trigger] tl[q2]).c@ == c,
            tl[0].plo == 0, tl[0].sub is Some,
            forall|q2: int| 0 < q2 < tasks ==> #[trigger] tl[q2].plo == tl[q2 - 1].phi,
            tl[tasks - 1].phi == PARTS,
            q == 0 ==> all@.len() == 0,
            q > 0 ==> all@.len() == tl[q - 1].phi && ad_injective(c),
            forall|p2: int| #![trigger all@[p2]] 0 <= p2 < all@.len() ==> pre_set_ok(all@[p2], c, p2) && tag_part_inj(c, p2),
        decreases tasks - q,
    {
        let o = outs.remove(0);
        proof {
            assert(o == allo[q as int]);
            assert(outs@ =~= allo.subrange(q + 1, tasks as int));
            assert(tl[q as int].post(allo[q as int]));
        }
        let BuildOut { sets, ok } = o;
        if !ok {
            return Ok(None);
        }
        let ghost all0 = all@;
        let ghost osets = sets@;
        let mut sets = sets;
        proof {
            assert(built_ok(c, tl[q as int].plo as int, osets));
            if q > 0 {
                assert(tl[q as int].plo == tl[q - 1].phi);
            }
        }
        all.append(&mut sets);
        proof {
            assert forall|p2: int| #![trigger all@[p2]] 0 <= p2 < all@.len() implies pre_set_ok(all@[p2], c, p2) && tag_part_inj(c, p2) by {
                if p2 < all0.len() {
                    assert(all@[p2] == all0[p2]);
                } else {
                    let kk = p2 - all0.len();
                    assert(all@[p2] == osets[kk]);
                    assert(pre_set_ok(osets[kk], c, tl[q as int].plo + kk) && tag_part_inj(c, tl[q as int].plo + kk));
                }
            }
        }
        q = q + 1;
    }
    proof {
        assert(all@.len() == PARTS);
        assert forall|a: int, b: int| 0 <= a < c.nt && 0 <= b < c.nt && #[trigger] tag_tv(c, a) == #[trigger] tag_tv(c, b)
            implies ttag(c, a) == ttag(c, b) && tver(c, a) == tver(c, b) by {
            let h = tag_tv(c, a);
            assert((h >> 56u64) < 256u64) by (bit_vector);
            let p2 = part_of(h);
            assert(pre_set_ok(all@[p2], c, p2) && tag_part_inj(c, p2));
        }
        assert forall|p2: int| #![trigger all@[p2]] 0 <= p2 < PARTS implies pre_set_ok(all@[p2], c, p2) by {}
    }
    Ok(Some(all))
}

/// The most tasks of phases 1 and 2.
pub const BUILD_TASKS: usize = 32;

/// Output slots per scan task in the first attempt (the kept rows are few); a full buffer retries with room for
/// every row.
pub const SCAN_CAP: usize = 0x1000;

/// Phase 3: the kept `num` rows, in row order (`None`: a task's buffer of `cap_limit` slots filled up). The chunks
/// are dealt round-robin to the tasks (`deal`); the caller concatenates the tasks' chunk segments in chunk order.
fn phase3(k: &Cols, pv: &'static [u8], dlo: i64, dhi: i64, sets: &Option<Arc<Vec<PairSet>>>, workers: usize,
    cap_limit: usize, dispatch: &mut Dispatch, Ghost(c): Ghost<Ctx>) -> (r: Result<Option<Vec<usize>>, WorkerFailure>)
    requires
        ctx_ok(c), cols_ok(*k, c), 1 <= workers <= MAX_WORKERS,
        pv@ == c.pv, dlo as int == c.dlo, dhi as int == c.dhi,
        sets matches Some(s) ==> fast_ok(c, s@),
    ensures
        r matches Ok(Some(u)) ==> u@ == kept(c, 0, c.n),
        cap_limit == usize::MAX ==> !(r matches Ok(None)),
{
    proof {
        lemma_text_cols_wf(c);
    }
    let n = k.ddate.len();
    let m = k.ptag.offsets.len() - 1;
    let plen = pv.len();
    let tasks = workers;
    let nch = n / CHUNK + 1;
    proof {
        assert(nch * CHUNK <= n + CHUNK && nch * CHUNK > n) by (nonlinear_arith) requires nch == n / CHUNK + 1, CHUNK == 0x4000;
    }
    let (lists, owner, slot) = deal(nch, tasks, Ghost(n as int));
    let ghost gl = lists@.map_values(|l: Vec<usize>| l@);
    let mut lists = lists;
    let mut list: Vec<ScanTask> = Vec::new();
    let cap = if cap_limit < n { cap_limit } else { n };
    let mut t: usize = 0;
    while t < tasks
        invariant
            t <= tasks, tasks == workers, 1 <= workers <= MAX_WORKERS, ctx_ok(c), cols_ok(*k, c),
            n as int == c.n, m as int == c.m, plen == pv@.len(), nch * CHUNK <= n + CHUNK,
            pv@ == c.pv, dlo as int == c.dlo, dhi as int == c.dhi,
            sets matches Some(s) ==> fast_ok(c, s@),
            cap_limit == usize::MAX ==> cap == n,
            gl.len() == tasks, lists@.len() == tasks - t,
            forall|t2: int| 0 <= t2 < tasks - t ==> (#[trigger] lists@[t2])@ == gl[t + t2],
            forall|t2: int| 0 <= t2 < tasks ==> #[trigger] chunks_ok(gl[t2], nch as int, c.n),
            list@.len() == t,
            forall|q: int| 0 <= q < t ==> (#[trigger] list@[q]).pre() && list@[q].c@ == c && list@[q].gs@ == gl[q]
                && list@[q].n == n,
            forall|q: int| 0 <= q < t ==> cap_limit == usize::MAX ==> (#[trigger] list@[q]).out.capacity() >= n,
        decreases tasks - t,
    {
        let ghost l0 = lists@;
        let gs = lists.remove(0);
        proof {
            assert(l0[0]@ == gl[t as int]);
            assert(gs@ == gl[t as int]);
            assert forall|t2: int| 0 <= t2 < tasks - t - 1 implies (#[trigger] lists@[t2])@ == gl[t + 1 + t2] by {
                assert(lists@[t2] == l0[t2 + 1]);
                assert(l0[t2 + 1]@ == gl[t + (t2 + 1)]);
            }
        }
        let s2 = match sets {
            Some(s) => Some(s.clone()),
            None => None,
        };
        let nj = gs.len();
        let task = ScanTask {
            c: Ghost(c), gs, nch, n,
            ntag: tc(&k.ntag), nver: tc(&k.nver), nadsh: tc(&k.nadsh), nuom: tc(&k.nuom), ddate: k.ddate,
            pv, plen, dlo, dhi,
            sets: s2, ptag: tc(&k.ptag), pver: tc(&k.pver), padsh: tc(&k.padsh), m,
            out: TaskBuffer::new(cap, 0usize), ends: vec![0usize; nj],
            bk: vec![0u64; BATCH], bx: vec![0u64; BATCH], brow: vec![0usize; BATCH], bh: vec![0u64; BATCH],
        };
        let ghost list0 = list@;
        list.push(task);
        proof {
            assert forall|q2: int| 0 <= q2 < t + 1 implies (#[trigger] list@[q2]).pre() && list@[q2].c@ == c
                && list@[q2].gs@ == gl[q2] && list@[q2].n == n by {
                if q2 < t as int {
                    assert(list@[q2] == list0[q2]);
                }
            }
            assert forall|q2: int| 0 <= q2 < t + 1 && cap_limit == usize::MAX implies (#[trigger] list@[q2]).out.capacity() >= n by {
                if q2 < t as int {
                    assert(list@[q2] == list0[q2]);
                }
            }
        }
        t = t + 1;
    }
    let ghost tl = list@;
    let outs: Vec<ScanOut> = if tasks == 1 {
        let x = list.pop().unwrap();
        proof {
            assert(x == tl[0]);
        }
        let o = x.run();
        let mut v: Vec<ScanOut> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, list) {
            Ok(v) => v,
            Err(e) => return Err(e),
        }
    };
    // Every task's segments, as plain vectors.
    let mut rows: Vec<Vec<usize>> = Vec::new();
    let mut ends: Vec<Vec<usize>> = Vec::new();
    let mut outs = outs;
    let ghost allo = outs@;
    let mut q: usize = 0;
    while q < tasks
        invariant
            q <= tasks, tasks == tl.len(), allo.len() == tasks, gl.len() == tasks,
            outs@ == allo.subrange(q as int, tasks as int),
            forall|q2: int| 0 <= q2 < tasks ==> #[trigger] tl[q2].post(allo[q2]),
            forall|q2: int| 0 <= q2 < tasks ==> (#[trigger] tl[q2]).c@ == c && tl[q2].gs@ == gl[q2] && tl[q2].n == n,
            forall|q2: int| 0 <= q2 < tasks ==> cap_limit == usize::MAX ==> (#[trigger] tl[q2]).out.capacity() >= n,
            n as int == c.n,
            rows@.len() == q, ends@.len() == q,
            forall|q2: int| 0 <= q2 < q ==> #[trigger] segs_hold(c, rows@[q2]@, ends@[q2]@, gl[q2], gl[q2].len() as int),
        decreases tasks - q,
    {
        let o = outs.remove(0);
        proof {
            assert(o == allo[q as int]);
            assert(outs@ =~= allo.subrange(q + 1, tasks as int));
            assert(tl[q as int].post(allo[q as int]));
        }
        let ScanOut { rows: rb, ends: e, full } = o;
        if full {
            return Ok(None);
        }
        let v = rb.into_vec();
        let ghost rows0 = rows@;
        let ghost ends0 = ends@;
        rows.push(v);
        ends.push(e);
        proof {
            assert forall|q2: int| 0 <= q2 < q + 1 implies #[trigger] segs_hold(c, rows@[q2]@, ends@[q2]@, gl[q2], gl[q2].len() as int) by {
                if q2 < q as int {
                    assert(rows@[q2] == rows0[q2]);
                    assert(ends@[q2] == ends0[q2]);
                }
            }
        }
        q = q + 1;
    }
    // Concatenate the segments in chunk order.
    let mut u: Vec<usize> = Vec::new();
    let mut g: usize = 0;
    proof {
        assert(kept(c, 0, chunk_lo(0, c.n)) =~= Seq::<usize>::empty());
    }
    while g < nch
        invariant
            g <= nch, nch * CHUNK <= n + CHUNK, nch * CHUNK > n, n as int == c.n, gl.len() == tasks,
            rows@.len() == tasks, ends@.len() == tasks,
            forall|q2: int| 0 <= q2 < tasks ==> #[trigger] segs_hold(c, rows@[q2]@, ends@[q2]@, gl[q2], gl[q2].len() as int),
            dealt(gl, owner@, slot@, nch as int, tasks as int),
            u@ == kept(c, 0, chunk_lo(g as int, c.n)),
        decreases nch - g,
    {
        let t = owner[g];
        let j = slot[g];
        proof {
            assert(segs_hold(c, rows@[t as int]@, ends@[t as int]@, gl[t as int], gl[t as int].len() as int));
            assert(seg_ok(c, rows@[t as int]@, ends@[t as int]@, gl[t as int], j as int));
        }
        let rv = &rows[t];
        let ev = &ends[t];
        let s = if j == 0 { 0 } else { ev[j - 1] };
        let e = ev[j];
        let ghost u0 = u@;
        let mut x = s;
        while x < e
            invariant
                s <= x <= e <= rv@.len(), u@ == u0 + rv@.subrange(s as int, x as int),
            decreases e - x,
        {
            u.push(rv[x]);
            proof {
                assert(u0 + rv@.subrange(s as int, x + 1) =~= (u0 + rv@.subrange(s as int, x as int)).push(rv@[x as int]));
            }
            x = x + 1;
        }
        proof {
            assert(rv@.subrange(s as int, e as int) == chunk_kept(c, g as int));
            lemma_kept_split(c, 0, chunk_lo(g as int, c.n), chunk_hi(g as int, c.n));
        }
        g = g + 1;
    }
    proof {
        assert(chunk_lo(nch as int, c.n) == c.n);
    }
    Ok(Some(u))
}

/// Chunk `g < nch` is slot `slot[g]` of the chunk list `gl[owner[g]]`.
pub open spec fn dealt(gl: Seq<Seq<usize>>, owner: Seq<usize>, slot: Seq<usize>, nch: int, w: int) -> bool {
    &&& owner.len() == nch && slot.len() == nch
    &&& forall|g: int| 0 <= g < nch ==> #[trigger] owner[g] < w && (slot[g] as int) < gl[owner[g] as int].len()
            && gl[owner[g] as int][slot[g] as int] == g
}

/// The chunks `0..nch` dealt round-robin to `w` lists (increasing in each list), with the owner and slot of
/// every chunk.
fn deal(nch: usize, w: usize, Ghost(n): Ghost<int>) -> (r: (Vec<Vec<usize>>, Vec<usize>, Vec<usize>))
    requires 1 <= w, nch * CHUNK <= n + CHUNK,
    ensures
        r.0@.len() == w,
        forall|t: int| 0 <= t < w ==> #[trigger] chunks_ok(r.0@[t]@, nch as int, n),
        dealt(r.0@.map_values(|l: Vec<usize>| l@), r.1@, r.2@, nch as int, w as int),
{
    let mut lists: Vec<Vec<usize>> = Vec::new();
    let mut t: usize = 0;
    while t < w
        invariant t <= w, lists@.len() == t, forall|t2: int| 0 <= t2 < t ==> (#[trigger] lists@[t2])@.len() == 0,
        decreases w - t,
    {
        lists.push(Vec::new());
        t = t + 1;
    }
    let mut owner: Vec<usize> = Vec::new();
    let mut slot: Vec<usize> = Vec::new();
    let mut t: usize = 0;
    let mut g: usize = 0;
    while g < nch
        invariant
            g <= nch, t < w, lists@.len() == w, owner@.len() == g, slot@.len() == g, nch * CHUNK <= n + CHUNK,
            forall|g2: int| 0 <= g2 < g ==> #[trigger] owner@[g2] < w && (slot@[g2] as int) < lists@[owner@[g2] as int]@.len()
                && lists@[owner@[g2] as int]@[slot@[g2] as int] == g2,
            forall|t2: int, j2: int| 0 <= t2 < w && 0 <= j2 < lists@[t2]@.len() ==> #[trigger] lists@[t2]@[j2] < g,
            forall|t2: int, j2: int| 0 <= t2 < w && 0 < j2 < lists@[t2]@.len() ==> #[trigger] lists@[t2]@[j2 - 1] < lists@[t2]@[j2],
        decreases nch - g,
    {
        let ghost l0 = lists@;
        let s = lists[t].len();
        lists[t].push(g);
        owner.push(t);
        slot.push(s);
        proof {
            assert forall|t2: int| 0 <= t2 < w && t2 != t implies #[trigger] lists@[t2] == l0[t2] by {}
            assert(lists@[t as int]@ == l0[t as int]@.push(g));
        }
        g = g + 1;
        t = if t + 1 == w { 0 } else { t + 1 };
    }
    let ghost gl = lists@.map_values(|l: Vec<usize>| l@);
    proof {
        assert forall|t2: int| 0 <= t2 < w implies #[trigger] chunks_ok(lists@[t2]@, nch as int, n) by {
            assert forall|j: int| 0 <= j < lists@[t2]@.len() implies #[trigger] lists@[t2]@[j] < nch by {}
            assert forall|j: int| 0 < j < lists@[t2]@.len() implies #[trigger] lists@[t2]@[j - 1] < lists@[t2]@[j] by {}
        }
        assert forall|g2: int| 0 <= g2 < nch implies #[trigger] owner@[g2] < w && (slot@[g2] as int) < gl[owner@[g2] as int].len()
            && gl[owner@[g2] as int][slot@[g2] as int] == g2 by {
            assert(gl[owner@[g2] as int] == lists@[owner@[g2] as int]@);
        }
    }
    (lists, owner, slot)
}

/// The kept rows of `lo..mid` then `mid..hi`.
pub proof fn lemma_kept_split(c: Ctx, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures kept(c, lo, mid) + kept(c, mid, hi) == kept(c, lo, hi),
{
    lemma_keep_range_split(c, lo, mid, hi);
    assert(kept(c, lo, mid) + kept(c, mid, hi) =~= kept(c, lo, hi));
}

/// The value part has at most `usize::MAX / 16` rows: no group count leaves int8.
fn rows_bound(value: &'static [i128]) -> (n: usize)
    ensures n == value@.len(), n <= int8_max(),
{
    let sz = core::mem::size_of_val::<[i128]>(value);
    proof {
        broadcast use vstd::layout::layout_of_slices;
        broadcast use vstd::layout::layout_of_primitives;
        assert(sz as int == value@.len() * 16);
    }
    value.len()
}

/// The produced rows are an allowed output on every database bound to the parts.
proof fn lemma_final(sv: crate::gendb_entry::stores::StoresView, c: Ctx, ps: Seq<crate::spec::ast::Literal>,
    u: Seq<usize>, reps: Seq<usize>, cnts: Seq<u64>, sums: Seq<i128>, masses: Seq<u128>, h: Seq<usize>, o: Seq<usize>,
    out: Vec<Vec<EVal>>)
    requires
        ctx_ok(c), lits_ok(c, ps), c.n <= usize::MAX, c.n <= int8_max(),
        c.np == sv.flat_num, c.pp == sv.flat_pre, c.sp == sv.flat_sub, c.tp == sv.flat_tag,
        u == kept(c, 0, c.n),
        groups_ok(c, xr(c, u), reps, cnts, sums, masses),
        reps.len() <= usize::MAX,
        h == hsel(cnts, cnts.len() as int),
        forall|q: int| 0 <= q < h.len() ==> (#[trigger] h[q] as int) < cnts.len(),
        rows_of(grows(c, reps, cnts, sums), o) == sort_rows_of(c, reps, cnts, sums, h),
        view_rows(out@) == rows_of(grows(c, reps, cnts, sums), o).take(if o.len() < 100 { o.len() as int } else { 100 }),
    ensures
        crate::gendb_entry::answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Rows(out))),
{
    assert forall|db2: Database| #[trigger] crate::gendb_entry::bound_db(sv, db2) implies
        crate::gendb_entry::outcome_ok(db2, crate::query::query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(out))) by {
        lemma_bound_ctx(sv, db2, c);
        lemma_answer(db2, c, ps, u, reps, cnts, sums, masses, h, o, view_rows(out@));
    }
}

pub open spec fn sort_rows_of(c: Ctx, reps: Seq<usize>, cnts: Seq<u64>, sums: Seq<i128>, h: Seq<usize>) -> Seq<Row> {
    crate::spec::order::sort_rows(crate::agent::sem::order_keys(), rows_of(grows(c, reps, cnts, sums), h))
}

#[verifier::spinoff_prover]
pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        crate::gendb_entry::stores_ready(old(stores)@),
        crate::query::param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        crate::gendb_entry::answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost db = choose|db: Database| #[trigger] crate::gendb_entry::bound_db(stores@, db);
    let ghost nrels = crate::stores::flat_num::declaration::stored_relations(db);
    let ghost prels = crate::stores::flat_pre::declaration::stored_relations(db);
    let ghost srels = crate::stores::flat_sub::declaration::stored_relations(db);
    let ghost trels = crate::stores::flat_tag::declaration::stored_relations(db);
    let n = ni::stored_rows(&stores.flat_num, Ghost(nrels));
    let m = pi::stored_rows(&stores.flat_pre, Ghost(prels));
    let ns = si::stored_rows(&stores.flat_sub, Ghost(srels));
    let nt = ti::stored_rows(&stores.flat_tag, Ghost(trels));
    let pv: &'static [u8] = params.p0;
    let dlo = params.p1;
    let dhi = params.p2;
    let ghost c = Ctx {
        np: stores@.flat_num, n: n as int, pp: stores@.flat_pre, m: m as int,
        sp: stores@.flat_sub, ns: ns as int, tp: stores@.flat_tag, nt: nt as int,
        pv: pv@, dlo: dlo as int, dhi: dhi as int,
    };
    proof {
        lemma_bound(sv, db, c);
        lemma_fk(db, c);
        lemma_lits(params@, c, pv@, dlo as int, dhi as int);
    }
    let k = read_cols(stores, Ghost(c));
    let nb = rows_bound(k.value);
    proof {
        lemma_text_cols_wf(c);
        assert(nb as int == c.n);
    }
    // Phases 1 and 2: the `pre` key hash pair sets, when every check passed. They allocate and fill about
    // 400 MB, so at most `BUILD_TASKS` tasks run them (more contend on page faults without speeding them up).
    let build_tasks = if workers < BUILD_TASKS { workers } else { BUILD_TASKS };
    let mut sets: Option<Arc<Vec<PairSet>>> = None;
    match phase1(&k, build_tasks, dispatch, Ghost(c)) {
        Err(e) => return Err(QueryError::WorkerFailed(e)),
        Ok(None) => {},
        Ok(Some((po, to, prng, trng))) => {
            match phase2(po, to, prng, trng, &k, build_tasks, dispatch, Ghost(c)) {
                Err(e) => return Err(QueryError::WorkerFailed(e)),
                Ok(None) => {},
                Ok(Some(all)) => {
                    sets = Some(Arc::new(all));
                },
            }
        },
    }
    // Phase 3: the kept rows (retried with room for every row when a task's buffer filled up).
    let u = match phase3(&k, pv, dlo, dhi, &sets, workers, SCAN_CAP, dispatch, Ghost(c)) {
        Err(e) => return Err(QueryError::WorkerFailed(e)),
        Ok(Some(u)) => u,
        Ok(None) => match phase3(&k, pv, dlo, dhi, &sets, 1, usize::MAX, dispatch, Ghost(c)) {
            Err(e) => return Err(QueryError::WorkerFailed(e)),
            Ok(Some(u)) => u,
            Ok(None) => vstd::pervasive::unreached(),
        },
    };
    proof {
        lemma_keep_range_elems(c, 0, c.n);
        assert forall|q: int| 0 <= q < u@.len() implies (#[trigger] u@[q] as int) < c.n && keep(c, u@[q] as int) by {
            assert(u@[q] as int == keep_range(c, 0, c.n)[q]);
        }
    }
    // Group, HAVING, ORDER BY, LIMIT.
    let (reps, cnts, sums, masses) = match group_rows(&u, &k.ntag, &k.nver, k.value, Ghost(c)) {
        Ok(gr) => gr,
        Err(key) => {
            proof {
                crate::agent::cap::lemma_capacity_all(sv, c, params@, u@, key@);
            }
            return Ok(Answer::Capacity);
        },
    };
    let ghost xs = xr(c, u@);
    let nreps = reps.len();
    proof {
        assert(nreps == reps@.len());
        lemma_groups_reps(c, xs, reps@, cnts@, sums@, masses@);
        lemma_having_groups(c, xs, reps@, cnts@, sums@, masses@);
    }
    let h = having_idx(&cnts);
    proof {
        lemma_having_rows(grows(c, reps@, cnts@, sums@), cnts@, cnts@.len() as int);
    }
    let o = sort_idx(&h, &cnts, Ghost(grows(c, reps@, cnts@, sums@)));
    let lim = if o.len() < 100 { o.len() } else { 100 };
    proof {
        lemma_keep_range_len(c, 0, c.n);
        assert forall|t: int| 0 <= t < reps@.len() implies (#[trigger] reps@[t] as int) < c.n && cnts@[t] <= i64::MAX by {
            lemma_groups_at(c, xs, reps@, cnts@, sums@, masses@, t);
            lemma_gcount_le(crate::agent::sem::nf(c), xs, crate::link::query::gkeys(crate::agent::sem::nf(c), xs)[t]);
        }
    }
    let out = out_rows(&o, lim, &reps, &cnts, &sums, &k.ntag, &k.nver, Ghost(c));
    proof {
        lemma_final(sv, c, params@, u@, reps@, cnts@, sums@, masses@, h@, o@, out);
    }
    Ok(Answer::Rows(out))
}

} // verus!
