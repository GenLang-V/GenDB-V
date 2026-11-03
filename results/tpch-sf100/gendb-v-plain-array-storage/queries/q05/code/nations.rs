//! The nation tables, computed serially from the (small) `region` and `nation` tables: whether each nation lies in a
//! region named `$1`, its group id (one group per distinct `n_name` among those nations, first occurrence first,
//! `reps[g]` the first nation of group `g`), and, while fewer than 253 nations lie in the region, a one-byte slot
//! per such nation (`fast`; otherwise the query runs in its slow mode, which needs no slots).
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::work::{text_bytes, text_eq};
use crate::link::query::{text_at, text_wf};
use crate::agent::model::*;
use crate::agent::contrib::*;
use crate::agent::cols::*;

verus! {

/// Most slots the fast mode uses (slot values stay below `SLOW = NONE - 1`).
pub const MAX_SLOTS: usize = 253;

/// Byte equality of two slices.
pub fn bytes_eq(x: &[u8], y: &[u8]) -> (r: bool)
    ensures r == (x@ == y@),
{
    if x.len() != y.len() {
        return false;
    }
    let n = x.len();
    let mut k: usize = 0;
    while k < n
        invariant n == x@.len(), n == y@.len(), k <= n, forall|i: int| 0 <= i < k ==> x@[i] == y@[i],
        decreases n - k,
    {
        if x[k] != y[k] {
            return false;
        }
        k = k + 1;
    }
    assert(x@ =~= y@);
    true
}

pub struct NationTabs {
    pub inreg: Vec<bool>,
    pub gids: Vec<usize>,
    pub reps: Vec<usize>,
    pub slots: Vec<u8>,
    pub gos: Vec<usize>,
    pub fast: bool,
}

/// `nation_ok` over the first `n` nations.
pub open spec fn nation_prefix(sv: StoresView, rp: Seq<u8>, inregv: Seq<bool>, gids: Seq<usize>, reps: Seq<usize>, n: int) -> bool {
    &&& inregv.len() == n
    &&& gids.len() == n
    &&& reps.len() <= n
    &&& forall|e: int| 0 <= e < n ==> #[trigger] inregv[e] == inreg(sv, rp, e)
    &&& forall|e: int| 0 <= e < n && inreg(sv, rp, e) ==> #[trigger] gids[e] < reps.len()
    &&& forall|e1: int, e2: int| 0 <= e1 < n && 0 <= e2 < n && inreg(sv, rp, e1) && inreg(sv, rp, e2)
        ==> (#[trigger] gids[e1] == #[trigger] gids[e2] <==> n_name(sv, e1) == n_name(sv, e2))
    &&& forall|g: int| 0 <= g < reps.len() ==> #[trigger] reps[g] < n && inreg(sv, rp, reps[g] as int) && gids[reps[g] as int] == g
}

/// `slots_ok` over the first `n` nations.
pub open spec fn slots_prefix(sv: StoresView, rp: Seq<u8>, gids: Seq<usize>, slots: Seq<u8>, gos: Seq<usize>, n: int) -> bool {
    &&& slots.len() == n
    &&& gos.len() <= MAX_SLOTS
    &&& forall|e: int| 0 <= e < n ==> (#[trigger] slots[e] != NONE <==> inreg(sv, rp, e))
    &&& forall|e: int| 0 <= e < n && inreg(sv, rp, e) ==> (#[trigger] slots[e] as int) < gos.len() && gos[slots[e] as int] == gids[e]
    &&& forall|e1: int, e2: int| 0 <= e1 < n && 0 <= e2 < n && #[trigger] slots[e1] == #[trigger] slots[e2] && slots[e1] != NONE ==> e1 == e2
}

/// Whether region row `f` is named `rp`.
fn region_named(c: &Cols, f: usize, rp: &[u8], Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires cols_ok(*c, sv), stores_wf(sv), f < c.nr,
    ensures r == (r_name(sv, f as int) == rp@),
{
    assert(text_wf(c.rname@, c.nr as int));
    let name = text_bytes(&c.rname, f);
    bytes_eq(name, rp)
}

/// Whether nation row `e` lies in a region named `rp`.
fn nation_in_region(c: &Cols, e: usize, rp: &[u8], Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires cols_ok(*c, sv), stores_wf(sv), e < c.nn,
    ensures r == inreg(sv, rp@, e as int),
{
    let mut f: usize = 0;
    let mut found = false;
    while f < c.nr
        invariant
            cols_ok(*c, sv), stores_wf(sv), e < c.nn, f <= c.nr,
            found == exists|x: int| 0 <= x < f && #[trigger] r_rk(sv)[x] == n_rk(sv)[e as int] && r_name(sv, x) == rp@,
        decreases c.nr - f,
    {
        if !found && c.rkeys[f] == c.nrk[e] && region_named(c, f, rp, Ghost(sv)) {
            found = true;
        }
        proof {
            if !found {
                assert forall|x: int| 0 <= x < f + 1 implies !(#[trigger] r_rk(sv)[x] == n_rk(sv)[e as int] && r_name(sv, x) == rp@) by {
                    if x == f {
                    }
                }
            }
        }
        f = f + 1;
    }
    found
}

/// The group of nation `e` among the representatives `reps`: the first with `e`'s name, or `reps.len()` if none.
fn find_group(c: &Cols, reps: &Vec<usize>, e: usize, Ghost(sv): Ghost<StoresView>) -> (gid: usize)
    requires
        cols_ok(*c, sv), text_wf(c.nname@, c.nn as int), e < c.nn,
        forall|x: int| 0 <= x < reps@.len() ==> #[trigger] reps@[x] < e,
    ensures
        gid <= reps@.len(),
        gid == reps@.len() ==> forall|x: int| 0 <= x < reps@.len() ==> n_name(sv, #[trigger] reps@[x] as int) != n_name(sv, e as int),
        gid < reps@.len() ==> n_name(sv, reps@[gid as int] as int) == n_name(sv, e as int),
{
    let nreps = reps.len();
    let mut gid = nreps;
    let mut g: usize = 0;
    while g < nreps
        invariant
            cols_ok(*c, sv), text_wf(c.nname@, c.nn as int), e < c.nn,
            nreps == reps@.len(), g <= nreps,
            forall|x: int| 0 <= x < nreps ==> #[trigger] reps@[x] < e,
            gid == nreps ==> forall|x: int| 0 <= x < g ==> n_name(sv, #[trigger] reps@[x] as int) != n_name(sv, e as int),
            gid < nreps ==> gid < g && n_name(sv, reps@[gid as int] as int) == n_name(sv, e as int),
            gid <= nreps,
        decreases nreps - g,
    {
        if gid == nreps && text_eq(&c.nname, reps[g], &c.nname, e) {
            gid = g;
        }
        g = g + 1;
    }
    gid
}

/// One in-region nation `e` joins group `gid` (an existing group of its name, or a new one).
proof fn lemma_nation_in(sv: StoresView, rp: Seq<u8>, inregv: Seq<bool>, gids: Seq<usize>, reps: Seq<usize>, eu: usize, gid: usize,
    reps2: Seq<usize>)
    requires
        nation_prefix(sv, rp, inregv, gids, reps, eu as int),
        inreg(sv, rp, eu as int),
        gid <= reps.len(),
        gid == reps.len() ==> forall|x: int| 0 <= x < reps.len() ==> n_name(sv, #[trigger] reps[x] as int) != n_name(sv, eu as int),
        gid < reps.len() ==> n_name(sv, reps[gid as int] as int) == n_name(sv, eu as int),
        reps2 == if gid == reps.len() { reps.push(eu) } else { reps },
    ensures nation_prefix(sv, rp, inregv.push(true), gids.push(gid), reps2, eu as int + 1),
{
    let e = eu as int;
    let n = e + 1;
    let gids2 = gids.push(gid);
    let inregv2 = inregv.push(true);
    assert forall|x: int| 0 <= x < n implies #[trigger] inregv2[x] == inreg(sv, rp, x) by {
        if x < e { assert(inregv2[x] == inregv[x]); }
    }
    assert forall|x: int| 0 <= x < n && inreg(sv, rp, x) implies #[trigger] gids2[x] < reps2.len() by {
        if x < e { assert(gids2[x] == gids[x]); }
    }
    assert forall|x1: int, x2: int| 0 <= x1 < n && 0 <= x2 < n && inreg(sv, rp, x1) && inreg(sv, rp, x2)
        implies (#[trigger] gids2[x1] == #[trigger] gids2[x2] <==> n_name(sv, x1) == n_name(sv, x2)) by {
        if x1 < e && x2 == e {
            let g1 = gids[x1] as int;
            assert(gids2[x1] == gids[x1]);
            let r1 = reps[g1] as int;
            assert(gids[r1] == g1);
            assert(n_name(sv, x1) == n_name(sv, r1));
        } else if x1 == e && x2 < e {
            let g2 = gids[x2] as int;
            assert(gids2[x2] == gids[x2]);
            let r2 = reps[g2] as int;
            assert(gids[r2] == g2);
            assert(n_name(sv, x2) == n_name(sv, r2));
        } else if x1 < e && x2 < e {
            assert(gids2[x1] == gids[x1] && gids2[x2] == gids[x2]);
        }
    }
    assert forall|g2: int| 0 <= g2 < reps2.len() implies #[trigger] reps2[g2] < n && inreg(sv, rp, reps2[g2] as int)
        && gids2[reps2[g2] as int] == g2 by {
        if g2 < reps.len() {
            assert(reps2[g2] == reps[g2]);
        } else {
            assert(reps2[g2] == eu);
            assert(gids2[e] == gid);
        }
    }
}

/// One nation `e` outside the region.
proof fn lemma_nation_out(sv: StoresView, rp: Seq<u8>, inregv: Seq<bool>, gids: Seq<usize>, reps: Seq<usize>, e: int)
    requires nation_prefix(sv, rp, inregv, gids, reps, e), !inreg(sv, rp, e), 0 <= e,
    ensures nation_prefix(sv, rp, inregv.push(false), gids.push(0), reps, e + 1),
{
    let n = e + 1;
    let gids2 = gids.push(0);
    let inregv2 = inregv.push(false);
    assert forall|x: int| 0 <= x < n implies #[trigger] inregv2[x] == inreg(sv, rp, x) by {
        if x < e { assert(inregv2[x] == inregv[x]); }
    }
    assert forall|x: int| 0 <= x < n && inreg(sv, rp, x) implies #[trigger] gids2[x] < reps.len() by {
        assert(gids2[x] == gids[x]);
    }
    assert forall|x1: int, x2: int| 0 <= x1 < n && 0 <= x2 < n && inreg(sv, rp, x1) && inreg(sv, rp, x2)
        implies (#[trigger] gids2[x1] == #[trigger] gids2[x2] <==> n_name(sv, x1) == n_name(sv, x2)) by {
        assert(gids2[x1] == gids[x1] && gids2[x2] == gids[x2]);
    }
}

/// One in-region nation `e` gets the next slot.
proof fn lemma_slot_in(sv: StoresView, rp: Seq<u8>, gids: Seq<usize>, slots: Seq<u8>, gos: Seq<usize>, e: int, gid: usize)
    requires slots_prefix(sv, rp, gids, slots, gos, e), inreg(sv, rp, e), gos.len() < MAX_SLOTS, 0 <= e, gids.len() == e,
    ensures slots_prefix(sv, rp, gids.push(gid), slots.push(gos.len() as u8), gos.push(gid), e + 1),
{
    let n = e + 1;
    let (gids2, slots2, gos2) = (gids.push(gid), slots.push(gos.len() as u8), gos.push(gid));
    assert forall|x: int| 0 <= x < n implies (#[trigger] slots2[x] != NONE <==> inreg(sv, rp, x)) by {
        if x < e { assert(slots2[x] == slots[x]); }
    }
    assert forall|x: int| 0 <= x < n && inreg(sv, rp, x) implies (#[trigger] slots2[x] as int) < gos2.len()
        && gos2[slots2[x] as int] == gids2[x] by {
        if x < e {
            assert(slots2[x] == slots[x]);
            assert(gos2[slots2[x] as int] == gos[slots[x] as int]);
            assert(gids2[x] == gids[x]);
        }
    }
    assert forall|x1: int, x2: int| 0 <= x1 < n && 0 <= x2 < n && #[trigger] slots2[x1] == #[trigger] slots2[x2]
        && slots2[x1] != NONE implies x1 == x2 by {
        if x1 < e { assert(slots2[x1] == slots[x1]); }
        if x2 < e { assert(slots2[x2] == slots[x2]); }
    }
}

/// One nation `e` outside the region has no slot.
proof fn lemma_slot_out(sv: StoresView, rp: Seq<u8>, gids: Seq<usize>, slots: Seq<u8>, gos: Seq<usize>, e: int, gid: usize)
    requires slots_prefix(sv, rp, gids, slots, gos, e), !inreg(sv, rp, e), 0 <= e, gids.len() == e,
    ensures slots_prefix(sv, rp, gids.push(gid), slots.push(NONE), gos, e + 1),
{
    let n = e + 1;
    let (gids2, slots2) = (gids.push(gid), slots.push(NONE));
    assert forall|x: int| 0 <= x < n implies (#[trigger] slots2[x] != NONE <==> inreg(sv, rp, x)) by {
        if x < e { assert(slots2[x] == slots[x]); }
    }
    assert forall|x: int| 0 <= x < n && inreg(sv, rp, x) implies (#[trigger] slots2[x] as int) < gos.len()
        && gos[slots2[x] as int] == gids2[x] by {
        assert(slots2[x] == slots[x]);
        assert(gids2[x] == gids[x]);
    }
    assert forall|x1: int, x2: int| 0 <= x1 < n && 0 <= x2 < n && #[trigger] slots2[x1] == #[trigger] slots2[x2]
        && slots2[x1] != NONE implies x1 == x2 by {
        assert(slots2[x1] == slots[x1] || x1 == e);
        assert(slots2[x2] == slots[x2] || x2 == e);
    }
}

/// Computes the nation tables.
pub fn nation_tables(c: &Cols, rp: &[u8], Ghost(sv): Ghost<StoresView>) -> (r: NationTabs)
    requires cols_ok(*c, sv), stores_wf(sv), keys_ok(sv),
    ensures
        nation_ok(sv, rp@, r.inreg@, r.gids@, r.reps@),
        r.reps@.len() <= nn(sv),
        r.slots@.len() == nn(sv),
        r.fast ==> slots_ok(sv, rp@, r.gids@, r.slots@, r.gos@),
        forall|s: int| 0 <= s < r.gos@.len() ==> #[trigger] r.gos@[s] < r.reps@.len(),
{
    let mut inregv: Vec<bool> = Vec::new();
    let mut gids: Vec<usize> = Vec::new();
    let mut reps: Vec<usize> = Vec::new();
    let mut slots: Vec<u8> = Vec::new();
    let mut gos: Vec<usize> = Vec::new();
    let mut fast = true;
    assert(text_wf(c.nname@, c.nn as int));
    let mut e: usize = 0;
    while e < c.nn
        invariant
            cols_ok(*c, sv), stores_wf(sv), keys_ok(sv), e <= c.nn,
            text_wf(c.nname@, c.nn as int),
            nation_prefix(sv, rp@, inregv@, gids@, reps@, e as int),
            slots@.len() == e,
            fast ==> slots_prefix(sv, rp@, gids@, slots@, gos@, e as int),
            forall|s: int| 0 <= s < gos@.len() ==> #[trigger] gos@[s] < reps@.len(),
        decreases c.nn - e,
    {
        let inr = nation_in_region(c, e, rp, Ghost(sv));
        let ghost (iv0, g0, r0, s0, o0) = (inregv@, gids@, reps@, slots@, gos@);
        if inr {
            let gid = find_group(c, &reps, e, Ghost(sv));
            if gid == reps.len() {
                reps.push(e);
            }
            proof { lemma_nation_in(sv, rp@, iv0, g0, r0, e, gid, reps@); }
            inregv.push(true);
            gids.push(gid);
            if fast && gos.len() < MAX_SLOTS {
                proof { lemma_slot_in(sv, rp@, g0, s0, o0, e as int, gid); }
                let s = gos.len() as u8;
                slots.push(s);
                gos.push(gid);
            } else {
                fast = false;
                slots.push(NONE);
            }
        } else {
            proof {
                lemma_nation_out(sv, rp@, iv0, g0, r0, e as int);
                if fast { lemma_slot_out(sv, rp@, g0, s0, o0, e as int, 0); }
            }
            inregv.push(false);
            gids.push(0);
            slots.push(NONE);
        }
        e = e + 1;
    }
    NationTabs { inreg: inregv, gids, reps, slots, gos, fast }
}

} // verus!
