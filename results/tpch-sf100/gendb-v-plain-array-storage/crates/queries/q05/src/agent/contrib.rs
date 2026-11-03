//! The per-lineitem contributions in the terms the executable code computes them.
//!
//! Nations: `inreg(e)` (nation row `e` lies in a region named `$1`); every such nation has a group id
//! `gids[e] < ng` (equal ids exactly for equal names, `nation_ok`), and, in the fast mode, a one-byte slot
//! `slots[e]` (distinct per nation, `NONE` outside the region, `gos[slots[e]] == gids[e]`, `slots_ok`).
//! Customers and suppliers carry the slot of their nation key (`nslot`); an order row carries its *order code*
//! (`ord_code`): its customer's slot when its date lies in the year, `NONE` otherwise.
//!
//! The group term of lineitem row `c` for group `g` (`gterm`) is its revenue when `c` is a candidate whose nation
//! has group id `g`. A lineitem row whose order has a non-`NONE` code contributes exactly when its supplier's slot is
//! that code (`lemma_fast_entry`); a row with no such order contributes nothing (`lemma_no_code_order`). The group
//! sums over all lineitem rows are the normal form's sums of the group's key (`lemma_group_key_sums`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem_from::*;
use crate::agent::sem_pred::*;
use crate::agent::plan::*;

verus! {

/// The code of "no nation of the region".
pub const NONE: u8 = 255;

/// Nation row `e` lies in a region named `rp`.
pub open spec fn inreg(sv: StoresView, rp: Seq<u8>, e: int) -> bool {
    exists|f: int| 0 <= f < nr(sv) && #[trigger] r_rk(sv)[f] == n_rk(sv)[e] && r_name(sv, f) == rp
}

/// The nation tables: `inregv` decides `inreg`; in-region nations have group ids `< reps.len()`, equal exactly for
/// equal names; group `g`'s representative `reps[g]` is an in-region nation of group `g`.
pub open spec fn nation_ok(sv: StoresView, rp: Seq<u8>, inregv: Seq<bool>, gids: Seq<usize>, reps: Seq<usize>) -> bool {
    &&& inregv.len() == nn(sv)
    &&& gids.len() == nn(sv)
    &&& forall|e: int| 0 <= e < nn(sv) ==> #[trigger] inregv[e] == inreg(sv, rp, e)
    &&& forall|e: int| 0 <= e < nn(sv) && inreg(sv, rp, e) ==> #[trigger] gids[e] < reps.len()
    &&& forall|e1: int, e2: int| 0 <= e1 < nn(sv) && 0 <= e2 < nn(sv) && inreg(sv, rp, e1) && inreg(sv, rp, e2)
        ==> (#[trigger] gids[e1] == #[trigger] gids[e2] <==> n_name(sv, e1) == n_name(sv, e2))
    &&& forall|g: int| 0 <= g < reps.len() ==> #[trigger] reps[g] < nn(sv) && inreg(sv, rp, reps[g] as int) && gids[reps[g] as int] == g
}

/// The slot tables of the fast mode: one distinct slot below `NONE - 1` per in-region nation, `NONE` otherwise,
/// and `gos[slot]` the slot's group id.
pub open spec fn slots_ok(sv: StoresView, rp: Seq<u8>, gids: Seq<usize>, slots: Seq<u8>, gos: Seq<usize>) -> bool {
    &&& slots.len() == nn(sv)
    &&& gos.len() < NONE - 1
    &&& forall|e: int| 0 <= e < nn(sv) ==> (#[trigger] slots[e] != NONE <==> inreg(sv, rp, e))
    &&& forall|e: int| 0 <= e < nn(sv) && inreg(sv, rp, e) ==> (#[trigger] slots[e] as int) < gos.len() && gos[slots[e] as int] == gids[e]
    &&& forall|e1: int, e2: int| 0 <= e1 < nn(sv) && 0 <= e2 < nn(sv) && #[trigger] slots[e1] == #[trigger] slots[e2] && slots[e1] != NONE ==> e1 == e2
}

/// The slot of the nation with key `k` (`NONE` if there is none).
pub open spec fn nslot(sv: StoresView, slots: Seq<u8>, k: i64) -> u8 {
    if exists|e: int| 0 <= e < nn(sv) && #[trigger] n_nk(sv)[e] == k {
        slots[choose|e: int| 0 <= e < nn(sv) && #[trigger] n_nk(sv)[e] == k]
    } else {
        NONE
    }
}

/// The code of order row `j`: its customer's slot when its date lies in the year, `NONE` otherwise.
pub open spec fn ord_code(sv: StoresView, slots: Seq<u8>, pd: int, t: int, j: int) -> u8 {
    if date_in(o_date(sv)[j], pd, t) && exists|i: int| 0 <= i < nc(sv) && #[trigger] c_ck(sv)[i] == o_ck(sv)[j] {
        nslot(sv, slots, c_nk(sv)[choose|i: int| 0 <= i < nc(sv) && #[trigger] c_ck(sv)[i] == o_ck(sv)[j]])
    } else {
        NONE
    }
}

/// The contribution of lineitem row `c` to group `g`.
pub open spec fn gterm(sv: StoresView, rp: Seq<u8>, pd: int, t: int, gids: Seq<usize>, g: int, c: int) -> int {
    if cand(sv, rp, pd, t, c) && gids[cnation(sv, rp, pd, t, c)] == g { crev(sv, c) } else { 0 }
}

/// Group sums over lineitem rows `[lo, hi)`: revenue, row count, absolute revenue.
pub open spec fn gsum_r(sv: StoresView, rp: Seq<u8>, pd: int, t: int, gids: Seq<usize>, g: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { gsum_r(sv, rp, pd, t, gids, g, lo, hi - 1) + gterm(sv, rp, pd, t, gids, g, hi - 1) }
}

pub open spec fn gcnt_r(sv: StoresView, rp: Seq<u8>, pd: int, t: int, gids: Seq<usize>, g: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else {
        gcnt_r(sv, rp, pd, t, gids, g, lo, hi - 1)
            + if cand(sv, rp, pd, t, hi - 1) && gids[cnation(sv, rp, pd, t, hi - 1)] == g { 1int } else { 0int }
    }
}

pub open spec fn gabs_r(sv: StoresView, rp: Seq<u8>, pd: int, t: int, gids: Seq<usize>, g: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { gabs_r(sv, rp, pd, t, gids, g, lo, hi - 1) + abs(gterm(sv, rp, pd, t, gids, g, hi - 1)) }
}

// ------------------------------------------------------------------------------------------ range laws

/// Adjacent ranges add.
pub proof fn lemma_range_split(sv: StoresView, rp: Seq<u8>, pd: int, t: int, gids: Seq<usize>, g: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures
        gsum_r(sv, rp, pd, t, gids, g, lo, hi) == gsum_r(sv, rp, pd, t, gids, g, lo, mid) + gsum_r(sv, rp, pd, t, gids, g, mid, hi),
        gcnt_r(sv, rp, pd, t, gids, g, lo, hi) == gcnt_r(sv, rp, pd, t, gids, g, lo, mid) + gcnt_r(sv, rp, pd, t, gids, g, mid, hi),
        gabs_r(sv, rp, pd, t, gids, g, lo, hi) == gabs_r(sv, rp, pd, t, gids, g, lo, mid) + gabs_r(sv, rp, pd, t, gids, g, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_range_split(sv, rp, pd, t, gids, g, lo, mid, hi - 1);
    }
}

/// One more row at the end of a range.
pub proof fn lemma_range_step(sv: StoresView, rp: Seq<u8>, pd: int, t: int, gids: Seq<usize>, g: int, lo: int, hi: int)
    requires lo <= hi,
    ensures
        gsum_r(sv, rp, pd, t, gids, g, lo, hi + 1) == gsum_r(sv, rp, pd, t, gids, g, lo, hi) + gterm(sv, rp, pd, t, gids, g, hi),
        gcnt_r(sv, rp, pd, t, gids, g, lo, hi + 1) == gcnt_r(sv, rp, pd, t, gids, g, lo, hi)
            + if cand(sv, rp, pd, t, hi) && gids[cnation(sv, rp, pd, t, hi)] == g { 1int } else { 0int },
        gabs_r(sv, rp, pd, t, gids, g, lo, hi + 1) == gabs_r(sv, rp, pd, t, gids, g, lo, hi) + abs(gterm(sv, rp, pd, t, gids, g, hi)),
{
}

/// Absolute revenue bounds the revenue; counts and masses are non-negative; counts are at most the range length.
pub proof fn lemma_range_bounds(sv: StoresView, rp: Seq<u8>, pd: int, t: int, gids: Seq<usize>, g: int, lo: int, hi: int)
    ensures
        abs(gsum_r(sv, rp, pd, t, gids, g, lo, hi)) <= gabs_r(sv, rp, pd, t, gids, g, lo, hi),
        0 <= gcnt_r(sv, rp, pd, t, gids, g, lo, hi),
        lo <= hi ==> gcnt_r(sv, rp, pd, t, gids, g, lo, hi) <= hi - lo,
        gcnt_r(sv, rp, pd, t, gids, g, lo, hi) == 0 ==> gabs_r(sv, rp, pd, t, gids, g, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_range_bounds(sv, rp, pd, t, gids, g, lo, hi - 1);
    }
}

// ------------------------------------------------------------------------------------------ candidates

/// A candidate's nation lies in the region, and its tuple's order row has the lineitem's order key.
pub proof fn lemma_cand_facts(sv: StoresView, rp: Seq<u8>, pd: int, t: int, c: int)
    requires stores_wf(sv), keys_ok(sv), cand(sv, rp, pd, t, c),
    ensures ({
        let u = ctuple(sv, rp, pd, t, c);
        &&& in6(sv, u.0, u.1, c, u.2, u.3, u.4)
        &&& qual6(sv, rp, pd, t, u.0, u.1, c, u.2, u.3, u.4)
        &&& inreg(sv, rp, cnation(sv, rp, pd, t, c))
        &&& 0 <= cnation(sv, rp, pd, t, c) < nn(sv)
    }),
{
    lemma_ctuple(sv, rp, pd, t, c);
    let u = ctuple(sv, rp, pd, t, c);
    assert(r_rk(sv)[u.4] == n_rk(sv)[u.3]);
}

/// The slot of an in-region nation's key is that nation's slot.
pub proof fn lemma_nslot_of(sv: StoresView, rp: Seq<u8>, slots: Seq<u8>, e: int)
    requires stores_wf(sv), keys_ok(sv), 0 <= e < nn(sv),
    ensures nslot(sv, slots, n_nk(sv)[e]) == slots[e],
{
    let k = n_nk(sv)[e];
    assert(exists|e2: int| 0 <= e2 < nn(sv) && #[trigger] n_nk(sv)[e2] == k);
    let e2 = choose|e2: int| 0 <= e2 < nn(sv) && #[trigger] n_nk(sv)[e2] == k;
    assert(e2 == e);
}

/// A non-`NONE` slot of key `k` belongs to an in-region nation with key `k`.
pub proof fn lemma_nslot_some(sv: StoresView, rp: Seq<u8>, gids: Seq<usize>, slots: Seq<u8>, gos: Seq<usize>, k: i64)
    requires stores_wf(sv), keys_ok(sv), slots_ok(sv, rp, gids, slots, gos), nslot(sv, slots, k) != NONE,
    ensures
        exists|e: int| 0 <= e < nn(sv) && #[trigger] n_nk(sv)[e] == k && inreg(sv, rp, e) && slots[e] == nslot(sv, slots, k),
{
    let e = choose|e: int| 0 <= e < nn(sv) && #[trigger] n_nk(sv)[e] == k;
    assert(slots[e] != NONE);
}

/// The order code is not `NONE` exactly when the order's date lies in the year and its customer's nation lies in
/// the region; then the code is that nation's slot.
pub proof fn lemma_ord_code(sv: StoresView, rp: Seq<u8>, pd: int, t: int, gids: Seq<usize>, slots: Seq<u8>, gos: Seq<usize>, j: int)
    requires stores_wf(sv), keys_ok(sv), slots_ok(sv, rp, gids, slots, gos), 0 <= j < no(sv),
    ensures
        ord_code(sv, slots, pd, t, j) != NONE ==> exists|i: int, e: int|
            0 <= i < nc(sv) && 0 <= e < nn(sv) && #[trigger] c_ck(sv)[i] == o_ck(sv)[j] && #[trigger] n_nk(sv)[e] == c_nk(sv)[i]
            && inreg(sv, rp, e) && slots[e] == ord_code(sv, slots, pd, t, j) && date_in(o_date(sv)[j], pd, t),
{
    if ord_code(sv, slots, pd, t, j) != NONE {
        let i = choose|i: int| 0 <= i < nc(sv) && #[trigger] c_ck(sv)[i] == o_ck(sv)[j];
        lemma_nslot_some(sv, rp, gids, slots, gos, c_nk(sv)[i]);
        let e = choose|e: int| 0 <= e < nn(sv) && #[trigger] n_nk(sv)[e] == c_nk(sv)[i] && inreg(sv, rp, e)
            && slots[e] == nslot(sv, slots, c_nk(sv)[i]);
        assert(c_ck(sv)[i] == o_ck(sv)[j] && n_nk(sv)[e] == c_nk(sv)[i]);
    }
}

/// A candidate's order row has a non-`NONE` code, the slot of the candidate's nation.
pub proof fn lemma_cand_code(sv: StoresView, rp: Seq<u8>, pd: int, t: int, gids: Seq<usize>, slots: Seq<u8>, gos: Seq<usize>, c: int)
    requires stores_wf(sv), keys_ok(sv), slots_ok(sv, rp, gids, slots, gos), cand(sv, rp, pd, t, c),
    ensures ({
        let u = ctuple(sv, rp, pd, t, c);
        &&& o_ok(sv)[u.1] == l_ok(sv)[c]
        &&& 0 <= u.1 < no(sv)
        &&& ord_code(sv, slots, pd, t, u.1) == slots[cnation(sv, rp, pd, t, c)]
        &&& ord_code(sv, slots, pd, t, u.1) != NONE
    }),
{
    lemma_cand_facts(sv, rp, pd, t, c);
    let u = ctuple(sv, rp, pd, t, c);
    let (i, j, d, e) = (u.0, u.1, u.2, u.3);
    assert(exists|i2: int| 0 <= i2 < nc(sv) && #[trigger] c_ck(sv)[i2] == o_ck(sv)[j]);
    let i2 = choose|i2: int| 0 <= i2 < nc(sv) && #[trigger] c_ck(sv)[i2] == o_ck(sv)[j];
    assert(i2 == i);
    lemma_nslot_of(sv, rp, slots, e);
    assert(c_nk(sv)[i] == n_nk(sv)[e]);
}

/// Lineitem row `c` whose order row `j` has code `code != NONE`: `c` is a candidate exactly when some supplier with
/// its supplier key has slot `code`; then its group is `gos[code]`.
pub proof fn lemma_fast_entry(sv: StoresView, rp: Seq<u8>, pd: int, t: int, gids: Seq<usize>, slots: Seq<u8>, gos: Seq<usize>,
    c: int, j: int, code: u8)
    requires
        stores_wf(sv), keys_ok(sv), slots_ok(sv, rp, gids, slots, gos),
        0 <= c < nl(sv), 0 <= j < no(sv), o_ok(sv)[j] == l_ok(sv)[c],
        code == ord_code(sv, slots, pd, t, j), code != NONE,
    ensures
        cand(sv, rp, pd, t, c) <==> exists|d: int| 0 <= d < ns(sv) && #[trigger] s_sk(sv)[d] == l_sk(sv)[c]
            && nslot(sv, slots, s_nk(sv)[d]) == code,
        cand(sv, rp, pd, t, c) ==> gids[cnation(sv, rp, pd, t, c)] == gos[code as int],
{
    lemma_ord_code(sv, rp, pd, t, gids, slots, gos, j);
    let (i, e1) = choose|i: int, e: int| 0 <= i < nc(sv) && 0 <= e < nn(sv) && #[trigger] c_ck(sv)[i] == o_ck(sv)[j]
        && #[trigger] n_nk(sv)[e] == c_nk(sv)[i] && inreg(sv, rp, e) && slots[e] == code && date_in(o_date(sv)[j], pd, t);
    if exists|d: int| 0 <= d < ns(sv) && #[trigger] s_sk(sv)[d] == l_sk(sv)[c] && nslot(sv, slots, s_nk(sv)[d]) == code {
        let d = choose|d: int| 0 <= d < ns(sv) && #[trigger] s_sk(sv)[d] == l_sk(sv)[c] && nslot(sv, slots, s_nk(sv)[d]) == code;
        lemma_nslot_some(sv, rp, gids, slots, gos, s_nk(sv)[d]);
        let e2 = choose|e: int| 0 <= e < nn(sv) && #[trigger] n_nk(sv)[e] == s_nk(sv)[d] && inreg(sv, rp, e)
            && slots[e] == nslot(sv, slots, s_nk(sv)[d]);
        assert(slots[e1] == slots[e2]);
        assert(e1 == e2);
        let f = choose|f: int| 0 <= f < nr(sv) && #[trigger] r_rk(sv)[f] == n_rk(sv)[e1] && r_name(sv, f) == rp;
        assert(in6(sv, i, j, c, d, e1, f));
        assert(qual6(sv, rp, pd, t, i, j, c, d, e1, f));
        assert(cand(sv, rp, pd, t, c));
    }
    if cand(sv, rp, pd, t, c) {
        lemma_cand_facts(sv, rp, pd, t, c);
        let u = ctuple(sv, rp, pd, t, c);
        assert(u.1 == j);
        assert(u.0 == i);
        let (d, e) = (u.2, u.3);
        assert(n_nk(sv)[e] == n_nk(sv)[e1]);
        assert(e == e1);
        lemma_nslot_of(sv, rp, slots, e);
        assert(nslot(sv, slots, s_nk(sv)[d]) == code);
        assert(gos[slots[e] as int] == gids[e]);
    }
}

/// A lineitem row none of whose orders has a non-`NONE` code contributes nothing.
pub proof fn lemma_no_code_order(sv: StoresView, rp: Seq<u8>, pd: int, t: int, gids: Seq<usize>, slots: Seq<u8>, gos: Seq<usize>, c: int)
    requires
        stores_wf(sv), keys_ok(sv), slots_ok(sv, rp, gids, slots, gos), 0 <= c < nl(sv),
        forall|j: int| 0 <= j < no(sv) && #[trigger] o_ok(sv)[j] == l_ok(sv)[c] ==> ord_code(sv, slots, pd, t, j) == NONE,
    ensures !cand(sv, rp, pd, t, c),
{
    if cand(sv, rp, pd, t, c) {
        lemma_cand_code(sv, rp, pd, t, gids, slots, gos, c);
    }
}

// ------------------------------------------------------------------------------------------ groups and keys

/// The key of group `g`.
pub open spec fn gkey(sv: StoresView, reps: Seq<usize>, g: int) -> Row {
    seq![Val::Text(n_name(sv, reps[g] as int))]
}

/// On a group's key, the normal form's lineitem terms are the group terms.
proof fn lemma_key_terms(sv: StoresView, rp: Seq<u8>, pd: int, t: int, inregv: Seq<bool>, gids: Seq<usize>, reps: Seq<usize>, g: int, c: int)
    requires stores_wf(sv), keys_ok(sv), nation_ok(sv, rp, inregv, gids, reps), 0 <= g < reps.len(),
    ensures
        cterm(sv, rp, pd, t, gkey(sv, reps, g), c) == gterm(sv, rp, pd, t, gids, g, c),
        (cand(sv, rp, pd, t, c) && seq![Val::Text(n_name(sv, cnation(sv, rp, pd, t, c)))] == gkey(sv, reps, g))
            == (cand(sv, rp, pd, t, c) && gids[cnation(sv, rp, pd, t, c)] == g),
{
    if cand(sv, rp, pd, t, c) {
        lemma_cand_facts(sv, rp, pd, t, c);
        let e = cnation(sv, rp, pd, t, c);
        let r = reps[g] as int;
        assert(gids[r] == g);
        assert((gids[e] == gids[r]) == (n_name(sv, e) == n_name(sv, r)));
        if n_name(sv, e) != n_name(sv, r) {
            assert(seq![Val::Text(n_name(sv, e))][0] != gkey(sv, reps, g)[0]);
        }
    }
}

/// The normal form's lineitem sums of group `g`'s key are the group sums.
pub proof fn lemma_group_key_sums(sv: StoresView, rp: Seq<u8>, pd: int, t: int, inregv: Seq<bool>, gids: Seq<usize>, reps: Seq<usize>,
    g: int, n: int)
    requires stores_wf(sv), keys_ok(sv), nation_ok(sv, rp, inregv, gids, reps), 0 <= g < reps.len(), 0 <= n,
    ensures
        csum(sv, rp, pd, t, gkey(sv, reps, g), n) == gsum_r(sv, rp, pd, t, gids, g, 0, n),
        ccount(sv, rp, pd, t, gkey(sv, reps, g), n) == gcnt_r(sv, rp, pd, t, gids, g, 0, n),
        cabs(sv, rp, pd, t, gkey(sv, reps, g), n) == gabs_r(sv, rp, pd, t, gids, g, 0, n),
    decreases n,
{
    if n > 0 {
        lemma_group_key_sums(sv, rp, pd, t, inregv, gids, reps, g, n - 1);
        lemma_key_terms(sv, rp, pd, t, inregv, gids, reps, g, n - 1);
    }
}

/// A key that is no group's key has no candidate row.
pub proof fn lemma_other_key(sv: StoresView, rp: Seq<u8>, pd: int, t: int, inregv: Seq<bool>, gids: Seq<usize>, reps: Seq<usize>,
    k: Row, n: int)
    requires
        stores_wf(sv), keys_ok(sv), nation_ok(sv, rp, inregv, gids, reps), 0 <= n,
        forall|g: int| 0 <= g < reps.len() ==> #[trigger] gkey(sv, reps, g) != k,
    ensures ccount(sv, rp, pd, t, k, n) == 0, cabs(sv, rp, pd, t, k, n) == 0, csum(sv, rp, pd, t, k, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_other_key(sv, rp, pd, t, inregv, gids, reps, k, n - 1);
        let c = n - 1;
        if cand(sv, rp, pd, t, c) {
            lemma_cand_facts(sv, rp, pd, t, c);
            let e = cnation(sv, rp, pd, t, c);
            let g = gids[e] as int;
            let r = reps[g] as int;
            assert(gids[r] == g);
            assert(n_name(sv, e) == n_name(sv, r));
            assert(gkey(sv, reps, g) != k);
            assert(seq![Val::Text(n_name(sv, e))] =~= gkey(sv, reps, g));
        }
    }
}

} // verus!
