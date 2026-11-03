//! From per-slot counts to name groups. GROUP BY s_name merges the slots whose suppliers share a name: the group of
//! slot `t` counts `gtot(t)`, the sum of the counts of every slot with `t`'s name; it is listed once, at its first
//! slot (`first`). `name_groups` lists the groups with a nonzero count in slot order (`gs_ok`): when the slots'
//! names are strictly increasing (`side::names_inc`, so every name is one slot) directly from the counts, else by
//! comparing names (quadratic, a fallback the storage contract does not exclude).
use vstd::prelude::*;
use crate::spec::text::lex_cmp;
use crate::stores::suppliers::interface::common::colfmt::text_range_ok;
use crate::stores::suppliers::interface::common::read::text_slice;
use super::common::isum::*;
use super::side::*;
use super::cand::*;

verus! {

/// The count of slot `u` when it has slot `t`'s name.
pub open spec fn same_f(sc: SCols, srows: Seq<usize>, tot: Seq<usize>, t: int) -> spec_fn(int) -> int {
    |u: int| if slot_name(sc, srows, u) == slot_name(sc, srows, t) { tot[u] as int } else { 0int }
}

/// The count of slot `t`'s name group.
pub open spec fn gtot(sc: SCols, srows: Seq<usize>, tot: Seq<usize>, t: int) -> int {
    isum(tot.len() as int, same_f(sc, srows, tot, t))
}

/// Slot `t` is the first slot of its name.
pub open spec fn first(sc: SCols, srows: Seq<usize>, t: int) -> bool {
    forall|u: int| 0 <= u < t ==> #[trigger] slot_name(sc, srows, u) != slot_name(sc, srows, t)
}

/// `gs` lists the nonzero name groups, at their first slots, in slot order.
pub open spec fn gs_ok(sc: SCols, srows: Seq<usize>, tot: Seq<usize>, gs: Seq<Cand>) -> bool {
    &&& forall|i: int| 0 <= i < gs.len() ==> {
        &&& (#[trigger] gs[i]).t < tot.len()
        &&& first(sc, srows, gs[i].t as int)
        &&& gs[i].cnt as int == gtot(sc, srows, tot, gs[i].t as int)
        &&& gs[i].cnt > 0
        &&& gs[i].cnt <= i64::MAX
    }
    &&& forall|i: int, j: int| 0 <= i < j < gs.len() ==> (#[trigger] gs[i]).t < (#[trigger] gs[j]).t
    &&& forall|t: int| 0 <= t < tot.len() && first(sc, srows, t) && #[trigger] gtot(sc, srows, tot, t) > 0 ==>
            exists|i: int| 0 <= i < gs.len() && (#[trigger] gs[i]).t == t
}

/// With strictly increasing names every slot is the first of its name, and its group is itself.
pub proof fn lemma_inc_groups(sc: SCols, srows: Seq<usize>, tot: Seq<usize>, t: int)
    requires
        names_inc(sc, srows),
        tot.len() == srows.len(),
        0 <= t < tot.len(),
    ensures
        first(sc, srows, t),
        gtot(sc, srows, tot, t) == tot[t] as int,
{
    assert forall|u: int| 0 <= u < tot.len() && u != t implies #[trigger] slot_name(sc, srows, u) != slot_name(sc, srows, t) by {
        if u < t {
            lemma_inc_lt(sc, srows, u, t);
            crate::bridge::equality::lemma_lex_cmp_zero(slot_name(sc, srows, u), slot_name(sc, srows, t));
        } else {
            lemma_inc_lt(sc, srows, t, u);
            crate::bridge::equality::lemma_lex_cmp_zero(slot_name(sc, srows, t), slot_name(sc, srows, u));
        }
    }
    let f = same_f(sc, srows, tot, t);
    assert forall|u: int| 0 <= u < tot.len() && u != t implies #[trigger] f(u) == 0 by {}
    lemma_isum_single(tot.len() as int, f, t);
}

/// Strictly increasing names: an earlier slot's name is below a later one's.
pub proof fn lemma_inc_lt(sc: SCols, srows: Seq<usize>, a: int, b: int)
    requires names_inc(sc, srows), 0 <= a < b < srows.len(),
    ensures lex_cmp(slot_name(sc, srows, a), slot_name(sc, srows, b)) < 0,
    decreases b - a,
{
    assert(inc_at(sc, srows, b - 1));
    assert(lex_cmp(slot_name(sc, srows, b - 1), slot_name(sc, srows, b)) < 0);
    if a < b - 1 {
        lemma_inc_lt(sc, srows, a, b - 1);
        crate::bridge::order::lemma_lex_cmp_trans(slot_name(sc, srows, a), slot_name(sc, srows, b - 1), slot_name(sc, srows, b));
        crate::bridge::equality::lemma_lex_cmp_zero(slot_name(sc, srows, a), slot_name(sc, srows, b));
        if slot_name(sc, srows, a) == slot_name(sc, srows, b) {
            crate::bridge::order::lemma_lex_cmp_antisym(slot_name(sc, srows, b - 1), slot_name(sc, srows, b));
        }
        crate::bridge::order::lemma_lex_cmp_antisym(slot_name(sc, srows, a), slot_name(sc, srows, b));
    }
}

/// Whether slots `a` and `b` have the same name.
fn same_name(sc: &SCols, srows: &Vec<usize>, a: usize, b: usize) -> (r: bool)
    requires
        scols_ok(*sc),
        a < srows@.len(),
        b < srows@.len(),
        srows@[a as int] < sc.n_s,
        srows@[b as int] < sc.n_s,
    ensures r == (slot_name(*sc, srows@, a as int) == slot_name(*sc, srows@, b as int)),
{
    let ra = srows[a];
    let rb = srows[b];
    assert(text_range_ok(sc.sm_offs@, sc.sm_bytes@, ra as int));
    assert(text_range_ok(sc.sm_offs@, sc.sm_bytes@, rb as int));
    let x = text_slice(sc.sm_offs, sc.sm_bytes, ra);
    let y = text_slice(sc.sm_offs, sc.sm_bytes, rb);
    bytes_eq(x, y)
}

/// Whether slot `t` is the first slot of its name (a scan of the earlier slots).
fn slot_first(sc: &SCols, srows: &Vec<usize>, t: usize) -> (r: bool)
    requires
        scols_ok(*sc),
        t < srows@.len(),
        forall|u: int| 0 <= u < srows@.len() ==> #[trigger] srows@[u] < sc.n_s,
    ensures r == first(*sc, srows@, t as int),
{
    let mut u: usize = 0;
    while u < t
        invariant
            scols_ok(*sc),
            t < srows@.len(),
            forall|w: int| 0 <= w < srows@.len() ==> #[trigger] srows@[w] < sc.n_s,
            u <= t,
            forall|w: int| 0 <= w < u ==> #[trigger] slot_name(*sc, srows@, w) != slot_name(*sc, srows@, t as int),
        decreases t - u,
    {
        if same_name(sc, srows, u, t) {
            return false;
        }
        u = u + 1;
    }
    true
}

/// The count of slot `t`'s name group (exact in `u128`: at most `2^64` slots of counts below `2^64`).
fn slot_total(sc: &SCols, srows: &Vec<usize>, tot: &Vec<usize>, t: usize) -> (r: u128)
    requires
        scols_ok(*sc),
        t < srows@.len(),
        tot@.len() == srows@.len(),
        forall|u: int| 0 <= u < srows@.len() ==> #[trigger] srows@[u] < sc.n_s,
    ensures r as int == gtot(*sc, srows@, tot@, t as int),
{
    let ns = tot.len();
    let ghost f = same_f(*sc, srows@, tot@, t as int);
    let mut total: u128 = 0;
    let mut u: usize = 0;
    while u < ns
        invariant
            scols_ok(*sc),
            ns == tot@.len(),
            tot@.len() == srows@.len(),
            forall|w: int| 0 <= w < srows@.len() ==> #[trigger] srows@[w] < sc.n_s,
            t < ns,
            u <= ns,
            f == same_f(*sc, srows@, tot@, t as int),
            total as int == isum(u as int, f),
            total <= u * 0xffff_ffff_ffff_ffffu128,
        decreases ns - u,
    {
        proof { lemma_isum_step(u as int, f); }
        if same_name(sc, srows, u, t) {
            proof {
                assert(u * 0xffff_ffff_ffff_ffffu128 + 0xffff_ffff_ffff_ffffu128 <= u128::MAX) by (nonlinear_arith)
                    requires u < 0x1_0000_0000_0000_0000int;
            }
            total = total + tot[u] as u128;
        }
        u = u + 1;
    }
    total
}

/// The name groups with a nonzero count, or the first slot whose group count exceeds `i64::MAX`.
pub fn name_groups(sc: &SCols, srows: &Vec<usize>, tot: &Vec<usize>, inc: bool) -> (r: Result<Vec<Cand>, usize>)
    requires
        scols_ok(*sc),
        tot@.len() == srows@.len(),
        forall|t: int| 0 <= t < srows@.len() ==> #[trigger] srows@[t] < sc.n_s,
        inc ==> names_inc(*sc, srows@),
    ensures
        r matches Ok(gs) ==> gs_ok(*sc, srows@, tot@, gs@),
        r matches Err(t) ==> t < tot@.len() && first(*sc, srows@, t as int) && gtot(*sc, srows@, tot@, t as int) > i64::MAX,
{
    let ns = tot.len();
    let mut gs: Vec<Cand> = Vec::new();
    let mut t: usize = 0;
    while t < ns
        invariant
            scols_ok(*sc),
            ns == tot@.len(),
            tot@.len() == srows@.len(),
            forall|u: int| 0 <= u < srows@.len() ==> #[trigger] srows@[u] < sc.n_s,
            inc ==> names_inc(*sc, srows@),
            t <= ns,
            forall|i: int| 0 <= i < gs@.len() ==> {
                &&& (#[trigger] gs@[i]).t < t
                &&& first(*sc, srows@, gs@[i].t as int)
                &&& gs@[i].cnt as int == gtot(*sc, srows@, tot@, gs@[i].t as int)
                &&& gs@[i].cnt > 0
                &&& gs@[i].cnt <= i64::MAX
            },
            forall|i: int, j: int| 0 <= i < j < gs@.len() ==> (#[trigger] gs@[i]).t < (#[trigger] gs@[j]).t,
            forall|u: int| 0 <= u < t && first(*sc, srows@, u) && #[trigger] gtot(*sc, srows@, tot@, u) > 0 ==>
                exists|i: int| 0 <= i < gs@.len() && (#[trigger] gs@[i]).t == u,
        decreases ns - t,
    {
        // Is t the first slot of its name, and what does its group count?
        let (is_first, total) = if inc {
            proof { lemma_inc_groups(*sc, srows@, tot@, t as int); }
            (true, tot[t] as u128)
        } else {
            let fst = slot_first(sc, srows, t);
            if fst { (true, slot_total(sc, srows, tot, t)) } else { (false, 0u128) }
        };
        let ghost old_gs = gs@;
        if is_first && total > 0 {
            if total > 0x7fff_ffff_ffff_ffffu128 {
                return Err(t);
            }
            gs.push(Cand { t, cnt: total as u64 });
            proof {
                assert(gs@[gs@.len() - 1].t == t);
                assert forall|i: int| 0 <= i < gs@.len() implies {
                    &&& (#[trigger] gs@[i]).t < t + 1
                    &&& first(*sc, srows@, gs@[i].t as int)
                    &&& gs@[i].cnt as int == gtot(*sc, srows@, tot@, gs@[i].t as int)
                    &&& gs@[i].cnt > 0
                    &&& gs@[i].cnt <= i64::MAX
                } by {
                    if i < old_gs.len() {
                        assert(gs@[i] == old_gs[i]);
                    }
                }
                assert forall|i: int, j: int| 0 <= i < j < gs@.len() implies (#[trigger] gs@[i]).t < (#[trigger] gs@[j]).t by {
                    assert(gs@[i] == old_gs[i]);
                    if j < old_gs.len() {
                        assert(gs@[j] == old_gs[j]);
                    }
                }
            }
        }
        proof {
            assert forall|u: int| 0 <= u < t + 1 && first(*sc, srows@, u) && #[trigger] gtot(*sc, srows@, tot@, u) > 0 implies
                exists|i: int| 0 <= i < gs@.len() && (#[trigger] gs@[i]).t == u by {
                if u < t {
                    let i = choose|i: int| 0 <= i < old_gs.len() && (#[trigger] old_gs[i]).t == u;
                    assert(gs@[i] == old_gs[i]);
                } else {
                    assert(gs@[gs@.len() - 1].t == t);
                }
            }
        }
        t = t + 1;
    }
    Ok(gs)
}

} // verus!
