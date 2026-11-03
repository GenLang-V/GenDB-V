//! What a successful fast path establishes about the normal form, from the slot sums `vals` of all `lineitem` rows
//! (`table_ok` over `[0, n)`) and the assumptions every row met (`range_fast` over `[0, n)`):
//! - every group key is a slot key `[base + s]`, every group's terms are positive, so its SUM is its absolute mass
//!   and positive exactly when the group exists (`lemma_fast_key`);
//! - the groups are inside `group_caps` (each SUM is an `i64` slot value, `lemma_fast_caps`);
//! - the largest slot value is the subquery's MAX (`lemma_fast_max`);
//! - with dense supplier keys (`keys[i] == base + i`), supplier row `i` is picked exactly when its slot holds that
//!   largest value and it is positive (`lemma_fast_pick`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::query::*;
use crate::link::expr::i128_max;
use crate::agent::common::max_num::*;
use crate::agent::normal::*;
use crate::agent::cols::*;
use crate::agent::bounds::*;
use crate::agent::scan::*;
use crate::agent::groups::*;
use crate::agent::answer::pick_of;

verus! {

/// The normal form under the window `w`.
pub open spec fn g_of(w: DayWindow) -> QuerySpec {
    q_spec(qb_of(w))
}

/// The group key of slot `s`.
pub open spec fn slot_key(base: int, s: int) -> Row {
    seq![Val::Int(base + s)]
}

/// Over the first `i` rows: the SUM of key `k` is its absolute mass, non-negative, positive exactly when the group
/// has a row, and a group with a row has a slot key.
pub proof fn lemma_fast_key(c: Cols, w: DayWindow, base: int, ns: int, k: Row, i: int)
    requires cols_wf(c), range_fast(c, w, base, ns, 0, c.n as int), 0 <= i <= c.n,
    ensures ({
        let g = g_of(w);
        let rows = crows(c).subrange(0, i);
        &&& gsum(g, rows, k, 0) == gabs(g, rows, k, 0)
        &&& gsum(g, rows, k, 0) >= 0
        &&& (gcount(g, rows, k) > 0 <==> gsum(g, rows, k, 0) > 0)
        &&& (gcount(g, rows, k) > 0 ==> exists|s: int| 0 <= s < ns && k == #[trigger] slot_key(base, s))
    }),
    decreases i,
{
    let g = g_of(w);
    if i == 0 {
        lemma_empty(g, crows(c), 0, k, 0);
    } else {
        lemma_fast_key(c, w, base, ns, k, i - 1);
        lemma_range_step(g, crows(c), 0, i - 1, k, 0);
        let r = i - 1;
        assert(crows(c)[r] == crow(c, r));
        if hit(g, crow(c, r), k) {
            assert(p_ship(c, w)(r));
            assert(row_fast(c, w, base, ns, r));
            assert(k == seq![Val::Int(c.supp@[r] as int)]);
            let s = c.supp@[r] as int - base;
            assert(k == slot_key(base, s));
            assert((g.arg)(0, crow(c, r)) == rev(c, r));
            assert(abs(rev(c, r)) == rev(c, r));
        }
    }
}

/// The SUM, mass and count of key `k` over all rows, as `lemma_fast_key` states them.
pub proof fn lemma_fast_key_all(c: Cols, w: DayWindow, base: int, ns: int, k: Row)
    requires cols_wf(c), range_fast(c, w, base, ns, 0, c.n as int),
    ensures ({
        let g = g_of(w);
        let xs = crows(c);
        &&& gsum(g, xs, k, 0) == gabs(g, xs, k, 0)
        &&& gsum(g, xs, k, 0) >= 0
        &&& (gcount(g, xs, k) > 0 <==> gsum(g, xs, k, 0) > 0)
        &&& (gcount(g, xs, k) > 0 ==> exists|s: int| 0 <= s < ns && k == #[trigger] slot_key(base, s))
    }),
{
    lemma_fast_key(c, w, base, ns, k, c.n as int);
    lemma_full_range(crows(c));
}

/// The SUM of slot key `base + s` over all rows is slot `s` of `vals`.
pub proof fn lemma_slot_sum(c: Cols, w: DayWindow, base: int, ns: int, vals: Seq<i64>, s: int)
    requires table_ok(vals, c, w, base, ns, 0, c.n as int), 0 <= s < ns,
    ensures gsum(g_of(w), crows(c), seq![Val::Int(base + s)], 0) == vals[s] as int,
{
    lemma_full_range(crows(c));
}

/// The groups are inside the capacity condition.
pub proof fn lemma_fast_caps(c: Cols, w: DayWindow, base: int, ns: int, vals: Seq<i64>)
    requires cols_wf(c), range_fast(c, w, base, ns, 0, c.n as int), table_ok(vals, c, w, base, ns, 0, c.n as int),
    ensures group_caps(g_of(w), crows(c)),
{
    let g = g_of(w);
    let xs = crows(c);
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
        assert(j == 0);
        lemma_fast_key_all(c, w, base, ns, k);
        if gcount(g, xs, k) > 0 {
            let s = choose|s: int| 0 <= s < ns && k == #[trigger] slot_key(base, s);
            lemma_slot_sum(c, w, base, ns, vals, s);
        } else {
            lemma_zero_count(g, xs, k, 0);
        }
    }
}

/// `best` is the largest slot value (0 when no slot is positive).
pub open spec fn is_best(vals: Seq<i64>, best: int) -> bool {
    &&& best >= 0
    &&& forall|s: int| 0 <= s < vals.len() ==> (#[trigger] vals[s]) as int <= best
    &&& best > 0 ==> exists|s: int| 0 <= s < vals.len() && (#[trigger] vals[s]) as int == best
}

/// The largest slot value is the subquery's MAX.
pub proof fn lemma_fast_max(c: Cols, w: DayWindow, base: int, ns: int, vals: Seq<i64>, best: int)
    requires
        cols_wf(c),
        range_fast(c, w, base, ns, 0, c.n as int),
        table_ok(vals, c, w, base, ns, 0, c.n as int),
        is_best(vals, best),
    ensures best == max_sum(g_of(w), crows(c)),
{
    let g = g_of(w);
    let xs = crows(c);
    let gk = gkeys(g, xs);
    let vs = sum_vals(g, xs);
    lemma_gkeys(g, xs);
    if gk.len() == 0 {
        assert(vs =~= Seq::<Val>::empty());
        if best > 0 {
            let s = choose|s: int| 0 <= s < vals.len() && (#[trigger] vals[s]) as int == best;
            let k = seq![Val::Int(base + s)];
            lemma_slot_sum(c, w, base, ns, vals, s);
            lemma_fast_key_all(c, w, base, ns, k);
            assert(gk.contains(k));
        }
    } else {
        // every group's SUM is a slot value, bounded by `best`
        assert forall|j: int| 0 <= j < vs.len() implies (#[trigger] vs[j])->Num_coeff <= best by {
            let k = gk[j];
            assert(gk.contains(k));
            lemma_fast_key_all(c, w, base, ns, k);
            let s = choose|s: int| 0 <= s < ns && k == #[trigger] slot_key(base, s);
            lemma_slot_sum(c, w, base, ns, vals, s);
        }
        // the first group has a positive SUM, so `best` is positive and some group reaches it
        let k0 = gk[0];
        assert(gk.contains(k0));
        lemma_fast_key_all(c, w, base, ns, k0);
        let s0 = choose|s: int| 0 <= s < ns && k0 == #[trigger] slot_key(base, s);
        lemma_slot_sum(c, w, base, ns, vals, s0);
        assert(best > 0);
        let s = choose|s: int| 0 <= s < vals.len() && (#[trigger] vals[s]) as int == best;
        let k = seq![Val::Int(base + s)];
        lemma_slot_sum(c, w, base, ns, vals, s);
        lemma_fast_key_all(c, w, base, ns, k);
        assert(gk.contains(k));
        let j = choose|j: int| 0 <= j < gk.len() && gk[j] == k;
        assert(vs[j]->Num_coeff == best);
        assert(is_max_of(vs, best));
        assert(all_num_at(vs, 4));
        lemma_max_value_num(vs, 4);
        lemma_max_unique(vs, best, coeff_max(vs));
    }
}

/// With dense supplier keys, supplier row `i` is picked exactly when its slot holds the positive largest value.
pub proof fn lemma_fast_pick(c: Cols, w: DayWindow, base: int, ns: int, vals: Seq<i64>, best: int, k: SuppKeys,
    srows: Seq<Row>, i: int)
    requires
        cols_wf(c),
        range_fast(c, w, base, ns, 0, c.n as int),
        table_ok(vals, c, w, base, ns, 0, c.n as int),
        keys_match(k, srows),
        k.ns == ns,
        forall|r: int| 0 <= r < ns ==> #[trigger] k.keys@[r] as int == base + r,
        0 <= i < ns,
    ensures pick_of(g_of(w), crows(c), srows, best)(i) == (vals[i] as int == best && best > 0),
{
    let g = g_of(w);
    let xs = crows(c);
    let key = seq![Val::Int(base + i)];
    assert(srows[i][0] == Val::Int(k.keys@[i] as int));
    assert(seq![srows[i][0]] =~= key);
    lemma_slot_sum(c, w, base, ns, vals, i);
    lemma_fast_key_all(c, w, base, ns, key);
    lemma_gkeys(g, xs);
}

} // verus!
