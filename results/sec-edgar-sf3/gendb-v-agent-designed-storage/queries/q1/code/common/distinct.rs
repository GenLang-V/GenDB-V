//! COUNT(DISTINCT x) over values of one exact type: `distinct_vals` (the first occurrence of each not-distinct
//! class, NULLs dropped) has no duplicates and the same elements as its non-NULL input, so the DISTINCT count is
//! the number of distinct values, `vs.to_set().len()`, whatever the order of the values.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::relation::count_non_null;
use crate::spec::equality::*;
use crate::bridge::equality::{same_exact_type, lemma_val_not_distinct_structural};

verus! {

/// Non-NULL values of pairwise one exact type (for example all text, or all numerics of one scale).
pub open spec fn exact_vals(vs: Seq<Val>) -> bool {
    &&& forall|i: int| 0 <= i < vs.len() ==> !(#[trigger] vs[i] is Null)
    &&& forall|i: int, j: int| 0 <= i < vs.len() && 0 <= j < vs.len() ==> same_exact_type(#[trigger] vs[i], #[trigger] vs[j])
}

/// On values of one exact type, `has_val_not_distinct` is `contains`.
proof fn lemma_has_val_contains(d: Seq<Val>, v: Val, pool: Seq<Val>)
    requires
        exact_vals(pool),
        pool.contains(v),
        forall|i: int| 0 <= i < d.len() ==> pool.contains(#[trigger] d[i]),
    ensures has_val_not_distinct(d, v) <==> d.contains(v),
    decreases d.len(),
{
    if d.len() > 0 {
        let di = d.drop_last();
        assert forall|i: int| 0 <= i < di.len() implies pool.contains(#[trigger] di[i]) by {
            assert(di[i] == d[i]);
        }
        lemma_has_val_contains(di, v, pool);
        assert(pool.contains(d[d.len() - 1]));
        let a = choose|a: int| 0 <= a < pool.len() && pool[a] == d.last();
        let b = choose|b: int| 0 <= b < pool.len() && pool[b] == v;
        assert(same_exact_type(pool[a], pool[b]));
        lemma_val_not_distinct_structural(d.last(), v);
        if di.contains(v) {
            let i = choose|i: int| 0 <= i < di.len() && di[i] == v;
            assert(d[i] == v);
        }
        if d.contains(v) && d.last() != v {
            let i = choose|i: int| 0 <= i < d.len() && d[i] == v;
            assert(i != d.len() - 1);
            assert(di[i] == v);
        }
    }
}

/// `distinct_vals` of a prefix of the pool: duplicate-free, its elements are the prefix's, and none is NULL.
proof fn lemma_distinct_vals_pool(vs: Seq<Val>, pool: Seq<Val>)
    requires
        exact_vals(pool),
        forall|i: int| 0 <= i < vs.len() ==> pool.contains(#[trigger] vs[i]),
    ensures
        distinct_vals(vs).no_duplicates(),
        forall|v: Val| #[trigger] distinct_vals(vs).contains(v) <==> vs.contains(v),
        count_non_null(distinct_vals(vs)) == distinct_vals(vs).len(),
    decreases vs.len(),
{
    let d = distinct_vals(vs);
    if vs.len() == 0 {
        assert(d =~= Seq::<Val>::empty());
    } else {
        let vi = vs.drop_last();
        let x = vs.last();
        assert forall|i: int| 0 <= i < vi.len() implies pool.contains(#[trigger] vi[i]) by {
            assert(vi[i] == vs[i]);
        }
        lemma_distinct_vals_pool(vi, pool);
        let di = distinct_vals(vi);
        assert(pool.contains(vs[vs.len() - 1]));
        let px = choose|a: int| 0 <= a < pool.len() && pool[a] == x;
        assert(!(x is Null));
        assert forall|i: int| 0 <= i < di.len() implies pool.contains(#[trigger] di[i]) by {
            assert(di.contains(di[i]));
            assert(vi.contains(di[i]));
            let j = choose|j: int| 0 <= j < vi.len() && vi[j] == di[i];
            assert(pool.contains(vi[j]));
        }
        lemma_has_val_contains(di, x, pool);
        if di.contains(x) {
            assert(d == di);
            assert forall|v: Val| #[trigger] d.contains(v) <==> vs.contains(v) by {
                if vs.contains(v) {
                    let j = choose|j: int| 0 <= j < vs.len() && vs[j] == v;
                    if j < vi.len() {
                        assert(vi[j] == v);
                        assert(vi.contains(v));
                    }
                }
                if d.contains(v) {
                    assert(vi.contains(v));
                    let j = choose|j: int| 0 <= j < vi.len() && vi[j] == v;
                    assert(vs[j] == v);
                }
            }
        } else {
            assert(d == di.push(x));
            assert(d.drop_last() =~= di);
            assert forall|a: int, b: int| 0 <= a < b < d.len() implies d[a] != d[b] by {
                if b == di.len() {
                    assert(di.contains(d[a]));
                } else {
                    assert(d[a] == di[a] && d[b] == di[b]);
                }
            }
            assert forall|v: Val| #[trigger] d.contains(v) <==> vs.contains(v) by {
                if vs.contains(v) {
                    let j = choose|j: int| 0 <= j < vs.len() && vs[j] == v;
                    if j < vi.len() {
                        assert(vi[j] == v);
                        assert(vi.contains(v));
                        assert(di.contains(v));
                        let i = choose|i: int| 0 <= i < di.len() && di[i] == v;
                        assert(d[i] == v);
                    } else {
                        assert(d[di.len() as int] == v);
                    }
                }
                if d.contains(v) {
                    let i = choose|i: int| 0 <= i < d.len() && d[i] == v;
                    if i < di.len() {
                        assert(di[i] == v);
                        assert(di.contains(v));
                        assert(vi.contains(v));
                        let j = choose|j: int| 0 <= j < vi.len() && vi[j] == v;
                        assert(vs[j] == v);
                    } else {
                        assert(vs[vs.len() - 1] == v);
                    }
                }
            }
        }
    }
}

/// COUNT(DISTINCT) over values of one exact type counts the distinct values.
pub proof fn lemma_count_distinct(vs: Seq<Val>)
    requires exact_vals(vs),
    ensures
        count_non_null(distinct_vals(vs)) == vs.to_set().len(),
        distinct_vals(vs).no_duplicates(),
        distinct_vals(vs).to_set() == vs.to_set(),
{
    assert forall|i: int| 0 <= i < vs.len() implies vs.contains(#[trigger] vs[i]) by {}
    lemma_distinct_vals_pool(vs, vs);
    let d = distinct_vals(vs);
    assert(d.to_set() =~= vs.to_set()) by {
        assert forall|v: Val| d.to_set().contains(v) <==> vs.to_set().contains(v) by {
            d.to_set_ensures();
            vs.to_set_ensures();
        }
    }
    d.unique_seq_to_set();
}

} // verus!
