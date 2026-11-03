//! COUNT(DISTINCT x) over integer values (`spec::equality::distinct_vals`): on integers SQL "not distinct" is
//! equality, so the distinct values are the set of values of the sequence without repetition. One more value adds
//! one exactly when it is new (`lemma_distinct_push`); values of a 32-bit integer column have at most `2^32`
//! distinct values (`lemma_distinct_bound`). Also: the exact numeric sum of values of one static scale.
use vstd::prelude::*;
use vstd::set_lib::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::relation::*;
use crate::spec::equality::*;

verus! {

/// Every value is an integer.
pub open spec fn all_int(vs: Seq<Val>) -> bool {
    forall|i: int| 0 <= i < vs.len() ==> #[trigger] vs[i] is Int
}

/// On integers "not distinct" is equality.
pub proof fn lemma_int_not_distinct(a: Val, b: Val)
    requires a is Int, b is Int,
    ensures val_not_distinct(a, b) == (a == b),
{
}

/// `has_val_not_distinct` over integers is `contains`.
pub proof fn lemma_has_int(d: Seq<Val>, v: Val)
    requires all_int(d), v is Int,
    ensures has_val_not_distinct(d, v) == d.contains(v),
    decreases d.len(),
{
    if d.len() > 0 {
        let di = d.drop_last();
        assert forall|i: int| 0 <= i < di.len() implies #[trigger] di[i] is Int by {
            assert(di[i] == d[i]);
        }
        lemma_has_int(di, v);
        assert(d[d.len() - 1] == d.last());
        lemma_int_not_distinct(d.last(), v);
        if di.contains(v) {
            let w = choose|w: int| 0 <= w < di.len() && di[w] == v;
            assert(d[w] == v);
        }
        if d.contains(v) && d.last() != v {
            let w = choose|w: int| 0 <= w < d.len() && d[w] == v;
            assert(di[w] == v);
        }
    }
}

/// The distinct values of integers: integers, without repetition, exactly the values of the sequence.
pub proof fn lemma_distinct_ints(vs: Seq<Val>)
    requires all_int(vs),
    ensures
        all_int(distinct_vals(vs)),
        distinct_vals(vs).no_duplicates(),
        forall|v: Val| #[trigger] distinct_vals(vs).contains(v) <==> vs.contains(v),
    decreases vs.len(),
{
    if vs.len() > 0 {
        let vi = vs.drop_last();
        let x = vs.last();
        assert forall|i: int| 0 <= i < vi.len() implies #[trigger] vi[i] is Int by {
            assert(vi[i] == vs[i]);
        }
        lemma_distinct_ints(vi);
        let d = distinct_vals(vi);
        assert(vs[vs.len() - 1] == x);
        lemma_has_int(d, x);
        assert forall|v: Val| vs.contains(v) <==> (vi.contains(v) || v == x) by {
            if vs.contains(v) {
                let w = choose|w: int| 0 <= w < vs.len() && vs[w] == v;
                if w < vi.len() {
                    assert(vi[w] == v);
                }
            }
            if vi.contains(v) {
                let w = choose|w: int| 0 <= w < vi.len() && vi[w] == v;
                assert(vs[w] == v);
            }
        }
        if !d.contains(x) {
            let d2 = d.push(x);
            assert forall|i: int| 0 <= i < d2.len() implies #[trigger] d2[i] is Int by {
                if i < d.len() {
                    assert(d2[i] == d[i]);
                }
            }
            assert forall|i: int, j: int| 0 <= i < d2.len() && 0 <= j < d2.len() && i != j implies d2[i] != d2[j] by {
                if i < d.len() && j < d.len() {
                    assert(d2[i] == d[i] && d2[j] == d[j]);
                } else if i < d.len() {
                    assert(d2[i] == d[i]);
                } else {
                    assert(d2[j] == d[j]);
                }
            }
            assert forall|v: Val| #[trigger] d2.contains(v) <==> (d.contains(v) || v == x) by {
                if d2.contains(v) {
                    let w = choose|w: int| 0 <= w < d2.len() && d2[w] == v;
                    if w < d.len() {
                        assert(d[w] == v);
                    }
                }
                if d.contains(v) {
                    let w = choose|w: int| 0 <= w < d.len() && d[w] == v;
                    assert(d2[w] == v);
                }
                if v == x {
                    assert(d2[d.len() as int] == x);
                }
            }
        }
    }
}

/// One more integer adds one distinct value exactly when it is new.
pub proof fn lemma_distinct_push(vs: Seq<Val>, x: Val)
    requires all_int(vs), x is Int,
    ensures distinct_vals(vs.push(x)).len() == distinct_vals(vs).len() + if vs.contains(x) { 0int } else { 1int },
{
    lemma_distinct_ints(vs);
    assert(vs.push(x).drop_last() =~= vs);
    assert(vs.push(x).last() == x);
    lemma_has_int(distinct_vals(vs), x);
}

/// At most `2^32` distinct values of 32-bit integers.
pub proof fn lemma_distinct_bound(vs: Seq<Val>)
    requires all_int(vs), forall|i: int| 0 <= i < vs.len() ==> -0x8000_0000 <= (#[trigger] vs[i])->Int_0 < 0x8000_0000,
    ensures distinct_vals(vs).len() <= 0x1_0000_0000,
{
    lemma_distinct_ints(vs);
    let d = distinct_vals(vs);
    let xs = d.map_values(|v: Val| v->Int_0);
    assert forall|i: int, j: int| 0 <= i < xs.len() && 0 <= j < xs.len() && i != j implies xs[i] != xs[j] by {
        assert(d[i] is Int && d[j] is Int);
        assert(d[i] != d[j]);
    }
    assert(xs.no_duplicates());
    xs.unique_seq_to_set();
    lemma_int_range(-0x8000_0000, 0x8000_0000);
    assert(xs.to_set().subset_of(set_int_range(-0x8000_0000, 0x8000_0000))) by {
        assert forall|x: int| xs.to_set().contains(x) implies set_int_range(-0x8000_0000, 0x8000_0000).contains(x) by {
            let w = choose|w: int| 0 <= w < xs.len() && xs[w] == x;
            assert(d.contains(d[w]));
            assert(vs.contains(d[w]));
            let w2 = choose|w2: int| 0 <= w2 < vs.len() && vs[w2] == d[w];
        }
    }
    lemma_len_subset(xs.to_set(), set_int_range(-0x8000_0000, 0x8000_0000));
}

/// Every value is a numeric of scale `s`.
pub open spec fn all_num(vs: Seq<Val>, s: nat) -> bool {
    forall|i: int| 0 <= i < vs.len() ==> (#[trigger] vs[i] is Num) && vs[i]->Num_scale == s
}

/// The exact sum of numerics of one scale `s` is the sum of their coefficients at scale `s` (`(0, 0)` empty).
pub proof fn lemma_num_sum_push(vs: Seq<Val>, sum: int, c: int, s: nat)
    requires num_sum(vs) == (sum, if vs.len() == 0 { 0nat } else { s }), vs.len() == 0 ==> sum == 0,
    ensures num_sum(vs.push(Val::Num { coeff: c, scale: s })) == (sum + c, s),
{
    let x = Val::Num { coeff: c, scale: s };
    assert(vs.push(x).drop_last() =~= vs);
    assert((s - s) as nat == 0nat);
    assert(pow10(0) == 1);
    if vs.len() == 0 {
        assert(align(sum, 0, s) == 0) by (nonlinear_arith) requires sum == 0, align(sum, 0, s) == sum * pow10((s - 0) as nat);
    }
}

} // verus!
