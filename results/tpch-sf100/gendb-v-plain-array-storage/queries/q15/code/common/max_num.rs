//! MAX over numeric values of one scale `s` (`spec::aggs::minmax::max_value`): on a non-empty list it is the value
//! at scale `s` with the largest coefficient (`coeff_max`); `is_max_of` characterizes that coefficient, so any
//! computation that finds a listed coefficient bounding all others has found it (`lemma_max_unique`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::numeric::{sign, max_nat};
use crate::spec::aggs::minmax::*;
use crate::link::expr::{lemma_compare_num, lemma_align_same};

verus! {

/// Every value is numeric at scale `s`.
pub open spec fn all_num_at(vs: Seq<Val>, s: nat) -> bool {
    forall|i: int| 0 <= i < vs.len() ==> (#[trigger] vs[i]) is Num && vs[i]->Num_scale == s
}

/// The largest coefficient of a non-empty list (0 for the empty list).
pub open spec fn coeff_max(vs: Seq<Val>) -> int
    decreases vs.len(),
{
    if vs.len() == 0 {
        0
    } else if vs.len() == 1 {
        vs[0]->Num_coeff
    } else {
        let a = coeff_max(vs.drop_last());
        let c = vs.last()->Num_coeff;
        if c > a { c } else { a }
    }
}

/// `m` is a coefficient of the list that bounds every coefficient of it.
pub open spec fn is_max_of(vs: Seq<Val>, m: int) -> bool {
    &&& forall|i: int| 0 <= i < vs.len() ==> (#[trigger] vs[i])->Num_coeff <= m
    &&& exists|i: int| 0 <= i < vs.len() && (#[trigger] vs[i])->Num_coeff == m
}

/// Two maxima of one list are equal.
pub proof fn lemma_max_unique(vs: Seq<Val>, m1: int, m2: int)
    requires is_max_of(vs, m1), is_max_of(vs, m2),
    ensures m1 == m2,
{
    let i1 = choose|i: int| 0 <= i < vs.len() && (#[trigger] vs[i])->Num_coeff == m1;
    let i2 = choose|i: int| 0 <= i < vs.len() && (#[trigger] vs[i])->Num_coeff == m2;
    assert(vs[i1]->Num_coeff <= m2);
    assert(vs[i2]->Num_coeff <= m1);
}

/// Two numerics at the same scale compare by their coefficients.
pub proof fn lemma_compare_same_scale(c1: int, c2: int, s: nat)
    ensures compare(Val::Num { coeff: c1, scale: s }, Val::Num { coeff: c2, scale: s }) == Some(sign(c1 - c2)),
{
    lemma_compare_num(c1, s, c2, s);
    assert(max_nat(s, s) == s);
    lemma_align_same(c1, s);
    lemma_align_same(c2, s);
}

/// MAX of a non-empty list of numerics at scale `s` is the numeric `coeff_max` at scale `s`, its largest coefficient.
pub proof fn lemma_max_value_num(vs: Seq<Val>, s: nat)
    requires all_num_at(vs, s), vs.len() > 0,
    ensures
        max_value(vs) == Ok::<Val, SqlError>(Val::Num { coeff: coeff_max(vs), scale: s }),
        is_max_of(vs, coeff_max(vs)),
    decreases vs.len(),
{
    let v = vs.last();
    let c = v->Num_coeff;
    assert(v == vs[vs.len() - 1]);
    assert(v == Val::Num { coeff: c, scale: s });
    if vs.len() == 1 {
        assert(vs.drop_last() =~= Seq::<Val>::empty());
        assert(extremum(true, vs.drop_last()) == Ok::<Val, SqlError>(Val::Null));
        assert(extremum(true, vs) == extremum_step(true, Val::Null, v));
        assert(vs[0]->Num_coeff == coeff_max(vs));
    } else {
        let d = vs.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]) is Num && d[i]->Num_scale == s by {
            assert(d[i] == vs[i]);
        }
        lemma_max_value_num(d, s);
        let a = coeff_max(d);
        lemma_compare_same_scale(c, a, s);
        assert(extremum(true, vs) == extremum_step(true, Val::Num { coeff: a, scale: s }, v));
        assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i])->Num_coeff <= coeff_max(vs) by {
            if i < d.len() {
                assert(vs[i] == d[i]);
                assert(d[i]->Num_coeff <= a);
            }
        }
        if c > a {
            assert(vs[vs.len() - 1]->Num_coeff == coeff_max(vs));
        } else {
            let w = choose|i: int| 0 <= i < d.len() && (#[trigger] d[i])->Num_coeff == a;
            assert(vs[w] == d[w]);
            assert(vs[w]->Num_coeff == coeff_max(vs));
        }
    }
}

} // verus!
