//! Relational facts over `spec::relation`: membership, positions and duplicate-freedom of left-major products,
//! `keep_true` as `link::join::keep` for three-valued truths, `keep` membership and duplicate-freedom, MIN over
//! numerics of one scale (`spec::aggs::minmax::extremum`), and splitting a sequence by a condition (`select`).
use vstd::prelude::*;
use vstd::multiset::Multiset;
use crate::spec::value::*;
use crate::spec::scalar::compare;
use crate::spec::numeric::sign;
use crate::spec::relation::{product_rows, keep_true};
use crate::spec::aggs::minmax::{extremum, extremum_step};
use crate::link::join::{keep, lemma_product_index};

verus! {

// ------------------------------------------------------------------------------------------------ products

/// Row `f` of a left-major product is `a[f / |b|] ++ b[f % |b|]`.
pub proof fn lemma_product_at(a: Seq<Row>, b: Seq<Row>, f: int)
    requires 0 <= f < a.len() * b.len(),
    ensures
        b.len() > 0,
        0 <= f / (b.len() as int) < a.len(),
        0 <= f % (b.len() as int) < b.len(),
        f == (f / (b.len() as int)) * (b.len() as int) + f % (b.len() as int),
        product_rows(a, b)[f] == a[f / (b.len() as int)] + b[f % (b.len() as int)],
{
    let nb = b.len() as int;
    lemma_product_index(a, b);
    if nb == 0 {
        assert(a.len() * b.len() == 0) by (nonlinear_arith) requires b.len() == 0;
    }
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(f, nb);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(f, nb);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(f, nb);
    let i = f / nb;
    let j = f % nb;
    assert(nb * i == i * nb) by (nonlinear_arith);
    assert(i < a.len()) by (nonlinear_arith) requires i * nb + j == f, f < a.len() * nb, j >= 0, nb > 0;
    assert(product_rows(a, b)[i * nb + j] == a[i] + b[j]);
}

/// Every pair of rows is a row of the product.
pub proof fn lemma_product_has(a: Seq<Row>, b: Seq<Row>, i: int, j: int)
    requires 0 <= i < a.len(), 0 <= j < b.len(),
    ensures product_rows(a, b).contains(a[i] + b[j]),
{
    lemma_product_index(a, b);
    let nb = b.len() as int;
    assert(0 <= i * nb + j < a.len() * nb) by (nonlinear_arith) requires 0 <= i < a.len(), 0 <= j < nb;
    assert(product_rows(a, b)[i * nb + j] == a[i] + b[j]);
}

/// Every row of the product is a pair of rows.
pub proof fn lemma_product_split(a: Seq<Row>, b: Seq<Row>, z: Row)
    requires product_rows(a, b).contains(z),
    ensures exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && z == #[trigger] a[i] + #[trigger] b[j],
{
    lemma_product_index(a, b);
    let f = choose|f: int| 0 <= f < product_rows(a, b).len() && product_rows(a, b)[f] == z;
    lemma_product_at(a, b, f);
    let nb = b.len() as int;
    assert(z == a[f / nb] + b[f % nb]);
}

/// Concatenations with left parts of one length are equal exactly when both parts are.
pub proof fn lemma_concat_inj(x1: Row, y1: Row, x2: Row, y2: Row)
    requires x1.len() == x2.len(), x1 + y1 == x2 + y2,
    ensures x1 == x2, y1 == y2,
{
    assert(x1 =~= (x1 + y1).subrange(0, x1.len() as int));
    assert(x2 =~= (x2 + y2).subrange(0, x2.len() as int));
    assert(y1 =~= (x1 + y1).subrange(x1.len() as int, (x1 + y1).len() as int));
    assert(y2 =~= (x2 + y2).subrange(x2.len() as int, (x2 + y2).len() as int));
}

/// The product of duplicate-free relations (left rows of one width) is duplicate-free.
pub proof fn lemma_product_nodup(a: Seq<Row>, b: Seq<Row>, w: nat)
    requires a.no_duplicates(), b.no_duplicates(), forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == w,
    ensures product_rows(a, b).no_duplicates(),
{
    lemma_product_index(a, b);
    let p = product_rows(a, b);
    let nb = b.len() as int;
    assert forall|f1: int, f2: int| 0 <= f1 < p.len() && 0 <= f2 < p.len() && f1 != f2 implies p[f1] != p[f2] by {
        lemma_product_at(a, b, f1);
        lemma_product_at(a, b, f2);
        let (i1, j1, i2, j2) = (f1 / nb, f1 % nb, f2 / nb, f2 % nb);
        if p[f1] == p[f2] {
            lemma_concat_inj(a[i1], b[j1], a[i2], b[j2]);
            assert(i1 == i2 && j1 == j2);
        }
    }
}

// ------------------------------------------------------------------------------------------------ filters

/// `keep_true` of truths that are `True` exactly where `f` holds is `keep(rows, f)` (`False` and `Unknown`
/// both drop a row).
pub proof fn lemma_keep_true_iff(rows: Seq<Row>, truths: Seq<Truth>, f: spec_fn(Row) -> bool)
    requires
        truths.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] truths[i] is True) == f(rows[i]),
    ensures keep_true(rows, truths) == keep(rows, f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < ri.len() implies (#[trigger] ti[i] is True) == f(ri[i]) by {
            assert(ti[i] == truths[i] && ri[i] == rows[i]);
        }
        lemma_keep_true_iff(ri, ti, f);
        assert((truths[rows.len() - 1] is True) == f(rows[rows.len() - 1]));
    }
}

/// A row of the input satisfying the condition is kept.
pub proof fn lemma_keep_has(rows: Seq<Row>, f: spec_fn(Row) -> bool, z: Row)
    requires rows.contains(z), f(z),
    ensures keep(rows, f).contains(z),
    decreases rows.len(),
{
    let ri = rows.drop_last();
    if rows.last() == z {
        assert(keep(rows, f) == keep(ri, f).push(z));
        assert(keep(rows, f)[keep(ri, f).len() as int] == z);
    } else {
        let i = choose|i: int| 0 <= i < rows.len() && rows[i] == z;
        assert(i < rows.len() - 1);
        assert(ri[i] == z);
        lemma_keep_has(ri, f, z);
        let k = keep(ri, f);
        let x = choose|x: int| 0 <= x < k.len() && k[x] == z;
        if f(rows.last()) {
            assert(keep(rows, f)[x] == z);
        }
    }
}

/// Kept rows of a duplicate-free input are duplicate-free.
pub proof fn lemma_keep_nodup(rows: Seq<Row>, f: spec_fn(Row) -> bool)
    requires rows.no_duplicates(),
    ensures keep(rows, f).no_duplicates(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert(ri.no_duplicates()) by {
            assert forall|i: int, j: int| 0 <= i < ri.len() && 0 <= j < ri.len() && i != j implies ri[i] != ri[j] by {
                assert(ri[i] == rows[i] && ri[j] == rows[j]);
            }
        }
        lemma_keep_nodup(ri, f);
        if f(rows.last()) {
            let k = keep(ri, f);
            crate::link::join::lemma_keep_members(ri, f);
            assert forall|x: int| 0 <= x < k.len() implies k[x] != rows.last() by {
                assert(ri.contains(k[x]));
                let i = choose|i: int| 0 <= i < ri.len() && ri[i] == k[x];
                assert(rows[i] != rows[rows.len() - 1]);
            }
            let kp = k.push(rows.last());
            assert forall|i: int, j: int| 0 <= i < kp.len() && 0 <= j < kp.len() && i != j implies kp[i] != kp[j] by {
                if i < k.len() && j < k.len() {
                    assert(kp[i] == k[i] && kp[j] == k[j]);
                } else if i < k.len() {
                    assert(kp[i] == k[i]);
                } else if j < k.len() {
                    assert(kp[j] == k[j]);
                }
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ MIN

/// MIN over numerics of one scale `s`: NULL on no value, else one of the values, at most every value.
pub proof fn lemma_min_num(vs: Seq<Val>, s: nat)
    requires forall|i: int| 0 <= i < vs.len() ==> (#[trigger] vs[i]) is Num && vs[i]->scale == s,
    ensures
        extremum(false, vs) is Ok,
        vs.len() == 0 ==> extremum(false, vs) == Ok::<Val, SqlError>(Val::Null),
        vs.len() > 0 ==> ({
            let r = extremum(false, vs)->Ok_0;
            &&& r is Num && r->scale == s
            &&& exists|i: int| 0 <= i < vs.len() && vs[i] == r
            &&& forall|i: int| 0 <= i < vs.len() ==> r->coeff <= (#[trigger] vs[i])->coeff
        }),
    decreases vs.len(),
{
    if vs.len() > 0 {
        let d = vs.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]) is Num && d[i]->scale == s by {
            assert(d[i] == vs[i]);
        }
        lemma_min_num(d, s);
        let v = vs.last();
        let acc = extremum(false, d)->Ok_0;
        assert(vs[vs.len() - 1] == v);
        if d.len() == 0 {
            assert(extremum(false, vs) == extremum_step(false, Val::Null, v));
            assert(vs[0] == v);
        } else {
            let (cv, ca) = (v->coeff, acc->coeff);
            crate::link::expr::lemma_compare_num(cv, s, ca, s);
            crate::link::expr::lemma_align_same(cv, s);
            crate::link::expr::lemma_align_same(ca, s);
            assert(compare(v, acc) == Some(sign(cv - ca)));
            let r = extremum(false, vs)->Ok_0;
            let i0 = choose|i: int| 0 <= i < d.len() && d[i] == acc;
            assert(vs[i0] == acc);
            if cv < ca {
                assert(r == v);
            } else {
                assert(r == acc);
            }
            assert forall|i: int| 0 <= i < vs.len() implies r->coeff <= (#[trigger] vs[i])->coeff by {
                if i < d.len() {
                    assert(vs[i] == d[i]);
                }
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ selections

/// The elements of `s` satisfying `f`, in order.
pub open spec fn select<A>(s: Seq<A>, f: spec_fn(A) -> bool) -> Seq<A>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if f(s.last()) {
        select(s.drop_last(), f).push(s.last())
    } else {
        select(s.drop_last(), f)
    }
}

/// One more element at the end.
pub proof fn lemma_select_push<A>(s: Seq<A>, x: A, f: spec_fn(A) -> bool)
    ensures select(s.push(x), f) == if f(x) { select(s, f).push(x) } else { select(s, f) },
{
    assert(s.push(x).drop_last() =~= s);
}

/// The selected elements are elements of `s` satisfying `f`.
pub proof fn lemma_select_members<A>(s: Seq<A>, f: spec_fn(A) -> bool)
    ensures forall|i: int| 0 <= i < select(s, f).len() ==> s.contains(#[trigger] select(s, f)[i]) && f(select(s, f)[i]),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        lemma_select_members(d, f);
        assert forall|i: int| 0 <= i < select(s, f).len() implies s.contains(#[trigger] select(s, f)[i]) && f(select(s, f)[i]) by {
            if i < select(d, f).len() {
                assert(select(s, f)[i] == select(d, f)[i]);
                let j = choose|j: int| 0 <= j < d.len() && d[j] == select(d, f)[i];
                assert(s[j] == d[j]);
            } else {
                assert(select(s, f)[i] == s.last());
                assert(s[s.len() - 1] == s.last());
            }
        }
    }
}

/// The elements satisfying `f` and those that do not are together all of `s`.
pub proof fn lemma_select_split<A>(s: Seq<A>, f: spec_fn(A) -> bool, g: spec_fn(A) -> bool)
    requires forall|x: A| #[trigger] g(x) == !f(x),
    ensures select(s, f).to_multiset().add(select(s, g).to_multiset()) == s.to_multiset(),
    decreases s.len(),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    if s.len() == 0 {
        assert(select(s, f).len() == 0);
        assert(select(s, g).len() == 0);
        assert(select(s, f).to_multiset().len() == 0);
        assert(select(s, g).to_multiset().len() == 0);
        assert(s.to_multiset().len() == 0);
        assert(select(s, f).to_multiset() =~= Multiset::empty());
        assert(select(s, g).to_multiset() =~= Multiset::empty());
        assert(s.to_multiset() =~= Multiset::empty());
    } else {
        let d = s.drop_last();
        let x = s.last();
        lemma_select_split(d, f, g);
        assert(d.push(x) =~= s);
        d.to_multiset_ensures();
        select(d, f).to_multiset_ensures();
        select(d, g).to_multiset_ensures();
        if f(x) {
            assert(select(s, f).to_multiset() =~= select(d, f).to_multiset().insert(x));
            assert(select(s, g) == select(d, g));
        } else {
            assert(select(s, g).to_multiset() =~= select(d, g).to_multiset().insert(x));
            assert(select(s, f) == select(d, f));
        }
        assert(select(s, f).to_multiset().add(select(s, g).to_multiset()) =~= s.to_multiset());
    }
}

/// Selections by complementary conditions, mapped, together hold the mapped sequence.
pub proof fn lemma_select_split_map<A, B>(s: Seq<A>, f: spec_fn(A) -> bool, g: spec_fn(A) -> bool, h: spec_fn(A) -> B)
    requires forall|x: A| #[trigger] g(x) == !f(x),
    ensures
        select(s, f).map_values(h).to_multiset().add(select(s, g).map_values(h).to_multiset()) == s.map_values(h).to_multiset(),
        select(s, f).len() + select(s, g).len() == s.len(),
    decreases s.len(),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    if s.len() == 0 {
        assert(select(s, f).map_values(h).len() == 0);
        assert(select(s, g).map_values(h).len() == 0);
        assert(s.map_values(h).len() == 0);
        assert(select(s, f).map_values(h).to_multiset() =~= Multiset::empty());
        assert(select(s, g).map_values(h).to_multiset() =~= Multiset::empty());
        assert(s.map_values(h).to_multiset() =~= Multiset::empty());
    } else {
        let d = s.drop_last();
        let x = s.last();
        lemma_select_split_map(d, f, g, h);
        assert(s.map_values(h) =~= d.map_values(h).push(h(x)));
        if f(x) {
            assert(select(s, f).map_values(h) =~= select(d, f).map_values(h).push(h(x)));
            assert(select(s, g) == select(d, g));
        } else {
            assert(select(s, g).map_values(h) =~= select(d, g).map_values(h).push(h(x)));
            assert(select(s, f) == select(d, f));
        }
        assert(select(s, f).map_values(h).to_multiset().add(select(s, g).map_values(h).to_multiset())
            =~= s.map_values(h).to_multiset());
    }
}

} // verus!
