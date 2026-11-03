//! Relational facts used to read a SQL denotation as counts: membership of kept rows, the bag of kept and mapped rows
//! as a sum of per-row hits, sums with one nonzero term, MAX over numerics of one scale, GROUP BY members, and the
//! distinct keys of a GROUP BY (pairwise distinct, covering every input key).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::aggs::minmax::*;
use crate::link::join::*;
use crate::link::expr::ival;
use crate::bridge::equality::*;

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

/// A kept row: every row satisfying the condition is in `keep`.
pub proof fn lemma_keep_complete(rows: Seq<Row>, f: spec_fn(Row) -> bool, k: int)
    requires 0 <= k < rows.len(), f(rows[k]),
    ensures keep(rows, f).contains(rows[k]),
    decreases rows.len(),
{
    let n = rows.len() - 1;
    if k == n {
        assert(keep(rows, f) == keep(rows.drop_last(), f).push(rows.last()));
        assert(keep(rows, f)[keep(rows, f).len() - 1] == rows[k]);
    } else {
        let d = rows.drop_last();
        assert(d[k] == rows[k]);
        lemma_keep_complete(d, f, k);
        let j = choose|j: int| 0 <= j < keep(d, f).len() && keep(d, f)[j] == rows[k];
        if f(rows.last()) {
            assert(keep(rows, f) == keep(d, f).push(rows.last()));
            assert(keep(rows, f)[j] == rows[k]);
        } else {
            assert(keep(rows, f) == keep(d, f));
        }
    }
}

/// Per-row hit of a kept-and-mapped bag: 1 when the row is kept and maps to `t`.
pub open spec fn hit(f: spec_fn(Row) -> bool, m: spec_fn(Row) -> Row, t: Row) -> spec_fn(Row) -> int {
    |x: Row| if f(x) && m(x) == t { 1int } else { 0int }
}

/// The multiplicity of `t` among the kept rows mapped by `m` is the number of rows that are kept and map to `t`.
pub proof fn lemma_count_keep_map(rows: Seq<Row>, f: spec_fn(Row) -> bool, m: spec_fn(Row) -> Row, t: Row)
    ensures keep(rows, f).map_values(m).to_multiset().count(t) == sum_of(rows, hit(f, m, t)),
    decreases rows.len(),
{
    if rows.len() == 0 {
        assert(keep(rows, f).map_values(m) =~= Seq::<Row>::empty());
    } else {
        let d = rows.drop_last();
        let x = rows.last();
        lemma_count_keep_map(d, f, m, t);
        if f(x) {
            assert(keep(rows, f) == keep(d, f).push(x));
            assert(keep(rows, f).map_values(m) =~= keep(d, f).map_values(m).push(m(x)));
        } else {
            assert(keep(rows, f) == keep(d, f));
        }
    }
}

/// A sum with at most one nonzero term, at position `i`.
pub proof fn lemma_sum_of_single(rows: Seq<Row>, f: spec_fn(Row) -> int, i: int)
    requires 0 <= i < rows.len(), forall|j: int| 0 <= j < rows.len() && j != i ==> f(#[trigger] rows[j]) == 0,
    ensures sum_of(rows, f) == f(rows[i]),
{
    lemma_sum_of_remove(rows, i, f);
    let r = rows.remove(i);
    assert forall|j: int| 0 <= j < r.len() implies f(#[trigger] r[j]) == 0 by {
        if j < i {
            assert(r[j] == rows[j]);
        } else {
            assert(r[j] == rows[j + 1]);
        }
    }
    lemma_sum_of_zero(r, f);
}

// ------------------------------------------------------------------ MAX over numerics of one scale

/// Every value is a numeric at scale `s`.
pub open spec fn all_num_at(vs: Seq<Val>, s: nat) -> bool {
    forall|i: int| 0 <= i < vs.len() ==> (#[trigger] vs[i] is Num && vs[i]->Num_scale == s)
}

/// The largest coefficient (meaningful for a nonempty list).
pub open spec fn max_coeff(vs: Seq<Val>) -> int
    decreases vs.len(),
{
    if vs.len() <= 1 {
        ival(vs[0])
    } else {
        let a = max_coeff(vs.drop_last());
        let b = ival(vs.last());
        if b > a { b } else { a }
    }
}

/// MAX of nonempty numerics at one scale is the numeric with the largest coefficient, at that scale; every value is
/// at most it and some value equals it.
pub proof fn lemma_max_num(vs: Seq<Val>, s: nat)
    requires vs.len() > 0, all_num_at(vs, s),
    ensures
        max_value(vs) == Ok::<Val, SqlError>(Val::Num { coeff: max_coeff(vs), scale: s }),
        forall|i: int| 0 <= i < vs.len() ==> ival(#[trigger] vs[i]) <= max_coeff(vs),
        exists|i: int| 0 <= i < vs.len() && ival(vs[i]) == max_coeff(vs),
    decreases vs.len(),
{
    let x = vs.last();
    assert(x is Num && x->Num_scale == s);
    if vs.len() == 1 {
        assert(vs.drop_last() =~= Seq::<Val>::empty());
        assert(extremum(true, vs.drop_last()) == Ok::<Val, SqlError>(Val::Null));
        assert(vs[0] == x);
        assert(ival(vs[0]) == max_coeff(vs));
    } else {
        let d = vs.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i] is Num && d[i]->Num_scale == s) by {
            assert(d[i] == vs[i]);
        }
        lemma_max_num(d, s);
        let a = max_coeff(d);
        let acc = Val::Num { coeff: a, scale: s };
        crate::link::expr::lemma_compare_num(x->Num_coeff, s, a, s);
        crate::link::expr::lemma_align_same(x->Num_coeff, s);
        crate::link::expr::lemma_align_same(a, s);
        assert(max_nat(s, s) == s);
        assert(compare(x, acc) == Some(sign(x->Num_coeff - a)));
        assert(max_value(vs) == extremum_step(true, acc, x));
        assert forall|i: int| 0 <= i < vs.len() implies ival(#[trigger] vs[i]) <= max_coeff(vs) by {
            if i < d.len() {
                assert(vs[i] == d[i]);
            }
        }
        let w = choose|i: int| 0 <= i < d.len() && ival(d[i]) == a;
        if ival(x) > a {
            assert(ival(vs[vs.len() - 1]) == max_coeff(vs));
        } else {
            assert(vs[w] == d[w]);
            assert(ival(vs[w]) == max_coeff(vs));
        }
    }
}

// ------------------------------------------------------------------ GROUP BY members and distinct keys

/// Members of a group: exactly the arguments of the input rows whose key is not distinct from `k`.
pub proof fn lemma_group_members(keys: Seq<Row>, args: Seq<Row>, k: Row)
    requires keys.len() == args.len(),
    ensures
        forall|m: int| #![trigger group_members(keys, args, k)[m]] 0 <= m < group_members(keys, args, k).len()
            ==> member_from(keys, args, k, group_members(keys, args, k)[m]),
        forall|i: int| 0 <= i < keys.len() && row_not_distinct(#[trigger] keys[i], k) ==> exists|m: int|
            0 <= m < group_members(keys, args, k).len() && group_members(keys, args, k)[m] == args[i],
    decreases keys.len(),
{
    if keys.len() > 0 {
        let (dk, da) = (keys.drop_last(), args.drop_last());
        lemma_group_members(dk, da, k);
        let gi = group_members(dk, da, k);
        let g = group_members(keys, args, k);
        let n = keys.len() - 1;
        assert forall|i: int| 0 <= i < n implies keys[i] == dk[i] && args[i] == da[i] by {}
        // A member of the shorter input is a member here.
        assert forall|r: Row| member_from(dk, da, k, r) implies member_from(keys, args, k, r) by {
            let i = choose|i: int| 0 <= i < dk.len() && row_not_distinct(dk[i], k) && r == da[i];
            assert(keys[i] == dk[i] && args[i] == da[i]);
        }
        if row_not_distinct(keys.last(), k) {
            assert(g == gi.push(args.last()));
            assert(member_from(keys, args, k, args[n]));
            assert forall|m: int| #![trigger g[m]] 0 <= m < g.len() implies member_from(keys, args, k, g[m]) by {
                if m < gi.len() {
                    assert(g[m] == gi[m]);
                    assert(member_from(dk, da, k, gi[m]));
                } else {
                    assert(g[m] == args[n]);
                }
            }
        } else {
            assert(g == gi);
            assert forall|m: int| #![trigger g[m]] 0 <= m < g.len() implies member_from(keys, args, k, g[m]) by {
                assert(member_from(dk, da, k, gi[m]));
            }
        }
        assert forall|i: int| 0 <= i < keys.len() && row_not_distinct(#[trigger] keys[i], k) implies exists|m: int|
            0 <= m < g.len() && g[m] == args[i] by {
            if i < n {
                assert(keys[i] == dk[i] && args[i] == da[i]);
                let m = choose|m: int| 0 <= m < gi.len() && gi[m] == da[i];
                assert(g[m] == gi[m]);
            } else {
                assert(g[gi.len() as int] == args[n]);
            }
        }
    } else {
        assert(group_members(keys, args, k) =~= Seq::<Row>::empty());
    }
}

/// `r` is the argument row of some input row whose key is not distinct from `k`.
pub open spec fn member_from(keys: Seq<Row>, args: Seq<Row>, k: Row, r: Row) -> bool {
    exists|i: int| 0 <= i < keys.len() && row_not_distinct(keys[i], k) && r == #[trigger] args[i]
}

/// `has_not_distinct` is an existential over positions.
pub proof fn lemma_has_not_distinct(rows: Seq<Row>, r: Row)
    ensures has_not_distinct(rows, r) == exists|i: int| 0 <= i < rows.len() && row_not_distinct(#[trigger] rows[i], r),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let d = rows.drop_last();
        lemma_has_not_distinct(d, r);
        if has_not_distinct(d, r) {
            let i = choose|i: int| 0 <= i < d.len() && row_not_distinct(d[i], r);
            assert(rows[i] == d[i]);
        }
        if exists|i: int| 0 <= i < rows.len() && row_not_distinct(#[trigger] rows[i], r) {
            let i = choose|i: int| 0 <= i < rows.len() && row_not_distinct(#[trigger] rows[i], r);
            if i < d.len() {
                assert(rows[i] == d[i]);
            }
        }
    }
}

/// The distinct keys are pairwise distinct, and every input key is not distinct from one of them.
pub proof fn lemma_distinct_rows(rows: Seq<Row>)
    ensures
        forall|a: int, b: int| 0 <= a < b < distinct_rows(rows).len()
            ==> !row_not_distinct(#[trigger] distinct_rows(rows)[a], #[trigger] distinct_rows(rows)[b]),
        forall|i: int| 0 <= i < rows.len() ==> exists|g: int| 0 <= g < distinct_rows(rows).len()
            && row_not_distinct(distinct_rows(rows)[g], #[trigger] rows[i]),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let init = rows.drop_last();
        let x = rows.last();
        lemma_distinct_rows(init);
        let d = distinct_rows(init);
        let dd = distinct_rows(rows);
        lemma_has_not_distinct(d, x);
        if has_not_distinct(d, x) {
            assert(dd == d);
        } else {
            assert(dd == d.push(x));
        }
        assert forall|a: int, b: int| 0 <= a < b < dd.len() implies !row_not_distinct(#[trigger] dd[a], #[trigger] dd[b]) by {
            if b < d.len() {
                assert(dd[a] == d[a] && dd[b] == d[b]);
            } else {
                assert(dd[a] == d[a] && dd[b] == x);
            }
        }
        assert forall|i: int| 0 <= i < rows.len() implies exists|g: int| 0 <= g < dd.len()
            && row_not_distinct(dd[g], #[trigger] rows[i]) by {
            if i < init.len() {
                assert(rows[i] == init[i]);
                let g = choose|g: int| 0 <= g < d.len() && row_not_distinct(d[g], init[i]);
                assert(dd[g] == d[g]);
            } else if has_not_distinct(d, x) {
                let g = choose|g: int| 0 <= g < d.len() && row_not_distinct(#[trigger] d[g], x);
                assert(dd[g] == d[g]);
            } else {
                lemma_row_not_distinct_refl(x);
                assert(dd[d.len() as int] == x);
            }
        }
    }
}

/// Two distinct keys at positions `a < b` are distinct.
pub proof fn lemma_distinct_pair(rows: Seq<Row>, a: int, b: int)
    requires 0 <= a < b < distinct_rows(rows).len(),
    ensures !row_not_distinct(distinct_rows(rows)[a], distinct_rows(rows)[b]),
{
    lemma_distinct_rows(rows);
}

/// Input key `i` is not distinct from some distinct key.
pub proof fn lemma_distinct_cover(rows: Seq<Row>, i: int)
    requires 0 <= i < rows.len(),
    ensures exists|g: int| 0 <= g < distinct_rows(rows).len() && row_not_distinct(#[trigger] distinct_rows(rows)[g], rows[i]),
{
    lemma_distinct_rows(rows);
    let d = distinct_rows(rows);
    assert(rows[i] == rows[i]);
    let g = choose|g: int| 0 <= g < d.len() && row_not_distinct(d[g], rows[i]);
    assert(row_not_distinct(d[g], rows[i]));
}

/// On rows of two texts, not distinct is equal.
pub proof fn lemma_not_distinct_text2(r: Row, s: Row)
    requires r.len() == 2, s.len() == 2, r[0] is Text, r[1] is Text, s[0] is Text, s[1] is Text,
    ensures row_not_distinct(r, s) == (r == s),
{
    lemma_val_not_distinct_structural(r[0], s[0]);
    lemma_val_not_distinct_structural(r[1], s[1]);
    if r == s {
        lemma_row_not_distinct_refl(r);
    }
    if row_not_distinct(r, s) {
        assert(val_not_distinct(r[0], s[0]) && val_not_distinct(r[1], s[1]));
        assert(r =~= s);
    }
}

// ------------------------------------------------------------------ sums over position ranges

/// `f(lo) + .. + f(hi - 1)`.
pub open spec fn sum_idx(lo: int, hi: int, f: spec_fn(int) -> int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { sum_idx(lo, hi - 1, f) + f(hi - 1) }
}

/// Splitting a range.
pub proof fn lemma_sum_idx_split(lo: int, mid: int, hi: int, f: spec_fn(int) -> int)
    requires lo <= mid <= hi,
    ensures sum_idx(lo, hi, f) == sum_idx(lo, mid, f) + sum_idx(mid, hi, f),
    decreases hi - mid,
{
    if hi > mid {
        lemma_sum_idx_split(lo, mid, hi - 1, f);
    }
}

/// Zero terms give a zero sum.
pub proof fn lemma_sum_idx_zero(lo: int, hi: int, f: spec_fn(int) -> int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] f(i) == 0,
    ensures sum_idx(lo, hi, f) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_sum_idx_zero(lo, hi - 1, f);
    }
}

/// Equal terms give equal sums.
pub proof fn lemma_sum_idx_ext(lo: int, hi: int, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] f(i) == g(i),
    ensures sum_idx(lo, hi, f) == sum_idx(lo, hi, g),
    decreases hi - lo,
{
    if hi > lo {
        lemma_sum_idx_ext(lo, hi - 1, f, g);
    }
}

/// The sum over a sequence built by index is the sum over the index range.
pub proof fn lemma_sum_of_new(n: nat, g: spec_fn(int) -> Row, f: spec_fn(Row) -> int)
    ensures sum_of(Seq::new(n, g), f) == sum_idx(0, n as int, |i: int| f(g(i))),
    decreases n,
{
    if n > 0 {
        assert(Seq::new(n, g).drop_last() =~= Seq::new((n - 1) as nat, g));
        lemma_sum_of_new((n - 1) as nat, g, f);
    }
}

/// The sum over a sequence is the sum over its positions.
pub proof fn lemma_sum_of_idx(rows: Seq<Row>, f: spec_fn(Row) -> int)
    ensures sum_of(rows, f) == sum_idx(0, rows.len() as int, |i: int| f(rows[i])),
{
    let g = |i: int| rows[i];
    assert(rows =~= Seq::new(rows.len(), g));
    lemma_sum_of_new(rows.len(), g, f);
    lemma_sum_idx_ext(0, rows.len() as int, |i: int| f(g(i)), |i: int| f(rows[i]));
}

} // verus!
