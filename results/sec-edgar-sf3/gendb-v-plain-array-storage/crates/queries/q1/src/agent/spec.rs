//! Normal form of the statement over the rows of `pre`: a row qualifies when its stmt (position 3) is not NULL;
//! its group key is (stmt, rfile) (positions 3 and 5). Per key `k` and row range `[lo, hi)`: the number of
//! qualifying rows of the group (`cnt_r`), the sum of their line values (position 2, `sum_r`) and the set of their
//! adsh values (position 0, `aset_r`). All three are defined by recursion on `hi`, so a scan of a range is proved
//! against them one row at a time, and ranges combine (`lemma_split`).
use vstd::prelude::*;
use crate::spec::value::*;

verus! {

/// The row's stmt is not NULL (the WHERE condition).
pub open spec fn qual(r: Row) -> bool {
    !(r[3] is Null)
}

/// The group key (stmt, rfile).
pub open spec fn key_of(r: Row) -> Row {
    seq![r[3], r[5]]
}

/// The row qualifies and belongs to group `k`.
pub open spec fn hit(r: Row, k: Row) -> bool {
    qual(r) && key_of(r) == k
}

/// The line value of a row (an integer column).
pub open spec fn line_of(r: Row) -> int {
    match r[2] {
        Val::Int(x) => x,
        _ => 0,
    }
}

/// Number of rows of group `k` in `t[lo..hi]`.
pub open spec fn cnt_r(t: Seq<Row>, k: Row, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo {
        0
    } else {
        cnt_r(t, k, lo, hi - 1) + if hit(t[hi - 1], k) { 1nat } else { 0nat }
    }
}

/// Sum of the line values of the rows of group `k` in `t[lo..hi]`.
pub open spec fn sum_r(t: Seq<Row>, k: Row, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo {
        0
    } else {
        sum_r(t, k, lo, hi - 1) + if hit(t[hi - 1], k) { line_of(t[hi - 1]) } else { 0 }
    }
}

/// The adsh values of the rows of group `k` in `t[lo..hi]`.
pub open spec fn aset_r(t: Seq<Row>, k: Row, lo: int, hi: int) -> Set<Val>
    decreases hi - lo,
{
    if hi <= lo {
        Set::empty()
    } else if hit(t[hi - 1], k) {
        aset_r(t, k, lo, hi - 1).insert(t[hi - 1][0])
    } else {
        aset_r(t, k, lo, hi - 1)
    }
}

/// Ranges combine: count and sum add up, adsh sets unite.
pub proof fn lemma_split(t: Seq<Row>, k: Row, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures
        cnt_r(t, k, lo, hi) == cnt_r(t, k, lo, mid) + cnt_r(t, k, mid, hi),
        sum_r(t, k, lo, hi) == sum_r(t, k, lo, mid) + sum_r(t, k, mid, hi),
        aset_r(t, k, lo, hi) == aset_r(t, k, lo, mid).union(aset_r(t, k, mid, hi)),
    decreases hi - mid,
{
    if hi > mid {
        lemma_split(t, k, lo, mid, hi - 1);
        let a = aset_r(t, k, lo, mid);
        let b = aset_r(t, k, mid, hi - 1);
        if hit(t[hi - 1], k) {
            assert(a.union(b).insert(t[hi - 1][0]) =~= a.union(b.insert(t[hi - 1][0])));
        }
    } else {
        assert(aset_r(t, k, lo, mid).union(Set::empty()) =~= aset_r(t, k, lo, mid));
    }
}

/// The adsh set has at most as many values as the group has rows.
pub proof fn lemma_aset_finite(t: Seq<Row>, k: Row, lo: int, hi: int)
    ensures
        aset_r(t, k, lo, hi).len() <= cnt_r(t, k, lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_aset_finite(t, k, lo, hi - 1);
    }
}

/// At most one row per position.
pub proof fn lemma_cnt_le(t: Seq<Row>, k: Row, lo: int, hi: int)
    requires lo <= hi,
    ensures cnt_r(t, k, lo, hi) <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_cnt_le(t, k, lo, hi - 1);
    }
}

/// With line values in `[-2^31, 2^31)` the sum is bounded by `2^31` per row of the group.
pub proof fn lemma_sum_bound(t: Seq<Row>, k: Row, lo: int, hi: int)
    requires
        forall|i: int| lo <= i < hi ==> -0x8000_0000 <= #[trigger] line_of(t[i]) < 0x8000_0000,
    ensures
        -0x8000_0000 * cnt_r(t, k, lo, hi) <= sum_r(t, k, lo, hi) <= 0x8000_0000 * cnt_r(t, k, lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_sum_bound(t, k, lo, hi - 1);
        assert(lo <= hi - 1 < hi);
    }
}

/// A group with rows in the range has a witness row.
pub proof fn lemma_cnt_witness(t: Seq<Row>, k: Row, lo: int, hi: int)
    requires cnt_r(t, k, lo, hi) > 0,
    ensures exists|i: int| lo <= i < hi && #[trigger] hit(t[i], k),
    decreases hi - lo,
{
    if hit(t[hi - 1], k) {
        assert(hit(t[hi - 1], k));
    } else {
        lemma_cnt_witness(t, k, lo, hi - 1);
    }
}

/// A value of the adsh set comes from a row of the group.
pub proof fn lemma_aset_witness(t: Seq<Row>, k: Row, lo: int, hi: int, v: Val)
    requires aset_r(t, k, lo, hi).contains(v),
    ensures exists|i: int| lo <= i < hi && #[trigger] hit(t[i], k) && t[i][0] == v,
    decreases hi - lo,
{
    if hi > lo {
        if hit(t[hi - 1], k) && t[hi - 1][0] == v {
        } else {
            lemma_aset_witness(t, k, lo, hi - 1, v);
        }
    }
}

/// Every row of the group contributes its adsh value.
pub proof fn lemma_aset_member(t: Seq<Row>, k: Row, lo: int, hi: int, i: int)
    requires lo <= i < hi, hit(t[i], k),
    ensures aset_r(t, k, lo, hi).contains(t[i][0]),
    decreases hi - lo,
{
    if i < hi - 1 {
        lemma_aset_member(t, k, lo, hi - 1, i);
    }
}

/// A group without rows in the range has no count, sum or adsh value there.
pub proof fn lemma_no_hit(t: Seq<Row>, k: Row, lo: int, hi: int)
    requires forall|i: int| lo <= i < hi ==> !#[trigger] hit(t[i], k),
    ensures cnt_r(t, k, lo, hi) == 0, sum_r(t, k, lo, hi) == 0, aset_r(t, k, lo, hi) == Set::<Val>::empty(),
    decreases hi - lo,
{
    if hi > lo {
        assert(!hit(t[hi - 1], k));
        lemma_no_hit(t, k, lo, hi - 1);
    }
}

} // verus!
