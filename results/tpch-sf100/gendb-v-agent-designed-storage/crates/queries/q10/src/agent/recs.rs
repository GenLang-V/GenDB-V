//! Order records of the fast path and their sums. A phase-1 task emits one record `(customer row, revenue)` per
//! order of its range that is dated in the window, has a returned lineitem and whose customer exists (`recs_ok`):
//! for every customer row `c`, the records naming `c` sum to the customer's revenue over the range (`rsum`), there
//! are as many as such orders (`rcnt`), and the absolute values of all records are bounded by the task's mass.
//! Range sums of the per-order values are prefix differences (`kernel::dsum`), so ranges of consecutive tasks
//! telescope.
use vstd::prelude::*;
use crate::spec::numeric::abs;
use super::common::isum::*;
use super::model::*;
use super::qspec::*;
use super::kernel::dsum;

verus! {

pub open spec fn rsum_f(rc: Seq<u32>, rr: Seq<i64>, c: int) -> spec_fn(int) -> int {
    |i: int| if rc[i] as int == c { rr[i] as int } else { 0int }
}

pub open spec fn rcnt_f(rc: Seq<u32>, c: int) -> spec_fn(int) -> int {
    |i: int| if rc[i] as int == c { 1int } else { 0int }
}

pub open spec fn rabs_f(rr: Seq<i64>) -> spec_fn(int) -> int {
    |i: int| abs(rr[i] as int)
}

/// Sum of the first `n` records naming customer row `c`.
pub open spec fn rsum(rc: Seq<u32>, rr: Seq<i64>, n: int, c: int) -> int { isum(n, rsum_f(rc, rr, c)) }
/// Number of the first `n` records naming customer row `c`.
pub open spec fn rcnt(rc: Seq<u32>, n: int, c: int) -> int { isum(n, rcnt_f(rc, c)) }
/// Absolute sum of the first `n` records.
pub open spec fn rabs(rr: Seq<i64>, n: int) -> int { isum(n, rabs_f(rr)) }

/// Order `q` counts for customer `c`: its order, in the window, with a returned lineitem.
pub open spec fn chit_f(m: M, p: QP, c: int) -> spec_fn(int) -> int {
    |q: int| if ohit(m, p, c, q) && lcnt(m, q) > 0 { 1int } else { 0int }
}

/// The records `(rc, rr)[0, n)` of the orders `[lo, hi)` with absolute mass at most `mass`.
pub open spec fn recs_ok(m: M, p: QP, rc: Seq<u32>, rr: Seq<i64>, n: int, lo: int, hi: int, mass: int) -> bool {
    &&& 0 <= n <= rc.len() && n <= rr.len()
    &&& forall|i: int| 0 <= i < n ==> (#[trigger] rc[i]) < m.c_n
    &&& forall|c: int| 0 <= c < m.c_n ==> {
        &&& #[trigger] rsum(rc, rr, n, c) == dsum(csum_f(m, p, c), lo, hi)
        &&& rcnt(rc, n, c) == dsum(chit_f(m, p, c), lo, hi)
        &&& dsum(cabs_f(m, p, c), lo, hi) <= mass
    }
    &&& rabs(rr, n) <= mass
}

// ------------------------------------------------------------------------------------------------ laws

/// One more record.
pub proof fn lemma_rec_step(rc: Seq<u32>, rr: Seq<i64>, n: int, c: int)
    requires n >= 0,
    ensures
        rsum(rc, rr, n + 1, c) == rsum(rc, rr, n, c) + if rc[n] as int == c { rr[n] as int } else { 0int },
        rcnt(rc, n + 1, c) == rcnt(rc, n, c) + if rc[n] as int == c { 1int } else { 0int },
        rabs(rr, n + 1) == rabs(rr, n) + abs(rr[n] as int),
{
    lemma_isum_step(n, rsum_f(rc, rr, c));
    lemma_isum_step(n, rcnt_f(rc, c));
    lemma_isum_step(n, rabs_f(rr));
}

/// Records agreeing on the first `n` entries have the same sums.
pub proof fn lemma_rec_ext(rc: Seq<u32>, rr: Seq<i64>, rc2: Seq<u32>, rr2: Seq<i64>, n: int, c: int)
    requires
        forall|i: int| 0 <= i < n ==> rc[i] == rc2[i] && rr[i] == rr2[i],
    ensures
        rsum(rc, rr, n, c) == rsum(rc2, rr2, n, c),
        rcnt(rc, n, c) == rcnt(rc2, n, c),
        rabs(rr, n) == rabs(rr2, n),
{
    assert forall|i: int| 0 <= i < n implies #[trigger] rsum_f(rc, rr, c)(i) == rsum_f(rc2, rr2, c)(i) by {}
    assert forall|i: int| 0 <= i < n implies #[trigger] rcnt_f(rc, c)(i) == rcnt_f(rc2, c)(i) by {}
    assert forall|i: int| 0 <= i < n implies #[trigger] rabs_f(rr)(i) == rabs_f(rr2)(i) by {}
    lemma_isum_ext(n, rsum_f(rc, rr, c), rsum_f(rc2, rr2, c));
    lemma_isum_ext(n, rcnt_f(rc, c), rcnt_f(rc2, c));
    lemma_isum_ext(n, rabs_f(rr), rabs_f(rr2));
}

/// The sum of the records naming one customer is bounded by the absolute sum of all records; the counts and the
/// absolute sums are nonnegative and nondecreasing.
pub proof fn lemma_rec_bounds(rc: Seq<u32>, rr: Seq<i64>, n: int, c: int)
    requires n >= 0,
    ensures
        abs(rsum(rc, rr, n, c)) <= rabs(rr, n),
        rcnt(rc, n, c) >= 0,
        rabs(rr, n) >= 0,
    decreases n,
{
    if n > 0 {
        lemma_rec_bounds(rc, rr, n - 1, c);
        lemma_rec_step(rc, rr, n - 1, c);
    }
}

/// The absolute sum of records is nondecreasing in the count.
pub proof fn lemma_rabs_mono(rr: Seq<i64>, a: int, b: int)
    requires 0 <= a <= b,
    ensures rabs(rr, a) <= rabs(rr, b),
    decreases b - a,
{
    if a < b {
        lemma_rabs_mono(rr, a, b - 1);
        lemma_isum_step(b - 1, rabs_f(rr));
    }
}

/// Range sums telescope.
pub proof fn lemma_dsum_join(f: spec_fn(int) -> int, a: int, b: int, c: int)
    ensures dsum(f, a, b) + dsum(f, b, c) == dsum(f, a, c),
{
}

/// One more term of a range sum.
pub proof fn lemma_dsum_step(f: spec_fn(int) -> int, a: int, b: int)
    requires 0 <= b,
    ensures dsum(f, a, b + 1) == dsum(f, a, b) + f(b),
{
    lemma_isum_step(b, f);
}

/// A range sum of terms bounded in absolute value by `g` is bounded by the range sum of `g`.
pub proof fn lemma_dsum_abs(f: spec_fn(int) -> int, g: spec_fn(int) -> int, a: int, b: int)
    requires
        0 <= a <= b,
        forall|i: int| a <= i < b ==> abs(#[trigger] f(i)) <= g(i),
    ensures abs(dsum(f, a, b)) <= dsum(g, a, b),
    decreases b - a,
{
    if a < b {
        lemma_dsum_abs(f, g, a, b - 1);
        lemma_dsum_step(f, a, b - 1);
        lemma_dsum_step(g, a, b - 1);
        assert(abs(f(b - 1)) <= g(b - 1));
    }
}

/// A range sum of nonnegative terms is nonnegative.
pub proof fn lemma_dsum_nonneg(f: spec_fn(int) -> int, a: int, b: int)
    requires
        0 <= a <= b,
        forall|i: int| a <= i < b ==> #[trigger] f(i) >= 0,
    ensures dsum(f, a, b) >= 0,
    decreases b - a,
{
    if a < b {
        lemma_dsum_nonneg(f, a, b - 1);
        lemma_dsum_step(f, a, b - 1);
    }
}

/// A range sum whose terms vanish outside `[a, b)` is the whole sum over `[0, n)`.
pub proof fn lemma_dsum_whole(f: spec_fn(int) -> int, a: int, b: int, n: int)
    requires
        0 <= a <= b <= n,
        forall|i: int| 0 <= i < n && (i < a || i >= b) ==> #[trigger] f(i) == 0,
    ensures dsum(f, a, b) == isum(n, f),
{
    lemma_isum_prefix_zero(a, f);
    lemma_isum_suffix_zero(b, n, f);
}

/// A sum of nonnegative terms is positive exactly when some term is.
pub proof fn lemma_isum_pos(n: int, f: spec_fn(int) -> int)
    requires forall|i: int| 0 <= i < n ==> #[trigger] f(i) >= 0,
    ensures (isum(n, f) > 0) == (exists|i: int| 0 <= i < n && #[trigger] f(i) > 0),
    decreases n,
{
    if n > 0 {
        lemma_isum_pos(n - 1, f);
        lemma_isum_nonneg(n - 1, n - 1, f);
        if isum(n, f) > 0 {
            if f(n - 1) <= 0 {
                let i = choose|i: int| 0 <= i < n - 1 && #[trigger] f(i) > 0;
            }
        }
        if exists|i: int| 0 <= i < n && #[trigger] f(i) > 0 {
            let i = choose|i: int| 0 <= i < n && #[trigger] f(i) > 0;
            if i < n - 1 {
                assert(isum(n - 1, f) > 0);
            }
        }
    }
}

/// A customer has a returned lineitem in the window exactly when some order counts for it.
pub proof fn lemma_ccnt_pos(m: M, p: QP, c: int)
    ensures (ccnt(m, p, c) > 0) == (isum(m.o_n, chit_f(m, p, c)) > 0),
{
    let f = ccnt_f(m, p, c);
    let h = chit_f(m, p, c);
    assert forall|q: int| 0 <= q < m.o_n implies #[trigger] lcnt_f(m, q)(0) >= 0 && lcnt(m, q) >= 0 by {
        assert forall|t: int| 0 <= t < m.l_n implies #[trigger] lcnt_f(m, q)(t) >= 0 by {}
        if m.l_n >= 0 {
            lemma_isum_nonneg(0, m.l_n, lcnt_f(m, q));
        }
    }
    assert forall|q: int| 0 <= q < m.o_n implies #[trigger] f(q) >= 0 by {
        assert(lcnt_f(m, q)(0) >= 0 && lcnt(m, q) >= 0);
    }
    assert forall|q: int| 0 <= q < m.o_n implies #[trigger] h(q) >= 0 by {}
    lemma_isum_pos(m.o_n, f);
    lemma_isum_pos(m.o_n, h);
    if exists|q: int| 0 <= q < m.o_n && #[trigger] f(q) > 0 {
        let q = choose|q: int| 0 <= q < m.o_n && #[trigger] f(q) > 0;
        assert(h(q) > 0);
    }
    if exists|q: int| 0 <= q < m.o_n && #[trigger] h(q) > 0 {
        let q = choose|q: int| 0 <= q < m.o_n && #[trigger] h(q) > 0;
        assert(f(q) > 0);
    }
}

} // verus!
