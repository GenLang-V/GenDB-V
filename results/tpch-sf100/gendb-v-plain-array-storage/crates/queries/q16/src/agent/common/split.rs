//! Splits of `0..n` into at most `k` consecutive non-empty ranges: of nearly equal length (`split_ranges`) or of
//! linearly growing length (`split_weighted`); and the fact that every position lies in one of them (`lemma_covered`).
use vstd::prelude::*;

verus! {

/// `rs` are consecutive non-empty ranges from `0` to `n`.
pub open spec fn covers(rs: Seq<(usize, usize)>, n: int) -> bool {
    &&& rs.len() >= 1
    &&& rs[0].0 == 0
    &&& rs[rs.len() - 1].1 == n
    &&& forall|i: int| 0 <= i < rs.len() ==> (#[trigger] rs[i]).0 < rs[i].1
    &&& forall|i: int| 0 <= i < rs.len() - 1 ==> (#[trigger] rs[i]).1 == rs[i + 1].0
}

/// Ranges are ordered: an earlier range ends no later than a later one starts.
pub proof fn lemma_ordered(rs: Seq<(usize, usize)>, n: int, i: int, j: int)
    requires covers(rs, n), 0 <= i < j < rs.len(),
    ensures rs[i].1 <= rs[j].0,
    decreases j - i,
{
    if j == i + 1 {
        assert(rs[i].1 == rs[i + 1].0);
    } else {
        lemma_ordered(rs, n, i, j - 1);
        assert(rs[j - 1].0 < rs[j - 1].1);
        assert(rs[j - 1].1 == rs[j].0);
    }
}

/// Every range lies in `0..n`.
pub proof fn lemma_in_bounds(rs: Seq<(usize, usize)>, n: int, i: int)
    requires covers(rs, n), 0 <= i < rs.len(),
    ensures 0 <= rs[i].0 < rs[i].1 <= n,
{
    if i > 0 { lemma_ordered(rs, n, 0, i); }
    if i < rs.len() - 1 { lemma_ordered(rs, n, i, rs.len() - 1); }
}

/// Every position of `0..n` lies in some range.
pub proof fn lemma_covered(rs: Seq<(usize, usize)>, n: int, x: int)
    requires covers(rs, n), 0 <= x < n,
    ensures exists|i: int| 0 <= i < rs.len() && rs[i].0 <= x < #[trigger] rs[i].1,
{
    lemma_covered_upto(rs, n, x, rs.len() - 1);
}

proof fn lemma_covered_upto(rs: Seq<(usize, usize)>, n: int, x: int, j: int)
    requires covers(rs, n), 0 <= x < rs[j].1, 0 <= j < rs.len(),
    ensures exists|i: int| 0 <= i <= j && rs[i].0 <= x < #[trigger] rs[i].1,
    decreases j,
{
    if x >= rs[j].0 {
    } else {
        assert(j > 0);
        assert(rs[j - 1].1 == rs[j].0);
        lemma_covered_upto(rs, n, x, j - 1);
    }
}

/// `0..n` split into at most `k` ranges of nearly equal length (`ceil(n / k)` each, the last possibly shorter).
pub fn split_ranges(n: usize, k: usize) -> (rs: Vec<(usize, usize)>)
    requires n >= 1, k >= 1,
    ensures covers(rs@, n as int), rs@.len() <= k,
{
    let chunk = (n - 1) / k + 1;
    proof {
        let q = ((n - 1) as int) / (k as int);
        let r = ((n - 1) as int) % (k as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod((n - 1) as int, k as int);
        vstd::arithmetic::div_mod::lemma_mod_bound((n - 1) as int, k as int);
        assert(chunk * k >= n) by (nonlinear_arith)
            requires chunk == q + 1, n - 1 == k * q + r, 0 <= r < k;
        assert(chunk >= 1);
    }
    let mut rs: Vec<(usize, usize)> = Vec::new();
    let mut lo: usize = 0;
    while lo < n
        invariant
            lo <= n, chunk >= 1, chunk * k >= n, k >= 1,
            lo < n ==> lo == rs@.len() * chunk,
            lo < n ==> rs@.len() < k,
            rs@.len() <= k,
            rs@.len() > 0 ==> lo == rs@[rs@.len() - 1].1 && rs@[0].0 == 0,
            rs@.len() == 0 ==> lo == 0,
            forall|i: int| 0 <= i < rs@.len() ==> (#[trigger] rs@[i]).0 < rs@[i].1,
            forall|i: int| 0 <= i < rs@.len() - 1 ==> (#[trigger] rs@[i]).1 == rs@[i + 1].0,
        decreases n - lo,
    {
        let hi = if n - lo > chunk { lo + chunk } else { n };
        let ghost old_rs = rs@;
        rs.push((lo, hi));
        proof {
            assert(rs@.len() == old_rs.len() + 1);
            assert forall|i: int| 0 <= i < rs@.len() - 1 implies (#[trigger] rs@[i]).1 == rs@[i + 1].0 by {
                if i < old_rs.len() - 1 { assert(rs@[i] == old_rs[i] && rs@[i + 1] == old_rs[i + 1]); }
                else { assert(rs@[i] == old_rs[i]); }
            }
            if hi < n {
                assert(hi == rs@.len() * chunk) by (nonlinear_arith)
                    requires hi == lo + chunk, lo == old_rs.len() * chunk, rs@.len() == old_rs.len() + 1;
                assert(rs@.len() < k) by (nonlinear_arith)
                    requires hi == rs@.len() * chunk, hi < n, chunk * k >= n, chunk >= 1;
            }
        }
        lo = hi;
    }
    rs
}


/// `0..n` split into at most `k` consecutive non-empty ranges whose lengths grow linearly with the range index:
/// range `t` (of `k`) gets about `1 + w * (2t / k - 1)` times the average length, `w = num / 100`. Its boundary `t`
/// is `n * F(t / k)` rounded down, `F(x) = x + w * (x^2 - x)`; an empty range is skipped. Used for tasks that start
/// one after another from the last (`fork_join` spawns from the back): the tasks started later get less work.
/// Falls back to `split_ranges` when `n < 64 * k`.
pub fn split_weighted(n: usize, k: usize, num: u64) -> (rs: Vec<(usize, usize)>)
    requires n >= 1, 1 <= k <= 1024, num <= 100,
    ensures covers(rs@, n as int), rs@.len() <= k,
{
    if k == 1 || n < 64 * k {
        return split_ranges(n, k);
    }
    let kk = k as u128;
    let nn = n as u128;
    let nm = num as u128;
    proof {
        assert(kk * kk <= 1024 * 1024) by (nonlinear_arith) requires 1 <= kk <= 1024;
    }
    let d = kk * kk * 100;
    let mut rs: Vec<(usize, usize)> = Vec::new();
    let mut lo: usize = 0;
    let mut t: usize = 1;
    while t <= k
        invariant
            1 <= k <= 1024, kk == k, nn == n, nm == num, num <= 100, d == kk * kk * 100, n >= 1,
            1 <= t <= k + 1, lo <= n, rs@.len() <= t - 1,
            rs@.len() > 0 ==> lo == rs@[rs@.len() - 1].1 && rs@[0].0 == 0,
            rs@.len() == 0 ==> lo == 0,
            t == k + 1 ==> lo == n,
            forall|i: int| 0 <= i < rs@.len() ==> (#[trigger] rs@[i]).0 < rs@[i].1,
            forall|i: int| 0 <= i < rs@.len() - 1 ==> (#[trigger] rs@[i]).1 == rs@[i + 1].0,
        decreases k + 1 - t,
    {
        let tt = t as u128;
        proof {
            assert(nm * tt <= 100 * 1024) by (nonlinear_arith) requires nm <= 100, 1 <= tt <= 1024;
            assert(tt * kk <= 1024 * 1024) by (nonlinear_arith) requires 1 <= tt <= kk <= 1024;
            assert(nm * tt * (kk - tt) <= tt * kk * 100) by (nonlinear_arith)
                requires nm <= 100, 1 <= tt <= kk;
            assert(tt * kk * 100 <= 1024 * 1024 * 100) by (nonlinear_arith) requires 1 <= tt <= kk <= 1024;
            assert(d >= 1) by (nonlinear_arith) requires d == kk * kk * 100, kk >= 1;
        }
        // F(t / k) * k^2 * 100.
        let f = tt * kk * 100 - nm * tt * (kk - tt);
        proof {
            assert(nn * f <= 0x1_0000_0000_0000_0000 * (1024 * 1024 * 100)) by (nonlinear_arith)
                requires nn < 0x1_0000_0000_0000_0000, f <= 1024 * 1024 * 100;
        }
        let q = nn * f / d;
        let hi: usize = if t == k { n } else if q >= nn { n } else { q as usize };
        if hi > lo {
            let ghost old_rs = rs@;
            rs.push((lo, hi));
            proof {
                assert forall|i: int| 0 <= i < rs@.len() - 1 implies (#[trigger] rs@[i]).1 == rs@[i + 1].0 by {
                    if i < old_rs.len() - 1 { assert(rs@[i] == old_rs[i] && rs@[i + 1] == old_rs[i + 1]); }
                    else { assert(rs@[i] == old_rs[i]); }
                }
                assert forall|i: int| 0 <= i < rs@.len() implies (#[trigger] rs@[i]).0 < rs@[i].1 by {
                    if i < old_rs.len() { assert(rs@[i] == old_rs[i]); }
                }
                if old_rs.len() > 0 { assert(rs@[0] == old_rs[0]); }
            }
            lo = hi;
        }
        t = t + 1;
    }
    proof {
        assert(rs@.len() > 0);
    }
    rs
}

} // verus!
