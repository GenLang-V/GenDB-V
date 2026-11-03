//! Task ranges: cutting `[0, n)` into consecutive ranges of about equal length (`split_range`) or of about equal
//! weight (`weight_cuts`), and the shift of a power-of-two block size (`pow2_shift`).
use vstd::prelude::*;
use vstd::arithmetic::power2::{pow2, lemma2_to64, lemma_pow2_unfold};

verus! {

/// `bnd` cuts `[0, n)` into the consecutive ranges `[bnd[k], bnd[k + 1])`.
pub open spec fn cuts(bnd: Seq<usize>, n: int) -> bool {
    &&& bnd.len() >= 1
    &&& bnd[0] == 0
    &&& bnd[bnd.len() - 1] == n
    &&& forall|k: int| 0 <= k < bnd.len() - 1 ==> #[trigger] bnd[k] <= bnd[k + 1]
}

/// Cuts `[0, n)` into at most `k` ranges of about `n / k` rows whose inner bounds are multiples of `align`.
pub fn split_range(n: usize, k: usize, align: usize) -> (r: Vec<usize>)
    requires k >= 1, align >= 1,
    ensures cuts(r@, n as int), r@.len() <= k + 1,
{
    let q = n / k;
    let per0 = if q < usize::MAX { q + 1 } else { q };
    let rem = per0 % align;
    let per = if rem == 0 { per0 } else if per0 <= usize::MAX - align { per0 + (align - rem) } else { per0 };
    let mut out: Vec<usize> = Vec::new();
    out.push(0);
    let mut x: usize = 0;
    let mut cnt: usize = 0;
    while x < n
        invariant
            out@.len() == cnt + 1, out@[0] == 0, out@[cnt as int] == x, x <= n, per >= 1,
            cnt <= k, x < n ==> cnt < k,
            forall|j: int| 0 <= j < cnt ==> #[trigger] out@[j] <= out@[j + 1],
        decreases n - x,
    {
        let nx = if cnt + 1 >= k || n - x <= per { n } else { x + per };
        out.push(nx);
        x = nx;
        cnt = cnt + 1;
    }
    out
}

/// `a + b`, or `u64::MAX` when it does not fit.
fn sat_add(a: u64, b: u64) -> (r: u64)
{
    if a <= u64::MAX - b { a + b } else { u64::MAX }
}

/// Cuts `[0, w.len())` into at most `k` ranges of about equal total weight (`w[i]` the weight of item `i`): a range
/// closes once its weight reaches `total / k + 1`. Any weights give valid cuts; the weights only steer the balance.
pub fn weight_cuts(w: &Vec<u64>, k: usize) -> (r: Vec<usize>)
    requires k >= 1,
    ensures cuts(r@, w@.len() as int), r@.len() <= k + 1,
{
    let n = w.len();
    let mut total: u64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant i <= n, n == w@.len(),
        decreases n - i,
    {
        total = sat_add(total, w[i]);
        i = i + 1;
    }
    let share = total / (k as u64);
    let per: u64 = if share < u64::MAX { share + 1 } else { share };
    let mut out: Vec<usize> = Vec::new();
    out.push(0);
    let mut acc: u64 = 0;
    let mut cnt: usize = 0;
    let mut q: usize = 0;
    while q < n
        invariant
            n == w@.len(), q <= n, k >= 1, cnt < k,
            out@.len() == cnt + 1, out@[0] == 0, out@[cnt as int] <= q,
            forall|j: int| 0 <= j < cnt ==> #[trigger] out@[j] <= out@[j + 1],
        decreases n - q,
    {
        acc = sat_add(acc, w[q]);
        q = q + 1;
        if acc >= per && cnt + 1 < k && q < n {
            out.push(q);
            cnt = cnt + 1;
            acc = 0;
        }
    }
    out.push(n);
    out
}

/// Pads cuts of `[0, n)` with empty ranges at the end up to `len` bounds.
pub fn pad_cuts(v: Vec<usize>, n: usize, len: usize) -> (r: Vec<usize>)
    requires cuts(v@, n as int), v@.len() <= len,
    ensures cuts(r@, n as int), r@.len() == len,
{
    let mut r = v;
    while r.len() < len
        invariant cuts(r@, n as int), r@.len() <= len,
        decreases len - r@.len(),
    {
        let ghost r0 = r@;
        r.push(n);
        proof {
            assert forall|k: int| 0 <= k < r@.len() - 1 implies #[trigger] r@[k] <= r@[k + 1] by {
                if k < r0.len() - 1 {
                    assert(r@[k] == r0[k] && r@[k + 1] == r0[k + 1]);
                }
            }
        }
    }
    r
}

/// `s` with `bs == 2^s` when `s < 32`; 32 when `bs` is no power of two below `2^32`.
pub fn pow2_shift(bs: usize) -> (r: u32)
    ensures r < 32 ==> bs as nat == pow2(r as nat),
{
    let mut s: u32 = 0;
    let mut p: usize = 1;
    proof {
        lemma2_to64();
    }
    while s < 31
        invariant s <= 31, p as nat == pow2(s as nat),
        decreases 31 - s,
    {
        if p == bs {
            return s;
        }
        proof {
            lemma_pow2_unfold((s + 1) as nat);
            lemma2_to64();
            vstd::arithmetic::power2::lemma_pow2_strictly_increases(s as nat, 31);
        }
        p = p * 2;
        s = s + 1;
    }
    if p == bs {
        return s;
    }
    32
}

} // verus!
