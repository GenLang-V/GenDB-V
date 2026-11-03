//! Stable counting-sort partition of a buffer prefix of i64 keys by ascending, disjoint key ranges.
//!
//! `partition_prefix(keys, n, lo, hi, nb, boff, cur)` reorders `keys[0 .. n]` so that the keys of range `t`
//! (`lo[t] <= v < hi[t]`, `t < nb`) form the segment `keys[boff[t] .. boff[t + 1]]`, and the keys of no range the
//! last segment `keys[boff[nb] .. boff[nb + 1]]` (`boff[nb + 1] == n`). It needs `n` free slots after the prefix
//! (`2 n <= keys.len()`): the keys are scattered into `keys[n .. 2 n]` and copied back. Every key keeps its count
//! (`cnt_rng`), so the reordered prefix is a permutation of the old one, and the count of a key of range `t` in
//! segment `t` is its count in the whole prefix (`segs_ok`). Allocation-free and `no_unwind` (worker bodies);
//! O(n log nb) time.
use vstd::prelude::*;
use crate::gendb_entry::work::put;

verus! {

/// Occurrences of `v` in `s[lo .. hi]`.
pub open spec fn cnt_rng(s: Seq<i64>, v: int, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo { 0 } else { cnt_rng(s, v, lo, hi - 1) + if s[hi - 1] as int == v { 1nat } else { 0nat } }
}

/// The ranges `[lo[t], hi[t])` are ascending and disjoint.
pub open spec fn ranges_ok(lo: Seq<i64>, hi: Seq<i64>) -> bool {
    &&& lo.len() == hi.len()
    &&& forall|t: int| 0 <= t < lo.len() ==> #[trigger] lo[t] <= hi[t]
    &&& forall|t: int| 0 <= t < lo.len() - 1 ==> #[trigger] hi[t] <= lo[t + 1]
}

/// `v` lies in range `t`.
pub open spec fn in_rng(lo: Seq<i64>, hi: Seq<i64>, t: int, v: int) -> bool {
    0 <= t < lo.len() && lo[t] <= v < hi[t]
}

/// The bucket of `v`: the range holding it, or `lo.len()` when no range does.
pub open spec fn bucket(lo: Seq<i64>, hi: Seq<i64>, v: int) -> int {
    if exists|t: int| in_rng(lo, hi, t, v) { choose|t: int| in_rng(lo, hi, t, v) } else { lo.len() as int }
}

/// `l[0 .. bo[nb + 1]]` is cut into the segments `l[bo[t] .. bo[t + 1]]`, and a key of range `t` occurs in segment
/// `t` as often as in the whole list. Opaque: `lemma_seg_count` states what a reader needs.
#[verifier::opaque]
pub open spec fn segs_ok(l: Seq<i64>, bo: Seq<usize>, lo: Seq<i64>, hi: Seq<i64>) -> bool {
    let nb = lo.len() as int;
    &&& bo.len() == nb + 2
    &&& bo[0] == 0
    &&& bo[nb + 1] == l.len()
    &&& forall|t: int| 0 <= t <= nb ==> #[trigger] bo[t] <= bo[t + 1]
    &&& forall|t: int, v: int| #[trigger] in_rng(lo, hi, t, v) ==>
            cnt_rng(l, v, bo[t] as int, bo[t + 1] as int) == cnt_rng(l, v, 0, l.len() as int)
}

/// Segment `t` of a cut list: its bounds, and the count in it of every key of range `t`.
pub proof fn lemma_seg_count(l: Seq<i64>, bo: Seq<usize>, lo: Seq<i64>, hi: Seq<i64>, t: int)
    requires segs_ok(l, bo, lo, hi), 0 <= t < lo.len(),
    ensures
        bo.len() == lo.len() + 2,
        bo[t] <= bo[t + 1] <= l.len(),
        forall|v: int| lo[t] <= v < hi[t] ==> #[trigger] cnt_rng(l, v, bo[t] as int, bo[t + 1] as int)
            == cnt_rng(l, v, 0, l.len() as int),
{
    reveal(segs_ok);
    let nb = lo.len() as int;
    assert forall|u: int| t + 1 <= u <= nb + 1 implies #[trigger] bo[u] <= l.len() by {
        lemma_bo_le(bo, nb, u);
    }
    assert forall|v: int| lo[t] <= v < hi[t] implies #[trigger] cnt_rng(l, v, bo[t] as int, bo[t + 1] as int)
        == cnt_rng(l, v, 0, l.len() as int) by {
        assert(in_rng(lo, hi, t, v));
    }
}

/// Offsets that ascend to the end stay below it.
proof fn lemma_bo_le(bo: Seq<usize>, nb: int, u: int)
    requires
        bo.len() == nb + 2, 0 <= u <= nb + 1,
        forall|t: int| 0 <= t <= nb ==> #[trigger] bo[t] <= bo[t + 1],
    ensures bo[u] <= bo[nb + 1],
    decreases nb + 1 - u,
{
    if u < nb + 1 {
        lemma_bo_le(bo, nb, u + 1);
    }
}

// ------------------------------------------------------------------------------------------------ ranges

/// Range starts ascend.
pub proof fn lemma_lo_mono(lo: Seq<i64>, hi: Seq<i64>, a: int, b: int)
    requires ranges_ok(lo, hi), 0 <= a <= b < lo.len(),
    ensures lo[a] <= lo[b],
    decreases b - a,
{
    if a < b {
        lemma_lo_mono(lo, hi, a + 1, b);
        assert(lo[a] <= hi[a] && hi[a] <= lo[a + 1]);
    }
}

/// A key lies in at most one range.
pub proof fn lemma_rng_unique(lo: Seq<i64>, hi: Seq<i64>, t1: int, t2: int, v: int)
    requires ranges_ok(lo, hi), in_rng(lo, hi, t1, v), in_rng(lo, hi, t2, v),
    ensures t1 == t2,
{
    if t1 < t2 {
        lemma_lo_mono(lo, hi, t1 + 1, t2);
        assert(hi[t1] <= lo[t1 + 1]);
    } else if t2 < t1 {
        lemma_lo_mono(lo, hi, t2 + 1, t1);
        assert(hi[t2] <= lo[t2 + 1]);
    }
}

/// The bucket of a key of range `t` is `t`; a bucket is a range index or `lo.len()`.
pub proof fn lemma_bucket(lo: Seq<i64>, hi: Seq<i64>, v: int)
    requires ranges_ok(lo, hi),
    ensures
        0 <= bucket(lo, hi, v) <= lo.len(),
        bucket(lo, hi, v) < lo.len() ==> in_rng(lo, hi, bucket(lo, hi, v), v),
        forall|t: int| #[trigger] in_rng(lo, hi, t, v) ==> bucket(lo, hi, v) == t,
{
    if exists|t: int| in_rng(lo, hi, t, v) {
        let c = choose|t: int| in_rng(lo, hi, t, v);
        assert forall|t: int| #[trigger] in_rng(lo, hi, t, v) implies bucket(lo, hi, v) == t by {
            lemma_rng_unique(lo, hi, c, t, v);
        }
    }
}

/// Keys of different buckets differ.
pub proof fn lemma_bucket_ne(lo: Seq<i64>, hi: Seq<i64>, v: int, w: int)
    requires bucket(lo, hi, v) != bucket(lo, hi, w),
    ensures v != w,
{
}

/// The bucket of `v` (binary search over the range starts).
pub fn find_bucket(lo: &Vec<i64>, hi: &Vec<i64>, nb: usize, v: i64) -> (r: usize)
    requires ranges_ok(lo@, hi@), nb == lo@.len(),
    ensures r as int == bucket(lo@, hi@, v as int), r <= nb,
    no_unwind
{
    proof {
        lemma_bucket(lo@, hi@, v as int);
    }
    if nb == 0 {
        return nb;
    }
    if v < lo[0] {
        proof {
            assert forall|t: int| !(#[trigger] in_rng(lo@, hi@, t, v as int)) by {
                if 0 <= t < nb {
                    lemma_lo_mono(lo@, hi@, 0, t);
                }
            }
        }
        return nb;
    }
    let mut a: usize = 0;
    let mut b: usize = nb;
    while b - a > 1
        invariant
            ranges_ok(lo@, hi@), nb == lo@.len(),
            0 <= a < b <= nb,
            lo@[a as int] <= v,
            b < nb ==> lo@[b as int] > v,
        decreases b - a,
    {
        let m = a + (b - a) / 2;
        if lo[m] <= v {
            a = m;
        } else {
            b = m;
        }
    }
    if v < hi[a] {
        proof {
            assert(in_rng(lo@, hi@, a as int, v as int));
        }
        a
    } else {
        proof {
            assert forall|t: int| !(#[trigger] in_rng(lo@, hi@, t, v as int)) by {
                if 0 <= t < a {
                    lemma_lo_mono(lo@, hi@, t + 1, a as int);
                    assert(hi@[t] <= lo@[t + 1]);
                } else if a < t < nb {
                    lemma_lo_mono(lo@, hi@, b as int, t);
                }
            }
        }
        nb
    }
}

// ------------------------------------------------------------------------------------------------ counts

/// Keys of `s[0 .. m]` in bucket `t`.
pub open spec fn cntb(s: Seq<i64>, lo: Seq<i64>, hi: Seq<i64>, t: int, m: int) -> nat
    decreases m,
{
    if m <= 0 { 0 } else { cntb(s, lo, hi, t, m - 1) + if bucket(lo, hi, s[m - 1] as int) == t { 1nat } else { 0nat } }
}

/// Keys of `s[0 .. m]` in the buckets below `t` (the start of segment `t`).
pub open spec fn pre(s: Seq<i64>, lo: Seq<i64>, hi: Seq<i64>, t: int, m: int) -> nat
    decreases t,
{
    if t <= 0 { 0 } else { pre(s, lo, hi, t - 1, m) + cntb(s, lo, hi, t - 1, m) }
}

/// Bucket counts grow with the prefix.
pub proof fn lemma_cntb_mono(s: Seq<i64>, lo: Seq<i64>, hi: Seq<i64>, t: int, m1: int, m2: int)
    requires 0 <= m1 <= m2,
    ensures cntb(s, lo, hi, t, m1) <= cntb(s, lo, hi, t, m2),
    decreases m2,
{
    if m1 < m2 {
        lemma_cntb_mono(s, lo, hi, t, m1, m2 - 1);
    }
}

/// Segment starts ascend.
pub proof fn lemma_pre_mono(s: Seq<i64>, lo: Seq<i64>, hi: Seq<i64>, t1: int, t2: int, m: int)
    requires 0 <= t1 <= t2,
    ensures pre(s, lo, hi, t1, m) <= pre(s, lo, hi, t2, m),
    decreases t2,
{
    if t1 < t2 {
        lemma_pre_mono(s, lo, hi, t1, t2 - 1, m);
    }
}

/// One more key adds one to the segment starts above its bucket.
pub proof fn lemma_pre_step(s: Seq<i64>, lo: Seq<i64>, hi: Seq<i64>, t: int, m: int)
    requires 1 <= m, 0 <= t,
    ensures pre(s, lo, hi, t, m) == pre(s, lo, hi, t, m - 1) + if bucket(lo, hi, s[m - 1] as int) < t { 1nat } else { 0nat },
    decreases t,
{
    if t > 0 {
        lemma_pre_step(s, lo, hi, t - 1, m);
    }
}

/// No key, no segment start above 0.
pub proof fn lemma_pre_zero(s: Seq<i64>, lo: Seq<i64>, hi: Seq<i64>, t: int)
    ensures pre(s, lo, hi, t, 0) == 0,
    decreases t,
{
    if t > 0 {
        lemma_pre_zero(s, lo, hi, t - 1);
    }
}

/// All buckets together hold every key.
pub proof fn lemma_pre_total(s: Seq<i64>, lo: Seq<i64>, hi: Seq<i64>, m: int)
    requires ranges_ok(lo, hi), 0 <= m <= s.len(),
    ensures pre(s, lo, hi, lo.len() as int + 1, m) == m,
    decreases m,
{
    if m == 0 {
        lemma_pre_zero(s, lo, hi, lo.len() as int + 1);
    } else {
        lemma_pre_total(s, lo, hi, m - 1);
        lemma_pre_step(s, lo, hi, lo.len() as int + 1, m);
        lemma_bucket(lo, hi, s[m - 1] as int);
        assert(bucket(lo, hi, s[m - 1] as int) < lo.len() as int + 1);
    }
}

// ------------------------------------------------------------------------------------------------ range counts

/// A range count splits at an inner point.
pub proof fn lemma_rng_split(s: Seq<i64>, v: int, a: int, b: int, c: int)
    requires a <= b <= c,
    ensures cnt_rng(s, v, a, c) == cnt_rng(s, v, a, b) + cnt_rng(s, v, b, c),
    decreases c - b,
{
    if b < c {
        lemma_rng_split(s, v, a, b, c - 1);
    }
}

/// A write outside a range keeps its count.
pub proof fn lemma_rng_frame(s: Seq<i64>, p: int, x: i64, v: int, a: int, c: int)
    requires 0 <= p < s.len(), p < a || c <= p,
    ensures cnt_rng(s.update(p, x), v, a, c) == cnt_rng(s, v, a, c),
    decreases c - a,
{
    if a < c {
        lemma_rng_frame(s, p, x, v, a, c - 1);
    }
}

/// Equal elements give equal counts (the second range shifted by `d`).
pub proof fn lemma_rng_shift(s: Seq<i64>, t: Seq<i64>, v: int, a: int, c: int, d: int)
    requires forall|i: int| a <= i < c ==> #[trigger] s[i] == t[i + d],
    ensures cnt_rng(s, v, a, c) == cnt_rng(t, v, a + d, c + d),
    decreases c - a,
{
    if a < c {
        lemma_rng_shift(s, t, v, a, c - 1, d);
        assert(s[c - 1] == t[(c - 1) + d]);
    }
}

/// A range count of a prefix is that of the whole sequence.
pub proof fn lemma_rng_sub(s: Seq<i64>, n: int, v: int, a: int, c: int)
    requires 0 <= a, c <= n <= s.len(),
    ensures cnt_rng(s.subrange(0, n), v, a, c) == cnt_rng(s, v, a, c),
    decreases c - a,
{
    if a < c {
        lemma_rng_sub(s, n, v, a, c - 1);
    }
}

// ------------------------------------------------------------------------------------------------ the partition

/// The scatter's segment `t` so far: `s[n + pre(t) .. n + cur[t]]`.
pub open spec fn seg_cnt(s: Seq<i64>, k: Seq<i64>, lo: Seq<i64>, hi: Seq<i64>, n: int, cur: Seq<usize>, t: int, v: int) -> nat {
    cnt_rng(s, v, n + pre(k, lo, hi, t, n), n + cur[t])
}

/// The scatter state after the first `j` keys of `k[0 .. n]`: segment `t` holds the bucket-`t` keys of `k[0 .. j]`.
pub open spec fn scatter_inv(s: Seq<i64>, k: Seq<i64>, lo: Seq<i64>, hi: Seq<i64>, n: int, cur: Seq<usize>, j: int) -> bool {
    let nb = lo.len() as int;
    &&& s.len() == k.len()
    &&& cur.len() == nb + 1
    &&& forall|i: int| 0 <= i < n ==> #[trigger] s[i] == k[i]
    &&& forall|u: int| 0 <= u <= nb ==> #[trigger] cur[u] == pre(k, lo, hi, u, n) + cntb(k, lo, hi, u, j)
    &&& forall|u: int, v: int| 0 <= u <= nb ==> #[trigger] seg_cnt(s, k, lo, hi, n, cur, u, v)
            == if bucket(lo, hi, v) == u { cnt_rng(k, v, 0, j) } else { 0 }
}

/// Bucket counts of one more key.
proof fn lemma_cntb_step(k: Seq<i64>, lo: Seq<i64>, hi: Seq<i64>, u: int, j: int)
    requires 0 <= j,
    ensures cntb(k, lo, hi, u, j + 1) == cntb(k, lo, hi, u, j) + if bucket(lo, hi, k[j] as int) == u { 1nat } else { 0nat },
{
}

/// One scatter step: key `k[j]` of bucket `b` goes to slot `n + cur[b]`.
proof fn lemma_scatter_step(s: Seq<i64>, k: Seq<i64>, lo: Seq<i64>, hi: Seq<i64>, n: int, cur: Seq<usize>, j: int, b: int)
    requires
        ranges_ok(lo, hi),
        0 <= j < n, 2 * n <= k.len(), k.len() <= usize::MAX,
        scatter_inv(s, k, lo, hi, n, cur, j),
        b == bucket(lo, hi, k[j] as int),
        0 <= b <= lo.len(),
        pre(k, lo, hi, lo.len() as int + 1, n) == n,
    ensures
        n + cur[b] < 2 * n,
        cur[b] + 1 <= n,
        scatter_inv(s.update(n + cur[b], k[j]), k, lo, hi, n, cur.update(b, (cur[b] + 1) as usize), j + 1),
{
    let nb = lo.len() as int;
    let key = k[j];
    let p = n + cur[b];
    let s1 = s.update(p, key);
    let c1 = cur.update(b, (cur[b] + 1) as usize);
    lemma_cntb_step(k, lo, hi, b, j);
    lemma_cntb_mono(k, lo, hi, b, j + 1, n);
    assert(pre(k, lo, hi, b + 1, n) == pre(k, lo, hi, b, n) + cntb(k, lo, hi, b, n));
    lemma_pre_mono(k, lo, hi, b + 1, nb + 1, n);
    assert forall|i: int| 0 <= i < n implies #[trigger] s1[i] == k[i] by {
        assert(s1[i] == s[i]);
    }
    assert(cur[b] + 1 <= n);
    assert(c1[b] == cur[b] + 1);
    assert forall|u: int| 0 <= u <= nb implies #[trigger] c1[u] == pre(k, lo, hi, u, n) + cntb(k, lo, hi, u, j + 1) by {
        lemma_cntb_step(k, lo, hi, u, j);
        if u != b {
            assert(c1[u] == cur[u]);
        }
    }
    assert forall|u: int, v: int| 0 <= u <= nb implies #[trigger] seg_cnt(s1, k, lo, hi, n, c1, u, v)
        == if bucket(lo, hi, v) == u { cnt_rng(k, v, 0, j + 1) } else { 0 } by {
        assert(seg_cnt(s, k, lo, hi, n, cur, u, v) == if bucket(lo, hi, v) == u { cnt_rng(k, v, 0, j) } else { 0 });
        let a = n + pre(k, lo, hi, u, n);
        if u == b {
            // Segment b grows by the key at p.
            lemma_rng_frame(s, p, key, v, a, p);
            assert(cnt_rng(s1, v, a, p + 1) == cnt_rng(s1, v, a, p) + if s1[p] as int == v { 1nat } else { 0nat });
            if bucket(lo, hi, v) != b {
                lemma_bucket_ne(lo, hi, v, key as int);
            }
        } else {
            // Segment u lies wholly before or after p.
            lemma_cntb_mono(k, lo, hi, u, j, n);
            assert(pre(k, lo, hi, u + 1, n) == pre(k, lo, hi, u, n) + cntb(k, lo, hi, u, n));
            if u < b {
                lemma_pre_mono(k, lo, hi, u + 1, b, n);
            } else {
                lemma_pre_mono(k, lo, hi, b + 1, u, n);
            }
            lemma_rng_frame(s, p, key, v, a, n + cur[u] as int);
            if bucket(lo, hi, v) == u {
                lemma_bucket_ne(lo, hi, v, key as int);
            }
        }
    }
}

/// Phase 1: `boff[t + 1]` = the keys of `keys[0 .. n]` in bucket `t`.
fn count_buckets(keys: &Vec<i64>, n: usize, lo: &Vec<i64>, hi: &Vec<i64>, nb: usize, boff: &mut Vec<usize>)
    requires
        n <= keys@.len(),
        nb + 2 <= usize::MAX,
        ranges_ok(lo@, hi@),
        nb == lo@.len(),
        old(boff)@.len() == nb + 2,
        forall|t: int| 0 <= t < nb + 2 ==> #[trigger] old(boff)@[t] == 0,
    ensures
        final(boff)@.len() == nb + 2,
        final(boff)@[0] == 0,
        forall|t: int| 0 <= t <= nb ==> #[trigger] final(boff)@[t + 1] == cntb(keys@, lo@, hi@, t, n as int),
    no_unwind
{
    let ghost (k, lv, hv) = (keys@, lo@, hi@);
    proof {
        assert forall|t: int| 0 <= t <= nb implies #[trigger] boff@[t + 1] == cntb(k, lv, hv, t, 0) by {}
    }
    let mut j: usize = 0;
    while j < n
        invariant
            k == keys@, lv == lo@, hv == hi@, ranges_ok(lv, hv), nb == lv.len(), nb + 2 <= usize::MAX,
            n <= k.len(),
            j <= n,
            boff@.len() == nb + 2,
            boff@[0] == 0,
            forall|t: int| 0 <= t <= nb ==> #[trigger] boff@[t + 1] == cntb(k, lv, hv, t, j as int),
        decreases n - j,
    {
        let t = find_bucket(lo, hi, nb, keys[j]);
        proof {
            lemma_cntb_le(k, lv, hv, t as int, j as int);
        }
        let c = boff[t + 1];
        put(boff, t + 1, c + 1);
        proof {
            assert forall|u: int| 0 <= u <= nb implies #[trigger] boff@[u + 1] == cntb(k, lv, hv, u, j + 1) by {
                lemma_cntb_step(k, lv, hv, u, j as int);
            }
        }
        j = j + 1;
    }
}

/// Phase 2: prefix sums, `boff[t] = cur[t] = pre(t)`.
fn prefix_offsets(boff: &mut Vec<usize>, cur: &mut Vec<usize>, nb: usize, Ghost(k): Ghost<Seq<i64>>,
    Ghost(lv): Ghost<Seq<i64>>, Ghost(hv): Ghost<Seq<i64>>, Ghost(n): Ghost<int>)
    requires
        nb + 2 <= usize::MAX,
        nb == lv.len(),
        0 <= n <= usize::MAX,
        pre(k, lv, hv, nb + 1, n) == n,
        old(boff)@.len() == nb + 2,
        old(boff)@[0] == 0,
        forall|t: int| 0 <= t <= nb ==> #[trigger] old(boff)@[t + 1] == cntb(k, lv, hv, t, n),
        old(cur)@.len() == nb + 1,
    ensures
        final(boff)@.len() == nb + 2,
        final(cur)@.len() == nb + 1,
        forall|u: int| 0 <= u <= nb + 1 ==> #[trigger] final(boff)@[u] == pre(k, lv, hv, u, n),
        forall|u: int| 0 <= u <= nb ==> #[trigger] final(cur)@[u] == pre(k, lv, hv, u, n),
    no_unwind
{
    proof {
        assert forall|u: int| 0 < u <= nb + 1 implies #[trigger] boff@[u] == cntb(k, lv, hv, u - 1, n) by {
            assert(boff@[(u - 1) + 1] == cntb(k, lv, hv, u - 1, n));
        }
    }
    let mut t: usize = 0;
    while t < nb + 1
        invariant
            nb + 2 <= usize::MAX, nb == lv.len(), 0 <= n <= usize::MAX,
            pre(k, lv, hv, nb + 1, n) == n,
            t <= nb + 1,
            boff@.len() == nb + 2,
            cur@.len() == nb + 1,
            forall|u: int| 0 <= u <= t ==> #[trigger] boff@[u] == pre(k, lv, hv, u, n),
            forall|u: int| t < u <= nb + 1 ==> #[trigger] boff@[u] == cntb(k, lv, hv, u - 1, n),
            forall|u: int| 0 <= u < t ==> #[trigger] cur@[u] == pre(k, lv, hv, u, n),
        decreases nb + 1 - t,
    {
        proof {
            lemma_pre_mono(k, lv, hv, t + 1, nb + 1, n);
            assert(pre(k, lv, hv, t + 1, n) == pre(k, lv, hv, t as int, n) + cntb(k, lv, hv, t as int, n));
        }
        let s = boff[t + 1] + boff[t];
        put(boff, t + 1, s);
        let p = boff[t];
        put(cur, t, p);
        t = t + 1;
    }
}

/// Phase 3: scatter each key `keys[j]` (`j < n`) of bucket `b` to `keys[n + cur[b]]`, in input order.
fn scatter(keys: &mut Vec<i64>, n: usize, lo: &Vec<i64>, hi: &Vec<i64>, nb: usize, cur: &mut Vec<usize>)
    requires
        n <= old(keys)@.len() - n,
        old(keys)@.len() <= usize::MAX,
        nb + 2 <= usize::MAX,
        ranges_ok(lo@, hi@),
        nb == lo@.len(),
        pre(old(keys)@, lo@, hi@, nb + 1, n as int) == n,
        old(cur)@.len() == nb + 1,
        forall|u: int| 0 <= u <= nb ==> #[trigger] old(cur)@[u] == pre(old(keys)@, lo@, hi@, u, n as int),
    ensures
        scatter_inv(final(keys)@, old(keys)@, lo@, hi@, n as int, final(cur)@, n as int),
    no_unwind
{
    let ghost (k, lv, hv) = (keys@, lo@, hi@);
    let ghost nn = n as int;
    proof {
        assert forall|u: int| 0 <= u <= nb implies #[trigger] cur@[u] == pre(k, lv, hv, u, nn) + cntb(k, lv, hv, u, 0) by {}
        assert forall|u: int, v: int| 0 <= u <= nb implies #[trigger] seg_cnt(keys@, k, lv, hv, nn, cur@, u, v)
            == if bucket(lv, hv, v) == u { cnt_rng(k, v, 0, 0) } else { 0 } by {}
    }
    let mut j: usize = 0;
    while j < n
        invariant
            lv == lo@, hv == hi@, ranges_ok(lv, hv), nb == lv.len(), nn == n, nb + 2 <= usize::MAX,
            n <= k.len() - n, k.len() <= usize::MAX,
            pre(k, lv, hv, nb + 1, nn) == nn,
            j <= n,
            scatter_inv(keys@, k, lv, hv, nn, cur@, j as int),
        decreases n - j,
    {
        let key = keys[j];
        let b = find_bucket(lo, hi, nb, key);
        proof {
            assert(key == k[j as int]);
            lemma_scatter_step(keys@, k, lv, hv, nn, cur@, j as int, b as int);
        }
        let c = cur[b];
        put(keys, n + c, key);
        put(cur, b, c + 1);
        j = j + 1;
    }
}

/// Phase 4: `keys[i] = keys[n + i]` for `i < n`.
fn copy_back(keys: &mut Vec<i64>, n: usize)
    requires n <= old(keys)@.len() - n, old(keys)@.len() <= usize::MAX,
    ensures
        final(keys)@.len() == old(keys)@.len(),
        forall|i: int| 0 <= i < n ==> #[trigger] final(keys)@[i] == old(keys)@[i + n],
    no_unwind
{
    let ghost sc = keys@;
    let mut j: usize = 0;
    while j < n
        invariant
            n <= sc.len() - n, sc.len() <= usize::MAX,
            j <= n,
            keys@.len() == sc.len(),
            forall|i: int| 0 <= i < j ==> #[trigger] keys@[i] == sc[i + n],
            forall|i: int| j <= i < sc.len() ==> #[trigger] keys@[i] == sc[i],
        decreases n - j,
    {
        let x = keys[n + j];
        put(keys, j, x);
        j = j + 1;
    }
}

/// The scattered segments, summed over the buckets below `t`.
proof fn lemma_segs_sum(s: Seq<i64>, k: Seq<i64>, lo: Seq<i64>, hi: Seq<i64>, n: int, v: int, t: int)
    requires
        0 <= t <= lo.len() + 1,
        forall|u: int| 0 <= u <= lo.len() ==> #[trigger] cnt_rng(s, v, n + pre(k, lo, hi, u, n), n + pre(k, lo, hi, u + 1, n))
            == if bucket(lo, hi, v) == u { cnt_rng(k, v, 0, n) } else { 0 },
    ensures
        cnt_rng(s, v, n, n + pre(k, lo, hi, t, n)) == if bucket(lo, hi, v) < t { cnt_rng(k, v, 0, n) } else { 0 },
    decreases t,
{
    if t > 0 {
        lemma_segs_sum(s, k, lo, hi, n, v, t - 1);
        lemma_pre_mono(k, lo, hi, t - 1, t, n);
        lemma_rng_split(s, v, n, n + pre(k, lo, hi, t - 1, n), n + pre(k, lo, hi, t, n));
        assert(cnt_rng(s, v, n + pre(k, lo, hi, t - 1, n), n + pre(k, lo, hi, (t - 1) + 1, n))
            == if bucket(lo, hi, v) == t - 1 { cnt_rng(k, v, 0, n) } else { 0 });
    }
}

/// The copied-back prefix has the counts and segments of the scatter.
proof fn lemma_result(out: Seq<i64>, sc: Seq<i64>, k: Seq<i64>, lo: Seq<i64>, hi: Seq<i64>, n: int, bo: Seq<usize>,
    cur: Seq<usize>)
    requires
        ranges_ok(lo, hi),
        0 <= n, 2 * n <= k.len(), out.len() == k.len(),
        scatter_inv(sc, k, lo, hi, n, cur, n),
        pre(k, lo, hi, lo.len() as int + 1, n) == n,
        forall|i: int| 0 <= i < n ==> #[trigger] out[i] == sc[i + n],
        bo.len() == lo.len() + 2,
        forall|u: int| 0 <= u <= lo.len() + 1 ==> #[trigger] bo[u] == pre(k, lo, hi, u, n),
    ensures
        forall|v: int| #[trigger] cnt_rng(out, v, 0, n) == cnt_rng(k, v, 0, n),
        segs_ok(out.subrange(0, n), bo, lo, hi),
{
    reveal(segs_ok);
    let nb = lo.len() as int;
    let l = out.subrange(0, n);
    // Each scattered segment is full: cur[u] = pre(u + 1).
    assert forall|u: int, v: int| 0 <= u <= nb implies #[trigger] cnt_rng(sc, v, n + pre(k, lo, hi, u, n), n + pre(k, lo, hi, u + 1, n))
        == if bucket(lo, hi, v) == u { cnt_rng(k, v, 0, n) } else { 0 } by {
        assert(pre(k, lo, hi, u + 1, n) == pre(k, lo, hi, u, n) + cntb(k, lo, hi, u, n));
        assert(seg_cnt(sc, k, lo, hi, n, cur, u, v) == if bucket(lo, hi, v) == u { cnt_rng(k, v, 0, n) } else { 0 });
    }
    assert forall|v: int| #[trigger] cnt_rng(out, v, 0, n) == cnt_rng(k, v, 0, n) by {
        lemma_rng_shift(out, sc, v, 0, n, n);
        lemma_bucket(lo, hi, v);
        lemma_segs_sum(sc, k, lo, hi, n, v, nb + 1);
    }
    assert(bo[0] == 0) by {
        lemma_pre_zero_t(k, lo, hi, n);
    }
    assert forall|u: int| 0 <= u <= nb implies #[trigger] bo[u] <= bo[u + 1] by {
        lemma_pre_mono(k, lo, hi, u, u + 1, n);
    }
    assert forall|u: int, v: int| #[trigger] in_rng(lo, hi, u, v) implies
        cnt_rng(l, v, bo[u] as int, bo[u + 1] as int) == cnt_rng(l, v, 0, l.len() as int) by {
        lemma_bucket(lo, hi, v);
        lemma_pre_mono(k, lo, hi, u, u + 1, n);
        lemma_pre_mono(k, lo, hi, u + 1, nb + 1, n);
        let a = pre(k, lo, hi, u, n) as int;
        let c = pre(k, lo, hi, u + 1, n) as int;
        assert forall|i: int| a <= i < c implies #[trigger] out[i] == sc[i + n] by {}
        lemma_rng_shift(out, sc, v, a, c, n);
        lemma_rng_sub(out, n, v, a, c);
        assert(cnt_rng(sc, v, a + n, c + n) == cnt_rng(sc, v, n + pre(k, lo, hi, u, n), n + pre(k, lo, hi, u + 1, n)));
        lemma_rng_sub(out, n, v, 0, n);
    }
}

/// The first segment starts at 0.
proof fn lemma_pre_zero_t(k: Seq<i64>, lo: Seq<i64>, hi: Seq<i64>, n: int)
    ensures pre(k, lo, hi, 0, n) == 0,
{
}

/// Reorders `keys[0 .. n]` into the segments of the ranges `[lo[t], hi[t])` (see the module header). `boff` comes in
/// zeroed with `nb + 2` slots and leaves with the segment offsets; `cur` (`nb + 1` slots) is scratch.
pub fn partition_prefix(keys: &mut Vec<i64>, n: usize, lo: &Vec<i64>, hi: &Vec<i64>, nb: usize, boff: &mut Vec<usize>,
    cur: &mut Vec<usize>)
    requires
        n <= old(keys)@.len() - n,
        old(keys)@.len() <= usize::MAX,
        nb + 2 <= usize::MAX,
        ranges_ok(lo@, hi@),
        nb == lo@.len(),
        old(boff)@.len() == nb + 2,
        forall|t: int| 0 <= t < nb + 2 ==> #[trigger] old(boff)@[t] == 0,
        old(cur)@.len() == nb + 1,
    ensures
        final(keys)@.len() == old(keys)@.len(),
        forall|v: int| #[trigger] cnt_rng(final(keys)@, v, 0, n as int) == cnt_rng(old(keys)@, v, 0, n as int),
        segs_ok(final(keys)@.subrange(0, n as int), final(boff)@, lo@, hi@),
    no_unwind
{
    let ghost k = keys@;
    proof {
        lemma_pre_total(k, lo@, hi@, n as int);
    }
    count_buckets(keys, n, lo, hi, nb, boff);
    prefix_offsets(boff, cur, nb, Ghost(k), Ghost(lo@), Ghost(hi@), Ghost(n as int));
    scatter(keys, n, lo, hi, nb, cur);
    let ghost sc = keys@;
    let ghost cs = cur@;
    copy_back(keys, n);
    proof {
        lemma_result(keys@, sc, k, lo@, hi@, n as int, boff@, cs);
    }
}

/// A bucket count never exceeds the prefix length.
pub proof fn lemma_cntb_le(s: Seq<i64>, lo: Seq<i64>, hi: Seq<i64>, t: int, m: int)
    requires 0 <= m,
    ensures cntb(s, lo, hi, t, m) <= m,
    decreases m,
{
    if m > 0 {
        lemma_cntb_le(s, lo, hi, t, m - 1);
    }
}

} // verus!
