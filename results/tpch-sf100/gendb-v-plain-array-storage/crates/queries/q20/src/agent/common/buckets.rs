//! Row triples kept in key-range buckets: bucket `u` holds the rows whose key `k` (first value of the triple) has
//! `bk(k, bm) == u`, the high 32 bits of `k * bm` (a multiply-shift that splits `[0, kmax)` into even key ranges for
//! `bm = nb * 2^32 / kmax`, `bucket_mult`); region `u` of the output buffer starts at element `3 * cap * u` and holds the bucket's
//! triples in the order they were appended, `cnt[u] <= cap` of them (`regions_ok`). `bucket_init` empties every
//! bucket, and `bucket_push` appends one row's triple to its bucket (`no_unwind`; false when the bucket is full).
//!
//! Layout: a list of `n` triples describing rows `rows` (`trip_at`): triple `t` at elements `base + 3 t ..= base + 3 t + 2`
//! is `(ka[rows[t]], kb[rows[t]], kc(rows[t]))` for two `i64` columns `ka`, `kb` and a value function `kc`.
use vstd::prelude::*;
use crate::agent::common::selection::*;

verus! {

/// The bucket of key `v`: the high 32 bits of `v * bm` (64-bit patterns, wrapping). Opaque: only `bucket_mult` and
/// `bucket_push` look inside.
#[verifier::opaque]
pub open spec fn bk(v: i64, bm: u64) -> int { ((v as u64).wrapping_mul(bm) >> 32u64) as int }

/// Buckets are not negative.
pub proof fn lemma_bk_nonneg(v: i64, bm: u64)
    ensures 0 <= bk(v, bm),
{
    reveal(bk);
}

/// The multiplier of `nb` buckets for the keys `[0, kmax)`: `nb * 2^32 / kmax`, so that every key below `kmax` has a
/// bucket below `nb`.
pub fn bucket_mult(kmax: u64, nb: usize) -> (bm: u64)
    requires 1 <= nb <= 64, 1 <= kmax <= 0x1_0000_0000,
    ensures forall|v: u64| v < kmax ==> #[trigger] bk(v as i64, bm) < nb,
{
    let n = nb as u64;
    let top = n * 0x1_0000_0000u64;
    let bm = top / kmax;
    proof {
        reveal(bk);
        assert(bm * kmax <= top) by (nonlinear_arith) requires bm == top / kmax, kmax >= 1;
        assert forall|v: u64| v < kmax implies #[trigger] bk(v as i64, bm) < nb by {
            assert((v as i64) as u64 == v);
            assert(v * bm < top) by (nonlinear_arith) requires v < kmax, bm * kmax <= top, top > 0;
            let x = v.wrapping_mul(bm);
            assert(x == v * bm);
            assert(x < top);
            assert(x >> 32u64 == x / 0x1_0000_0000u64) by (bit_vector);
            assert(x / 0x1_0000_0000u64 < n) by (nonlinear_arith) requires x < top, top == n * 0x1_0000_0000u64;
        }
    }
    bm
}

/// Row `r`'s key `ka[r]` lies in bucket `u`.
pub open spec fn kbucket(ka: Seq<i64>, bm: u64, u: int) -> spec_fn(int) -> bool { |r: int| bk(ka[r], bm) == u }

/// The `n` triples from element `base` on describe the rows `rows`.
pub open spec fn trip_at(buf: Seq<i64>, base: int, n: int, ka: Seq<i64>, kb: Seq<i64>, kc: spec_fn(int) -> int, rows: Seq<int>) -> bool {
    &&& n == rows.len() && 0 <= base && base + 3 * n <= buf.len()
    &&& forall|t: int| 0 <= t < n ==> buf[base + 3 * t] == ka[#[trigger] rows[t]] && buf[base + 3 * t + 1] == kb[rows[t]]
            && buf[base + 3 * t + 2] as int == kc(rows[t])
}

/// Writes outside a list's elements keep it.
pub proof fn lemma_trip_frame(b0: Seq<i64>, b1: Seq<i64>, base: int, n: int, ka: Seq<i64>, kb: Seq<i64>, kc: spec_fn(int) -> int,
    rows: Seq<int>, w: int)
    requires
        trip_at(b0, base, n, ka, kb, kc, rows), b1.len() == b0.len(),
        forall|i: int| 0 <= i < b0.len() && !(w <= i < w + 3) ==> b1[i] == b0[i],
        base + 3 * n <= w || w + 3 <= base,
    ensures trip_at(b1, base, n, ka, kb, kc, rows),
{
    assert forall|t: int| 0 <= t < n implies b1[base + 3 * t] == ka[#[trigger] rows[t]] && b1[base + 3 * t + 1] == kb[rows[t]]
        && b1[base + 3 * t + 2] as int == kc(rows[t]) by {
        assert(b1[base + 3 * t] == b0[base + 3 * t]);
        assert(b1[base + 3 * t + 1] == b0[base + 3 * t + 1]);
        assert(b1[base + 3 * t + 2] == b0[base + 3 * t + 2]);
    }
}

/// Writing row `r`'s triple right after a list extends it by `r`.
pub proof fn lemma_trip_push(b0: Seq<i64>, b1: Seq<i64>, base: int, n: int, ka: Seq<i64>, kb: Seq<i64>, kc: spec_fn(int) -> int,
    rows: Seq<int>, r: int)
    requires
        trip_at(b0, base, n, ka, kb, kc, rows), b1.len() == b0.len(), base + 3 * n + 3 <= b0.len(),
        forall|i: int| 0 <= i < base + 3 * n ==> b1[i] == b0[i],
        b1[base + 3 * n] == ka[r], b1[base + 3 * n + 1] == kb[r], b1[base + 3 * n + 2] as int == kc(r),
    ensures trip_at(b1, base, n + 1, ka, kb, kc, rows.push(r)),
{
    let rs = rows.push(r);
    assert forall|t: int| 0 <= t < n + 1 implies b1[base + 3 * t] == ka[#[trigger] rs[t]] && b1[base + 3 * t + 1] == kb[rs[t]]
        && b1[base + 3 * t + 2] as int == kc(rs[t]) by {
        if t < n {
            assert(rs[t] == rows[t]);
            assert(b1[base + 3 * t] == b0[base + 3 * t]);
            assert(b1[base + 3 * t + 1] == b0[base + 3 * t + 1]);
            assert(b1[base + 3 * t + 2] == b0[base + 3 * t + 2]);
        } else {
            assert(rs[t] == r);
        }
    }
}

/// Regions of `cap` triples for different buckets do not overlap, and all lie below `3 * cap * nb`.
pub proof fn lemma_regions(cap: int, u: int, b: int, nb: int)
    requires 0 <= cap, 0 <= u < nb, 0 <= b < nb,
    ensures
        u < b ==> 3 * cap * u + 3 * cap <= 3 * cap * b,
        b < u ==> 3 * cap * b + 3 * cap <= 3 * cap * u,
        3 * cap * b + 3 * cap <= 3 * cap * nb,
        0 <= 3 * cap * b,
{
    assert(u < b ==> 3 * cap * u + 3 * cap <= 3 * cap * b) by (nonlinear_arith) requires 0 <= cap;
    assert(b < u ==> 3 * cap * b + 3 * cap <= 3 * cap * u) by (nonlinear_arith) requires 0 <= cap;
    assert(3 * cap * b + 3 * cap <= 3 * cap * nb) by (nonlinear_arith) requires 0 <= cap, b < nb;
    assert(0 <= 3 * cap * b) by (nonlinear_arith) requires 0 <= cap, 0 <= b;
}

/// Every bucket `u < nb` of `out` holds the list `seqs(u)`, at most `cap` triples.
pub open spec fn regions_ok(out: Seq<i64>, cnt: Seq<usize>, nb: int, cap: int, ka: Seq<i64>, kb: Seq<i64>, kc: spec_fn(int) -> int,
    seqs: spec_fn(int) -> Seq<int>) -> bool {
    &&& cnt.len() >= nb && 3 * cap * nb <= out.len()
    &&& forall|u: int| 0 <= u < nb ==> #[trigger] cnt[u] <= cap && trip_at(out, 3 * cap * u, cnt[u] as int, ka, kb, kc, seqs(u))
}

/// Empty buckets (`no_unwind`): the counts of buckets `0 .. nb` become 0.
pub fn bucket_init(cnt: &mut Vec<usize>, nb: usize, Ghost(out): Ghost<Seq<i64>>, cap: usize, Ghost(ka): Ghost<Seq<i64>>,
    Ghost(kb): Ghost<Seq<i64>>, Ghost(kc): Ghost<spec_fn(int) -> int>, Ghost(seqs): Ghost<spec_fn(int) -> Seq<int>>)
    requires
        old(cnt)@.len() >= nb, 3 * cap * nb <= out.len(),
        forall|u: int| 0 <= u < nb ==> #[trigger] seqs(u) == Seq::<int>::empty(),
    ensures
        final(cnt)@.len() == old(cnt)@.len(),
        regions_ok(out, final(cnt)@, nb as int, cap as int, ka, kb, kc, seqs),
    no_unwind
{
    let mut z: usize = 0;
    while z < nb
        invariant
            z <= nb, cnt@.len() == old(cnt)@.len(), cnt@.len() >= nb,
            forall|u: int| 0 <= u < z ==> #[trigger] cnt@[u] == 0,
        decreases nb - z,
    {
        cnt[z] = 0;
        z = z + 1;
    }
    proof {
        assert forall|u: int| 0 <= u < nb implies #[trigger] cnt@[u] <= cap
            && trip_at(out, 3 * cap * u, cnt@[u] as int, ka, kb, kc, seqs(u)) by {
            lemma_regions(cap as int, u, u, nb as int);
        }
    }
}

/// Append row `r`'s triple `(a, b, c)` to bucket `bk(a, bm)` (`no_unwind`); a row of bucket `nb` or above is dropped.
/// Afterwards the buckets hold `seqs2`: `seqs` with `r` appended to its bucket. False when the bucket is full.
pub fn bucket_push(out: &mut Vec<i64>, cnt: &mut Vec<usize>, olen: usize, nb: usize, bm: u64, cap: usize, a: i64, b: i64, c: i64,
    Ghost(ka): Ghost<Seq<i64>>, Ghost(kb): Ghost<Seq<i64>>, Ghost(kc): Ghost<spec_fn(int) -> int>,
    Ghost(seqs): Ghost<spec_fn(int) -> Seq<int>>, Ghost(seqs2): Ghost<spec_fn(int) -> Seq<int>>, Ghost(r): Ghost<int>) -> (ok: bool)
    requires
        regions_ok(old(out)@, old(cnt)@, nb as int, cap as int, ka, kb, kc, seqs), olen == old(out)@.len(),
        1 <= nb <= 0x1_0000, a == ka[r], b == kb[r], c as int == kc(r),
        forall|u: int| 0 <= u < nb ==> #[trigger] seqs2(u) == if bk(a, bm) == u { seqs(u).push(r) } else { seqs(u) },
    ensures
        final(out)@.len() == old(out)@.len(), final(cnt)@.len() == old(cnt)@.len(),
        ok ==> regions_ok(final(out)@, final(cnt)@, nb as int, cap as int, ka, kb, kc, seqs2),
    no_unwind
{
    let h = (a as u64).wrapping_mul(bm) >> 32u64;
    proof { reveal(bk); }
    if h < nb as u64 {
        let bu = h as usize;
        let k = cnt[bu];
        if k >= cap {
            return false;
        }
        proof {
            lemma_regions(cap as int, bu as int, bu as int, nb as int);
            assert(3 * cap * bu + 3 * k + 3 <= olen);
        }
        let base = 3 * cap * bu;
        let ghost o0 = out@;
        let ghost c0 = cnt@;
        out[base + 3 * k] = a;
        out[base + 3 * k + 1] = b;
        out[base + 3 * k + 2] = c;
        cnt[bu] = k + 1;
        proof {
            let w = base + 3 * k;
            assert forall|u: int| 0 <= u < nb implies #[trigger] cnt@[u] <= cap
                && trip_at(out@, 3 * cap * u, cnt@[u] as int, ka, kb, kc, seqs2(u)) by {
                if u == bu as int {
                    lemma_trip_push(o0, out@, 3 * cap * u, c0[u] as int, ka, kb, kc, seqs(u), r);
                } else {
                    lemma_regions(cap as int, u, bu as int, nb as int);
                    assert(cnt@[u] == c0[u]);
                    lemma_trip_frame(o0, out@, 3 * cap * u, c0[u] as int, ka, kb, kc, seqs(u), w);
                }
            }
        }
    } else {
        proof {
            assert forall|u: int| 0 <= u < nb implies #[trigger] cnt@[u] <= cap
                && trip_at(out@, 3 * cap * u, cnt@[u] as int, ka, kb, kc, seqs2(u)) by {
                assert(seqs2(u) == seqs(u));
            }
        }
    }
    true
}

} // verus!
