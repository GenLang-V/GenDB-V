//! The run directory of a frame-of-reference key column: one pass over the stored rows splits them into maximal
//! runs of equal key (a run ends where the next row's key differs), recording each run's row count (U8; a longer
//! run makes the build give up, mode 0) and the start row of every `stride`-th run.
//!
//! Proof: the loop keeps the finished runs (`runs_built` over the rows before the current run's start `s`) and the
//! current run `[s, j)` of key `ck`; `rstart` of a longer length sequence agrees on every earlier run
//! (`lemma_rstart_push`), so finished runs stay finished.
use vstd::prelude::*;
use crate::stores::liruns::interface::{rstart, start_ok};

verus! {

/// Key of stored row `j`: `kb[j / bs] + kc[j]` (opaque: the run proofs only compare keys).
#[verifier::opaque]
pub open spec fn fkey(kc: Seq<u32>, kb: Seq<i64>, bs: int, j: int) -> int {
    kb[j / bs] as int + kc[j] as int
}

/// Every row of run `r` has the key of the run's first row.
#[verifier::opaque]
pub open spec fn rs_same(kc: Seq<u32>, kb: Seq<i64>, bs: int, lens: Seq<u8>, r: int) -> bool {
    forall|j: int| rstart(lens, r) <= j < rstart(lens, r + 1) ==> #[trigger] fkey(kc, kb, bs, j) == fkey(kc, kb, bs, rstart(lens, r))
}

/// The rows on both sides of the start of run `r` have different keys.
pub open spec fn rs_cut(kc: Seq<u32>, kb: Seq<i64>, bs: int, lens: Seq<u8>, r: int) -> bool {
    fkey(kc, kb, bs, rstart(lens, r) - 1) != fkey(kc, kb, bs, rstart(lens, r))
}

/// The finished runs `lens` cover rows `[0, rstart(lens, len))`; `starts` samples every `stride`-th start.
#[verifier::opaque]
pub open spec fn runs_built(kc: Seq<u32>, kb: Seq<i64>, bs: int, lens: Seq<u8>, starts: Seq<u64>, stride: int) -> bool {
    &&& forall|r: int| 0 <= r < lens.len() ==> #[trigger] lens[r] >= 1 && rs_same(kc, kb, bs, lens, r)
    &&& forall|r: int| 0 < r < lens.len() ==> #[trigger] rs_cut(kc, kb, bs, lens, r)
    &&& forall|b: int| 0 <= b < starts.len() ==> #[trigger] start_ok(lens, starts, stride, b)
}

/// A pushed length leaves the earlier starts unchanged.
pub proof fn lemma_rstart_push(lens: Seq<u8>, x: u8, r: int)
    requires 0 <= r <= lens.len(),
    ensures rstart(lens.push(x), r) == rstart(lens, r),
    decreases r,
{
    if r > 0 {
        lemma_rstart_push(lens, x, r - 1);
        assert(lens.push(x)[r - 1] == lens[r - 1]);
    }
}

/// Starts never decrease.
pub proof fn lemma_rstart_mono(lens: Seq<u8>, a: int, b: int)
    requires 0 <= a <= b <= lens.len(),
    ensures rstart(lens, a) <= rstart(lens, b),
    decreases b - a,
{
    if a < b {
        lemma_rstart_mono(lens, a, b - 1);
    }
}

/// A pushed length keeps every earlier start.
proof fn lemma_push_starts(lens: Seq<u8>, x: u8)
    ensures forall|r: int| 0 <= r <= lens.len() ==> #[trigger] rstart(lens.push(x), r) == rstart(lens, r),
{
    assert forall|r: int| 0 <= r <= lens.len() implies #[trigger] rstart(lens.push(x), r) == rstart(lens, r) by {
        lemma_rstart_push(lens, x, r);
    }
}

/// Run `r` keeps its rows when the starts around it are unchanged.
proof fn lemma_same_transfer(kc: Seq<u32>, kb: Seq<i64>, bs: int, a: Seq<u8>, b: Seq<u8>, r: int)
    requires
        rs_same(kc, kb, bs, a, r),
        rstart(a, r) == rstart(b, r),
        rstart(a, r + 1) == rstart(b, r + 1),
    ensures rs_same(kc, kb, bs, b, r),
{
    reveal(rs_same);
}

/// The run `[s, j)` of one key, pushed as run `nr`.
proof fn lemma_same_new(kc: Seq<u32>, kb: Seq<i64>, bs: int, l2: Seq<u8>, nr: int, s: int, j: int)
    requires
        rstart(l2, nr) == s,
        rstart(l2, nr + 1) == j,
        forall|t: int| s <= t < j ==> #[trigger] fkey(kc, kb, bs, t) == fkey(kc, kb, bs, s),
    ensures rs_same(kc, kb, bs, l2, nr),
{
    reveal(rs_same);
}

/// Pushing the run `[s, j)` keeps the earlier runs' properties and adds the new run's.
proof fn lemma_push_same(kc: Seq<u32>, kb: Seq<i64>, bs: int, lens: Seq<u8>, s: int, j: int, x: u8)
    requires
        forall|r: int| 0 <= r < lens.len() ==> #[trigger] lens[r] >= 1 && rs_same(kc, kb, bs, lens, r),
        forall|r: int| 0 < r < lens.len() ==> #[trigger] rs_cut(kc, kb, bs, lens, r),
        rstart(lens, lens.len() as int) == s,
        s < j, x as int == j - s,
        forall|t: int| s <= t < j ==> #[trigger] fkey(kc, kb, bs, t) == fkey(kc, kb, bs, s),
        s > 0 ==> fkey(kc, kb, bs, s - 1) != fkey(kc, kb, bs, s),
        lens.len() > 0 <==> s > 0,
    ensures
        forall|r: int| 0 <= r < lens.push(x).len() ==> #[trigger] lens.push(x)[r] >= 1 && rs_same(kc, kb, bs, lens.push(x), r),
        forall|r: int| 0 < r < lens.push(x).len() ==> #[trigger] rs_cut(kc, kb, bs, lens.push(x), r),
        rstart(lens.push(x), lens.len() as int + 1) == j,
{
    let l2 = lens.push(x);
    let nr = lens.len() as int;
    lemma_push_starts(lens, x);
    assert(rstart(l2, nr) == s);
    assert(l2[nr] == x);
    assert(rstart(l2, nr + 1) == rstart(l2, nr) + l2[nr]);
    lemma_same_new(kc, kb, bs, l2, nr, s, j);
    assert forall|r: int| 0 <= r < l2.len() implies #[trigger] l2[r] >= 1 && rs_same(kc, kb, bs, l2, r) by {
        if r < nr {
            assert(l2[r] == lens[r]);
            lemma_same_transfer(kc, kb, bs, lens, l2, r);
        }
    }
    assert forall|r: int| 0 < r < l2.len() implies #[trigger] rs_cut(kc, kb, bs, l2, r) by {
        assert(rstart(l2, r) == rstart(lens, r));
        if r < nr {
            assert(rs_cut(kc, kb, bs, lens, r));
        }
    }
}

/// Pushing a run (and its start `s` when `push_start`) keeps the sampled starts.
proof fn lemma_push_sample(lens: Seq<u8>, starts: Seq<u64>, s2: Seq<u64>, stride: int, s: int, x: u8, push_start: bool)
    requires
        forall|b: int| 0 <= b < starts.len() ==> #[trigger] start_ok(lens, starts, stride, b),
        rstart(lens, lens.len() as int) == s,
        0 <= s <= u64::MAX,
        push_start ==> starts.len() * stride == lens.len() && s2 == starts.push(s as u64),
        !push_start ==> s2 == starts,
        stride >= 1,
    ensures
        forall|b: int| 0 <= b < s2.len() ==> #[trigger] start_ok(lens.push(x), s2, stride, b),
{
    let l2 = lens.push(x);
    let nr = lens.len() as int;
    lemma_push_starts(lens, x);
    assert forall|b: int| 0 <= b < s2.len() implies #[trigger] start_ok(l2, s2, stride, b) by {
        if b < starts.len() {
            assert(start_ok(lens, starts, stride, b));
            assert(s2[b] == starts[b]);
            assert(0 <= b * stride) by (nonlinear_arith) requires b >= 0, stride >= 1;
            assert(rstart(l2, b * stride) == rstart(lens, b * stride));
        } else {
            assert(push_start);
            assert(b == starts.len());
            assert(b * stride == nr);
            assert(s2[b] == s as u64);
            assert(rstart(l2, nr) == rstart(lens, nr));
        }
    }
}

/// Pushing the run `[s, j)` (all of key `fkey(s)`, cut at `s` when `s > 0`) keeps the runs built.
proof fn lemma_push_run(kc: Seq<u32>, kb: Seq<i64>, bs: int, lens: Seq<u8>, starts: Seq<u64>, stride: int,
    s: int, j: int, x: u8, push_start: bool)
    requires
        runs_built(kc, kb, bs, lens, starts, stride),
        rstart(lens, lens.len() as int) == s,
        0 <= s < j, s <= u64::MAX, x as int == j - s,
        forall|t: int| s <= t < j ==> #[trigger] fkey(kc, kb, bs, t) == fkey(kc, kb, bs, s),
        s > 0 ==> fkey(kc, kb, bs, s - 1) != fkey(kc, kb, bs, s),
        lens.len() > 0 <==> s > 0,
        push_start ==> starts.len() * stride == lens.len(),
        stride >= 1,
    ensures ({
        let l2 = lens.push(x);
        let s2 = if push_start { starts.push(s as u64) } else { starts };
        &&& runs_built(kc, kb, bs, l2, s2, stride)
        &&& rstart(l2, l2.len() as int) == j
    }),
{
    reveal(runs_built);
    let s2 = if push_start { starts.push(s as u64) } else { starts };
    lemma_push_same(kc, kb, bs, lens, s, j, x);
    lemma_push_sample(lens, starts, s2, stride, s, x, push_start);
}

/// The runs of the `n` rows of key column `kc`/`kb` (blocks of `bs` rows): `Some((lens, starts))` with every run
/// length at most 255, or `None` when some run is longer (or the counts would overflow).
pub fn build_runs(kc: &[u32], kb: &[i64], bs: usize, n: usize, stride: usize) -> (r: Option<(Vec<u8>, Vec<u64>)>)
    requires
        kc.len() == n,
        bs >= 1,
        kb.len() * bs >= n,
        1 <= stride <= 4096,
    ensures
        r matches Some(p) ==> runs_built(kc@, kb@, bs as int, p.0@, p.1@, stride as int)
            && rstart(p.0@, p.0@.len() as int) == n,
{
    let mut lens: Vec<u8> = Vec::new();
    let mut starts: Vec<u64> = Vec::new();
    if n == 0 {
        proof {
            reveal(runs_built);
        }
        return Some((lens, starts));
    }
    if n >= usize::MAX - 8192 {
        return None;
    }
    let ghost kcs = kc@;
    let ghost kbs = kb@;
    let ghost b = bs as int;
    proof {
        crate::stores::liruns::interface::common::read::lemma_div_lt(0, b, kb.len() as int);
    }
    let mut ck: i128 = kb[0 / bs] as i128 + kc[0] as i128;
    proof {
        reveal(fkey);
    }
    let mut s: usize = 0;
    let mut j: usize = 1;
    let mut next_at: usize = 0;
    proof {
        reveal(runs_built);
        assert(0 * (stride as int) == 0) by (nonlinear_arith);
        assert(runs_built(kcs, kbs, b, lens@, starts@, stride as int));
    }
    while j < n
        invariant
            kc@ == kcs, kb@ == kbs, b == bs as int,
            kc.len() == n, bs >= 1, kb.len() * bs >= n, 1 <= stride <= 4096, n < usize::MAX - 8192,
            0 <= s < j <= n,
            ck as int == fkey(kcs, kbs, b, s as int),
            forall|t: int| s <= t < j ==> #[trigger] fkey(kcs, kbs, b, t) == fkey(kcs, kbs, b, s as int),
            s > 0 ==> fkey(kcs, kbs, b, s - 1) != fkey(kcs, kbs, b, s as int),
            lens.len() > 0 <==> s > 0,
            lens.len() <= s,
            rstart(lens@, lens.len() as int) == s,
            runs_built(kcs, kbs, b, lens@, starts@, stride as int),
            next_at as int == starts.len() * stride,
            lens.len() <= next_at <= lens.len() + stride,
        decreases n - j,
    {
        proof {
            crate::stores::liruns::interface::common::read::lemma_div_lt(j as int, b, kb.len() as int);
        }
        let k: i128 = kb[j / bs] as i128 + kc[j] as i128;
        proof {
            reveal(fkey);
        }
        if k != ck {
            let len = j - s;
            if len > 255 {
                return None;
            }
            let push_start = next_at == lens.len();
            let ghost l0 = lens@;
            let ghost st0 = starts@;
            proof {
                lemma_push_run(kcs, kbs, b, l0, st0, stride as int, s as int, j as int, len as u8, push_start);
            }
            if push_start {
                starts.push(s as u64);
                proof {
                    assert((st0.len() + 1) * stride == st0.len() * stride + stride) by (nonlinear_arith);
                }
                next_at = next_at + stride;
            }
            lens.push(len as u8);
            s = j;
            ck = k;
        }
        j = j + 1;
    }
    let len = n - s;
    if len > 255 {
        return None;
    }
    let push_start = next_at == lens.len();
    proof {
        lemma_push_run(kcs, kbs, b, lens@, starts@, stride as int, s as int, n as int, len as u8, push_start);
    }
    if push_start {
        starts.push(s as u64);
    }
    lens.push(len as u8);
    Some((lens, starts))
}

} // verus!
