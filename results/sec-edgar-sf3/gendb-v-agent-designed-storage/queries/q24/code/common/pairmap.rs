//! Code map between two coded pair lists: source pair `q` (codes `(sf[q], ss[q])`) to the target pair whose codes are
//! the images of `q`'s codes under two component maps (`m1`, `m2`: code + 1, 0 = no image), + 1; 0 when either
//! component has no image or the target has no such pair. The target pairs strictly increase lexicographically
//! (`pairs_increasing`), so each lookup is a short linear step or a galloping search from the previous position;
//! parallel over chunks of `1 << shift` source pairs, each task filling one chunk (`common::chunks`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::stores::num_tvg::interface::common::runs::{pairs_increasing, pair_lt};
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::work::put;
use super::dictmap::{task_count, cut, cut_exec, lemma_cut_mono};
use super::flat::{concat, lemma_flatten_cuts};
use super::chunks::{chunks_shape, chunk_at, chunk_len, lemma_chunk_index, lemma_shift_mask};
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use vstd::arithmetic::power2::pow2;

verus! {

/// A coded pair list held as stored slices.
#[derive(Clone, Copy)]
pub struct Pairs {
    pub first: &'static [u64],
    pub second: &'static [u64],
    pub count: usize,
}

impl Pairs {
    pub open spec fn wf(&self) -> bool {
        &&& self.first@.len() == self.count
        &&& self.second@.len() == self.count
    }
}

/// `v` is the image of source pair `q`.
pub open spec fn pair_entry_ok(src: Pairs, dst: Pairs, m1: Seq<u64>, m2: Seq<u64>, q: int, v: u64) -> bool {
    let a = m1[src.first@[q] as int];
    let b = m2[src.second@[q] as int];
    &&& v != 0 ==> v - 1 < dst.count && a != 0 && b != 0
        && dst.first@[v - 1] + 1 == a && dst.second@[v - 1] + 1 == b
    &&& v == 0 ==> forall|p: int| 0 <= p < dst.count ==> !(a != 0 && b != 0 && #[trigger] dst.first@[p] + 1 == a
        && dst.second@[p] + 1 == b)
}

/// The inputs of a pair map: every source code has a component image entry.
pub open spec fn inputs_ok(src: Pairs, dst: Pairs, m1: Seq<u64>, m2: Seq<u64>) -> bool {
    &&& src.wf() && dst.wf()
    &&& pairs_increasing(dst.first@, dst.second@)
    &&& forall|q: int| 0 <= q < src.count ==> (#[trigger] src.first@[q]) < m1.len() && src.second@[q] < m2.len()
}

/// Search of the pair `(a, b)` in the strictly increasing target pairs, starting from a position hint (the previous
/// answer: consecutive source pairs usually map to nearby targets): probes `lo + 1, lo + 2, lo + 4, ..` from the
/// hint, then bisects. Returns the first position not below `(a, b)` (`r.1`) and whether it holds `(a, b)`.
/// `no_unwind`.
fn find_pair(dst: Pairs, a: u64, b: u64, hint: usize) -> (r: (bool, usize))
    requires dst.wf(), pairs_increasing(dst.first@, dst.second@), hint <= dst.count,
    ensures
        r.1 <= dst.count,
        r.0 ==> r.1 < dst.count && dst.first@[r.1 as int] == a && dst.second@[r.1 as int] == b,
        !r.0 ==> forall|p: int| 0 <= p < dst.count ==> !(#[trigger] dst.first@[p] == a && dst.second@[p] == b),
    no_unwind
{
    // initial bracket from the hint: positions below `lo` are below (a, b), positions from `hi` on are not
    let mut lo: usize = 0;
    let mut hi: usize = dst.count;
    if hint > 0 {
        let f = dst.first[hint - 1];
        let s = dst.second[hint - 1];
        if f < a || (f == a && s < b) {
            proof {
                assert forall|p: int| 0 <= p < hint implies pair_lt(#[trigger] dst.first@[p], dst.second@[p], a, b) by {
                    if p < hint - 1 {
                        assert(pair_lt(dst.first@[p], dst.second@[p], dst.first@[hint - 1], dst.second@[hint - 1]));
                    }
                }
            }
            lo = hint;
        } else {
            proof {
                assert forall|p: int| hint - 1 <= p < dst.count implies !pair_lt(#[trigger] dst.first@[p], dst.second@[p], a, b) by {
                    if p > hint - 1 {
                        assert(pair_lt(dst.first@[hint - 1], dst.second@[hint - 1], dst.first@[p], dst.second@[p]));
                    }
                }
            }
            hi = hint - 1;
        }
    }
    // a few linear steps first: consecutive source pairs usually map to the same or the next target positions
    let mut lin: usize = 0;
    while lo < hi && lin < 8
        invariant
            dst.wf(), pairs_increasing(dst.first@, dst.second@),
            lo <= hi <= dst.count,
            forall|p: int| 0 <= p < lo ==> pair_lt(#[trigger] dst.first@[p], dst.second@[p], a, b),
            forall|p: int| hi <= p < dst.count ==> !pair_lt(#[trigger] dst.first@[p], dst.second@[p], a, b),
        decreases hi - lo,
    {
        let f = dst.first[lo];
        let s = dst.second[lo];
        if f < a || (f == a && s < b) {
            lo = lo + 1;
            lin = lin + 1;
        } else {
            proof {
                assert forall|p: int| lo <= p < dst.count implies !pair_lt(#[trigger] dst.first@[p], dst.second@[p], a, b) by {
                    if p > lo {
                        assert(pair_lt(dst.first@[lo as int], dst.second@[lo as int], dst.first@[p], dst.second@[p]));
                    }
                }
            }
            hi = lo;
        }
    }
    let mut step: usize = 1;
    while lo < hi
        invariant
            dst.wf(), pairs_increasing(dst.first@, dst.second@),
            lo <= hi <= dst.count, step >= 1,
            forall|p: int| 0 <= p < lo ==> pair_lt(#[trigger] dst.first@[p], dst.second@[p], a, b),
            forall|p: int| hi <= p < dst.count ==> !pair_lt(#[trigger] dst.first@[p], dst.second@[p], a, b),
        decreases hi - lo,
    {
        let mid = if step < hi - lo { lo + step } else { lo + (hi - lo) / 2 };
        let f = dst.first[mid];
        let s = dst.second[mid];
        if f < a || (f == a && s < b) {
            proof {
                assert forall|p: int| 0 <= p < mid + 1 implies pair_lt(#[trigger] dst.first@[p], dst.second@[p], a, b) by {
                    if p < mid {
                        assert(pair_lt(dst.first@[p], dst.second@[p], dst.first@[mid as int], dst.second@[mid as int]));
                    }
                }
            }
            lo = mid + 1;
            if step < 0x4000_0000 {
                step = step * 2;
            }
        } else {
            proof {
                assert forall|p: int| mid <= p < dst.count implies !pair_lt(#[trigger] dst.first@[p], dst.second@[p], a, b) by {
                    if p > mid {
                        assert(pair_lt(dst.first@[mid as int], dst.second@[mid as int], dst.first@[p], dst.second@[p]));
                    }
                }
            }
            hi = mid;
        }
    }
    if lo < dst.count && dst.first[lo] == a && dst.second[lo] == b {
        (true, lo)
    } else {
        proof {
            assert forall|p: int| 0 <= p < dst.count implies !(#[trigger] dst.first@[p] == a && dst.second@[p] == b) by {
                if p > lo {
                    assert(pair_lt(dst.first@[lo as int], dst.second@[lo as int], dst.first@[p], dst.second@[p]));
                }
            }
        }
        (false, lo)
    }
}

/// The image of source pair `q` (target pair + 1, or 0) and the next search hint: first the hint position itself
/// (consecutive source pairs usually map to consecutive target pairs), else `find_pair` from the hint. `no_unwind`.
#[inline(always)]
fn pair_image(src: Pairs, dst: Pairs, m1: &Vec<u64>, m2: &Vec<u64>, m1n: usize, m2n: usize, q: usize, hint: usize)
    -> (r: (u64, usize))
    requires
        inputs_ok(src, dst, m1@, m2@), m1n == m1@.len(), m2n == m2@.len(), q < src.count, hint <= dst.count,
    ensures
        pair_entry_ok(src, dst, m1@, m2@, q as int, r.0), r.0 <= dst.count, r.1 <= dst.count,
    no_unwind
{
    proof {
        assert(src.first@[q as int] < m1@.len() && src.second@[q as int] < m2@.len());
    }
    let fa = src.first[q];
    let fb = src.second[q];
    assert(fa < m1n && fb < m2n);
    let a = m1[fa as usize];
    let b = m2[fb as usize];
    let mut v: u64 = 0;
    let mut h2 = hint;
    if a != 0 && b != 0 {
        if hint < dst.count && dst.first[hint] == a - 1 && dst.second[hint] == b - 1 {
            v = (hint as u64) + 1;
            h2 = hint + 1;
        } else {
            let (found, p) = find_pair(dst, a - 1, b - 1, hint);
            if found {
                v = (p as u64) + 1;
                h2 = p + 1;
            } else {
                h2 = p;
            }
        }
    }
    proof {
        assert(a == m1@[src.first@[q as int] as int] && b == m2@[src.second@[q as int] as int]);
        if v == 0 && a != 0 && b != 0 {
            assert forall|p: int| 0 <= p < dst.count implies !(a != 0 && b != 0 && #[trigger] dst.first@[p] + 1 == a
                && dst.second@[p] + 1 == b) by {
                assert(!(dst.first@[p] == a - 1 && dst.second@[p] == b - 1));
            }
        }
        assert(pair_entry_ok(src, dst, m1@, m2@, q as int, v));
    }
    (v, h2)
}

/// Map source pairs `[lo, hi)`.
pub struct PairMapTask {
    pub src: Pairs,
    pub dst: Pairs,
    pub m1: Arc<Vec<u64>>,
    pub m2: Arc<Vec<u64>>,
    pub lo: usize,
    pub hi: usize,
    pub out: Vec<u64>,
}

impl WorkerTask for PairMapTask {
    type Output = Vec<u64>;

    open spec fn pre(&self) -> bool {
        &&& inputs_ok(self.src, self.dst, self.m1@, self.m2@)
        &&& self.lo <= self.hi <= self.src.count
        &&& self.out@.len() == self.hi - self.lo
    }

    open spec fn post(&self, out: Vec<u64>) -> bool {
        &&& out@.len() == self.hi - self.lo
        &&& forall|q: int| self.lo <= q < self.hi
            ==> pair_entry_ok(self.src, self.dst, self.m1@, self.m2@, q, #[trigger] out@[q - self.lo])
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: Vec<u64>) {
        let src = self.src;
        let dst = self.dst;
        let m1 = self.m1;
        let m2 = self.m2;
        let lo = self.lo;
        let hi = self.hi;
        let mut out = self.out;
        let m1n = m1.len();
        let m2n = m2.len();
        let mut hint: usize = 0;
        let mut q = lo;
        while q < hi
            invariant
                hint <= dst.count,
                m1n == m1@.len(), m2n == m2@.len(),
                inputs_ok(src, dst, m1@, m2@),
                lo <= q <= hi <= src.count,
                out@.len() == hi - lo,
                forall|q2: int| lo <= q2 < q ==> pair_entry_ok(src, dst, m1@, m2@, q2, #[trigger] out@[q2 - lo]),
            decreases hi - q,
        {
            let (v, h2) = pair_image(src, dst, &*m1, &*m2, m1n, m2n, q, hint);
            hint = h2;
            let ghost before = out@;
            put(&mut out, q - lo, v);
            proof {
                assert forall|q2: int| lo <= q2 < q + 1 implies pair_entry_ok(src, dst, m1@, m2@, q2, #[trigger] out@[q2 - lo]) by {
                    if q2 < q {
                        assert(out@[q2 - lo] == before[q2 - lo]);
                    }
                }
            }
            q = q + 1;
        }
        out
    }
}

/// The image of every source pair (+ 1; 0: none), with at most `workers` threads, as chunks of `size = 1 << shift`
/// values (one chunk per task; no concatenation).
pub fn pair_map(src: Pairs, dst: Pairs, m1: Arc<Vec<u64>>, m2: Arc<Vec<u64>>, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<(Vec<Vec<u64>>, u64, u64), QueryError>)
    requires inputs_ok(src, dst, m1@, m2@), 1 <= workers <= MAX_WORKERS, src.count <= 0x1000_0000_0000_0000,
    ensures
        r matches Ok((cs, shift, size)) ==> shift < 64 && size == 1u64 << shift
            && chunks_shape(cs@, size as int, src.count as int)
            && forall|q: int| 0 <= q < src.count ==> pair_entry_ok(src, dst, m1@, m2@, q, #[trigger] chunk_at(cs@, size as int, q)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let n = src.count;
    let k = task_count(n, 49152, workers);
    // the smallest chunk size 1 << shift (at least 4096) with fewer than k full chunks: at most k chunks
    let mut shift: u64 = 12;
    while shift < 62 && ((n as u64) >> shift) >= (k as u64)
        invariant 12 <= shift <= 62,
        decreases 62 - shift,
    {
        shift = shift + 1;
    }
    proof {
        if shift == 62 {
            vstd::bits::lemma_u64_shr_is_div(n as u64, 62);
            vstd::bits::lemma_u64_pow2_no_overflow(62);
            assert(pow2(62) == 0x4000_0000_0000_0000) by {
                vstd::arithmetic::power2::lemma2_to64_rest();
            }
            assert((n as u64) >> 62 == 0);
        }
    }
    let size: u64 = 1u64 << shift;
    proof {
        lemma_shift_mask(n as u64, shift, size);
        lemma_fundamental_div_mod(n as int, size as int);
    }
    let full = ((n as u64) >> shift) as usize;
    let nc: usize = if (n as u64) & (size - 1) != 0 { full + 1 } else { full };
    proof {
        let sz = size as int;
        let rem = (n as int) % sz;
        assert(nc <= k);
        assert(n <= nc * size) by (nonlinear_arith)
            requires n == sz * full + rem, 0 <= rem < sz, sz == size, nc == (if rem != 0 { full + 1 } else { full as int });
        assert(nc * size < n + size) by (nonlinear_arith)
            requires n == sz * full + rem, 0 <= rem < sz, sz == size, nc == (if rem != 0 { full + 1 } else { full as int });
    }
    let mut tasks: Vec<PairMapTask> = Vec::new();
    let mut c: usize = 0;
    while c < nc
        invariant
            inputs_ok(src, dst, m1@, m2@), n == src.count, nc <= k <= workers <= MAX_WORKERS, c <= nc,
            size >= 1, n <= nc * size, nc * size < n + size, n <= 0x1000_0000_0000_0000,
            tasks@.len() == c,
            forall|u: int| 0 <= u < c ==> (#[trigger] tasks@[u]).pre() && tasks@[u].src == src && tasks@[u].dst == dst
                && tasks@[u].m1@ == m1@ && tasks@[u].m2@ == m2@
                && tasks@[u].lo == u * size && tasks@[u].hi == u * size + chunk_len(size as int, n as int, u),
        decreases nc - c,
    {
        assert(c * size < n) by (nonlinear_arith) requires c < nc, size >= 1, nc * size < n + size;
        let lo = ((c as u64) * size) as usize;
        assert(lo == c * size);
        let left = (n - lo) as u64;
        let hi = if left < size {
            n
        } else {
            assert(size <= n - lo);
            lo + size as usize
        };
        assert(hi == c * size + chunk_len(size as int, n as int, c as int));
        let task = PairMapTask { src, dst, m1: m1.clone(), m2: m2.clone(), lo, hi, out: vec![0u64; hi - lo] };
        assert(task.pre());
        let ghost t0 = tasks@;
        tasks.push(task);
        proof {
            assert forall|u: int| 0 <= u < c + 1 implies (#[trigger] tasks@[u]).pre() && tasks@[u].src == src && tasks@[u].dst == dst
                && tasks@[u].m1@ == m1@ && tasks@[u].m2@ == m2@
                && tasks@[u].lo == u * size && tasks@[u].hi == u * size + chunk_len(size as int, n as int, u) by {
                if u < c {
                    assert(tasks@[u] == t0[u]);
                }
            }
        }
        c = c + 1;
    }
    let ghost tv = tasks@;
    let outs = match super::tasks::run_tasks(dispatch, tasks, workers == 1) {
        Ok(outs) => outs,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        assert forall|u: int| 0 <= u < outs@.len() implies (#[trigger] outs@[u])@.len() == chunk_len(size as int, n as int, u) by {
            assert(tv[u].post(outs@[u]));
        }
        assert forall|q: int| 0 <= q < src.count implies pair_entry_ok(src, dst, m1@, m2@, q, #[trigger] chunk_at(outs@, size as int, q)) by {
            let u = q / size as int;
            let r = q % size as int;
            lemma_chunk_index(outs@, size as int, n as int, q);
            lemma_fundamental_div_mod(q, size as int);
            assert(tv[u].post(outs@[u]));
            assert(q == u * size + r) by (nonlinear_arith) requires q == size * u + r;
            assert(r < chunk_len(size as int, n as int, u));
            assert(tv[u].lo <= q < tv[u].hi);
            assert(q - tv[u].lo == r);
        }
    }
    Ok((outs, shift, size))
}

/// Map source pairs `[lo, hi)` into `u32` images (the target has fewer than `u32::MAX` pairs).
pub struct PairMapTask32 {
    pub src: Pairs,
    pub dst: Pairs,
    pub m1: Arc<Vec<u64>>,
    pub m2: Arc<Vec<u64>>,
    pub lo: usize,
    pub hi: usize,
    pub out: Vec<u32>,
}

impl WorkerTask for PairMapTask32 {
    type Output = Vec<u32>;

    open spec fn pre(&self) -> bool {
        &&& inputs_ok(self.src, self.dst, self.m1@, self.m2@)
        &&& self.dst.count < u32::MAX
        &&& self.lo <= self.hi <= self.src.count
        &&& self.out@.len() == self.hi - self.lo
    }

    open spec fn post(&self, out: Vec<u32>) -> bool {
        &&& out@.len() == self.hi - self.lo
        &&& forall|q: int| self.lo <= q < self.hi
            ==> pair_entry_ok(self.src, self.dst, self.m1@, self.m2@, q, (#[trigger] out@[q - self.lo]) as u64)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: Vec<u32>) {
        let src = self.src;
        let dst = self.dst;
        let m1 = self.m1;
        let m2 = self.m2;
        let lo = self.lo;
        let hi = self.hi;
        let mut out = self.out;
        let m1n = m1.len();
        let m2n = m2.len();
        let mut hint: usize = 0;
        let mut q = lo;
        while q < hi
            invariant
                hint <= dst.count, dst.count < u32::MAX,
                m1n == m1@.len(), m2n == m2@.len(),
                inputs_ok(src, dst, m1@, m2@),
                lo <= q <= hi <= src.count,
                out@.len() == hi - lo,
                forall|q2: int| lo <= q2 < q ==> pair_entry_ok(src, dst, m1@, m2@, q2, (#[trigger] out@[q2 - lo]) as u64),
            decreases hi - q,
        {
            let (v, h2) = pair_image(src, dst, &*m1, &*m2, m1n, m2n, q, hint);
            hint = h2;
            let ghost before = out@;
            put(&mut out, q - lo, v as u32);
            proof {
                assert((v as u32) as u64 == v);
                assert forall|q2: int| lo <= q2 < q + 1 implies
                    pair_entry_ok(src, dst, m1@, m2@, q2, (#[trigger] out@[q2 - lo]) as u64) by {
                    if q2 < q {
                        assert(out@[q2 - lo] == before[q2 - lo]);
                    }
                }
            }
            q = q + 1;
        }
        out
    }
}

/// The image of every source pair (+ 1; 0: none) as one `u32` vector, with at most `workers` threads (tasks over
/// equal cuts of the source pairs, outputs concatenated; one task on the calling thread when `workers == 1`).
pub fn pair_map32(src: Pairs, dst: Pairs, m1: Arc<Vec<u64>>, m2: Arc<Vec<u64>>, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<Vec<u32>, QueryError>)
    requires inputs_ok(src, dst, m1@, m2@), dst.count < u32::MAX, 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(m) ==> m@.len() == src.count
            && forall|q: int| 0 <= q < src.count ==> pair_entry_ok(src, dst, m1@, m2@, q, (#[trigger] m@[q]) as u64),
        r matches Err(e) ==> e is WorkerFailed,
{
    let n = src.count;
    let k = task_count(n, 49152, workers);
    let mut tasks: Vec<PairMapTask32> = Vec::new();
    let mut t: usize = 0;
    while t < k
        invariant
            inputs_ok(src, dst, m1@, m2@), dst.count < u32::MAX, n == src.count, 1 <= k <= workers <= MAX_WORKERS, t <= k,
            tasks@.len() == t,
            forall|u: int| 0 <= u < t ==> (#[trigger] tasks@[u]).pre() && tasks@[u].src == src && tasks@[u].dst == dst
                && tasks@[u].m1@ == m1@ && tasks@[u].m2@ == m2@
                && tasks@[u].lo == cut(n as int, k as int, u) && tasks@[u].hi == cut(n as int, k as int, u + 1),
        decreases k - t,
    {
        let lo = cut_exec(n, k, t);
        let hi = cut_exec(n, k, t + 1);
        proof {
            lemma_cut_mono(n as int, k as int, t as int);
        }
        tasks.push(PairMapTask32 { src, dst, m1: m1.clone(), m2: m2.clone(), lo, hi, out: vec![0u32; hi - lo] });
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = match super::tasks::run_tasks(dispatch, tasks, workers == 1) {
        Ok(outs) => outs,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let ghost ok = |q: int, v: u32| pair_entry_ok(src, dst, m1@, m2@, q, v as u64);
    proof {
        assert forall|u: int| 0 <= u < outs@.len() implies
            (#[trigger] outs@[u])@.len() == cut(n as int, k as int, u + 1) - cut(n as int, k as int, u) by {
            assert(tv[u].post(outs@[u]));
        }
        assert forall|u: int, c: int| 0 <= u < outs@.len() && cut(n as int, k as int, u) <= c < cut(n as int, k as int, u + 1)
            implies ok(c, #[trigger] outs@[u]@[c - cut(n as int, k as int, u)]) by {
            assert(tv[u].post(outs@[u]));
        }
        lemma_flatten_cuts(outs@, n as int, k as int, ok);
        lemma_cut_mono(n as int, k as int, k - 1);
    }
    let m = concat(outs);
    proof {
        assert forall|q: int| 0 <= q < src.count implies pair_entry_ok(src, dst, m1@, m2@, q, (#[trigger] m@[q]) as u64) by {
            assert(ok(q, m@[q]));
        }
    }
    Ok(m)
}

} // verus!
