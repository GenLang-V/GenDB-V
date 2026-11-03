//! Code map between two sorted text dictionaries: every source code to the target code of the same value (+ 1), or
//! 0 when the target has no such value. Computed as a merge of the two sorted value lists, in parallel over source
//! code ranges (each range finds its start in the target by binary search); value comparisons first try one slice
//! equality (`compare_fast`: merges of similar dictionaries compare mostly equal values). Several maps can share one
//! `fork_join` (`dict_map3`). Also a lower-bound search of a key.
//!
//! Dictionaries are text lists (`U64` offsets + `U8` bytes, `text_parts_wf`) whose values strictly increase in byte
//! order (`text_strictly_sorted`), as stored by the admitted storages.
use vstd::prelude::*;
use crate::spec::text::lex_cmp;
use crate::stores::num_tvg::interface::common::text::{text_entry, text_parts_wf, text_strictly_sorted, text_entry_of,
    compare_bytes, lemma_lex_cmp_lt_trans};
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::bridge::order::{lemma_lex_cmp_antisym, lemma_lex_cmp_trans};
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::work::put;

verus! {

/// A sorted dictionary held as stored slices.
#[derive(Clone, Copy)]
pub struct Dict {
    pub off: &'static [u64],
    pub bytes: &'static [u8],
    pub count: usize,
}

impl Dict {
    pub open spec fn wf(&self) -> bool {
        &&& text_parts_wf(self.off@, self.bytes@, self.count as int)
        &&& text_strictly_sorted(self.off@, self.bytes@, self.count as int)
        &&& self.count < usize::MAX
    }

    /// Value `k`.
    pub open spec fn at(&self, k: int) -> Seq<u8> {
        text_entry(self.off@, self.bytes@, k)
    }
}

/// `v` is the map value of source code `c`: target code + 1 of the equal value, or 0 when there is none.
pub open spec fn map_entry_ok(src: Dict, dst: Dict, c: int, v: u64) -> bool {
    &&& v != 0 ==> v - 1 < dst.count && dst.at(v - 1) == src.at(c)
    &&& v == 0 ==> forall|d: int| 0 <= d < dst.count ==> dst.at(d) != src.at(c)
}

/// `m` maps every source code.
pub open spec fn map_ok(src: Dict, dst: Dict, m: Seq<u64>) -> bool {
    &&& m.len() == src.count
    &&& forall|c: int| 0 <= c < src.count ==> map_entry_ok(src, dst, c, #[trigger] m[c])
}

/// In a sorted dictionary, values before a value below `key` are below `key`.
proof fn lemma_below(d: Dict, key: Seq<u8>, mid: int, k: int)
    requires d.wf(), 0 <= k <= mid < d.count, lex_cmp(d.at(mid), key) < 0,
    ensures lex_cmp(d.at(k), key) < 0,
{
    if k < mid {
        lemma_lex_cmp_lt_trans(d.at(k), d.at(mid), key);
    }
}

/// In a sorted dictionary, values after a value not below `key` are not below `key`.
proof fn lemma_above(d: Dict, key: Seq<u8>, mid: int, k: int)
    requires d.wf(), 0 <= mid <= k < d.count, lex_cmp(d.at(mid), key) >= 0,
    ensures lex_cmp(d.at(k), key) >= 0,
{
    if k > mid {
        lemma_lex_cmp_antisym(d.at(mid), key);
        lemma_lex_cmp_antisym(d.at(k), key);
        lemma_lex_cmp_trans(key, d.at(mid), d.at(k));
    }
}

/// No value equals `key` when the values before `p` are below it and value `p` (if any) is above it.
proof fn lemma_absent(d: Dict, key: Seq<u8>, p: int)
    requires
        d.wf(), 0 <= p <= d.count,
        forall|k: int| 0 <= k < p ==> lex_cmp(#[trigger] d.at(k), key) < 0,
        p < d.count ==> lex_cmp(d.at(p), key) > 0,
    ensures forall|k: int| 0 <= k < d.count ==> d.at(k) != key,
{
    assert forall|k: int| 0 <= k < d.count implies d.at(k) != key by {
        lemma_lex_cmp_zero(d.at(k), key);
        if k > p {
            lemma_lex_cmp_antisym(d.at(p), key);
            lemma_lex_cmp_lt_trans(key, d.at(p), d.at(k));
            lemma_lex_cmp_antisym(d.at(k), key);
        }
    }
}

/// Byte order of two slices (`lex_cmp`), lengths passed in: equal slices are recognized by one slice comparison
/// (a `memcmp`), others compared byte by byte (`compare_bytes`). Not `no_unwind` (slice equality has no such
/// specification): for the calling thread only.
pub fn compare_fast(x: &[u8], xn: usize, y: &[u8], yn: usize) -> (r: i8)
    requires xn == x@.len(), yn == y@.len(),
    ensures r as int == lex_cmp(x@, y@),
{
    if xn == yn && x == y {
        proof {
            assert(x@ =~= y@);
            lemma_lex_cmp_zero(x@, y@);
        }
        0
    } else {
        compare_bytes(x, xn, y, yn)
    }
}

/// First position whose value is not below `key` (`no_unwind`).
pub fn lower_bound(d: Dict, key: &[u8], key_len: usize) -> (r: usize)
    requires d.wf(), key_len == key@.len(),
    ensures
        r <= d.count,
        forall|k: int| 0 <= k < r ==> lex_cmp(#[trigger] d.at(k), key@) < 0,
        r < d.count ==> lex_cmp(d.at(r as int), key@) >= 0,
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = d.count;
    while lo < hi
        invariant
            d.wf(), key_len == key@.len(),
            lo <= hi <= d.count,
            forall|k: int| 0 <= k < lo ==> lex_cmp(#[trigger] d.at(k), key@) < 0,
            forall|k: int| hi <= k < d.count ==> lex_cmp(#[trigger] d.at(k), key@) >= 0,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let (e, en) = text_entry_of(d.off, d.bytes, d.count, mid);
        if compare_bytes(e, en, key, key_len) < 0 {
            proof {
                assert forall|k: int| 0 <= k < mid + 1 implies lex_cmp(#[trigger] d.at(k), key@) < 0 by {
                    lemma_below(d, key@, mid as int, k);
                }
            }
            lo = mid + 1;
        } else {
            proof {
                assert forall|k: int| mid <= k < d.count implies lex_cmp(#[trigger] d.at(k), key@) >= 0 by {
                    lemma_above(d, key@, mid as int, k);
                }
            }
            hi = mid;
        }
    }
    lo
}

/// The map of every source code, by one merge on the calling thread (equal values found by `compare_fast`).
pub fn merge_map(src: Dict, dst: Dict) -> (m: Vec<u64>)
    requires src.wf(), dst.wf(),
    ensures map_ok(src, dst, m@),
{
    let lo: usize = 0;
    let hi = src.count;
    let mut out = vec![0u64; hi];
    if lo >= hi {
        return out;
    }
    let (e0, en0) = text_entry_of(src.off, src.bytes, src.count, lo);
    let mut d = lower_bound(dst, e0, en0);
    let mut c = lo;
    while c < hi
        invariant
            src.wf(), dst.wf(),
            lo <= c <= hi <= src.count,
            out@.len() == hi - lo,
            d <= dst.count,
            c < hi ==> forall|k: int| 0 <= k < d ==> lex_cmp(#[trigger] dst.at(k), src.at(c as int)) < 0,
            forall|c2: int| lo <= c2 < c ==> map_entry_ok(src, dst, c2, #[trigger] out@[c2 - lo]),
        decreases hi - c,
    {
        let (e, en) = text_entry_of(src.off, src.bytes, src.count, c);
        let mut v: u64 = 0;
        let mut searching = true;
        let mut last: i8 = 1;
        while searching && d < dst.count
            invariant
                src.wf(), dst.wf(),
                lo <= c < hi <= src.count,
                e@ == src.at(c as int), en == e@.len(),
                d <= dst.count,
                forall|k: int| 0 <= k < d ==> lex_cmp(#[trigger] dst.at(k), e@) < 0,
                !searching ==> d < dst.count && last as int == lex_cmp(dst.at(d as int), e@) && last >= 0,
                !searching ==> v as int == if last == 0 { d as int + 1 } else { 0int },
                searching ==> v == 0,
            decreases dst.count - d, if searching { 1int } else { 0int },
        {
            let (f, fln) = text_entry_of(dst.off, dst.bytes, dst.count, d);
            let cmp = compare_fast(f, fln, e, en);
            if cmp < 0 {
                d = d + 1;
            } else {
                last = cmp;
                if cmp == 0 {
                    v = (d as u64) + 1;
                }
                searching = false;
            }
        }
        proof {
            lemma_lex_cmp_zero(dst.at(d as int), e@);
            if v == 0 {
                lemma_absent(dst, e@, d as int);
            }
        }
        put(&mut out, c - lo, v);
        // a matched target value equals this source value, so it is below the next one: the merge moves past it
        let ghost d0 = d;
        if v != 0 {
            d = d + 1;
        }
        proof {
            if c + 1 < hi {
                let next = src.at(c + 1);
                assert(lex_cmp(src.at(c as int), next) < 0);
                assert forall|k: int| 0 <= k < d implies lex_cmp(#[trigger] dst.at(k), next) < 0 by {
                    if k < d0 {
                        lemma_lex_cmp_lt_trans(dst.at(k), src.at(c as int), next);
                    } else {
                        assert(dst.at(k) == src.at(c as int));
                    }
                }
            }
        }
        c = c + 1;
    }
    proof {
        assert forall|c2: int| 0 <= c2 < src.count implies map_entry_ok(src, dst, c2, #[trigger] out@[c2]) by {
            assert(c2 - lo == c2);
        }
    }
    out
}

/// Map source codes `[lo, hi)` (a merge with the target from the target's lower bound of the first value).
pub struct DictMapTask {
    pub src: Dict,
    pub dst: Dict,
    pub lo: usize,
    pub hi: usize,
    pub out: Vec<u64>,
}

impl WorkerTask for DictMapTask {
    type Output = Vec<u64>;

    open spec fn pre(&self) -> bool {
        &&& self.src.wf() && self.dst.wf()
        &&& self.lo <= self.hi <= self.src.count
        &&& self.out@.len() == self.hi - self.lo
    }

    open spec fn post(&self, out: Vec<u64>) -> bool {
        &&& out@.len() == self.hi - self.lo
        &&& forall|c: int| self.lo <= c < self.hi ==> map_entry_ok(self.src, self.dst, c, #[trigger] out@[c - self.lo])
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: Vec<u64>) {
        let src = self.src;
        let dst = self.dst;
        let lo = self.lo;
        let hi = self.hi;
        let mut out = self.out;
        if lo >= hi {
            return out;
        }
        let (e0, en0) = text_entry_of(src.off, src.bytes, src.count, lo);
        let mut d = lower_bound(dst, e0, en0);
        let mut c = lo;
        while c < hi
            invariant
                src.wf(), dst.wf(),
                lo <= c <= hi <= src.count,
                out@.len() == hi - lo,
                d <= dst.count,
                c < hi ==> forall|k: int| 0 <= k < d ==> lex_cmp(#[trigger] dst.at(k), src.at(c as int)) < 0,
                forall|c2: int| lo <= c2 < c ==> map_entry_ok(src, dst, c2, #[trigger] out@[c2 - lo]),
            decreases hi - c,
        {
            let (e, en) = text_entry_of(src.off, src.bytes, src.count, c);
            let mut v: u64 = 0;
            let mut searching = true;
            let mut last: i8 = 1;
            while searching && d < dst.count
                invariant
                    src.wf(), dst.wf(),
                    lo <= c < hi <= src.count,
                    e@ == src.at(c as int), en == e@.len(),
                    d <= dst.count,
                    forall|k: int| 0 <= k < d ==> lex_cmp(#[trigger] dst.at(k), e@) < 0,
                    !searching ==> d < dst.count && last as int == lex_cmp(dst.at(d as int), e@) && last >= 0,
                    !searching ==> v as int == if last == 0 { d as int + 1 } else { 0int },
                    searching ==> v == 0,
                decreases dst.count - d, if searching { 1int } else { 0int },
            {
                let (f, fln) = text_entry_of(dst.off, dst.bytes, dst.count, d);
                let cmp = compare_bytes(f, fln, e, en);
                if cmp < 0 {
                    d = d + 1;
                } else {
                    last = cmp;
                    if cmp == 0 {
                        v = (d as u64) + 1;
                    }
                    searching = false;
                }
            }
            proof {
                lemma_lex_cmp_zero(dst.at(d as int), e@);
                if v == 0 {
                    lemma_absent(dst, e@, d as int);
                }
            }
            put(&mut out, c - lo, v);
            // as in `merge_map`: move past a matched target value
            let ghost d0 = d;
            if v != 0 {
                d = d + 1;
            }
            proof {
                if c + 1 < hi {
                    let next = src.at(c + 1);
                    assert(lex_cmp(src.at(c as int), next) < 0);
                    assert forall|k: int| 0 <= k < d implies lex_cmp(#[trigger] dst.at(k), next) < 0 by {
                        if k < d0 {
                            lemma_lex_cmp_lt_trans(dst.at(k), src.at(c as int), next);
                        } else {
                            assert(dst.at(k) == src.at(c as int));
                        }
                    }
                }
            }
            c = c + 1;
        }
        out
    }
}

/// Concatenation of task outputs in task order (`outs[t]` covers `[b(t), b(t + 1))` of a cut `b`).
pub fn concat_u64(outs: Vec<Vec<u64>>, total: usize) -> (r: Vec<u64>)
    ensures r@ == flatten(outs@),
{
    let ghost orig = outs@;
    let mut outs = outs;
    let mut res: Vec<u64> = Vec::with_capacity(total);
    proof {
        assert(orig.subrange(0, 0) =~= Seq::<Vec<u64>>::empty());
    }
    let ghost done: int = 0;
    while outs.len() > 0
        invariant
            0 <= done <= orig.len(),
            outs@ == orig.subrange(done, orig.len() as int),
            res@ == flatten(orig.subrange(0, done)),
        decreases outs.len(),
    {
        let mut o = outs.remove(0);
        proof {
            assert(o == orig[done]);
            assert(orig.subrange(0, done + 1).drop_last() =~= orig.subrange(0, done));
            assert(orig.subrange(0, done + 1).last() == orig[done]);
        }
        res.append(&mut o);
        proof {
            done = done + 1;
            assert(outs@ =~= orig.subrange(done, orig.len() as int));
        }
    }
    proof {
        assert(orig.subrange(0, done) =~= orig);
    }
    res
}

/// Concatenation of the first `m` vectors of `outs`, which are removed from `outs`.
pub fn concat_front(outs: &mut Vec<Vec<u64>>, m: usize, total: usize) -> (r: Vec<u64>)
    requires m <= old(outs)@.len(),
    ensures
        r@ == flatten(old(outs)@.subrange(0, m as int)),
        final(outs)@ == old(outs)@.subrange(m as int, old(outs)@.len() as int),
{
    let ghost orig = outs@;
    let mut res: Vec<u64> = Vec::with_capacity(total);
    proof {
        assert(orig.subrange(0, 0) =~= Seq::<Vec<u64>>::empty());
        assert(outs@ =~= orig.subrange(0, orig.len() as int));
    }
    let mut done: usize = 0;
    while done < m
        invariant
            0 <= done <= m <= orig.len(),
            outs@ == orig.subrange(done as int, orig.len() as int),
            res@ == flatten(orig.subrange(0, done as int)),
        decreases m - done,
    {
        let mut o = outs.remove(0);
        proof {
            assert(o == orig[done as int]);
            assert(orig.subrange(0, done + 1).drop_last() =~= orig.subrange(0, done as int));
            assert(orig.subrange(0, done + 1).last() == orig[done as int]);
        }
        res.append(&mut o);
        done = done + 1;
        proof {
            assert(outs@ =~= orig.subrange(done as int, orig.len() as int));
        }
    }
    res
}

/// The elements of the vectors, in order.
pub open spec fn flatten(vs: Seq<Vec<u64>>) -> Seq<u64>
    decreases vs.len(),
{
    if vs.len() == 0 { Seq::empty() } else { flatten(vs.drop_last()) + vs.last()@ }
}

/// Chunk `t` of `k` equal chunks of `0..n` starts at `n * t / k`.
pub open spec fn cut(n: int, k: int, t: int) -> int {
    n * t / k
}

pub fn cut_exec(n: usize, k: usize, t: usize) -> (r: usize)
    requires 1 <= k, t <= k,
    ensures r == cut(n as int, k as int, t as int), r <= n,
{
    proof {
        lemma_cut_le(n as int, k as int, t as int);
        assert((n as int) * (t as int) <= 0xffff_ffff_ffff_ffffint * 0xffff_ffff_ffff_ffffint) by (nonlinear_arith)
            requires 0 <= n <= 0xffff_ffff_ffff_ffffint, 0 <= t <= 0xffff_ffff_ffff_ffffint;
    }
    ((n as u128) * (t as u128) / (k as u128)) as usize
}

pub proof fn lemma_cut_le(n: int, k: int, t: int)
    requires n >= 0, k >= 1, 0 <= t <= k,
    ensures 0 <= cut(n, k, t) <= n,
{
    assert(n * t <= n * k) by (nonlinear_arith) requires n >= 0, t <= k;
    assert((n * t) / k <= (n * k) / k) by (nonlinear_arith) requires n * t <= n * k, k >= 1;
    assert((n * k) / k == n) by (nonlinear_arith) requires k >= 1;
    assert(n * t >= 0) by (nonlinear_arith) requires n >= 0, t >= 0;
    assert(0 <= (n * t) / k) by (nonlinear_arith) requires n * t >= 0, k >= 1;
}

pub proof fn lemma_cut_mono(n: int, k: int, t: int)
    requires n >= 0, k >= 1, 0 <= t < k,
    ensures 0 <= cut(n, k, t) <= cut(n, k, t + 1) <= n, cut(n, k, 0) == 0, cut(n, k, k) == n,
{
    assert(n * t <= n * (t + 1)) by (nonlinear_arith) requires n >= 0, t >= 0;
    assert((n * t) / k <= (n * (t + 1)) / k) by (nonlinear_arith) requires n * t <= n * (t + 1), k >= 1;
    assert(n * (t + 1) <= n * k) by (nonlinear_arith) requires n >= 0, t + 1 <= k;
    assert((n * (t + 1)) / k <= (n * k) / k) by (nonlinear_arith) requires n * (t + 1) <= n * k, k >= 1;
    assert((n * k) / k == n) by (nonlinear_arith) requires k >= 1;
    assert(n * 0 == 0);
    assert(0 <= (n * t) / k) by (nonlinear_arith) requires n * t >= 0, k >= 1;
    assert(n * t >= 0) by (nonlinear_arith) requires n >= 0, t >= 0;
}

/// `flatten` of chunk outputs that each satisfy `ok` at their positions.
pub proof fn lemma_flatten_chunks(vs: Seq<Vec<u64>>, n: int, k: int, ok: spec_fn(int, u64) -> bool)
    requires
        n >= 0, k >= 1, vs.len() <= k,
        forall|t: int| 0 <= t < vs.len() ==> (#[trigger] vs[t])@.len() == cut(n, k, t + 1) - cut(n, k, t),
        forall|t: int, c: int| 0 <= t < vs.len() && cut(n, k, t) <= c < cut(n, k, t + 1)
            ==> ok(c, #[trigger] vs[t]@[c - cut(n, k, t)]),
    ensures
        flatten(vs).len() == cut(n, k, vs.len() as int),
        forall|c: int| 0 <= c < flatten(vs).len() ==> ok(c, #[trigger] flatten(vs)[c]),
    decreases vs.len(),
{
    if vs.len() == 0 {
        assert(cut(n, k, 0) == 0) by {
            assert(n * 0 == 0);
        }
    } else {
        let vi = vs.drop_last();
        let t = vs.len() - 1;
        assert forall|u: int| 0 <= u < vi.len() implies (#[trigger] vi[u])@.len() == cut(n, k, u + 1) - cut(n, k, u) by {
            assert(vi[u] == vs[u]);
        }
        assert forall|u: int, c: int| 0 <= u < vi.len() && cut(n, k, u) <= c < cut(n, k, u + 1)
            implies ok(c, #[trigger] vi[u]@[c - cut(n, k, u)]) by {
            assert(vi[u] == vs[u]);
        }
        lemma_flatten_chunks(vi, n, k, ok);
        lemma_cut_mono(n, k, t);
        let f = flatten(vs);
        let fi = flatten(vi);
        assert(f == fi + vs[t]@);
        assert forall|c: int| 0 <= c < f.len() implies ok(c, #[trigger] f[c]) by {
            if c >= fi.len() {
                assert(f[c] == vs[t]@[c - cut(n, k, t)]);
            } else {
                assert(f[c] == fi[c]);
            }
        }
    }
}

/// Number of tasks for `n` items: at most `workers`, about `grain` items each, at least 1.
pub fn task_count(n: usize, grain: usize, workers: usize) -> (k: usize)
    requires grain >= 1, 1 <= workers <= MAX_WORKERS,
    ensures 1 <= k <= workers,
{
    let mut k = n / grain;
    if k > workers {
        k = workers;
    }
    if k == 0 {
        k = 1;
    }
    k
}

/// The map of every source code to its target code + 1 (0: absent), with at most `workers` threads.
pub fn dict_map(src: Dict, dst: Dict, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<u64>, QueryError>)
    requires src.wf(), dst.wf(), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(m) ==> map_ok(src, dst, m@),
        r matches Err(e) ==> e is WorkerFailed,
{
    let n = src.count;
    let k = task_count(n, 12288, workers);
    let mut tasks: Vec<DictMapTask> = Vec::new();
    let mut t: usize = 0;
    while t < k
        invariant
            src.wf(), dst.wf(), n == src.count, 1 <= k <= workers <= MAX_WORKERS, t <= k,
            tasks@.len() == t,
            forall|u: int| 0 <= u < t ==> (#[trigger] tasks@[u]).pre() && tasks@[u].src == src && tasks@[u].dst == dst
                && tasks@[u].lo == cut(n as int, k as int, u) && tasks@[u].hi == cut(n as int, k as int, u + 1),
        decreases k - t,
    {
        let lo = cut_exec(n, k, t);
        let hi = cut_exec(n, k, t + 1);
        proof {
            lemma_cut_mono(n as int, k as int, t as int);
        }
        tasks.push(DictMapTask { src, dst, lo, hi, out: vec![0u64; hi - lo] });
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(outs) => outs,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let ghost ok = |c: int, v: u64| map_entry_ok(src, dst, c, v);
    proof {
        assert forall|u: int| 0 <= u < outs@.len() implies (#[trigger] outs@[u])@.len() == cut(n as int, k as int, u + 1) - cut(n as int, k as int, u) by {
            assert(tv[u].post(outs@[u]));
        }
        assert forall|u: int, c: int| 0 <= u < outs@.len() && cut(n as int, k as int, u) <= c < cut(n as int, k as int, u + 1)
            implies ok(c, #[trigger] outs@[u]@[c - cut(n as int, k as int, u)]) by {
            assert(tv[u].post(outs@[u]));
        }
        lemma_flatten_chunks(outs@, n as int, k as int, ok);
        lemma_cut_mono(n as int, k as int, 0);
    }
    let ghost ov = outs@;
    let m = concat_u64(outs, n);
    proof {
        assert forall|c: int| 0 <= c < src.count implies map_entry_ok(src, dst, c, #[trigger] m@[c]) by {
            assert(ok(c, flatten(ov)[c]));
        }
    }
    Ok(m)
}

/// The maps of two dictionary pairs (`src1` -> `dst1`, `src2` -> `dst2`) with one `fork_join` (at most `workers` tasks
/// in all; two serial calls of `dict_map` when `workers < 2`).
pub fn dict_map2(src1: Dict, dst1: Dict, src2: Dict, dst2: Dict, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<(Vec<u64>, Vec<u64>), QueryError>)
    requires src1.wf(), dst1.wf(), src2.wf(), dst2.wf(), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok((m1, m2)) ==> map_ok(src1, dst1, m1@) && map_ok(src2, dst2, m2@),
        r matches Err(e) ==> e is WorkerFailed,
{
    if workers < 2 {
        let m1 = match dict_map(src1, dst1, workers, dispatch) {
            Ok(m) => m,
            Err(e) => return Err(e),
        };
        let m2 = match dict_map(src2, dst2, workers, dispatch) {
            Ok(m) => m,
            Err(e) => return Err(e),
        };
        return Ok((m1, m2));
    }
    let n1 = src1.count;
    let n2 = src2.count;
    let k2 = task_count(n2, 12288, workers / 2);
    let k1 = task_count(n1, 12288, workers - k2);
    let mut tasks: Vec<DictMapTask> = Vec::new();
    let mut t: usize = 0;
    while t < k1
        invariant
            src1.wf(), dst1.wf(), n1 == src1.count, 1 <= k1, k1 + k2 <= workers <= MAX_WORKERS, t <= k1,
            tasks@.len() == t,
            forall|u: int| 0 <= u < t ==> (#[trigger] tasks@[u]).pre() && tasks@[u].src == src1 && tasks@[u].dst == dst1
                && tasks@[u].lo == cut(n1 as int, k1 as int, u) && tasks@[u].hi == cut(n1 as int, k1 as int, u + 1),
        decreases k1 - t,
    {
        let lo = cut_exec(n1, k1, t);
        let hi = cut_exec(n1, k1, t + 1);
        proof {
            lemma_cut_mono(n1 as int, k1 as int, t as int);
        }
        tasks.push(DictMapTask { src: src1, dst: dst1, lo, hi, out: vec![0u64; hi - lo] });
        t = t + 1;
    }
    let mut t: usize = 0;
    while t < k2
        invariant
            src2.wf(), dst2.wf(), n2 == src2.count, 1 <= k2, k1 + k2 <= workers <= MAX_WORKERS, t <= k2,
            tasks@.len() == k1 + t,
            forall|u: int| 0 <= u < k1 ==> (#[trigger] tasks@[u]).pre() && tasks@[u].src == src1 && tasks@[u].dst == dst1
                && tasks@[u].lo == cut(n1 as int, k1 as int, u) && tasks@[u].hi == cut(n1 as int, k1 as int, u + 1),
            forall|u: int| k1 <= u < k1 + t ==> (#[trigger] tasks@[u]).pre() && tasks@[u].src == src2 && tasks@[u].dst == dst2
                && tasks@[u].lo == cut(n2 as int, k2 as int, u - k1) && tasks@[u].hi == cut(n2 as int, k2 as int, u - k1 + 1),
        decreases k2 - t,
    {
        let lo = cut_exec(n2, k2, t);
        let hi = cut_exec(n2, k2, t + 1);
        proof {
            lemma_cut_mono(n2 as int, k2 as int, t as int);
        }
        tasks.push(DictMapTask { src: src2, dst: dst2, lo, hi, out: vec![0u64; hi - lo] });
        t = t + 1;
    }
    let ghost tv = tasks@;
    let mut outs = match fork_join(dispatch, tasks) {
        Ok(outs) => outs,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let ghost ov = outs@;
    let ghost ok1 = |c: int, v: u64| map_entry_ok(src1, dst1, c, v);
    let ghost ok2 = |c: int, v: u64| map_entry_ok(src2, dst2, c, v);
    let ghost o1 = ov.subrange(0, k1 as int);
    let ghost o2 = ov.subrange(k1 as int, (k1 + k2) as int);
    proof {
        assert forall|u: int| 0 <= u < o1.len() implies (#[trigger] o1[u])@.len() == cut(n1 as int, k1 as int, u + 1) - cut(n1 as int, k1 as int, u) by {
            assert(tv[u].post(ov[u]));
        }
        assert forall|u: int, c: int| 0 <= u < o1.len() && cut(n1 as int, k1 as int, u) <= c < cut(n1 as int, k1 as int, u + 1)
            implies ok1(c, #[trigger] o1[u]@[c - cut(n1 as int, k1 as int, u)]) by {
            assert(tv[u].post(ov[u]));
        }
        lemma_flatten_chunks(o1, n1 as int, k1 as int, ok1);
        lemma_cut_mono(n1 as int, k1 as int, 0);
        assert forall|u: int| 0 <= u < o2.len() implies (#[trigger] o2[u])@.len() == cut(n2 as int, k2 as int, u + 1) - cut(n2 as int, k2 as int, u) by {
            assert(o2[u] == ov[k1 + u]);
            assert(tv[k1 + u].post(ov[k1 + u]));
        }
        assert forall|u: int, c: int| 0 <= u < o2.len() && cut(n2 as int, k2 as int, u) <= c < cut(n2 as int, k2 as int, u + 1)
            implies ok2(c, #[trigger] o2[u]@[c - cut(n2 as int, k2 as int, u)]) by {
            assert(o2[u] == ov[k1 + u]);
            assert(tv[k1 + u].post(ov[k1 + u]));
        }
        lemma_flatten_chunks(o2, n2 as int, k2 as int, ok2);
        lemma_cut_mono(n2 as int, k2 as int, 0);
    }
    let m1 = concat_front(&mut outs, k1, n1);
    proof {
        assert(outs@ =~= o2);
    }
    let m2 = concat_u64(outs, n2);
    proof {
        assert forall|c: int| 0 <= c < src1.count implies map_entry_ok(src1, dst1, c, #[trigger] m1@[c]) by {
            assert(ok1(c, flatten(o1)[c]));
        }
        assert forall|c: int| 0 <= c < src2.count implies map_entry_ok(src2, dst2, c, #[trigger] m2@[c]) by {
            assert(ok2(c, flatten(o2)[c]));
        }
    }
    Ok((m1, m2))
}

/// Task `u` of the `k` tasks of the map `src -> dst`: source codes `[cut(u), cut(u + 1))`.
pub open spec fn map_task_ok(t: DictMapTask, src: Dict, dst: Dict, k: int, u: int) -> bool {
    &&& t.pre() && t.src == src && t.dst == dst
    &&& t.lo == cut(src.count as int, k, u) && t.hi == cut(src.count as int, k, u + 1)
}

/// Append the `k` tasks of the map `src -> dst`.
fn push_map_tasks(tasks: &mut Vec<DictMapTask>, src: Dict, dst: Dict, k: usize)
    requires src.wf(), dst.wf(), 1 <= k,
    ensures
        final(tasks)@.len() == old(tasks)@.len() + k,
        forall|u: int| 0 <= u < old(tasks)@.len() ==> #[trigger] final(tasks)@[u] == old(tasks)@[u],
        forall|u: int| 0 <= u < k ==> map_task_ok(#[trigger] final(tasks)@[old(tasks)@.len() + u], src, dst, k as int, u),
{
    let ghost t0 = tasks@;
    let n = src.count;
    let mut t: usize = 0;
    while t < k
        invariant
            src.wf(), dst.wf(), n == src.count, 1 <= k, t <= k,
            tasks@.len() == t0.len() + t,
            forall|u: int| 0 <= u < t0.len() ==> #[trigger] tasks@[u] == t0[u],
            forall|u: int| 0 <= u < t ==> map_task_ok(#[trigger] tasks@[t0.len() + u], src, dst, k as int, u),
        decreases k - t,
    {
        let lo = cut_exec(n, k, t);
        let hi = cut_exec(n, k, t + 1);
        proof {
            lemma_cut_mono(n as int, k as int, t as int);
        }
        tasks.push(DictMapTask { src, dst, lo, hi, out: vec![0u64; hi - lo] });
        proof {
            assert(tasks@[t0.len() + t as int].lo == lo);
        }
        t = t + 1;
    }
}

/// The map of the `k` outputs at the front of `outs` (outputs of the tasks of `src -> dst`), removed from `outs`.
fn take_map(outs: &mut Vec<Vec<u64>>, src: Dict, dst: Dict, k: usize) -> (m: Vec<u64>)
    requires
        1 <= k <= old(outs)@.len(),
        forall|u: int| 0 <= u < k ==> (#[trigger] old(outs)@[u])@.len()
            == cut(src.count as int, k as int, u + 1) - cut(src.count as int, k as int, u),
        forall|u: int, c: int| 0 <= u < k && cut(src.count as int, k as int, u) <= c < cut(src.count as int, k as int, u + 1)
            ==> map_entry_ok(src, dst, c, #[trigger] old(outs)@[u]@[c - cut(src.count as int, k as int, u)]),
    ensures
        map_ok(src, dst, m@),
        final(outs)@ == old(outs)@.subrange(k as int, old(outs)@.len() as int),
{
    let ghost ov = outs@;
    let ghost o1 = ov.subrange(0, k as int);
    let ghost n = src.count as int;
    let ghost ok = |c: int, v: u64| map_entry_ok(src, dst, c, v);
    proof {
        assert forall|u: int| 0 <= u < o1.len() implies (#[trigger] o1[u])@.len() == cut(n, k as int, u + 1) - cut(n, k as int, u) by {
            assert(o1[u] == ov[u]);
        }
        assert forall|u: int, c: int| 0 <= u < o1.len() && cut(n, k as int, u) <= c < cut(n, k as int, u + 1)
            implies ok(c, #[trigger] o1[u]@[c - cut(n, k as int, u)]) by {
            assert(o1[u] == ov[u]);
        }
        lemma_flatten_chunks(o1, n, k as int, ok);
        lemma_cut_mono(n, k as int, 0);
    }
    let m = concat_front(outs, k, src.count);
    proof {
        assert forall|c: int| 0 <= c < src.count implies map_entry_ok(src, dst, c, #[trigger] m@[c]) by {
            assert(ok(c, flatten(o1)[c]));
        }
    }
    m
}

/// The outputs of the `k` tasks of `src -> dst` starting at task `base` meet `take_map`'s precondition.
proof fn lemma_map_outs(tv: Seq<DictMapTask>, ov: Seq<Vec<u64>>, src: Dict, dst: Dict, base: int, k: int)
    requires
        0 <= base, base + k <= tv.len() == ov.len(), 1 <= k,
        forall|u: int| 0 <= u < k ==> map_task_ok(#[trigger] tv[base + u], src, dst, k, u),
        forall|u: int| 0 <= u < tv.len() ==> (#[trigger] tv[u]).post(ov[u]),
    ensures ({
        let o = ov.subrange(base, ov.len() as int);
        &&& forall|u: int| 0 <= u < k ==> (#[trigger] o[u])@.len()
            == cut(src.count as int, k, u + 1) - cut(src.count as int, k, u)
        &&& forall|u: int, c: int| 0 <= u < k && cut(src.count as int, k, u) <= c < cut(src.count as int, k, u + 1)
            ==> map_entry_ok(src, dst, c, #[trigger] o[u]@[c - cut(src.count as int, k, u)])
    }),
{
    let o = ov.subrange(base, ov.len() as int);
    assert forall|u: int| 0 <= u < k implies (#[trigger] o[u])@.len() == cut(src.count as int, k, u + 1) - cut(src.count as int, k, u) by {
        assert(map_task_ok(tv[base + u], src, dst, k, u));
        assert(tv[base + u].post(ov[base + u]));
    }
    assert forall|u: int, c: int| 0 <= u < k && cut(src.count as int, k, u) <= c < cut(src.count as int, k, u + 1)
        implies map_entry_ok(src, dst, c, #[trigger] o[u]@[c - cut(src.count as int, k, u)]) by {
        assert(map_task_ok(tv[base + u], src, dst, k, u));
        assert(tv[base + u].post(ov[base + u]));
    }
}

/// The maps of three dictionary pairs with one `fork_join` (at most `workers` tasks in all, at least one per map).
pub fn dict_map3(src1: Dict, dst1: Dict, src2: Dict, dst2: Dict, src3: Dict, dst3: Dict, workers: usize,
    dispatch: &mut Dispatch) -> (r: Result<(Vec<u64>, Vec<u64>, Vec<u64>), QueryError>)
    requires src1.wf(), dst1.wf(), src2.wf(), dst2.wf(), src3.wf(), dst3.wf(), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok((m1, m2, m3)) ==> map_ok(src1, dst1, m1@) && map_ok(src2, dst2, m2@) && map_ok(src3, dst3, m3@),
        r matches Err(e) ==> e is WorkerFailed,
{
    // at most `workers` tasks in all; when `workers < 3` three merges on the calling thread
    if workers < 3 {
        let m1 = merge_map(src1, dst1);
        let m2 = merge_map(src2, dst2);
        let m3 = merge_map(src3, dst3);
        return Ok((m1, m2, m3));
    }
    let serial = false;
    let w3 = if serial { 1 } else { workers / 3 };
    let k2 = task_count(src2.count, 12288, w3);
    let k3 = task_count(src3.count, 12288, w3);
    let k1 = if serial { 1 } else { task_count(src1.count, 12288, workers - k2 - k3) };
    let mut tasks: Vec<DictMapTask> = Vec::new();
    push_map_tasks(&mut tasks, src1, dst1, k1);
    push_map_tasks(&mut tasks, src2, dst2, k2);
    let ghost t2 = tasks@;
    push_map_tasks(&mut tasks, src3, dst3, k3);
    let ghost tv = tasks@;
    proof {
        assert forall|i: int| 0 <= i < tv.len() implies #[trigger] tv[i].pre() by {
            if i < k1 {
                assert(tv[i] == t2[i]);
                assert(map_task_ok(t2[0 + i], src1, dst1, k1 as int, i));
            } else if i < k1 + k2 {
                assert(tv[i] == t2[i]);
                assert(map_task_ok(t2[k1 + (i - k1)], src2, dst2, k2 as int, i - k1));
            } else {
                assert(map_task_ok(tv[(k1 + k2) + (i - k1 - k2)], src3, dst3, k3 as int, i - k1 - k2));
            }
        }
        assert forall|u: int| 0 <= u < k1 implies map_task_ok(#[trigger] tv[0 + u], src1, dst1, k1 as int, u) by {
            assert(tv[u] == t2[u]);
        }
        assert forall|u: int| 0 <= u < k2 implies map_task_ok(#[trigger] tv[k1 + u], src2, dst2, k2 as int, u) by {
            assert(tv[k1 + u] == t2[k1 + u]);
        }
    }
    let mut outs = match super::tasks::run_tasks(dispatch, tasks, serial) {
        Ok(outs) => outs,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let ghost ov = outs@;
    proof {
        assert forall|u: int| 0 <= u < tv.len() implies (#[trigger] tv[u]).post(ov[u]) by {}
        lemma_map_outs(tv, ov, src1, dst1, 0, k1 as int);
        assert(ov.subrange(0, ov.len() as int) =~= ov);
        lemma_map_outs(tv, ov, src2, dst2, k1 as int, k2 as int);
        lemma_map_outs(tv, ov, src3, dst3, (k1 + k2) as int, k3 as int);
    }
    let m1 = take_map(&mut outs, src1, dst1, k1);
    proof {
        assert(outs@ =~= ov.subrange(k1 as int, ov.len() as int));
    }
    let m2 = take_map(&mut outs, src2, dst2, k2);
    proof {
        assert(outs@ =~= ov.subrange((k1 + k2) as int, ov.len() as int));
    }
    let m3 = take_map(&mut outs, src3, dst3, k3);
    Ok((m1, m2, m3))
}

} // verus!
