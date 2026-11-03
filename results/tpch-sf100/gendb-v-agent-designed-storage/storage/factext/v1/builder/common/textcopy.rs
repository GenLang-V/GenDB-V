//! Plain text columns in stored order: `copy_text` lays out the values of a delivered text column in the order a
//! row map (a bijection) gives, as U64 offsets (`n + 1`, from 0) and bytes. The offsets are prefix sums over the
//! stored rows (calling thread); the bytes are copied by worker tasks into per-task buffers that are then
//! concatenated. Value `j` of the result is the source value of canonical row `rm_at(rm, j)`.
use vstd::prelude::*;
use crate::link::query::{text_at, text_wf, TextCol, TextView};
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::builder::iface::common::colfmt::*;
use crate::builder::common::colsrc::*;
use crate::builder::common::perm::*;

verus! {

/// Byte length of value `i`.
pub open spec fn tlen(t: TextView, i: int) -> int {
    t.offsets[i + 1] - t.offsets[i]
}

/// `tlen` as a function.
pub open spec fn tlen_fn(t: TextView) -> spec_fn(int) -> int {
    |i: int| tlen(t, i)
}

/// The row map as integers.
pub open spec fn rm_seq(rm: RowMap, n: int) -> Seq<int> {
    Seq::new(n as nat, |j: int| rm_at(rm, j))
}

/// The row map is a bijection of `[0, n)`.
pub open spec fn rm_perm(rm: RowMap, n: int) -> bool {
    rm_wf(rm, n) && is_perm(rm_seq(rm, n), n)
}

/// Bytes of the stored rows before `j`.
#[verifier::opaque]
pub open spec fn pre_bytes(t: TextView, rm: RowMap, n: int, j: int) -> int {
    sum_over(rm_seq(rm, n), tlen_fn(t), j)
}

/// Canonical rows named by a well-formed map lie below `n`.
proof fn lemma_rm_bound(rm: RowMap, n: int, j: int)
    requires
        rm_wf(rm, n),
        0 <= j < n,
    ensures
        0 <= rm_at(rm, j) < n,
{
    match rm {
        RowMap::Identity => {},
        RowMap::Map(v) => {
            assert(v@[j] < n);
        },
    }
}

/// One more stored row adds its value's bytes.
proof fn lemma_pre_bytes_step(t: TextView, rm: RowMap, n: int, j: int)
    requires
        text_wf(t, n),
        rm_wf(rm, n),
        0 <= j < n,
    ensures
        pre_bytes(t, rm, n, j + 1) == pre_bytes(t, rm, n, j) + tlen(t, rm_at(rm, j)),
        0 <= tlen(t, rm_at(rm, j)),
        0 <= t.offsets[rm_at(rm, j)],
        t.offsets[rm_at(rm, j) + 1] <= t.bytes.len(),
{
    reveal(pre_bytes);
    lemma_rm_bound(rm, n, j);
    let i = rm_at(rm, j);
    assert(0 <= t.offsets[i] <= t.offsets[i + 1] <= t.bytes.len());
    assert(rm_seq(rm, n)[j] == i);
}

/// No stored rows, no bytes.
proof fn lemma_pre_bytes_zero(t: TextView, rm: RowMap, n: int)
    ensures pre_bytes(t, rm, n, 0) == 0,
{
    reveal(pre_bytes);
}

/// Prefix byte counts are nonnegative and nondecreasing.
proof fn lemma_pre_bytes_mono(t: TextView, rm: RowMap, n: int, a: int, b: int)
    requires
        text_wf(t, n),
        rm_wf(rm, n),
        0 <= a <= b <= n,
    ensures
        0 <= pre_bytes(t, rm, n, a) <= pre_bytes(t, rm, n, b),
    decreases b,
{
    if b > a {
        lemma_pre_bytes_mono(t, rm, n, a, b - 1);
        lemma_pre_bytes_step(t, rm, n, b - 1);
    } else if b > 0 {
        lemma_pre_bytes_mono(t, rm, n, 0, b - 1);
        lemma_pre_bytes_step(t, rm, n, b - 1);
    } else {
        lemma_pre_bytes_zero(t, rm, n);
    }
}

proof fn lemma_telescope(t: TextView, n: int, k: int)
    requires
        text_wf(t, n),
        0 <= k <= n,
    ensures
        sum_range(tlen_fn(t), k) == t.offsets[k] - t.offsets[0],
    decreases k,
{
    if k > 0 {
        lemma_telescope(t, n, k - 1);
    }
}

/// The stored rows hold all of the source's bytes, which fit in memory.
proof fn lemma_total_bytes(t: TextView, tb: &[u8], rm: RowMap, n: int)
    requires
        text_wf(t, n),
        t.bytes == tb@,
        rm_perm(rm, n),
    ensures
        pre_bytes(t, rm, n, n) <= usize::MAX,
{
    reveal(pre_bytes);
    lemma_sum_perm(rm_seq(rm, n), n, tlen_fn(t));
    lemma_telescope(t, n, n);
    vstd::slice::axiom_spec_len(tb);
    if n > 0 {
        assert(0 <= t.offsets[0] <= t.offsets[0int + 1]);
        assert(t.offsets[n - 1] <= t.offsets[(n - 1) + 1] <= t.bytes.len());
    }
}

/// Stored offsets: entry `j` is the byte count of the stored rows before `j` (calling thread).
fn stored_offsets(t: &TextCol, n: usize, rm: &RowMap) -> (offs: Vec<u64>)
    requires
        text_wf(t@, n as int),
        rm_perm(*rm, n as int),
    ensures
        offs@.len() == n + 1,
        forall|j: int| 0 <= j <= n ==> #[trigger] offs@[j] == pre_bytes(t@, *rm, n as int, j),
        pre_bytes(t@, *rm, n as int, n as int) <= usize::MAX,
{
    proof {
        lemma_total_bytes(t@, t.bytes, *rm, n as int);
        vstd::slice::axiom_spec_len(t.offsets);
        lemma_pre_bytes_zero(t@, *rm, n as int);
    }
    let mut offs: Vec<u64> = Vec::with_capacity(n + 1);
    offs.push(0);
    let mut acc: u64 = 0;
    let mut j: usize = 0;
    while j < n
        invariant
            text_wf(t@, n as int),
            rm_perm(*rm, n as int),
            pre_bytes(t@, *rm, n as int, n as int) <= usize::MAX,
            j <= n,
            offs@.len() == j + 1,
            acc == pre_bytes(t@, *rm, n as int, j as int),
            forall|k: int| 0 <= k <= j ==> #[trigger] offs@[k] == pre_bytes(t@, *rm, n as int, k),
        decreases n - j,
    {
        let i = rm_get(rm, n, j);
        proof {
            lemma_pre_bytes_step(t@, *rm, n as int, j as int);
            lemma_pre_bytes_mono(t@, *rm, n as int, j + 1, n as int);
        }
        let len = (t.offsets[i + 1] - t.offsets[i]) as u64;
        acc = acc + len;
        offs.push(acc);
        j = j + 1;
    }
    offs
}

/// Value `r`'s bytes sit in `buf` at its stored offset relative to stored row `lo`.
pub open spec fn seg_ok(buf: Seq<u8>, t: TextView, rm: RowMap, n: int, lo: int, r: int) -> bool {
    buf.subrange(pre_bytes(t, rm, n, r) - pre_bytes(t, rm, n, lo), pre_bytes(t, rm, n, r + 1) - pre_bytes(t, rm, n, lo))
        == text_at(t, rm_at(rm, r))
}

/// A segment stays in place when only bytes at or after its end change.
proof fn lemma_seg_frame(b1: Seq<u8>, b2: Seq<u8>, t: TextView, rm: RowMap, n: int, lo: int, r: int, upto: int)
    requires
        text_wf(t, n),
        rm_wf(rm, n),
        0 <= lo <= r < n,
        seg_ok(b1, t, rm, n, lo, r),
        pre_bytes(t, rm, n, r + 1) - pre_bytes(t, rm, n, lo) <= upto,
        upto <= b1.len(),
        b1.len() == b2.len(),
        forall|q: int| 0 <= q < upto ==> #[trigger] b2[q] == b1[q],
    ensures
        seg_ok(b2, t, rm, n, lo, r),
{
    lemma_pre_bytes_mono(t, rm, n, lo, r);
    lemma_pre_bytes_mono(t, rm, n, r, r + 1);
    let (x, y) = (pre_bytes(t, rm, n, r) - pre_bytes(t, rm, n, lo), pre_bytes(t, rm, n, r + 1) - pre_bytes(t, rm, n, lo));
    assert(b2.subrange(x, y) =~= b1.subrange(x, y));
}

/// One worker task: copy the values of stored rows `[lo, hi)` into `buf`.
pub struct CopyTask {
    pub t: TextCol,
    pub rm: RowMap,
    pub n: usize,
    pub lo: usize,
    pub hi: usize,
    pub buf: Vec<u8>,
}

impl WorkerTask for CopyTask {
    type Output = Vec<u8>;

    open spec fn pre(&self) -> bool {
        &&& twf(self.t@, self.n as int)
        &&& rm_wf(self.rm, self.n as int)
        &&& self.lo <= self.hi <= self.n
        &&& self.buf@.len() == pre_bytes(self.t@, self.rm, self.n as int, self.hi as int) - pre_bytes(self.t@, self.rm, self.n as int, self.lo as int)
    }

    open spec fn post(&self, out: Vec<u8>) -> bool {
        &&& out@.len() == self.buf@.len()
        &&& forall|r: int| self.lo <= r < self.hi ==> #[trigger] seg_ok(out@, self.t@, self.rm, self.n as int, self.lo as int, r)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: Vec<u8>) {
        let CopyTask { t, rm, n, lo, hi, mut buf } = self;
        proof {
            reveal(twf);
        }
        let blen = buf.len();
        let ghost base = pre_bytes(t@, rm, n as int, lo as int);
        proof {
            lemma_pre_bytes_mono(t@, rm, n as int, lo as int, hi as int);
            vstd::slice::axiom_spec_len(t.bytes);
        }
        let mut pos: usize = 0;
        let mut j = lo;
        while j < hi
            invariant
                self.t == t && self.rm == rm && self.n == n && self.lo == lo && self.hi == hi,
                text_wf(t@, n as int),
                rm_wf(rm, n as int),
                t@.bytes.len() <= usize::MAX,
                lo <= j <= hi <= n,
                base == pre_bytes(t@, rm, n as int, lo as int),
                blen == pre_bytes(t@, rm, n as int, hi as int) - base,
                buf@.len() == blen,
                pos == pre_bytes(t@, rm, n as int, j as int) - base,
                forall|r: int| lo <= r < j ==> #[trigger] seg_ok(buf@, t@, rm, n as int, lo as int, r),
            decreases hi - j,
        {
            let i = rm_get(&rm, n, j);
            proof {
                lemma_pre_bytes_step(t@, rm, n as int, j as int);
                lemma_pre_bytes_mono(t@, rm, n as int, j + 1, hi as int);
                lemma_pre_bytes_mono(t@, rm, n as int, lo as int, j as int);
            }
            let a = t.offsets[i] as usize;
            let len = (t.offsets[i + 1] - t.offsets[i]) as usize;
            let ghost before = buf@;
            let mut k: usize = 0;
            while k < len
                invariant
                    a + len <= t@.bytes.len(),
                    pos + len <= blen,
                    buf@.len() == blen,
                    before.len() == blen,
                    k <= len,
                    forall|q: int| 0 <= q < pos ==> #[trigger] buf@[q] == before[q],
                    forall|q: int| 0 <= q < k ==> #[trigger] buf@[pos + q] == t@.bytes[a + q],
                decreases len - k,
            {
                buf[pos + k] = t.bytes[a + k];
                k = k + 1;
            }
            proof {
                assert forall|q: int| 0 <= q < len implies #[trigger] buf@.subrange(pos as int, pos + len)[q] == t@.bytes.subrange(a as int, a + len)[q] by {
                    assert(buf@[pos + q] == t@.bytes[a + q]);
                }
                assert(buf@.subrange(pos as int, pos + len) =~= t@.bytes.subrange(a as int, a + len));
                assert(seg_ok(buf@, t@, rm, n as int, lo as int, j as int));
                assert forall|r: int| lo <= r < j + 1 implies #[trigger] seg_ok(buf@, t@, rm, n as int, lo as int, r) by {
                    if r < j {
                        lemma_pre_bytes_mono(t@, rm, n as int, r + 1, j as int);
                        lemma_seg_frame(before, buf@, t@, rm, n as int, lo as int, r, pos as int);
                    }
                }
            }
            pos = pos + len;
            j = j + 1;
        }
        buf
    }
}

/// Splits `n` rows into at most `ntasks` chunks of `chunk` rows: `chunk * ntasks >= n`.
fn chunk_size(n: usize, ntasks: usize) -> (chunk: usize)
    requires 1 <= ntasks, ntasks <= n,
    ensures chunk >= 1, chunk * ntasks >= n, chunk <= n,
{
    let q = n / ntasks;
    let rr = n % ntasks;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, ntasks as int);
        assert((n / ntasks) * ntasks == ntasks * (n / ntasks)) by (nonlinear_arith);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(n as int, ntasks as int);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(n as int, ntasks as int);
        if rr != 0 {
            assert(q < n) by (nonlinear_arith) requires q * ntasks + rr == n, ntasks >= 1, q >= 0, rr >= 1;
        } else {
            assert(q <= n) by (nonlinear_arith) requires q * ntasks == n, ntasks >= 1, q >= 0;
        }
    }
    let chunk = if rr == 0 { q } else { q + 1 };
    proof {
        if rr != 0 {
            assert(chunk * ntasks >= n) by (nonlinear_arith) requires chunk == q + 1, n == q * ntasks + rr, rr < ntasks;
        }
        assert(chunk >= 1) by (nonlinear_arith) requires chunk * ntasks >= n, n >= 1, ntasks >= 1, chunk >= 0;
    }
    chunk
}

/// Appending a task's buffer keeps the earlier values in place and adds the task's values.
proof fn lemma_concat_step(t: TextView, rm: RowMap, n: int, lo: int, hi: int, before: Seq<u8>, ob: Seq<u8>, after: Seq<u8>)
    requires
        text_wf(t, n),
        rm_wf(rm, n),
        0 <= lo <= hi <= n,
        before.len() == pre_bytes(t, rm, n, lo),
        pre_bytes(t, rm, n, 0) == 0,
        forall|j: int| 0 <= j < lo ==> #[trigger] seg_ok(before, t, rm, n, 0, j),
        ob.len() == pre_bytes(t, rm, n, hi) - pre_bytes(t, rm, n, lo),
        forall|r: int| lo <= r < hi ==> #[trigger] seg_ok(ob, t, rm, n, lo, r),
        after == before + ob,
    ensures
        after.len() == pre_bytes(t, rm, n, hi),
        forall|j: int| 0 <= j < hi ==> #[trigger] seg_ok(after, t, rm, n, 0, j),
{
    let p0 = pre_bytes(t, rm, n, lo);
    lemma_pre_bytes_mono(t, rm, n, lo, hi);
    assert forall|j: int| 0 <= j < hi implies #[trigger] seg_ok(after, t, rm, n, 0, j) by {
        lemma_pre_bytes_mono(t, rm, n, j, j + 1);
        let (x, y) = (pre_bytes(t, rm, n, j), pre_bytes(t, rm, n, j + 1));
        if j < lo {
            lemma_pre_bytes_mono(t, rm, n, j + 1, lo);
            assert(seg_ok(before, t, rm, n, 0, j));
            assert(after.subrange(x, y) =~= before.subrange(x, y));
        } else {
            lemma_pre_bytes_mono(t, rm, n, lo, j);
            lemma_pre_bytes_mono(t, rm, n, j + 1, hi);
            assert(seg_ok(ob, t, rm, n, lo, j));
            assert(after.subrange(x, y) =~= ob.subrange(x - p0, y - p0));
        }
    }
}

/// The values of `t` (`n` rows) in the stored order `rm`, as offsets (from 0) and bytes.
pub fn copy_text(t: &TextCol, n: usize, rm: &RowMap, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<(Vec<u64>, Vec<u8>), WorkerFailure>)
    requires
        twf(t@, n as int),
        rm_perm(*rm, n as int),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok((offs, bytes)) ==> text_parts_wf(offs@, bytes@, n as int)
            && forall|j: int| 0 <= j < n ==> #[trigger] text_of(offs@, bytes@, j) == text_at(t@, rm_at(*rm, j)),
{
    proof {
        reveal(twf);
    }
    let offs = stored_offsets(t, n, rm);
    let ntasks: usize = if n < workers { n } else { workers };
    let chunk: usize = if ntasks == 0 { 1 } else { chunk_size(n, ntasks) };
    let mut tasks: Vec<CopyTask> = Vec::new();
    let mut lo: usize = 0;
    while lo < n
        invariant
            text_wf(t@, n as int),
            twf(t@, n as int),
            rm_perm(*rm, n as int),
            offs@.len() == n + 1,
            forall|j: int| 0 <= j <= n ==> #[trigger] offs@[j] == pre_bytes(t@, *rm, n as int, j),
            pre_bytes(t@, *rm, n as int, n as int) <= usize::MAX,
            chunk >= 1,
            ntasks <= MAX_WORKERS,
            n > 0 ==> ntasks >= 1 && chunk * ntasks >= n,
            lo <= n,
            tasks@.len() <= ntasks,
            lo < n ==> lo == tasks@.len() * chunk,
            forall|u: int| 0 <= u < tasks@.len() ==> (#[trigger] tasks@[u]).pre() && tasks@[u].t == *t && tasks@[u].rm == *rm && tasks@[u].n == n,
            tasks@.len() == 0 ==> lo == 0,
            tasks@.len() > 0 ==> tasks@[0].lo == 0 && tasks@[tasks@.len() - 1].hi == lo,
            forall|u: int| 0 <= u < tasks@.len() - 1 ==> #[trigger] tasks@[u].hi == tasks@[u + 1].lo,
        decreases n - lo,
    {
        proof {
            assert(tasks@.len() < ntasks) by (nonlinear_arith) requires tasks@.len() * chunk < n, chunk * ntasks >= n, chunk >= 1;
        }
        let hi = if n - lo > chunk { lo + chunk } else { n };
        proof {
            if hi < n {
                assert(hi == (tasks@.len() + 1) * chunk) by (nonlinear_arith) requires hi == lo + chunk, lo == tasks@.len() * chunk;
            }
            lemma_pre_bytes_mono(t@, *rm, n as int, lo as int, hi as int);
            lemma_pre_bytes_mono(t@, *rm, n as int, hi as int, n as int);
        }
        let size = (offs[hi] - offs[lo]) as usize;
        let buf: Vec<u8> = vec![0u8; size];
        let task = CopyTask { t: TextCol { offsets: t.offsets, bytes: t.bytes }, rm: rm_clone(rm), n, lo, hi, buf };
        let ghost old_tasks = tasks@;
        tasks.push(task);
        proof {
            assert forall|u: int| 0 <= u < tasks@.len() - 1 implies #[trigger] tasks@[u].hi == tasks@[u + 1].lo by {
                if u < old_tasks.len() - 1 {
                    assert(tasks@[u] == old_tasks[u] && tasks@[u + 1] == old_tasks[u + 1]);
                }
            }
        }
        lo = hi;
    }
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let ghost all_outs = outs@;
    let mut outs = outs;
    let nt = outs.len();
    let mut bytes: Vec<u8> = Vec::new();
    let mut u: usize = 0;
    proof {
        lemma_pre_bytes_zero(t@, *rm, n as int);
    }
    while u < nt
        invariant
            nt == all_outs.len(),
            nt == tv.len(),
            u <= nt,
            outs@ == all_outs.subrange(u as int, nt as int),
            text_wf(t@, n as int),
            rm_wf(*rm, n as int),
            pre_bytes(t@, *rm, n as int, 0) == 0,
            forall|w: int| 0 <= w < tv.len() ==> (#[trigger] tv[w]).pre() && tv[w].t == *t && tv[w].rm == *rm && tv[w].n == n,
            forall|w: int| 0 <= w < nt ==> tv[w].post(#[trigger] all_outs[w]),
            tv.len() > 0 ==> tv[0].lo == 0 && tv[tv.len() - 1].hi == n,
            tv.len() == 0 ==> n == 0,
            forall|w: int| 0 <= w < tv.len() - 1 ==> #[trigger] tv[w].hi == tv[w + 1].lo,
            bytes@.len() == pre_bytes(t@, *rm, n as int, if u == 0 { 0 } else { tv[u - 1].hi as int }),
            forall|j: int| 0 <= j < (if u == 0 { 0 } else { tv[u - 1].hi as int }) ==> #[trigger] seg_ok(bytes@, t@, *rm, n as int, 0, j),
        decreases nt - u,
    {
        let mut o = outs.remove(0);
        let ghost task = tv[u as int];
        proof {
            assert(o == all_outs[u as int]);
            if u > 0 {
                assert(tv[u - 1].hi == tv[(u - 1) + 1].lo);
            }
        }
        let ghost before = bytes@;
        let ghost ob = o@;
        bytes.append(&mut o);
        proof {
            lemma_concat_step(t@, *rm, n as int, task.lo as int, task.hi as int, before, ob, bytes@);
        }
        u = u + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < n implies #[trigger] text_range_ok(offs@, bytes@, j) by {
            lemma_pre_bytes_mono(t@, *rm, n as int, j, j + 1);
            lemma_pre_bytes_mono(t@, *rm, n as int, j + 1, n as int);
        }
        assert forall|j: int| 0 <= j < n implies #[trigger] text_of(offs@, bytes@, j) == text_at(t@, rm_at(*rm, j)) by {
            assert(seg_ok(bytes@, t@, *rm, n as int, 0, j));
        }
    }
    Ok((offs, bytes))
}

} // verus!
