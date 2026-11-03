//! Parallel check that a frame-of-reference U32 key column is dense: row `c` holds the key `c + 1` (then a key
//! lookup is one subtraction). Each worker checks one contiguous row range; the ranges cover `[0, n)`.
use vstd::prelude::*;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS, WorkerTask, fork_join};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::common::forview::*;

verus! {

/// Rows `[lo, hi)` hold `row + 1`.
pub open spec fn dense_on(codes: Seq<u32>, bases: Seq<i64>, bs: int, lo: int, hi: int) -> bool {
    forall|c: int| lo <= c < hi ==> #[trigger] fv32(codes, bases, bs, c) == c + 1
}

/// One range of the dense check.
pub struct DenseTask {
    pub codes: &'static [u32],
    pub bases: &'static [i64],
    pub d: Div,
    pub n: usize,
    pub lo: usize,
    pub hi: usize,
}

impl WorkerTask for DenseTask {
    type Output = bool;

    open spec fn pre(&self) -> bool {
        &&& self.d.ok()
        &&& col32_ok(self.codes@, self.bases@, self.d.bs as int, self.n as int)
        &&& self.lo <= self.hi <= self.n
    }

    open spec fn post(&self, out: bool) -> bool {
        out == dense_on(self.codes@, self.bases@, self.d.bs as int, self.lo as int, self.hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: bool) {
        let mut c = self.lo;
        while c < self.hi
            invariant
                self.d.ok(),
                col32_ok(self.codes@, self.bases@, self.d.bs as int, self.n as int),
                self.lo <= c <= self.hi <= self.n,
                dense_on(self.codes@, self.bases@, self.d.bs as int, self.lo as int, c as int),
            decreases self.hi - c,
        {
            let v = get32(self.codes, self.bases, self.d, self.n, c);
            if v as i128 != c as i128 + 1 {
                return false;
            }
            c = c + 1;
        }
        true
    }
}

/// Start of range `t` of `parts` near-equal ranges of `[0, n)`.
pub open spec fn range_at(n: int, parts: int, t: int) -> int {
    n * t / parts
}

/// Range starts: 0 first, `n` last, nondecreasing.
pub proof fn lemma_range_at(n: int, parts: int, a: int, b: int)
    requires 1 <= parts, 0 <= a <= b <= parts, 0 <= n,
    ensures
        0 <= range_at(n, parts, a) <= range_at(n, parts, b) <= n,
        range_at(n, parts, 0) == 0,
        range_at(n, parts, parts) == n,
{
    let x = n * a;
    let y = n * b;
    assert(0 <= x <= y) by (nonlinear_arith) requires 0 <= a <= b, n >= 0, x == n * a, y == n * b;
    vstd::arithmetic::div_mod::lemma_div_is_ordered(x, y, parts);
    assert(y <= n * parts) by (nonlinear_arith) requires b <= parts, n >= 0, y == n * b;
    vstd::arithmetic::div_mod::lemma_div_is_ordered(y, n * parts, parts);
    vstd::arithmetic::div_mod::lemma_div_by_multiple(n, parts);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(x, parts);
    assert(n * 0 == 0);
}

/// `range_at` in machine integers.
pub fn range_start(n: usize, parts: usize, t: usize) -> (r: usize)
    requires 1 <= parts, t <= parts,
    ensures r as int == range_at(n as int, parts as int, t as int),
{
    proof {
        let m = 0xffff_ffff_ffff_ffffint;
        assert((n as int) * (t as int) <= m * m) by (nonlinear_arith) requires 0 <= n <= m, 0 <= t <= m;
        lemma_range_at(n as int, parts as int, t as int, parts as int);
    }
    let x = (n as u128) * (t as u128) / (parts as u128);
    x as usize
}

/// Whether every row of the column holds `row + 1`, checked by at most `workers` threads.
pub fn check_dense(codes: &'static [u32], bases: &'static [i64], d: Div, n: usize, workers: usize,
    dispatch: &mut Dispatch) -> (r: Result<bool, WorkerFailure>)
    requires d.ok(), col32_ok(codes@, bases@, d.bs as int, n as int), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(b) ==> b == dense_on(codes@, bases@, d.bs as int, 0, n as int),
{
    let parts = workers;
    let mut tasks: Vec<DenseTask> = Vec::new();
    let mut t: usize = 0;
    while t < parts
        invariant
            d.ok(), col32_ok(codes@, bases@, d.bs as int, n as int),
            1 <= parts <= MAX_WORKERS,
            t <= parts,
            tasks@.len() == t,
            forall|i: int| 0 <= i < t ==> (#[trigger] tasks@[i]).pre(),
            forall|i: int| 0 <= i < t ==> (#[trigger] tasks@[i]).codes == codes && tasks@[i].bases == bases
                && tasks@[i].d == d && tasks@[i].n == n,
            forall|i: int| 0 <= i < t ==> (#[trigger] tasks@[i]).lo == range_at(n as int, parts as int, i)
                && tasks@[i].hi == range_at(n as int, parts as int, i + 1),
        decreases parts - t,
    {
        let lo = range_start(n, parts, t);
        let hi = range_start(n, parts, t + 1);
        proof {
            lemma_range_at(n as int, parts as int, t as int, t as int + 1);
        }
        tasks.push(DenseTask { codes, bases, d, n, lo, hi });
        t = t + 1;
    }
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let ghost tk = tasks@;
    let mut ok = true;
    let mut i: usize = 0;
    while i < outs.len()
        invariant
            outs@.len() == parts, tk.len() == parts,
            forall|k: int| 0 <= k < parts ==> #[trigger] tk[k].post(outs@[k]),
            forall|k: int| 0 <= k < parts ==> (#[trigger] tk[k]).codes == codes && tk[k].bases == bases && tk[k].d == d,
            forall|k: int| 0 <= k < parts ==> (#[trigger] tk[k]).lo == range_at(n as int, parts as int, k)
                && tk[k].hi == range_at(n as int, parts as int, k + 1),
            1 <= parts,
            i <= parts,
            ok == dense_on(codes@, bases@, d.bs as int, 0, range_at(n as int, parts as int, i as int)),
        decreases parts - i,
    {
        proof {
            let a = range_at(n as int, parts as int, i as int);
            let b = range_at(n as int, parts as int, i as int + 1);
            assert(tk[i as int].post(outs@[i as int]));
            lemma_range_at(n as int, parts as int, i as int, i as int + 1);
            if dense_on(codes@, bases@, d.bs as int, 0, b) {
                assert(dense_on(codes@, bases@, d.bs as int, 0, a));
                assert(dense_on(codes@, bases@, d.bs as int, a, b));
            }
            if dense_on(codes@, bases@, d.bs as int, 0, a) && dense_on(codes@, bases@, d.bs as int, a, b) {
                assert forall|c: int| 0 <= c < b implies #[trigger] fv32(codes@, bases@, d.bs as int, c) == c + 1 by {
                    if c < a {
                    } else {
                    }
                }
            }
        }
        ok = ok && outs[i];
        i = i + 1;
    }
    proof {
        lemma_range_at(n as int, parts as int, 0, parts as int);
    }
    Ok(ok)
}

} // verus!
