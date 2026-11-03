//! The two parallel passes over the customer rows (`no_unwind` worker bodies over `StoredParts` extents).
//! - readers: the group of a row (`row_gid`: the end of the first two characters of c_phone, then the lookup table
//!   of two-byte codes or a comparison with every parameter), the absence of orders of a key (`no_orders`);
//! - `TaskA` (pass A): count and sum of the balances of the rows entering the AVG subquery, over `[lo, hi)`;
//! - `TaskB` (pass B): per group, count and sum of the balances of the result rows over `[lo, hi)`, with the
//!   average as an integer coefficient threshold (`thr_ok`);
//! - `run_a` / `run_b`: one task per chunk of `bounds`, joined and merged on the calling thread.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::put;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::numeric::*;
use crate::stores::custpart::interface::common::colfmt::text_of;
use super::common::sub2::*;
use super::model::*;

verus! {

// ------------------------------------------------------------------------------------------------ chunks

/// `k` chunks `[b[t], b[t + 1])` covering `[0, n)` in order.
pub open spec fn bounds_ok(b: Seq<usize>, k: int, n: int) -> bool {
    &&& b.len() == k + 1
    &&& b[0] == 0
    &&& b[k] == n
    &&& forall|t: int| 0 <= t < k ==> #[trigger] b[t] <= b[t + 1]
}

/// `k` chunk bounds over `n` rows (about equal sizes).
pub fn make_bounds(n: usize, k: usize) -> (b: Vec<usize>)
    requires k >= 1,
    ensures bounds_ok(b@, k as int, n as int),
{
    let chunk = if n / k < usize::MAX { n / k + 1 } else { n / k };
    let mut b: Vec<usize> = Vec::new();
    b.push(0);
    let mut cur: usize = 0;
    let mut t: usize = 1;
    while t < k
        invariant
            1 <= t <= k,
            b@.len() == t,
            b@[0] == 0,
            cur == b@[t - 1],
            cur <= n,
            forall|s: int| 0 <= s < t - 1 ==> #[trigger] b@[s] <= b@[s + 1],
        decreases k - t,
    {
        cur = if n - cur > chunk { cur + chunk } else { n };
        b.push(cur);
        t = t + 1;
    }
    b.push(n);
    b
}

/// Chunk bounds lie inside `[0, n]`.
pub proof fn lemma_bounds_le(b: Seq<usize>, k: int, n: int, t: int)
    requires bounds_ok(b, k, n), 0 <= t < k,
    ensures 0 <= b[t] <= b[t + 1] <= n,
    decreases k - t,
{
    if t + 1 < k {
        lemma_bounds_le(b, k, n, t + 1);
    }
}

// ------------------------------------------------------------------------------------------------ readers

/// The lookup table of two-byte country codes: entry `256 x + y` is the group of the code `[x, y]`.
pub open spec fn table_ok(t: Seq<u8>, ps: Seq<Literal>) -> bool {
    &&& t.len() == 65536
    &&& forall|x: int| 0 <= x < 65536 ==> #[trigger] t[x] as int == gid(ps, seq![(x / 256) as u8, (x % 256) as u8])
}

/// The parameter texts as slices with their lengths.
pub open spec fn pats_ok(pats: Seq<&'static [u8]>, plens: Seq<usize>, ps: Seq<Literal>) -> bool {
    &&& pats.len() == 7
    &&& plens.len() == 7
    &&& forall|k: int| 0 <= k < 7 ==> (#[trigger] pats[k])@ == ptext(ps, k) && plens[k] == ptext(ps, k).len()
}

/// Skipping slots that do not hold `t`.
pub proof fn lemma_gid_skip(ps: Seq<Literal>, k: int, t: Seq<u8>)
    requires 0 <= k < 7, ptext(ps, k) != t,
    ensures gid_from(ps, k, t) == gid_from(ps, k + 1, t),
{
}

/// The group is a slot holding the code, or `NG`.
pub proof fn lemma_gid_range(ps: Seq<Literal>, k: int, t: Seq<u8>)
    requires 0 <= k <= 7,
    ensures
        k <= gid_from(ps, k, t) <= 7,
        gid_from(ps, k, t) < 7 ==> ptext(ps, gid_from(ps, k, t)) == t,
        forall|j: int| k <= j < gid_from(ps, k, t) ==> #[trigger] ptext(ps, j) != t,
    decreases 7 - k,
{
    if k < 7 && ptext(ps, k) != t {
        lemma_gid_range(ps, k + 1, t);
    }
}

/// `x[xs .. xs + len] == y` (`len` is `y`'s length).
fn bytes_eq_at(x: &[u8], xs: usize, y: &[u8], len: usize) -> (r: bool)
    requires xs + len <= x@.len(), xs + len <= usize::MAX, len == y@.len(),
    ensures r == (x@.subrange(xs as int, xs + len) == y@),
    no_unwind
{
    let mut j: usize = 0;
    while j < len
        invariant
            j <= len,
            xs + len <= x@.len(),
            xs + len <= usize::MAX,
            len == y@.len(),
            forall|m: int| 0 <= m < j ==> #[trigger] x@[xs + m] == y@[m],
        decreases len - j,
    {
        if x[xs + j] != y[j] {
            proof {
                assert(x@.subrange(xs as int, xs + len)[j as int] == x@[xs + j]);
            }
            return false;
        }
        j = j + 1;
    }
    proof {
        let xr = x@.subrange(xs as int, xs + len);
        assert forall|m: int| 0 <= m < len implies xr[m] == y@[m] by {
            assert(xr[m] == x@[xs + m]);
        }
        assert(xr =~= y@);
    }
    true
}

/// The group of the code `bytes[s .. s + len]` by comparison with every parameter.
fn slow_gid(bytes: &[u8], s: usize, len: usize, pats: &Vec<&'static [u8]>, plens: &Vec<usize>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (g: usize)
    requires
        s + len <= bytes@.len(),
        s + len <= usize::MAX,
        pats_ok(pats@, plens@, ps),
    ensures g == gid(ps, bytes@.subrange(s as int, s + len)),
    no_unwind
{
    let ghost t = bytes@.subrange(s as int, s + len);
    let mut k: usize = 0;
    while k < 7
        invariant
            k <= 7,
            s + len <= bytes@.len(),
            s + len <= usize::MAX,
            t == bytes@.subrange(s as int, s + len),
            pats_ok(pats@, plens@, ps),
            gid(ps, t) == gid_from(ps, k as int, t),
        decreases 7 - k,
    {
        let p: &'static [u8] = pats[k];
        proof {
            assert(p == pats@[k as int]);
            assert(p@ == ptext(ps, k as int) && plens@[k as int] == ptext(ps, k as int).len());
        }
        if plens[k] == len {
            if bytes_eq_at(bytes, s, p, len) {
                proof {
                    assert(gid_from(ps, k as int, t) == k);
                }
                return k;
            }
        }
        proof {
            assert(ptext(ps, k as int) != t);
            lemma_gid_skip(ps, k as int, t);
        }
        k = k + 1;
    }
    7
}

/// The group of row `i`'s country code.
pub fn row_gid(poffs: &[u64], pbytes: &[u8], i: usize, table: &Vec<u8>, pats: &Vec<&'static [u8]>, plens: &Vec<usize>,
    Ghost(v): Ghost<Cv>) -> (g: usize)
    requires
        cv_ok(v),
        v.poffs == poffs@,
        v.pbytes == pbytes@,
        0 <= i < v.n,
        table_ok(table@, v.ps),
        pats_ok(pats@, plens@, v.ps),
    ensures g == rgid(v, i as int), g <= 7,
    no_unwind
{
    let s = poffs[i] as usize;
    let e = poffs[i + 1] as usize;
    let ghost b = pbytes@.subrange(s as int, e as int);
    assert(b == rtext(v, i as int));
    let p2 = sub2_end_exec(pbytes, s, e);
    proof {
        lemma_sub2(b);
        lemma_gid_range(v.ps, 0, sub2(b));
    }
    if p2 == 2 {
        let x0 = pbytes[s];
        let x1 = pbytes[s + 1];
        let key = (x0 as usize) * 256 + (x1 as usize);
        proof {
            assert(sub2(b) =~= seq![x0, x1]);
            assert((key as int) / 256 == x0 as int) by (nonlinear_arith) requires key as int == x0 as int * 256 + x1 as int, 0 <= x1 < 256;
            assert((key as int) % 256 == x1 as int) by (nonlinear_arith) requires key as int == x0 as int * 256 + x1 as int, 0 <= x1 < 256;
            assert(((key as int) / 256) as u8 == x0);
            assert(((key as int) % 256) as u8 == x1);
            assert(table@[key as int] as int == gid(v.ps, seq![x0, x1]));
        }
        table[key] as usize
    } else {
        proof {
            assert(sub2(b) =~= pbytes@.subrange(s as int, s + p2));
        }
        slow_gid(pbytes, s, p2, pats, plens, Ghost(v.ps))
    }
}

/// No orders row has o_custkey `key` (directory entry, or every stored key in fallback mode).
pub fn no_orders(key: i64, dir: bool, kmin: i64, offs: &[u32], nk: usize, keys: &[i64], n_o: usize, Ghost(v): Ghost<Cv>)
    -> (r: bool)
    requires
        cv_ok(v),
        v.dir == dir, v.kmin == kmin, v.offs == offs@, v.nk == nk, v.keys == keys@, v.n_o == n_o,
    ensures r == noord_key(v, key as int),
    no_unwind
{
    if dir {
        let e: i128 = (key as i128) - (kmin as i128);
        if 0 <= e && e < nk as i128 {
            let eu = e as usize;
            offs[eu + 1] == offs[eu]
        } else {
            true
        }
    } else {
        let mut r: usize = 0;
        while r < n_o
            invariant
                r <= n_o,
                cv_ok(v), v.dir == dir, v.keys == keys@, v.n_o == n_o, !dir,
                forall|q: int| 0 <= q < r ==> #[trigger] keys@[q] != key,
            decreases n_o - r,
        {
            if keys[r] == key {
                return false;
            }
            r = r + 1;
        }
        true
    }
}

// ------------------------------------------------------------------------------------------------ pass A

/// One pass A task over the rows `[lo, hi)`.
pub struct TaskA {
    pub poffs: &'static [u64],
    pub pbytes: &'static [u8],
    pub ac: &'static [u32],
    pub ab: &'static [i64],
    pub bs: usize,
    pub lo: usize,
    pub hi: usize,
    pub table: Arc<Vec<u8>>,
    pub pats: Arc<Vec<&'static [u8]>>,
    pub plens: Arc<Vec<usize>>,
    pub v: Ghost<Cv>,
}

/// The shared views a task reads.
pub open spec fn views_a(t: TaskA) -> bool {
    let v = t.v@;
    &&& cv_ok(v)
    &&& v.poffs == t.poffs@ && v.pbytes == t.pbytes@ && v.ac == t.ac@ && v.ab == t.ab@ && v.bs == t.bs as int
    &&& t.lo <= t.hi <= v.n
    &&& table_ok(t.table@, v.ps)
    &&& pats_ok(t.pats@, t.plens@, v.ps)
}

impl WorkerTask for TaskA {
    type Output = (i128, u64);

    open spec fn pre(&self) -> bool {
        views_a(*self)
    }

    open spec fn post(&self, out: (i128, u64)) -> bool {
        &&& out.0 == suma(self.v@, self.lo as int, self.hi as int)
        &&& out.1 == cnta(self.v@, self.lo as int, self.hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: (i128, u64)) {
        let ghost task = self;
        let ghost v = self.v@;
        let TaskA { poffs, pbytes, ac, ab, bs, lo, hi, table, pats, plens, v: gv } = self;
        let mut sum: i128 = 0;
        let mut cnt: u64 = 0;
        let mut i = lo;
        while i < hi
            invariant
                views_a(task), v == task.v@,
                poffs == task.poffs, pbytes == task.pbytes, ac == task.ac, ab == task.ab, bs == task.bs,
                lo == task.lo, hi == task.hi, table@ == task.table@, pats@ == task.pats@, plens@ == task.plens@,
                lo <= i <= hi,
                sum == suma(v, lo as int, i as int),
                cnt == cnta(v, lo as int, i as int),
            decreases hi - i,
        {
            proof {
                lemma_a_bound(v, lo as int, i as int);
                assert(cnt <= i - lo);
            }
            let g = row_gid(poffs, pbytes, i, &*table, &*pats, &*plens, Ghost(v));
            if g < 7 {
                assert(-acct_bound() < racct(v, i as int) < acct_bound());
                let a: i64 = ab[i / bs] + ac[i] as i64;
                if a > 0 {
                    proof {
                        let c = cnt as int;
                        assert(c * acct_bound() <= 0x1_0000_0000_0000_0000 * acct_bound()) by (nonlinear_arith)
                            requires 0 <= c <= 0x1_0000_0000_0000_0000;
                    }
                    sum = sum + a as i128;
                    cnt = cnt + 1;
                }
            }
            i = i + 1;
        }
        (sum, cnt)
    }
}

/// Pass A over the chunks of `bounds`: the count and sum of the subquery's rows over `[0, n)`.
pub fn run_a(poffs: &'static [u64], pbytes: &'static [u8], ac: &'static [u32], ab: &'static [i64], bs: usize,
    table: &Arc<Vec<u8>>, pats: &Arc<Vec<&'static [u8]>>, plens: &Arc<Vec<usize>>, bounds: &Vec<usize>, k: usize,
    dispatch: &mut Dispatch, Ghost(v): Ghost<Cv>) -> (r: Result<(i128, u64), WorkerFailure>)
    requires
        1 <= k <= MAX_WORKERS,
        bounds_ok(bounds@, k as int, v.n),
        cv_ok(v),
        v.poffs == poffs@ && v.pbytes == pbytes@ && v.ac == ac@ && v.ab == ab@ && v.bs == bs as int,
        table_ok(table@, v.ps),
        pats_ok(pats@, plens@, v.ps),
    ensures
        r matches Ok(o) ==> o.0 == suma(v, 0, v.n) && o.1 == cnta(v, 0, v.n),
{
    let mut tasks: Vec<TaskA> = Vec::new();
    let mut t: usize = 0;
    while t < k
        invariant
            1 <= k <= MAX_WORKERS,
            bounds_ok(bounds@, k as int, v.n),
            cv_ok(v),
            v.poffs == poffs@ && v.pbytes == pbytes@ && v.ac == ac@ && v.ab == ab@ && v.bs == bs as int,
            table_ok(table@, v.ps),
            pats_ok(pats@, plens@, v.ps),
            t <= k,
            tasks@.len() == t,
            forall|s: int| 0 <= s < t ==> #[trigger] tasks@[s].pre(),
            forall|s: int| 0 <= s < t ==> (#[trigger] tasks@[s]).v@ == v && tasks@[s].lo == bounds@[s]
                && tasks@[s].hi == bounds@[s + 1],
        decreases k - t,
    {
        proof {
            lemma_bounds_le(bounds@, k as int, v.n, t as int);
        }
        let task = TaskA {
            poffs, pbytes, ac, ab, bs, lo: bounds[t], hi: bounds[t + 1], table: table.clone(), pats: pats.clone(),
            plens: plens.clone(), v: Ghost(v),
        };
        tasks.push(task);
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(f) => return Err(f),
    };
    let mut sum: i128 = 0;
    let mut cnt: u64 = 0;
    let mut t: usize = 0;
    while t < k
        invariant
            t <= k,
            outs@.len() == k,
            tv.len() == k,
            cv_ok(v),
            bounds_ok(bounds@, k as int, v.n),
            forall|s: int| 0 <= s < k ==> #[trigger] tv[s].post(outs@[s]),
            forall|s: int| 0 <= s < k ==> (#[trigger] tv[s]).v@ == v && tv[s].lo == bounds@[s] && tv[s].hi == bounds@[s + 1],
            sum == suma(v, 0, bounds@[t as int] as int),
            cnt == cnta(v, 0, bounds@[t as int] as int),
        decreases k - t,
    {
        proof {
            lemma_bounds_le(bounds@, k as int, v.n, t as int);
            let (a, b) = (bounds@[t as int] as int, bounds@[t + 1] as int);
            assert(tv[t as int].post(outs@[t as int]));
            lemma_a_split(v, 0, a, b);
            lemma_a_bound(v, 0, b);
            lemma_a_bound(v, 0, a);
            lemma_a_bound(v, a, b);
            assert(cnta(v, 0, b) <= v.n);
            assert(v.n <= v.poffs.len());
            let c = cnta(v, 0, b) as int;
            assert(c * acct_bound() <= 0x1_0000_0000_0000_0000 * acct_bound()) by (nonlinear_arith)
                requires 0 <= c <= 0x1_0000_0000_0000_0000;
        }
        let (s, c) = outs[t];
        sum = sum + s;
        cnt = cnt + c;
        t = t + 1;
    }
    Ok((sum, cnt))
}

// ------------------------------------------------------------------------------------------------ pass B

/// `thr` is the coefficient threshold of `a > avg` on the balances.
pub open spec fn thr_ok(thr: i128, avg: Val) -> bool {
    forall|a: int| -acct_bound() < a < acct_bound() ==> #[trigger] gt_avg(a, avg) == (a > thr)
}

/// One pass B task over the rows `[lo, hi)`.
pub struct TaskB {
    pub poffs: &'static [u64],
    pub pbytes: &'static [u8],
    pub ac: &'static [u32],
    pub ab: &'static [i64],
    pub kc: &'static [u32],
    pub kb: &'static [i64],
    pub bs: usize,
    pub lo: usize,
    pub hi: usize,
    pub table: Arc<Vec<u8>>,
    pub pats: Arc<Vec<&'static [u8]>>,
    pub plens: Arc<Vec<usize>>,
    pub dir: bool,
    pub kmin: i64,
    pub offs: &'static [u32],
    pub nk: usize,
    pub keys: &'static [i64],
    pub n_o: usize,
    pub thr: i128,
    pub cnts: Vec<u64>,
    pub sums: Vec<i128>,
    pub v: Ghost<Cv>,
    pub avg: Ghost<Val>,
}

/// The shared views a task reads.
pub open spec fn views_b(t: TaskB) -> bool {
    let v = t.v@;
    &&& cv_ok(v)
    &&& v.poffs == t.poffs@ && v.pbytes == t.pbytes@ && v.ac == t.ac@ && v.ab == t.ab@ && v.bs == t.bs as int
    &&& v.kc == t.kc@ && v.kb == t.kb@
    &&& v.dir == t.dir && v.kmin == t.kmin && v.offs == t.offs@ && v.nk == t.nk && v.keys == t.keys@ && v.n_o == t.n_o
    &&& t.lo <= t.hi <= v.n
    &&& table_ok(t.table@, v.ps)
    &&& pats_ok(t.pats@, t.plens@, v.ps)
    &&& thr_ok(t.thr, t.avg@)
}

/// Per group: count and sum of the result rows of `[lo, hi)`.
pub open spec fn post_b(v: Cv, avg: Val, lo: int, hi: int, cnts: Seq<u64>, sums: Seq<i128>) -> bool {
    &&& cnts.len() == 7
    &&& sums.len() == 7
    &&& forall|k: int| 0 <= k < 7 ==> #[trigger] cnts[k] == cntb(v, avg, k, lo, hi) && sums[k] == sumb(v, avg, k, lo, hi)
}

impl WorkerTask for TaskB {
    type Output = (Vec<u64>, Vec<i128>);

    open spec fn pre(&self) -> bool {
        &&& views_b(*self)
        &&& post_b(self.v@, self.avg@, self.lo as int, self.lo as int, self.cnts@, self.sums@)
    }

    open spec fn post(&self, out: (Vec<u64>, Vec<i128>)) -> bool {
        post_b(self.v@, self.avg@, self.lo as int, self.hi as int, out.0@, out.1@)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: (Vec<u64>, Vec<i128>)) {
        let ghost task = self;
        let ghost v = self.v@;
        let ghost avg = self.avg@;
        let TaskB {
            poffs, pbytes, ac, ab, kc, kb, bs, lo, hi, table, pats, plens, dir, kmin, offs, nk, keys, n_o, thr, cnts,
            sums, v: gv, avg: ga,
        } = self;
        let mut cnts = cnts;
        let mut sums = sums;
        let mut i = lo;
        while i < hi
            invariant
                views_b(task), v == task.v@, avg == task.avg@,
                poffs == task.poffs, pbytes == task.pbytes, ac == task.ac, ab == task.ab, kc == task.kc,
                kb == task.kb, bs == task.bs, lo == task.lo, hi == task.hi, table@ == task.table@,
                pats@ == task.pats@, plens@ == task.plens@, dir == task.dir, kmin == task.kmin, offs == task.offs,
                nk == task.nk, keys == task.keys, n_o == task.n_o, thr == task.thr,
                lo <= i <= hi,
                post_b(v, avg, lo as int, i as int, cnts@, sums@),
            decreases hi - i,
        {
            let ghost (c0, s0) = (cnts@, sums@);
            let g = row_gid(poffs, pbytes, i, &*table, &*pats, &*plens, Ghost(v));
            let mut hitk: bool = false;
            if g < 7 {
                assert(-acct_bound() < racct(v, i as int) < acct_bound());
                let a: i64 = ab[i / bs] + ac[i] as i64;
                assert(gt_avg(a as int, avg) == (a > thr));
                if a as i128 > thr {
                    assert(i64::MIN <= rkey(v, i as int) <= i64::MAX);
                    let key: i64 = kb[i / bs] + kc[i] as i64;
                    if no_orders(key, dir, kmin, offs, nk, keys, n_o, Ghost(v)) {
                        proof {
                            lemma_b_bound(v, avg, g as int, lo as int, i as int);
                            let c = cnts@[g as int] as int;
                            assert(c <= i - lo);
                            assert(c * acct_bound() <= 0x1_0000_0000_0000_0000 * acct_bound()) by (nonlinear_arith)
                                requires 0 <= c <= 0x1_0000_0000_0000_0000;
                        }
                        let nc = cnts[g] + 1;
                        let ns = sums[g] + a as i128;
                        put(&mut cnts, g, nc);
                        put(&mut sums, g, ns);
                        hitk = true;
                    }
                }
            }
            proof {
                assert(qb(v, avg, i as int) == hitk);
                assert forall|k: int| 0 <= k < 7 implies #[trigger] cnts@[k] == cntb(v, avg, k, lo as int, i + 1)
                    && sums@[k] == sumb(v, avg, k, lo as int, i + 1) by {
                    assert(cntb(v, avg, k, lo as int, i + 1) == cntb(v, avg, k, lo as int, i as int)
                        + if qb(v, avg, i as int) && rgid(v, i as int) == k { 1nat } else { 0nat });
                    assert(c0[k] == cntb(v, avg, k, lo as int, i as int));
                    assert(s0[k] == sumb(v, avg, k, lo as int, i as int));
                }
            }
            i = i + 1;
        }
        (cnts, sums)
    }
}

/// Pass B over the chunks of `bounds`: per group, the count and sum of the result rows over `[0, n)`.
pub fn run_b(poffs: &'static [u64], pbytes: &'static [u8], ac: &'static [u32], ab: &'static [i64], kc: &'static [u32],
    kb: &'static [i64], bs: usize, table: &Arc<Vec<u8>>, pats: &Arc<Vec<&'static [u8]>>, plens: &Arc<Vec<usize>>,
    dir: bool, kmin: i64, offs: &'static [u32], nk: usize, keys: &'static [i64], n_o: usize, thr: i128,
    bounds: &Vec<usize>, k: usize, dispatch: &mut Dispatch, Ghost(v): Ghost<Cv>, Ghost(avg): Ghost<Val>)
    -> (r: Result<(Vec<u64>, Vec<i128>), WorkerFailure>)
    requires
        1 <= k <= MAX_WORKERS,
        bounds_ok(bounds@, k as int, v.n),
        cv_ok(v),
        v.poffs == poffs@ && v.pbytes == pbytes@ && v.ac == ac@ && v.ab == ab@ && v.bs == bs as int,
        v.kc == kc@ && v.kb == kb@,
        v.dir == dir && v.kmin == kmin && v.offs == offs@ && v.nk == nk && v.keys == keys@ && v.n_o == n_o,
        table_ok(table@, v.ps),
        pats_ok(pats@, plens@, v.ps),
        thr_ok(thr, avg),
    ensures
        r matches Ok(o) ==> post_b(v, avg, 0, v.n, o.0@, o.1@),
{
    let mut tasks: Vec<TaskB> = Vec::new();
    let mut t: usize = 0;
    while t < k
        invariant
            1 <= k <= MAX_WORKERS,
            bounds_ok(bounds@, k as int, v.n),
            cv_ok(v),
            v.poffs == poffs@ && v.pbytes == pbytes@ && v.ac == ac@ && v.ab == ab@ && v.bs == bs as int,
            v.kc == kc@ && v.kb == kb@,
            v.dir == dir && v.kmin == kmin && v.offs == offs@ && v.nk == nk && v.keys == keys@ && v.n_o == n_o,
            table_ok(table@, v.ps),
            pats_ok(pats@, plens@, v.ps),
            thr_ok(thr, avg),
            t <= k,
            tasks@.len() == t,
            forall|s: int| 0 <= s < t ==> #[trigger] tasks@[s].pre(),
            forall|s: int| 0 <= s < t ==> (#[trigger] tasks@[s]).v@ == v && tasks@[s].avg@ == avg
                && tasks@[s].lo == bounds@[s] && tasks@[s].hi == bounds@[s + 1],
        decreases k - t,
    {
        proof {
            lemma_bounds_le(bounds@, k as int, v.n, t as int);
        }
        let lo = bounds[t];
        let cnts: Vec<u64> = vec![0u64; 7];
        let sums: Vec<i128> = vec![0i128; 7];
        let task = TaskB {
            poffs, pbytes, ac, ab, kc, kb, bs, lo, hi: bounds[t + 1], table: table.clone(), pats: pats.clone(),
            plens: plens.clone(), dir, kmin, offs, nk, keys, n_o, thr, cnts, sums, v: Ghost(v), avg: Ghost(avg),
        };
        proof {
            assert forall|kk: int| 0 <= kk < 7 implies #[trigger] task.cnts@[kk] == cntb(v, avg, kk, lo as int, lo as int)
                && task.sums@[kk] == sumb(v, avg, kk, lo as int, lo as int) by {}
        }
        tasks.push(task);
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(f) => return Err(f),
    };
    let mut cnts: Vec<u64> = vec![0u64; 7];
    let mut sums: Vec<i128> = vec![0i128; 7];
    let mut t: usize = 0;
    while t < k
        invariant
            t <= k,
            outs@.len() == k,
            tv.len() == k,
            cv_ok(v),
            bounds_ok(bounds@, k as int, v.n),
            forall|s: int| 0 <= s < k ==> #[trigger] tv[s].post(outs@[s]),
            forall|s: int| 0 <= s < k ==> (#[trigger] tv[s]).v@ == v && tv[s].avg@ == avg && tv[s].lo == bounds@[s]
                && tv[s].hi == bounds@[s + 1],
            post_b(v, avg, 0, bounds@[t as int] as int, cnts@, sums@),
        decreases k - t,
    {
        proof {
            lemma_bounds_le(bounds@, k as int, v.n, t as int);
        }
        let ghost (a, b) = (bounds@[t as int] as int, bounds@[t + 1] as int);
        assert(tv[t as int].post(outs@[t as int]));
        let ghost (c0, s0) = (cnts@, sums@);
        let mut g: usize = 0;
        while g < 7
            invariant
                g <= 7,
                t < k,
                outs@.len() == k,
                cv_ok(v),
                0 <= a <= b <= v.n,
                post_b(v, avg, a, b, outs@[t as int].0@, outs@[t as int].1@),
                post_b(v, avg, 0, a, c0, s0),
                cnts@.len() == 7, sums@.len() == 7,
                forall|kk: int| g <= kk < 7 ==> #[trigger] cnts@[kk] == c0[kk] && sums@[kk] == s0[kk],
                forall|kk: int| 0 <= kk < g ==> #[trigger] cnts@[kk] == cntb(v, avg, kk, 0, b) && sums@[kk] == sumb(v, avg, kk, 0, b),
            decreases 7 - g,
        {
            proof {
                let kk = g as int;
                lemma_b_split(v, avg, kk, 0, a, b);
                lemma_b_bound(v, avg, kk, 0, b);
                assert(v.n <= v.poffs.len());
                let c = cntb(v, avg, kk, 0, b) as int;
                assert(c * acct_bound() <= 0x1_0000_0000_0000_0000 * acct_bound()) by (nonlinear_arith)
                    requires 0 <= c <= 0x1_0000_0000_0000_0000;
            }
            let nc = cnts[g] + outs[t].0[g];
            let ns = sums[g] + outs[t].1[g];
            cnts.set(g, nc);
            sums.set(g, ns);
            g = g + 1;
        }
        t = t + 1;
    }
    Ok((cnts, sums))
}

} // verus!
