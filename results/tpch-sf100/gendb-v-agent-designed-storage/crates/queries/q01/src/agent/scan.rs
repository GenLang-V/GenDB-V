//! The fast path's assembly: `s` worker tasks (`fast::FastTask`), task `k` taking blocks `k, k + s, k + 2s, ...`
//! (round-robin, so every task reads every region of the table and every memory node holding it), the task tables
//! added up (all tasks together are every block once: `stride::lemma_rsum_total`), and the entries of the non-empty
//! groups read off the dense table in dictionary order. A single task runs on the calling thread. Under the fast
//! path's bounds no sum's absolute mass can reach `i128` (`model::lemma_kabs_fast`), so every entry keeps its sums.
use vstd::prelude::*;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::filled;
use crate::link::expr::i128_max;
use super::model::*;
use super::fast::*;
use super::stride::*;
use super::finish::{Entry, entry_vals, entries_ok, eover, esum, key_lt};

verus! {

/// Task `tk` is task `k` of `s` over `q` rounds of the given slices.
pub open spec fn task_is(tk: FastTask, cols: Cols, n: usize, bsize: usize, nrf: usize, nls: usize, t: usize, p: i64,
    k: int, s: int, q: int) -> bool
{
    &&& tk.cols == cols && tk.n == n && tk.bsize == bsize && tk.nrf == nrf && tk.nls == nls && tk.t == t && tk.p == p
    &&& tk.k == k && tk.s == s && tk.q == q
}

/// The fast path's facts about the model of the slices.
pub open spec fn fast_ok(m: Model, nrf: int, nls: int, t: int, p: int) -> bool {
    &&& model_wf(m) && m.n <= u64::MAX && m.nb * m.bsize < m.n + m.bsize && m.n + m.bsize <= usize::MAX
    &&& m.nb * 64 <= usize::MAX
    &&& nrf == m.nrf && nls == m.nls && t == nrf * nls && t <= MAXT
    &&& forall|g: int| 0 <= g < m.nb ==> #[trigger] block_ok(m, g)
    &&& -0x8000_0000 <= p <= 0x7fff_ffff
}

/// Every row of the model lies in a block with `block_ok`.
proof fn lemma_all_rows_ok(m: Model, nrf: int, nls: int, t: int, p: int)
    requires fast_ok(m, nrf, nls, t, p),
    ensures forall|j: int| 0 <= j < m.n ==> #[trigger] block_ok(m, blk(m, j)),
{
    assert forall|j: int| 0 <= j < m.n implies #[trigger] block_ok(m, blk(m, j)) by {
        lemma_blk(m, j);
    }
}

/// Task `k`'s table added to the tables of tasks `0 .. k`: the tables of tasks `0 .. k + 1`.
fn merge_task(total_cnt: &mut Vec<u64>, total_sum: &mut Vec<i128>, out: &FastOut, t: usize, Ghost(m): Ghost<Model>,
    Ghost(p): Ghost<int>, Ghost(k): Ghost<int>, Ghost(s): Ghost<int>, Ghost(q): Ghost<int>)
    requires
        model_wf(m), m.n <= u64::MAX, t <= MAXT, 0 <= k < s <= 64, 0 <= q, q * s >= m.nb,
        q * m.bsize <= 0x1_0000_0000_0000_0000,
        forall|j: int| 0 <= j < m.n ==> #[trigger] block_ok(m, blk(m, j)),
        old(total_cnt)@.len() == t, old(total_sum)@.len() == 5 * t, out.cnt@.len() == t, out.sum@.len() == 5 * t,
        forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 ==> #[trigger] tval(old(total_cnt)@, old(total_sum)@, i, w)
            == rsum(m, p, i, w, k, s, q),
        forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 ==> #[trigger] tval(out.cnt@, out.sum@, i, w)
            == ssum(m, p, i, w, k, s, q),
    ensures
        final(total_cnt)@.len() == t, final(total_sum)@.len() == 5 * t,
        forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 ==> #[trigger] tval(final(total_cnt)@, final(total_sum)@, i, w)
            == rsum(m, p, i, w, k + 1, s, q),
{
    let ghost t0 = t as int;
    let mut i: usize = 0;
    while i < t
        invariant
            model_wf(m), m.n <= u64::MAX, t <= MAXT, 0 <= k < s <= 64, 0 <= q, q * s >= m.nb, i <= t, t0 == t,
            q * m.bsize <= 0x1_0000_0000_0000_0000,
            forall|j: int| 0 <= j < m.n ==> #[trigger] block_ok(m, blk(m, j)),
            out.cnt@.len() == t, out.sum@.len() == 5 * t,
            forall|i2: int, w: int| 0 <= i2 < t && 0 <= w <= 5 ==> #[trigger] tval(out.cnt@, out.sum@, i2, w)
                == ssum(m, p, i2, w, k, s, q),
            total_cnt@.len() == t && total_sum@.len() == 5 * t,
            forall|i2: int, w: int| 0 <= i2 < t && 0 <= w <= 5 ==> #[trigger] tval(total_cnt@, total_sum@, i2, w)
                == rsum(m, p, i2, w, k, s, q) + if i2 < i { ssum(m, p, i2, w, k, s, q) } else { 0 },
        decreases t - i,
    {
        let ghost ii = i as int;
        proof {
            assert(i * 5 + 4 < 5 * t) by (nonlinear_arith) requires i < t;
            // every partial sum stays inside i128 (at most 64 tasks of at most q blocks) and the counts inside u64
            assert forall|w: int| 0 <= w < 5 implies -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
                <= #[trigger] rsum(m, p, ii, w, k + 1, s, q) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff by {
                lemma_rsum_bound(m, p, ii, w, k + 1, s, q);
                assert(vbound(w) <= 0x4_0000_0000_0000);
                assert((k + 1) * (q * m.bsize * vbound(w)) <= 64 * (0x1_0000_0000_0000_0000 * 0x4_0000_0000_0000))
                    by (nonlinear_arith) requires 0 <= k + 1 <= 64, 0 <= q * m.bsize <= 0x1_0000_0000_0000_0000,
                    0 <= vbound(w) <= 0x4_0000_0000_0000, q * m.bsize * vbound(w) == (q * m.bsize) * vbound(w);
            }
            lemma_rsum_bound(m, p, ii, 5, k + 1, s, q);
            lemma_rsum_count_mono(m, p, ii, k + 1, s, s, q);
            lemma_rsum_total(m, p, ii, 5, s, q);
            lemma_isum_bound(m, p, ii, 5, 0, m.n);
            assert(tval(total_cnt@, total_sum@, ii, 5) == rsum(m, p, ii, 5, k, s, q));
            assert(tval(out.cnt@, out.sum@, ii, 5) == ssum(m, p, ii, 5, k, s, q));
            assert forall|w: int| 0 <= w < 5 implies -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
                <= #[trigger] (total_sum@[ii * 5 + w] + out.sum@[ii * 5 + w]) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff by {
                assert(tval(total_cnt@, total_sum@, ii, w) == rsum(m, p, ii, w, k, s, q));
                assert(tval(out.cnt@, out.sum@, ii, w) == ssum(m, p, ii, w, k, s, q));
                assert(rsum(m, p, ii, w, k + 1, s, q) == rsum(m, p, ii, w, k, s, q) + ssum(m, p, ii, w, k, s, q));
            }
        }
        let ghost (oc, os) = (total_cnt@, total_sum@);
        proof {
            let bi = i * 5;
            assert(-0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff <= total_sum@[bi + 0] + out.sum@[bi + 0] <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff);
            assert(-0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff <= total_sum@[bi + 1] + out.sum@[bi + 1] <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff);
            assert(-0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff <= total_sum@[bi + 2] + out.sum@[bi + 2] <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff);
            assert(-0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff <= total_sum@[bi + 3] + out.sum@[bi + 3] <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff);
            assert(-0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff <= total_sum@[bi + 4] + out.sum@[bi + 4] <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff);
            assert(bi + 0 == bi);
            assert(total_cnt@[ii] as int + out.cnt@[ii] as int <= u64::MAX);
        }
        let b = i * NSUMS;
        total_cnt.set(i, total_cnt[i] + out.cnt[i]);
        total_sum.set(b, total_sum[b] + out.sum[b]);
        total_sum.set(b + 1, total_sum[b + 1] + out.sum[b + 1]);
        total_sum.set(b + 2, total_sum[b + 2] + out.sum[b + 2]);
        total_sum.set(b + 3, total_sum[b + 3] + out.sum[b + 3]);
        total_sum.set(b + 4, total_sum[b + 4] + out.sum[b + 4]);
        proof {
            assert forall|i2: int, w: int| 0 <= i2 < t && 0 <= w <= 5 implies #[trigger] tval(total_cnt@, total_sum@, i2, w)
                == rsum(m, p, i2, w, k, s, q) + if i2 < i + 1 { ssum(m, p, i2, w, k, s, q) } else { 0 } by {
                assert(tval(oc, os, i2, w) == rsum(m, p, i2, w, k, s, q) + if i2 < i { ssum(m, p, i2, w, k, s, q) } else { 0 });
                if w < 5 {
                    if i2 != i {
                        assert(i2 * 5 + w != b && i2 * 5 + w != b + 1 && i2 * 5 + w != b + 2 && i2 * 5 + w != b + 3 && i2 * 5 + w != b + 4)
                            by (nonlinear_arith) requires i2 != i, 0 <= w < 5, b == i * 5;
                    } else {
                        assert(tval(out.cnt@, out.sum@, i2, w) == ssum(m, p, i2, w, k, s, q));
                    }
                } else if i2 == i {
                    assert(tval(out.cnt@, out.sum@, i2, 5) == ssum(m, p, i2, 5, k, s, q));
                }
            }
        }
        i = i + 1;
    }
}

/// The table of all `n` stored rows, scanned by up to `workers` tasks, task `k` taking blocks `k, k + s, ...`
/// (one task runs on the calling thread).
pub fn fast_table(cols: Cols, n: usize, bsize: usize, nrf: usize, nls: usize, t: usize, p: i64, workers: usize,
    dispatch: &mut Dispatch, Ghost(m): Ghost<Model>) -> (r: Result<(Vec<u64>, Vec<i128>), WorkerFailure>)
    requires
        fast_ok(m, nrf as int, nls as int, t as int, p as int),
        m == cols_model(cols, m.n, m.bsize, m.nrf, m.nls), n == m.n, bsize == m.bsize,
        1 <= workers <= MAX_WORKERS, masks_hold(cols),
    ensures r matches Ok(tb) ==> tbl_ok(tb.0@, tb.1@, m, p as int, 0, m.n, t as int),
{
    let ng = cols.qty_b.len();
    let ntasks: usize = if workers < ng { workers } else if ng == 0 { 1 } else { ng };
    // rounds: every task runs `q` rounds, `q * ntasks >= ng`
    let q: usize = (ng + ntasks - 1) / ntasks;
    proof {
        lemma_all_rows_ok(m, nrf as int, nls as int, t as int, p as int);
        let (s, g) = (ntasks as int, ng as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(g + s - 1, s);
        let rem = (g + s - 1) % s;
        assert(g + s - 1 == s * q + rem && 0 <= rem < s);
        assert(q * s >= g) by (nonlinear_arith) requires g + s - 1 == s * q + rem, rem < s, q >= 0;
        assert(q * s <= g + s) by (nonlinear_arith) requires g + s - 1 == s * q + rem, rem >= 0;
        assert(q <= g) by (nonlinear_arith) requires g + s - 1 == s * q + rem, rem >= 0, s >= 1, q >= 0,
            g >= 1 || s == 1;
        assert(q * bsize <= g * bsize) by (nonlinear_arith) requires q <= g, bsize >= 1;
    }
    let mut tasks: Vec<FastTask> = Vec::new();
    let mut k: usize = 0;
    while k < ntasks
        invariant
            fast_ok(m, nrf as int, nls as int, t as int, p as int),
            m == cols_model(cols, m.n, m.bsize, m.nrf, m.nls), n == m.n, bsize == m.bsize, ng == m.nb,
            1 <= ntasks <= MAX_WORKERS, k <= ntasks, tasks@.len() == k, masks_hold(cols),
            q <= ng, q * ntasks <= ng + ntasks,
            forall|i: int| 0 <= i < k ==> #[trigger] tasks@[i].pre(),
            forall|i: int| 0 <= i < k ==> #[trigger] task_is(tasks@[i], cols, n, bsize, nrf, nls, t, p, i, ntasks as int, q as int),
        decreases ntasks - k,
    {
        let task = FastTask {
            cols, n, bsize, nrf, nls, t, k, s: ntasks, q, ng, p,
            out_cnt: filled(t, 0u64),
            out_sum: filled(t * NSUMS, 0i128),
            blk_cnt: filled(t, 0u64),
            blk_sum: filled(t * NSUMS, 0i128),
        };
        proof {
            assert(task.pre());
        }
        tasks.push(task);
        k = k + 1;
    }
    let ghost tv = tasks@;
    let outs = if ntasks == 1 {
        // one task: run it on the calling thread
        let mut tasks = tasks;
        let tk = tasks.pop().unwrap();
        proof {
            assert(tk == tv[0]);
        }
        let o = tk.run();
        let mut v: Vec<FastOut> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, tasks) {
            Ok(o) => o,
            Err(e) => return Err(e),
        }
    };
    let mut total_cnt: Vec<u64> = filled(t, 0u64);
    let mut total_sum: Vec<i128> = filled(t * NSUMS, 0i128);
    proof {
        assert forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 implies #[trigger] tval(total_cnt@, total_sum@, i, w)
            == rsum(m, p as int, i, w, 0, ntasks as int, q as int) by {
            if w < 5 {
                assert(0 <= i * 5 + w < 5 * t) by (nonlinear_arith) requires 0 <= i < t, 0 <= w < 5;
            }
        }
        assert(q * bsize <= 0x1_0000_0000_0000_0000);
    }
    let mut k: usize = 0;
    while k < ntasks
        invariant
            fast_ok(m, nrf as int, nls as int, t as int, p as int),
            m == cols_model(cols, m.n, m.bsize, m.nrf, m.nls), n == m.n, bsize == m.bsize, ng == m.nb,
            1 <= ntasks <= MAX_WORKERS, k <= ntasks, outs@.len() == ntasks, tv.len() == ntasks,
            q * ntasks >= ng, q * bsize <= 0x1_0000_0000_0000_0000,
            forall|j: int| 0 <= j < m.n ==> #[trigger] block_ok(m, blk(m, j)),
            forall|i: int| 0 <= i < ntasks ==> #[trigger] tv[i].post(outs@[i]),
            forall|i: int| 0 <= i < ntasks ==> #[trigger] task_is(tv[i], cols, n, bsize, nrf, nls, t, p, i, ntasks as int, q as int),
            total_cnt@.len() == t, total_sum@.len() == 5 * t,
            forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 ==> #[trigger] tval(total_cnt@, total_sum@, i, w)
                == rsum(m, p as int, i, w, k as int, ntasks as int, q as int),
        decreases ntasks - k,
    {
        proof {
            assert(tv[k as int].post(outs@[k as int]));
            assert(task_is(tv[k as int], cols, n, bsize, nrf, nls, t, p, k as int, ntasks as int, q as int));
        }
        merge_task(&mut total_cnt, &mut total_sum, &outs[k], t, Ghost(m), Ghost(p as int), Ghost(k as int),
            Ghost(ntasks as int), Ghost(q as int));
        k = k + 1;
    }
    proof {
        assert forall|i: int, w: int| 0 <= i < t && 0 <= w <= 5 implies #[trigger] tval(total_cnt@, total_sum@, i, w)
            == isum(m, p as int, i, w, 0, m.n) by {
            lemma_rsum_total(m, p as int, i, w, ntasks as int, q as int);
        }
    }
    Ok((total_cnt, total_sum))
}

/// The entries of the non-empty groups read off the table of all rows, in dictionary order.
pub fn table_entries(cnt: &Vec<u64>, sum: &Vec<i128>, nrf: usize, nls: usize, t: usize, Ghost(m): Ghost<Model>,
    Ghost(p): Ghost<int>) -> (es: Vec<Entry>)
    requires
        fast_ok(m, nrf as int, nls as int, t as int, p),
        tbl_ok(cnt@, sum@, m, p, 0, m.n, t as int),
    ensures entries_ok(es@, m, p),
{
    proof {
        lemma_all_rows_ok(m, nrf as int, nls as int, t as int, p);
    }
    let mut es: Vec<Entry> = Vec::new();
    let mut a: usize = 0;
    while a < nrf
        invariant
            fast_ok(m, nrf as int, nls as int, t as int, p),
            tbl_ok(cnt@, sum@, m, p, 0, m.n, t as int),
            forall|j: int| 0 <= j < m.n ==> #[trigger] block_ok(m, blk(m, j)),
            a <= nrf,
            forall|k: int| 0 <= k < es@.len() ==> {
                &&& #[trigger] es@[k].a < a && es@[k].b < m.nls && es@[k].cnt > 0
                &&& entry_vals(es@[k], m, p)
            },
            forall|k1: int, k2: int| 0 <= k1 < k2 < es@.len() ==> #[trigger] key_lt(es@[k1], es@[k2]),
            forall|a2: int, b2: int| 0 <= a2 < a && 0 <= b2 < m.nls && #[trigger] ksum(m, p, a2, b2, 5, 0, m.n) > 0
                ==> exists|k: int| 0 <= k < es@.len() && es@[k].a == a2 && es@[k].b == b2,
        decreases nrf - a,
    {
        let mut b: usize = 0;
        while b < nls
            invariant
                fast_ok(m, nrf as int, nls as int, t as int, p),
                tbl_ok(cnt@, sum@, m, p, 0, m.n, t as int),
                forall|j: int| 0 <= j < m.n ==> #[trigger] block_ok(m, blk(m, j)),
                a < nrf, b <= nls,
                forall|k: int| 0 <= k < es@.len() ==> {
                    &&& #[trigger] es@[k].a <= a && es@[k].b < m.nls && es@[k].cnt > 0
                    &&& entry_vals(es@[k], m, p)
                    &&& (es@[k].a < a || es@[k].b < b)
                },
                forall|k1: int, k2: int| 0 <= k1 < k2 < es@.len() ==> #[trigger] key_lt(es@[k1], es@[k2]),
                forall|a2: int, b2: int| ((0 <= a2 < a && 0 <= b2 < m.nls) || (a2 == a && 0 <= b2 < b))
                    && #[trigger] ksum(m, p, a2, b2, 5, 0, m.n) > 0
                    ==> exists|k: int| 0 <= k < es@.len() && es@[k].a == a2 && es@[k].b == b2,
            decreases nls - b,
        {
            proof {
                assert(a * nls + b < t) by (nonlinear_arith) requires a < nrf, b < nls, t == nrf * nls;
                assert(a * nls + b >= 0) by (nonlinear_arith) requires a >= 0, b >= 0, nls >= 0;
            }
            let i = a * nls + b;
            let c = cnt[i];
            let ghost (ai, bi) = (a as int, b as int);
            proof {
                assert(i * 5 + 4 < 5 * t) by (nonlinear_arith) requires i < t;
                assert forall|w: int| 0 <= w <= 5 implies #[trigger] tval(cnt@, sum@, i as int, w) == ksum(m, p, ai, bi, w, 0, m.n) by {
                    lemma_isum_ksum(m, p, ai, bi, w, 0, m.n);
                }
                assert(c == tval(cnt@, sum@, i as int, 5));
            }
            if c > 0 {
                let e = Entry {
                    a, b, cnt: c,
                    s0: sum[i * NSUMS], s1: sum[i * NSUMS + 1], s2: sum[i * NSUMS + 2], s3: sum[i * NSUMS + 3], s4: sum[i * NSUMS + 4],
                    o0: false, o1: false, o2: false, o3: false, o4: false,
                };
                proof {
                    assert forall|w: int| 0 <= w < 5 implies #[trigger] eover(e, w) == (kabs(m, p, ai, bi, w, 0, m.n) > i128_max()) by {
                        lemma_kabs_fast(m, p, ai, bi, w, 0, m.n);
                        assert(vbound(w) <= 0x4_0000_0000_0000);
                        assert(m.n * vbound(w) <= 0x1_0000_0000_0000_0000 * 0x4_0000_0000_0000) by (nonlinear_arith)
                            requires 0 <= m.n <= 0x1_0000_0000_0000_0000, 0 <= vbound(w) <= 0x4_0000_0000_0000;
                    }
                    assert forall|w: int| 0 <= w < 5 && !eover(e, w) implies #[trigger] esum(e, w) == ksum(m, p, ai, bi, w, 0, m.n) by {
                        assert(tval(cnt@, sum@, i as int, w) == sum@[i * 5 + w]);
                    }
                }
                let ghost old_es = es@;
                es.push(e);
                proof {
                    assert forall|k1: int, k2: int| 0 <= k1 < k2 < es@.len() implies #[trigger] key_lt(es@[k1], es@[k2]) by {
                        if k2 == es@.len() - 1 {
                            assert(es@[k1] == old_es[k1]);
                        } else {
                            assert(es@[k1] == old_es[k1] && es@[k2] == old_es[k2]);
                        }
                    }
                    assert forall|a2: int, b2: int| ((0 <= a2 < a && 0 <= b2 < m.nls) || (a2 == a && 0 <= b2 < b + 1))
                        && #[trigger] ksum(m, p, a2, b2, 5, 0, m.n) > 0
                        implies exists|k: int| 0 <= k < es@.len() && es@[k].a == a2 && es@[k].b == b2 by {
                        if a2 == a && b2 == b {
                            assert(es@[es@.len() - 1].a == a2 && es@[es@.len() - 1].b == b2);
                        } else {
                            let k = choose|k: int| 0 <= k < old_es.len() && old_es[k].a == a2 && old_es[k].b == b2;
                            assert(es@[k] == old_es[k]);
                        }
                    }
                }
            }
            b = b + 1;
        }
        a = a + 1;
    }
    es
}

} // verus!
