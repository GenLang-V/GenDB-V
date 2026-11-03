//! The group table of all qualifying orders (`compute_groups`).
//!
//! Partition: `lineitem` rows into `nt` equal chunks `[lb[t], lb[t + 1])`; `orders` rows into chunks `[ob[t], ob[t + 1])`
//! that start at the first order whose key reaches the first key of the `lineitem` chunk (a binary search that assumes
//! `o_orderkey` sorted only for balance: any monotone split is correct). One `MTask` per pair of chunks.
//!
//! After the join: when every task kept its table and found its `lineitem` pairs in key order, `l_orderkey` is sorted
//! (`lemma_pairs_join` over the chunks), so every task's rows are the qualifying orders of its chunk, and the tables
//! merge in chunk order into the table of `q_list(0, no)`. Otherwise (unsorted keys, or more than `SLOTS` priorities
//! in a task) the calling thread computes the table directly: each order in the window, `has` by a scan of
//! `lineitem`.
use vstd::prelude::*;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::cols::*;
use crate::agent::lists::*;
use crate::agent::table::*;
use crate::agent::task::*;

verus! {

/// First row `r >= a` of `orders` whose key is at least `k` on sorted keys (any row in `[a, no]` otherwise).
fn okey_lower(o: &OCols, k: i64, a: usize) -> (r: usize)
    requires ocols_wf(*o), a <= o.no,
    ensures a <= r <= o.no,
{
    let mut lo = a;
    let mut hi = o.no;
    while lo < hi
        invariant ocols_wf(*o), a <= lo <= hi <= o.no,
        decreases hi - lo,
    {
        let m = lo + (hi - lo) / 2;
        if o.okey[m] < k {
            lo = m + 1;
        } else {
            hi = m;
        }
    }
    lo
}

/// Chunk `t` of `n` rows in `nt` chunks starts at `t * (n / nt)`; the chunks are ordered and inside `[0, n]`.
pub proof fn lemma_chunk(t: int, nt: int, n: int)
    requires 0 <= t < nt, n >= 0,
    ensures
        0 <= t * (n / nt) <= (t + 1) * (n / nt),
        t + 1 < nt ==> (t + 1) * (n / nt) <= n,
        t * (n / nt) <= n,
{
    let c = n / nt;
    assert(c * nt <= n) by (nonlinear_arith) requires c == n / nt, nt >= 1, n >= 0;
    assert(0 <= c) by (nonlinear_arith) requires c == n / nt, nt >= 1, n >= 0;
    assert(t * c <= (t + 1) * c) by (nonlinear_arith) requires c >= 0, t >= 0;
    assert((t + 1) * c <= nt * c) by (nonlinear_arith) requires c >= 0, t + 1 <= nt;
    assert(0 <= t * c) by (nonlinear_arith) requires c >= 0, t >= 0;
    assert(nt * c == c * nt) by (nonlinear_arith);
    assert(t * c <= (t + 1) * c);
    assert((t + 1) * c <= n);
}

/// The task facts the merge needs, per chunk `t`.
pub open spec fn task_ok(tk: MTask, l: LCols, o: OCols, w: Win, lb: Seq<usize>, ob: Seq<usize>, t: int) -> bool {
    &&& tk.l == l
    &&& tk.o == o
    &&& tk.w == w
    &&& tk.lo == lb[t]
    &&& tk.hi == lb[t + 1]
    &&& tk.olo == ob[t]
    &&& tk.ohi == ob[t + 1]
    &&& tk.pre()
}

/// The chunk bounds: ordered, from 0 to the row counts.
pub open spec fn bounds_ok(l: LCols, o: OCols, lb: Seq<usize>, ob: Seq<usize>, nt: int) -> bool {
    &&& lb.len() == nt + 1
    &&& ob.len() == nt + 1
    &&& lb[0] == 0
    &&& ob[0] == 0
    &&& lb[nt] == l.nl
    &&& ob[nt] == o.no
    &&& forall|t: int| 0 <= t < nt ==> lb[t] <= #[trigger] lb[t + 1] <= l.nl
    &&& forall|t: int| 0 <= t < nt ==> ob[t] <= #[trigger] ob[t + 1] <= o.no
}

/// One task per chunk pair, with its buffers.
fn make_tasks(l: LCols, o: OCols, w: Win, nt: usize) -> (r: (Vec<MTask>, Vec<usize>, Vec<usize>))
    requires lcols_wf(l), ocols_wf(o), 1 <= nt <= MAX_WORKERS,
    ensures
        r.0@.len() == nt,
        bounds_ok(l, o, r.1@, r.2@, nt as int),
        forall|t: int| 0 <= t < nt ==> task_ok(#[trigger] r.0@[t], l, o, w, r.1@, r.2@, t),
{
    let nl = l.nl;
    let no = o.no;
    let chunk = nl / nt;
    let mut tasks: Vec<MTask> = Vec::new();
    let mut lb: Vec<usize> = Vec::new();
    let mut ob: Vec<usize> = Vec::new();
    lb.push(0);
    ob.push(0);
    let mut t: usize = 0;
    while t < nt
        invariant
            lcols_wf(l),
            ocols_wf(o),
            nl == l.nl,
            no == o.no,
            1 <= nt <= MAX_WORKERS,
            chunk == nl / nt,
            t <= nt,
            tasks@.len() == t,
            lb@.len() == t + 1,
            ob@.len() == t + 1,
            lb@[0] == 0,
            ob@[0] == 0,
            t < nt ==> lb@[t as int] == t * chunk,
            t == nt ==> lb@[t as int] == nl,
            t == nt ==> ob@[t as int] == no,
            forall|x: int| 0 <= x < t ==> lb@[x] <= #[trigger] lb@[x + 1] <= nl,
            forall|x: int| 0 <= x < t ==> ob@[x] <= #[trigger] ob@[x + 1] <= no,
            ob@[t as int] <= no,
            forall|x: int| 0 <= x < t ==> task_ok(#[trigger] tasks@[x], l, o, w, lb@, ob@, x),
        decreases nt - t,
    {
        proof {
            lemma_chunk(t as int, nt as int, nl as int);
        }
        let lo = lb[t];
        let hi = if t + 1 == nt { nl } else { (t + 1) * chunk };
        let olo = ob[t];
        let ohi = if t + 1 == nt {
            no
        } else if hi < nl {
            okey_lower(&o, l.lk[hi], olo)
        } else {
            no
        };
        let task = MTask {
            l, o, w, lo, hi, olo, ohi,
            reps: vec![0usize; SLOTS],
            counts: vec![0u64; SLOTS],
            bk: vec![0i64; BATCH],
            bi: vec![0usize; BATCH],
            bs: vec![0usize; BATCH],
            be: vec![0usize; BATCH],
            bf: vec![0usize; BATCH],
            cache: vec![0usize; CACHE],
        };
        let ghost (lb0, ob0, tk0) = (lb@, ob@, tasks@);
        tasks.push(task);
        lb.push(hi);
        ob.push(ohi);
        proof {
            assert forall|x: int| 0 <= x < t + 1 implies task_ok(#[trigger] tasks@[x], l, o, w, lb@, ob@, x) by {
                if x < t {
                    assert(tasks@[x] == tk0[x]);
                    assert(task_ok(tk0[x], l, o, w, lb0, ob0, x));
                }
            }
            assert forall|x: int| 0 <= x < t + 1 implies lb@[x] <= #[trigger] lb@[x + 1] <= nl by {
                if x < t {
                    assert(lb0[x] <= lb0[x + 1] <= nl);
                }
            }
            assert forall|x: int| 0 <= x < t + 1 implies ob@[x] <= #[trigger] ob@[x + 1] <= no by {
                if x < t {
                    assert(ob0[x] <= ob0[x + 1] <= no);
                }
            }
        }
        t = t + 1;
    }
    (tasks, lb, ob)
}

/// The table computed by the calling thread alone: each order in the window, `has` by a scan of `lineitem`.
fn groups_seq(l: &LCols, o: &OCols, w: Win) -> (r: (Vec<usize>, Vec<u64>))
    requires lcols_wf(*l), ocols_wf(*o),
    ensures
        r.0@.len() == r.1@.len(),
        tbl_ok(*o, r.0@, r.1@, r.0@.len() as int, q_list(*l, *o, w, 0, o.no as int)),
{
    let mut reps: Vec<usize> = Vec::new();
    let mut counts: Vec<u64> = Vec::new();
    proof {
        lemma_tbl_empty(*o, reps@, counts@);
        assert(q_list(*l, *o, w, 0, 0) == Seq::<usize>::empty());
    }
    let no = o.no;
    let mut i: usize = 0;
    while i < no
        invariant
            lcols_wf(*l),
            ocols_wf(*o),
            no == o.no,
            i <= no,
            reps@.len() == counts@.len(),
            tbl_ok(*o, reps@, counts@, reps@.len() as int, q_list(*l, *o, w, 0, i as int)),
        decreases no - i,
    {
        let ghost p = q_list(*l, *o, w, 0, i as int);
        proof {
            lemma_q_list(*l, *o, w, 0, i as int);
        }
        let d = o.odate[i] as i64;
        if d >= w.dlo && d < w.dhi {
            if has_scan(l, o.okey[i]) {
                tbl_add_grow(o, &mut reps, &mut counts, i, Ghost(p));
            }
        }
        i = i + 1;
    }
    (reps, counts)
}

/// The group table of all qualifying orders, computed by up to `nt` tasks.
pub fn compute_groups(l: &LCols, o: &OCols, w: Win, nt: usize, dispatch: &mut Dispatch)
    -> (r: Result<(Vec<usize>, Vec<u64>), WorkerFailure>)
    requires lcols_wf(*l), ocols_wf(*o), 1 <= nt <= MAX_WORKERS,
    ensures
        r matches Ok(t) ==> t.0@.len() == t.1@.len()
            && tbl_ok(*o, t.0@, t.1@, t.0@.len() as int, q_list(*l, *o, w, 0, o.no as int)),
{
    let (tasks, lb, ob) = make_tasks(*l, *o, w, nt);
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    // Every task kept its table and its pairs are in order: then `l_orderkey` is sorted.
    let mut all_ok = true;
    let mut t: usize = 0;
    proof {
        assert forall|j: int| 0 < j < chunk_end(*l, 0) implies #[trigger] pair_ok(*l, j) by {}
    }
    while t < nt
        invariant
            lcols_wf(*l),
            ocols_wf(*o),
            outs@.len() == nt,
            tv.len() == nt,
            bounds_ok(*l, *o, lb@, ob@, nt as int),
            forall|x: int| 0 <= x < nt ==> task_ok(#[trigger] tv[x], *l, *o, w, lb@, ob@, x),
            forall|x: int| 0 <= x < nt ==> #[trigger] tv[x].post(outs@[x]),
            t <= nt,
            all_ok ==> pairs_ok(*l, 0, chunk_end(*l, lb@[t as int] as int)),
            all_ok ==> forall|x: int| 0 <= x < t ==> !(#[trigger] outs@[x]).full,
        decreases nt - t,
    {
        let good = outs[t].ok && !outs[t].full;
        proof {
            assert(task_ok(tv[t as int], *l, *o, w, lb@, ob@, t as int));
            assert(tv[t as int].post(outs@[t as int]));
            if all_ok && good {
                let (a, b) = (lb@[t as int] as int, lb@[t + 1] as int);
                assert(lb@[t as int] <= lb@[t + 1]);
                if a < l.nl {
                    lemma_pairs_join(*l, 0, a, chunk_end(*l, b));
                } else {
                    assert(b == l.nl);
                }
            }
        }
        if !good {
            all_ok = false;
        }
        t = t + 1;
    }
    if !all_ok {
        return Ok(groups_seq(l, o, w));
    }
    proof {
        assert(sorted(*l));
    }
    // Merge the task tables in chunk order.
    let mut reps: Vec<usize> = Vec::new();
    let mut counts: Vec<u64> = Vec::new();
    proof {
        lemma_tbl_empty(*o, reps@, counts@);
        assert(q_list(*l, *o, w, 0, 0) == Seq::<usize>::empty());
    }
    let mut t: usize = 0;
    while t < nt
        invariant
            lcols_wf(*l),
            ocols_wf(*o),
            sorted(*l),
            outs@.len() == nt,
            tv.len() == nt,
            bounds_ok(*l, *o, lb@, ob@, nt as int),
            forall|x: int| 0 <= x < nt ==> task_ok(#[trigger] tv[x], *l, *o, w, lb@, ob@, x),
            forall|x: int| 0 <= x < nt ==> #[trigger] tv[x].post(outs@[x]),
            forall|x: int| 0 <= x < nt ==> !(#[trigger] outs@[x]).full,
            t <= nt,
            reps@.len() == counts@.len(),
            tbl_ok(*o, reps@, counts@, reps@.len() as int, q_list(*l, *o, w, 0, ob@[t as int] as int)),
        decreases nt - t,
    {
        let ghost p1 = q_list(*l, *o, w, 0, ob@[t as int] as int);
        let ghost (a, b) = (ob@[t as int] as int, ob@[t + 1] as int);
        proof {
            assert(task_ok(tv[t as int], *l, *o, w, lb@, ob@, t as int));
            assert(tv[t as int].post(outs@[t as int]));
            assert(!outs@[t as int].full);
            assert(ob@[t as int] <= ob@[t + 1] <= o.no);
            lemma_q_list(*l, *o, w, 0, a);
            lemma_q_list(*l, *o, w, a, b);
            lemma_q_list_split(*l, *o, w, 0, a, b);
        }
        tbl_merge(o, &mut reps, &mut counts, &outs[t].reps, &outs[t].counts, outs[t].ng, Ghost(p1), Ghost(outs@[t as int].p@));
        t = t + 1;
    }
    Ok((reps, counts))
}

} // verus!
