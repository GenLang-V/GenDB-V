//! Assembly of the index on the calling thread: the ship index check (`ship_check`), facts of the
//! directory of `dirscan` (`lemma_dir_*`), one task per run of entries (`make_task`) and the concatenation of the
//! tasks' outputs (`build_index`), which proves `entry_out` (with `p0 == 0`, `k0 == kmin`) for every entry of the
//! directory over the concatenated rows and ship keys.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::stores::li_pkship::interface::*;
use super::src::*;
use super::dirscan::*;
use super::task::*;

verus! {

/// Every stored row's l_shipinstruct and l_shipmode dictionary indices are below 16 (`ships_in`), checked.
pub fn ship_check(sc: &[u8], sb: &[u64], mc: &[u8], mb: &[u64], bs: usize, n: usize, Ghost(fp): Ghost<Seq<PartView>>)
    -> (ok: bool)
    requires
        base_ok(fp, n as int),
        bs as int == bsize(fp),
        sc@ == u8s(fp[LI_SI_CODES as int]), sb@ == u64s(fp[LI_SI_BASE as int]),
        mc@ == u8s(fp[LI_SM_CODES as int]), mb@ == u64s(fp[LI_SM_BASE as int]),
    ensures ok ==> ships_in(fp, n as int),
{
    let mut s: usize = 0;
    while s < n
        invariant
            base_ok(fp, n as int), bs as int == bsize(fp),
            sc@ == u8s(fp[LI_SI_CODES as int]), sb@ == u64s(fp[LI_SI_BASE as int]),
            mc@ == u8s(fp[LI_SM_CODES as int]), mb@ == u64s(fp[LI_SM_BASE as int]),
            s <= n,
            forall|t: int| 0 <= t < s ==> 0 <= #[trigger] si_at(fp, t) < 16 && 0 <= sm_at(fp, t) < 16,
        decreases n - s,
    {
        proof {
            lemma_div_lt(s as int, bs as int, sb@.len() as int);
            lemma_div_lt(s as int, bs as int, mb@.len() as int);
        }
        let b = s / bs;
        if sb[b] >= 16 || mb[b] >= 16 {
            return false;
        }
        let si = sb[b] + sc[s] as u64;
        let sm = mb[b] + mc[s] as u64;
        if si >= 16 || sm >= 16 {
            return false;
        }
        s = s + 1;
    }
    proof {
        reveal(ships_in);
    }
    true
}

/// Directory bounds: entries start at 0 and end at `n`.
pub proof fn lemma_dir_ends(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>)
    requires dir_spec(fp, n, kmin, offs), n >= 1,
    ensures offs[0] == 0, offs[offs.len() - 1] == n,
{
    reveal(dir_spec);
    let nk = offs.len() - 1;
    let e0 = key_at(fp, kirow(fp, 0)) - kmin;
    assert(0 <= e0 < nk && offs[e0] <= 0);
    lemma_offs_le(offs, nk, 0, e0);
    let e1 = key_at(fp, kirow(fp, n - 1)) - kmin;
    assert(0 <= e1 < nk && n - 1 < offs[e1 + 1]);
    lemma_offs_le(offs, nk, e1 + 1, nk);
}

/// Nondecreasing offsets over a span of entries.
pub proof fn lemma_offs_le(offs: Seq<u32>, nk: int, a: int, b: int)
    requires 0 <= a <= b <= nk, offs.len() == nk + 1, forall|e: int| 0 <= e < nk ==> #[trigger] offs[e] <= offs[e + 1],
    ensures offs[a] <= offs[b],
    decreases b - a,
{
    if a < b {
        lemma_offs_le(offs, nk, a, b - 1);
    }
}

/// A position inside entry `e` holds a row of key `kmin + e`.
pub proof fn lemma_dir_entry(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>, e: int, p: int)
    requires
        dir_spec(fp, n, kmin, offs),
        0 <= e < offs.len() - 1,
        offs[e] <= p < offs[e + 1],
    ensures
        0 <= p < n,
        key_at(fp, kirow(fp, p)) == kmin + e,
{
    reveal(dir_spec);
    let nk = offs.len() - 1;
    lemma_offs_le(offs, nk, e + 1, nk);
    let f = key_at(fp, kirow(fp, p)) - kmin;
    assert(0 <= f < nk && offs[f] <= p < offs[f + 1]);
    if f < e {
        lemma_offs_le(offs, nk, f + 1, e);
    } else if f > e {
        lemma_offs_le(offs, nk, e + 1, f);
    }
}

/// A position below `offs[k]` lies in some entry (offsets nondecreasing from `offs[0] == 0`).
pub proof fn lemma_find_entry(offs: Seq<u32>, k: int, j: int) -> (e: int)
    requires
        0 <= k, offs.len() == k + 1, offs[0] == 0,
        forall|e: int| 0 <= e < k ==> #[trigger] offs[e] <= offs[e + 1],
        0 <= j < offs[k],
    ensures 0 <= e < k, offs[e] <= j < offs[e + 1],
    decreases k,
{
    if j >= offs[k - 1] {
        k - 1
    } else {
        lemma_find_entry(offs.subrange(0, k), k - 1, j)
    }
}

/// A position below `offs[k]` lies in some entry (offsets nondecreasing from `offs[0] == 0`).
pub proof fn lemma_find_entry_m(offs: Seq<u32>, k: int, j: int) -> (e: int)
    requires
        0 <= k, offs.len() == k + 1, offs[0] == 0,
        ents_mono(offs, k),
        0 <= j < offs[k],
    ensures 0 <= e < k, offs[e] <= j < offs[e + 1],
    decreases k,
{
    if j >= offs[k - 1] {
        lemma_ents_le(offs, k, k - 1, k);
        k - 1
    } else {
        let pre = offs.subrange(0, k);
        assert(ents_mono(pre, k - 1)) by {
            reveal(ents_mono);
            assert forall|i: int| 0 <= i < k - 1 implies #[trigger] pre[i] <= pre[i + 1] by {
                assert(pre[i] == offs[i] && pre[i + 1] == offs[i + 1]);
            }
        }
        lemma_find_entry_m(pre, k - 1, j)
    }
}

/// The directory's offsets never decrease.
pub proof fn lemma_dir_mono(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>)
    requires dir_spec(fp, n, kmin, offs),
    ensures ents_mono(offs, offs.len() - 1), offs.len() >= 1,
{
    reveal(dir_spec);
    reveal(ents_mono);
}

/// Task `t` covers entries `e_lo .. e_lo + ne` of the directory `o`, positions `o[e_lo] .. o[e_lo + ne]`.
pub open spec fn task_cover(t: IdxTask, fp: Seq<PartView>, n: int, kmin: int, o: Seq<u32>) -> bool {
    &&& t.fp@ == fp && t.n == n && t.kmin@ == kmin
    &&& 0 <= t.e_lo@ && t.e_lo@ + t.ne < o.len()
    &&& t.ents@ == o.subrange(t.e_lo@, t.e_lo@ + t.ne + 1)
    &&& t.p0 == o[t.e_lo@] && t.p1 == o[t.e_lo@ + t.ne]
}

/// The keys of the task's entries, from the directory.
proof fn lemma_task_keys(fp: Seq<PartView>, n: int, kmin: int, o: Seq<u32>, e_lo: int, ne: int, ents: Seq<u32>, j: int)
    requires
        dir_spec(fp, n, kmin, o),
        0 <= e_lo, e_lo + ne < o.len(),
        ents == o.subrange(e_lo, e_lo + ne + 1),
        0 <= j < ne,
    ensures entry_keys(fp, kmin + e_lo, ents, j),
{
    reveal(entry_keys);
    assert forall|p: int| ents[j] <= p < ents[j + 1] implies #[trigger] key_at(fp, kirow(fp, p)) == (kmin + e_lo) + j by {
        lemma_dir_entry(fp, n, kmin, o, e_lo + j, p);
    }
}

/// The task's entry starts never decrease.
proof fn lemma_task_mono(o: Seq<u32>, e_lo: int, ne: int, ents: Seq<u32>)
    requires
        ents_mono(o, o.len() - 1),
        0 <= e_lo, e_lo + ne < o.len(),
        ents == o.subrange(e_lo, e_lo + ne + 1),
    ensures ents_mono(ents, ne),
{
    reveal(ents_mono);
    assert forall|j: int| 0 <= j < ne implies #[trigger] ents[j] <= ents[j + 1] by {
        assert(ents[j] == o[e_lo + j] && ents[j + 1] == o[e_lo + j + 1]);
        assert(o[e_lo + j] <= o[e_lo + j + 1]);
    }
}

/// The task covering entries `e_lo .. e_hi` (calling thread; allocates its buffers).
pub fn make_task(ic: &'static [u32], ib: &'static [u64], sc: &'static [u8], sb: &'static [u64], mc: &'static [u8], mb: &'static [u64], bs: usize, n: usize,
    kmin: i64, offs: &Vec<u32>, e_lo: usize, e_hi: usize, Ghost(fp): Ghost<Seq<PartView>>) -> (t: IdxTask)
    requires
        task_src(fp, n as int, bs as int, ic@, ib@, sc@, sb@, mc@, mb@),
        dir_spec(fp, n as int, kmin as int, offs@),
        ships_in(fp, n as int),
        offs@[offs@.len() - 1] <= n,
        e_lo <= e_hi < offs@.len(),
    ensures
        task_pre(t),
        task_cover(t, fp, n as int, kmin as int, offs@),
        t.e_lo@ == e_lo, t.ne == e_hi - e_lo,
{
    let ghost o = offs@;
    let nk = offs.len() - 1;
    proof {
        lemma_dir_mono(fp, n as int, kmin as int, o);
        lemma_ents_le(o, nk as int, e_lo as int, e_hi as int);
        lemma_ents_le(o, nk as int, e_hi as int, nk as int);
    }
    let mut ents: Vec<u32> = Vec::new();
    let mut e = e_lo;
    while e <= e_hi
        invariant
            e_lo <= e <= e_hi + 1, e_hi < o.len(), o == offs@, e_hi < offs.len(),
            ents@ == o.subrange(e_lo as int, e as int),
        decreases e_hi + 1 - e,
    {
        ents.push(offs[e]);
        proof { assert(ents@ =~= o.subrange(e_lo as int, e + 1)); }
        e = e + 1;
    }
    let p0 = offs[e_lo] as usize;
    let p1 = offs[e_hi] as usize;
    let len = p1 - p0;
    let packed: Vec<u64> = vec![0u64; len];
    let tmp: Vec<u64> = vec![0u64; len];
    let rows: Vec<u32> = vec![0u32; len];
    let dates: Vec<u8> = vec![0u8; len];
    let task = IdxTask {
        ic, ib, sc, sb, mc, mb, bs, n, ents, ne: e_hi - e_lo, p0, p1, packed, tmp, rows, ships: dates,
        fp: Ghost(fp), kmin: Ghost(kmin as int), e_lo: Ghost(e_lo as int),
    };
    proof {
        let ev = task.ents@;
        assert(ev[0] == o[e_lo as int]);
        assert(ev[(e_hi - e_lo) as int] == o[e_hi as int]);
        lemma_task_mono(o, e_lo as int, (e_hi - e_lo) as int, ev);
        assert forall|j: int| 0 <= j < e_hi - e_lo implies #[trigger] entry_keys(fp, kmin + e_lo, ev, j) by {
            lemma_task_keys(fp, n as int, kmin as int, o, e_lo as int, (e_hi - e_lo) as int, ev, j);
        }
    }
    task
}

/// An entry before the appended part keeps `entry_out` (its positions are unchanged).
proof fn lemma_entry_keep(fp: Seq<PartView>, n: int, kmin: int, o: Seq<u32>,
    r0: Seq<u32>, d0: Seq<u8>, r1: Seq<u32>, d1: Seq<u8>, e: int)
    requires
        entry_out(fp, n, kmin, o, 0, r0, d0, e),
        o[e] <= o[e + 1] <= r0.len(), r0.len() == d0.len(),
        r1.len() >= r0.len(), d1.len() >= d0.len(),
        forall|p: int| 0 <= p < r0.len() ==> r1[p] == r0[p],
        forall|p: int| 0 <= p < d0.len() ==> d1[p] == d0[p],
    ensures entry_out(fp, n, kmin, o, 0, r1, d1, e),
{
    reveal(entry_out);
}

/// An entry of the appended task's run: `entry_out` over the concatenation from the task's output.
proof fn lemma_entry_new(fp: Seq<PartView>, n: int, kmin: int, o: Seq<u32>, t: IdxTask,
    out: (Vec<u32>, Vec<u8>), r1: Seq<u32>, d1: Seq<u8>, e: int)
    requires
        task_cover(t, fp, n, kmin, o),
        task_post(t, out),
        t.e_lo@ <= e < t.e_lo@ + t.ne,
        o[e] <= o[e + 1],
        t.p0 <= o[e], o[e + 1] <= t.p1,
        forall|p: int| t.p0 <= p < t.p1 ==> r1[p] == out.0@[p - t.p0] && d1[p] == out.1@[p - t.p0],
    ensures entry_out(fp, n, kmin, o, 0, r1, d1, e),
{
    let j = e - t.e_lo@;
    let p0 = t.p0 as int;
    assert(entry_out(fp, n, kmin + t.e_lo@, t.ents@, p0, out.0@, out.1@, j));
    reveal(entry_out);
    let ents = t.ents@;
    assert(ents[j] == o[e] && ents[j + 1] == o[e + 1]);
    assert forall|x: int| o[e] - 0 <= x < o[e + 1] - 0 implies {
        &&& (#[trigger] r1[x]) < n
        &&& key_at(fp, r1[x] as int) == kmin + e
        &&& d1[x] == ship_of(fp, r1[x] as int)
        &&& (x + 1 < o[e + 1] - 0 ==> d1[x] <= d1[x + 1])
    } by {
        let y = x - p0;
        assert(r1[x] == out.0@[y] && d1[x] == out.1@[y]);
        assert(ents[j] - p0 <= y < ents[j + 1] - p0);
        assert(out.0@[y] < n);
        if x + 1 < o[e + 1] {
            assert(d1[x + 1] == out.1@[y + 1]);
        }
    }
}

/// One more task's output appended: `entry_out` for its entries over the concatenation.
proof fn lemma_concat_step(fp: Seq<PartView>, n: int, kmin: int, o: Seq<u32>, t: IdxTask,
    r0: Seq<u32>, d0: Seq<u8>, out: (Vec<u32>, Vec<u8>), r1: Seq<u32>, d1: Seq<u8>)
    requires
        task_cover(t, fp, n, kmin, o),
        task_post(t, out),
        ents_mono(o, o.len() - 1),
        r0.len() == t.p0, d0.len() == t.p0,
        r1 == r0 + out.0@, d1 == d0 + out.1@,
        forall|e: int| 0 <= e < t.e_lo@ ==> #[trigger] entry_out(fp, n, kmin, o, 0, r0, d0, e),
    ensures
        r1.len() == t.p1, d1.len() == t.p1,
        forall|e: int| 0 <= e < t.e_lo@ + t.ne ==> #[trigger] entry_out(fp, n, kmin, o, 0, r1, d1, e),
{
    let nk = o.len() - 1;
    assert forall|e: int| 0 <= e < t.e_lo@ + t.ne implies #[trigger] entry_out(fp, n, kmin, o, 0, r1, d1, e) by {
        lemma_ents_le(o, nk, e, e + 1);
        if e < t.e_lo@ {
            lemma_ents_le(o, nk, e + 1, t.e_lo@);
            lemma_entry_keep(fp, n, kmin, o, r0, d0, r1, d1, e);
        } else {
            lemma_ents_le(o, nk, t.e_lo@, e);
            lemma_ents_le(o, nk, e + 1, t.e_lo@ + t.ne);
            lemma_entry_new(fp, n, kmin, o, t, out, r1, d1, e);
        }
    }
}

/// The index rows and ship keys of every entry, built by one task per run of entries.
pub fn build_index(ic: &'static [u32], ib: &'static [u64], sc: &'static [u8], sb: &'static [u64], mc: &'static [u8], mb: &'static [u64], bs: usize, n: usize,
    kmin: i64, offs: &Vec<u32>, workers: usize, dispatch: &mut Dispatch, Ghost(fp): Ghost<Seq<PartView>>)
    -> (r: Result<(Vec<u32>, Vec<u8>), QueryError>)
    requires
        task_src(fp, n as int, bs as int, ic@, ib@, sc@, sb@, mc@, mb@),
        dir_spec(fp, n as int, kmin as int, offs@),
        ships_in(fp, n as int),
        1 <= n,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok((rows, dates)) ==> rows@.len() == n && dates@.len() == n
            && forall|e: int| 0 <= e < offs@.len() - 1 ==>
                #[trigger] entry_out(fp, n as int, kmin as int, offs@, 0, rows@, dates@, e),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost o = offs@;
    proof {
        lemma_dir_mono(fp, n as int, kmin as int, o);
        lemma_dir_ends(fp, n as int, kmin as int, o);
    }
    let nk = offs.len() - 1;
    let nt = if nk < workers { nk } else { workers };
    let chunk = nk / nt;
    let mut tasks: Vec<IdxTask> = Vec::new();
    let mut t: usize = 0;
    let mut e_lo: usize = 0;
    while t < nt
        invariant
            task_src(fp, n as int, bs as int, ic@, ib@, sc@, sb@, mc@, mb@),
            dir_spec(fp, n as int, kmin as int, o), o == offs@, nk == o.len() - 1, nk >= 1,
            ships_in(fp, n as int),
            o[nk as int] == n,
            1 <= nt <= nk, nt <= MAX_WORKERS, t <= nt, tasks@.len() == t,
            e_lo <= nk,
            t == nt ==> e_lo == nk,
            t == 0 ==> e_lo == 0,
            t > 0 ==> tasks@[0].e_lo@ == 0,
            forall|i: int| 0 <= i < t ==> {
                &&& (#[trigger] tasks@[i]).pre()
                &&& task_cover(tasks@[i], fp, n as int, kmin as int, o)
                &&& tasks@[i].e_lo@ + tasks@[i].ne == (if i + 1 < t { tasks@[i + 1].e_lo@ } else { e_lo as int })
            },
        decreases nt - t,
    {
        let e_hi = if t + 1 == nt || chunk > nk - e_lo { nk } else { e_lo + chunk };
        let task = make_task(ic, ib, sc, sb, mc, mb, bs, n, kmin, offs, e_lo, e_hi, Ghost(fp));
        let ghost old_tasks = tasks@;
        tasks.push(task);
        proof {
            assert forall|i: int| 0 <= i < t + 1 implies {
                &&& (#[trigger] tasks@[i]).pre()
                &&& task_cover(tasks@[i], fp, n as int, kmin as int, o)
                &&& tasks@[i].e_lo@ + tasks@[i].ne == (if i + 1 < t + 1 { tasks@[i + 1].e_lo@ } else { e_hi as int })
            } by {
                if i < t {
                    assert(tasks@[i] == old_tasks[i]);
                }
            }
        }
        e_lo = e_hi;
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    // Concatenate in task order.
    let mut outs = outs;
    let mut rev: Vec<(Vec<u32>, Vec<u8>)> = Vec::new();
    while outs.len() > 0
        invariant
            outs@.len() + rev@.len() == nt,
            forall|i: int| 0 <= i < outs@.len() ==> #[trigger] tv[i].post(outs@[i]),
            forall|i: int| 0 <= i < rev@.len() ==> #[trigger] tv[nt - 1 - i].post(rev@[i]),
        decreases outs@.len(),
    {
        let x = outs.pop().unwrap();
        rev.push(x);
    }
    let mut rows: Vec<u32> = Vec::new();
    let mut dates: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    while rev.len() > 0
        invariant
            rev@.len() + k == nt, k <= nt, 1 <= nt, o == offs@, nk == o.len() - 1,
            o[nk as int] == n,
            ents_mono(o, nk as int),
            forall|i: int| 0 <= i < rev@.len() ==> #[trigger] tv[nt - 1 - i].post(rev@[i]),
            forall|i: int| 0 <= i < nt ==> {
                &&& task_cover(#[trigger] tv[i], fp, n as int, kmin as int, o)
                &&& tv[i].e_lo@ + tv[i].ne == (if i + 1 < nt { tv[i + 1].e_lo@ } else { nk as int })
            },
            tv[0].e_lo@ == 0,
            rows@.len() == dates@.len(),
            rows@.len() == (if k < nt { tv[k as int].p0 as int } else { n as int }),
            forall|e: int| 0 <= e < (if k < nt { tv[k as int].e_lo@ } else { nk as int }) ==>
                #[trigger] entry_out(fp, n as int, kmin as int, o, 0, rows@, dates@, e),
        decreases rev@.len(),
    {
        let ghost rv = rev@;
        let x = rev.pop().unwrap();
        proof {
            assert(x == rv[rv.len() - 1]);
            assert(tv[nt - 1 - (rv.len() - 1)].post(rv[rv.len() - 1]));
            assert(nt - 1 - (rv.len() - 1) == k);
        }
        let (mut ro, mut da) = x;
        let ghost task = tv[k as int];
        let ghost (r0, d0) = (rows@, dates@);
        rows.append(&mut ro);
        dates.append(&mut da);
        proof {
            assert(task_post(task, x));
            lemma_concat_step(fp, n as int, kmin as int, o, task, r0, d0, x, rows@, dates@);
            if k + 1 < nt {
                assert(tv[k + 1].p0 == o[tv[k + 1].e_lo@]);
            }
        }
        k = k + 1;
    }
    Ok((rows, dates))
}

} // verus!
