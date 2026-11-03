//! Running the scan: the orders range `[p0, p1)` (clustered layout) or all lineitem rows (otherwise) is split
//! into one range per worker; each worker runs `kernel::ScanTask`; the task outputs are merged in range order.
//! Adjacent tasks meet at the same lineitem row (`lemma_split_unique`), and lineitem rows outside the scanned
//! range take part in no group (`plan::lemma_outside_zero`), so the totals are the accumulators over every stored
//! lineitem row (`totals_ok`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::link::join::*;
use crate::link::expr::i128_max;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS, WorkerTask, fork_join};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::filled;
use crate::agent::q5spec::*;
use crate::agent::chain::*;
use crate::agent::kernel::*;
use crate::agent::setup::*;
use crate::agent::plan::*;
use crate::agent::common::sums::*;
use crate::agent::common::dense::{range_at, lemma_range_at, range_start};
use crate::agent::common::forview::{Div, div_new};
use std::sync::Arc;

verus! {

/// The merged accumulators of every group.
pub struct Totals {
    pub cnt: Vec<usize>,
    pub sum: Vec<i128>,
    pub abs: Vec<u128>,
    pub ovf: Vec<bool>,
}

/// The totals are the accumulators over stored lineitem rows `[a, b)`.
pub open spec fn totals_on(t: ScanCtx, tot: Totals, a: int, b: int) -> bool {
    let ng = t.gnames@.len();
    &&& tot.cnt@.len() == ng && tot.sum@.len() == ng && tot.abs@.len() == ng && tot.ovf@.len() == ng
    &&& forall|gi: int| 0 <= gi < ng ==> #[trigger] t.acc_ok(gi, a, b, tot.cnt@[gi], tot.sum@[gi], tot.abs@[gi], tot.ovf@[gi])
}

/// A lineitem row's multiplicity is never negative.
pub proof fn lemma_mult_nonneg(rs: Rels, prm: Prm, k: Row, l: Row)
    ensures line_mult(rs, prm, k, l) >= 0,
{
    reveal(line_mult);
    assert forall|i: int| 0 <= i < rs.o.len() implies #[trigger] o_term(rs, prm, k, l, rs.o[i]) >= 0 by {
        let o = rs.o[i];
        assert forall|ic: int| 0 <= ic < rs.c.len() implies #[trigger] c_term(rs, o, l, k, prm.name, rs.c[ic]) >= 0 by {
            let c = rs.c[ic];
            assert forall|is: int| 0 <= is < rs.s.len() implies #[trigger] s_term(rs, c, l, k, prm.name, rs.s[is]) >= 0 by {
                let s = rs.s[is];
                assert forall|ni: int| 0 <= ni < rs.n.len() implies #[trigger] n_term(rs, s, k, prm.name, rs.n[ni]) >= 0 by {
                    let n = rs.n[ni];
                    lemma_sum_nonneg(rs.r, |r: Row| r_term(n, prm.name, r));
                }
                lemma_sum_nonneg(rs.n, |n: Row| n_term(rs, s, k, prm.name, n));
            }
            lemma_sum_nonneg(rs.s, |s: Row| s_term(rs, c, l, k, prm.name, s));
        }
        lemma_sum_nonneg(rs.c, |c: Row| c_term(rs, o, l, k, prm.name, c));
    }
    lemma_sum_nonneg(rs.o, |o: Row| o_term(rs, prm, k, l, o));
}

/// Nonnegative terms have a nonnegative sum.
pub proof fn lemma_sum_nonneg(rows: Seq<Row>, f: spec_fn(Row) -> int)
    requires forall|i: int| 0 <= i < rows.len() ==> f(#[trigger] rows[i]) >= 0,
    ensures sum_of(rows, f) >= 0,
{
    lemma_sum_range_nonneg(rows, f, 0, rows.len() as int);
    lemma_sum_range_all(rows, f);
}

/// The absolute-revenue accumulator has nonnegative terms.
pub proof fn lemma_abs_terms(t: ScanCtx, gi: int)
    ensures
        forall|j: int| 0 <= j < t.lrows@.len() ==>
            #[trigger] contrib_fn(t.rs@, t.prm@, gkey(t.gnames@, gi), 2)(t.lrows@[j]) >= 0,
{
    assert forall|j: int| 0 <= j < t.lrows@.len() implies
        #[trigger] contrib_fn(t.rs@, t.prm@, gkey(t.gnames@, gi), 2)(t.lrows@[j]) >= 0 by {
        let l = t.lrows@[j];
        let m = line_mult(t.rs@, t.prm@, gkey(t.gnames@, gi), l);
        lemma_mult_nonneg(t.rs@, t.prm@, gkey(t.gnames@, gi), l);
        let w = wsel(2, l);
        assert(w >= 0);
        assert(m * w >= 0) by (nonlinear_arith) requires m >= 0, w >= 0;
    }
}

/// Two lineitem rows splitting at the same orders position are the same row.
pub proof fn lemma_split_unique(t: ScanCtx, p: int, r1: int, r2: int)
    requires t.split_at(p, r1), t.split_at(p, r2),
    ensures r1 == r2,
{
    if r1 < r2 {
        assert(r1 < t.n_l);
        assert(t.op(r1) < p);
    } else if r2 < r1 {
        assert(r2 < t.n_l);
        assert(t.op(r2) < p);
    }
}

/// Merge one task's accumulators (rows `[b, c)`) into the totals of rows `[a, b)`.
fn merge_task(t: &ScanCtx, tot: &mut Totals, out: &ScanOut, a: usize, b: usize, c: usize)
    requires
        t.wf(), a <= b <= c <= t.n_l,
        totals_on(*t, *old(tot), a as int, b as int),
        out.cnt@.len() == t.gnames@.len() && out.sum@.len() == t.gnames@.len()
            && out.abs@.len() == t.gnames@.len() && out.ovf@.len() == t.gnames@.len(),
        forall|gi: int| 0 <= gi < t.gnames@.len() ==>
            #[trigger] t.acc_ok(gi, b as int, c as int, out.cnt@[gi], out.sum@[gi], out.abs@[gi], out.ovf@[gi]),
    ensures totals_on(*t, *final(tot), a as int, c as int),
{
    let ng = tot.cnt.len();
    let mut gi: usize = 0;
    while gi < ng
        invariant
            t.wf(), a <= b <= c <= t.n_l,
            ng == t.gnames@.len(),
            tot.cnt@.len() == ng && tot.sum@.len() == ng && tot.abs@.len() == ng && tot.ovf@.len() == ng,
            out.cnt@.len() == ng && out.sum@.len() == ng && out.abs@.len() == ng && out.ovf@.len() == ng,
            gi <= ng,
            forall|h: int| 0 <= h < gi ==> #[trigger] t.acc_ok(h, a as int, c as int, tot.cnt@[h], tot.sum@[h], tot.abs@[h], tot.ovf@[h]),
            forall|h: int| gi <= h < ng ==> #[trigger] t.acc_ok(h, a as int, b as int, tot.cnt@[h], tot.sum@[h], tot.abs@[h], tot.ovf@[h]),
            forall|h: int| 0 <= h < ng ==>
                #[trigger] t.acc_ok(h, b as int, c as int, out.cnt@[h], out.sum@[h], out.abs@[h], out.ovf@[h]),
        decreases ng - gi,
    {
        let ghost g = gi as int;
        proof {
            assert(t.acc_ok(g, a as int, b as int, tot.cnt@[g], tot.sum@[g], tot.abs@[g], tot.ovf@[g]));
            assert(t.acc_ok(g, b as int, c as int, out.cnt@[g], out.sum@[g], out.abs@[g], out.ovf@[g]));
            lemma_abs_terms(*t, g);
            let f = contrib_fn(t.rs@, t.prm@, gkey(t.gnames@, g), 2);
            lemma_sum_range_mono(t.lrows@, f, a as int, b as int, a as int, c as int);
            lemma_sum_range_mono(t.lrows@, f, b as int, c as int, a as int, c as int);
            assert forall|m: int| #[trigger] t.lsum(g, m, a as int, c as int) == t.lsum(g, m, a as int, b as int) + t.lsum(g, m, b as int, c as int) by {
                lemma_sum_range_split(t.lrows@, contrib_fn(t.rs@, t.prm@, gkey(t.gnames@, g), m), a as int, b as int, c as int);
            }
        }
        if tot.ovf[gi] || out.ovf[gi] {
            tot.ovf[gi] = true;
        } else if tot.abs[gi] <= (i128::MAX as u128) - out.abs[gi] {
            tot.abs[gi] = tot.abs[gi] + out.abs[gi];
            tot.sum[gi] = tot.sum[gi] + out.sum[gi];
            tot.cnt[gi] = tot.cnt[gi] + out.cnt[gi];
        } else {
            tot.ovf[gi] = true;
        }
        proof {
            assert(t.lsum(g, 0, a as int, c as int) == t.lsum(g, 0, a as int, b as int) + t.lsum(g, 0, b as int, c as int));
            assert(t.lsum(g, 1, a as int, c as int) == t.lsum(g, 1, a as int, b as int) + t.lsum(g, 1, b as int, c as int));
            assert(t.lsum(g, 2, a as int, c as int) == t.lsum(g, 2, a as int, b as int) + t.lsum(g, 2, b as int, c as int));
            assert(t.acc_ok(g, a as int, c as int, tot.cnt@[g], tot.sum@[g], tot.abs@[g], tot.ovf@[g]));
        }
        gi = gi + 1;
    }
}

/// `n` copies of the qualifying-list vectors for one task.
fn copy_i64s(v: &Vec<i64>) -> (r: Vec<i64>)
    ensures r@ == v@,
{
    let mut r: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
        proof {
            assert(r@ =~= v@.subrange(0, i as int));
        }
    }
    proof {
        assert(v@.subrange(0, v@.len() as int) =~= v@);
    }
    r
}

fn copy_usizes(v: &Vec<usize>) -> (r: Vec<usize>)
    ensures r@ == v@,
{
    let mut r: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
        proof {
            assert(r@ =~= v@.subrange(0, i as int));
        }
    }
    proof {
        assert(v@.subrange(0, v@.len() as int) =~= v@);
    }
    r
}

/// Run the scan on at most `workers` threads: the totals over every stored lineitem row.
pub fn run_scan(t: ScanCtx, qkey: &Vec<i64>, qgrp: &Vec<usize>, oc: &OrdCols, p0: usize, p1: usize, ng: usize,
    cm: Arc<Vec<Vec<u64>>>, cmd: Div, sm: Arc<Vec<Vec<u64>>>, smd: Div, use_map: bool,
    workers: usize, dispatch: &mut Dispatch) -> (r: Result<Totals, WorkerFailure>)
    requires
        map_ok(t, qkey@, (*cm)@, cmd, (*sm)@, smd, use_map),
        t.wf(),
        qlist_ok(t.rs@, t.prm@, qkey@, qgrp@, t.qrow@, t.gnames@),
        ng == t.gnames@.len(),
        1 <= workers <= MAX_WORKERS,
        range_ok(*oc, t.lo_day, t.hi_day, p0 as int, p1 as int),
        oc.n_o == t.n_o, oc.od_c == t.od_c, oc.od_b == t.od_b, oc.div == t.odiv,
    ensures r matches Ok(tot) ==> totals_on(t, tot, 0, t.n_l as int),
{
    // the ranges: orders positions (clustered) or lineitem rows
    let (base, span) = if t.clustered { (p0, p1 - p0) } else { (0, t.n_l) };
    let parts = workers;
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut k: usize = 0;
    while k < parts
        invariant
            t.wf(),
            qlist_ok(t.rs@, t.prm@, qkey@, qgrp@, t.qrow@, t.gnames@),
            map_ok(t, qkey@, (*cm)@, cmd, (*sm)@, smd, use_map),
            ng == t.gnames@.len(),
            1 <= parts <= MAX_WORKERS,
            k <= parts,
            t.clustered ==> base + span <= t.n_o,
            !t.clustered ==> base == 0 && span == t.n_l,
            tasks@.len() == k,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre() && tasks@[i].ctx == t
                && tasks@[i].pa == base + range_at(span as int, parts as int, i)
                && tasks@[i].pb == base + range_at(span as int, parts as int, i + 1),
        decreases parts - k,
    {
        let a = range_start(span, parts, k);
        let b = range_start(span, parts, k + 1);
        proof {
            lemma_range_at(span as int, parts as int, k as int, k as int + 1);
            lemma_range_at(span as int, parts as int, k as int + 1, parts as int);
        }
        let task = ScanTask {
            ctx: t,
            qkey: copy_i64s(qkey),
            qgrp: copy_usizes(qgrp),
            cm: cm.clone(),
            cmd,
            sm: sm.clone(),
            smd,
            use_map,
            vbuf: filled(4096, 0u8),
            lp: filled(4096, 0usize),
            obuf: filled(4096, 0u8),
            hb: filled(4096, 0usize),
            hg: filled(4096, 0usize),
            pa: base + a,
            pb: base + b,
            cnt: filled(ng, 0usize),
            sum: filled(ng, 0i128),
            abs: filled(ng, 0u128),
            ovf: filled(ng, false),
        };
        tasks.push(task);
        k = k + 1;
    }
    let ghost tk = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    // merge in range order
    let mut tot = Totals { cnt: filled(ng, 0usize), sum: filled(ng, 0i128), abs: filled(ng, 0u128), ovf: filled(ng, false) };
    if outs.len() == 0 {
        return Ok(tot);
    }
    let a0 = outs[0].ja;
    proof {
        assert(tk[0].post(outs@[0]));
        assert forall|gi: int| 0 <= gi < ng implies
            #[trigger] t.acc_ok(gi, a0 as int, a0 as int, tot.cnt@[gi], tot.sum@[gi], tot.abs@[gi], tot.ovf@[gi]) by {
            assert forall|m: int| #[trigger] t.lsum(gi, m, a0 as int, a0 as int) == 0 by {
                lemma_sum_range_empty(t.lrows@, contrib_fn(t.rs@, t.prm@, gkey(t.gnames@, gi), m), a0 as int);
            }
        }
    }
    let mut i: usize = 0;
    let mut cur: usize = a0;
    while i < outs.len()
        invariant
            t.wf(),
            ng == t.gnames@.len(),
            outs@.len() == parts, tk.len() == parts, 1 <= parts,
            forall|x: int| 0 <= x < parts ==> #[trigger] tk[x].post(outs@[x]),
            forall|x: int| 0 <= x < parts ==> (#[trigger] tk[x]).ctx == t
                && tk[x].pa == base + range_at(span as int, parts as int, x)
                && tk[x].pb == base + range_at(span as int, parts as int, x + 1),
            i <= parts,
            a0 == outs@[0].ja,
            a0 <= cur <= t.n_l,
            i < parts ==> cur == outs@[i as int].ja,
            i == parts ==> cur == outs@[parts - 1].jb,
            totals_on(t, tot, a0 as int, cur as int),
        decreases parts - i,
    {
        let ja = outs[i].ja;
        let jb = outs[i].jb;
        proof {
            assert(tk[i as int].post(outs@[i as int]));
        }
        merge_task(&t, &mut tot, &outs[i], a0, ja, jb);
        proof {
            if i + 1 < parts {
                assert(tk[i as int + 1].post(outs@[i as int + 1]));
                assert(tk[i as int].pb == tk[i as int + 1].pa);
                if t.clustered {
                    lemma_split_unique(t, tk[i as int].pb as int, jb as int, outs@[i as int + 1].ja as int);
                }
            }
        }
        cur = jb;
        i = i + 1;
    }
    // rows outside the scanned range contribute nothing
    proof {
        let last = (parts - 1) as int;
        assert(tk[0].post(outs@[0]));
        assert(tk[last].post(outs@[last]));
        lemma_range_at(span as int, parts as int, 0, parts as int);
        assert(tk[0].pa == base);
        assert(tk[last].pb == base + span);
        let a1 = cur as int;
        assert forall|gi: int| 0 <= gi < ng implies
            #[trigger] t.acc_ok(gi, 0, t.n_l as int, tot.cnt@[gi], tot.sum@[gi], tot.abs@[gi], tot.ovf@[gi]) by {
            let k = gkey(t.gnames@, gi);
            assert(t.acc_ok(gi, a0 as int, a1, tot.cnt@[gi], tot.sum@[gi], tot.abs@[gi], tot.ovf@[gi]));
            assert forall|m: int| #[trigger] t.lsum(gi, m, 0, t.n_l as int) == t.lsum(gi, m, a0 as int, a1) by {
                let f = contrib_fn(t.rs@, t.prm@, k, m);
                lemma_sum_range_split(t.lrows@, f, 0, a0 as int, t.n_l as int);
                lemma_sum_range_split(t.lrows@, f, a0 as int, a1, t.n_l as int);
                if t.clustered {
                    assert forall|j: int| 0 <= j < a0 implies f(#[trigger] t.lrows@[j]) == 0 by {
                        assert(t.split_at(base as int, a0 as int));
                        lemma_outside_zero(t, *oc, p0 as int, p1 as int, j, k);
                    }
                    assert forall|j: int| a1 <= j < t.n_l implies f(#[trigger] t.lrows@[j]) == 0 by {
                        assert(t.split_at((base + span) as int, a1));
                        lemma_outside_zero(t, *oc, p0 as int, p1 as int, j, k);
                    }
                }
                lemma_sum_range_zero(t.lrows@, f, 0, a0 as int);
                lemma_sum_range_zero(t.lrows@, f, a1, t.n_l as int);
            }
            assert(t.lsum(gi, 0, 0, t.n_l as int) == t.lsum(gi, 0, a0 as int, a1));
            assert(t.lsum(gi, 1, 0, t.n_l as int) == t.lsum(gi, 1, a0 as int, a1));
            assert(t.lsum(gi, 2, 0, t.n_l as int) == t.lsum(gi, 2, a0 as int, a1));
        }
    }
    Ok(tot)
}

} // verus!
