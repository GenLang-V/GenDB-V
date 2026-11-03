//! Running phase B over all lineitem rows: `nt` tasks over consecutive ranges of lineitem rows (`scan::LineTask`),
//! then the per-task accumulators merged group by group (`totals_ok`: the group sums over all lineitem rows). The
//! fast mode needs each order chunk's list of qualifying keys (`qkeys`); the slow mode computes every row from
//! scratch.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::put;
use crate::agent::model::*;
use crate::agent::contrib::*;
use crate::agent::rows::*;
use crate::agent::qkeys::*;
use crate::agent::scan::*;
use crate::agent::codes::lemma_chunk;
use crate::agent::common::lookup::lower_bound;
use crate::agent::common::exact_sum::*;

verus! {

/// Every group accumulator holds its group's sums over all lineitem rows.
pub open spec fn totals_ok(t: Seq<Acc>, sh: Shared, x: Ctx) -> bool {
    &&& t.len() == sh.ng
    &&& forall|g: int| 0 <= g < sh.ng ==> acc_ok(#[trigger] t[g],
        gsum_r(x.sv, x.rp, x.pd, x.t, sh.gids@, g, 0, nl(x.sv) as int),
        gabs_r(x.sv, x.rp, x.pd, x.t, sh.gids@, g, 0, nl(x.sv) as int),
        gcnt_r(x.sv, x.rp, x.pd, x.t, sh.gids@, g, 0, nl(x.sv) as int))
}

/// `n` zero accumulators.
fn zeros(n: usize) -> (v: Vec<Acc>)
    ensures v@.len() == n, forall|g: int| 0 <= g < n ==> acc_ok(#[trigger] v@[g], 0, 0, 0),
{
    let mut v: Vec<Acc> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n, v@.len() == i, forall|g: int| 0 <= g < i ==> acc_ok(#[trigger] v@[g], 0, 0, 0),
        decreases n - i,
    {
        v.push(acc_zero());
        i = i + 1;
    }
    v
}

/// Runs phase B with `nt` tasks. Fast mode: task `t` takes order chunk `t`'s key list and the lineitem rows from
/// the previous task's end to the first row whose key is not below the next order chunk's first key (a binary
/// search that only places the boundary: the ranges partition the lineitem rows whatever it returns). Slow mode:
/// equal ranges.
pub fn scan_all(sh: &Arc<Shared>, chunks: Vec<ChunkKeys>, fast: bool, nt: usize, dispatch: &mut Dispatch, Ghost(x): Ghost<Ctx>)
    -> (r: Result<Vec<Acc>, WorkerFailure>)
    requires
        shared_ok(**sh, x), 1 <= nt <= MAX_WORKERS,
        fast ==> sh.fast && nt <= sh.c.no && chunks@.len() == nt && forall|t: int| 0 <= t < nt ==>
            chunk_ok(x, (#[trigger] chunks@[t]).keys@, chunks@[t].codes@, chunks@[t].n as int, chunks@[t].lo as int, chunks@[t].hi as int),
    ensures r matches Ok(t) ==> totals_ok(t@, **sh, x),
{
    let shr: &Shared = &**sh;
    let ghost sv = x.sv;
    let nl = shr.c.nl;
    let no = shr.c.no;
    let ng = shr.ng;
    let lok = shr.c.lok;
    let ook = shr.c.ook;
    assert(lok@.len() == nl && ook@.len() == no);
    let ch = nl / nt;
    let och = no / nt;
    let ghost orig = chunks@;
    let mut chunks = chunks;
    let mut tasks: Vec<LineTask> = Vec::new();
    let mut ca: usize = 0;
    let ghost mut cas: Seq<int> = seq![0int];
    let mut t: usize = 0;
    while t < nt
        invariant
            shared_ok(*shr, x), shr == &**sh, sv == x.sv, 1 <= nt <= MAX_WORKERS, t <= nt,
            ch == nl / nt, och == no / nt, nl == shr.c.nl, no == shr.c.no, ng == shr.ng, lok@.len() == nl, ook@.len() == no,
            fast ==> shr.fast && nt <= no && orig.len() == nt && chunks@ == orig.subrange(t as int, nt as int)
                && forall|w: int| 0 <= w < nt ==> chunk_ok(x, (#[trigger] orig[w]).keys@, orig[w].codes@, orig[w].n as int,
                    orig[w].lo as int, orig[w].hi as int),
            tasks@.len() == t, cas.len() == t + 1, cas[t as int] == ca, cas[0] == 0, ca <= nl,
            forall|u: int| 0 <= u < t ==> #[trigger] cas[u] <= cas[u + 1],
            forall|u: int| 0 <= u < t ==> (#[trigger] tasks@[u]).pre() && *tasks@[u].sh == *shr && tasks@[u].x@ == x
                && tasks@[u].ca == cas[u] && tasks@[u].cb == cas[u + 1],
            t == nt ==> ca == nl,
        decreases nt - t,
    {
        let cb = if t + 1 == nt {
            nl
        } else if fast {
            proof {
                lemma_chunk(t as int, no as int, nt as int);
                assert((t + 1) * och < no) by (nonlinear_arith) requires och == no / nt, 1 <= nt <= no, t + 1 < nt;
            }
            let lb = lower_bound(lok, nl, ook[(t + 1) * och]);
            if lb < ca { ca } else { lb }
        } else {
            proof {
                assert((t + 1) * ch <= nl) by (nonlinear_arith) requires ch == nl / nt, 1 <= nt, t + 1 < nt;
            }
            let e = (t + 1) * ch;
            if e < ca { ca } else { e }
        };
        let task = if fast {
            proof { assert(chunks@[0] == orig[t as int]); }
            let ck = chunks.remove(0);
            proof { assert(chunks@ =~= orig.subrange(t as int + 1, nt as int)); }
            let ChunkKeys { keys, codes, n, lo, hi } = ck;
            LineTask {
                sh: sh.clone(), keys, codes, nk: n, klo: lo, khi: hi, ca, cb, fast,
                buf: Buf { rrow: vec![0usize; CAP], rcode: vec![0u8; CAP], rsc: vec![0u8; CAP], rsk: vec![0i64; CAP], nr: 0 },
                accs: zeros(ng), x: Ghost(x),
            }
        } else {
            LineTask {
                sh: sh.clone(), keys: Vec::new(), codes: Vec::new(), nk: 0, klo: 0, khi: 0, ca, cb, fast,
                buf: Buf { rrow: vec![0usize; CAP], rcode: vec![0u8; CAP], rsc: vec![0u8; CAP], rsk: vec![0i64; CAP], nr: 0 },
                accs: zeros(ng), x: Ghost(x),
            }
        };
        proof { assert(task.pre()); }
        tasks.push(task);
        proof { cas = cas.push(cb as int); }
        ca = cb;
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let mut totals = zeros(ng);
    let mut u: usize = 0;
    while u < nt
        invariant
            shared_ok(*shr, x), sv == x.sv, ng == shr.ng, nl == shr.c.nl,
            u <= nt, outs@.len() == nt, tv.len() == nt, cas.len() == nt + 1, cas[0] == 0, cas[nt as int] == nl,
            forall|w: int| 0 <= w < nt ==> #[trigger] tv[w].post(outs@[w]),
            forall|w: int| 0 <= w < nt ==> *(#[trigger] tv[w]).sh == *shr && tv[w].x@ == x
                && tv[w].ca == cas[w] && tv[w].cb == cas[w + 1],
            forall|w: int| 0 <= w < nt ==> #[trigger] cas[w] <= cas[w + 1],
            totals@.len() == ng,
            forall|g: int| 0 <= g < ng ==> acc_ok(#[trigger] totals@[g],
                gsum_r(sv, x.rp, x.pd, x.t, shr.gids@, g, 0, cas[u as int]),
                gabs_r(sv, x.rp, x.pd, x.t, shr.gids@, g, 0, cas[u as int]),
                gcnt_r(sv, x.rp, x.pd, x.t, shr.gids@, g, 0, cas[u as int])),
            0 <= cas[u as int],
        decreases nt - u,
    {
        proof { assert(tv[u as int].post(outs@[u as int])); }
        let ghost (lo, hi) = (cas[u as int], cas[u as int + 1]);
        let mut g: usize = 0;
        while g < ng
            invariant
                shared_ok(*shr, x), sv == x.sv, ng == shr.ng, u < nt, outs@.len() == nt, totals@.len() == ng, g <= ng,
                0 <= lo <= hi, lo == cas[u as int], hi == cas[u as int + 1],
                outs@[u as int].accs@.len() == ng,
                forall|h: int| 0 <= h < ng ==> acc_ok(#[trigger] outs@[u as int].accs@[h],
                    gsum_r(sv, x.rp, x.pd, x.t, shr.gids@, h, lo, hi), gabs_r(sv, x.rp, x.pd, x.t, shr.gids@, h, lo, hi),
                    gcnt_r(sv, x.rp, x.pd, x.t, shr.gids@, h, lo, hi)),
                forall|h: int| 0 <= h < ng ==> acc_ok(#[trigger] totals@[h],
                    gsum_r(sv, x.rp, x.pd, x.t, shr.gids@, h, 0, if h < g { hi } else { lo }),
                    gabs_r(sv, x.rp, x.pd, x.t, shr.gids@, h, 0, if h < g { hi } else { lo }),
                    gcnt_r(sv, x.rp, x.pd, x.t, shr.gids@, h, 0, if h < g { hi } else { lo })),
            decreases ng - g,
        {
            let ghost gi = g as int;
            let ghost (s1, m1, n1) = (gsum_r(sv, x.rp, x.pd, x.t, shr.gids@, gi, 0, lo), gabs_r(sv, x.rp, x.pd, x.t, shr.gids@, gi, 0, lo),
                gcnt_r(sv, x.rp, x.pd, x.t, shr.gids@, gi, 0, lo));
            let ghost (s2, m2, n2) = (gsum_r(sv, x.rp, x.pd, x.t, shr.gids@, gi, lo, hi), gabs_r(sv, x.rp, x.pd, x.t, shr.gids@, gi, lo, hi),
                gcnt_r(sv, x.rp, x.pd, x.t, shr.gids@, gi, lo, hi));
            let ghost t0 = totals@;
            let mut a = Acc { sum: totals[g].sum, mass: totals[g].mass, cnt: totals[g].cnt, over: totals[g].over };
            acc_merge(&mut a, &outs[u].accs[g], Ghost(s1), Ghost(m1), Ghost(n1), Ghost(s2), Ghost(m2), Ghost(n2));
            put(&mut totals, g, a);
            proof {
                lemma_range_split(sv, x.rp, x.pd, x.t, shr.gids@, gi, 0, lo, hi);
                assert forall|h: int| 0 <= h < ng implies acc_ok(#[trigger] totals@[h],
                    gsum_r(sv, x.rp, x.pd, x.t, shr.gids@, h, 0, if h < g + 1 { hi } else { lo }),
                    gabs_r(sv, x.rp, x.pd, x.t, shr.gids@, h, 0, if h < g + 1 { hi } else { lo }),
                    gcnt_r(sv, x.rp, x.pd, x.t, shr.gids@, h, 0, if h < g + 1 { hi } else { lo })) by {
                    if h != gi { assert(totals@[h] == t0[h]); }
                }
            }
            g = g + 1;
        }
        u = u + 1;
    }
    Ok(totals)
}

} // verus!
