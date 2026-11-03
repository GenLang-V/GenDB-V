//! The scan pass: one parallel task per worker scans a range of partsupp (`pspass::ps_range`) and a range of
//! lineitem (`linepass::line_range`), both against the key bitmaps of the matching parts, writing both outputs into
//! `nb` part-key buckets (`bucket`). Task `t` of `nt` takes the `t`-th even split of each table (`split`), so
//! bucket `u` of all tasks, in task order, holds the matching partsupp rows and the recorded lineitem rows of bucket
//! `u` of the whole tables (`scan_all`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::tables::*;
use crate::agent::cols::*;
use crate::agent::keys::*;
use crate::agent::pspass::*;
use crate::agent::linepass::*;
use crate::agent::bucket::*;
use crate::agent::common::split::*;
use crate::agent::common::bigzero::{zeroed_i64, zeroed_u32};

verus! {

/// The output of one scan task: the matching partsupp triples and the lineitem records in buckets, `nb` regions of
/// `cp` (`cr`) triples with the bucket sizes `bnp` (`bnr`). `fit` is false when a bucket outgrew its region (then
/// nothing is claimed about the buckets).
pub struct ScanOut {
    pub bps: Vec<i64>,
    pub bnp: Vec<usize>,
    pub cp: usize,
    pub brec: Vec<i64>,
    pub bnr: Vec<usize>,
    pub cr: usize,
    pub fit: bool,
}

/// Partsupp range `t` of `nt`.
pub open spec fn ps_lo(sv: StoresView, nt: int, t: int) -> int { split(n_ps(sv) as int, nt, t) }
/// Lineitem range `t` of `nt`.
pub open spec fn li_lo(sv: StoresView, nt: int, t: int) -> int { split(n_l(sv) as int, nt, t) }

/// The buckets of task `t` of `nt`: its partsupp rows and its lineitem records of each bucket.
pub open spec fn scan_ok(o: ScanOut, nt: int, t: int, sv: StoresView, ps: Seq<Literal>, keys: Seq<int>, dlo: int, dhi: int,
    nb: int, bm: u64) -> bool {
    o.fit ==> {
        &&& bps_ok(o.bps@, o.bnp@, o.cp as int, nb, sv, ps, bm, ps_lo(sv, nt, t), ps_lo(sv, nt, t + 1))
        &&& brec_ok(o.brec@, o.bnr@, o.cr as int, nb, sv, dlo, dhi, keys, bm, li_lo(sv, nt, t), li_lo(sv, nt, t + 1))
    }
}

/// The outputs of all `nt` tasks.
pub open spec fn scan_all(outs: Seq<ScanOut>, nt: int, sv: StoresView, ps: Seq<Literal>, keys: Seq<int>, dlo: int, dhi: int,
    nb: int, bm: u64) -> bool {
    &&& outs.len() == nt && 1 <= nt
    &&& forall|t: int| 0 <= t < nt ==> #[trigger] scan_ok(outs[t], nt, t, sv, ps, keys, dlo, dhi, nb, bm)
}

/// Bucket regions for `rows` input rows split `nb` ways: `cap` triples each (`rows / per + 4096`, or 0 when that is
/// too large), and the buffer length `3 * cap * nb`. Partsupp is stored in part-key order, so one task's partsupp rows
/// fall into one or two buckets (`per` = 8); lineitem rows spread over all buckets (`per` = `2 nb`).
pub fn bucket_cap(rows: usize, per: usize, nb: usize) -> (r: (usize, usize))
    requires 1 <= per, 1 <= nb <= 64,
    ensures r.1 as int == 3 * r.0 * nb,
{
    let q = rows / per;
    if q <= usize::MAX / 192 - 4096 {
        let cap = q + 4096;
        proof {
            assert(3 * cap * nb <= usize::MAX) by (nonlinear_arith)
                requires 0 <= cap <= usize::MAX / 192, 1 <= nb <= 64;
        }
        let len = 3 * cap * nb;
        assert(len as int == 3 * cap * nb);
        (cap, len)
    } else {
        assert(3 * 0 * nb == 0) by (nonlinear_arith);
        (0, 0)
    }
}

/// One task of the scan pass.
pub struct ScanTask {
    pub pspk: &'static [i64],
    pub pssk: &'static [i64],
    pub psaq: &'static [i64],
    pub nps: usize,
    pub plo: usize,
    pub phi: usize,
    pub lpk: &'static [i64],
    pub lsk: &'static [i64],
    pub lsd: &'static [i32],
    pub lqt: &'static [i128],
    pub nl: usize,
    pub llo: usize,
    pub lhi: usize,
    pub cand: Vec<u32>,
    pub nb: usize,
    pub bm: u64,
    pub cp: usize,
    pub bps: Vec<i64>,
    pub bnp: Vec<usize>,
    pub cr: usize,
    pub brec: Vec<i64>,
    pub bnr: Vec<usize>,
    pub kb: Arc<KeyBits>,
    pub dlo: i32,
    pub dhi: i32,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
    pub keys: Ghost<Seq<int>>,
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        &&& ps_cols_ok(self.pspk, self.pssk, self.psaq, self.nps, self.sv@)
        &&& line_cols_ok(self.lpk, self.lsk, self.lsd, self.lqt, self.nl, self.sv@)
        &&& kb_ok(*self.kb, self.keys@) && keys_decide(self.keys@, self.sv@, self.ps@)
        &&& self.plo <= self.phi <= self.nps
        &&& self.llo <= self.lhi <= self.nl && self.cand@.len() >= CH
        &&& 1 <= self.nb <= 64
        &&& self.bps@.len() >= 3 * self.cp * self.nb && self.bnp@.len() >= self.nb
        &&& self.brec@.len() >= 3 * self.cr * self.nb && self.bnr@.len() >= self.nb
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        &&& out.cp == self.cp && out.cr == self.cr
        &&& out.fit ==> {
            &&& bps_ok(out.bps@, out.bnp@, self.cp as int, self.nb as int, self.sv@, self.ps@, self.bm, self.plo as int, self.phi as int)
            &&& brec_ok(out.brec@, out.bnr@, self.cr as int, self.nb as int, self.sv@, self.dlo as int, self.dhi as int, self.keys@,
                    self.bm, self.llo as int, self.lhi as int)
        }
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.llo as u64, self.lhi as u64)
    }

    fn run(self) -> (out: ScanOut) {
        let ScanTask { pspk, pssk, psaq, nps, plo, phi, lpk, lsk, lsd, lqt, nl, llo, lhi, cand, nb, bm, cp, bps, bnp,
            cr, brec, bnr, kb, dlo, dhi, sv, ps, keys } = self;
        let kbr: &KeyBits = &*kb;
        let mut cand = cand;
        let mut bps = bps;
        let mut bnp = bnp;
        let mut brec = brec;
        let mut bnr = bnr;
        let fp = ps_range(pspk, pssk, psaq, nps, kbr, plo, phi, nb, bm, cp, &mut bps, &mut bnp, Ghost(sv@), Ghost(ps@), Ghost(keys@));
        let fr = if fp {
            line_range(lpk, lsk, lsd, lqt, nl, kbr, dlo, dhi, llo, lhi, nb, bm, cr, &mut brec, &mut bnr, &mut cand, Ghost(sv@), Ghost(keys@))
        } else {
            false
        };
        ScanOut { bps, bnp, cp, brec, bnr, cr, fit: fp && fr }
    }
}

/// The scan pass over both tables by `nt` parallel tasks, with `nb` part-key buckets (multiplier `bm`).
pub fn scan_pass(c: &Cols, kb: Arc<KeyBits>, dlo: i32, dhi: i32, nt: usize, nb: usize, bm: u64, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(keys): Ghost<Seq<int>>) -> (r: Result<Vec<ScanOut>, WorkerFailure>)
    requires
        cols_ok(*c, sv), domains_ok(sv), 1 <= nt <= MAX_WORKERS, kb_ok(*kb, keys), keys_decide(keys, sv, ps),
        c.nl <= usize::MAX / 4, c.nps <= usize::MAX / 4, 1 <= nb <= 64,
    ensures
        r matches Ok(outs) ==> scan_all(outs@, nt as int, sv, ps, keys, dlo as int, dhi as int, nb as int, bm),
{
    let nps = c.nps;
    let nl = c.nl;
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut t: usize = 0;
    while t < nt
        invariant
            cols_ok(*c, sv), domains_ok(sv), nps == c.nps, nl == c.nl, 1 <= nt <= MAX_WORKERS, t <= nt, tasks@.len() == t,
            nl <= usize::MAX / 4, nps <= usize::MAX / 4,
            kb_ok(*kb, keys), keys_decide(keys, sv, ps), 1 <= nb <= 64,
            forall|i: int| 0 <= i < t ==> (#[trigger] tasks@[i]).pre()
                && tasks@[i].plo as int == ps_lo(sv, nt as int, i) && tasks@[i].phi as int == ps_lo(sv, nt as int, i + 1)
                && tasks@[i].llo as int == li_lo(sv, nt as int, i) && tasks@[i].lhi as int == li_lo(sv, nt as int, i + 1)
                && tasks@[i].sv@ == sv && tasks@[i].ps@ == ps && tasks@[i].keys@ == keys
                && tasks@[i].dlo == dlo && tasks@[i].dhi == dhi && tasks@[i].nb == nb && tasks@[i].bm == bm,
        decreases nt - t,
    {
        let plo = split_exec(nps, nt, t);
        let phi = split_exec(nps, nt, t + 1);
        let llo = split_exec(nl, nt, t);
        let lhi = split_exec(nl, nt, t + 1);
        proof {
            lemma_split(nps as int, nt as int, t as int, t as int + 1);
            lemma_split(nl as int, nt as int, t as int, t as int + 1);
        }
        let (cp, lp) = bucket_cap(phi - plo, 8, nb);
        let (cr, lr) = bucket_cap(lhi - llo, 2 * nb, nb);
        let task = ScanTask {
            pspk: c.pspk, pssk: c.pssk, psaq: c.psaq, nps, plo, phi,
            lpk: c.lpk, lsk: c.lsk, lsd: c.lsd, lqt: c.lqt, nl, llo, lhi, cand: zeroed_u32(CH),
            nb, bm, cp, bps: zeroed_i64(lp), bnp: vec![0usize; nb], cr, brec: zeroed_i64(lr), bnr: vec![0usize; nb],
            kb: kb.clone(), dlo, dhi, sv: Ghost(sv), ps: Ghost(ps), keys: Ghost(keys),
        };
        tasks.push(task);
        t = t + 1;
    }
    let ghost tasks_v = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => { return Err(e); },
    };
    proof {
        assert forall|j: int| 0 <= j < nt implies #[trigger] scan_ok(outs@[j], nt as int, j, sv, ps, keys, dlo as int, dhi as int,
            nb as int, bm) by {
            assert(tasks_v[j].post(outs@[j]));
        }
    }
    Ok(outs)
}

} // verus!
