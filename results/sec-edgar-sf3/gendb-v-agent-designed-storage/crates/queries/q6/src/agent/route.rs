//! Phase B: route the pre pair code of every selected row of one task's filings to the buffer of its bucket (phase C
//! answers each code with its num pair). Routing is only a performance device: phase D checks every answer against
//! the row's own pair code and resolves the pair itself when it does not match, so this task promises nothing about
//! its buffers' contents (it checks every bound it reads at run time).
use vstd::prelude::*;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use crate::agent::filings::{Filing, bucket_of};

verus! {

/// Inputs and buffers of a phase-B task: the task's filings, the bucket cuts, and one buffer per bucket `v`
/// (`bufs[v]`, sized by phase A's counts).
pub struct RouteTask {
    pub filings: Vec<Filing>,
    pub nf: usize,
    pub cuts: Vec<u64>,
    pub nbuckets: usize,
    pub sub_start: &'static [u64],
    pub sub_group: &'static [u64],
    pub nsubs: usize,
    pub group_stmt: &'static [u64],
    pub ngroups: usize,
    pub stmt_key: u64,
    pub pre_tv: &'static [u64],
    pub npre: usize,
    pub bufs: Vec<Vec<u64>>,
    pub lens: Vec<usize>,
}

pub struct RouteOut {
    pub filings: Vec<Filing>,
    pub nf: usize,
    pub bufs: Vec<Vec<u64>>,
    pub lens: Vec<usize>,
}

impl WorkerTask for RouteTask {
    type Output = RouteOut;

    open spec fn pre(&self) -> bool {
        &&& self.nf <= self.filings@.len()
        &&& self.nbuckets >= 1 && self.cuts@.len() == self.nbuckets + 1
        &&& self.sub_start@.len() == self.nsubs + 1 && self.sub_group@.len() == self.nsubs
        &&& self.group_stmt@.len() == self.ngroups && self.pre_tv@.len() == self.npre
        &&& self.bufs@.len() == self.nbuckets && self.lens@.len() == self.nbuckets
        &&& forall|v: int| 0 <= v < self.nbuckets ==> #[trigger] self.lens@[v] == 0
    }

    open spec fn post(&self, out: RouteOut) -> bool {
        &&& out.filings@ == self.filings@
        &&& out.nf == self.nf
        &&& out.bufs@.len() == self.nbuckets && out.lens@.len() == self.nbuckets
        &&& forall|v: int| 0 <= v < self.nbuckets ==> #[trigger] out.lens@[v] <= out.bufs@[v]@.len()
    }

    fn declared_rows(&self) -> (u64, u64) {
        (0, self.nf as u64)
    }

    fn run(self) -> (out: RouteOut) {
        let mut t = self;
        let mut fi: usize = 0;
        while fi < t.nf
            invariant
                t.nf <= t.filings@.len(), t.filings@ == self.filings@, t.nf == self.nf,
                t.nbuckets == self.nbuckets, t.nbuckets >= 1, t.cuts@.len() == t.nbuckets + 1,
                t.sub_start@.len() == t.nsubs + 1, t.sub_group@.len() == t.nsubs,
                t.group_stmt@.len() == t.ngroups, t.pre_tv@.len() == t.npre,
                t.bufs@.len() == t.nbuckets, t.lens@.len() == t.nbuckets,
            decreases t.nf - fi,
        {
            let f = t.filings[fi];
            if f.sa <= f.sb && f.sb <= t.nsubs as u64 {
                let mut s = f.sa as usize;
                let sb = f.sb as usize;
                while s < sb
                    invariant
                        t.nf <= t.filings@.len(), t.filings@ == self.filings@, t.nf == self.nf,
                        t.nbuckets == self.nbuckets, t.nbuckets >= 1, t.cuts@.len() == t.nbuckets + 1,
                        t.sub_start@.len() == t.nsubs + 1, t.sub_group@.len() == t.nsubs,
                        t.group_stmt@.len() == t.ngroups, t.pre_tv@.len() == t.npre,
                        t.bufs@.len() == t.nbuckets, t.lens@.len() == t.nbuckets,
                        sb <= t.nsubs,
                    decreases sb - s,
                {
                    let g = t.sub_group[s];
                    if g < t.ngroups as u64 && t.group_stmt[g as usize] == t.stmt_key {
                        let q0 = t.sub_start[s];
                        let q1 = t.sub_start[s + 1];
                        if q0 <= q1 && q1 <= t.npre as u64 {
                            let mut q = q0 as usize;
                            let qe = q1 as usize;
                            while q < qe
                                invariant
                                    t.nf <= t.filings@.len(), t.filings@ == self.filings@, t.nf == self.nf,
                                    t.nbuckets == self.nbuckets, t.nbuckets >= 1, t.cuts@.len() == t.nbuckets + 1,
                                    t.sub_start@.len() == t.nsubs + 1, t.sub_group@.len() == t.nsubs,
                                    t.group_stmt@.len() == t.ngroups, t.pre_tv@.len() == t.npre,
                                    t.bufs@.len() == t.nbuckets, t.lens@.len() == t.nbuckets,
                                    qe <= t.npre, sb <= t.nsubs, s < sb,
                                decreases qe - q,
                            {
                                let c = t.pre_tv[q];
                                let v = bucket_of(&t.cuts, t.nbuckets, c);
                                let k = t.lens[v];
                                if k < t.bufs[v].len() {
                                    put(&mut t.lens, v, k + 1);
                                    {
                                        let bv = vstd::std_specs::vec::vec_index_mut(&mut t.bufs, v);
                                        put(bv, k, c);
                                    }
                                }
                                q = q + 1;
                            }
                        }
                    }
                    s = s + 1;
                }
            }
            fi = fi + 1;
        }
        // no recorded length beyond its buffer
        let mut v: usize = 0;
        while v < t.nbuckets
            invariant
                t.bufs@.len() == t.nbuckets, t.lens@.len() == t.nbuckets, v <= t.nbuckets,
                t.nbuckets == self.nbuckets, t.filings@ == self.filings@, t.nf == self.nf,
                forall|x: int| 0 <= x < v ==> #[trigger] t.lens@[x] <= t.bufs@[x]@.len(),
            decreases t.nbuckets - v,
        {
            let n = t.bufs[v].len();
            if t.lens[v] > n {
                put(&mut t.lens, v, n);
            }
            v = v + 1;
        }
        RouteOut { filings: t.filings, nf: t.nf, bufs: t.bufs, lens: t.lens }
    }
}

} // verus!
