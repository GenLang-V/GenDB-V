//! Q7 scan task over the lineitem groups `[g0, g1)` (model: `super::model`). Per group, the shipdate zone map skips
//! groups outside the window and marks groups inside it; the lines are then taken in batches of `BATCH`:
//! - phase A walks the lines, tracks a guess of the stored orders row of each line (one step per line with
//!   `l_linenumber = 1`: lines are stored grouped by order, in orders order), and keeps every line in the window
//!   whose supplier's nation has a class as a candidate (line, guess, supplier class). Every other line is in no
//!   group, so the candidates' sums equal the batch's sums (`lr_eq`);
//! - phase B looks up each candidate's order (the guess when it holds the line's order key, else the key index),
//!   its customer's class, and adds the line to its group (count, sum, absolute mass; `over` when a mass would
//!   pass `i128::MAX`).
//! A wrong guess only costs a key-index search: every lookup is checked.
//! When the storage's co-clustering flag holds and the supplier and customer keys are dense, each batch is first
//! taken by the supplier-first path over the l_orderkey runs (`super::sfast`); the passes above take a batch it
//! leaves (after a failed check).
use vstd::prelude::*;
use crate::gendb_entry::parallel::WorkerTask;
use super::model::*;
use super::lookup::*;
use super::dates::*;
use super::cmap::*;
use super::sfast::*;
use super::common::incseq::*;
use super::runs::lemma_runs_inc;
use std::sync::Arc;

verus! {

/// Lines per batch (candidate buffer size).
pub const BATCH: usize = 4096;

/// Orders rows an orders cursor moves per candidate before the key index is asked.
pub const STEPS: usize = 64;

// ------------------------------------------------------------------------------------------------ list sums

/// Count of the candidate lines `js[0 .. n)` in group `gi`.
pub open spec fn lcnt(c: Cols, x: Ctx, gi: int, js: Seq<usize>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { lcnt(c, x, gi, js, n - 1) + if l_grp(c, x, js[n - 1] as int) == gi { 1int } else { 0 } }
}

pub open spec fn lsum(c: Cols, x: Ctx, gi: int, js: Seq<usize>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { lsum(c, x, gi, js, n - 1) + if l_grp(c, x, js[n - 1] as int) == gi { l_vol(c, js[n - 1] as int) } else { 0 } }
}

pub open spec fn lmass(c: Cols, x: Ctx, gi: int, js: Seq<usize>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { lmass(c, x, gi, js, n - 1) + if l_grp(c, x, js[n - 1] as int) == gi { iabs(l_vol(c, js[n - 1] as int)) } else { 0 } }
}

/// List sums only read the first `n` entries.
pub proof fn lemma_l_ext(c: Cols, x: Ctx, gi: int, a: Seq<usize>, b: Seq<usize>, n: int)
    requires 0 <= n <= a.len(), n <= b.len(), forall|i: int| 0 <= i < n ==> a[i] == b[i],
    ensures
        lcnt(c, x, gi, a, n) == lcnt(c, x, gi, b, n),
        lsum(c, x, gi, a, n) == lsum(c, x, gi, b, n),
        lmass(c, x, gi, a, n) == lmass(c, x, gi, b, n),
    decreases n,
{
    if n > 0 {
        lemma_l_ext(c, x, gi, a, b, n - 1);
    }
}

/// The candidate list's sums are the range's, for every group.
pub open spec fn lr_eq(c: Cols, x: Ctx, js: Seq<usize>, n: int, a: int, b: int) -> bool {
    forall|gi: int| 0 <= gi < 4 ==> {
        &&& #[trigger] lcnt(c, x, gi, js, n) == rcnt(c, x, gi, a, b)
        &&& lsum(c, x, gi, js, n) == rsum(c, x, gi, a, b)
        &&& lmass(c, x, gi, js, n) == rmass(c, x, gi, a, b)
    }
}

// ------------------------------------------------------------------------------------------------ accumulators

pub open spec fn i128_max() -> int { 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff }

/// The accumulators hold the sums of the lines `[a, b)` plus the candidates `js[0 .. n)`: counts always; sums and
/// masses unless `over`, which means some group's mass passes `i128::MAX`.
pub open spec fn acc_ok(c: Cols, x: Ctx, sums: Seq<i128>, mass: Seq<i128>, cnts: Seq<usize>, over: bool,
    a: int, b: int, js: Seq<usize>, n: int) -> bool
{
    &&& sums.len() == 4 && mass.len() == 4 && cnts.len() == 4
    &&& forall|gi: int| 0 <= gi < 4 ==> #[trigger] cnts[gi] as int == rcnt(c, x, gi, a, b) + lcnt(c, x, gi, js, n)
    &&& !over ==> forall|gi: int| 0 <= gi < 4 ==> #[trigger] sums[gi] as int == rsum(c, x, gi, a, b) + lsum(c, x, gi, js, n)
    &&& !over ==> forall|gi: int| 0 <= gi < 4 ==>
            #[trigger] mass[gi] as int == rmass(c, x, gi, a, b) + lmass(c, x, gi, js, n) && mass[gi] as int <= i128_max()
    &&& over ==> exists|gi: int| 0 <= gi < 4 && #[trigger] rmass(c, x, gi, a, b) + lmass(c, x, gi, js, n) > i128_max()
}

/// List counts and masses are bounded like range ones.
proof fn lemma_l_bounds(c: Cols, x: Ctx, gi: int, js: Seq<usize>, n: int)
    requires 0 <= n,
    ensures
        0 <= lcnt(c, x, gi, js, n) <= n,
        0 <= lmass(c, x, gi, js, n),
        -lmass(c, x, gi, js, n) <= lsum(c, x, gi, js, n) <= lmass(c, x, gi, js, n),
    decreases n,
{
    if n > 0 {
        lemma_l_bounds(c, x, gi, js, n - 1);
    }
}

// ------------------------------------------------------------------------------------------------ groups of rows

/// First stored line of group `g` (clamped to the table).
pub open spec fn jlo(c: Cols, g: int) -> int {
    if g * c.bs_l < c.n_l { g * c.bs_l } else { c.n_l as int }
}

/// Row `j` of group `g` has `j / bs == g`.
pub proof fn lemma_div_group(j: int, bs: int, g: int)
    requires bs >= 1, g * bs <= j < g * bs + bs,
    ensures j / bs == g,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j, bs, g, j - g * bs);
}

pub proof fn lemma_next_group(g: int, bs: int)
    ensures (g + 1) * bs == g * bs + bs,
{
    assert((g + 1) * bs == g * bs + bs) by (nonlinear_arith);
}

pub proof fn lemma_group_nonneg(g: int, bs: int)
    requires g >= 0, bs >= 1,
    ensures g * bs >= 0, g * bs + bs >= g + 1,
{
    assert(g * bs >= 0) by (nonlinear_arith) requires g >= 0, bs >= 1;
    assert(g * bs + bs >= g + 1) by (nonlinear_arith) requires g >= 0, bs >= 1;
}

/// The group shapes the task needs: one base per group, and the last group ends at the table.
pub open spec fn groups_ok(c: Cols) -> bool {
    c.ls_bases@.len() * c.bs_l < c.n_l + c.bs_l
}

// ------------------------------------------------------------------------------------------------ the task

pub struct ScanTask {
    pub cols: Cols,
    pub sh: Shifts,
    pub s_dense: bool,
    pub s_key0: i64,
    pub c_dense: bool,
    pub c_key0: i64,
    pub nk: Vec<i64>,
    pub nc: Vec<u8>,
    pub nt: Vec<u8>,
    pub sm: Arc<Vec<u8>>,
    pub same: bool,
    pub cmv: bool,
    pub cm: Arc<Vec<u32>>,
    pub smv: bool,
    pub sm2: Arc<Vec<u32>>,
    pub g0: usize,
    pub g1: usize,
    pub sums: Vec<i128>,
    pub mass: Vec<i128>,
    pub cnts: Vec<usize>,
    pub cand_j: Vec<usize>,
    pub cand_p: Vec<usize>,
    pub cand_x: Vec<u8>,
    pub lcls: [u8; BATCH],
    pub ccls: [u8; BATCH],
    /// The supplier-first path may run (`sfast_ok`), with the fixed-size supplier class map `sma`.
    pub rf: bool,
    pub sma: Arc<Box<[u32; SMW]>>,
    pub hm: [u64; HW],
    pub x: Ghost<Ctx>,
}

/// What a scan task returns: sums, masses, counts per group, and the overflow flag.
pub type ScanOut = (Vec<i128>, Vec<i128>, Vec<usize>, bool);

/// The lookup facts every scan of one call shares.
pub open spec fn scan_ok(c: Cols, s: Shifts, sd: bool, sk0: i64, cd: bool, ck0: i64, nk: Seq<i64>, nc: Seq<u8>,
    nt: Seq<u8>, sm: Seq<u8>, x: Ctx) -> bool {
    &&& cols_ok(c)
    &&& keys_ok(c)
    &&& groups_ok(c)
    &&& shifts_ok(c, s)
    &&& s_dense_ok(c, sd, sk0)
    &&& c_dense_ok(c, cd, ck0)
    &&& ncls_ok(x, nk, nc)
    &&& ntab_ok(x, nt)
    &&& smap_ok(c, x, sd, sk0, sm)
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        &&& scan_ok(self.cols, self.sh, self.s_dense, self.s_key0, self.c_dense, self.c_key0, self.nk@, self.nc@, self.nt@, self.sm@, self.x@)
        &&& self.x@.same == self.same
        &&& (self.cmv ==> cmap_ok(self.cols, self.x@, self.c_key0, self.cm@))
        &&& (self.smv ==> smap2_ok(self.cols, self.x@, self.s_key0, self.sm2@))
        &&& (self.rf ==> sfast_ok(self.cols, self.sh, self.s_key0, self.c_key0, self.cm@, self.sm2@, self.sma@, self.x@))
        &&& self.g0 <= self.g1 <= self.cols.ls_bases@.len()
        &&& self.sums@ == seq![0i128, 0, 0, 0]
        &&& self.mass@ == seq![0i128, 0, 0, 0]
        &&& self.cnts@ == seq![0usize, 0, 0, 0]
        &&& self.cand_j@.len() == BATCH
        &&& self.cand_p@.len() == BATCH
        &&& self.cand_x@.len() == BATCH
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        acc_ok(self.cols, self.x@, out.0@, out.1@, out.2@, out.3,
            jlo(self.cols, self.g0 as int), jlo(self.cols, self.g1 as int), Seq::<usize>::empty(), 0)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.g0 as u64, self.g1 as u64)
    }

    fn run(self) -> (out: ScanOut) {
        let c = self.cols;
        let s = self.sh;
        let ghost x = self.x@;
        let (sd, sk0, cd, ck0, same) = (self.s_dense, self.s_key0, self.c_dense, self.c_key0, self.same);
        let (g0, g1) = (self.g0, self.g1);
        let nk_v = self.nk;
        let nc_v = self.nc;
        let nt_v = self.nt;
        let sm_v = self.sm;
        let cmv = self.cmv;
        let cm_v = self.cm;
        let smv = self.smv;
        let sm2_v = self.sm2;
        let nn = nk_v.len();
        let mut sums = self.sums;
        let mut mass = self.mass;
        let mut cnts = self.cnts;
        let mut over = false;
        let mut cand_j = self.cand_j;
        let mut cand_p = self.cand_p;
        let mut cand_x = self.cand_x;
        let mut lcls = self.lcls;
        let mut ccls = self.ccls;
        let mut hm = self.hm;
        let rf0 = self.rf;
        let sma_v = self.sma;
        let lo: i64 = -1826;
        let hi: i64 = -1096;
        let bs = c.bs_l;
        let n_l = c.n_l;
        let ghost a = jlo(c, g0 as int);
        let ghost e = Seq::<usize>::empty();
        // the run cursor at the task's first line (the supplier-first path runs only with one)
        let mut rp: usize = 0;
        let mut rf = false;
        if rf0 && g0 < g1 {
            proof {
                lemma_runs_inc(c);
                lemma_group_nonneg(g0 as int, bs as int);
                assert((g0 as int) * (bs as int) <= 0xffff_ffff_ffff_ffffu128 * 0xffff_ffff_ffff_ffffu128) by (nonlinear_arith)
                    requires 0 <= g0 <= 0xffff_ffff_ffff_ffffu64, 0 <= bs <= 0xffff_ffff_ffff_ffffu64;
            }
            let gbs = g0 as u128 * bs as u128;
            let j0t: u128 = if gbs < n_l as u128 { gbs } else { n_l as u128 };
            if j0t <= 0xffff_ffffu128 {
                match find_le(c.l_st, c.n_st, j0t as u32) {
                    Some(r) => {
                        rp = r;
                        rf = true;
                    },
                    None => {},
                }
            }
        }
        let mut g = g0;
        while g < g1
            invariant
                scan_ok(c, s, sd, sk0, cd, ck0, nk_v@, nc_v@, nt_v@, sm_v@, x),
                cmv ==> cmap_ok(c, x, ck0, cm_v@),
                smv ==> smap2_ok(c, x, sk0, sm2_v@),
                rf ==> sfast_ok(c, s, sk0, ck0, cm_v@, sm2_v@, sma_v@, x),
                rf ==> rp < c.l_st@.len() && c.l_st@[rp as int] <= jlo(c, g as int),
                x.same == same,
                nn == nk_v@.len(),
                g0 <= g <= g1 <= c.ls_bases@.len(),
                bs == c.bs_l, n_l == c.n_l,
                lo == win_lo(), hi == win_hi(),
                a == jlo(c, g0 as int),
                0 <= a <= jlo(c, g as int),
                acc_ok(c, x, sums@, mass@, cnts@, over, a, jlo(c, g as int), e, 0),
                cand_j@.len() == BATCH, cand_p@.len() == BATCH, cand_x@.len() == BATCH,
            decreases g1 - g,
        {
            proof {
                lemma_group_nonneg(g as int, bs as int);
                assert((g as int + 1) * (bs as int) <= c.ls_bases@.len() * (bs as int)) by (nonlinear_arith)
                    requires g < c.ls_bases@.len(), bs >= 1;
                lemma_next_group(g as int, bs as int);
                assert((g as int) * (bs as int) < n_l);
            }
            let gbs = g * bs;
            let j0 = if gbs < n_l { gbs } else { n_l };
            let j1 = if n_l - gbs > bs { gbs + bs } else { n_l };
            proof {
                assert(j0 == jlo(c, g as int));
                assert(j1 == jlo(c, g + 1));
                assert forall|j: int| j0 <= j < j1 implies #[trigger] (j / bs as int) == g by {
                    lemma_div_group(j, bs as int, g as int);
                }
            }
            let zlo = c.ls_bases[g];
            let zhi = c.ls_zmax[g];
            if zlo > hi || zhi < lo {
                // no line of the group is in the window
                proof {
                    assert forall|j: int| j0 <= j < j1 implies #[trigger] l_grp(c, x, j) == -1 by {
                        assert(j / bs as int == g);
                        assert(lship(c, j) <= c.ls_zmax@[j / bs as int]);
                    }
                    assert forall|gi: int| 0 <= gi < 4 implies {
                        &&& rcnt(c, x, gi, j0 as int, j1 as int) == 0
                        &&& rsum(c, x, gi, j0 as int, j1 as int) == 0
                        &&& rmass(c, x, gi, j0 as int, j1 as int) == 0
                    } by {
                        lemma_r_none(c, x, gi, j0 as int, j1 as int);
                    }
                    lemma_acc_extend(c, x, sums@, mass@, cnts@, over, a, j0 as int, j1 as int);
                }
            } else {
                let inside = zlo >= lo && zhi <= hi;
                if rf {
                    // the supplier-first path, batch by batch; a batch it leaves goes to the line-first passes
                    let mut js = j0;
                    while js < j1
                        invariant
                            scan_ok(c, s, sd, sk0, cd, ck0, nk_v@, nc_v@, nt_v@, sm_v@, x),
                            cmv ==> cmap_ok(c, x, ck0, cm_v@),
                            smv ==> smap2_ok(c, x, sk0, sm2_v@),
                            sfast_ok(c, s, sk0, ck0, cm_v@, sm2_v@, sma_v@, x),
                            rp < c.l_st@.len(), c.l_st@[rp as int] <= js,
                            x.same == same,
                            nn == nk_v@.len(),
                            g < c.ls_bases@.len(),
                            j0 <= js <= j1 <= c.n_l,
                            forall|j: int| j0 <= j < j1 ==> #[trigger] (j / c.bs_l as int) == g,
                            inside ==> c.ls_bases@[g as int] >= win_lo() && c.ls_zmax@[g as int] <= win_hi(),
                            bs == c.bs_l,
                            0 <= a <= j0,
                            acc_ok(c, x, sums@, mass@, cnts@, over, a, js as int, e, 0),
                            cand_j@.len() == BATCH, cand_p@.len() == BATCH, cand_x@.len() == BATCH,
                        decreases j1 - js,
                    {
                        let je = if j1 - js > BATCH { js + BATCH } else { j1 };
                        proof {
                            assert forall|j: int| js <= j < je implies #[trigger] (j / c.bs_l as int) == g by {
                                assert(j0 <= j < j1);
                            }
                        }
                        let smr: &[u32; SMW] = &sma_v;
                        let (o, took, rp2) = sfast_batch(&c, s, sk0, ck0, &cm_v, &sm2_v, smr, same, g, js, je, inside, rp,
                            sums, mass, cnts, over, &mut lcls, &mut hm, &mut ccls, &mut cand_j, &mut cand_p, &mut cand_x,
                            Ghost(x), Ghost(a));
                        sums = o.0;
                        mass = o.1;
                        cnts = o.2;
                        over = o.3;
                        rp = rp2;
                        if !took {
                            let (sums2, mass2, cnts2, over2) = scan_group(&c, s, sd, sk0, cd, ck0, &nk_v, &nc_v, &nt_v, &sm_v, nn, same, cmv, &cm_v, smv, &sm2_v,
                                g, js, je, inside, sums, mass, cnts, over, &mut cand_j, &mut cand_p, &mut cand_x, &mut lcls, &mut ccls, Ghost(x), Ghost(a));
                            sums = sums2;
                            mass = mass2;
                            cnts = cnts2;
                            over = over2;
                        }
                        js = je;
                    }
                } else {
                    let (sums2, mass2, cnts2, over2) = scan_group(&c, s, sd, sk0, cd, ck0, &nk_v, &nc_v, &nt_v, &sm_v, nn, same, cmv, &cm_v, smv, &sm2_v,
                        g, j0, j1, inside, sums, mass, cnts, over, &mut cand_j, &mut cand_p, &mut cand_x, &mut lcls, &mut ccls, Ghost(x), Ghost(a));
                    sums = sums2;
                    mass = mass2;
                    cnts = cnts2;
                    over = over2;
                }
            }
            g = g + 1;
        }
        (sums, mass, cnts, over)
    }
}

/// Lines `[b, b2)` in no group extend the accumulators' range.
pub proof fn lemma_acc_extend(c: Cols, x: Ctx, sums: Seq<i128>, mass: Seq<i128>, cnts: Seq<usize>, over: bool, a: int, b: int, b2: int)
    requires
        a <= b <= b2,
        acc_ok(c, x, sums, mass, cnts, over, a, b, Seq::<usize>::empty(), 0),
        forall|gi: int| 0 <= gi < 4 ==> {
            &&& rcnt(c, x, gi, b, b2) == 0
            &&& rsum(c, x, gi, b, b2) == 0
            &&& rmass(c, x, gi, b, b2) == 0
        },
    ensures acc_ok(c, x, sums, mass, cnts, over, a, b2, Seq::<usize>::empty(), 0),
{
    let e = Seq::<usize>::empty();
    assert forall|gi: int| 0 <= gi < 4 implies {
        &&& rcnt(c, x, gi, a, b2) == rcnt(c, x, gi, a, b)
        &&& rsum(c, x, gi, a, b2) == rsum(c, x, gi, a, b)
        &&& rmass(c, x, gi, a, b2) == rmass(c, x, gi, a, b)
    } by {
        lemma_r_split(c, x, gi, a, b, b2);
    }
    assert forall|gi: int| 0 <= gi < 4 implies #[trigger] cnts[gi] as int == rcnt(c, x, gi, a, b2) + lcnt(c, x, gi, e, 0) by {
        assert(cnts[gi] as int == rcnt(c, x, gi, a, b) + lcnt(c, x, gi, e, 0));
    }
    if !over {
        assert forall|gi: int| 0 <= gi < 4 implies #[trigger] sums[gi] as int == rsum(c, x, gi, a, b2) + lsum(c, x, gi, e, 0) by {
            assert(sums[gi] as int == rsum(c, x, gi, a, b) + lsum(c, x, gi, e, 0));
        }
        assert forall|gi: int| 0 <= gi < 4 implies #[trigger] mass[gi] as int == rmass(c, x, gi, a, b2) + lmass(c, x, gi, e, 0) && mass[gi] as int <= i128_max() by {
            assert(sums[gi] as int == rsum(c, x, gi, a, b) + lsum(c, x, gi, e, 0));
        }
    } else {
        let gi = choose|gi: int| 0 <= gi < 4 && #[trigger] rmass(c, x, gi, a, b) + lmass(c, x, gi, e, 0) > i128_max();
        assert(rmass(c, x, gi, a, b2) + lmass(c, x, gi, e, 0) > i128_max());
    }
}

/// The lines of one group `[j0, j1)` (group `g`, which the zone map does not exclude), in batches.
fn scan_group(c: &Cols, s: Shifts, sd: bool, sk0: i64, cd: bool, ck0: i64, nkeys: &Vec<i64>, nclss: &Vec<u8>, nt: &Vec<u8>, sm: &Arc<Vec<u8>>, nn: usize,
    same: bool, cmv: bool, cm: &Vec<u32>, smv: bool, sm2: &Vec<u32>, g: usize, j0: usize, j1: usize, inside: bool,
    sums: Vec<i128>, mass: Vec<i128>, cnts: Vec<usize>, over: bool,
    cand_j: &mut Vec<usize>, cand_p: &mut Vec<usize>, cand_x: &mut Vec<u8>, lcls: &mut [u8; BATCH],
    ccls: &mut [u8; BATCH], Ghost(x): Ghost<Ctx>, Ghost(a): Ghost<int>) -> (r: ScanOut)
    requires
        scan_ok(*c, s, sd, sk0, cd, ck0, nkeys@, nclss@, nt@, sm@, x),
        cmv ==> cmap_ok(*c, x, ck0, cm@),
        smv ==> smap2_ok(*c, x, sk0, sm2@),
        x.same == same,
        nn == nkeys@.len(),
        g < c.ls_bases@.len(),
        j0 <= j1 <= c.n_l,
        forall|j: int| j0 <= j < j1 ==> #[trigger] (j / c.bs_l as int) == g,
        inside ==> c.ls_bases@[g as int] >= win_lo() && c.ls_zmax@[g as int] <= win_hi(),
        0 <= a <= j0,
        acc_ok(*c, x, sums@, mass@, cnts@, over, a, j0 as int, Seq::<usize>::empty(), 0),
        old(cand_j)@.len() == BATCH, old(cand_p)@.len() == BATCH, old(cand_x)@.len() == BATCH,
    ensures
        acc_ok(*c, x, r.0@, r.1@, r.2@, r.3, a, j1 as int, Seq::<usize>::empty(), 0),
        final(cand_j)@.len() == BATCH, final(cand_p)@.len() == BATCH, final(cand_x)@.len() == BATCH,
    no_unwind
{
    let one_code: i64 = if 0 <= c.lln_bases[g] && c.lln_bases[g] <= 1 { 1 - c.lln_bases[g] } else { -1 };
    // dense supplier keys with a last key: the class map answers keys in [sk0, sk_hi]
    let sk_top: i128 = sk0 as i128 + c.n_s as i128 - 1;
    let sdd = sd && c.n_s > 0 && (c.n_s as u64) < 0x4000_0000_0000_0000u64 && sk_top <= 0x7fff_ffff_ffff_ffffi128;
    let sk_hi: i64 = if sdd { sk_top as i64 } else { 0 };
    // the fast path: class maps of dense supplier keys [sk0, sk_hi2] and customer keys [ck0, ck_hi]
    let ck_top: i128 = ck0 as i128 + c.n_c as i128 - 1;
    let fast = cmv && smv && c.n_c > 0 && c.n_c < usize::MAX / 32 && ck_top <= 0x7fff_ffff_ffff_ffffi128
        && c.n_s > 0 && sk_top <= 0x7fff_ffff_ffff_ffffi128 && c.n_o < usize::MAX / 2;
    let ck_hi: i64 = if fast { ck_top as i64 } else { 0 };
    // the group's supplier key base minus sk0 (small: no overflow in the line class pass)
    let off128: i128 = c.lsk_bases[g] as i128 - sk0 as i128;
    let gfast = fast && -0x4000_0000_0000_0000i128 < off128 && off128 < 0x4000_0000_0000_0000i128
        && (c.n_s as u64) < 0x4000_0000_0000_0000u64;
    let off: i64 = if gfast { off128 as i64 } else { 0 };
    let mut sums = sums;
    let mut mass = mass;
    let mut cnts = cnts;
    let mut over = over;
    // the stored orders row of the group's first line seeds the guess (minus one when that line starts its order,
    // since every line with l_linenumber = 1 advances it)
    let mut p: usize = 0;
    // orders cursor of the fast path: row `q` holds (a guess of) the order of the line before the batch, key `kq`
    let n_o = c.n_o;
    let mut q: usize = 0;
    if j0 < j1 {
        proof {
            assert(j0 as int / c.bs_l as int == g as int);
            assert(in_i64(lkey(*c, j0 as int)));
        }
        let k0 = c.lok_bases[g] + c.lok_codes[j0] as i64;
        match order_row(c, s, k0, 0) {
            Some(q0) => {
                p = if q0 > 0 && (c.lln_codes[j0] as i64 == one_code) { q0 - 1 } else { q0 };
                q = p;
            },
            None => {},
        }
    }
    let mut jb = j0;
    while jb < j1
        invariant
            scan_ok(*c, s, sd, sk0, cd, ck0, nkeys@, nclss@, nt@, sm@, x),
            x.same == same,
            nn == nkeys@.len(),
            g < c.ls_bases@.len(),
            j0 <= jb <= j1 <= c.n_l,
            forall|j: int| j0 <= j < j1 ==> #[trigger] (j / c.bs_l as int) == g,
            inside ==> c.ls_bases@[g as int] >= win_lo() && c.ls_zmax@[g as int] <= win_hi(),
            sdd ==> sd && 0 < c.n_s < 0x4000_0000_0000_0000 && sk_hi == sk0 + c.n_s - 1,
            fast ==> 0 < c.n_c < usize::MAX / 32 && ck_hi == ck0 + c.n_c - 1 && cmap_ok(*c, x, ck0, cm@),
            q <= n_o, n_o == c.n_o, fast ==> n_o < usize::MAX / 2,
            fast ==> 0 < c.n_s && smap2_ok(*c, x, sk0, sm2@),
            gfast ==> fast && c.n_s < 0x4000_0000_0000_0000 && off == c.lsk_bases@[g as int] - sk0
                && -0x4000_0000_0000_0000 < off < 0x4000_0000_0000_0000,
            0 <= a <= j0,
            acc_ok(*c, x, sums@, mass@, cnts@, over, a, jb as int, Seq::<usize>::empty(), 0),
            cand_j@.len() == BATCH, cand_p@.len() == BATCH, cand_x@.len() == BATCH,
        decreases j1 - jb,
    {
        let je = if j1 - jb > BATCH { jb + BATCH } else { j1 };
        proof {
            assert forall|j: int| jb <= j < je implies #[trigger] (j / c.bs_l as int) == g by {
                assert(j0 <= j < j1);
            }
        }
        let mut done = false;
        if gfast {
            line_classes(c, sk0, off, sm2, g, jb, je, lcls, Ghost(x));
            let (nc, q2) = pick_lines(c, g, jb, je, q, one_code, lcls, cand_j, cand_p, Ghost(x));
            q = if q2 < n_o { q2 } else { n_o };
            resolve_orders(c, s, ck0, ck_hi, g, nc, cand_j, cand_p, Ghost(x), Ghost(jb as int), Ghost(je as int));
            cust_kernel(cand_p, c.n_c, cm, ccls, nc);
            group_codes(c, ck0, cm, same, g, jb, nc, cand_j, cand_p, lcls, ccls, cand_x, Ghost(x), Ghost(je as int));
            proof {
                lemma_acc_list0(*c, x, sums@, mass@, cnts@, over, a, jb as int, cand_j@);
            }
            let (s2, m2, c2, o2) = add_codes(c, g, nc, cand_j, cand_x, sums, mass, cnts, over,
                Ghost(x), Ghost(a), Ghost(jb as int), Ghost(je as int));
            sums = s2;
            mass = m2;
            cnts = c2;
            over = o2;
            proof {
                lemma_acc_batch(*c, x, sums@, mass@, cnts@, over, a, jb as int, je as int, cand_j@, nc as int);
            }
            done = true;
        }
        if !done {
            let (nc, p2) = phase_a(c, s, sd, sk0, sdd, sk_hi, sm, nt, nkeys, nclss, nn, g, jb, je, inside, one_code, p,
                cand_j, cand_p, cand_x, Ghost(x));
            p = p2;
            phase_b1(c, s, cd, ck0, g, nc, cand_j, cand_p, Ghost(x), Ghost(jb as int), Ghost(je as int));
            proof {
                lemma_acc_list0(*c, x, sums@, mass@, cnts@, over, a, jb as int, cand_j@);
            }
            let (s2, m2, c2, o2) = phase_b2(c, s, nt, nkeys, nclss, nn, same, g, nc, cand_j, cand_p, cand_x,
                sums, mass, cnts, over, Ghost(x), Ghost(a), Ghost(jb as int), Ghost(je as int));
            sums = s2;
            mass = m2;
            cnts = c2;
            over = o2;
            proof {
                lemma_acc_batch(*c, x, sums@, mass@, cnts@, over, a, jb as int, je as int, cand_j@, nc as int);
            }
        }
        jb = je;
    }
    (sums, mass, cnts, over)
}

/// The customer class of the customer of orders row `q`.
pub open spec fn q_cls(c: Cols, x: Ctx, q: int) -> int {
    c_cls(c, x, ocust(c, q))
}

/// The group of line `j` as a code: its group 0..4, or 4 when it is in none.
pub open spec fn g_code(c: Cols, x: Ctx, j: int) -> int {
    if l_grp(c, x, j) >= 0 { l_grp(c, x, j) } else { 4 }
}

/// A line whose order key is held by orders row `q` has that row's customer class.
pub proof fn lemma_line_order(c: Cols, x: Ctx, j: int, q: int)
    requires keys_ok(c), 0 <= q < c.n_o, okey(c, q) == lkey(c, j),
    ensures o_cls(c, x, lkey(c, j)) == q_cls(c, x, q),
{
    let k = lkey(c, j);
    assert(has_o(c, k));
    let w = orow(c, k);
    assert(0 <= w < c.n_o && okey(c, w) == k);
    assert(w == q);
}

/// The supplier class of line `j` when its shipdate is in the window, else 0.
pub open spec fn l_scw(c: Cols, x: Ctx, j: int) -> int {
    if win_lo() <= lship(c, j) <= win_hi() { s_cls(c, x, lsupp(c, j)) } else { 0 }
}

/// The subslice `s[a..b]` (by two `split_at`s, which do not unwind).
pub fn sub_u32(s: &'static [u32], a: usize, b: usize) -> (r: &'static [u32])
    requires a <= b <= s@.len(),
    ensures r@ == s@.subrange(a as int, b as int),
    no_unwind
{
    let (_, tail) = s.split_at(a);
    let (r, _) = tail.split_at(b - a);
    proof {
        assert(r@ =~= s@.subrange(a as int, b as int));
    }
    r
}

/// The subslice `s[a..b]` of a U16 column.
pub fn sub_u16(s: &'static [u16], a: usize, b: usize) -> (r: &'static [u16])
    requires a <= b <= s@.len(),
    ensures r@ == s@.subrange(a as int, b as int),
    no_unwind
{
    let (_, tail) = s.split_at(a);
    let (r, _) = tail.split_at(b - a);
    proof {
        assert(r@ =~= s@.subrange(a as int, b as int));
    }
    r
}

/// The subslice `s[a..b]` of a U8 column.
pub fn sub_u8(s: &'static [u8], a: usize, b: usize) -> (r: &'static [u8])
    requires a <= b <= s@.len(),
    ensures r@ == s@.subrange(a as int, b as int),
    no_unwind
{
    let (_, tail) = s.split_at(a);
    let (r, _) = tail.split_at(b - a);
    proof {
        assert(r@ =~= s@.subrange(a as int, b as int));
    }
    r
}

/// The class of supplier row `r` in a map of `ns` rows, 0 outside the rows.
pub open spec fn cls_of(m: Seq<u32>, ns: int, r: int) -> int {
    if 0 <= r < ns { get2(m[r / 16], r % 16) } else { 0 }
}

/// The class of a line from its supplier key code (row `code + off`) and shipdate code (day `sbase + dcode`): the
/// supplier row's class when the day is in the window, else 0.
pub open spec fn lcw(m: Seq<u32>, ns: int, off: int, sbase: int, code: u32, dcode: u16) -> int {
    let d = sbase + dcode as int;
    if win_lo() <= d <= win_hi() { cls_of(m, ns, code as int + off) } else { 0 }
}

/// `out[t] = lcw(.., sk[t], sd[t])` for `t < n`: branch-free, so it vectorizes (a masked word gather per 8 lines).
#[inline(never)]
fn classes_kernel(sk: &[u32], sd: &[u16], sbase: i64, off: i64, ns: i64, m32: &Vec<u32>, out: &mut [u8], n0: usize)
    requires
        n0 <= sk@.len(), n0 <= sd@.len(), n0 <= old(out)@.len(),
        16 * m32@.len() >= ns, 0 <= ns < 0x4000_0000_0000_0000,
        -0x4000_0000_0000_0000 < off < 0x4000_0000_0000_0000,
        forall|t: int| 0 <= t < n0 ==> in_i64(sbase + #[trigger] sd@[t] as int),
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|t: int| 0 <= t < n0 ==> #[trigger] final(out)@[t] as int == lcw(m32@, ns as int, off as int, sbase as int, sk@[t], sd@[t]),
        forall|t: int| 0 <= t < n0 ==> #[trigger] final(out)@[t] < 4,
    no_unwind
{
    let lo: i64 = -1826;
    let hi: i64 = -1096;
    // slices of exactly `n0` entries (so the loop's indexing needs no checks); the output is a slice the loop alone
    // writes, so the map's gather vectorizes
    let (sk, _) = sk.split_at(n0);
    let (sd, _) = sd.split_at(n0);
    let ghost out0 = out@;
    let (o, rest) = out.split_at_mut(n0);
    let ml = m32.len();
    let mut t: usize = 0;
    while t < n0
        invariant
            n0 == sk@.len(), n0 == sd@.len(), n0 == o@.len(), ml == m32@.len(),
            16 * m32@.len() >= ns, 0 <= ns < 0x4000_0000_0000_0000,
            -0x4000_0000_0000_0000 < off < 0x4000_0000_0000_0000,
            forall|s: int| 0 <= s < n0 ==> in_i64(sbase + #[trigger] sd@[s] as int),
            lo == win_lo(), hi == win_hi(),
            t <= n0,
            forall|s: int| 0 <= s < t ==> #[trigger] o@[s] as int == lcw(m32@, ns as int, off as int, sbase as int, sk@[s], sd@[s]),
            forall|s: int| 0 <= s < t ==> #[trigger] o@[s] < 4,
        decreases n0 - t,
    {
        let r = sk[t] as i64 + off;
        let inr = 0 <= r && r < ns;
        let mk: u32 = if inr { 3 } else { 0 };
        let rr: u64 = r as u64;
        let wi = (rr >> 4) as usize;
        let w = if wi < ml { m32[wi] } else { 0 };
        proof {
            assert((rr & 15) <= 15) by (bit_vector);
        }
        let c = (w >> ((rr & 15) * 2) as u32) & mk;
        let d = sbase + sd[t] as i64;
        let inw = lo <= d && d <= hi;
        let v: u8 = if inw { c as u8 } else { 0 };
        proof {
            assert(((w >> ((rr & 15) * 2) as u32) & 0u32) == 0u32 && ((w >> ((rr & 15) * 2) as u32) & 3u32) < 4u32) by (bit_vector);
            if inr {
                let ri = r as int;
                assert(rr == r);
                assert((rr >> 4u64) == rr / 16 && (rr & 15u64) == rr % 16) by (bit_vector);
                assert(wi == ri / 16 && ((rr & 15) * 2) as u32 == (2 * (ri % 16)) as u32);
                assert(wi < m32@.len());
                assert(c as int == get2(m32@[ri / 16], ri % 16));
            }
            assert(v as int == lcw(m32@, ns as int, off as int, sbase as int, sk@[t as int], sd@[t as int]));
        }
        let ghost o0 = o@;
        o[t] = v;
        proof {
            assert forall|s: int| 0 <= s < t + 1 implies #[trigger] o@[s] as int == lcw(m32@, ns as int, off as int, sbase as int, sk@[s], sd@[s]) && o@[s] < 4 by {
                if s < t {
                    assert(o@[s] == o0[s]);
                }
            }
        }
        t = t + 1;
    }
    proof {
        assert forall|s: int| 0 <= s < n0 implies #[trigger] out@[s] == o@[s] by {}
    }
}

/// A line's `lcw` (from its codes and the group's bases) is its `l_scw` under dense supplier keys from `sk0`.
pub proof fn lemma_lcw(c: Cols, x: Ctx, sk0: i64, sm: Seq<u32>, g: int, j: int)
    requires
        cols_ok(c), keys_ok(c),
        smap2_ok(c, x, sk0, sm),
        0 <= j < c.n_l, j / c.bs_l as int == g, 0 <= g < c.ls_bases@.len(),
    ensures
        lcw(sm, c.n_s as int, c.lsk_bases@[g] - sk0, c.ls_bases@[g] as int, c.lsk_codes@[j], c.ls_codes@[j]) == l_scw(c, x, j),
{
    let off = c.lsk_bases@[g] - sk0;
    let r = c.lsk_codes@[j] as int + off;
    assert(lship(c, j) == c.ls_bases@[g] + c.ls_codes@[j] as int);
    assert(lsupp(c, j) == sk0 + r);
    if 0 <= r < c.n_s {
        lemma_map_row(x, c.sn_bases@, c.sn_codes@, c.bs_s as int, c.n_s as int, sm, r);
        assert(snat(c, r) == nat_of(c.sn_bases@, c.sn_codes@, c.bs_s as int, r));
        let k = sk0 + r;
        assert(skey(c, r) == k);
        assert(has_s(c, k));
        let w = srow(c, k);
        assert(0 <= w < c.n_s && skey(c, w) == k);
        assert(w == r);
    } else {
        assert forall|i: int| 0 <= i < c.n_s implies #[trigger] skey(c, i) != lsupp(c, j) by {
            assert(skey(c, i) == sk0 + i);
        }
        assert(!has_s(c, lsupp(c, j)));
    }
}

/// Fast path, pass A1 over the lines `[jb, je)` of group `g`: `lc[t]` is the class of line `jb + t` (`l_scw`), from
/// the supplier class map (dense supplier keys from `sk0`; `off` is the group's supplier key base minus `sk0`).
pub fn line_classes(c: &Cols, sk0: i64, off: i64, sm: &Vec<u32>, g: usize, jb: usize, je: usize, lc: &mut [u8; BATCH],
    Ghost(x): Ghost<Ctx>)
    requires
        cols_ok(*c), keys_ok(*c),
        smap2_ok(*c, x, sk0, sm@),
        c.n_s < 0x4000_0000_0000_0000,
        g < c.ls_bases@.len(),
        off == c.lsk_bases@[g as int] - sk0,
        -0x4000_0000_0000_0000 < off < 0x4000_0000_0000_0000,
        jb < je <= c.n_l,
        je - jb <= BATCH,
        forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
    ensures
        forall|t: int| 0 <= t < je - jb ==> #[trigger] final(lc)@[t] as int == l_scw(*c, x, jb + t),
        forall|t: int| 0 <= t < je - jb ==> #[trigger] final(lc)@[t] < 4,
    no_unwind
{
    let sk = sub_u32(c.lsk_codes, jb, je);
    let sd = sub_u16(c.ls_codes, jb, je);
    let sbase = c.ls_bases[g];
    proof {
        assert forall|t: int| 0 <= t < je - jb implies in_i64(sbase + #[trigger] sd@[t] as int) by {
            let j = jb + t;
            assert(j / c.bs_l as int == g as int);
            assert(in_i64(lship(*c, j)));
            assert(sd@[t] == c.ls_codes@[j]);
        }
    }
    classes_kernel(sk, sd, sbase, off, c.n_s as i64, sm, lc, je - jb);
    proof {
        assert forall|t: int| 0 <= t < je - jb implies #[trigger] lc@[t] as int == l_scw(*c, x, jb + t) by {
            let j = jb + t;
            assert(j / c.bs_l as int == g as int);
            assert(sk@[t] == c.lsk_codes@[j] && sd@[t] == c.ls_codes@[j]);
            lemma_lcw(*c, x, sk0, sm@, g as int, j);
        }
    }
}

/// Fast path, pass A2 over the lines `[jb, je)` of group `g`: the candidates are the lines with a class `lc` (in the
/// window, supplier with a class); every other line is in no group. An orders cursor guesses each candidate's orders
/// row (`cand_p`): stored lines are grouped by order, in orders order, so the row of a line's order is the row of the
/// previous line's order plus one when the line starts its order (`l_linenumber` code `one`; a guess, checked by
/// `resolve_orders`). `q0`: the cursor before line `jb`; returns the count and the cursor after line `je - 1`.
#[inline(never)]
fn pick_lines(c: &Cols, g: usize, jb: usize, je: usize, q0: usize, one: i64, lc: &[u8; BATCH],
    cand_j: &mut Vec<usize>, cand_p: &mut Vec<usize>, Ghost(x): Ghost<Ctx>) -> (r: (usize, usize))
    requires
        cols_ok(*c),
        g < c.ls_bases@.len(),
        jb < je <= c.n_l,
        je - jb <= BATCH,
        q0 <= usize::MAX - BATCH,
        forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
        forall|t: int| 0 <= t < je - jb ==> #[trigger] lc@[t] as int == l_scw(*c, x, jb + t),
        old(cand_j)@.len() == BATCH, old(cand_p)@.len() == BATCH,
    ensures
        r.0 <= je - jb,
        r.1 <= q0 + (je - jb),
        final(cand_j)@.len() == BATCH, final(cand_p)@.len() == BATCH,
        lr_eq(*c, x, final(cand_j)@, r.0 as int, jb as int, je as int),
        forall|i: int| 0 <= i < r.0 ==> jb <= #[trigger] final(cand_j)@[i] < je,
    no_unwind
{
    let ln = sub_u8(c.lln_codes, jb, je);
    let n = je - jb;
    let mut q = q0;
    let mut nc: usize = 0;
    let mut t: usize = 0;
    proof {
        assert forall|gi: int| 0 <= gi < 4 implies {
            &&& #[trigger] lcnt(*c, x, gi, cand_j@, 0) == rcnt(*c, x, gi, jb as int, jb as int)
            &&& lsum(*c, x, gi, cand_j@, 0) == rsum(*c, x, gi, jb as int, jb as int)
            &&& lmass(*c, x, gi, cand_j@, 0) == rmass(*c, x, gi, jb as int, jb as int)
        } by {}
    }
    while t < n
        invariant
            cols_ok(*c),
            g < c.ls_bases@.len(),
            jb < je <= c.n_l,
            n == je - jb, n <= BATCH,
            q0 <= usize::MAX - BATCH, q <= q0 + t,
            ln@ == c.lln_codes@.subrange(jb as int, je as int),
            forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
            forall|s: int| 0 <= s < je - jb ==> #[trigger] lc@[s] as int == l_scw(*c, x, jb + s),
            cand_j@.len() == BATCH, cand_p@.len() == BATCH,
            t <= n, nc <= t,
            lr_eq(*c, x, cand_j@, nc as int, jb as int, jb + t),
            forall|i: int| 0 <= i < nc ==> jb <= #[trigger] cand_j@[i] < jb + t,
        decreases n - t,
    {
        let j = jb + t;
        let st: usize = if ln[t] as i64 == one { 1 } else { 0 };
        q = q + st;
        let f = lc[t];
        let ghost js0 = cand_j@;
        crate::gendb_entry::work::put(cand_j, nc, j);
        crate::gendb_entry::work::put(cand_p, nc, q);
        let take_n: usize = if f != 0 { 1 } else { 0 };
        proof {
            assert(f as int == l_scw(*c, x, j as int));
            assert forall|i: int| 0 <= i < nc implies jb <= #[trigger] cand_j@[i] < j by {
                assert(cand_j@[i] == js0[i]);
            }
            assert forall|gi: int| 0 <= gi < 4 implies {
                &&& lcnt(*c, x, gi, cand_j@, nc as int) == lcnt(*c, x, gi, js0, nc as int)
                &&& lsum(*c, x, gi, cand_j@, nc as int) == lsum(*c, x, gi, js0, nc as int)
                &&& lmass(*c, x, gi, cand_j@, nc as int) == lmass(*c, x, gi, js0, nc as int)
            } by {
                lemma_l_ext(*c, x, gi, cand_j@, js0, nc as int);
            }
            assert forall|gi: int| 0 <= gi < 4 implies {
                &&& rcnt(*c, x, gi, jb as int, j + 1) == rcnt(*c, x, gi, jb as int, j as int) + if l_grp(*c, x, j as int) == gi { 1int } else { 0 }
                &&& rsum(*c, x, gi, jb as int, j + 1) == rsum(*c, x, gi, jb as int, j as int) + if l_grp(*c, x, j as int) == gi { l_vol(*c, j as int) } else { 0 }
                &&& rmass(*c, x, gi, jb as int, j + 1) == rmass(*c, x, gi, jb as int, j as int) + if l_grp(*c, x, j as int) == gi { iabs(l_vol(*c, j as int)) } else { 0 }
            } by {
                lemma_r_step(*c, x, gi, jb as int, j as int);
            }
            if take_n == 0 {
                // not in the window, or a supplier without class: in no group
                assert(l_grp(*c, x, j as int) == -1);
            }
        }
        let ghost nc2: int = nc + take_n;
        proof {
            assert(cand_j@[nc as int] == j);
            assert forall|gi: int| 0 <= gi < 4 implies {
                &&& #[trigger] lcnt(*c, x, gi, cand_j@, nc2) == rcnt(*c, x, gi, jb as int, j + 1)
                &&& lsum(*c, x, gi, cand_j@, nc2) == rsum(*c, x, gi, jb as int, j + 1)
                &&& lmass(*c, x, gi, cand_j@, nc2) == rmass(*c, x, gi, jb as int, j + 1)
            } by {
                assert(lcnt(*c, x, gi, js0, nc as int) == rcnt(*c, x, gi, jb as int, j as int));
                assert(lsum(*c, x, gi, js0, nc as int) == rsum(*c, x, gi, jb as int, j as int));
                assert(lmass(*c, x, gi, js0, nc as int) == rmass(*c, x, gi, jb as int, j as int));
                lemma_l_step(*c, x, cand_j@, nc as int);
            }
            assert(lr_eq(*c, x, cand_j@, nc2, jb as int, j + 1));
        }
        nc = nc + take_n;
        t = t + 1;
    }
    (nc, q)
}

/// Fast path, pass B: each candidate's guessed orders row is checked to hold the line's order key (else the orders
/// key index finds the row), and becomes the row of its order's customer (`cr_ok`; dense customer keys
/// `[ck0, ck_hi]`).
#[inline(never)]
fn resolve_orders(c: &Cols, s: Shifts, ck0: i64, ck_hi: i64, g: usize, nc: usize, cand_j: &Vec<usize>,
    cand_p: &mut Vec<usize>, Ghost(x): Ghost<Ctx>, Ghost(jb): Ghost<int>, Ghost(je): Ghost<int>)
    requires
        cols_ok(*c), keys_ok(*c), shifts_ok(*c, s),
        0 < c.n_c < usize::MAX / 32, ck_hi == ck0 + c.n_c - 1, c_dense_ok(*c, true, ck0),
        g < c.ls_bases@.len(),
        0 <= jb <= je <= c.n_l,
        nc <= BATCH,
        forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
        cand_j@.len() == BATCH, old(cand_p)@.len() == BATCH,
        forall|i: int| 0 <= i < nc ==> jb <= #[trigger] cand_j@[i] < je,
    ensures
        final(cand_p)@.len() == BATCH,
        forall|i: int| 0 <= i < nc ==> #[trigger] cr_ok(*c, x, lkey(*c, cand_j@[i] as int), final(cand_p)@[i] as int),
    no_unwind
{
    let kbase = c.lok_bases[g];
    let n_o = c.n_o;
    let n_c = c.n_c;
    let mut i: usize = 0;
    while i < nc
        invariant
            cols_ok(*c), keys_ok(*c), shifts_ok(*c, s),
            0 < c.n_c < usize::MAX / 32, ck_hi == ck0 + c.n_c - 1, c_dense_ok(*c, true, ck0),
            g < c.ls_bases@.len(),
            0 <= jb <= je <= c.n_l,
            i <= nc <= BATCH,
            n_o == c.n_o, n_c == c.n_c,
            kbase == c.lok_bases@[g as int],
            forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
            cand_j@.len() == BATCH, cand_p@.len() == BATCH,
            forall|t: int| 0 <= t < nc ==> jb <= #[trigger] cand_j@[t] < je,
            forall|t: int| 0 <= t < i ==> #[trigger] cr_ok(*c, x, lkey(*c, cand_j@[t] as int), cand_p@[t] as int),
        decreases nc - i,
    {
        let jj = cand_j[i];
        let guess = cand_p[i];
        proof {
            assert(jb <= jj < je);
            assert(jj as int / c.bs_l as int == g as int);
            assert(in_i64(lkey(*c, jj as int)));
        }
        let k = kbase + c.lok_codes[jj] as i64;
        let cr: usize = match order_row(c, s, k, guess) {
            Some(p) => {
                proof {
                    lemma_div_below(p as int, c.bs_o as int, c.oc_bases@.len() as int, c.n_o as int);
                    assert(in_i64(ocust(*c, p as int)));
                    assert(k == lkey(*c, jj as int));
                    lemma_line_order(*c, x, jj as int, p as int);
                }
                let og = div_bs(p, c.bs_o, s.sh_o, s.pow_o);
                let ck = c.oc_bases[og] + c.oc_codes[p] as i64;
                if ck0 <= ck && ck <= ck_hi {
                    let r = (ck - ck0) as usize;
                    proof {
                        assert(ck == ocust(*c, p as int));
                        assert(in_i64(cnat(*c, r as int)));
                        assert(ckey(*c, r as int) == ck);
                        assert(has_c(*c, ck as int));
                        let w = crow(*c, ck as int);
                        assert(0 <= w < c.n_c && ckey(*c, w) == ck);
                        assert(w == r);
                    }
                    r
                } else {
                    proof {
                        assert(ck == ocust(*c, p as int));
                        assert forall|t: int| 0 <= t < c.n_c implies #[trigger] ckey(*c, t) != ck by {
                            assert(ckey(*c, t) == ck0 + t);
                        }
                        assert(!has_c(*c, ck as int));
                    }
                    n_c
                }
            },
            None => n_c,
        };
        let ghost ps0 = cand_p@;
        crate::gendb_entry::work::put(cand_p, i, cr);
        proof {
            assert(cr_ok(*c, x, lkey(*c, jj as int), cr as int));
            assert forall|t: int| 0 <= t < i + 1 implies #[trigger] cr_ok(*c, x, lkey(*c, cand_j@[t] as int), cand_p@[t] as int) by {
                if t < i {
                    assert(cand_p@[t] == ps0[t]);
                }
            }
        }
        i = i + 1;
    }
}

/// `out[i] = cls_of(m32, ncust, cp[i])` for `i < n`: the classes of the candidates' customer rows (rows `>= ncust`:
/// none), branch-free so the word gather vectorizes.
#[inline(never)]
pub fn cust_kernel(cp: &Vec<usize>, ncust: usize, m32: &Vec<u32>, out: &mut [u8], n0: usize)
    requires
        n0 <= cp@.len(), n0 <= old(out)@.len(),
        16 * m32@.len() >= ncust,
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|i: int| 0 <= i < n0 ==> #[trigger] final(out)@[i] as int == cls_of(m32@, ncust as int, cp@[i] as int),
    no_unwind
{
    let n = if n0 < cp.len() { n0 } else { cp.len() };
    let (o, rest) = out.split_at_mut(n0);
    let ml = m32.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == n0, n0 <= cp@.len(), n0 == o@.len(), ml == m32@.len(),
            16 * m32@.len() >= ncust,
            i <= n,
            forall|s: int| 0 <= s < i ==> #[trigger] o@[s] as int == cls_of(m32@, ncust as int, cp@[s] as int),
        decreases n - i,
    {
        let r = cp[i];
        let mk: u32 = if r < ncust { 3 } else { 0 };
        let wi = r >> 4;
        let w = if wi < ml { m32[wi] } else { 0 };
        proof {
            assert((r & 15) <= 15) by (bit_vector);
        }
        let c = (w >> ((r & 15) * 2) as u32) & mk;
        proof {
            assert(((w >> ((r & 15) * 2) as u32) & 0u32) == 0u32 && ((w >> ((r & 15) * 2) as u32) & 3u32) < 4u32) by (bit_vector);
            if r < ncust {
                assert((r >> 4) == r / 16 && (r & 15) == r % 16) by (bit_vector);
                assert(((r & 15) * 2) as u32 == (2 * (r as int % 16)) as u32);
                assert(wi < m32@.len());
                assert(c as int == get2(m32@[r as int / 16], r as int % 16));
            }
            assert(c as int == cls_of(m32@, ncust as int, r as int));
            assert(c < 4);
        }
        let ghost o0 = o@;
        o[i] = c as u8;
        proof {
            assert forall|s: int| 0 <= s < i + 1 implies #[trigger] o@[s] as int == cls_of(m32@, ncust as int, cp@[s] as int) by {
                if s < i {
                    assert(o@[s] == o0[s]);
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert forall|s: int| 0 <= s < n0 implies #[trigger] out@[s] == o@[s] by {}
    }
}

/// Fast path, pass C: each candidate's supplier class `cand_x[i]` becomes its line's group code (`g_code`), from its
/// order's customer row (pass B) through the customer class map, and its shipdate.
#[inline(never)]
pub fn group_codes(c: &Cols, ck0: i64, cm: &Vec<u32>, same: bool, g: usize, jb: usize,
    nc: usize, cand_j: &Vec<usize>, cand_p: &Vec<usize>, lc: &[u8; BATCH], cc: &[u8; BATCH], cand_x: &mut Vec<u8>,
    Ghost(x): Ghost<Ctx>, Ghost(je): Ghost<int>)
    requires
        cols_ok(*c),
        cmap_ok(*c, x, ck0, cm@),
        x.same == same,
        g < c.ls_bases@.len(),
        0 <= jb <= je <= c.n_l,
        nc <= BATCH,
        forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
        je - jb <= BATCH,
        cand_j@.len() == BATCH, cand_p@.len() == BATCH, old(cand_x)@.len() == BATCH,
        forall|t: int| 0 <= t < nc ==> jb <= #[trigger] cand_j@[t] < je,
        forall|t: int| 0 <= t < nc ==> #[trigger] cr_ok(*c, x, lkey(*c, cand_j@[t] as int), cand_p@[t] as int),
        forall|t: int| 0 <= t < nc ==> #[trigger] cc@[t] as int == cls_of(cm@, c.n_c as int, cand_p@[t] as int),
        forall|t: int| 0 <= t < je - jb ==> #[trigger] lc@[t] as int == l_scw(*c, x, jb + t),
    ensures
        final(cand_x)@.len() == BATCH,
        forall|t: int| 0 <= t < nc ==> #[trigger] final(cand_x)@[t] as int == g_code(*c, x, cand_j@[t] as int),
    no_unwind
{
    let lo: i64 = -1826;
    let hi: i64 = -1096;
    let sbase = c.ls_bases[g];
    let n_c = c.n_c;
    let mut i: usize = 0;
    while i < nc
        invariant
            cols_ok(*c),
            cmap_ok(*c, x, ck0, cm@),
            x.same == same,
            g < c.ls_bases@.len(),
            0 <= jb <= je <= c.n_l,
            i <= nc <= BATCH,
            n_c == c.n_c,
            forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
            sbase == c.ls_bases@[g as int],
            lo == win_lo(), hi == win_hi(),
            je - jb <= BATCH,
            cand_j@.len() == BATCH, cand_p@.len() == BATCH, cand_x@.len() == BATCH,
            forall|t: int| 0 <= t < nc ==> jb <= #[trigger] cand_j@[t] < je,
            forall|t: int| 0 <= t < nc ==> #[trigger] cr_ok(*c, x, lkey(*c, cand_j@[t] as int), cand_p@[t] as int),
            forall|t: int| 0 <= t < je - jb ==> #[trigger] lc@[t] as int == l_scw(*c, x, jb + t),
            forall|t: int| 0 <= t < nc ==> #[trigger] cc@[t] as int == cls_of(cm@, c.n_c as int, cand_p@[t] as int),
            forall|t: int| 0 <= t < i ==> #[trigger] cand_x@[t] as int == g_code(*c, x, cand_j@[t] as int),
        decreases nc - i,
    {
        let jj = cand_j[i];
        let cr = cand_p[i];
        proof {
            assert(jb <= jj < je);
            assert(lc@[jj - jb] as int == l_scw(*c, x, jb + (jj - jb)));
            assert(jj as int / c.bs_l as int == g as int);
            assert(in_i64(lship(*c, jj as int)));
            assert(cr_ok(*c, x, lkey(*c, jj as int), cr as int));
        }
        let sc = lc[jj - jb];
        let cc = cc[i];
        proof {
            assert(cc as int == cls_of(cm@, c.n_c as int, cr as int));
            if cr < n_c {
                lemma_map_row(x, c.cn_bases@, c.cn_codes@, c.bs_c as int, c.n_c as int, cm@, cr as int);
                assert(cnat(*c, cr as int) == nat_of(c.cn_bases@, c.cn_codes@, c.bs_c as int, cr as int));
            }
        }
        let d = sbase + c.ls_codes[jj] as i64;
        let p0 = sc % 2 == 1 && cc >= 2;
        let p1 = !same && sc >= 2 && cc % 2 == 1;
        let yi: u8 = if d >= -1461 { 1 } else { 0 };
        let code: u8 = if lo <= d && d <= hi && (p0 || p1) { if p0 { yi } else { 2 + yi } } else { 4 };
        proof {
            assert(d == lship(*c, jj as int));
            assert(cc as int == o_cls(*c, x, lkey(*c, jj as int)));
            if lo <= d && d <= hi {
                assert(sc as int == s_cls(*c, x, lsupp(*c, jj as int)));
            }
            assert(code as int == g_code(*c, x, jj as int));
        }
        let ghost co0 = cand_x@;
        crate::gendb_entry::work::put(cand_x, i, code);
        proof {
            assert forall|t: int| 0 <= t < i + 1 implies #[trigger] cand_x@[t] as int == g_code(*c, x, cand_j@[t] as int) by {
                if t < i {
                    assert(cand_x@[t] == co0[t]);
                }
            }
        }
        i = i + 1;
    }
}

/// Fast path, pass D: the candidates with a group (code below 4) into the accumulators.
#[inline(never)]
pub fn add_codes(c: &Cols, g: usize, nc: usize, cand_j: &Vec<usize>, cand_o: &Vec<u8>,
    sums: Vec<i128>, mass: Vec<i128>, cnts: Vec<usize>, over: bool,
    Ghost(x): Ghost<Ctx>, Ghost(a): Ghost<int>, Ghost(jb): Ghost<int>, Ghost(je): Ghost<int>) -> (r: ScanOut)
    requires
        cols_ok(*c),
        g < c.ls_bases@.len(),
        0 <= a <= jb <= je <= c.n_l,
        nc <= BATCH, nc <= je - jb,
        forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
        cand_j@.len() == BATCH, cand_o@.len() == BATCH,
        forall|t: int| 0 <= t < nc ==> jb <= #[trigger] cand_j@[t] < je,
        forall|t: int| 0 <= t < nc ==> #[trigger] cand_o@[t] as int == g_code(*c, x, cand_j@[t] as int),
        acc_ok(*c, x, sums@, mass@, cnts@, over, a, jb, cand_j@, 0),
    ensures
        acc_ok(*c, x, r.0@, r.1@, r.2@, r.3, a, jb, cand_j@, nc as int),
    no_unwind
{
    let mut sums = sums;
    let mut mass = mass;
    let mut cnts = cnts;
    let mut over = over;
    let mut i: usize = 0;
    while i < nc
        invariant
            cols_ok(*c),
            g < c.ls_bases@.len(),
            0 <= a <= jb <= je <= c.n_l,
            i <= nc <= BATCH, nc <= je - jb,
            forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
            cand_j@.len() == BATCH, cand_o@.len() == BATCH,
            forall|t: int| 0 <= t < nc ==> jb <= #[trigger] cand_j@[t] < je,
            forall|t: int| 0 <= t < nc ==> #[trigger] cand_o@[t] as int == g_code(*c, x, cand_j@[t] as int),
            acc_ok(*c, x, sums@, mass@, cnts@, over, a, jb, cand_j@, i as int),
        decreases nc - i,
    {
        let code = cand_o[i];
        if code < 4 {
            let jj = cand_j[i];
            proof {
                assert(jb <= jj < je);
                assert(jj as int / c.bs_l as int == g as int);
                assert(small15(lprice(*c, jj as int)) && small15(ldisc(*c, jj as int)));
            }
            let price = c.lp_bases[g] + c.lp_codes[jj] as i64;
            let disc = c.ld_bases[g] + c.ld_codes[jj] as i64;
            proof {
                assert(price == lprice(*c, jj as int) && disc == ldisc(*c, jj as int));
                lemma_vol_bound(price as int, disc as int);
            }
            let vol: i128 = price as i128 * (100 - disc as i128);
            proof {
                assert(l_grp(*c, x, jj as int) == code as int);
                assert(vol == l_vol(*c, jj as int));
            }
            let (s2, m2, c2, o2) = add_line(sums, mass, cnts, over, code as usize, vol,
                Ghost(*c), Ghost(x), Ghost(a), Ghost(jb), Ghost(cand_j@), Ghost(i as int));
            sums = s2;
            mass = m2;
            cnts = c2;
            over = o2;
        } else {
            proof {
                assert(l_grp(*c, x, cand_j@[i as int] as int) == -1);
                lemma_acc_skip(*c, x, sums@, mass@, cnts@, over, a, jb, cand_j@, i as int);
            }
        }
        i = i + 1;
    }
    (sums, mass, cnts, over)
}

/// Phase A over the lines `[jb, je)` of group `g`: the candidates (line, guessed stored orders row, supplier class)
/// and the guess after the last line.
#[inline(never)]
fn phase_a(c: &Cols, s: Shifts, sd: bool, sk0: i64, sdd: bool, sk_hi: i64, sm: &Arc<Vec<u8>>, nt: &Vec<u8>,
    nkeys: &Vec<i64>, nclss: &Vec<u8>, nn: usize, g: usize, jb: usize, je: usize, inside: bool, one_code: i64, p0: usize,
    cand_j: &mut Vec<usize>, cand_p: &mut Vec<usize>, cand_x: &mut Vec<u8>, Ghost(x): Ghost<Ctx>) -> (r: (usize, usize))
    requires
        cols_ok(*c), keys_ok(*c), shifts_ok(*c, s), s_dense_ok(*c, sd, sk0), smap_ok(*c, x, sd, sk0, sm@),
        ntab_ok(x, nt@), ncls_ok(x, nkeys@, nclss@), nn == nkeys@.len(),
        sdd ==> sd && 0 < c.n_s < 0x4000_0000_0000_0000 && sk_hi == sk0 + c.n_s - 1,
        g < c.ls_bases@.len(),
        jb < je <= c.n_l,
        je - jb <= BATCH,
        forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
        inside ==> c.ls_bases@[g as int] >= win_lo() && c.ls_zmax@[g as int] <= win_hi(),
        old(cand_j)@.len() == BATCH, old(cand_p)@.len() == BATCH, old(cand_x)@.len() == BATCH,
    ensures
        r.0 <= je - jb,
        final(cand_j)@.len() == BATCH, final(cand_p)@.len() == BATCH, final(cand_x)@.len() == BATCH,
        lr_eq(*c, x, final(cand_j)@, r.0 as int, jb as int, je as int),
        forall|i: int| 0 <= i < r.0 ==> jb <= #[trigger] final(cand_j)@[i] < je,
        forall|i: int| 0 <= i < r.0 ==> #[trigger] final(cand_x)@[i] as int == s_cls(*c, x, lsupp(*c, final(cand_j)@[i] as int)),
        forall|i: int| 0 <= i < r.0 ==> #[trigger] final(cand_x)@[i] < 4,
    no_unwind
{
    let lo: i64 = -1826;
    let hi: i64 = -1096;
    let sbase = c.ls_bases[g];
    let skbase = c.lsk_bases[g];
    let n_o = c.n_o;
    let mut p = p0;
    let mut nc: usize = 0;
    let mut j = jb;
    proof {
        assert forall|gi: int| 0 <= gi < 4 implies {
            &&& #[trigger] lcnt(*c, x, gi, cand_j@, 0) == rcnt(*c, x, gi, jb as int, jb as int)
            &&& lsum(*c, x, gi, cand_j@, 0) == rsum(*c, x, gi, jb as int, jb as int)
            &&& lmass(*c, x, gi, cand_j@, 0) == rmass(*c, x, gi, jb as int, jb as int)
        } by {}
    }
    while j < je
        invariant
            cols_ok(*c), keys_ok(*c), shifts_ok(*c, s), s_dense_ok(*c, sd, sk0), smap_ok(*c, x, sd, sk0, sm@),
            ntab_ok(x, nt@), ncls_ok(x, nkeys@, nclss@), nn == nkeys@.len(),
            sdd ==> sd && 0 < c.n_s < 0x4000_0000_0000_0000 && sk_hi == sk0 + c.n_s - 1,
            g < c.ls_bases@.len(),
            jb <= j <= je <= c.n_l,
            je - jb <= BATCH,
            nc <= j - jb,
            n_o == c.n_o,
            forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
            inside ==> c.ls_bases@[g as int] >= win_lo() && c.ls_zmax@[g as int] <= win_hi(),
            sbase == c.ls_bases@[g as int], skbase == c.lsk_bases@[g as int],
            lo == win_lo(), hi == win_hi(),
            cand_j@.len() == BATCH, cand_p@.len() == BATCH, cand_x@.len() == BATCH,
            lr_eq(*c, x, cand_j@, nc as int, jb as int, j as int),
            forall|i: int| 0 <= i < nc ==> jb <= #[trigger] cand_j@[i] < j,
            forall|i: int| 0 <= i < nc ==> #[trigger] cand_x@[i] as int == s_cls(*c, x, lsupp(*c, cand_j@[i] as int)),
            forall|i: int| 0 <= i < nc ==> #[trigger] cand_x@[i] < 4,
        decreases je - j,
    {
        proof {
            assert(j as int / c.bs_l as int == g as int);
            assert(in_i64(lship(*c, j as int)) && in_i64(lsupp(*c, j as int)));
        }
        p = if (c.lln_codes[j] as i64 == one_code) && p < n_o { p + 1 } else { p };
        let d = sbase + c.ls_codes[j] as i64;
        let inwin = inside || (lo <= d && d <= hi);
        let k = skbase + c.lsk_codes[j] as i64;
        let sc: u8 = if !inwin {
            0
        } else if sdd {
            if sk0 <= k && k <= sk_hi {
                proof {
                    assert(sm@[k - sk0] as int == s_cls(*c, x, sk0 + (k - sk0)));
                }
                sm[(k - sk0) as usize]
            } else {
                proof {
                    assert forall|i: int| 0 <= i < c.n_s implies #[trigger] skey(*c, i) != k by {
                        assert(skey(*c, i) == sk0 + i);
                    }
                    assert(!has_s(*c, k as int));
                }
                0
            }
        } else {
            supp_class(c, s, sd, sk0, nt, nkeys, nclss, nn, k, Ghost(x))
        };
        let ghost js0 = cand_j@;
        let ghost xs0 = cand_x@;
        crate::gendb_entry::work::put(cand_j, nc, j);
        crate::gendb_entry::work::put(cand_p, nc, p);
        crate::gendb_entry::work::put(cand_x, nc, sc);
        proof {
            assert(d == lship(*c, j as int));
            assert(k == lsupp(*c, j as int));
            if inside {
                assert(c.ls_bases@[g as int] <= lship(*c, j as int) <= c.ls_zmax@[g as int]);
            }
            assert(inwin == (win_lo() <= lship(*c, j as int) <= win_hi()));
            assert forall|gi: int| 0 <= gi < 4 implies {
                &&& lcnt(*c, x, gi, cand_j@, nc as int) == lcnt(*c, x, gi, js0, nc as int)
                &&& lsum(*c, x, gi, cand_j@, nc as int) == lsum(*c, x, gi, js0, nc as int)
                &&& lmass(*c, x, gi, cand_j@, nc as int) == lmass(*c, x, gi, js0, nc as int)
            } by {
                lemma_l_ext(*c, x, gi, cand_j@, js0, nc as int);
            }
            assert forall|gi: int| 0 <= gi < 4 implies {
                &&& rcnt(*c, x, gi, jb as int, j + 1) == rcnt(*c, x, gi, jb as int, j as int) + if l_grp(*c, x, j as int) == gi { 1int } else { 0 }
                &&& rsum(*c, x, gi, jb as int, j + 1) == rsum(*c, x, gi, jb as int, j as int) + if l_grp(*c, x, j as int) == gi { l_vol(*c, j as int) } else { 0 }
                &&& rmass(*c, x, gi, jb as int, j + 1) == rmass(*c, x, gi, jb as int, j as int) + if l_grp(*c, x, j as int) == gi { iabs(l_vol(*c, j as int)) } else { 0 }
            } by {
                lemma_r_step(*c, x, gi, jb as int, j as int);
            }
            if sc == 0 {
                // not in the window, or a supplier without class: in no group
                assert(l_grp(*c, x, j as int) == -1);
            }
            assert forall|i: int| 0 <= i < nc implies #[trigger] cand_x@[i] as int == s_cls(*c, x, lsupp(*c, cand_j@[i] as int)) by {
                assert(cand_x@[i] == xs0[i] && cand_j@[i] == js0[i]);
            }
        }
        let ghost nc2: int = if sc != 0 { nc + 1 } else { nc as int };
        proof {
            assert(cand_j@[nc as int] == j);
            assert forall|gi: int| 0 <= gi < 4 implies {
                &&& #[trigger] lcnt(*c, x, gi, cand_j@, nc2) == rcnt(*c, x, gi, jb as int, j + 1)
                &&& lsum(*c, x, gi, cand_j@, nc2) == rsum(*c, x, gi, jb as int, j + 1)
                &&& lmass(*c, x, gi, cand_j@, nc2) == rmass(*c, x, gi, jb as int, j + 1)
            } by {
                assert(lcnt(*c, x, gi, js0, nc as int) == rcnt(*c, x, gi, jb as int, j as int));
                assert(lsum(*c, x, gi, js0, nc as int) == rsum(*c, x, gi, jb as int, j as int));
                assert(lmass(*c, x, gi, js0, nc as int) == rmass(*c, x, gi, jb as int, j as int));
            }
            if sc != 0 {
                assert(sc as int == s_cls(*c, x, lsupp(*c, j as int)));
            }
        }
        if sc != 0 {
            nc = nc + 1;
        }
        j = j + 1;
    }
    (nc, p)
}

/// The customer row of the order of key `k`: `r < n_c` is that row, `r >= n_c` means the key has no customer
/// class source (no order, or an order whose customer key has no row).
pub open spec fn cr_ok(c: Cols, x: Ctx, k: int, r: int) -> bool {
    &&& r < c.n_c ==> o_cls(c, x, k) == nat_cls(x, cnat(c, r)) && in_i64(cnat(c, r))
    &&& r >= c.n_c ==> o_cls(c, x, k) == 0
}

/// Phase B1: each candidate's guessed orders row becomes its order's customer row (`cr_ok`).
#[inline(never)]
fn phase_b1(c: &Cols, s: Shifts, cd: bool, ck0: i64, g: usize, nc: usize, cand_j: &Vec<usize>, cand_p: &mut Vec<usize>,
    Ghost(x): Ghost<Ctx>, Ghost(jb): Ghost<int>, Ghost(je): Ghost<int>)
    requires
        cols_ok(*c), keys_ok(*c), shifts_ok(*c, s), c_dense_ok(*c, cd, ck0),
        g < c.ls_bases@.len(),
        0 <= jb <= je <= c.n_l,
        nc <= BATCH,
        forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
        cand_j@.len() == BATCH, old(cand_p)@.len() == BATCH,
        forall|i: int| 0 <= i < nc ==> jb <= #[trigger] cand_j@[i] < je,
    ensures
        final(cand_p)@.len() == BATCH,
        forall|i: int| 0 <= i < nc ==> #[trigger] cr_ok(*c, x, lkey(*c, cand_j@[i] as int), final(cand_p)@[i] as int),
    no_unwind
{
    let kbase = c.lok_bases[g];
    let n_c = c.n_c;
    let mut prev_k: i64 = 0;
    let mut prev_r: usize = 0;
    let mut have_prev = false;
    let mut i: usize = 0;
    while i < nc
        invariant
            cols_ok(*c), keys_ok(*c), shifts_ok(*c, s), c_dense_ok(*c, cd, ck0),
            g < c.ls_bases@.len(),
            0 <= jb <= je <= c.n_l,
            i <= nc <= BATCH,
            n_c == c.n_c,
            kbase == c.lok_bases@[g as int],
            forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
            cand_j@.len() == BATCH, cand_p@.len() == BATCH,
            forall|t: int| 0 <= t < nc ==> jb <= #[trigger] cand_j@[t] < je,
            forall|t: int| 0 <= t < i ==> #[trigger] cr_ok(*c, x, lkey(*c, cand_j@[t] as int), cand_p@[t] as int),
            have_prev ==> cr_ok(*c, x, prev_k as int, prev_r as int),
        decreases nc - i,
    {
        let jj = cand_j[i];
        proof {
            assert(jb <= jj < je);
            assert(jj as int / c.bs_l as int == g as int);
            assert(in_i64(lkey(*c, jj as int)));
        }
        let k = kbase + c.lok_codes[jj] as i64;
        let r: usize = if have_prev && k == prev_k {
            prev_r
        } else {
            match order_row(c, s, k, cand_p[i]) {
                Some(q) => {
                    proof {
                        assert(has_o(*c, k as int));
                        let w = orow(*c, k as int);
                        assert(okey(*c, w) == k && 0 <= w < c.n_o);
                        assert(w == q);
                        assert(in_i64(ocust(*c, q as int)));
                        lemma_div_below(q as int, c.bs_o as int, c.oc_bases@.len() as int, c.n_o as int);
                    }
                    let og = div_bs(q, c.bs_o, s.sh_o, s.pow_o);
                    let ck = c.oc_bases[og] + c.oc_codes[q] as i64;
                    match cust_row(c, cd, ck0, ck) {
                        Some(cr) => {
                            proof {
                                assert(has_c(*c, ck as int));
                                let w = crow(*c, ck as int);
                                assert(ckey(*c, w) == ck && 0 <= w < c.n_c);
                                assert(w == cr);
                                assert(in_i64(cnat(*c, cr as int)));
                            }
                            cr
                        },
                        None => n_c,
                    }
                },
                None => n_c,
            }
        };
        let ghost ps0 = cand_p@;
        crate::gendb_entry::work::put(cand_p, i, r);
        proof {
            assert(k == lkey(*c, jj as int));
            assert(cr_ok(*c, x, k as int, r as int));
            assert forall|t: int| 0 <= t < i + 1 implies #[trigger] cr_ok(*c, x, lkey(*c, cand_j@[t] as int), cand_p@[t] as int) by {
                if t < i {
                    assert(cand_p@[t] == ps0[t]);
                }
            }
        }
        prev_k = k;
        prev_r = r;
        have_prev = true;
        i = i + 1;
    }
}

/// Phase B2: each candidate's customer class, group and volume into the accumulators.
#[inline(never)]
fn phase_b2(c: &Cols, s: Shifts, nt: &Vec<u8>, nkeys: &Vec<i64>, nclss: &Vec<u8>, nn: usize, same: bool, g: usize,
    nc: usize, cand_j: &Vec<usize>, cand_p: &Vec<usize>, cand_x: &Vec<u8>,
    sums: Vec<i128>, mass: Vec<i128>, cnts: Vec<usize>, over: bool,
    Ghost(x): Ghost<Ctx>, Ghost(a): Ghost<int>, Ghost(jb): Ghost<int>, Ghost(je): Ghost<int>) -> (r: ScanOut)
    requires
        cols_ok(*c), shifts_ok(*c, s),
        ntab_ok(x, nt@), ncls_ok(x, nkeys@, nclss@), nn == nkeys@.len(),
        x.same == same,
        g < c.ls_bases@.len(),
        0 <= a <= jb <= je <= c.n_l,
        nc <= BATCH, nc <= je - jb,
        forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
        cand_j@.len() == BATCH, cand_p@.len() == BATCH, cand_x@.len() == BATCH,
        forall|t: int| 0 <= t < nc ==> jb <= #[trigger] cand_j@[t] < je,
        forall|t: int| 0 <= t < nc ==> #[trigger] cand_x@[t] as int == s_cls(*c, x, lsupp(*c, cand_j@[t] as int)),
        forall|t: int| 0 <= t < nc ==> #[trigger] cand_x@[t] < 4,
        forall|t: int| 0 <= t < nc ==> #[trigger] cr_ok(*c, x, lkey(*c, cand_j@[t] as int), cand_p@[t] as int),
        acc_ok(*c, x, sums@, mass@, cnts@, over, a, jb, cand_j@, 0),
    ensures
        acc_ok(*c, x, r.0@, r.1@, r.2@, r.3, a, jb, cand_j@, nc as int),
    no_unwind
{
    let lo: i64 = -1826;
    let hi: i64 = -1096;
    let sbase = c.ls_bases[g];
    let n_c = c.n_c;
    let mut sums = sums;
    let mut mass = mass;
    let mut cnts = cnts;
    let mut over = over;
    let mut i: usize = 0;
    while i < nc
        invariant
            cols_ok(*c), shifts_ok(*c, s),
            ntab_ok(x, nt@), ncls_ok(x, nkeys@, nclss@), nn == nkeys@.len(),
            x.same == same,
            g < c.ls_bases@.len(),
            0 <= a <= jb <= je <= c.n_l,
            i <= nc <= BATCH, nc <= je - jb,
            n_c == c.n_c,
            forall|j: int| jb <= j < je ==> #[trigger] (j / c.bs_l as int) == g,
            sbase == c.ls_bases@[g as int],
            lo == win_lo(), hi == win_hi(),
            cand_j@.len() == BATCH, cand_p@.len() == BATCH, cand_x@.len() == BATCH,
            forall|t: int| 0 <= t < nc ==> jb <= #[trigger] cand_j@[t] < je,
            forall|t: int| 0 <= t < nc ==> #[trigger] cand_x@[t] as int == s_cls(*c, x, lsupp(*c, cand_j@[t] as int)),
            forall|t: int| 0 <= t < nc ==> #[trigger] cand_x@[t] < 4,
            forall|t: int| 0 <= t < nc ==> #[trigger] cr_ok(*c, x, lkey(*c, cand_j@[t] as int), cand_p@[t] as int),
            acc_ok(*c, x, sums@, mass@, cnts@, over, a, jb, cand_j@, i as int),
        decreases nc - i,
    {
        let jj = cand_j[i];
        let cr = cand_p[i];
        proof {
            assert(jb <= jj < je);
            assert(jj as int / c.bs_l as int == g as int);
            assert(in_i64(lship(*c, jj as int)));
            assert(small15(lprice(*c, jj as int)) && small15(ldisc(*c, jj as int)));
            assert(cr_ok(*c, x, lkey(*c, jj as int), cr as int));
        }
        let cc: u8 = if cr < n_c {
            proof {
                lemma_div_below(cr as int, c.bs_c as int, c.cn_bases@.len() as int, c.n_c as int);
            }
            let cg = div_bs(cr, c.bs_c, s.sh_c, s.pow_c);
            nat_fast(nt, nkeys, nclss, nn, c.cn_bases[cg] + c.cn_codes[cr] as i64, Ghost(x))
        } else {
            0
        };
        let sc = cand_x[i];
        let d = sbase + c.ls_codes[jj] as i64;
        let p0 = sc % 2 == 1 && cc >= 2;
        let p1 = !same && sc >= 2 && cc % 2 == 1;
        let ghost gl = l_grp(*c, x, jj as int);
        proof {
            assert(d == lship(*c, jj as int));
            assert(cc as int == o_cls(*c, x, lkey(*c, jj as int)));
            assert(sc as int == s_cls(*c, x, lsupp(*c, jj as int)));
        }
        if lo <= d && d <= hi && (p0 || p1) {
            let yi: usize = if d >= -1461 { 1 } else { 0 };
            let gi: usize = if p0 { yi } else { 2 + yi };
            let price = c.lp_bases[g] + c.lp_codes[jj] as i64;
            let disc = c.ld_bases[g] + c.ld_codes[jj] as i64;
            proof {
                assert(price == lprice(*c, jj as int) && disc == ldisc(*c, jj as int));
                lemma_vol_bound(price as int, disc as int);
            }
            let vol: i128 = price as i128 * (100 - disc as i128);
            proof {
                assert(gl == gi as int);
                assert(vol == l_vol(*c, jj as int));
            }
            let (s2, m2, c2, o2) = add_line(sums, mass, cnts, over, gi, vol,
                Ghost(*c), Ghost(x), Ghost(a), Ghost(jb), Ghost(cand_j@), Ghost(i as int));
            sums = s2;
            mass = m2;
            cnts = c2;
            over = o2;
        } else {
            proof {
                assert(gl == -1);
                lemma_acc_skip(*c, x, sums@, mass@, cnts@, over, a, jb, cand_j@, i as int);
            }
        }
        i = i + 1;
    }
    (sums, mass, cnts, over)
}

/// `price * (100 - disc)` of numeric(15, 2) coefficients is far inside `i128`.
pub proof fn lemma_vol_bound(price: int, disc: int)
    requires small15(price), small15(disc),
    ensures -0x1_0000_0000_0000_0000_0000_0000_0000 < price * (100 - disc) < 0x1_0000_0000_0000_0000_0000_0000_0000,
{
    let q = 100 - disc;
    assert(-1_000_000_000_000_100 < q < 1_000_000_000_000_100);
    assert(-1_000_000_000_000_100_000_000_000_000_000 < price * q < 1_000_000_000_000_100_000_000_000_000_000) by (nonlinear_arith)
        requires -1_000_000_000_000_000 < price < 1_000_000_000_000_000, -1_000_000_000_000_100 < q < 1_000_000_000_000_100;
}

/// One more list entry.
proof fn lemma_l_step(c: Cols, x: Ctx, js: Seq<usize>, i: int)
    requires 0 <= i,
    ensures forall|gi: int| {
        &&& #[trigger] lcnt(c, x, gi, js, i + 1) == lcnt(c, x, gi, js, i) + if l_grp(c, x, js[i] as int) == gi { 1int } else { 0 }
        &&& lsum(c, x, gi, js, i + 1) == lsum(c, x, gi, js, i) + if l_grp(c, x, js[i] as int) == gi { l_vol(c, js[i] as int) } else { 0 }
        &&& lmass(c, x, gi, js, i + 1) == lmass(c, x, gi, js, i) + if l_grp(c, x, js[i] as int) == gi { iabs(l_vol(c, js[i] as int)) } else { 0 }
    },
{
}

/// The empty prefix of any list adds nothing.
pub proof fn lemma_acc_list0(c: Cols, x: Ctx, sums: Seq<i128>, mass: Seq<i128>, cnts: Seq<usize>, over: bool, a: int, b: int, js: Seq<usize>)
    requires acc_ok(c, x, sums, mass, cnts, over, a, b, Seq::<usize>::empty(), 0),
    ensures acc_ok(c, x, sums, mass, cnts, over, a, b, js, 0),
{
    let e = Seq::<usize>::empty();
    assert forall|gi: int| 0 <= gi < 4 implies #[trigger] cnts[gi] as int == rcnt(c, x, gi, a, b) + lcnt(c, x, gi, js, 0) by {
        assert(cnts[gi] as int == rcnt(c, x, gi, a, b) + lcnt(c, x, gi, e, 0));
    }
    if !over {
        assert forall|gi: int| 0 <= gi < 4 implies #[trigger] sums[gi] as int == rsum(c, x, gi, a, b) + lsum(c, x, gi, js, 0) by {
            assert(sums[gi] as int == rsum(c, x, gi, a, b) + lsum(c, x, gi, e, 0));
        }
        assert forall|gi: int| 0 <= gi < 4 implies #[trigger] mass[gi] as int == rmass(c, x, gi, a, b) + lmass(c, x, gi, js, 0) && mass[gi] as int <= i128_max() by {
            assert(sums[gi] as int == rsum(c, x, gi, a, b) + lsum(c, x, gi, e, 0));
        }
    } else {
        let gi = choose|gi: int| 0 <= gi < 4 && #[trigger] rmass(c, x, gi, a, b) + lmass(c, x, gi, e, 0) > i128_max();
        assert(rmass(c, x, gi, a, b) + lmass(c, x, gi, js, 0) > i128_max());
    }
}

/// A candidate in no group: the accumulators also hold one more entry.
pub proof fn lemma_acc_skip(c: Cols, x: Ctx, sums: Seq<i128>, mass: Seq<i128>, cnts: Seq<usize>, over: bool, a: int, b: int, js: Seq<usize>, i: int)
    requires
        0 <= i < js.len(),
        l_grp(c, x, js[i] as int) == -1,
        acc_ok(c, x, sums, mass, cnts, over, a, b, js, i),
    ensures acc_ok(c, x, sums, mass, cnts, over, a, b, js, i + 1),
{
    lemma_l_step(c, x, js, i);
    assert forall|gi: int| 0 <= gi < 4 implies #[trigger] cnts[gi] as int == rcnt(c, x, gi, a, b) + lcnt(c, x, gi, js, i + 1) by {
        assert(cnts[gi] as int == rcnt(c, x, gi, a, b) + lcnt(c, x, gi, js, i));
    }
    if !over {
        assert forall|gi: int| 0 <= gi < 4 implies #[trigger] sums[gi] as int == rsum(c, x, gi, a, b) + lsum(c, x, gi, js, i + 1) by {
            assert(sums[gi] as int == rsum(c, x, gi, a, b) + lsum(c, x, gi, js, i));
        }
        assert forall|gi: int| 0 <= gi < 4 implies #[trigger] mass[gi] as int == rmass(c, x, gi, a, b) + lmass(c, x, gi, js, i + 1) && mass[gi] as int <= i128_max() by {
            assert(sums[gi] as int == rsum(c, x, gi, a, b) + lsum(c, x, gi, js, i));
        }
    } else {
        let gi = choose|gi: int| 0 <= gi < 4 && #[trigger] rmass(c, x, gi, a, b) + lmass(c, x, gi, js, i) > i128_max();
        assert(rmass(c, x, gi, a, b) + lmass(c, x, gi, js, i + 1) > i128_max());
    }
}

/// Add candidate `js[i]` (group `gi`, volume `vol`) to the accumulators.
pub fn add_line(sums: Vec<i128>, mass: Vec<i128>, cnts: Vec<usize>, over: bool, gi: usize, vol: i128,
    Ghost(c): Ghost<Cols>, Ghost(x): Ghost<Ctx>, Ghost(a): Ghost<int>, Ghost(b): Ghost<int>, Ghost(js): Ghost<Seq<usize>>,
    Ghost(i): Ghost<int>) -> (r: ScanOut)
    requires
        0 <= i < js.len(),
        0 <= a <= b,
        b + i < usize::MAX,
        gi < 4,
        l_grp(c, x, js[i] as int) == gi,
        vol == l_vol(c, js[i] as int),
        -0x1_0000_0000_0000_0000_0000_0000_0000 < vol < 0x1_0000_0000_0000_0000_0000_0000_0000,
        acc_ok(c, x, sums@, mass@, cnts@, over, a, b, js, i),
    ensures acc_ok(c, x, r.0@, r.1@, r.2@, r.3, a, b, js, i + 1),
    no_unwind
{
    let mut sums = sums;
    let mut mass = mass;
    let mut cnts = cnts;
    let mut over = over;
    proof {
        lemma_l_step(c, x, js, i);
        lemma_r_bounds(c, x, gi as int, a, b);
        lemma_l_bounds(c, x, gi as int, js, i);
        assert(cnts@[gi as int] as int == rcnt(c, x, gi as int, a, b) + lcnt(c, x, gi as int, js, i));
    }
    let ghost s0 = sums@;
    let ghost m0 = mass@;
    let ghost c0 = cnts@;
    let cv = cnts[gi] + 1;
    crate::gendb_entry::work::put(&mut cnts, gi, cv);
    let av: i128 = if vol < 0 { -vol } else { vol };
    let ghost over0 = over;
    if !over {
        let mv = mass[gi];
        proof {
            assert(mv as int == rmass(c, x, gi as int, a, b) + lmass(c, x, gi as int, js, i));
            assert(0 <= mv as int <= i128_max());
        }
        if (mv as u128) + (av as u128) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128 {
            let sv = sums[gi];
            proof {
                assert(sv as int == rsum(c, x, gi as int, a, b) + lsum(c, x, gi as int, js, i));
                assert(-(mv as int) <= sv as int <= mv as int);
            }
            crate::gendb_entry::work::put(&mut mass, gi, mv + av);
            crate::gendb_entry::work::put(&mut sums, gi, sv + vol);
        } else {
            over = true;
        }
    }
    proof {
        assert forall|h: int| 0 <= h < 4 implies #[trigger] cnts@[h] as int == rcnt(c, x, h, a, b) + lcnt(c, x, h, js, i + 1) by {
            assert(c0[h] as int == rcnt(c, x, h, a, b) + lcnt(c, x, h, js, i));
        }
        if !over {
            assert forall|h: int| 0 <= h < 4 implies {
                &&& #[trigger] sums@[h] as int == rsum(c, x, h, a, b) + lsum(c, x, h, js, i + 1)
                &&& mass@[h] as int == rmass(c, x, h, a, b) + lmass(c, x, h, js, i + 1)
                &&& mass@[h] as int <= i128_max()
            } by {
                assert(s0[h] as int == rsum(c, x, h, a, b) + lsum(c, x, h, js, i));
                assert(m0[h] as int == rmass(c, x, h, a, b) + lmass(c, x, h, js, i));
            }
        } else if over0 {
            let h = choose|h: int| 0 <= h < 4 && #[trigger] rmass(c, x, h, a, b) + lmass(c, x, h, js, i) > i128_max();
            lemma_l_bounds(c, x, h, js, i);
            assert(rmass(c, x, h, a, b) + lmass(c, x, h, js, i + 1) > i128_max());
        } else {
            assert(rmass(c, x, gi as int, a, b) + lmass(c, x, gi as int, js, i + 1) > i128_max());
        }
    }
    (sums, mass, cnts, over)
}

/// The end of a batch: the candidates' sums are the batch's lines' sums.
pub proof fn lemma_acc_batch(c: Cols, x: Ctx, sums: Seq<i128>, mass: Seq<i128>, cnts: Seq<usize>, over: bool,
    a: int, b: int, b2: int, js: Seq<usize>, n: int)
    requires
        a <= b <= b2,
        acc_ok(c, x, sums, mass, cnts, over, a, b, js, n),
        lr_eq(c, x, js, n, b, b2),
    ensures acc_ok(c, x, sums, mass, cnts, over, a, b2, Seq::<usize>::empty(), 0),
{
    let e = Seq::<usize>::empty();
    assert forall|gi: int| 0 <= gi < 4 implies {
        &&& rcnt(c, x, gi, a, b2) == rcnt(c, x, gi, a, b) + lcnt(c, x, gi, js, n)
        &&& rsum(c, x, gi, a, b2) == rsum(c, x, gi, a, b) + lsum(c, x, gi, js, n)
        &&& rmass(c, x, gi, a, b2) == rmass(c, x, gi, a, b) + lmass(c, x, gi, js, n)
    } by {
        lemma_r_split(c, x, gi, a, b, b2);
        assert(lcnt(c, x, gi, js, n) == rcnt(c, x, gi, b, b2));
    }
    assert forall|gi: int| 0 <= gi < 4 implies #[trigger] cnts[gi] as int == rcnt(c, x, gi, a, b2) + lcnt(c, x, gi, e, 0) by {
        assert(cnts[gi] as int == rcnt(c, x, gi, a, b) + lcnt(c, x, gi, js, n));
    }
    if !over {
        assert forall|gi: int| 0 <= gi < 4 implies #[trigger] sums[gi] as int == rsum(c, x, gi, a, b2) + lsum(c, x, gi, e, 0) by {
            assert(sums[gi] as int == rsum(c, x, gi, a, b) + lsum(c, x, gi, js, n));
        }
        assert forall|gi: int| 0 <= gi < 4 implies #[trigger] mass[gi] as int == rmass(c, x, gi, a, b2) + lmass(c, x, gi, e, 0) && mass[gi] as int <= i128_max() by {
            assert(sums[gi] as int == rsum(c, x, gi, a, b) + lsum(c, x, gi, js, n));
        }
    } else {
        let gi = choose|gi: int| 0 <= gi < 4 && #[trigger] rmass(c, x, gi, a, b) + lmass(c, x, gi, js, n) > i128_max();
        assert(rmass(c, x, gi, a, b2) + lmass(c, x, gi, e, 0) > i128_max());
    }
}

} // verus!
