//! The parallel scan: the lineitem groups `[ga, gb)` split into at most `workers` tasks of contiguous groups
//! (`tb`: task `t` covers `[tb(t), tb(t + 1))`, sizes differ by at most one group), one `fork_join`, and the merge of the
//! task sums (`merge_one`: counts add; sums and masses add while every merged mass stays within `i128::MAX`, else
//! the result is `over`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::{filled, put};
use super::model::*;
use super::lookup::*;
use super::kernel::*;
use super::cmap::{cmap_ok, smap2_ok};
use super::sfast::{SMW, HW, sfast_ok};

verus! {

/// Task boundary `i` of `nt` tasks over `[a, b)` in chunks of `chunk` groups, the remainder `b - a - chunk * nt`
/// spread one group each over the first tasks (so task sizes differ by at most one group when `chunk` is
/// `(b - a) / nt`).
pub open spec fn tb(a: int, b: int, chunk: int, nt: int, i: int) -> int {
    if i >= nt { b } else { a + chunk * i + if i < b - a - chunk * nt { i } else { b - a - chunk * nt } }
}

pub proof fn lemma_tb(a: int, b: int, chunk: int, nt: int, i: int, j: int)
    requires 0 <= a <= b, nt >= 1, chunk >= 0, chunk * nt <= b - a, 0 <= i <= j <= nt,
    ensures a <= tb(a, b, chunk, nt, i) <= tb(a, b, chunk, nt, j) <= b, tb(a, b, chunk, nt, 0) == a,
        tb(a, b, chunk, nt, nt) == b,
{
    assert(chunk * 0 == 0);
    assert(chunk * i <= chunk * j) by (nonlinear_arith) requires i <= j, chunk >= 0;
    assert(chunk * j <= chunk * nt) by (nonlinear_arith) requires j <= nt, chunk >= 0;
    assert(chunk * i >= 0) by (nonlinear_arith) requires i >= 0, chunk >= 0;
}

/// `tb(a, b, chunk, nt, i)` for `i < nt`.
pub fn tb_at(a: usize, b: usize, chunk: usize, nt: usize, i: usize) -> (r: usize)
    requires a <= b, nt >= 1, chunk * nt <= b - a, i < nt,
    ensures r as int == tb(a as int, b as int, chunk as int, nt as int, i as int),
{
    proof {
        lemma_tb(a as int, b as int, chunk as int, nt as int, i as int, nt as int);
        assert(chunk * i <= chunk * nt) by (nonlinear_arith) requires i <= nt;
    }
    let rem = (b - a) - chunk * nt;
    let extra = if i < rem { i } else { rem };
    a + chunk * i + extra
}

/// `jlo` grows with the group.
proof fn lemma_jlo_mono(c: Cols, g1: int, g2: int)
    requires 0 <= g1 <= g2, c.bs_l >= 1,
    ensures 0 <= jlo(c, g1) <= jlo(c, g2) <= c.n_l,
{
    assert(g1 * c.bs_l <= g2 * c.bs_l) by (nonlinear_arith) requires g1 <= g2, c.bs_l >= 1;
    assert(g1 * c.bs_l >= 0) by (nonlinear_arith) requires g1 >= 0, c.bs_l >= 1;
}

pub fn copy_i64s(v: &Vec<i64>) -> (r: Vec<i64>)
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

pub fn copy_u8s(v: &Vec<u8>) -> (r: Vec<u8>)
    ensures r@ == v@,
{
    let mut r: Vec<u8> = Vec::new();
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

/// The scan tasks over the groups `[ga, gb)`: at most `workers`, at least 4 groups each (one task for a small
/// range).
fn make_tasks(c: &Cols, s: Shifts, sd: bool, sk0: i64, cd: bool, ck0: i64, nk: &Vec<i64>, nc: &Vec<u8>, ntb: &Vec<u8>, sm: &Arc<Vec<u8>>, same: bool,
    cmv: bool, cm: &Arc<Vec<u32>>, smv: bool, sm2: &Arc<Vec<u32>>, rf: bool, sma: &Arc<Box<[u32; SMW]>>, ga: usize, gb: usize, workers: usize, Ghost(x): Ghost<Ctx>) -> (r: (Vec<ScanTask>, Ghost<int>))
    requires
        rf ==> sfast_ok(*c, s, sk0, ck0, cm@, sm2@, sma@, x),
        scan_ok(*c, s, sd, sk0, cd, ck0, nk@, nc@, ntb@, sm@, x),
        cmv ==> cmap_ok(*c, x, ck0, cm@),
        smv ==> smap2_ok(*c, x, sk0, sm2@),
        x.same == same,
        ga <= gb <= c.ls_bases@.len(),
        1 <= workers <= MAX_WORKERS,
    ensures ({
        let (tasks, chunk) = (r.0@, r.1@);
        let nt = tasks.len() as int;
        &&& 1 <= nt <= MAX_WORKERS
        &&& chunk >= 0
        &&& chunk * nt <= gb - ga
        &&& forall|i: int| 0 <= i < nt ==> {
            &&& (#[trigger] tasks[i]).pre()
            &&& tasks[i].cols == *c
            &&& tasks[i].x@ == x
            &&& tasks[i].g0 == tb(ga as int, gb as int, chunk, nt, i)
            &&& tasks[i].g1 == tb(ga as int, gb as int, chunk, nt, i + 1)
        }
    }),
{
    let span = gb - ga;
    let mut nt: usize = workers;
    let cap = span / 4 + 1;
    if cap < nt {
        nt = cap;
    }
    let chunk = span / nt;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(span as int, nt as int);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(span as int, nt as int);
        assert(chunk * nt <= span) by (nonlinear_arith)
            requires nt * chunk + span as int % nt as int == span, span as int % nt as int >= 0;
    }
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut t: usize = 0;
    while t < nt
        invariant
            scan_ok(*c, s, sd, sk0, cd, ck0, nk@, nc@, ntb@, sm@, x),
            cmv ==> cmap_ok(*c, x, ck0, cm@),
            smv ==> smap2_ok(*c, x, sk0, sm2@),
            rf ==> sfast_ok(*c, s, sk0, ck0, cm@, sm2@, sma@, x),
            x.same == same,
            ga <= gb <= c.ls_bases@.len(),
            span == gb - ga,
            1 <= nt <= MAX_WORKERS,
            chunk * nt <= span,
            t <= nt,
            tasks@.len() == t,
            forall|i: int| 0 <= i < t ==> {
                &&& (#[trigger] tasks@[i]).pre()
                &&& tasks@[i].cols == *c
                &&& tasks@[i].x@ == x
                &&& tasks@[i].g0 == tb(ga as int, gb as int, chunk as int, nt as int, i)
                &&& tasks@[i].g1 == tb(ga as int, gb as int, chunk as int, nt as int, i + 1)
            },
        decreases nt - t,
    {
        proof {
            lemma_tb(ga as int, gb as int, chunk as int, nt as int, t as int, t + 1);
        }
        let g0 = tb_at(ga, gb, chunk, nt, t);
        let g1 = if t + 1 == nt { gb } else { tb_at(ga, gb, chunk, nt, t + 1) };
        let sums = filled(4, 0i128);
        let mass = filled(4, 0i128);
        let cnts = filled(4, 0usize);
        proof {
            assert(sums@ =~= seq![0i128, 0, 0, 0]);
            assert(mass@ =~= seq![0i128, 0, 0, 0]);
            assert(cnts@ =~= seq![0usize, 0, 0, 0]);
        }
        let task = ScanTask {
            cols: *c, sh: s, s_dense: sd, s_key0: sk0, c_dense: cd, c_key0: ck0,
            nk: copy_i64s(nk), nc: copy_u8s(nc), nt: copy_u8s(ntb), sm: Arc::clone(sm), same, cmv, cm: Arc::clone(cm), smv, sm2: Arc::clone(sm2), g0, g1, sums, mass, cnts,
            cand_j: vec![0usize; BATCH], cand_p: vec![0usize; BATCH], cand_x: vec![0u8; BATCH], lcls: [0u8; BATCH], ccls: [0u8; BATCH],
            rf, sma: Arc::clone(sma), hm: [0u64; HW],
            x: Ghost(x),
        };
        tasks.push(task);
        t = t + 1;
    }
    (tasks, Ghost(chunk as int))
}

/// Merge one task's sums over `[b, b2)` into the sums over `[a, b)`.
fn merge_one(acc: ScanOut, o: &ScanOut, Ghost(c): Ghost<Cols>, Ghost(x): Ghost<Ctx>, Ghost(a): Ghost<int>,
    Ghost(b): Ghost<int>, Ghost(b2): Ghost<int>) -> (r: ScanOut)
    requires
        0 <= a <= b <= b2 <= c.n_l,
        acc_ok(c, x, acc.0@, acc.1@, acc.2@, acc.3, a, b, Seq::<usize>::empty(), 0),
        acc_ok(c, x, o.0@, o.1@, o.2@, o.3, b, b2, Seq::<usize>::empty(), 0),
    ensures acc_ok(c, x, r.0@, r.1@, r.2@, r.3, a, b2, Seq::<usize>::empty(), 0),
{
    let ghost e = Seq::<usize>::empty();
    let (mut sums, mut mass, mut cnts, over0) = acc;
    let mut over = over0 || o.3;
    proof {
        assert forall|gi: int| 0 <= gi < 4 implies {
            &&& rcnt(c, x, gi, a, b2) == rcnt(c, x, gi, a, b) + rcnt(c, x, gi, b, b2)
            &&& rsum(c, x, gi, a, b2) == rsum(c, x, gi, a, b) + rsum(c, x, gi, b, b2)
            &&& rmass(c, x, gi, a, b2) == rmass(c, x, gi, a, b) + rmass(c, x, gi, b, b2)
            &&& 0 <= rcnt(c, x, gi, a, b2) <= b2 - a
            &&& 0 <= rmass(c, x, gi, a, b) && 0 <= rmass(c, x, gi, b, b2)
        } by {
            lemma_r_split(c, x, gi, a, b, b2);
            lemma_r_bounds(c, x, gi, a, b2);
            lemma_r_bounds(c, x, gi, a, b);
            lemma_r_bounds(c, x, gi, b, b2);
        }
        if over0 {
            let gi = choose|gi: int| 0 <= gi < 4 && #[trigger] rmass(c, x, gi, a, b) + lmass(c, x, gi, e, 0) > i128_max();
            assert(rmass(c, x, gi, a, b2) + lmass(c, x, gi, e, 0) > i128_max());
        } else if o.3 {
            let gi = choose|gi: int| 0 <= gi < 4 && #[trigger] rmass(c, x, gi, b, b2) + lmass(c, x, gi, e, 0) > i128_max();
            assert(rmass(c, x, gi, a, b2) + lmass(c, x, gi, e, 0) > i128_max());
        }
    }
    let ghost s0 = sums@;
    let ghost m0 = mass@;
    let ghost c0 = cnts@;
    let mut gi: usize = 0;
    while gi < 4
        invariant
            0 <= a <= b <= b2 <= c.n_l,
            gi <= 4,
            sums@.len() == 4, mass@.len() == 4, cnts@.len() == 4,
            o.0@.len() == 4, o.1@.len() == 4, o.2@.len() == 4,
            acc_ok(c, x, s0, m0, c0, over0, a, b, e, 0),
            acc_ok(c, x, o.0@, o.1@, o.2@, o.3, b, b2, e, 0),
            forall|h: int| 0 <= h < 4 ==> {
                &&& rcnt(c, x, h, a, b2) == rcnt(c, x, h, a, b) + rcnt(c, x, h, b, b2)
                &&& rsum(c, x, h, a, b2) == rsum(c, x, h, a, b) + rsum(c, x, h, b, b2)
                &&& rmass(c, x, h, a, b2) == rmass(c, x, h, a, b) + rmass(c, x, h, b, b2)
                &&& 0 <= rcnt(c, x, h, a, b2) <= b2 - a
                &&& 0 <= rmass(c, x, h, a, b) && 0 <= rmass(c, x, h, b, b2)
            },
            over0 || o.3 ==> over,
            over ==> exists|h: int| 0 <= h < 4 && #[trigger] rmass(c, x, h, a, b2) + lmass(c, x, h, e, 0) > i128_max(),
            forall|h: int| 0 <= h < gi ==> #[trigger] cnts@[h] as int == rcnt(c, x, h, a, b2),
            forall|h: int| gi <= h < 4 ==> #[trigger] cnts@[h] == c0[h],
            !over ==> forall|h: int| 0 <= h < gi ==> #[trigger] sums@[h] as int == rsum(c, x, h, a, b2),
            !over ==> forall|h: int| 0 <= h < gi ==> #[trigger] mass@[h] as int == rmass(c, x, h, a, b2) && mass@[h] as int <= i128_max(),
            forall|h: int| gi <= h < 4 ==> #[trigger] sums@[h] == s0[h] && mass@[h] == m0[h],
        decreases 4 - gi,
    {
        let ghost (sp, mp, cp) = (sums@, mass@, cnts@);
        proof {
            assert(c0[gi as int] as int == rcnt(c, x, gi as int, a, b) + lcnt(c, x, gi as int, e, 0));
            assert(o.2@[gi as int] as int == rcnt(c, x, gi as int, b, b2) + lcnt(c, x, gi as int, e, 0));
            assert(cnts@[gi as int] == c0[gi as int]);
            assert(lcnt(c, x, gi as int, e, 0) == 0);
            assert(rcnt(c, x, gi as int, a, b2) == rcnt(c, x, gi as int, a, b) + rcnt(c, x, gi as int, b, b2));
            assert(0 <= rcnt(c, x, gi as int, a, b2) <= b2 - a);
            assert(cnts@[gi as int] + o.2@[gi as int] <= b2 - a);
        }
        let cv = cnts[gi] + o.2[gi];
        put(&mut cnts, gi, cv);
        if !over {
            let (ma, mo) = (mass[gi], o.1[gi]);
            let (sa, so) = (sums[gi], o.0[gi]);
            proof {
                assert(m0[gi as int] as int == rmass(c, x, gi as int, a, b) + lmass(c, x, gi as int, e, 0));
                assert(s0[gi as int] as int == rsum(c, x, gi as int, a, b) + lsum(c, x, gi as int, e, 0));
                assert(o.1@[gi as int] as int == rmass(c, x, gi as int, b, b2) + lmass(c, x, gi as int, e, 0));
                assert(o.0@[gi as int] as int == rsum(c, x, gi as int, b, b2) + lsum(c, x, gi as int, e, 0));
                lemma_r_bounds(c, x, gi as int, a, b);
                lemma_r_bounds(c, x, gi as int, b, b2);
                assert(0 <= ma as int <= i128_max() && 0 <= mo as int <= i128_max());
            }
            if (ma as u128) + (mo as u128) <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128 {
                put(&mut mass, gi, ma + mo);
                put(&mut sums, gi, sa + so);
            } else {
                over = true;
                proof {
                    assert(rmass(c, x, gi as int, a, b2) + lmass(c, x, gi as int, e, 0) > i128_max());
                }
            }
        }
        proof {
            assert forall|h: int| gi + 1 <= h < 4 implies #[trigger] sums@[h] == s0[h] && mass@[h] == m0[h] by {
                assert(sums@[h] == sp[h] && mass@[h] == mp[h]);
            }
            assert forall|h: int| gi + 1 <= h < 4 implies #[trigger] cnts@[h] == c0[h] by {
                assert(cnts@[h] == cp[h]);
            }
        }
        gi = gi + 1;
    }
    proof {
        assert forall|h: int| 0 <= h < 4 implies #[trigger] cnts@[h] as int == rcnt(c, x, h, a, b2) + lcnt(c, x, h, e, 0) by {}
        if !over {
            assert forall|h: int| 0 <= h < 4 implies #[trigger] sums@[h] as int == rsum(c, x, h, a, b2) + lsum(c, x, h, e, 0) by {}
            assert forall|h: int| 0 <= h < 4 implies #[trigger] mass@[h] as int == rmass(c, x, h, a, b2) + lmass(c, x, h, e, 0)
                && mass@[h] as int <= i128_max() by {}
        }
    }
    (sums, mass, cnts, over)
}

/// The scan of the groups `[ga, gb)` in parallel: its sums over the lines `[jlo(ga), jlo(gb))`.
pub fn run_scan(c: &Cols, s: Shifts, sd: bool, sk0: i64, cd: bool, ck0: i64, nk: &Vec<i64>, nc: &Vec<u8>, ntb: &Vec<u8>, sm: &Arc<Vec<u8>>, same: bool,
    cmv: bool, cm: &Arc<Vec<u32>>, smv: bool, sm2: &Arc<Vec<u32>>, rf: bool, sma: &Arc<Box<[u32; SMW]>>, ga: usize, gb: usize, workers: usize, dispatch: &mut Dispatch, Ghost(x): Ghost<Ctx>) -> (r: Result<ScanOut, WorkerFailure>)
    requires
        rf ==> sfast_ok(*c, s, sk0, ck0, cm@, sm2@, sma@, x),
        scan_ok(*c, s, sd, sk0, cd, ck0, nk@, nc@, ntb@, sm@, x),
        cmv ==> cmap_ok(*c, x, ck0, cm@),
        smv ==> smap2_ok(*c, x, sk0, sm2@),
        x.same == same,
        ga <= gb <= c.ls_bases@.len(),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(o) ==> acc_ok(*c, x, o.0@, o.1@, o.2@, o.3, jlo(*c, ga as int), jlo(*c, gb as int), Seq::<usize>::empty(), 0),
{
    let ghost e = Seq::<usize>::empty();
    let (tasks, chunk) = make_tasks(c, s, sd, sk0, cd, ck0, nk, nc, ntb, sm, same, cmv, cm, smv, sm2, rf, sma, ga, gb, workers, Ghost(x));
    let ghost tv = tasks@;
    let ghost nt = tv.len() as int;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(f) => return Err(f),
    };
    let ghost a = jlo(*c, ga as int);
    let mut acc: ScanOut = (filled(4, 0i128), filled(4, 0i128), filled(4, 0usize), false);
    proof {
        lemma_tb(ga as int, gb as int, chunk@, nt, 0, 0);
        assert(tb(ga as int, gb as int, chunk@, nt, 0) == ga);
        assert forall|h: int| 0 <= h < 4 implies #[trigger] acc.2@[h] as int == rcnt(*c, x, h, a, a) + lcnt(*c, x, h, e, 0) by {}
        assert forall|h: int| 0 <= h < 4 implies #[trigger] acc.0@[h] as int == rsum(*c, x, h, a, a) + lsum(*c, x, h, e, 0) by {}
        assert forall|h: int| 0 <= h < 4 implies #[trigger] acc.1@[h] as int == rmass(*c, x, h, a, a) + lmass(*c, x, h, e, 0)
            && acc.1@[h] as int <= i128_max() by {}
    }
    let n_out = outs.len();
    let mut t: usize = 0;
    while t < n_out
        invariant
            n_out == nt == outs@.len(),
            1 <= nt,
            chunk@ >= 0,
            chunk@ * nt <= gb - ga,
            ga <= gb <= c.ls_bases@.len(),
            c.bs_l >= 1,
            t <= nt,
            a == jlo(*c, ga as int),
            forall|i: int| 0 <= i < nt ==> {
                &&& (#[trigger] tv[i]).post(outs@[i])
                &&& tv[i].cols == *c
                &&& tv[i].x@ == x
                &&& tv[i].g0 == tb(ga as int, gb as int, chunk@, nt, i)
                &&& tv[i].g1 == tb(ga as int, gb as int, chunk@, nt, i + 1)
            },
            acc_ok(*c, x, acc.0@, acc.1@, acc.2@, acc.3, a, jlo(*c, tb(ga as int, gb as int, chunk@, nt, t as int)), e, 0),
        decreases nt - t,
    {
        let ghost t0 = tb(ga as int, gb as int, chunk@, nt, t as int);
        let ghost t1 = tb(ga as int, gb as int, chunk@, nt, t + 1);
        proof {
            lemma_tb(ga as int, gb as int, chunk@, nt, t as int, t + 1);
            lemma_tb(ga as int, gb as int, chunk@, nt, 0, t as int);
            lemma_jlo_mono(*c, ga as int, t0);
            lemma_jlo_mono(*c, t0, t1);
            assert(tv[t as int].post(outs@[t as int]));
        }
        acc = merge_one(acc, &outs[t], Ghost(*c), Ghost(x), Ghost(a), Ghost(jlo(*c, t0)), Ghost(jlo(*c, t1)));
        t = t + 1;
    }
    proof {
        assert(tb(ga as int, gb as int, chunk@, nt, nt) == gb);
    }
    Ok(acc)
}

} // verus!
