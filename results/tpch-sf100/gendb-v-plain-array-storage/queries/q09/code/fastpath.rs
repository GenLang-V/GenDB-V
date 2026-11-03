//! The fast path of the lineitem scan: `T` tasks over consecutive row ranges (`common::split`), each scanning its
//! range in blocks (`scan`), and the merge of their tables in range order (`lemma_table_merge`): counts and amounts
//! add, and the absolute amounts add (the merged mass must stay within `i128`).
use vstd::prelude::*;
use crate::agent::common::zeroed::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::filled;
use crate::link::expr::i128_max;
use crate::agent::tables::*;
use crate::agent::lines::*;
use crate::agent::answer::*;
use crate::agent::columns::*;
use crate::agent::nations::*;
use crate::agent::scan::*;
use crate::agent::common::split::*;

verus! {

/// The preallocated buffers of a task.
pub struct Bufs {
    pub cand: Vec<u32>,
    pub chk: Vec<u32>,
    pub rix: Vec<usize>,
    pub costb: Vec<i64>,
    pub slotb: Vec<u32>,
    pub orw: Vec<u64>,
}

pub open spec fn bufs_ok(b: Bufs) -> bool {
    &&& b.cand@.len() == BLK && b.chk@.len() == BLK && b.rix@.len() == BLK
    &&& b.costb@.len() == BLK && b.slotb@.len() == BLK && b.orw@.len() == BLK
}

/// Fresh buffers (calling thread).
pub fn new_bufs() -> (b: Bufs)
    ensures bufs_ok(b),
{
    Bufs { cand: zeros_u32(BLK), chk: zeros_u32(BLK), rix: zeros_usize(BLK), costb: zeros_i64(BLK),
        slotb: zeros_u32(BLK), orw: zeros_u64(BLK) }
}

/// One task of the scan: rows `lo..hi`.
pub struct LineTask {
    pub c: Cols,
    pub bits: Arc<Vec<u64>>,
    pub wl: Arc<Vec<u64>>,
    pub recs: Arc<Vec<Vec<i64>>>,
    pub ytab: Arc<Vec<u8>>,
    pub pc: [u8; 256],
    pub par: ScanPar,
    pub lo: usize,
    pub hi: usize,
    pub blk: usize,
    pub bufs: Bufs,
    pub acc: Vec<i128>,
    pub cnt: Vec<u64>,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
}

/// A task's result: its table and mass when `ok`, and the warming checksum (no meaning).
pub struct LineOut {
    pub acc: Vec<i128>,
    pub cnt: Vec<u64>,
    pub mass: u128,
    pub ok: bool,
    pub touch: u64,
}

/// Zero tables.
pub open spec fn zero_acc() -> Seq<i128> { Seq::new(NT as nat, |_i: int| 0i128) }
pub open spec fn zero_cnt() -> Seq<u64> { Seq::new(NT as nat, |_i: int| 0u64) }

/// The checksum value at which a block is one row long (every block length is correct; testing the checksum keeps
/// the warming reads in the compiled code).
pub const ONE_ROW_TOUCH: u64 = 0x9E37_79B9_7F4A_7C15;

impl WorkerTask for LineTask {
    type Output = LineOut;

    open spec fn pre(&self) -> bool {
        &&& scan_ok(self.c, self.bits@, self.wl@, self.recs@, self.ytab@, self.pc@, self.par, self.sv@, self.ps@)
        &&& self.lo <= self.hi <= self.c.nl
        &&& 1 <= self.blk <= BLK
        &&& bufs_ok(self.bufs)
        &&& self.acc@ == zero_acc() && self.cnt@ == zero_cnt()
    }

    open spec fn post(&self, out: LineOut) -> bool {
        out.ok ==> table_ok(out.acc@, out.cnt@, out.mass, self.sv@, self.ps@, self.lo as int, self.hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: LineOut) {
        let LineTask { c, bits, wl, recs, ytab, pc, par, lo, hi, blk, bufs, acc, cnt, sv, ps } = self;
        let ghost sv = sv@;
        let ghost ps = ps@;
        let bits: &Vec<u64> = &*bits;
        let wl: &Vec<u64> = &*wl;
        let recs: &Vec<Vec<i64>> = &*recs;
        let ytab: &Vec<u8> = &*ytab;
        let Bufs { mut cand, mut chk, mut rix, mut costb, mut slotb, mut orw } = bufs;
        let mut acc = acc;
        let mut cnt = cnt;
        let mut mass: u128 = 0;
        let mut touch: u64 = 0;
        proof { lemma_table_empty(acc@, cnt@, sv, ps, lo as int); }
        let mut b0 = lo;
        while b0 < hi
            invariant
                scan_ok(c, bits@, wl@, recs@, ytab@, pc@, par, sv, ps), lo <= b0 <= hi <= c.nl, 1 <= blk <= BLK,
                cand@.len() == BLK, chk@.len() == BLK, rix@.len() == BLK, costb@.len() == BLK, slotb@.len() == BLK,
                orw@.len() == BLK,
                table_ok(acc@, cnt@, mass, sv, ps, lo as int, b0 as int),
            decreases hi - b0,
        {
            let step = if touch == ONE_ROW_TOUCH { 1 } else { blk };
            let b1 = if hi - b0 > step { b0 + step } else { hi };
            let n = stage_filter(&c, bits, par, b0, b1, &mut cand, Ghost(wl@), Ghost(recs@), Ghost(ytab@), Ghost(pc@),
                Ghost(sv), Ghost(ps));
            stage_rank(&c, wl, recs, &pc, par, b0, &cand, n, &mut chk, &mut rix, Ghost(bits@), Ghost(recs@), Ghost(ytab@),
                Ghost(sv), Ghost(ps), Ghost(b1 as int));
            touch = touch.wrapping_add(touch_recs(recs, &chk, &rix, n, Ghost(sv), Ghost(ps), Ghost(par), Ghost(cand@), Ghost(b0 as int)));
            touch = touch.wrapping_add(touch_cols(&c, b0, &cand, n, Ghost(b1 as int)));
            if !stage_match(&c, recs, par, b0, &cand, n, &chk, &rix, &mut costb, &mut slotb, &mut orw,
                Ghost(bits@), Ghost(wl@), Ghost(ytab@), Ghost(pc@), Ghost(sv), Ghost(ps), Ghost(b1 as int)) {
                return LineOut { acc, cnt, mass, ok: false, touch };
            }
            touch = touch.wrapping_add(touch_orders(&c, &orw, n));
            if !stage_acc(&c, ytab, b0, &cand, n, &costb, &slotb, &orw, &mut acc, &mut cnt, &mut mass,
                Ghost(bits@), Ghost(wl@), Ghost(recs@), Ghost(pc@), Ghost(par), Ghost(sv), Ghost(ps), Ghost(lo as int), Ghost(b1 as int)) {
                return LineOut { acc, cnt, mass, ok: false, touch };
            }
            b0 = b1;
        }
        LineOut { acc, cnt, mass, ok: true, touch }
    }
}

// ------------------------------------------------------------------------------------------------ the merge

/// Tables of adjacent ranges add (the merged mass within `i128`).
pub proof fn lemma_table_merge(a1: Seq<i128>, c1: Seq<u64>, m1: u128, a2: Seq<i128>, c2: Seq<u64>, m2: u128,
    sv: StoresView, ps: Seq<Literal>, lo: int, mid: int, hi: int, a3: Seq<i128>, c3: Seq<u64>, m3: u128)
    requires
        table_ok(a1, c1, m1, sv, ps, lo, mid), table_ok(a2, c2, m2, sv, ps, mid, hi), lo <= mid <= hi,
        a3.len() == NT, c3.len() == NT,
        forall|ix: int| 0 <= ix < NT ==> #[trigger] a3[ix] as int == a1[ix] + a2[ix] && c3[ix] as int == c1[ix] + c2[ix],
        m3 as int == m1 + m2, m3 as int <= i128_max(),
    ensures table_ok(a3, c3, m3, sv, ps, lo, hi),
{
    lemma_msum_split(sv, ps, lo, mid, hi);
    assert forall|ix: int| 0 <= ix < NT implies #[trigger] a3[ix] as int == tsum(sv, ps, tgrp(ix), tyr(ix), 1, lo, hi)
        && c3[ix] as int == tsum(sv, ps, tgrp(ix), tyr(ix), 0, lo, hi) by {
        lemma_tsum_split(sv, ps, tgrp(ix), tyr(ix), 1, lo, mid, hi);
        lemma_tsum_split(sv, ps, tgrp(ix), tyr(ix), 0, lo, mid, hi);
    }
    assert forall|a: int, y: int| #[trigger] tsum(sv, ps, a, y, 0, lo, hi) > 0 implies 0 <= a < NG && Y0 <= y < Y0 + YW by {
        lemma_tsum_split(sv, ps, a, y, 0, lo, mid, hi);
        lemma_tsum_bounds(sv, ps, a, y, lo, mid);
        lemma_tsum_bounds(sv, ps, a, y, mid, hi);
        if tsum(sv, ps, a, y, 0, lo, mid) > 0 {
        } else {
            assert(tsum(sv, ps, a, y, 0, mid, hi) > 0);
        }
    }
}

/// The merged table of a task's table into the running table (`None` when the merged mass leaves `i128`).
fn merge_into(acc: &mut Vec<i128>, cnt: &mut Vec<u64>, mass: u128, o: &LineOut,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(lo): Ghost<int>, Ghost(mid): Ghost<int>, Ghost(hi): Ghost<int>)
    -> (r: Option<u128>)
    requires
        table_ok(old(acc)@, old(cnt)@, mass, sv, ps, lo, mid), table_ok(o.acc@, o.cnt@, o.mass, sv, ps, mid, hi),
        0 <= lo <= mid <= hi <= usize::MAX,
    ensures r matches Some(m3) ==> table_ok(final(acc)@, final(cnt)@, m3, sv, ps, lo, hi),
{
    let m3 = mass + o.mass;
    if m3 > i128::MAX as u128 {
        return None;
    }
    let ghost a1 = acc@;
    let ghost c1 = cnt@;
    let mut ix: usize = 0;
    while ix < NT
        invariant
            ix <= NT, acc@.len() == NT, cnt@.len() == NT, a1.len() == NT, c1.len() == NT,
            table_ok(a1, c1, mass, sv, ps, lo, mid), table_ok(o.acc@, o.cnt@, o.mass, sv, ps, mid, hi),
            0 <= lo <= mid <= hi <= usize::MAX, m3 as int == mass + o.mass, m3 as int <= i128_max(),
            forall|j: int| 0 <= j < ix ==> #[trigger] acc@[j] as int == a1[j] + o.acc@[j] && cnt@[j] as int == c1[j] + o.cnt@[j],
            forall|j: int| ix <= j < NT ==> #[trigger] acc@[j] == a1[j] && cnt@[j] == c1[j],
        decreases NT - ix,
    {
        proof {
            let (a, y) = (tgrp(ix as int), tyr(ix as int));
            lemma_tsum_bounds(sv, ps, a, y, lo, mid);
            lemma_tsum_bounds(sv, ps, a, y, mid, hi);
            lemma_count_le(sv, ps, a, y, lo, mid);
            lemma_count_le(sv, ps, a, y, mid, hi);
            assert(acc@[ix as int] == a1[ix as int]);
        }
        acc[ix] = acc[ix] + o.acc[ix];
        cnt[ix] = cnt[ix] + o.cnt[ix];
        ix = ix + 1;
    }
    proof {
        lemma_table_merge(a1, c1, mass, o.acc@, o.cnt@, o.mass, sv, ps, lo, mid, hi, acc@, cnt@, m3);
    }
    Some(m3)
}

/// The fast scan of all lineitem rows by `t` tasks: `Ok(Some(..))` the table of all rows, `Ok(None)` when some task
/// could not place a row (or the mass left `i128`).
pub fn fast_scan(c: &Cols, bits: Arc<Vec<u64>>, wl: Arc<Vec<u64>>, recs: Arc<Vec<Vec<i64>>>, ytab: Arc<Vec<u8>>,
    pc: [u8; 256], par: ScanPar, workers: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Result<Option<(Vec<i128>, Vec<u64>, u128)>, WorkerFailure>)
    requires
        scan_ok(*c, bits@, wl@, recs@, ytab@, pc@, par, sv, ps), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some((acc, cnt, mass))) ==> table_ok(acc@, cnt@, mass, sv, ps, 0, n_l(sv)),
{
    let nl = c.nl;
    let k = workers;
    // rows per block: long blocks for one worker (more loads in flight), short ones for many (less cache pressure)
    let blk = if workers == 1 { BLK } else { BLK_PAR };
    let mut tasks: Vec<LineTask> = Vec::new();
    let mut t: usize = 0;
    while t < k
        invariant
            t <= k, k == workers, 1 <= k <= MAX_WORKERS, tasks@.len() == t, nl == c.nl, 1 <= blk <= BLK,
            scan_ok(*c, bits@, wl@, recs@, ytab@, pc@, par, sv, ps),
            forall|j: int| 0 <= j < t ==> (#[trigger] tasks@[j]).pre() && tasks@[j].sv@ == sv && tasks@[j].ps@ == ps
                && tasks@[j].lo == split(nl as int, k as int, j) && tasks@[j].hi == split(nl as int, k as int, j + 1),
        decreases k - t,
    {
        proof { lemma_split(nl as int, k as int, t as int, t + 1); lemma_split(nl as int, k as int, t + 1, k as int); }
        let lo = split_exec(nl, k, t);
        let hi = split_exec(nl, k, t + 1);
        let task = LineTask { c: *c, bits: bits.clone(), wl: wl.clone(), recs: recs.clone(), ytab: ytab.clone(), pc, par,
            lo, hi, blk, bufs: new_bufs(), acc: zeros_i128(NT), cnt: zeros_u64(NT), sv: Ghost(sv), ps: Ghost(ps) };
        proof {
            assert(task.acc@ =~= zero_acc());
            assert(task.cnt@ =~= zero_cnt());
        }
        tasks.push(task);
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = if k == 1 {
        let task = tasks.pop().unwrap();
        assert(task == tv[0]);
        let o = task.run();
        let mut v: Vec<LineOut> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, tasks) {
            Ok(o) => o,
            Err(e) => { return Err(e); },
        }
    };
    assert(outs@.len() == k && forall|j: int| 0 <= j < k ==> #[trigger] tv[j].post(outs@[j]));
    // merge in range order
    let mut acc: Vec<i128> = zeros_i128(NT);
    let mut cnt: Vec<u64> = zeros_u64(NT);
    let mut mass: u128 = 0;
    proof {
        assert(acc@ =~= zero_acc());
        assert(cnt@ =~= zero_cnt());
        lemma_table_empty(acc@, cnt@, sv, ps, 0);
        lemma_split(nl as int, k as int, 0, k as int);
    }
    let mut j: usize = 0;
    while j < k
        invariant
            j <= k, k == workers, 1 <= k <= MAX_WORKERS, outs@.len() == k, nl == c.nl, cols_ok(*c, sv),
            forall|q: int| 0 <= q < k ==> #[trigger] tv[q].post(outs@[q]) && tv[q].sv@ == sv && tv[q].ps@ == ps
                && tv[q].lo == split(nl as int, k as int, q) && tv[q].hi == split(nl as int, k as int, q + 1),
            table_ok(acc@, cnt@, mass, sv, ps, 0, split(nl as int, k as int, j as int)),
        decreases k - j,
    {
        proof { lemma_split(nl as int, k as int, j as int, j + 1); lemma_split(nl as int, k as int, j + 1, k as int); }
        let o = &outs[j];
        if !o.ok {
            return Ok(None);
        }
        proof { assert(tv[j as int].post(outs@[j as int])); }
        match merge_into(&mut acc, &mut cnt, mass, o, Ghost(sv), Ghost(ps), Ghost(0), Ghost(split(nl as int, k as int, j as int)),
            Ghost(split(nl as int, k as int, j + 1))) {
            Some(m3) => { mass = m3; },
            None => { return Ok(None); },
        }
        j = j + 1;
    }
    proof { lemma_split(nl as int, k as int, k as int, k as int); }
    Ok(Some((acc, cnt, mass)))
}

} // verus!
