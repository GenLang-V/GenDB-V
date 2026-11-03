//! The parallel scan over the part rows (fast path without part_bcs's index).
//!
//! The part rows `0 .. n` are split into contiguous ranges, one worker task each (`ScanTask`). A task walks its
//! rows block by block: a row matches when its p_brand and p_container dictionary indices are those of `$1` and
//! `$2` (`tb`, `tc`; in a block both are the block's base plus the row's U8 code, so a block whose bases cannot
//! reach them is skipped); a matching row adds `lookup::part_sum` of its key. Its output is the exact sum of
//! l_extendedprice over the kept rows of its part rows and whether one is kept (`range_sum`, `range_cnt` over
//! `bind::zrows`), or `None` when a threshold leaves the fast range. The calling thread adds the outputs in range
//! order (`merge`). Sums stay inside `i128`: every partial sum is bounded by the total absolute mass, at most
//! `|lineitem| * 10^15` because part keys are distinct (`vals::lemma_mass_bound`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::join::*;
use crate::link::expr::ival;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::{WorkerTask, MAX_WORKERS};
use crate::stores::li_pkqty::interface as LI;
use crate::stores::custpart::interface as CPI;
use crate::stores::custpart::interface::common::colfmt as CF;
use crate::stores::custpart::interface::common::read::lemma_div_lt;
use super::vals::*;
use super::bind::*;
use super::lookup::*;

verus! {

/// Bound of every partial sum's absolute mass (`2^115`).
pub open spec fn mass_max() -> int {
    0x8_0000_0000_0000_0000_0000_0000_0000
}

/// The part extents the scan reads (whole parts).
#[derive(Clone, Copy)]
pub struct PaCols {
    /// Number of stored part rows.
    pub n: usize,
    /// Rows per block.
    pub bs: u64,
    pub pk: &'static [u32],
    pub pkb: &'static [i64],
    pub br: &'static [u8],
    pub brb: &'static [u64],
    pub ct: &'static [u8],
    pub ctb: &'static [u64],
}

/// The extents are the parts.
pub open spec fn pa_cols_ok(c: PaCols, cp: Seq<PartView>) -> bool {
    &&& pa_facts(cp)
    &&& c.n == n_pa(cp)
    &&& c.bs == pa_bs(cp)
    &&& c.pk@ == CF::u32s(cp[pp(CPI::PA_PARTKEY_CODES)])
    &&& c.pkb@ == CF::i64s(cp[pp(CPI::PA_PARTKEY_BASE)])
    &&& c.br@ == CF::u8s(cp[pp(CPI::PA_BRAND_CODES)])
    &&& c.brb@ == CF::u64s(cp[pp(CPI::PA_BRAND_BASE)])
    &&& c.ct@ == CF::u8s(cp[pp(CPI::PA_CONTAINER_CODES)])
    &&& c.ctb@ == CF::u64s(cp[pp(CPI::PA_CONTAINER_BASE)])
}

/// Per part value row: the kept SUM, count and mass over the index-ordered lineitem value rows.
pub open spec fn fsum(lp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>) -> spec_fn(Row) -> int {
    |z: Row| psum(irows(lp), b, c, z)
}

pub open spec fn fcnt(lp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>) -> spec_fn(Row) -> int {
    |z: Row| pcnt(irows(lp), b, c, z)
}

pub open spec fn fmass(lp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>) -> spec_fn(Row) -> int {
    |z: Row| pmass(irows(lp), b, c, z)
}

/// Sums over the part rows `a .. e`.
pub open spec fn range_sum(lp: Seq<PartView>, cp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>, a: int, e: int) -> int {
    sum_of(zrows(cp).subrange(a, e), fsum(lp, b, c))
}

pub open spec fn range_cnt(lp: Seq<PartView>, cp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>, a: int, e: int) -> int {
    sum_of(zrows(cp).subrange(a, e), fcnt(lp, b, c))
}

pub open spec fn range_mass(lp: Seq<PartView>, cp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>, a: int, e: int) -> int {
    sum_of(zrows(cp).subrange(a, e), fmass(lp, b, c))
}

/// The dictionary indices of `$1` and `$2`, and the total mass bound.
pub open spec fn targets_ok(lp: Seq<PartView>, cp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>, tb: u64, tc: u64) -> bool {
    &&& 0 <= tb < n_bd(cp)
    &&& CF::text_of(bd_o(cp), bd_y(cp), tb as int) == b
    &&& 0 <= tc < n_cd(cp)
    &&& CF::text_of(cd_o(cp), cd_y(cp), tc as int) == c
    &&& sum_of(zrows(cp), fmass(lp, b, c)) <= mass_max()
}

// ------------------------------------------------------------------------------------------------ range sums

/// A sum over `a .. e` splits at `m`.
pub proof fn lemma_sum_of_split(zs: Seq<Row>, f: spec_fn(Row) -> int, a: int, m: int, e: int)
    requires 0 <= a <= m <= e <= zs.len(),
    ensures sum_of(zs.subrange(a, e), f) == sum_of(zs.subrange(a, m), f) + sum_of(zs.subrange(m, e), f),
{
    assert(zs.subrange(a, e) =~= zs.subrange(a, m) + zs.subrange(m, e));
    lemma_sum_of_append(zs.subrange(a, m), zs.subrange(m, e), f);
}

/// Per part value row: `|psum| <= pmass`, `pcnt >= 0`, `pmass >= 0` (typed lineitem rows).
pub proof fn lemma_part_bounds(lp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>, z: Row)
    requires li_facts(lp), LI::has_idx(lp),
    ensures
        -fmass(lp, b, c)(z) <= fsum(lp, b, c)(z) <= fmass(lp, b, c)(z),
        fcnt(lp, b, c)(z) >= 0,
        fmass(lp, b, c)(z) >= 0,
{
    lemma_irows_ok(lp);
    lemma_part_sums(irows(lp), b, c, z);
}

/// Range sums: `|sum| <= mass <= total mass`, `count >= 0`.
pub proof fn lemma_range_bounds(lp: Seq<PartView>, cp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>, a: int, e: int)
    requires li_facts(lp), LI::has_idx(lp), 0 <= a <= e <= zrows(cp).len(),
    ensures
        -range_mass(lp, cp, b, c, a, e) <= range_sum(lp, cp, b, c, a, e) <= range_mass(lp, cp, b, c, a, e),
        range_cnt(lp, cp, b, c, a, e) >= 0,
        range_mass(lp, cp, b, c, a, e) <= sum_of(zrows(cp), fmass(lp, b, c)),
{
    let zs = zrows(cp);
    let w = zs.subrange(a, e);
    assert forall|i: int| 0 <= i < w.len() implies -fmass(lp, b, c)(#[trigger] w[i]) <= fsum(lp, b, c)(w[i]) <= fmass(lp, b, c)(w[i])
        && fcnt(lp, b, c)(w[i]) >= 0 by {
        lemma_part_bounds(lp, b, c, w[i]);
    }
    crate::agent::sqlmain::lemma_sum_of_within(w, fsum(lp, b, c), fmass(lp, b, c));
    lemma_sum_of_nonneg(w, fcnt(lp, b, c));
    assert forall|i: int| 0 <= i < zs.len() implies fmass(lp, b, c)(#[trigger] zs[i]) >= 0 by {
        lemma_part_bounds(lp, b, c, zs[i]);
    }
    lemma_sum_of_sub_le(zs, fmass(lp, b, c), a, e);
}

// ------------------------------------------------------------------------------------------------ one part row

/// Row `j` lies in block `g` (`g * bs <= j < (g + 1) * bs`): its block is `j / bs`.
proof fn lemma_block(j: int, g: int, bs: int)
    requires bs >= 1, g >= 0, g * bs <= j < (g + 1) * bs,
    ensures j / bs == g,
{
    assert((g + 1) * bs == g * bs + bs) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j, bs, g, j - g * bs);
}

/// A part row matches exactly when its dictionary indices are the targets'; a row that does not match keeps no
/// lineitem row.
pub proof fn lemma_match(lp: Seq<PartView>, cp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>, tb: u64, tc: u64, j: int)
    requires
        li_facts(lp),
        LI::has_idx(lp),
        pa_facts(cp),
        targets_ok(lp, cp, b, c, tb, tc),
        0 <= j < n_pa(cp),
    ensures
        (bidx_at(cp, j) == tb && cidx_at(cp, j) == tc) ==> zrow(cp, j) == seq![Val::Int(pkey_at(cp, j)), Val::Text(b), Val::Text(c)],
        !(bidx_at(cp, j) == tb && cidx_at(cp, j) == tc) ==>
            fsum(lp, b, c)(zrow(cp, j)) == 0 && fcnt(lp, b, c)(zrow(cp, j)) == 0 && fmass(lp, b, c)(zrow(cp, j)) == 0,
        zrows(cp)[j] == zrow(cp, j),
{
    let z = zrow(cp, j);
    let ys = irows(lp);
    if bidx_at(cp, j) != tb {
        CF::lemma_dict_distinct(bd_o(cp), bd_y(cp), n_bd(cp), bidx_at(cp, j), tb as int);
        assert(z[1] != Val::Text(b));
    } else if cidx_at(cp, j) != tc {
        CF::lemma_dict_distinct(cd_o(cp), cd_y(cp), n_cd(cp), cidx_at(cp, j), tc as int);
        assert(z[2] != Val::Text(c));
    }
    if !(bidx_at(cp, j) == tb && cidx_at(cp, j) == tc) {
        assert forall|i: int| 0 <= i < ys.len() implies !kept(ys, b, c, #[trigger] ys[i], z) by {}
        lemma_sum_of_zero(ys, tsum(ys, b, c, z));
        lemma_sum_of_zero(ys, tcnt(ys, b, c, z));
        lemma_sum_of_zero(ys, tmass(ys, b, c, z));
    } else {
        assert(z =~= seq![Val::Int(pkey_at(cp, j)), Val::Text(b), Val::Text(c)]);
    }
}

// ------------------------------------------------------------------------------------------------ the worker task

/// One worker's share: the part rows `j_lo .. j_hi`.
pub struct ScanTask {
    pub li: LiCols,
    pub pa: PaCols,
    pub tb: u64,
    pub tc: u64,
    pub j_lo: usize,
    pub j_hi: usize,
    pub lp: Ghost<Seq<PartView>>,
    pub cp: Ghost<Seq<PartView>>,
    pub b: Ghost<Seq<u8>>,
    pub c: Ghost<Seq<u8>>,
}

/// The task's inputs.
pub open spec fn task_ok(t: ScanTask) -> bool {
    &&& li_cols_ok(t.li, t.lp@)
    &&& pa_cols_ok(t.pa, t.cp@)
    &&& targets_ok(t.lp@, t.cp@, t.b@, t.c@, t.tb, t.tc)
    &&& t.j_lo <= t.j_hi <= t.pa.n
}

/// A range's output: the exact sum and whether a row is kept.
pub open spec fn out_ok(lp: Seq<PartView>, cp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>, a: int, e: int, out: Option<(i128, bool)>) -> bool {
    out matches Some((s, any)) ==> s == range_sum(lp, cp, b, c, a, e) && any == (range_cnt(lp, cp, b, c, a, e) > 0)
}

/// The scan of the part rows `j_lo .. j_hi`.
pub fn scan_range(li: &LiCols, pa: &PaCols, tb: u64, tc: u64, j_lo: usize, j_hi: usize,
    Ghost(lp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(b): Ghost<Seq<u8>>, Ghost(c): Ghost<Seq<u8>>)
    -> (out: Option<(i128, bool)>)
    requires
        li_cols_ok(*li, lp),
        pa_cols_ok(*pa, cp),
        targets_ok(lp, cp, b, c, tb, tc),
        j_lo <= j_hi <= pa.n,
    ensures out_ok(lp, cp, b, c, j_lo as int, j_hi as int, out),
    no_unwind
{
    let ghost zs = zrows(cp);
    let mut acc: i128 = 0;
    let mut any = false;
    let mut j = j_lo;
    proof {
        assert(zs.subrange(j_lo as int, j_lo as int) =~= Seq::<Row>::empty());
    }
    while j < j_hi
        invariant
            li_cols_ok(*li, lp),
            pa_cols_ok(*pa, cp),
            targets_ok(lp, cp, b, c, tb, tc),
            zs == zrows(cp),
            j_lo <= j <= j_hi <= pa.n,
            acc == range_sum(lp, cp, b, c, j_lo as int, j as int),
            any == (range_cnt(lp, cp, b, c, j_lo as int, j as int) > 0),
        decreases j_hi - j,
    {
        let g = (j as u64 / pa.bs) as usize;
        let rem = j as u64 % pa.bs;
        let step = pa.bs - rem;
        let g_end = if step < (j_hi - j) as u64 { j + step as usize } else { j_hi };
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j as int, pa.bs as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(j as int, pa.bs as int);
            lemma_div_lt(j as int, pa.bs as int, pa.brb@.len() as int);
            lemma_div_lt(j as int, pa.bs as int, pa.ctb@.len() as int);
            lemma_div_lt(j as int, pa.bs as int, pa.pkb@.len() as int);
            assert(g * pa.bs + rem == j) by (nonlinear_arith) requires pa.bs * g + rem == j;
            assert(g_end <= (g + 1) * pa.bs) by (nonlinear_arith) requires g * pa.bs + rem == j, step == pa.bs - rem, g_end <= j + step;
        }
        let bb = pa.brb[g];
        let cb = pa.ctb[g];
        if tb >= bb && tb - bb < 256 && tc >= cb && tc - cb < 256 {
            let xb = (tb - bb) as u8;
            let xc = (tc - cb) as u8;
            while j < g_end
                invariant
                    li_cols_ok(*li, lp),
                    pa_cols_ok(*pa, cp),
                    targets_ok(lp, cp, b, c, tb, tc),
                    zs == zrows(cp),
                    j_lo <= j <= g_end <= j_hi <= pa.n,
                    g * pa.bs <= j,
                    g_end <= (g + 1) * pa.bs,
                    g < pa.brb@.len() && g < pa.ctb@.len() && g < pa.pkb@.len(),
                    bb == pa.brb@[g as int] && cb == pa.ctb@[g as int],
                    xb as int == tb - bb && xc as int == tc - cb,
                    acc == range_sum(lp, cp, b, c, j_lo as int, j as int),
                    any == (range_cnt(lp, cp, b, c, j_lo as int, j as int) > 0),
                decreases g_end - j,
            {
                proof {
                    lemma_block(j as int, g as int, pa.bs as int);
                    lemma_match(lp, cp, b, c, tb, tc, j as int);
                    lemma_sum_of_sub_push(zs, fsum(lp, b, c), j_lo as int, j as int);
                    lemma_sum_of_sub_push(zs, fcnt(lp, b, c), j_lo as int, j as int);
                    lemma_range_bounds(lp, cp, b, c, j_lo as int, j as int);
                    lemma_range_bounds(lp, cp, b, c, j_lo as int, j + 1);
                    lemma_part_bounds(lp, b, c, zs[j as int]);
                    lemma_sum_of_sub_push(zs, fmass(lp, b, c), j_lo as int, j as int);
                }
                if pa.br[j] == xb && pa.ct[j] == xc {
                    let k = pa.pkb[g] + pa.pk[j] as i64;
                    let ghost z = zrow(cp, j as int);
                    let r = part_sum(li, k, Ghost(lp), Ghost(b), Ghost(c), Ghost(z));
                    match r {
                        None => return None,
                        Some((s, a)) => {
                            acc = acc + s;
                            any = any || a;
                        },
                    }
                }
                j = j + 1;
            }
        } else {
            proof {
                // No row of this block can reach the target indices: the rows j .. g_end add nothing.
                assert forall|i: int| j <= i < g_end implies fsum(lp, b, c)(#[trigger] zs[i]) == 0 && fcnt(lp, b, c)(zs[i]) == 0 by {
                    lemma_block(i, g as int, pa.bs as int);
                    lemma_match(lp, cp, b, c, tb, tc, i);
                }
                let w = zs.subrange(j as int, g_end as int);
                assert forall|i: int| 0 <= i < w.len() implies fsum(lp, b, c)(#[trigger] w[i]) == 0 && fcnt(lp, b, c)(w[i]) == 0 by {
                    assert(w[i] == zs[j + i]);
                }
                lemma_sum_of_zero(w, fsum(lp, b, c));
                lemma_sum_of_zero(w, fcnt(lp, b, c));
                lemma_sum_of_split(zs, fsum(lp, b, c), j_lo as int, j as int, g_end as int);
                lemma_sum_of_split(zs, fcnt(lp, b, c), j_lo as int, j as int, g_end as int);
            }
            j = g_end;
        }
    }
    Some((acc, any))
}

impl WorkerTask for ScanTask {
    type Output = Option<(i128, bool)>;

    open spec fn pre(&self) -> bool {
        task_ok(*self)
    }

    open spec fn post(&self, out: Option<(i128, bool)>) -> bool {
        out_ok(self.lp@, self.cp@, self.b@, self.c@, self.j_lo as int, self.j_hi as int, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.j_lo as u64, self.j_hi as u64)
    }

    fn run(self) -> (out: Option<(i128, bool)>) {
        scan_range(&self.li, &self.pa, self.tb, self.tc, self.j_lo, self.j_hi, self.lp, self.cp, self.b, self.c)
    }
}

// ------------------------------------------------------------------------------------------------ tasks and merge

/// The tasks `t` of a partition `bnds` of the part rows (task `t` covers `bnds[t] .. bnds[t + 1]`).
pub open spec fn tasks_ok(tasks: Seq<ScanTask>, bnds: Seq<int>, li: LiCols, pa: PaCols, tb: u64, tc: u64,
    lp: Seq<PartView>, cp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>) -> bool {
    &&& bnds.len() == tasks.len() + 1
    &&& bnds[0] == 0
    &&& forall|t: int| 0 <= t < tasks.len() ==> {
        &&& (#[trigger] tasks[t]).j_lo == bnds[t]
        &&& tasks[t].j_hi == bnds[t + 1]
        &&& tasks[t].li == li
        &&& tasks[t].pa == pa
        &&& tasks[t].tb == tb && tasks[t].tc == tc
        &&& tasks[t].lp@ == lp && tasks[t].cp@ == cp && tasks[t].b@ == b && tasks[t].c@ == c
        &&& tasks[t].pre()
    }
}

/// `ntasks` contiguous ranges of about equal size covering every part row.
pub fn make_tasks(li: &LiCols, pa: &PaCols, tb: u64, tc: u64, ntasks: usize,
    Ghost(lp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(b): Ghost<Seq<u8>>, Ghost(c): Ghost<Seq<u8>>)
    -> (r: (Vec<ScanTask>, Ghost<Seq<int>>))
    requires
        li_cols_ok(*li, lp),
        pa_cols_ok(*pa, cp),
        targets_ok(lp, cp, b, c, tb, tc),
        1 <= ntasks <= MAX_WORKERS,
    ensures
        r.0@.len() == ntasks,
        tasks_ok(r.0@, r.1@, *li, *pa, tb, tc, lp, cp, b, c),
        r.1@[ntasks as int] == pa.n,
{
    let mut tasks: Vec<ScanTask> = Vec::new();
    let ghost mut bnds: Seq<int> = seq![0int];
    let mut a: usize = 0;
    let mut t: usize = 0;
    while t < ntasks
        invariant
            li_cols_ok(*li, lp),
            pa_cols_ok(*pa, cp),
            targets_ok(lp, cp, b, c, tb, tc),
            1 <= ntasks <= MAX_WORKERS,
            t <= ntasks,
            a <= pa.n,
            t == ntasks ==> a == pa.n,
            tasks@.len() == t,
            bnds[t as int] == a,
            tasks_ok(tasks@, bnds, *li, *pa, tb, tc, lp, cp, b, c),
        decreases ntasks - t,
    {
        proof {
            let num = (t as int + 1) * (pa.n as int);
            assert(num <= (ntasks as int) * (pa.n as int)) by (nonlinear_arith)
                requires num == (t as int + 1) * (pa.n as int), t + 1 <= ntasks, pa.n >= 0;
            assert(0 <= num <= 64 * 0xffff_ffff_ffff_ffff) by (nonlinear_arith)
                requires num == (t as int + 1) * (pa.n as int), t + 1 <= 64, 0 <= pa.n <= 0xffff_ffff_ffff_ffff;
            assert(num / (ntasks as int) <= pa.n as int) by (nonlinear_arith)
                requires num <= (ntasks as int) * (pa.n as int), ntasks >= 1, num >= 0;
        }
        let e0 = ((t as u128 + 1) * pa.n as u128 / ntasks as u128) as usize;
        let e1 = if e0 < a { a } else { e0 };
        let e = if t + 1 == ntasks { pa.n } else { e1 };
        let task = ScanTask { li: *li, pa: *pa, tb, tc, j_lo: a, j_hi: e, lp: Ghost(lp), cp: Ghost(cp), b: Ghost(b), c: Ghost(c) };
        let ghost old_tasks = tasks@;
        tasks.push(task);
        proof {
            bnds = bnds.push(e as int);
            assert forall|k: int| 0 <= k < tasks@.len() implies {
                &&& (#[trigger] tasks@[k]).j_lo == bnds[k]
                &&& tasks@[k].j_hi == bnds[k + 1]
                &&& tasks@[k].li == *li
                &&& tasks@[k].pa == *pa
                &&& tasks@[k].tb == tb && tasks@[k].tc == tc
                &&& tasks@[k].lp@ == lp && tasks@[k].cp@ == cp && tasks@[k].b@ == b && tasks@[k].c@ == c
                &&& tasks@[k].pre()
            } by {
                if k < t {
                    assert(tasks@[k] == old_tasks[k]);
                }
            }
        }
        a = e;
        t = t + 1;
    }
    (tasks, Ghost(bnds))
}

/// Adds the task outputs in range order: the totals over every part row, or `None` when a task met a threshold
/// outside the fast range.
pub fn merge(outs: &Vec<Option<(i128, bool)>>, Ghost(tv): Ghost<Seq<ScanTask>>, Ghost(bnds): Ghost<Seq<int>>,
    li: &LiCols, pa: &PaCols, tb: u64, tc: u64,
    Ghost(lp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(b): Ghost<Seq<u8>>, Ghost(c): Ghost<Seq<u8>>)
    -> (r: Option<(i128, bool)>)
    requires
        li_cols_ok(*li, lp),
        pa_cols_ok(*pa, cp),
        targets_ok(lp, cp, b, c, tb, tc),
        tasks_ok(tv, bnds, *li, *pa, tb, tc, lp, cp, b, c),
        bnds[tv.len() as int] == pa.n,
        outs@.len() == tv.len(),
        forall|t: int| 0 <= t < tv.len() ==> (#[trigger] tv[t]).post(outs@[t]),
    ensures out_ok(lp, cp, b, c, 0, pa.n as int, r),
{
    let ghost zs = zrows(cp);
    let mut acc: i128 = 0;
    let mut any = false;
    let mut i: usize = 0;
    proof {
        assert(zs.subrange(0, 0) =~= Seq::<Row>::empty());
    }
    while i < outs.len()
        invariant
            li_cols_ok(*li, lp),
            pa_cols_ok(*pa, cp),
            targets_ok(lp, cp, b, c, tb, tc),
            tasks_ok(tv, bnds, *li, *pa, tb, tc, lp, cp, b, c),
            bnds[tv.len() as int] == pa.n,
            outs@.len() == tv.len(),
            forall|t: int| 0 <= t < tv.len() ==> (#[trigger] tv[t]).post(outs@[t]),
            zs == zrows(cp),
            i <= tv.len(),
            0 <= bnds[i as int] <= pa.n,
            acc == range_sum(lp, cp, b, c, 0, bnds[i as int]),
            any == (range_cnt(lp, cp, b, c, 0, bnds[i as int]) > 0),
        decreases outs.len() - i,
    {
        let ghost (m, e) = (bnds[i as int], bnds[i + 1]);
        proof {
            assert(tv[i as int].pre());
            assert(tv[i as int].post(outs@[i as int]));
        }
        let o = outs[i];
        let (s, a) = match o {
            Some(x) => x,
            None => return None,
        };
        proof {
            lemma_sum_of_split(zs, fsum(lp, b, c), 0, m, e);
            lemma_sum_of_split(zs, fcnt(lp, b, c), 0, m, e);
            lemma_sum_of_split(zs, fmass(lp, b, c), 0, m, e);
            lemma_range_bounds(lp, cp, b, c, 0, m);
            lemma_range_bounds(lp, cp, b, c, m, e);
            lemma_range_bounds(lp, cp, b, c, 0, e);
        }
        acc = acc + s;
        any = any || a;
        i = i + 1;
    }
    Some((acc, any))
}

} // verus!
