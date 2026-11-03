//! The kernel: a scan of the part rows; for a part row with an arm, a walk over its lineitem rows in key order.
//!
//! A part row's arm (`arm_at`) is decided on dictionary indices: `Arms` holds, per arm, the p_brand and p_container
//! dictionary indices of its literals (`arm_k_ok`: an index matches exactly when the entry is the literal) and its
//! size and quantity bounds. Most rows are rejected by the brand index alone. For a part row of key `k` with an arm,
//! the l_partkey key index (kinds 1 and 2: keys nondecreasing along positions) is searched for the first position
//! with key `>= k` (`lower_bound`: probes chosen by interpolation, alternating with bisection), and the positions
//! from there while the key is `k` are the part's lineitem rows (`part_fast`); each adds its value when the arm's
//! quantity window, ship mode and ship instruction hold (`row_add`, on the dictionary indices of `LiK`). Without a
//! key index (kind 0) every lineitem row is compared with the key (`part_slow`).
//!
//! Accumulators: the exact sum (scale 4), the absolute mass and whether a row qualified, over a range of part rows
//! (`acc_ok`: `terms::tot`). The mass is kept at most `i128::MAX`, which bounds every partial sum; a mass beyond it
//! returns `None`, and then the total mass over all part rows is beyond it too (`mass_over`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::link::expr::{ival, tval};
use crate::link::join::sum_of;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::{WorkerTask, MAX_WORKERS};
use crate::stores::facts::interface::common::keyidx::lemma_sorted_le;
use super::model::*;
use super::terms::*;
use super::decode::*;
use super::sums::*;

verus! {

/// Bound of the absolute mass: every partial sum then stays inside `i128`.
pub open spec fn mmax() -> int {
    i128::MAX as int
}

// ------------------------------------------------------------------------------------------------ dictionary indices

/// The dictionary indices of one arm's literals (an absent literal has an index no entry has) and its bounds.
#[derive(Clone, Copy)]
pub struct ArmK {
    /// p_brand index of the brand parameter.
    pub b: u64,
    /// p_container indices of the four containers.
    pub c0: u64,
    pub c1: u64,
    pub c2: u64,
    pub c3: u64,
    /// Size upper bound.
    pub smax: i64,
    /// Quantity window as coefficients of scale 2: `[100 * $q, 100 * ($q + 10)]`.
    pub qlo: i64,
    pub qhi: i64,
}

pub open spec fn arm_k_ok(k: ArmK, ps: Seq<Literal>, a: int, cp: Seq<PartView>) -> bool {
    &&& forall|e: int| 0 <= e < n_bd(cp) ==> ((e == k.b) == (#[trigger] bdict(cp, e) == brand_p(ps, a)))
    &&& forall|e: int| 0 <= e < n_cd(cp) ==>
            ((e == k.c0 || e == k.c1 || e == k.c2 || e == k.c3) == cont_in(a, #[trigger] cdict(cp, e)))
    &&& k.smax == smax(a)
    &&& k.qlo == 100 * qty_p(ps, a)
    &&& k.qhi == 100 * (qty_p(ps, a) + 10)
}

/// The three arms.
#[derive(Clone, Copy)]
pub struct Arms {
    pub a0: ArmK,
    pub a1: ArmK,
    pub a2: ArmK,
}

pub open spec fn arms_ok(r: Arms, ps: Seq<Literal>, cp: Seq<PartView>) -> bool {
    &&& arm_k_ok(r.a0, ps, 0, cp)
    &&& arm_k_ok(r.a1, ps, 1, cp)
    &&& arm_k_ok(r.a2, ps, 2, cp)
}

/// The l_shipinstruct index of `'DELIVER IN PERSON'` and the l_shipmode indices of `'AIR'`, `'AIR REG'`.
#[derive(Clone, Copy)]
pub struct LiK {
    pub it: u64,
    pub m1: u64,
    pub m2: u64,
}

pub open spec fn li_k_ok(k: LiK, fp: Seq<PartView>) -> bool {
    &&& n_sd(fp) < u64::MAX && n_md(fp) < u64::MAX
    &&& forall|e: int| 0 <= e < n_sd(fp) ==> ((e == k.it) == (#[trigger] sdict(fp, e) == dip()))
    &&& forall|e: int| 0 <= e < n_md(fp) ==> ((e == k.m1 || e == k.m2) == mode_in(#[trigger] mdict(fp, e)))
}

/// The arm of part values with dictionary indices `b`, `c` and size `sz`.
#[inline(always)]
pub fn arm_at(arms: &Arms, b: u64, sz: i64, c: u64, Ghost(ps): Ghost<Seq<Literal>>, Ghost(cp): Ghost<Seq<PartView>>) -> (a: u8)
    requires
        arms_ok(*arms, ps, cp),
        b < n_bd(cp),
        c < n_cd(cp),
    ensures
        a as int == arm_of(ps, bdict(cp, b as int), sz as int, cdict(cp, c as int)),
    no_unwind
{
    let ghost (bt, ct) = (bdict(cp, b as int), cdict(cp, c as int));
    let k0 = arms.a0;
    let k1 = arms.a1;
    let k2 = arms.a2;
    if b == k0.b && (c == k0.c0 || c == k0.c1 || c == k0.c2 || c == k0.c3) && 1 <= sz && sz <= k0.smax {
        0
    } else if b == k1.b && (c == k1.c0 || c == k1.c1 || c == k1.c2 || c == k1.c3) && 1 <= sz && sz <= k1.smax {
        1
    } else if b == k2.b && (c == k2.c0 || c == k2.c1 || c == k2.c2 || c == k2.c3) && 1 <= sz && sz <= k2.smax {
        2
    } else {
        3
    }
}

/// The quantity window of arm `a`.
#[inline(always)]
pub fn arm_window(arms: &Arms, a: u8) -> (r: (i64, i64))
    requires a < 3,
    ensures
        a == 0 ==> r == (arms.a0.qlo, arms.a0.qhi),
        a == 1 ==> r == (arms.a1.qlo, arms.a1.qhi),
        a == 2 ==> r == (arms.a2.qlo, arms.a2.qhi),
    no_unwind
{
    if a == 0 { (arms.a0.qlo, arms.a0.qhi) } else if a == 1 { (arms.a1.qlo, arms.a1.qhi) } else { (arms.a2.qlo, arms.a2.qhi) }
}

// ------------------------------------------------------------------------------------------------ lineitem rows

/// The stored row at key index position `p`.
#[inline(always)]
pub fn pos_row(li: &LiCols, p: usize, Ghost(fp): Ghost<Seq<PartView>>) -> (s: usize)
    requires li_cols_ok(*li, fp), p < li.n,
    ensures s as int == irow_at(fp, p as int), s < li.n,
    no_unwind
{
    proof {
        lemma_ikey(fp, p as int);
    }
    if li.kind == 2 {
        let g = li.dv.div(p as u64) as usize;
        (li.kb[g] + li.kc[p] as u64) as usize
    } else {
        p
    }
}

/// The l_partkey of stored row `s`.
#[inline(always)]
pub fn row_key(li: &LiCols, s: usize, Ghost(fp): Ghost<Seq<PartView>>) -> (k: i64)
    requires li_cols_ok(*li, fp), s < li.n,
    ensures k as int == lpk_at(fp, s as int),
    no_unwind
{
    proof {
        lemma_li_decode(fp, s as int);
    }
    let g = li.dv.div(s as u64) as usize;
    li.pkb[g] + li.pk[s] as i64
}

/// The l_quantity coefficient of stored row `s`.
#[inline(always)]
pub fn row_qty(li: &LiCols, s: usize, Ghost(fp): Ghost<Seq<PartView>>) -> (q: i64)
    requires li_cols_ok(*li, fp), s < li.n,
    ensures q as int == qty_at(fp, s as int),
    no_unwind
{
    proof {
        lemma_li_decode(fp, s as int);
    }
    let g = li.dv.div(s as u64) as usize;
    li.qb[g] + li.q[s] as i64
}

/// The key at key index position `p`.
#[inline(always)]
pub fn key_pos(li: &LiCols, p: usize, Ghost(fp): Ghost<Seq<PartView>>) -> (k: i64)
    requires li_cols_ok(*li, fp), p < li.n,
    ensures k as int == ikey_at(fp, p as int),
    no_unwind
{
    proof {
        lemma_ikey(fp, p as int);
    }
    let s = pos_row(li, p, Ghost(fp));
    row_key(li, s, Ghost(fp))
}

/// The lineitem side of arm `a` on stored row `s`.
pub open spec fn row_qual(fp: Seq<PartView>, ps: Seq<Literal>, a: int, s: int) -> bool {
    li_arm(ps, a, qty_at(fp, s), sdict(fp, sidx_at(fp, s)), mdict(fp, midx_at(fp, s)))
}

/// The value of stored row `s` (coefficient of scale 4).
pub open spec fn row_val(fp: Seq<PartView>, s: int) -> int {
    price_at(fp, s) * (100 - disc_at(fp, s))
}

/// Adds stored row `s` to the accumulators when the lineitem side of the arm (window `qlo .. qhi`) holds: the new
/// sum and mass, and whether it qualified; `None` when the mass would exceed `i128::MAX`.
#[inline(always)]
pub fn row_add(li: &LiCols, lk: &LiK, s: usize, qlo: i64, qhi: i64, sum: i128, mass: i128,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(a): Ghost<int>) -> (r: Option<(i128, i128, bool)>)
    requires
        li_cols_ok(*li, fp),
        li_k_ok(*lk, fp),
        s < li.n,
        0 <= a < 3,
        qlo == 100 * qty_p(ps, a),
        qhi == 100 * (qty_p(ps, a) + 10),
        0 <= mass <= mmax(),
        -mass <= sum <= mass,
    ensures
        r matches Some((s2, m2, hit)) ==> {
            let q = row_qual(fp, ps, a, s as int);
            &&& hit == q
            &&& s2 == sum + contrib(1, q, row_val(fp, s as int))
            &&& m2 == mass + contrib(2, q, row_val(fp, s as int))
            &&& 0 <= m2 <= mmax()
            &&& -m2 <= s2 <= m2
        },
        r is None ==> mass + contrib(2, row_qual(fp, ps, a, s as int), row_val(fp, s as int)) > mmax(),
    no_unwind
{
    proof {
        lemma_li_decode(fp, s as int);
        let _ = sdict(fp, sidx_at(fp, s as int));
        let _ = mdict(fp, midx_at(fp, s as int));
    }
    let g = li.dv.div(s as u64) as usize;
    let q = li.qb[g] + li.q[s] as i64;
    if qlo <= q && q <= qhi {
        let si = li.sib[g] + li.si[s] as u64;
        let sm = li.smb[g] + li.sm[s] as u64;
        if si == lk.it && (sm == lk.m1 || sm == lk.m2) {
            let pr = li.prb[g] + li.pr[s] as i64;
            let dc = li.db[g] + li.d[s] as i64;
            proof {
                let (x, y) = (pr as int, 100 - dc as int);
                assert(-p15() < x < p15() && -p15() + 100 < y < p15() + 100);
                assert(-0x10_0000_0000_0000_0000_0000_0000 < x * y < 0x10_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
                    requires -p15() < x < p15(), -p15() + 100 < y < p15() + 100;
            }
            let v: i128 = pr as i128 * (100 - dc as i128);
            let av: i128 = if v < 0 { -v } else { v };
            if av > i128::MAX - mass {
                return None;
            }
            return Some((sum + v, mass + av, true));
        }
    }
    Some((sum, mass, false))
}

// ------------------------------------------------------------------------------------------------ key search

/// The first key index position at or after `lo0` whose key is at least `k` (positions before `lo0` have smaller
/// keys). `klo` and `khi` are guesses of the keys around the answer; they only steer the probes.
pub fn lower_bound(li: &LiCols, k: i64, lo0: usize, klo: i64, khi: i64, Ghost(fp): Ghost<Seq<PartView>>) -> (r: usize)
    requires
        li_cols_ok(*li, fp),
        li.kind >= 1,
        lo0 <= li.n,
        forall|p: int| 0 <= p < lo0 ==> #[trigger] ikey_at(fp, p) < k,
    ensures
        lo0 <= r <= li.n,
        forall|p: int| 0 <= p < r ==> #[trigger] ikey_at(fp, p) < k,
        forall|p: int| r <= p < li.n ==> #[trigger] ikey_at(fp, p) >= k,
    no_unwind
{
    let ghost n = li.n as int;
    let mut lo = lo0;
    let mut hi = li.n;
    let mut kl: i64 = klo;
    let mut kh: i64 = khi;
    let mut step: u32 = 0;
    while lo < hi
        invariant
            li_cols_ok(*li, fp),
            li.kind >= 1,
            n == li.n,
            lo0 <= lo <= hi <= li.n,
            forall|p: int| 0 <= p < lo ==> #[trigger] ikey_at(fp, p) < k,
            forall|p: int| hi <= p < n ==> #[trigger] ikey_at(fp, p) >= k,
        decreases hi - lo,
    {
        let w = hi - lo;
        let mut mid = lo + w / 2;
        if step < 3 || step % 2 == 0 {
            // Interpolate between the keys known (or guessed) around [lo, hi).
            let dk: i128 = k as i128 - kl as i128;
            let span: i128 = kh as i128 - kl as i128;
            if 0 < dk && dk < span && (w as u64) < 0x100_0000_0000u64 && dk < 0x100_0000_0000i128 {
                proof {
                    assert((dk as int) * (w as int) < 0x1_0000_0000_0000_0000_0000) by (nonlinear_arith)
                        requires 0 < dk < 0x100_0000_0000int, 0 <= w < 0x100_0000_0000int;
                }
                let off: u128 = (dk as u128) * (w as u128) / (span as u128);
                proof {
                    assert((dk as int) * (w as int) < (span as int) * (w as int)) by (nonlinear_arith)
                        requires 0 < dk < span, w > 0;
                    assert(((dk as int) * (w as int)) / (span as int) < w as int) by (nonlinear_arith)
                        requires (dk as int) * (w as int) < (span as int) * (w as int), span > 0, dk > 0, w > 0;
                }
                mid = lo + off as usize;
            }
        }
        step = if step < 1000 { step + 1 } else { step };
        let s = pos_row(li, mid, Ghost(fp));
        let km = row_key(li, s, Ghost(fp));
        proof {
            lemma_ikey(fp, mid as int);
        }
        if km < k {
            proof {
                assert forall|p: int| 0 <= p < mid + 1 implies #[trigger] ikey_at(fp, p) < k by {
                    if p >= lo {
                        lemma_sorted_le(pk_c(fp), pk_b(fp), kx_c(fp), kx_b(fp), li_bs(fp), kx_kind(fp), n, p, mid as int);
                    }
                }
            }
            lo = mid + 1;
            kl = km;
        } else {
            proof {
                assert forall|p: int| mid <= p < n implies #[trigger] ikey_at(fp, p) >= k by {
                    lemma_sorted_le(pk_c(fp), pk_b(fp), kx_c(fp), kx_b(fp), li_bs(fp), kx_kind(fp), n, mid as int, p);
                }
            }
            hi = mid;
            kh = km;
        }
    }
    lo
}

// ------------------------------------------------------------------------------------------------ key ranges

/// A key directory (storage `li_partdir`: for key `kmin + e`, the key index positions `offs[e] .. offs[e + 1]`). Its
/// values are only guesses here: a range taken from it is used only after `range_check` confirms it on the key index.
#[derive(Clone, Copy)]
pub struct Dir {
    /// 1 when the directory is present.
    pub mode: i64,
    /// The key of entry 0.
    pub kmin: i64,
    pub offs: &'static [u32],
    /// Number of offsets.
    pub n: usize,
}

/// The offsets' count.
pub open spec fn dir_ok(d: Dir) -> bool {
    d.offs@.len() == d.n
}

/// The key index positions `lb .. ub` hold exactly the rows of key `k`.
pub open spec fn exact_range(fp: Seq<PartView>, k: i64, lb: int, ub: int) -> bool {
    &&& 0 <= lb <= ub <= n_li(fp)
    &&& forall|p: int| 0 <= p < lb ==> #[trigger] ikey_at(fp, p) < k
    &&& forall|p: int| lb <= p < ub ==> #[trigger] ikey_at(fp, p) == k
    &&& forall|p: int| ub <= p < n_li(fp) ==> #[trigger] ikey_at(fp, p) > k
}

/// Whether `lb .. ub` holds exactly the rows of key `k`: since keys are nondecreasing along the index, it is enough
/// that the key before `lb` is smaller, the key at `ub` larger, and the keys at both ends of the range are `k`. The
/// four keys are read independently (their memory latencies overlap).
#[inline(always)]
pub fn range_check(li: &LiCols, k: i64, lb: usize, ub: usize, Ghost(fp): Ghost<Seq<PartView>>) -> (r: bool)
    requires li_cols_ok(*li, fp), li.kind >= 1,
    ensures r ==> exact_range(fp, k, lb as int, ub as int),
    no_unwind
{
    if lb > ub || ub > li.n {
        return false;
    }
    let k_before = if lb > 0 { key_pos(li, lb - 1, Ghost(fp)) } else { i64::MIN };
    let k_after = if ub < li.n { key_pos(li, ub, Ghost(fp)) } else { i64::MAX };
    let k_first = if lb < ub { key_pos(li, lb, Ghost(fp)) } else { k };
    let k_last = if lb < ub { key_pos(li, ub - 1, Ghost(fp)) } else { k };
    let ok = (lb == 0 || k_before < k) && (ub == li.n || k_after > k) && k_first == k && k_last == k;
    proof {
        let n = li.n as int;
        if ok {
            assert forall|p: int| 0 <= p < lb implies #[trigger] ikey_at(fp, p) < k by {
                lemma_sorted_le(pk_c(fp), pk_b(fp), kx_c(fp), kx_b(fp), li_bs(fp), kx_kind(fp), n, p, lb - 1);
            }
            assert forall|p: int| lb <= p < ub implies #[trigger] ikey_at(fp, p) == k by {
                lemma_sorted_le(pk_c(fp), pk_b(fp), kx_c(fp), kx_b(fp), li_bs(fp), kx_kind(fp), n, lb as int, p);
                lemma_sorted_le(pk_c(fp), pk_b(fp), kx_c(fp), kx_b(fp), li_bs(fp), kx_kind(fp), n, p, ub - 1);
            }
            assert forall|p: int| ub <= p < n implies #[trigger] ikey_at(fp, p) > k by {
                lemma_sorted_le(pk_c(fp), pk_b(fp), kx_c(fp), kx_b(fp), li_bs(fp), kx_kind(fp), n, ub as int, p);
            }
        }
    }
    ok
}

/// The key index positions of key `k`: the directory's range when it checks, else two searches from `lo0` (every
/// position before `lo0` has a smaller key); `kl` and `khi` steer the searches.
pub fn find_range(li: &LiCols, dir: &Dir, k: i64, lo0: usize, kl: i64, khi: i64, Ghost(fp): Ghost<Seq<PartView>>)
    -> (r: (usize, usize))
    requires
        li_cols_ok(*li, fp),
        dir_ok(*dir),
        li.kind >= 1,
        lo0 <= li.n,
        forall|p: int| 0 <= p < lo0 ==> #[trigger] ikey_at(fp, p) < k,
    ensures exact_range(fp, k, r.0 as int, r.1 as int),
    no_unwind
{
    if dir.mode == 1 && k >= dir.kmin && dir.n >= 2 {
        let e: i128 = k as i128 - dir.kmin as i128;
        if e < (dir.n - 1) as i128 {
            let lb = dir.offs[e as usize] as usize;
            let ub = dir.offs[e as usize + 1] as usize;
            if range_check(li, k, lb, ub, Ghost(fp)) {
                return (lb, ub);
            }
        }
    }
    let lb = lower_bound(li, k, lo0, kl, khi, Ghost(fp));
    let ub = if k < i64::MAX { lower_bound(li, k + 1, lb, k, khi, Ghost(fp)) } else { li.n };
    proof {
        assert forall|p: int| lb <= p < ub implies #[trigger] ikey_at(fp, p) == k by {
            if k == i64::MAX {
                lemma_ikey(fp, p);
            }
        }
    }
    (lb, ub)
}

// ------------------------------------------------------------------------------------------------ one part row

/// The accumulators.
#[derive(Clone, Copy)]
pub struct Acc {
    /// Exact sum of the qualifying values (scale 4).
    pub sum: i128,
    /// Sum of their absolute values.
    pub mass: i128,
    /// Some row qualified.
    pub any: bool,
}

/// Mass within `i128::MAX` and the sum within the mass.
pub open spec fn acc_small(acc: Acc) -> bool {
    0 <= acc.mass <= mmax() && -acc.mass <= acc.sum <= acc.mass
}

/// The accumulators of the part rows `j0 .. j1`.
pub open spec fn acc_ok(acc: Acc, fp: Seq<PartView>, cp: Seq<PartView>, ps: Seq<Literal>, j0: int, j1: int) -> bool {
    &&& acc.sum == tot(fp, cp, ps, 1, j0, j1)
    &&& acc.mass == tot(fp, cp, ps, 2, j0, j1)
    &&& acc.any == (tot(fp, cp, ps, 0, j0, j1) > 0)
}

/// What a part row of key `k` with arm `a` adds, in key index order from `lb`.
pub open spec fn part_pre(fp: Seq<PartView>, ps: Seq<Literal>, z: Row, a: int, k: i64, qlo: i64, qhi: i64) -> bool {
    &&& z.len() == 4
    &&& ival(z[0]) == k
    &&& zarm(ps, z) == a
    &&& 0 <= a < 3
    &&& qlo == 100 * qty_p(ps, a)
    &&& qhi == 100 * (qty_p(ps, a) + 10)
}

/// The accumulators after adding part row `z`.
pub open spec fn part_post(fp: Seq<PartView>, ps: Seq<Literal>, z: Row, acc: Acc, acc2: Acc) -> bool {
    &&& acc2.sum == acc.sum + pin(fp, ps, 1)(z)
    &&& acc2.mass == acc.mass + pin(fp, ps, 2)(z)
    &&& acc2.any == (acc.any || pin(fp, ps, 0)(z) > 0)
    &&& acc_small(acc2)
}

/// Position `p`'s terms when its key is the part's: the row's contribution under the arm.
pub proof fn lemma_pos_in(fp: Seq<PartView>, ps: Seq<Literal>, z: Row, a: int, k: i64, p: int)
    requires li_shape(fp), 0 <= p < n_li(fp), z.len() == 4, ival(z[0]) == k, zarm(ps, z) == a, 0 <= a < 3,
        ikey_at(fp, p) == k,
    ensures ({
        let s = irow_at(fp, p);
        &&& jt(ps, 0, z)(irows(fp)[p]) == contrib(0, row_qual(fp, ps, a, s), row_val(fp, s))
        &&& jt(ps, 1, z)(irows(fp)[p]) == contrib(1, row_qual(fp, ps, a, s), row_val(fp, s))
        &&& jt(ps, 2, z)(irows(fp)[p]) == contrib(2, row_qual(fp, ps, a, s), row_val(fp, s))
    }),
{
    lemma_pos_term(fp, ps, 0, z, p);
    lemma_pos_term(fp, ps, 1, z, p);
    lemma_pos_term(fp, ps, 2, z, p);
}

/// Position `p`'s terms when its key is not the part's: zero.
pub proof fn lemma_pos_out(fp: Seq<PartView>, ps: Seq<Literal>, z: Row, k: i64, p: int)
    requires li_shape(fp), 0 <= p < n_li(fp), z.len() == 4, ival(z[0]) == k, ikey_at(fp, p) != k,
    ensures
        jt(ps, 0, z)(irows(fp)[p]) == 0,
        jt(ps, 1, z)(irows(fp)[p]) == 0,
        jt(ps, 2, z)(irows(fp)[p]) == 0,
{
    lemma_pos_term(fp, ps, 0, z, p);
    lemma_pos_term(fp, ps, 1, z, p);
    lemma_pos_term(fp, ps, 2, z, p);
}

/// One more position of the walk: the three range sums step by the position's terms.
pub proof fn lemma_kin_step(fp: Seq<PartView>, ps: Seq<Literal>, z: Row, lb: int, p: int)
    requires 0 <= lb <= p < n_li(fp),
    ensures
        kin(fp, ps, 0, z, lb, p + 1) == kin(fp, ps, 0, z, lb, p) + jt(ps, 0, z)(irows(fp)[p]),
        kin(fp, ps, 1, z, lb, p + 1) == kin(fp, ps, 1, z, lb, p) + jt(ps, 1, z)(irows(fp)[p]),
        kin(fp, ps, 2, z, lb, p + 1) == kin(fp, ps, 2, z, lb, p) + jt(ps, 2, z)(irows(fp)[p]),
{
    lemma_sum_step(irows(fp), jt(ps, 0, z), lb, p);
    lemma_sum_step(irows(fp), jt(ps, 1, z), lb, p);
    lemma_sum_step(irows(fp), jt(ps, 2, z), lb, p);
}

/// Positions `a .. b` whose keys all differ from the part's add nothing.
pub proof fn lemma_kin_zero(fp: Seq<PartView>, ps: Seq<Literal>, z: Row, k: i64, a: int, b: int)
    requires
        li_shape(fp), 0 <= a <= b <= n_li(fp), z.len() == 4, ival(z[0]) == k,
        forall|p: int| a <= p < b ==> #[trigger] ikey_at(fp, p) != k,
    ensures
        kin(fp, ps, 0, z, a, b) == 0,
        kin(fp, ps, 1, z, a, b) == 0,
        kin(fp, ps, 2, z, a, b) == 0,
{
    let rows = irows(fp);
    assert forall|p: int| a <= p < b implies jt(ps, 0, z)(#[trigger] rows[p]) == 0 && jt(ps, 1, z)(rows[p]) == 0
        && jt(ps, 2, z)(rows[p]) == 0 by {
        lemma_pos_out(fp, ps, z, k, p);
    }
    lemma_sum_zero_range(rows, jt(ps, 0, z), a, b);
    lemma_sum_zero_range(rows, jt(ps, 1, z), a, b);
    lemma_sum_zero_range(rows, jt(ps, 2, z), a, b);
}

/// The walk covered the positions `lb .. e` holding every row of the part's key: the part's totals.
pub proof fn lemma_walk_total(fp: Seq<PartView>, ps: Seq<Literal>, z: Row, k: i64, lb: int, e: int)
    requires
        li_shape(fp), 0 <= lb <= e <= n_li(fp), z.len() == 4, ival(z[0]) == k,
        forall|p: int| 0 <= p < lb ==> #[trigger] ikey_at(fp, p) != k,
        forall|p: int| e <= p < n_li(fp) ==> #[trigger] ikey_at(fp, p) != k,
    ensures
        pin(fp, ps, 0)(z) == kin(fp, ps, 0, z, lb, e),
        pin(fp, ps, 1)(z) == kin(fp, ps, 1, z, lb, e),
        pin(fp, ps, 2)(z) == kin(fp, ps, 2, z, lb, e),
{
    let n = n_li(fp);
    let rows = irows(fp);
    lemma_kin_zero(fp, ps, z, k, 0, lb);
    lemma_kin_zero(fp, ps, z, k, e, n);
    lemma_sum_split(rows, jt(ps, 0, z), 0, lb, n);
    lemma_sum_split(rows, jt(ps, 0, z), lb, e, n);
    lemma_sum_split(rows, jt(ps, 1, z), 0, lb, n);
    lemma_sum_split(rows, jt(ps, 1, z), lb, e, n);
    lemma_sum_split(rows, jt(ps, 2, z), 0, lb, n);
    lemma_sum_split(rows, jt(ps, 2, z), lb, e, n);
    lemma_pin_kin(fp, ps, 0, z);
    lemma_pin_kin(fp, ps, 1, z);
    lemma_pin_kin(fp, ps, 2, z);
}

/// Accumulator `kk` over the positions `sel` (in order), for part row `z`.
pub open spec fn psel(fp: Seq<PartView>, ps: Seq<Literal>, kk: int, z: Row, sel: Seq<int>) -> int
    decreases sel.len(),
{
    if sel.len() == 0 { 0 } else { psel(fp, ps, kk, z, sel.drop_last()) + jt(ps, kk, z)(irows(fp)[sel.last()]) }
}

/// One more selected position.
proof fn lemma_psel_push(fp: Seq<PartView>, ps: Seq<Literal>, z: Row, sel: Seq<int>, p: int)
    ensures
        psel(fp, ps, 0, z, sel.push(p)) == psel(fp, ps, 0, z, sel) + jt(ps, 0, z)(irows(fp)[p]),
        psel(fp, ps, 1, z, sel.push(p)) == psel(fp, ps, 1, z, sel) + jt(ps, 1, z)(irows(fp)[p]),
        psel(fp, ps, 2, z, sel.push(p)) == psel(fp, ps, 2, z, sel) + jt(ps, 2, z)(irows(fp)[p]),
{
    assert(sel.push(p).drop_last() =~= sel);
}

/// A prefix of the selected positions, one longer.
proof fn lemma_psel_take(fp: Seq<PartView>, ps: Seq<Literal>, z: Row, sel: Seq<int>, t: int)
    requires 0 <= t < sel.len(),
    ensures
        psel(fp, ps, 0, z, sel.take(t + 1)) == psel(fp, ps, 0, z, sel.take(t)) + jt(ps, 0, z)(irows(fp)[sel[t]]),
        psel(fp, ps, 1, z, sel.take(t + 1)) == psel(fp, ps, 1, z, sel.take(t)) + jt(ps, 1, z)(irows(fp)[sel[t]]),
        psel(fp, ps, 2, z, sel.take(t + 1)) == psel(fp, ps, 2, z, sel.take(t)) + jt(ps, 2, z)(irows(fp)[sel[t]]),
{
    assert(sel.take(t + 1).drop_last() =~= sel.take(t));
}

/// Mass over a prefix of the selected positions is at most the mass over all of them, and the count and sum
/// keep the bounds of the terms.
proof fn lemma_psel_bounds(fp: Seq<PartView>, ps: Seq<Literal>, z: Row, sel: Seq<int>, t: int)
    requires 0 <= t <= sel.len(),
    ensures
        0 <= psel(fp, ps, 2, z, sel.take(t)) <= psel(fp, ps, 2, z, sel),
        -psel(fp, ps, 2, z, sel) <= psel(fp, ps, 1, z, sel) <= psel(fp, ps, 2, z, sel),
        psel(fp, ps, 0, z, sel) >= 0,
        psel(fp, ps, 0, z, sel) == 0 ==> psel(fp, ps, 2, z, sel) == 0,
    decreases sel.len(),
{
    if sel.len() > 0 {
        let d = sel.drop_last();
        if t == sel.len() {
            assert(sel.take(t) =~= sel);
            lemma_psel_bounds(fp, ps, z, d, d.len() as int);
            assert(d.take(d.len() as int) =~= d);
        } else {
            lemma_psel_bounds(fp, ps, z, d, t);
            assert(d.take(t) =~= sel.take(t));
        }
        lemma_term_bounds(ps, irows(fp)[sel.last()] + z);
    } else {
        assert(sel.take(t) =~= sel);
    }
}

/// Key index kinds 1 and 2: the walk over the positions `lb .. ub`, which hold exactly the rows of the part's key,
/// in chunks of 64 positions. Per chunk, a branch-free first pass gathers the stored rows whose quantity lies in the
/// arm's window (independent loads, so their memory latencies overlap); the second pass checks the rest of the arm
/// on those rows only and adds their values. Returns the accumulators with the part row added.
pub fn part_fast(li: &LiCols, lk: &LiK, qlo: i64, qhi: i64, lb: usize, ub: usize, acc: Acc,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(z): Ghost<Row>, Ghost(a): Ghost<int>,
    Ghost(k): Ghost<i64>) -> (r: Option<Acc>)
    requires
        li_cols_ok(*li, fp),
        li_k_ok(*lk, fp),
        lb <= ub <= li.n,
        forall|p: int| 0 <= p < lb ==> #[trigger] ikey_at(fp, p) != k,
        forall|p: int| lb <= p < ub ==> #[trigger] ikey_at(fp, p) == k,
        forall|p: int| ub <= p < li.n ==> #[trigger] ikey_at(fp, p) != k,
        part_pre(fp, ps, z, a, k, qlo, qhi),
        acc_small(acc),
    ensures
        r matches Some(acc2) ==> part_post(fp, ps, z, acc, acc2),
        r is None ==> acc.mass + pin(fp, ps, 2)(z) > mmax(),
    no_unwind
{
    let ghost n = li.n as int;
    let mut buf: [usize; 64] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let mut p = lb;
    let mut sum = acc.sum;
    let mut mass = acc.mass;
    let mut any = acc.any;
    proof {
        lemma_sum_empty(irows(fp), jt(ps, 0, z), lb as int);
        lemma_sum_empty(irows(fp), jt(ps, 1, z), lb as int);
        lemma_sum_empty(irows(fp), jt(ps, 2, z), lb as int);
        lemma_walk_total(fp, ps, z, k, lb as int, ub as int);
    }
    while p < ub
        invariant
            li_cols_ok(*li, fp),
            li_k_ok(*lk, fp),
            n == li.n,
            lb <= p <= ub <= n,
            buf@.len() == 64,
            forall|q: int| lb <= q < ub ==> #[trigger] ikey_at(fp, q) == k,
            part_pre(fp, ps, z, a, k, qlo, qhi),
            acc_small(acc),
            pin(fp, ps, 2)(z) == kin(fp, ps, 2, z, lb as int, ub as int),
            sum == acc.sum + kin(fp, ps, 1, z, lb as int, p as int),
            mass == acc.mass + kin(fp, ps, 2, z, lb as int, p as int),
            any == (acc.any || kin(fp, ps, 0, z, lb as int, p as int) > 0),
            0 <= mass <= mmax(),
            -mass <= sum <= mass,
        decreases ub - p,
    {
        let c_end = if ub - p > 64 { p + 64 } else { ub };
        // Pass 1: the stored rows of the chunk whose quantity is in the window.
        let mut cnt: usize = 0;
        let mut i = p;
        let ghost mut sel: Seq<int> = Seq::empty();
        proof {
            lemma_sum_empty(irows(fp), jt(ps, 0, z), p as int);
            lemma_sum_empty(irows(fp), jt(ps, 1, z), p as int);
            lemma_sum_empty(irows(fp), jt(ps, 2, z), p as int);
        }
        while i < c_end
            invariant
                li_cols_ok(*li, fp),
                n == li.n,
                lb <= p <= i <= c_end <= ub <= n,
                c_end <= p + 64,
                buf@.len() == 64,
                forall|q: int| lb <= q < ub ==> #[trigger] ikey_at(fp, q) == k,
                part_pre(fp, ps, z, a, k, qlo, qhi),
                cnt == sel.len(),
                cnt <= i - p,
                cnt <= 64,
                forall|t: int| 0 <= t < cnt ==> p <= #[trigger] sel[t] < i && buf@[t] as int == irow_at(fp, sel[t]),
                kin(fp, ps, 0, z, p as int, i as int) == psel(fp, ps, 0, z, sel),
                kin(fp, ps, 1, z, p as int, i as int) == psel(fp, ps, 1, z, sel),
                kin(fp, ps, 2, z, p as int, i as int) == psel(fp, ps, 2, z, sel),
            decreases c_end - i,
        {
            let s = pos_row(li, i, Ghost(fp));
            let q = row_qty(li, s, Ghost(fp));
            buf[cnt] = s;
            let pass = qlo <= q && q <= qhi;
            proof {
                lemma_ikey(fp, i as int);
                lemma_pos_in(fp, ps, z, a, k, i as int);
                lemma_kin_step(fp, ps, z, p as int, i as int);
                if pass {
                    lemma_psel_push(fp, ps, z, sel, i as int);
                    sel = sel.push(i as int);
                }
            }
            cnt = cnt + if pass { 1usize } else { 0usize };
            i = i + 1;
        }
        // Pass 2: the rest of the arm on the gathered rows.
        let mut t: usize = 0;
        let ghost sum0 = sum;
        let ghost mass0 = mass;
        let ghost any0 = any;
        proof {
            assert(sel.take(0) =~= Seq::<int>::empty());
            lemma_psel_bounds(fp, ps, z, sel, 0);
        }
        while t < cnt
            invariant
                li_cols_ok(*li, fp),
                li_k_ok(*lk, fp),
                n == li.n,
                lb <= p < c_end <= ub <= n,
                buf@.len() == 64,
                forall|q: int| lb <= q < ub ==> #[trigger] ikey_at(fp, q) == k,
                part_pre(fp, ps, z, a, k, qlo, qhi),
                cnt == sel.len(),
                cnt <= 64,
                t <= cnt,
                pin(fp, ps, 2)(z) == kin(fp, ps, 2, z, lb as int, ub as int),
                kin(fp, ps, 0, z, p as int, c_end as int) == psel(fp, ps, 0, z, sel),
                kin(fp, ps, 1, z, p as int, c_end as int) == psel(fp, ps, 1, z, sel),
                kin(fp, ps, 2, z, p as int, c_end as int) == psel(fp, ps, 2, z, sel),
                sum0 == acc.sum + kin(fp, ps, 1, z, lb as int, p as int),
                mass0 == acc.mass + kin(fp, ps, 2, z, lb as int, p as int),
                any0 == (acc.any || kin(fp, ps, 0, z, lb as int, p as int) > 0),
                acc_small(acc),
                forall|u: int| 0 <= u < cnt ==> p <= #[trigger] sel[u] < c_end && buf@[u] as int == irow_at(fp, sel[u]),
                sum == sum0 + psel(fp, ps, 1, z, sel.take(t as int)),
                mass == mass0 + psel(fp, ps, 2, z, sel.take(t as int)),
                any == (any0 || psel(fp, ps, 0, z, sel.take(t as int)) > 0),
                psel(fp, ps, 0, z, sel.take(t as int)) >= 0,
                0 <= mass <= mmax(),
                -mass <= sum <= mass,
            decreases cnt - t,
        {
            let s = buf[t];
            proof {
                let x = sel[t as int];
                lemma_ikey(fp, x);
                lemma_pos_in(fp, ps, z, a, k, x);
                lemma_psel_take(fp, ps, z, sel, t as int);
                lemma_term_bounds(ps, irows(fp)[x] + z);
            }
            match row_add(li, lk, s, qlo, qhi, sum, mass, Ghost(fp), Ghost(ps), Ghost(a)) {
                None => {
                    proof {
                        lemma_psel_bounds(fp, ps, z, sel, t + 1);
                        lemma_kin_mass_le(fp, ps, z, lb as int, lb as int, p as int, ub as int);
                        lemma_kin_mass_le(fp, ps, z, lb as int, p as int, c_end as int, ub as int);
                        lemma_sum_split(irows(fp), jt(ps, 2, z), lb as int, p as int, c_end as int);
                        lemma_sum_split(irows(fp), jt(ps, 2, z), lb as int, c_end as int, ub as int);
                        lemma_kin_mass_le(fp, ps, z, lb as int, c_end as int, ub as int, ub as int);
                    }
                    return None;
                },
                Some((s2, m2, hit)) => {
                    sum = s2;
                    mass = m2;
                    any = any || hit;
                },
            }
            t = t + 1;
        }
        proof {
            assert(sel.take(cnt as int) =~= sel);
            lemma_sum_split(irows(fp), jt(ps, 0, z), lb as int, p as int, c_end as int);
            lemma_sum_split(irows(fp), jt(ps, 1, z), lb as int, p as int, c_end as int);
            lemma_sum_split(irows(fp), jt(ps, 2, z), lb as int, p as int, c_end as int);
            lemma_kin_bounds(fp, ps, z, lb as int, p as int);
        }
        p = c_end;
    }
    Some(Acc { sum, mass, any })
}

/// Key index kind 0: every lineitem row compared with the key.
pub fn part_slow(li: &LiCols, lk: &LiK, k: i64, qlo: i64, qhi: i64, acc: Acc,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(z): Ghost<Row>, Ghost(a): Ghost<int>)
    -> (r: Option<Acc>)
    requires
        li_cols_ok(*li, fp),
        li_k_ok(*lk, fp),
        part_pre(fp, ps, z, a, k, qlo, qhi),
        acc_small(acc),
    ensures
        r matches Some(acc2) ==> part_post(fp, ps, z, acc, acc2),
        r is None ==> acc.mass + pin(fp, ps, 2)(z) > mmax(),
    no_unwind
{
    let ghost n = li.n as int;
    let mut p: usize = 0;
    let mut sum = acc.sum;
    let mut mass = acc.mass;
    let mut any = acc.any;
    proof {
        lemma_sum_empty(irows(fp), jt(ps, 0, z), 0);
        lemma_sum_empty(irows(fp), jt(ps, 1, z), 0);
        lemma_sum_empty(irows(fp), jt(ps, 2, z), 0);
    }
    while p < li.n
        invariant
            li_cols_ok(*li, fp),
            li_k_ok(*lk, fp),
            n == li.n,
            p <= n,
            part_pre(fp, ps, z, a, k, qlo, qhi),
            acc_small(acc),
            sum == acc.sum + kin(fp, ps, 1, z, 0, p as int),
            mass == acc.mass + kin(fp, ps, 2, z, 0, p as int),
            any == (acc.any || kin(fp, ps, 0, z, 0, p as int) > 0),
            0 <= mass <= mmax(),
            -mass <= sum <= mass,
        decreases n - p,
    {
        let s = pos_row(li, p, Ghost(fp));
        let key = row_key(li, s, Ghost(fp));
        proof {
            lemma_ikey(fp, p as int);
            lemma_kin_step(fp, ps, z, 0, p as int);
            lemma_kin_bounds(fp, ps, z, 0, p as int);
        }
        if key == k {
            proof {
                lemma_pos_in(fp, ps, z, a, k, p as int);
            }
            match row_add(li, lk, s, qlo, qhi, sum, mass, Ghost(fp), Ghost(ps), Ghost(a)) {
                None => {
                    proof {
                        lemma_kin_mass_le(fp, ps, z, 0, 0, p + 1, n);
                        lemma_pin_kin(fp, ps, 2, z);
                    }
                    return None;
                },
                Some((s2, m2, hit)) => {
                    sum = s2;
                    mass = m2;
                    any = any || hit;
                },
            }
        } else {
            proof {
                lemma_pos_out(fp, ps, z, k, p as int);
            }
        }
        p = p + 1;
    }
    proof {
        lemma_pin_kin(fp, ps, 0, z);
        lemma_pin_kin(fp, ps, 1, z);
        lemma_pin_kin(fp, ps, 2, z);
    }
    Some(Acc { sum, mass, any })
}

/// Adds part row `z` (arm `a`, key `k`, quantity window `qlo .. qhi`) to the accumulators. With a key index, its
/// lineitem rows are the key's range (`find_range`, searching from `prev_end` when the keys increase: every position
/// before `prev_end` has a key at most `prev_k`); also returns the new `(prev_k, prev_end)`.
pub fn add_part(li: &LiCols, lk: &LiK, dir: &Dir, qlo: i64, qhi: i64, k: i64, acc: Acc, prev_k: i64, prev_end: usize,
    kmin: i64, khi: i64,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(z): Ghost<Row>, Ghost(a): Ghost<int>)
    -> (r: Option<(Acc, i64, usize)>)
    requires
        li_cols_ok(*li, fp),
        dir_ok(*dir),
        li_k_ok(*lk, fp),
        part_pre(fp, ps, z, a, k, qlo, qhi),
        acc_small(acc),
        prev_end <= li.n,
        forall|p: int| 0 <= p < prev_end ==> #[trigger] ikey_at(fp, p) <= prev_k,
    ensures
        r matches Some((acc2, pk, pe)) ==> part_post(fp, ps, z, acc, acc2) && pe <= li.n
            && forall|p: int| 0 <= p < pe ==> #[trigger] ikey_at(fp, p) <= pk,
        r is None ==> acc.mass + pin(fp, ps, 2)(z) > mmax(),
    no_unwind
{
    if li.kind >= 1 {
        let lo0 = if prev_k < k { prev_end } else { 0 };
        let kl = if prev_k < k && prev_end > 0 { prev_k } else if kmin > i64::MIN { kmin - 1 } else { kmin };
        let (lb, ub) = find_range(li, dir, k, lo0, kl, khi, Ghost(fp));
        proof {
            assert forall|p: int| 0 <= p < lb implies #[trigger] ikey_at(fp, p) != k by {}
            assert forall|p: int| ub <= p < li.n implies #[trigger] ikey_at(fp, p) != k by {}
        }
        match part_fast(li, lk, qlo, qhi, lb, ub, acc, Ghost(fp), Ghost(ps), Ghost(z), Ghost(a), Ghost(k)) {
            None => None,
            Some(acc2) => {
                proof {
                    assert forall|p: int| 0 <= p < ub implies #[trigger] ikey_at(fp, p) <= k by {}
                }
                Some((acc2, k, ub))
            },
        }
    } else {
        match part_slow(li, lk, k, qlo, qhi, acc, Ghost(fp), Ghost(ps), Ghost(z), Ghost(a)) {
            None => None,
            Some(acc2) => Some((acc2, prev_k, prev_end)),
        }
    }
}

/// The code of dictionary index `b` in a group whose base is `base`, or 256 when no U8 code reaches it.
#[inline(always)]
pub fn code_of(b: u64, base: u64) -> (t: u16)
    ensures
        t <= 256,
        t < 256 ==> base + t == b,
        t == 256 ==> (b < base || b - base >= 256),
    no_unwind
{
    if b >= base && b - base < 256 { (b - base) as u16 } else { 256 }
}

// ------------------------------------------------------------------------------------------------ the part scan

/// The inputs of a scan over part rows.
pub open spec fn scan_pre(li: LiCols, pa: PaCols, lk: LiK, arms: Arms, fp: Seq<PartView>, cp: Seq<PartView>,
    ps: Seq<Literal>) -> bool {
    &&& li_cols_ok(li, fp)
    &&& pa_cols_ok(pa, cp)
    &&& li_k_ok(lk, fp)
    &&& arms_ok(arms, ps, cp)
    &&& n_bd(cp) < u64::MAX
    &&& n_cd(cp) < u64::MAX
}

/// A scan's output over part rows `j0 .. j1`: the accumulators, or `None` when the mass exceeds `i128::MAX`.
pub open spec fn out_ok(fp: Seq<PartView>, cp: Seq<PartView>, ps: Seq<Literal>, j0: int, j1: int, out: Option<Acc>) -> bool {
    &&& out matches Some(acc) ==> acc_ok(acc, fp, cp, ps, j0, j1) && acc_small(acc)
    &&& out is None ==> tot(fp, cp, ps, 2, j0, j1) > mmax()
}

/// Part row `j`'s values and arm.
proof fn lemma_part_row(cp: Seq<PartView>, ps: Seq<Literal>, j: int)
    requires pa_shape(cp), 0 <= j < n_pa(cp),
    ensures
        pa_rows(cp)[j].len() == 4,
        ival(pa_rows(cp)[j][0]) == pkey_at(cp, j),
        zarm(ps, pa_rows(cp)[j]) == arm_of(ps, bdict(cp, bidx_at(cp, j)), size_at(cp, j), cdict(cp, cidx_at(cp, j))),
{
}

/// The scan of the part rows `j_lo .. j_hi`, block by block. In a block, a row whose p_brand code is none of the
/// arms' brand codes has no arm (most rows); another row's arm is decided on its dictionary indices and size.
pub fn scan_range(li: &LiCols, pa: &PaCols, lk: &LiK, arms: &Arms, dir: &Dir, kmin: i64, kmax: i64, j_lo: usize,
    j_hi: usize, Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (out: Option<Acc>)
    requires
        scan_pre(*li, *pa, *lk, *arms, fp, cp, ps),
        dir_ok(*dir),
        j_lo <= j_hi <= pa.n,
    ensures out_ok(fp, cp, ps, j_lo as int, j_hi as int, out),
    no_unwind
{
    let ghost zs = pa_rows(cp);
    let ghost nl = li.n as int;
    let br = pa.br;
    let mut acc = Acc { sum: 0, mass: 0, any: false };
    let mut j = j_lo;
    // Every key index position before `prev_end` has a key at most `prev_k` (kinds 1 and 2).
    let mut prev_k: i64 = i64::MIN;
    let mut prev_end: usize = 0;
    let khi: i64 = if kmax < i64::MAX { kmax + 1 } else { kmax };
    proof {
        lemma_sum_empty(zs, pin(fp, ps, 0), j_lo as int);
        lemma_sum_empty(zs, pin(fp, ps, 1), j_lo as int);
        lemma_sum_empty(zs, pin(fp, ps, 2), j_lo as int);
    }
    while j < j_hi
        invariant
            scan_pre(*li, *pa, *lk, *arms, fp, cp, ps),
            dir_ok(*dir),
            zs == pa_rows(cp),
            nl == li.n,
            br == pa.br,
            j_lo <= j <= j_hi <= pa.n,
            acc_ok(acc, fp, cp, ps, j_lo as int, j as int),
            acc_small(acc),
            prev_end <= li.n,
            forall|p: int| 0 <= p < prev_end ==> #[trigger] ikey_at(fp, p) <= prev_k,
        decreases j_hi - j,
    {
        let g = (j as u64 / pa.bs) as usize;
        proof {
            lemma_pa_decode(cp, j as int);
            cpc_lemma_block_end(j as int, pa.bs as int, n_pa(cp));
        }
        let g_end0 = (g as u64 + 1) * pa.bs;
        let g_end: usize = if g_end0 < j_hi as u64 { g_end0 as usize } else { j_hi };
        let pkb = pa.pkb[g];
        let brb = pa.brb[g];
        let szb = pa.szb[g];
        let ctb = pa.ctb[g];
        let t0 = code_of(arms.a0.b, brb);
        let t1 = code_of(arms.a1.b, brb);
        let t2 = code_of(arms.a2.b, brb);
        while j < g_end
            invariant
                scan_pre(*li, *pa, *lk, *arms, fp, cp, ps),
                dir_ok(*dir),
                zs == pa_rows(cp),
                nl == li.n,
                br == pa.br,
                j_lo <= j <= g_end <= j_hi <= pa.n,
                (g as int) * (pa.bs as int) <= j,
                g_end <= (g as int + 1) * (pa.bs as int),
                g < pa.pkb@.len() && g < pa.brb@.len() && g < pa.szb@.len() && g < pa.ctb@.len(),
                pkb == pa.pkb@[g as int] && brb == pa.brb@[g as int] && szb == pa.szb@[g as int] && ctb == pa.ctb@[g as int],
                t0 <= 256 && (t0 < 256 ==> brb + t0 == arms.a0.b) && (t0 == 256 ==> (arms.a0.b < brb || arms.a0.b - brb >= 256)),
                t1 <= 256 && (t1 < 256 ==> brb + t1 == arms.a1.b) && (t1 == 256 ==> (arms.a1.b < brb || arms.a1.b - brb >= 256)),
                t2 <= 256 && (t2 < 256 ==> brb + t2 == arms.a2.b) && (t2 == 256 ==> (arms.a2.b < brb || arms.a2.b - brb >= 256)),
                acc_ok(acc, fp, cp, ps, j_lo as int, j as int),
                acc_small(acc),
                prev_end <= li.n,
                forall|p: int| 0 <= p < prev_end ==> #[trigger] ikey_at(fp, p) <= prev_k,
            decreases g_end - j,
        {
            proof {
                lemma_block(j as int, g as int, pa.bs as int);
                lemma_pa_decode(cp, j as int);
                lemma_part_row(cp, ps, j as int);
                lemma_sum_step(zs, pin(fp, ps, 0), j_lo as int, j as int);
                lemma_sum_step(zs, pin(fp, ps, 1), j_lo as int, j as int);
                lemma_sum_step(zs, pin(fp, ps, 2), j_lo as int, j as int);
                lemma_pin_bounds(fp, ps, zs[j as int]);
                lemma_tot_bounds(fp, cp, ps, j_lo as int, j as int);
                lemma_tot_bounds(fp, cp, ps, j_lo as int, j + 1);
            }
            let ghost z = zs[j as int];
            let c = br[j] as u16;
            if c == t0 || c == t1 || c == t2 {
                let bi = brb + c as u64;
                let ci = ctb + pa.ct[j] as u64;
                let sz = szb + pa.sz[j] as i64;
                let a = arm_at(arms, bi, sz, ci, Ghost(ps), Ghost(cp));
                if a < 3 {
                    let k = pkb + pa.pk[j] as i64;
                    let (qlo, qhi) = arm_window(arms, a);
                    match add_part(li, lk, dir, qlo, qhi, k, acc, prev_k, prev_end, kmin, khi,
                        Ghost(fp), Ghost(ps), Ghost(z), Ghost(a as int)) {
                        None => {
                            proof {
                                lemma_tot_mass_le(fp, cp, ps, j_lo as int, j_lo as int, j + 1, j_hi as int);
                            }
                            return None;
                        },
                        Some((acc2, pk2, pe2)) => {
                            acc = acc2;
                            prev_k = pk2;
                            prev_end = pe2;
                        },
                    }
                } else {
                    proof {
                        lemma_pin_none(fp, ps, 0, z);
                        lemma_pin_none(fp, ps, 1, z);
                        lemma_pin_none(fp, ps, 2, z);
                    }
                }
            } else {
                proof {
                    let bt = bdict(cp, bidx_at(cp, j as int));
                    assert(bidx_at(cp, j as int) != arms.a0.b && bidx_at(cp, j as int) != arms.a1.b
                        && bidx_at(cp, j as int) != arms.a2.b);
                    assert(bt != brand_p(ps, 0) && bt != brand_p(ps, 1) && bt != brand_p(ps, 2));
                    lemma_pin_none(fp, ps, 0, z);
                    lemma_pin_none(fp, ps, 1, z);
                    lemma_pin_none(fp, ps, 2, z);
                }
            }
            j = j + 1;
        }
    }
    Some(acc)
}

/// The end of row `j`'s block fits `u64` and lies past `j`.
pub proof fn cpc_lemma_block_end(j: int, bs: int, n: int)
    requires bs >= 1, 0 <= j < n, n + bs <= u64::MAX,
    ensures
        (j / bs) * bs <= j < (j / bs + 1) * bs,
        (j / bs + 1) * bs <= n + bs,
        0 <= j / bs <= j,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, bs);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, bs);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, bs);
    let g = j / bs;
    assert(bs * g == g * bs) by (nonlinear_arith);
    assert((g + 1) * bs == g * bs + bs) by (nonlinear_arith);
    assert(g <= j) by (nonlinear_arith) requires g * bs <= j, bs >= 1, g >= 0;
}

// ------------------------------------------------------------------------------------------------ the worker task

/// One worker's share: the part rows `j_lo .. j_hi`.
pub struct ScanTask {
    pub li: LiCols,
    pub pa: PaCols,
    pub lk: LiK,
    pub arms: Arms,
    pub dir: Dir,
    pub kmin: i64,
    pub kmax: i64,
    pub j_lo: usize,
    pub j_hi: usize,
    pub fp: Ghost<Seq<PartView>>,
    pub cp: Ghost<Seq<PartView>>,
    pub ps: Ghost<Seq<Literal>>,
}

impl WorkerTask for ScanTask {
    type Output = Option<Acc>;

    open spec fn pre(&self) -> bool {
        &&& scan_pre(self.li, self.pa, self.lk, self.arms, self.fp@, self.cp@, self.ps@)
        &&& dir_ok(self.dir)
        &&& self.j_lo <= self.j_hi <= self.pa.n
    }

    open spec fn post(&self, out: Option<Acc>) -> bool {
        out_ok(self.fp@, self.cp@, self.ps@, self.j_lo as int, self.j_hi as int, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.j_lo as u64, self.j_hi as u64)
    }

    fn run(self) -> (out: Option<Acc>) {
        scan_range(&self.li, &self.pa, &self.lk, &self.arms, &self.dir, self.kmin, self.kmax, self.j_lo, self.j_hi, self.fp, self.cp, self.ps)
    }
}

// ------------------------------------------------------------------------------------------------ tasks and merge

/// The tasks `t` of a partition `bnds` of the part rows (task `t` covers `bnds[t] .. bnds[t + 1]`).
pub open spec fn tasks_ok(tasks: Seq<ScanTask>, bnds: Seq<int>, fp: Seq<PartView>, cp: Seq<PartView>, ps: Seq<Literal>) -> bool {
    &&& bnds.len() == tasks.len() + 1
    &&& bnds[0] == 0
    &&& forall|t: int| 0 <= t < tasks.len() ==> {
        &&& (#[trigger] tasks[t]).j_lo == bnds[t]
        &&& tasks[t].j_hi == bnds[t + 1]
        &&& tasks[t].fp@ == fp && tasks[t].cp@ == cp && tasks[t].ps@ == ps
        &&& tasks[t].pre()
    }
}

/// `ntasks` contiguous ranges of about equal size covering every part row.
pub fn make_tasks(li: &LiCols, pa: &PaCols, lk: &LiK, arms: &Arms, dir: &Dir, kmin: i64, kmax: i64, ntasks: usize,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: (Vec<ScanTask>, Ghost<Seq<int>>))
    requires
        scan_pre(*li, *pa, *lk, *arms, fp, cp, ps),
        dir_ok(*dir),
        1 <= ntasks <= MAX_WORKERS,
    ensures
        r.0@.len() == ntasks,
        tasks_ok(r.0@, r.1@, fp, cp, ps),
        r.1@[ntasks as int] == pa.n,
{
    let mut tasks: Vec<ScanTask> = Vec::new();
    let ghost mut bnds: Seq<int> = seq![0int];
    let mut a: usize = 0;
    let mut t: usize = 0;
    while t < ntasks
        invariant
            scan_pre(*li, *pa, *lk, *arms, fp, cp, ps),
            dir_ok(*dir),
            1 <= ntasks <= MAX_WORKERS,
            t <= ntasks,
            a <= pa.n,
            t == ntasks ==> a == pa.n,
            tasks@.len() == t,
            bnds[t as int] == a,
            tasks_ok(tasks@, bnds, fp, cp, ps),
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
        let task = ScanTask { li: *li, pa: *pa, lk: *lk, arms: *arms, dir: *dir, kmin, kmax, j_lo: a, j_hi: e,
            fp: Ghost(fp), cp: Ghost(cp), ps: Ghost(ps) };
        let ghost old_tasks = tasks@;
        tasks.push(task);
        proof {
            bnds = bnds.push(e as int);
            assert forall|k: int| 0 <= k < tasks@.len() implies {
                &&& (#[trigger] tasks@[k]).j_lo == bnds[k]
                &&& tasks@[k].j_hi == bnds[k + 1]
                &&& tasks@[k].fp@ == fp && tasks@[k].cp@ == cp && tasks@[k].ps@ == ps
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

/// Adds the task outputs in range order: the accumulators over every part row, or `None` when the mass exceeds
/// `i128::MAX`.
pub fn merge(outs: &Vec<Option<Acc>>, Ghost(tv): Ghost<Seq<ScanTask>>, Ghost(bnds): Ghost<Seq<int>>, n: usize,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Option<Acc>)
    requires
        tasks_ok(tv, bnds, fp, cp, ps),
        bnds[tv.len() as int] == n,
        n == n_pa(cp),
        outs@.len() == tv.len(),
        forall|t: int| 0 <= t < tv.len() ==> (#[trigger] tv[t]).post(outs@[t]),
    ensures out_ok(fp, cp, ps, 0, n as int, r),
{
    let ghost zs = pa_rows(cp);
    let mut acc = Acc { sum: 0, mass: 0, any: false };
    let mut i: usize = 0;
    proof {
        if tv.len() > 0 {
            assert(tv[0].pre());
        }
        lemma_sum_empty(zs, pin(fp, ps, 0), 0);
        lemma_sum_empty(zs, pin(fp, ps, 1), 0);
        lemma_sum_empty(zs, pin(fp, ps, 2), 0);
    }
    while i < outs.len()
        invariant
            tasks_ok(tv, bnds, fp, cp, ps),
            bnds[tv.len() as int] == n,
            n == n_pa(cp),
            outs@.len() == tv.len(),
            forall|t: int| 0 <= t < tv.len() ==> (#[trigger] tv[t]).post(outs@[t]),
            zs == pa_rows(cp),
            i <= tv.len(),
            0 <= bnds[i as int] <= n,
            acc_ok(acc, fp, cp, ps, 0, bnds[i as int]),
            acc_small(acc),
        decreases outs.len() - i,
    {
        let ghost (m, e) = (bnds[i as int], bnds[i + 1]);
        proof {
            assert(tv[i as int].pre());
            assert(tv[i as int].post(outs@[i as int]));
            assert(pa_cols_ok(tv[i as int].pa, cp));
            lemma_tot_mass_le(fp, cp, ps, 0, m, e, n as int);
            lemma_tot_mass_le(fp, cp, ps, 0, 0, m, n as int);
            lemma_sum_split(zs, pin(fp, ps, 0), 0, m, e);
            lemma_sum_split(zs, pin(fp, ps, 1), 0, m, e);
            lemma_sum_split(zs, pin(fp, ps, 2), 0, m, e);
            lemma_tot_mass_le(fp, cp, ps, 0, 0, e, n as int);
            lemma_tot_bounds(fp, cp, ps, 0, m);
            lemma_tot_bounds(fp, cp, ps, m, e);
        }
        let o = outs[i];
        let x = match o {
            Some(x) => x,
            None => return None,
        };
        if x.mass > i128::MAX - acc.mass {
            return None;
        }
        acc = Acc { sum: acc.sum + x.sum, mass: acc.mass + x.mass, any: acc.any || x.any };
        i = i + 1;
    }
    proof {
        if tv.len() == 0 {
            assert(bnds[0] == 0);
        }
    }
    Some(acc)
}

} // verus!
