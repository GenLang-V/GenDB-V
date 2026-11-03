//! The lineitem side of one matching part row: the rows of its key through the directory of li_pkqty's
//! (l_partkey, l_quantity) index, their AVG threshold and the SUM of l_extendedprice of the rows below it
//! (`part_sum`), all `no_unwind` so worker tasks run it.
//!
//! The rows of key `k` are the index positions `lo .. hi` of directory entry `k - kmin` (none outside the
//! directory's key range). One pass sums their quantity keys (`qbase + qk[p]`, read contiguously: no lineitem row
//! is touched; `S`, count `c = hi - lo`), the exact PostgreSQL
//! quotient `q` at scale `r` of `S / c` gives `0.2 * AVG = 2 q` at scale `r + 1`, and a row is kept exactly when
//! `quantity * 10^(r - 1) < 2 q` (`lemma_lt_threshold`). Spec values are over the index-ordered value rows
//! `bind::irows`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::fns::div::*;
use crate::link::join::*;
use crate::link::expr::ival;
use crate::gendb_entry::layout::PartView;
use crate::stores::li_pkqty::interface as LI;
use crate::stores::custpart::interface::common::read::lemma_div_lt;
use crate::bridge::fns::div::lemma_div_scale_range;
use super::vals::*;
use super::bind::*;
use super::common::numdiv::{num_div_nu, pow10_nu};

verus! {

/// The lineitem extents the lookups read (whole parts).
#[derive(Clone, Copy)]
pub struct LiCols {
    /// Number of stored rows.
    pub n: usize,
    /// Index rows: the stored row at each index position.
    pub rows: &'static [u32],
    /// Index quantity keys: `qbase + qk[p]` is the l_quantity coefficient of `rows[p]`.
    pub qk: &'static [u16],
    pub qbase: i64,
    /// l_extendedprice codes and bases (blocks of 65536 rows).
    pub xc: &'static [u32],
    pub xb: &'static [i64],
    /// First key of the directory.
    pub kmin: i64,
    /// Number of directory entries.
    pub nk: usize,
    pub offs: &'static [u32],
}

/// Rows per block of the frame-of-reference columns the lookups decode with a shift.
pub open spec fn fast_bs() -> int {
    65536
}

/// The extents are the parts, in index mode, with blocks of 65536 rows.
pub open spec fn li_cols_ok(c: LiCols, lp: Seq<PartView>) -> bool {
    &&& li_facts(lp)
    &&& LI::has_idx(lp)
    &&& c.n == n_li(lp)
    &&& LI::bsize(lp) == fast_bs()
    &&& c.rows@ == LI::idx_rows(lp)
    &&& c.qk@ == LI::idx_qkeys(lp)
    &&& c.qbase == LI::idx_qbase(lp)
    &&& c.xc@ == LI::u32s(lp[LI::LI_EXTENDEDPRICE_CODES as int])
    &&& c.xb@ == LI::i64s(lp[LI::LI_EXTENDEDPRICE_BASE as int])
    &&& c.kmin == LI::idx_kmin(lp)
    &&& c.offs@ == LI::idx_offs(lp)
    &&& c.nk == LI::idx_nkeys(lp)
}

/// The block of row `s` (blocks of 65536 rows) is `s >> 16`.
pub proof fn lemma_shift16(s: u64)
    ensures (s >> 16u64) as int == s as int / 65536,
{
    assert(s >> 16u64 == s / 65536) by (bit_vector);
}

/// The stored row at index position `p`.
pub fn irow_at(c: &LiCols, p: usize, Ghost(lp): Ghost<Seq<PartView>>) -> (s: usize)
    requires li_cols_ok(*c, lp), p < c.n,
    ensures s as int == LI::irow(lp, p as int), s < c.n,
    no_unwind
{
    proof {
        assert(0 <= LI::irow(lp, p as int) < c.n);
    }
    c.rows[p] as usize
}

/// l_quantity coefficient of the stored row at index position `p` (its quantity key).
pub fn qty_at_pos(c: &LiCols, p: usize, Ghost(lp): Ghost<Seq<PartView>>) -> (q: i64)
    requires li_cols_ok(*c, lp), p < c.n,
    ensures q as int == LI::qty_at(lp, LI::irow(lp, p as int)), -p15() < q < p15(),
    no_unwind
{
    proof {
        assert(LI::qkey_ok(lp, p as int));
        assert(0 <= LI::irow(lp, p as int) < c.n);
        assert(y_ok(srow(lp, LI::irow(lp, p as int))));
    }
    c.qbase + c.qk[p] as i64
}

/// l_extendedprice coefficient of stored row `s`.
pub fn price_of(c: &LiCols, s: usize, Ghost(lp): Ghost<Seq<PartView>>) -> (x: i64)
    requires li_cols_ok(*c, lp), s < c.n,
    ensures x as int == LI::price_at(lp, s as int), -p15() < x < p15(),
    no_unwind
{
    proof {
        lemma_shift16(s as u64);
        lemma_div_lt(s as int, 65536, c.xb@.len() as int);
        assert(y_ok(srow(lp, s as int)));
    }
    c.xb[(s as u64 >> 16u64) as usize] + c.xc[s] as i64
}

/// `q < 0.2 * AVG` with `0.2 * AVG = 2 avg` at scale `r + 1` (`r >= 2`): `q * 10^(r - 1) < 2 avg`.
pub proof fn lemma_lt_threshold(qv: int, a: int, r: nat)
    requires r >= 2,
    ensures
        lt_true(Val::Num { coeff: qv, scale: 2 }, Val::Num { coeff: 2 * a, scale: r + 1 })
            == (qv * pow10((r - 1) as nat) < 2 * a),
{
    let s = max_nat(2, r + 1);
    assert(s == r + 1);
    assert(((r + 1) - 2) as nat == (r - 1) as nat);
    assert(pow10(0) == 1);
    assert(align(2 * a, r + 1, s) == 2 * a);
    assert(num_cmp(qv, 2, 2 * a, r + 1) == sign(qv * pow10((r - 1) as nat) - 2 * a));
}

/// The value rows of index positions `lo .. hi` have key `k`; the others do not.
pub open spec fn window_ok(lp: Seq<PartView>, k: int, lo: int, hi: int) -> bool {
    &&& 0 <= lo <= hi <= n_li(lp)
    &&& forall|p: int| 0 <= p < n_li(lp) ==> (lo <= p < hi <==> #[trigger] is_key(irows(lp)[p], k))
}

/// No index position has key `k`, or the directory entry of `k`: a window of the rows of key `k`.
proof fn lemma_window(lp: Seq<PartView>, k: int, e: int)
    requires
        li_facts(lp),
        LI::has_idx(lp),
        0 <= e < LI::idx_nkeys(lp),
        k == LI::idx_kmin(lp) + e,
    ensures window_ok(lp, k, LI::idx_offs(lp)[e] as int, LI::idx_offs(lp)[e + 1] as int),
{
    let n = n_li(lp);
    assert forall|p: int| 0 <= p < n implies (LI::idx_offs(lp)[e] <= p < LI::idx_offs(lp)[e + 1] <==> #[trigger] is_key(irows(lp)[p], k)) by {
        LI::lemma_entry_exact(lp, n, e, p);
        assert(irows(lp)[p] == srow(lp, LI::irow(lp, p)));
    }
    if n > 0 {
        LI::lemma_entry_exact(lp, n, e, 0);
    } else {
        LI::lemma_offs_mono(lp, n, e, e + 1);
        LI::lemma_offs_mono(lp, n, e + 1, LI::idx_nkeys(lp));
    }
}

/// A key outside the directory's range: an empty window.
proof fn lemma_window_none(lp: Seq<PartView>, k: int)
    requires
        li_facts(lp),
        LI::has_idx(lp),
        !(LI::idx_kmin(lp) <= k < LI::idx_kmin(lp) + LI::idx_nkeys(lp)),
    ensures window_ok(lp, k, 0, 0),
{
    let n = n_li(lp);
    assert forall|p: int| 0 <= p < n implies !#[trigger] is_key(irows(lp)[p], k) by {
        LI::lemma_outside_none(lp, n, k, p);
        assert(irows(lp)[p] == srow(lp, LI::irow(lp, p)));
    }
}

/// Over a window of key `k`, a term that vanishes on rows of other keys sums to its sum over the window.
proof fn lemma_window_sum(lp: Seq<PartView>, k: int, lo: int, hi: int, f: spec_fn(Row) -> int)
    requires
        window_ok(lp, k, lo, hi),
        forall|y: Row| !is_key(y, k) ==> #[trigger] f(y) == 0,
    ensures sum_of(irows(lp), f) == sum_of(irows(lp).subrange(lo, hi), f),
{
    let ys = irows(lp);
    assert forall|i: int| 0 <= i < ys.len() && !(lo <= i < hi) implies #[trigger] f(ys[i]) == 0 by {
        assert(!is_key(ys[i], k));
    }
    lemma_sum_of_window(ys, f, lo, hi);
}

/// The value row at index position `p` (stored row `s = irow(p)`).
proof fn lemma_irow_val(lp: Seq<PartView>, p: int, s: int)
    requires li_facts(lp), 0 <= p < n_li(lp), s == LI::irow(lp, p),
    ensures
        irows(lp)[p] == srow(lp, s),
        irows(lp)[p] == yrow(LI::key_at(lp, s), LI::qty_at(lp, s), LI::price_at(lp, s)),
{
}

/// The index-ordered value rows are typed.
pub proof fn lemma_irows_ok(lp: Seq<PartView>)
    requires li_facts(lp), LI::has_idx(lp),
    ensures ys_ok(irows(lp)),
{
    let ys = irows(lp);
    let n = n_li(lp);
    assert forall|i: int| 0 <= i < ys.len() implies y_ok(#[trigger] ys[i]) by {
        assert(ys[i] == srow(lp, LI::irow(lp, i)));
        assert(0 <= LI::irow(lp, i) < n);
    }
}

/// Sum and number of the quantities of key `k` over the window `[lo, hi)`.
fn window_qsum(c: &LiCols, lo: usize, hi: usize, Ghost(lp): Ghost<Seq<PartView>>, Ghost(k): Ghost<int>) -> (r: i128)
    requires
        li_cols_ok(*c, lp),
        window_ok(lp, k, lo as int, hi as int),
    ensures
        r == qsum(irows(lp), k),
        hi - lo == qcnt(irows(lp), k),
    no_unwind
{
    let ghost ys = irows(lp);
    let mut sq: i128 = 0;
    let mut p = lo;
    while p < hi
        invariant
            li_cols_ok(*c, lp),
            window_ok(lp, k, lo as int, hi as int),
            ys == irows(lp),
            lo <= p <= hi,
            sq == sum_of(ys.subrange(lo as int, p as int), tq(k)),
            -(p - lo) * p15() <= sq <= (p - lo) * p15(),
            hi <= 0xffff_ffff_ffff_ffff,
        decreases hi - p,
    {
        let q = qty_at_pos(c, p, Ghost(lp));
        proof {
            lemma_irow_val(lp, p as int, LI::irow(lp, p as int));
            assert(is_key(ys[p as int], k));
            assert(tq(k)(ys[p as int]) == q);
            lemma_sum_of_sub_push(ys, tq(k), lo as int, p as int);
            assert(-(p + 1 - lo) * p15() == -(p - lo) * p15() - p15()) by (nonlinear_arith);
            assert((p + 1 - lo) * p15() == (p - lo) * p15() + p15()) by (nonlinear_arith);
            assert((p - lo) * p15() <= 0xffff_ffff_ffff_ffff * p15()) by (nonlinear_arith)
                requires p - lo <= 0xffff_ffff_ffff_ffff;
        }
        sq = sq + q as i128;
        p = p + 1;
    }
    proof {
        lemma_window_sum(lp, k, lo as int, hi as int, tq(k));
        lemma_window_sum(lp, k, lo as int, hi as int, t1(k));
        let w = ys.subrange(lo as int, hi as int);
        assert forall|i: int| 0 <= i < w.len() implies #[trigger] t1(k)(w[i]) == 1 by {
            assert(w[i] == ys[lo + i]);
        }
        lemma_sum_of_const(w, t1(k), 1);
    }
    sq
}

/// The SUM of l_extendedprice and whether a row is kept, for the part value row `z` of key `k` (brand `b`,
/// container `cc`): `None` only when the AVG threshold leaves the fast integer range.
pub fn part_sum(c: &LiCols, k: i64, Ghost(lp): Ghost<Seq<PartView>>, Ghost(b): Ghost<Seq<u8>>,
    Ghost(cc): Ghost<Seq<u8>>, Ghost(z): Ghost<Row>) -> (r: Option<(i128, bool)>)
    requires
        li_cols_ok(*c, lp),
        z == seq![Val::Int(k as int), Val::Text(b), Val::Text(cc)],
    ensures
        r matches Some((s, any)) ==> s == psum(irows(lp), b, cc, z) && any == (pcnt(irows(lp), b, cc, z) > 0),
    no_unwind
{
    let ghost ys = irows(lp);
    let ghost ki = k as int;
    proof {
        lemma_irows_ok(lp);
        lemma_part_sums(ys, b, cc, z);
    }
    let kk: i128 = k as i128 - c.kmin as i128;
    if kk < 0 || kk >= c.nk as i128 {
        proof {
            lemma_window_none(lp, ki);
            lemma_window_sum(lp, ki, 0, 0, tsum(ys, b, cc, z));
            lemma_window_sum(lp, ki, 0, 0, tcnt(ys, b, cc, z));
        }
        return Some((0, false));
    }
    let e = kk as usize;
    proof {
        lemma_window(lp, ki, e as int);
    }
    let lo = c.offs[e] as usize;
    let hi = c.offs[e + 1] as usize;
    let sq = window_qsum(c, lo, hi, Ghost(lp), Ghost(ki));
    let cnt = hi - lo;
    proof {
        lemma_window_sum(lp, ki, lo as int, hi as int, tsum(ys, b, cc, z));
        lemma_window_sum(lp, ki, lo as int, hi as int, tcnt(ys, b, cc, z));
    }
    if cnt == 0 {
        proof {
            assert(ys.subrange(lo as int, hi as int) =~= Seq::<Row>::empty());
        }
        return Some((0, false));
    }
    proof {
        lemma_irows_ok(lp);
        lemma_qsum_bound(ys, ki);
    }
    let (q, r) = match num_div_nu(sq, 2, cnt as i128, 0) {
        Some(x) => x,
        None => return None,
    };
    if r > 21 || q > 0x0100_0000_0000_0000_0000_0000_0000_0000i128 || q < -0x0100_0000_0000_0000_0000_0000_0000_0000i128 {
        return None;
    }
    proof {
        lemma_div_scale_range(sq as int, 2, cnt as int, 0);
        assert(sub_val(ys, ki) == (Val::Num { coeff: 2 * q, scale: (r + 1) as nat }));
    }
    let pw: i128 = pow10_nu(r - 1) as i128;
    let x2: i128 = 2 * q;
    proof {
        lemma_pow10_monotone((r - 1) as nat, 20);
        assert(pow10(20) == 100_000_000_000_000_000_000) by (compute);
    }
    let mut acc: i128 = 0;
    let mut any = false;
    let mut p = lo;
    while p < hi
        invariant
            li_cols_ok(*c, lp),
            window_ok(lp, ki, lo as int, hi as int),
            ys == irows(lp),
            z == seq![Val::Int(ki), Val::Text(b), Val::Text(cc)],
            sub_val(ys, ki) == (Val::Num { coeff: 2 * q, scale: (r + 1) as nat }),
            2 <= r <= 21,
            pw as int == pow10((r - 1) as nat),
            1 <= pw <= 100_000_000_000_000_000_000,
            x2 == 2 * q,
            lo <= p <= hi,
            hi <= 0xffff_ffff_ffff_ffff,
            acc == sum_of(ys.subrange(lo as int, p as int), tsum(ys, b, cc, z)),
            any == (sum_of(ys.subrange(lo as int, p as int), tcnt(ys, b, cc, z)) > 0),
            sum_of(ys.subrange(lo as int, p as int), tcnt(ys, b, cc, z)) >= 0,
            -(p - lo) * p15() <= acc <= (p - lo) * p15(),
        decreases hi - p,
    {
        let qv = qty_at_pos(c, p, Ghost(lp));
        proof {
            lemma_irow_val(lp, p as int, LI::irow(lp, p as int));
            assert(is_key(ys[p as int], ki));
            lemma_lt_threshold(qv as int, q as int, r as nat);
            assert(qv * pw <= 1_000_000_000_000_000 * 100_000_000_000_000_000_000) by (nonlinear_arith)
                requires -1_000_000_000_000_000 < qv < 1_000_000_000_000_000, 1 <= pw <= 100_000_000_000_000_000_000;
            assert(qv * pw >= -1_000_000_000_000_000 * 100_000_000_000_000_000_000) by (nonlinear_arith)
                requires -1_000_000_000_000_000 < qv < 1_000_000_000_000_000, 1 <= pw <= 100_000_000_000_000_000_000;
            lemma_sum_of_sub_push(ys, tsum(ys, b, cc, z), lo as int, p as int);
            lemma_sum_of_sub_push(ys, tcnt(ys, b, cc, z), lo as int, p as int);
            assert(-(p + 1 - lo) * p15() == -(p - lo) * p15() - p15()) by (nonlinear_arith);
            assert((p + 1 - lo) * p15() == (p - lo) * p15() + p15()) by (nonlinear_arith);
            assert((p - lo) * p15() <= 0xffff_ffff_ffff_ffff * p15()) by (nonlinear_arith)
                requires p - lo <= 0xffff_ffff_ffff_ffff;
        }
        if (qv as i128) * pw < x2 {
            let s = irow_at(c, p, Ghost(lp));
            let xv = price_of(c, s, Ghost(lp));
            acc = acc + xv as i128;
            any = true;
        }
        p = p + 1;
    }
    Some((acc, any))
}

} // verus!
