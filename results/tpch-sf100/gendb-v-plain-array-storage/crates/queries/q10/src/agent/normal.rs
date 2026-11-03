//! The statement's quantities over the stored columns (`agent::cols`).
//!
//! Parameters: `$1` is `pd_of(ps)` days since 2000-01-01; the window's upper bound `$1::timestamp + 3 months` is
//! `hi_res(pd)` (microseconds, or the SQL error of leaving the timestamp range). On stored days (since 1970-01-01)
//! the window is `[dlo, dhi)` (`win_of`): `dlo = pd + 10957` and `dhi` the first day whose midnight is not below
//! the upper bound.
//!
//! Per row: orders row `j` is in the window (`win`); lineitem row `i` hits order key `k` (`lhit`) when its key is
//! `k` and its return flag is `R`; its value is `l_extendedprice * (100 - l_discount)` (coefficient at scale 4,
//! `lval`). `ksum(k, lo, hi)` sums the values of the rows `lo..hi` that hit key `k` (`kcnt` counts them, `kabs` sums
//! the absolute values). Customer row `a` collects the orders `j` with its key and in the window (`cmatch`):
//! `csum(a, lo, hi)` sums `ksum(o_orderkey[j], 0, n_l)` over the orders `lo..hi` it collects (`ccnt`, `cabs`
//! likewise). The group of customer `a` exists when its nation exists (`natok`) and `ccnt(a) > 0`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::datetime::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::text_at;
use crate::agent::cols::*;

verus! {

// ------------------------------------------------------------------------------------------------ parameters

/// `$1`: days since 2000-01-01.
pub open spec fn pd_of(ps: Seq<Literal>) -> int {
    match ps[0] { Literal::Date { y, m, d } => date_from_civil(y, m, d), _ => 0 }
}

/// Microseconds per day.
pub open spec fn usecs() -> int { 86_400_000_000 }

/// `$1::timestamp + interval '3 month'` for the parameter day `pd`.
pub open spec fn hi_res(pd: int) -> Result<int, SqlError> {
    match date_to_ts(pd) {
        Ok(t) => ts_add_interval(t, 3, 0, 0),
        Err(e) => Err(e),
    }
}

/// The window on stored days `[dlo, dhi)` for the parameter day `pd` and upper bound `t1`.
pub open spec fn win_of(dlo: int, dhi: int, pd: int, t1: int) -> bool {
    &&& dlo == pd + 10957
    &&& (dhi - 10957) * usecs() >= t1
    &&& (dhi - 10957 - 1) * usecs() < t1
}

/// `d * usecs < t1` exactly when `d < dhi - 10957`.
pub proof fn lemma_win_hi(dlo: int, dhi: int, pd: int, t1: int, d: int)
    requires win_of(dlo, dhi, pd, t1),
    ensures (d * usecs() < t1) == (d < dhi - 10957),
{
    let h = dhi - 10957;
    let u = usecs();
    if d < h {
        assert(d * u <= (h - 1) * u) by (nonlinear_arith) requires d <= h - 1, u > 0;
    } else {
        assert(d * u >= h * u) by (nonlinear_arith) requires d >= h, u > 0;
    }
}

// ------------------------------------------------------------------------------------------------ rows

/// Orders row `j` lies in the window `[dlo, dhi)` (stored days).
pub open spec fn win(sv: StoresView, dlo: int, dhi: int, j: int) -> bool {
    dlo <= od(sv)[j] as int && (od(sv)[j] as int) < dhi
}

/// The return flag of lineitem row `i` is `R`.
pub open spec fn is_r(sv: StoresView, i: int) -> bool { rf(sv, i) == seq![82u8] }

/// `l_extendedprice * (1 - l_discount)` of lineitem row `i` (coefficient at scale 4).
pub open spec fn lval(sv: StoresView, i: int) -> int { lp(sv)[i] * (100 - ld(sv)[i]) }

/// Lineitem row `i` has order key `k` and return flag `R`.
pub open spec fn lhit(sv: StoresView, k: int, i: int) -> bool { lk(sv)[i] as int == k && is_r(sv, i) }

/// Sum of `lval` over the lineitem rows `lo..hi` that hit key `k`.
pub open spec fn ksum(sv: StoresView, k: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { ksum(sv, k, lo, hi - 1) + if lhit(sv, k, hi - 1) { lval(sv, hi - 1) } else { 0 } }
}

/// Number of lineitem rows `lo..hi` that hit key `k`.
pub open spec fn kcnt(sv: StoresView, k: int, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo { 0 } else { kcnt(sv, k, lo, hi - 1) + if lhit(sv, k, hi - 1) { 1nat } else { 0nat } }
}

/// Sum of `|lval|` over the lineitem rows `lo..hi` that hit key `k`.
pub open spec fn kabs(sv: StoresView, k: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { kabs(sv, k, lo, hi - 1) + if lhit(sv, k, hi - 1) { abs(lval(sv, hi - 1)) } else { 0 } }
}

/// Orders row `j` belongs to customer row `a` and lies in the window.
pub open spec fn cmatch(sv: StoresView, dlo: int, dhi: int, a: int, j: int) -> bool {
    oc(sv)[j] == ck(sv)[a] && win(sv, dlo, dhi, j)
}

/// Sum of the order sums of the orders `lo..hi` that customer `a` collects.
pub open spec fn csum(sv: StoresView, dlo: int, dhi: int, a: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else {
        csum(sv, dlo, dhi, a, lo, hi - 1)
            + if cmatch(sv, dlo, dhi, a, hi - 1) { ksum(sv, ok(sv)[hi - 1] as int, 0, n_l(sv)) } else { 0 }
    }
}

/// Number of hitting lineitem rows of the orders `lo..hi` that customer `a` collects.
pub open spec fn ccnt(sv: StoresView, dlo: int, dhi: int, a: int, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo { 0 } else {
        ccnt(sv, dlo, dhi, a, lo, hi - 1)
            + if cmatch(sv, dlo, dhi, a, hi - 1) { kcnt(sv, ok(sv)[hi - 1] as int, 0, n_l(sv)) } else { 0nat }
    }
}

/// Absolute mass of the orders `lo..hi` that customer `a` collects.
pub open spec fn cabs(sv: StoresView, dlo: int, dhi: int, a: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else {
        cabs(sv, dlo, dhi, a, lo, hi - 1)
            + if cmatch(sv, dlo, dhi, a, hi - 1) { kabs(sv, ok(sv)[hi - 1] as int, 0, n_l(sv)) } else { 0 }
    }
}

/// The totals of customer `a` over all orders.
pub open spec fn ctot(sv: StoresView, dlo: int, dhi: int, a: int) -> int { csum(sv, dlo, dhi, a, 0, n_o(sv)) }
pub open spec fn ctcnt(sv: StoresView, dlo: int, dhi: int, a: int) -> nat { ccnt(sv, dlo, dhi, a, 0, n_o(sv)) }
pub open spec fn ctabs(sv: StoresView, dlo: int, dhi: int, a: int) -> int { cabs(sv, dlo, dhi, a, 0, n_o(sv)) }

// ------------------------------------------------------------------------------------------------ nations, groups

/// Customer row `a` has a nation row (`c_nationkey = n_nationkey`).
pub open spec fn natok(sv: StoresView, a: int) -> bool {
    exists|n: int| 0 <= n < n_n(sv) && #[trigger] nk(sv)[n] == cnk(sv)[a]
}

/// The nation row of customer row `a` (unique by the primary key; meaningful under `natok`).
pub open spec fn nat_row(sv: StoresView, a: int) -> int {
    choose|n: int| 0 <= n < n_n(sv) && #[trigger] nk(sv)[n] == cnk(sv)[a]
}

/// Customer row `a` is a group of the statement: its nation exists and some lineitem row reaches it.
pub open spec fn is_group(sv: StoresView, dlo: int, dhi: int, a: int) -> bool {
    0 <= a < n_c(sv) && natok(sv, a) && ctcnt(sv, dlo, dhi, a) > 0
}

/// The group key of customer row `a`: `c_custkey, c_name, c_acctbal, c_phone, n_name, c_address, c_comment`.
pub open spec fn ckey(sv: StoresView, a: int) -> Row {
    seq![
        Val::Int(ck(sv)[a] as int),
        Val::Text(text_at(cname_col(sv), a)),
        Val::Num { coeff: cacct(sv)[a] as int, scale: 2 },
        Val::Text(text_at(cphone_col(sv), a)),
        Val::Text(text_at(nname_col(sv), nat_row(sv, a))),
        Val::Text(text_at(caddr_col(sv), a)),
        Val::Text(text_at(ccomm_col(sv), a)),
    ]
}

/// The output row of customer row `a` with revenue `s` (scale 4): `c_custkey, c_name, revenue, c_acctbal, n_name,
/// c_address, c_phone, c_comment`.
pub open spec fn cust_row(sv: StoresView, a: int, s: int) -> Row {
    seq![
        Val::Int(ck(sv)[a] as int),
        Val::Text(text_at(cname_col(sv), a)),
        Val::Num { coeff: s, scale: 4 },
        Val::Num { coeff: cacct(sv)[a] as int, scale: 2 },
        Val::Text(text_at(nname_col(sv), nat_row(sv, a))),
        Val::Text(text_at(caddr_col(sv), a)),
        Val::Text(text_at(cphone_col(sv), a)),
        Val::Text(text_at(ccomm_col(sv), a)),
    ]
}

// ------------------------------------------------------------------------------------------------ range laws

/// Adjacent lineitem ranges add.
pub proof fn lemma_k_split(sv: StoresView, k: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures
        ksum(sv, k, lo, hi) == ksum(sv, k, lo, mid) + ksum(sv, k, mid, hi),
        kcnt(sv, k, lo, hi) == kcnt(sv, k, lo, mid) + kcnt(sv, k, mid, hi),
        kabs(sv, k, lo, hi) == kabs(sv, k, lo, mid) + kabs(sv, k, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_k_split(sv, k, lo, mid, hi - 1);
    }
}

/// Lineitem ranges without a hit add nothing.
pub proof fn lemma_k_none(sv: StoresView, k: int, lo: int, hi: int)
    requires forall|i: int| lo <= i < hi ==> !#[trigger] lhit(sv, k, i),
    ensures ksum(sv, k, lo, hi) == 0, kcnt(sv, k, lo, hi) == 0, kabs(sv, k, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_k_none(sv, k, lo, hi - 1);
    }
}

/// When every hitting value is non-negative, the absolute mass is the sum.
pub proof fn lemma_k_nonneg(sv: StoresView, k: int, lo: int, hi: int)
    requires forall|i: int| lo <= i < hi && #[trigger] lhit(sv, k, i) ==> lval(sv, i) >= 0,
    ensures kabs(sv, k, lo, hi) == ksum(sv, k, lo, hi), ksum(sv, k, lo, hi) >= 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_k_nonneg(sv, k, lo, hi - 1);
    }
}

/// Counts are bounded by the range; masses are non-negative; a zero count has zero sums.
pub proof fn lemma_k_bounds(sv: StoresView, k: int, lo: int, hi: int)
    requires lo <= hi,
    ensures
        kcnt(sv, k, lo, hi) <= hi - lo,
        0 <= kabs(sv, k, lo, hi),
        -kabs(sv, k, lo, hi) <= ksum(sv, k, lo, hi) <= kabs(sv, k, lo, hi),
        kcnt(sv, k, lo, hi) == 0 ==> ksum(sv, k, lo, hi) == 0 && kabs(sv, k, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_k_bounds(sv, k, lo, hi - 1);
    }
}

/// Adjacent order ranges add.
pub proof fn lemma_c_split(sv: StoresView, dlo: int, dhi: int, a: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures
        csum(sv, dlo, dhi, a, lo, hi) == csum(sv, dlo, dhi, a, lo, mid) + csum(sv, dlo, dhi, a, mid, hi),
        ccnt(sv, dlo, dhi, a, lo, hi) == ccnt(sv, dlo, dhi, a, lo, mid) + ccnt(sv, dlo, dhi, a, mid, hi),
        cabs(sv, dlo, dhi, a, lo, hi) == cabs(sv, dlo, dhi, a, lo, mid) + cabs(sv, dlo, dhi, a, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_c_split(sv, dlo, dhi, a, lo, mid, hi - 1);
    }
}

/// Order ranges that customer `a` does not collect from add nothing.
pub proof fn lemma_c_none(sv: StoresView, dlo: int, dhi: int, a: int, lo: int, hi: int)
    requires forall|j: int| lo <= j < hi ==> !#[trigger] cmatch(sv, dlo, dhi, a, j),
    ensures csum(sv, dlo, dhi, a, lo, hi) == 0, ccnt(sv, dlo, dhi, a, lo, hi) == 0, cabs(sv, dlo, dhi, a, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_c_none(sv, dlo, dhi, a, lo, hi - 1);
    }
}

/// Counts and masses of a customer: non-negative; a zero count has zero sums.
pub proof fn lemma_c_bounds(sv: StoresView, dlo: int, dhi: int, a: int, lo: int, hi: int)
    requires lo <= hi,
    ensures
        0 <= cabs(sv, dlo, dhi, a, lo, hi),
        -cabs(sv, dlo, dhi, a, lo, hi) <= csum(sv, dlo, dhi, a, lo, hi) <= cabs(sv, dlo, dhi, a, lo, hi),
        ccnt(sv, dlo, dhi, a, lo, hi) == 0 ==> csum(sv, dlo, dhi, a, lo, hi) == 0 && cabs(sv, dlo, dhi, a, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_c_bounds(sv, dlo, dhi, a, lo, hi - 1);
        if cmatch(sv, dlo, dhi, a, hi - 1) {
            lemma_k_bounds(sv, ok(sv)[hi - 1] as int, 0, n_l(sv));
        }
    }
}

/// The nation row of a customer whose nation exists: in range, with the customer's nation key.
pub proof fn lemma_nat_row(sv: StoresView, a: int)
    requires natok(sv, a),
    ensures 0 <= nat_row(sv, a) < n_n(sv), nk(sv)[nat_row(sv, a)] == cnk(sv)[a],
{
}

} // verus!
