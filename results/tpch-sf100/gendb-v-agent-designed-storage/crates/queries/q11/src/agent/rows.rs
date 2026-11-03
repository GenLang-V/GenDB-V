//! The plan's accumulators over partsupp row indices. Row `r` qualifies (`rowq`) when its supplier is in a nation
//! named `$1`; its group key is ps_partkey (`rkey`), its argument `ps_supplycost * ps_availqty` (`rval`, scale 2).
//! Over a row range `lo .. hi`: `ksum`/`kcnt` the SUM and count of the qualifying rows of key `k`, `tsum`/`tabs`
//! the SUM and absolute mass of all qualifying rows (each defined by recursion on `hi`, so a scan step is one
//! unfolding). `lemma_bridge` equates the whole-table accumulators with the normal form's (`nf::gq`, `nf::gs`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::expr::ival;
use crate::link::query::{gsum, gcount, gabs};
use crate::link::join::{sum_of, lemma_sum_of_ext};
use super::nf::*;
use super::tables::Tabs;

verus! {

pub open spec fn rowq(t: Tabs, name: Seq<u8>, r: int) -> bool {
    rq(t, name, t.ps[r])
}

pub open spec fn rkey(t: Tabs, r: int) -> int {
    ival(t.ps[r][0])
}

pub open spec fn rval(t: Tabs, r: int) -> int {
    pval(t.ps[r])
}

/// SUM of the qualifying rows of key `k` in `lo .. hi`.
pub open spec fn ksum(t: Tabs, name: Seq<u8>, k: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else {
        ksum(t, name, k, lo, hi - 1) + if rowq(t, name, hi - 1) && rkey(t, hi - 1) == k { rval(t, hi - 1) } else { 0 }
    }
}

/// Number of qualifying rows of key `k` in `lo .. hi`.
pub open spec fn kcnt(t: Tabs, name: Seq<u8>, k: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else {
        kcnt(t, name, k, lo, hi - 1) + if rowq(t, name, hi - 1) && rkey(t, hi - 1) == k { 1int } else { 0 }
    }
}

/// SUM of all qualifying rows in `lo .. hi`.
pub open spec fn tsum(t: Tabs, name: Seq<u8>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { tsum(t, name, lo, hi - 1) + if rowq(t, name, hi - 1) { rval(t, hi - 1) } else { 0 } }
}

/// Absolute mass of all qualifying rows in `lo .. hi`.
pub open spec fn tabs(t: Tabs, name: Seq<u8>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { tabs(t, name, lo, hi - 1) + if rowq(t, name, hi - 1) { abs(rval(t, hi - 1)) } else { 0 } }
}

/// Adjacent ranges add.
pub proof fn lemma_split(t: Tabs, name: Seq<u8>, k: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures
        ksum(t, name, k, lo, hi) == ksum(t, name, k, lo, mid) + ksum(t, name, k, mid, hi),
        kcnt(t, name, k, lo, hi) == kcnt(t, name, k, lo, mid) + kcnt(t, name, k, mid, hi),
        tsum(t, name, lo, hi) == tsum(t, name, lo, mid) + tsum(t, name, mid, hi),
        tabs(t, name, lo, hi) == tabs(t, name, lo, mid) + tabs(t, name, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_split(t, name, k, lo, mid, hi - 1);
    }
}

/// Bounds: counts and masses are non-negative; every partial SUM is bounded by the mass.
pub proof fn lemma_bounds(t: Tabs, name: Seq<u8>, k: int, lo: int, hi: int)
    ensures
        kcnt(t, name, k, lo, hi) >= 0,
        tabs(t, name, lo, hi) >= 0,
        abs(ksum(t, name, k, lo, hi)) <= tabs(t, name, lo, hi),
        abs(tsum(t, name, lo, hi)) <= tabs(t, name, lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_bounds(t, name, k, lo, hi - 1);
    }
}

/// A key without qualifying rows has a zero SUM.
pub proof fn lemma_kzero(t: Tabs, name: Seq<u8>, k: int, lo: int, hi: int)
    requires kcnt(t, name, k, lo, hi) == 0,
    ensures ksum(t, name, k, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_bounds(t, name, k, lo, hi - 1);
        lemma_kzero(t, name, k, lo, hi - 1);
    }
}

/// An empty range has no rows.
pub proof fn lemma_kcnt_empty(t: Tabs, name: Seq<u8>, k: int, lo: int, hi: int)
    requires hi <= lo,
    ensures kcnt(t, name, k, lo, hi) == 0,
{
}

/// A key with a qualifying row has a witness row.
pub proof fn lemma_kwit(t: Tabs, name: Seq<u8>, k: int, lo: int, hi: int)
    requires kcnt(t, name, k, lo, hi) > 0,
    ensures exists|r: int| lo <= r < hi && rowq(t, name, r) && #[trigger] rkey(t, r) == k,
    decreases hi - lo,
{
    if hi > lo && !(rowq(t, name, hi - 1) && rkey(t, hi - 1) == k) {
        lemma_kwit(t, name, k, lo, hi - 1);
    }
}

/// A key no row of the range has: no qualifying rows, zero SUM.
pub proof fn lemma_knone(t: Tabs, name: Seq<u8>, k: int, lo: int, hi: int)
    requires forall|r: int| lo <= r < hi ==> #[trigger] rkey(t, r) != k,
    ensures kcnt(t, name, k, lo, hi) == 0, ksum(t, name, k, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_knone(t, name, k, lo, hi - 1);
    }
}

/// A qualifying row makes its key's count positive.
pub proof fn lemma_kpos(t: Tabs, name: Seq<u8>, r: int, lo: int, hi: int)
    requires lo <= r < hi, rowq(t, name, r),
    ensures kcnt(t, name, rkey(t, r), lo, hi) > 0,
    decreases hi - lo,
{
    lemma_bounds(t, name, rkey(t, r), lo, hi - 1);
    if r < hi - 1 {
        lemma_kpos(t, name, r, lo, hi - 1);
    }
}

// ------------------------------------------------------------------------------------------------ the bridge

/// `sum_of` over the first `n` rows is the index recursion of the same term.
proof fn lemma_prefix_sum(rows: Seq<Row>, f: spec_fn(Row) -> int, n: int)
    requires 0 <= n <= rows.len(),
    ensures sum_of(rows.subrange(0, n), f) == (if n == 0 { 0 } else { sum_of(rows.subrange(0, n - 1), f) + f(rows[n - 1]) }),
{
    if n > 0 {
        assert(rows.subrange(0, n).drop_last() =~= rows.subrange(0, n - 1));
    }
}

proof fn lemma_bridge_k(t: Tabs, name: Seq<u8>, k: int, n: int)
    requires tabs_typed(t), 0 <= n <= t.ps.len(),
    ensures
        ksum(t, name, k, 0, n) == sum_of(t.ps.subrange(0, n), on_rq(t, name, key_val(seq![Val::Int(k)]))),
        kcnt(t, name, k, 0, n) == sum_of(t.ps.subrange(0, n), on_rq(t, name, key_one(seq![Val::Int(k)]))),
    decreases n,
{
    lemma_prefix_sum(t.ps, on_rq(t, name, key_val(seq![Val::Int(k)])), n);
    lemma_prefix_sum(t.ps, on_rq(t, name, key_one(seq![Val::Int(k)])), n);
    if n > 0 {
        lemma_bridge_k(t, name, k, n - 1);
        let a = t.ps[n - 1];
        assert(ps_typed(a));
        assert((seq![a[0]] == seq![Val::Int(k)]) <==> (rkey(t, n - 1) == k)) by {
            if rkey(t, n - 1) == k {
                assert(seq![a[0]] =~= seq![Val::Int(k)]);
            }
            if seq![a[0]] == seq![Val::Int(k)] {
                assert(seq![a[0]][0] == seq![Val::Int(k)][0]);
            }
        }
    }
}

proof fn lemma_bridge_t(t: Tabs, name: Seq<u8>, n: int)
    requires 0 <= n <= t.ps.len(),
    ensures
        tsum(t, name, 0, n) == sum_of(t.ps.subrange(0, n), on_rq(t, name, all_val())),
        tabs(t, name, 0, n) == sum_of(t.ps.subrange(0, n), on_rq(t, name, all_abs())),
    decreases n,
{
    lemma_prefix_sum(t.ps, on_rq(t, name, all_val()), n);
    lemma_prefix_sum(t.ps, on_rq(t, name, all_abs()), n);
    if n > 0 {
        lemma_bridge_t(t, name, n - 1);
    }
}

/// The whole-table accumulators are the normal form's (`gq` per group key `[k]`, `gs` for the scalar group).
pub proof fn lemma_bridge(t: Tabs, name: Seq<u8>, k: int)
    requires tabs_typed(t), keys_unique(t),
    ensures ({
        let n = t.ps.len() as int;
        let e = Seq::<Val>::empty();
        &&& gsum(gq(name), xs(t), seq![Val::Int(k)], 0) == ksum(t, name, k, 0, n)
        &&& gcount(gq(name), xs(t), seq![Val::Int(k)]) == kcnt(t, name, k, 0, n)
        &&& gsum(gs(name), xs(t), e, 0) == tsum(t, name, 0, n)
        &&& gabs(gs(name), xs(t), e, 0) == tabs(t, name, 0, n)
    }),
{
    let n = t.ps.len() as int;
    lemma_accs(t, name, seq![Val::Int(k)]);
    lemma_bridge_k(t, name, k, n);
    lemma_bridge_t(t, name, n);
    assert(t.ps.subrange(0, n) =~= t.ps);
}

} // verus!
