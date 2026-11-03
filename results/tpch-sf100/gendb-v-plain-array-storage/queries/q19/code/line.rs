//! The statement per lineitem row (the normal form the scan computes).
//!
//! The WHERE clause is three branches `k = 0, 1, 2` (the SQL's first, second and third parenthesized group). Branch
//! `k` holds on part row `a` (`pcond`) when its brand is the parameter `pb(ps, k)` (`$1`, `$3`, `$5`), its
//! container is one of the branch's four containers (`cont_ok`) and `1 <= p_size <= 5 (k + 1)`; on lineitem row `l`
//! (`qcond`) when `pv <= l_quantity <= pv + 10` for the parameter `pv(ps, k)` (`$2`, `$4`, `$6`; on coefficients at
//! scale 2, `100 pv <= q <= 100 (pv + 10)`). Every branch also needs `l_shipmode IN ('AIR', 'AIR REG')` and
//! `l_shipinstruct = 'DELIVER IN PERSON'` (`ship_ok`).
//!
//! Row `l` qualifies (`qual`) when some part row has its `l_partkey` (`has_part`; the part key column is
//! duplicate-free, so that row, `part_of`, is unique) and some branch holds on that part row and on `l`. Its volume
//! `vol` is `l_extendedprice * (1 - l_discount)` as a coefficient at scale 4.
//!
//! `tot(sv, ps, lo, hi)` sums over the rows `lo..hi` the qualifying rows, their volume and absolute volume (`Tot`).
//! Each is a `range_sum` of a guarded per-row term, so adjacent ranges add (`lemma_tot_split`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::int::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;
use crate::agent::common::selection::*;

verus! {

// ------------------------------------------------------------------------------------------------ literals

/// The container literals of branch `k` (`j = 0..3` in the order of the SQL's IN lists).
pub open spec fn cont_lit(k: int, j: int) -> Seq<u8> {
    if k == 0 {
        if j == 0 { seq![83u8, 77u8, 32u8, 67u8, 65u8, 83u8, 69u8] }              // SM CASE
        else if j == 1 { seq![83u8, 77u8, 32u8, 66u8, 79u8, 88u8] }               // SM BOX
        else if j == 2 { seq![83u8, 77u8, 32u8, 80u8, 65u8, 67u8, 75u8] }         // SM PACK
        else { seq![83u8, 77u8, 32u8, 80u8, 75u8, 71u8] }                         // SM PKG
    } else if k == 1 {
        if j == 0 { seq![77u8, 69u8, 68u8, 32u8, 66u8, 65u8, 71u8] }              // MED BAG
        else if j == 1 { seq![77u8, 69u8, 68u8, 32u8, 66u8, 79u8, 88u8] }         // MED BOX
        else if j == 2 { seq![77u8, 69u8, 68u8, 32u8, 80u8, 75u8, 71u8] }         // MED PKG
        else { seq![77u8, 69u8, 68u8, 32u8, 80u8, 65u8, 67u8, 75u8] }             // MED PACK
    } else {
        if j == 0 { seq![76u8, 71u8, 32u8, 67u8, 65u8, 83u8, 69u8] }              // LG CASE
        else if j == 1 { seq![76u8, 71u8, 32u8, 66u8, 79u8, 88u8] }               // LG BOX
        else if j == 2 { seq![76u8, 71u8, 32u8, 80u8, 65u8, 67u8, 75u8] }         // LG PACK
        else { seq![76u8, 71u8, 32u8, 80u8, 75u8, 71u8] }                         // LG PKG
    }
}

/// `AIR`, `AIR REG` and `DELIVER IN PERSON`.
pub open spec fn air_lit() -> Seq<u8> { seq![65u8, 73u8, 82u8] }
pub open spec fn air_reg_lit() -> Seq<u8> { seq![65u8, 73u8, 82u8, 32u8, 82u8, 69u8, 71u8] }
pub open spec fn dip_lit() -> Seq<u8> {
    seq![68u8, 69u8, 76u8, 73u8, 86u8, 69u8, 82u8, 32u8, 73u8, 78u8, 32u8, 80u8, 69u8, 82u8, 83u8, 79u8, 78u8]
}

// ------------------------------------------------------------------------------------------------ parameters

/// The brand parameter of branch `k` (`$1`, `$3`, `$5`).
pub open spec fn pb(ps: Seq<Literal>, k: int) -> Seq<u8> {
    match ps[2 * k] { Literal::Text(b) => b, _ => Seq::empty() }
}

/// The quantity parameter of branch `k` (`$2`, `$4`, `$6`).
pub open spec fn pv(ps: Seq<Literal>, k: int) -> int {
    match ps[2 * k + 1] { Literal::Int { v, .. } => v, _ => 0 }
}

/// The largest `p_size` of branch `k`.
pub open spec fn size_hi(k: int) -> int { 5 * (k + 1) }

// ------------------------------------------------------------------------------------------------ conditions

/// The container text `s` is one of branch `k`'s.
pub open spec fn cont_ok(k: int, s: Seq<u8>) -> bool {
    s == cont_lit(k, 0) || s == cont_lit(k, 1) || s == cont_lit(k, 2) || s == cont_lit(k, 3)
}

/// Branch `k`'s conditions on part row `a`.
pub open spec fn pcond(sv: StoresView, ps: Seq<Literal>, k: int, a: int) -> bool {
    &&& p_brand(sv, a) == pb(ps, k)
    &&& cont_ok(k, p_cont(sv, a))
    &&& 1 <= p_size(sv)[a] <= size_hi(k)
}

/// Branch `k`'s quantity window on lineitem row `l` (coefficients at scale 2).
pub open spec fn qcond(sv: StoresView, ps: Seq<Literal>, k: int, l: int) -> bool {
    100 * pv(ps, k) <= l_qty(sv)[l] as int && l_qty(sv)[l] as int <= 100 * (pv(ps, k) + 10)
}

/// The ship mode and instruction of lineitem row `l`.
pub open spec fn ship_ok(sv: StoresView, l: int) -> bool {
    &&& (l_mode(sv, l) == air_lit() || l_mode(sv, l) == air_reg_lit())
    &&& l_instr(sv, l) == dip_lit()
}

/// Some branch holds on part row `a` and lineitem row `l`.
pub open spec fn lq(sv: StoresView, ps: Seq<Literal>, a: int, l: int) -> bool {
    &&& (pcond(sv, ps, 0, a) && qcond(sv, ps, 0, l)) || (pcond(sv, ps, 1, a) && qcond(sv, ps, 1, l))
        || (pcond(sv, ps, 2, a) && qcond(sv, ps, 2, l))
    &&& ship_ok(sv, l)
}

/// Some part row has row `l`'s part key.
pub open spec fn has_part(sv: StoresView, l: int) -> bool {
    exists|a: int| 0 <= a < n_p(sv) && #[trigger] p_key(sv)[a] == l_pkey(sv)[l]
}

/// The part row of row `l` (unique when it exists, `lemma_part_of`).
pub open spec fn part_of(sv: StoresView, l: int) -> int {
    choose|a: int| 0 <= a < n_p(sv) && #[trigger] p_key(sv)[a] == l_pkey(sv)[l]
}

/// Row `l` qualifies: it has a part, and some branch holds.
pub open spec fn qual(sv: StoresView, ps: Seq<Literal>, l: int) -> bool {
    has_part(sv, l) && lq(sv, ps, part_of(sv, l), l)
}

/// `l_extendedprice * (1 - l_discount)` of row `l` (coefficient at scale 4).
pub open spec fn vol(sv: StoresView, l: int) -> int {
    l_price(sv)[l] as int * (100 - l_disc(sv)[l] as int)
}

// ------------------------------------------------------------------------------------------------ totals

/// The per-row terms of the three totals.
pub open spec fn f_cnt(sv: StoresView, ps: Seq<Literal>) -> spec_fn(int) -> int { |l: int| if qual(sv, ps, l) { 1int } else { 0int } }
pub open spec fn f_all(sv: StoresView, ps: Seq<Literal>) -> spec_fn(int) -> int { |l: int| if qual(sv, ps, l) { vol(sv, l) } else { 0int } }
pub open spec fn f_abs(sv: StoresView, ps: Seq<Literal>) -> spec_fn(int) -> int { |l: int| if qual(sv, ps, l) { abs(vol(sv, l)) } else { 0int } }

/// Totals over a set of rows: qualifying rows, their volume and absolute volume (scale-4 coefficients).
pub struct Tot {
    pub cnt: int,
    pub s_all: int,
    pub a_all: int,
}

/// The totals over the rows `lo..hi`.
pub open spec fn tot(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int) -> Tot {
    Tot {
        cnt: range_sum(lo, hi, f_cnt(sv, ps)),
        s_all: range_sum(lo, hi, f_all(sv, ps)),
        a_all: range_sum(lo, hi, f_abs(sv, ps)),
    }
}

pub open spec fn tot_plus(a: Tot, b: Tot) -> Tot {
    Tot { cnt: a.cnt + b.cnt, s_all: a.s_all + b.s_all, a_all: a.a_all + b.a_all }
}

pub open spec fn tot_zero() -> Tot { Tot { cnt: 0, s_all: 0, a_all: 0 } }

/// The contribution of row `l` to the totals.
pub open spec fn tot1(sv: StoresView, ps: Seq<Literal>, l: int) -> Tot {
    Tot { cnt: (f_cnt(sv, ps))(l), s_all: (f_all(sv, ps))(l), a_all: (f_abs(sv, ps))(l) }
}

/// Totals with the bounds of real ones: a non-negative count and a mass bounding the sum.
pub open spec fn tot_sane(t: Tot) -> bool {
    &&& 0 <= t.cnt
    &&& 0 <= t.a_all
    &&& -t.a_all <= t.s_all <= t.a_all
    &&& t.cnt == 0 ==> t.a_all == 0 && t.s_all == 0
}

// ------------------------------------------------------------------------------------------------ lemmas

/// The part row of a row with a part holds its key, and it is the only one.
pub proof fn lemma_part_of(sv: StoresView, l: int)
    requires keys_unique(p_key(sv)), has_part(sv, l),
    ensures
        0 <= part_of(sv, l) < n_p(sv),
        p_key(sv)[part_of(sv, l)] == l_pkey(sv)[l],
        forall|a: int| 0 <= a < n_p(sv) && #[trigger] p_key(sv)[a] == l_pkey(sv)[l] ==> a == part_of(sv, l),
{
    let a0 = part_of(sv, l);
    assert forall|a: int| 0 <= a < n_p(sv) && #[trigger] p_key(sv)[a] == l_pkey(sv)[l] implies a == a0 by {
        if a != a0 {
            assert(p_key(sv)[a] == p_key(sv)[a0]);
        }
    }
}

/// A part row holding row `l`'s key is its part row.
pub proof fn lemma_part_is(sv: StoresView, l: int, a: int)
    requires keys_unique(p_key(sv)), 0 <= a < n_p(sv), p_key(sv)[a] == l_pkey(sv)[l],
    ensures has_part(sv, l), part_of(sv, l) == a,
{
    assert(has_part(sv, l));
    lemma_part_of(sv, l);
}

/// One more row of a range.
pub proof fn lemma_tot_step(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int)
    requires lo <= hi,
    ensures tot(sv, ps, lo, hi + 1) == tot_plus(tot(sv, ps, lo, hi), tot1(sv, ps, hi)),
{
}

/// Adjacent ranges add.
pub proof fn lemma_tot_split(sv: StoresView, ps: Seq<Literal>, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures tot(sv, ps, lo, hi) == tot_plus(tot(sv, ps, lo, mid), tot(sv, ps, mid, hi)),
    decreases hi - mid,
{
    if hi > mid {
        lemma_tot_split(sv, ps, lo, mid, hi - 1);
    }
}

/// The empty range.
pub proof fn lemma_tot_empty(sv: StoresView, ps: Seq<Literal>, lo: int)
    ensures tot(sv, ps, lo, lo) == tot_zero(),
{
}

/// Totals of a range are sane and count at most its rows.
pub proof fn lemma_tot_bounds(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int)
    requires lo <= hi,
    ensures tot_sane(tot(sv, ps, lo, hi)), tot(sv, ps, lo, hi).cnt <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_tot_bounds(sv, ps, lo, hi - 1);
    }
}

} // verus!
