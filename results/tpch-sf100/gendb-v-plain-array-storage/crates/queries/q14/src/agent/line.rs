//! The statement per lineitem row (the normal form the scan computes).
//!
//! The ship window is `Win { lo, hi }` in stored days (since 1970-01-01): row `l` is inside when
//! `lo <= l_shipdate < hi`. Row `l` qualifies (`qual`) when it is inside the window and some part row has its
//! `l_partkey` (`has_part`; the part key column is duplicate-free, so that row, `part_of`, is unique). A qualifying
//! row counts as promotional (`lpromo`) when its part's `p_type` starts with the characters `PROMO`
//! (`common::like_prefix::starts_with_chars`, the meaning of `LIKE 'PROMO%'`). Its volume `vol` is
//! `l_extendedprice * (1 - l_discount)` as a coefficient at scale 4.
//!
//! `tot(sv, w, lo, hi)` sums over the rows `lo..hi`: the qualifying rows, their volume and absolute volume, and the
//! same three over the promotional rows (`Tot`). Each is a `range_sum` of a guarded per-row term, so adjacent ranges
//! add (`lemma_tot_split`).
use vstd::prelude::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;
use crate::agent::common::selection::*;
use crate::agent::common::like_prefix::starts_with_chars;

verus! {

/// The ship window in stored days: `lo <= l_shipdate < hi`.
pub struct Win {
    pub lo: int,
    pub hi: int,
}

/// Row `l`'s ship date is inside the window.
pub open spec fn in_win(sv: StoresView, w: Win, l: int) -> bool {
    w.lo <= l_ship(sv)[l] as int && (l_ship(sv)[l] as int) < w.hi
}

/// Some part row has row `l`'s part key.
pub open spec fn has_part(sv: StoresView, l: int) -> bool {
    exists|a: int| 0 <= a < n_p(sv) && #[trigger] p_key(sv)[a] == l_pkey(sv)[l]
}

/// The part row of row `l` (unique when it exists, `lemma_part_of`).
pub open spec fn part_of(sv: StoresView, l: int) -> int {
    choose|a: int| 0 <= a < n_p(sv) && #[trigger] p_key(sv)[a] == l_pkey(sv)[l]
}

/// The bytes `PROMO`.
pub open spec fn promo_lit() -> Seq<u8> { seq![80u8, 82u8, 79u8, 77u8, 79u8] }

/// Part row `a`'s type starts with the characters `PROMO`.
pub open spec fn promo(sv: StoresView, a: int) -> bool { starts_with_chars(p_type(sv, a), promo_lit()) }

/// Row `l` qualifies: inside the window, with a part.
pub open spec fn qual(sv: StoresView, w: Win, l: int) -> bool { in_win(sv, w, l) && has_part(sv, l) }

/// Row `l` qualifies and its part is promotional.
pub open spec fn lpromo(sv: StoresView, w: Win, l: int) -> bool { qual(sv, w, l) && promo(sv, part_of(sv, l)) }

/// `l_extendedprice * (1 - l_discount)` of row `l` (coefficient at scale 4).
pub open spec fn vol(sv: StoresView, l: int) -> int {
    l_price(sv)[l] as int * (100 - l_disc(sv)[l] as int)
}

/// The per-row terms of the six totals.
pub open spec fn f_cnt(sv: StoresView, w: Win) -> spec_fn(int) -> int { |l: int| if qual(sv, w, l) { 1int } else { 0int } }
pub open spec fn f_all(sv: StoresView, w: Win) -> spec_fn(int) -> int { |l: int| if qual(sv, w, l) { vol(sv, l) } else { 0int } }
pub open spec fn f_abs(sv: StoresView, w: Win) -> spec_fn(int) -> int { |l: int| if qual(sv, w, l) { abs(vol(sv, l)) } else { 0int } }
pub open spec fn f_npr(sv: StoresView, w: Win) -> spec_fn(int) -> int { |l: int| if lpromo(sv, w, l) { 1int } else { 0int } }
pub open spec fn f_pr(sv: StoresView, w: Win) -> spec_fn(int) -> int { |l: int| if lpromo(sv, w, l) { vol(sv, l) } else { 0int } }
pub open spec fn f_apr(sv: StoresView, w: Win) -> spec_fn(int) -> int { |l: int| if lpromo(sv, w, l) { abs(vol(sv, l)) } else { 0int } }

/// Totals over a set of rows: qualifying rows, their volume and absolute volume, and the same over the
/// promotional rows (exact integers; volumes are scale-4 coefficients).
pub struct Tot {
    pub cnt: int,
    pub s_all: int,
    pub a_all: int,
    pub n_pr: int,
    pub s_pr: int,
    pub a_pr: int,
}

/// The totals over the rows `lo..hi`.
pub open spec fn tot(sv: StoresView, w: Win, lo: int, hi: int) -> Tot {
    Tot {
        cnt: range_sum(lo, hi, f_cnt(sv, w)),
        s_all: range_sum(lo, hi, f_all(sv, w)),
        a_all: range_sum(lo, hi, f_abs(sv, w)),
        n_pr: range_sum(lo, hi, f_npr(sv, w)),
        s_pr: range_sum(lo, hi, f_pr(sv, w)),
        a_pr: range_sum(lo, hi, f_apr(sv, w)),
    }
}

pub open spec fn tot_plus(a: Tot, b: Tot) -> Tot {
    Tot {
        cnt: a.cnt + b.cnt,
        s_all: a.s_all + b.s_all,
        a_all: a.a_all + b.a_all,
        n_pr: a.n_pr + b.n_pr,
        s_pr: a.s_pr + b.s_pr,
        a_pr: a.a_pr + b.a_pr,
    }
}

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

/// No part row holds row `l`'s key.
pub proof fn lemma_no_part(sv: StoresView, l: int)
    requires forall|a: int| 0 <= a < n_p(sv) ==> #[trigger] p_key(sv)[a] != l_pkey(sv)[l],
    ensures !has_part(sv, l),
{
}

/// Adjacent ranges add.
pub proof fn lemma_tot_split(sv: StoresView, w: Win, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures tot(sv, w, lo, hi) == tot_plus(tot(sv, w, lo, mid), tot(sv, w, mid, hi)),
    decreases hi - mid,
{
    if hi > mid {
        lemma_tot_split(sv, w, lo, mid, hi - 1);
    }
}

/// The empty range.
pub proof fn lemma_tot_empty(sv: StoresView, w: Win, lo: int)
    ensures tot(sv, w, lo, lo) == (Tot { cnt: 0, s_all: 0, a_all: 0, n_pr: 0, s_pr: 0, a_pr: 0 }),
{
}

/// Counts and absolute sums are non-negative and bound the sums; the promotional part is bounded by the whole.
pub proof fn lemma_tot_bounds(sv: StoresView, w: Win, lo: int, hi: int)
    requires lo <= hi,
    ensures ({
        let t = tot(sv, w, lo, hi);
        &&& 0 <= t.n_pr <= t.cnt <= hi - lo
        &&& 0 <= t.a_pr <= t.a_all
        &&& -t.a_all <= t.s_all <= t.a_all
        &&& -t.a_pr <= t.s_pr <= t.a_pr
        &&& t.cnt == 0 ==> t.a_all == 0 && t.s_all == 0 && t.n_pr == 0
        &&& t.n_pr == 0 ==> t.a_pr == 0 && t.s_pr == 0
    }),
    decreases hi - lo,
{
    if hi > lo {
        lemma_tot_bounds(sv, w, lo, hi - 1);
    }
}

/// An empty window has no qualifying row.
pub proof fn lemma_tot_no_window(sv: StoresView, w: Win, lo: int, hi: int)
    requires w.hi <= w.lo, lo <= hi,
    ensures tot(sv, w, lo, hi).cnt == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_tot_no_window(sv, w, lo, hi - 1);
    }
}

} // verus!
