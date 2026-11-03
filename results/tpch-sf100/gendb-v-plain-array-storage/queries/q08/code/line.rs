//! The statement per lineitem row (the normal form the scan computes).
//!
//! A *tuple* of lineitem row `l` names one row of each other FROM input: part `p`, supplier `s`, orders `o`,
//! customer `c`, nation `n1` (the customer's), nation `n2` (the supplier's) and region `r`. It is *ok*
//! (`tup_ok`) when it satisfies every WHERE conjunct together with `l`. Row `l` qualifies (`line_q`) when it has
//! an ok tuple; the primary keys make that tuple unique (`lemma_tup_unique`), and `line_tup` names it. The row's
//! group is the year of its order date (`line_year`: 1995 or 1996, the only years of the date window), its
//! volume is `l_extendedprice * (1 - l_discount)` (`line_vol`, coefficient at scale 4), and it counts for
//! `$1` when its supplier's nation is named `$1` (`line_then`).
//!
//! `tot(sv, ps, y, lo, hi)` sums, over the qualifying rows `lo..hi` of year `y`, the count, the volume, its
//! absolute value, and the same three over the rows that count for `$1` (`Tot`). Adjacent ranges add
//! (`lemma_tot_split`).
//!
//! Dates are stored days since 1970-01-01: the window 1995-01-01 ..= 1996-12-31 is `9131 ..= 9861`, and
//! 1996-01-01 is day 9496.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;

verus! {

// ------------------------------------------------------------------------------------------------ parameters

/// `$1`: the nation name whose share is computed.
pub open spec fn nat_of(ps: Seq<Literal>) -> Seq<u8> { match ps[0] { Literal::Text(b) => b, _ => Seq::empty() } }

/// `$2`: the region name of the customers.
pub open spec fn reg_of(ps: Seq<Literal>) -> Seq<u8> { match ps[1] { Literal::Text(b) => b, _ => Seq::empty() } }

/// `$3`: the part type.
pub open spec fn typ_of(ps: Seq<Literal>) -> Seq<u8> { match ps[2] { Literal::Text(b) => b, _ => Seq::empty() } }

// ------------------------------------------------------------------------------------------------ dates

/// First and last stored day of the window, and the first day of 1996.
pub open spec fn day_lo() -> int { 9131 }
pub open spec fn day_hi() -> int { 9861 }
pub open spec fn day_1996() -> int { 9496 }

/// A stored order date inside `BETWEEN DATE '1995-01-01' AND DATE '1996-12-31'`.
pub open spec fn date_in(d: i32) -> bool { day_lo() <= d <= day_hi() }

/// The year of a stored date inside the window.
pub open spec fn year_of_day(d: i32) -> int { if (d as int) < day_1996() { 1995 } else { 1996 } }

// ------------------------------------------------------------------------------------------------ tuples

/// Row indices of the other inputs joined with one lineitem row.
pub struct Tup {
    pub p: int,
    pub s: int,
    pub o: int,
    pub c: int,
    pub n1: int,
    pub n2: int,
    pub r: int,
}

/// Every index is a row of its table.
pub open spec fn tup_in(sv: StoresView, t: Tup) -> bool {
    &&& 0 <= t.p < n_p(sv)
    &&& 0 <= t.s < n_s(sv)
    &&& 0 <= t.o < n_o(sv)
    &&& 0 <= t.c < n_c(sv)
    &&& 0 <= t.n1 < n_n(sv)
    &&& 0 <= t.n2 < n_n(sv)
    &&& 0 <= t.r < n_r(sv)
}

/// Part row `p` joins lineitem row `l` and has type `$3`.
pub open spec fn part_hit(sv: StoresView, ps: Seq<Literal>, p: int, l: int) -> bool {
    p_key(sv)[p] == l_pkey(sv)[l] && p_type(sv, p) == typ_of(ps)
}

/// Orders row `o` joins lineitem row `l` and is dated inside the window.
pub open spec fn ord_hit(sv: StoresView, o: int, l: int) -> bool {
    o_key(sv)[o] == l_okey(sv)[l] && date_in(o_date(sv)[o])
}

/// Region row `r` is nation row `n1`'s region and is named `$2`.
pub open spec fn reg_hit(sv: StoresView, ps: Seq<Literal>, r: int, n1: int) -> bool {
    r_key(sv)[r] == n_reg(sv)[n1] && r_name(sv, r) == reg_of(ps)
}

/// Every WHERE conjunct holds for lineitem row `l` and the tuple `t`.
pub open spec fn tup_ok(sv: StoresView, ps: Seq<Literal>, l: int, t: Tup) -> bool {
    &&& tup_in(sv, t)
    &&& part_hit(sv, ps, t.p, l)
    &&& s_key(sv)[t.s] == l_skey(sv)[l]
    &&& ord_hit(sv, t.o, l)
    &&& c_key(sv)[t.c] == o_cust(sv)[t.o]
    &&& n_key(sv)[t.n1] == c_nat(sv)[t.c]
    &&& reg_hit(sv, ps, t.r, t.n1)
    &&& n_key(sv)[t.n2] == s_nat(sv)[t.s]
}

/// Lineitem row `l` qualifies: some tuple is ok.
pub open spec fn line_q(sv: StoresView, ps: Seq<Literal>, l: int) -> bool {
    exists|t: Tup| #[trigger] tup_ok(sv, ps, l, t)
}

/// The ok tuple of a qualifying row (unique, `lemma_tup_unique`).
pub open spec fn line_tup(sv: StoresView, ps: Seq<Literal>, l: int) -> Tup {
    choose|t: Tup| #[trigger] tup_ok(sv, ps, l, t)
}

/// The group (year) of a qualifying row.
pub open spec fn line_year(sv: StoresView, ps: Seq<Literal>, l: int) -> int {
    year_of_day(o_date(sv)[line_tup(sv, ps, l).o])
}

/// `l_extendedprice * (1 - l_discount)` of row `l` (coefficient at scale 4).
pub open spec fn line_vol(sv: StoresView, l: int) -> int {
    l_price(sv)[l] * (100 - l_disc(sv)[l])
}

/// The supplier's nation of a qualifying row is named `$1`.
pub open spec fn line_then(sv: StoresView, ps: Seq<Literal>, l: int) -> bool {
    n_name(sv, line_tup(sv, ps, l).n2) == nat_of(ps)
}

/// The primary keys make the ok tuple of a row unique.
pub proof fn lemma_tup_unique(sv: StoresView, ps: Seq<Literal>, l: int, t1: Tup, t2: Tup)
    requires keys_ok(sv), tup_ok(sv, ps, l, t1), tup_ok(sv, ps, l, t2),
    ensures t1 == t2,
{
    assert(p_key(sv)[t1.p] == p_key(sv)[t2.p]);
    assert(t1.p == t2.p);
    assert(s_key(sv)[t1.s] == s_key(sv)[t2.s]);
    assert(t1.s == t2.s);
    assert(o_key(sv)[t1.o] == o_key(sv)[t2.o]);
    assert(t1.o == t2.o);
    assert(c_key(sv)[t1.c] == c_key(sv)[t2.c]);
    assert(t1.c == t2.c);
    assert(n_key(sv)[t1.n1] == n_key(sv)[t2.n1]);
    assert(t1.n1 == t2.n1);
    assert(r_key(sv)[t1.r] == r_key(sv)[t2.r]);
    assert(t1.r == t2.r);
    assert(n_key(sv)[t1.n2] == n_key(sv)[t2.n2]);
    assert(t1.n2 == t2.n2);
}

/// An ok tuple is the row's tuple.
pub proof fn lemma_tup_is(sv: StoresView, ps: Seq<Literal>, l: int, t: Tup)
    requires keys_ok(sv), tup_ok(sv, ps, l, t),
    ensures line_q(sv, ps, l), line_tup(sv, ps, l) == t, tup_ok(sv, ps, l, line_tup(sv, ps, l)),
{
    assert(tup_ok(sv, ps, l, t));
    let t0 = line_tup(sv, ps, l);
    lemma_tup_unique(sv, ps, l, t0, t);
}

// ------------------------------------------------------------------------------------------------ totals

/// Per-year totals: qualifying rows, their volume and absolute volume, and the same over the rows counting for
/// `$1` (all exact integers; volumes are scale-4 coefficients).
pub struct Tot {
    pub cnt: int,
    pub s_all: int,
    pub a_all: int,
    pub n_then: int,
    pub s_then: int,
    pub a_then: int,
}

pub open spec fn tot_zero() -> Tot {
    Tot { cnt: 0, s_all: 0, a_all: 0, n_then: 0, s_then: 0, a_then: 0 }
}

pub open spec fn tot_plus(a: Tot, b: Tot) -> Tot {
    Tot {
        cnt: a.cnt + b.cnt,
        s_all: a.s_all + b.s_all,
        a_all: a.a_all + b.a_all,
        n_then: a.n_then + b.n_then,
        s_then: a.s_then + b.s_then,
        a_then: a.a_then + b.a_then,
    }
}

/// Lineitem row `l` qualifies and belongs to year `y`.
pub open spec fn hit(sv: StoresView, ps: Seq<Literal>, l: int, y: int) -> bool {
    line_q(sv, ps, l) && line_year(sv, ps, l) == y
}

/// Row `l`'s contribution to year `y`.
pub open spec fn line_tot(sv: StoresView, ps: Seq<Literal>, y: int, l: int) -> Tot {
    if hit(sv, ps, l, y) {
        let v = line_vol(sv, l);
        let t = line_then(sv, ps, l);
        Tot {
            cnt: 1,
            s_all: v,
            a_all: abs(v),
            n_then: if t { 1 } else { 0 },
            s_then: if t { v } else { 0 },
            a_then: if t { abs(v) } else { 0 },
        }
    } else {
        tot_zero()
    }
}

/// Totals of year `y` over the lineitem rows `lo..hi`.
pub open spec fn tot(sv: StoresView, ps: Seq<Literal>, y: int, lo: int, hi: int) -> Tot
    decreases hi - lo,
{
    if hi <= lo { tot_zero() } else { tot_plus(tot(sv, ps, y, lo, hi - 1), line_tot(sv, ps, y, hi - 1)) }
}

/// Adjacent ranges add.
pub proof fn lemma_tot_split(sv: StoresView, ps: Seq<Literal>, y: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures tot(sv, ps, y, lo, hi) == tot_plus(tot(sv, ps, y, lo, mid), tot(sv, ps, y, mid, hi)),
    decreases hi - mid,
{
    if hi > mid {
        lemma_tot_split(sv, ps, y, lo, mid, hi - 1);
    }
}

/// One more row.
pub proof fn lemma_tot_step(sv: StoresView, ps: Seq<Literal>, y: int, lo: int, hi: int)
    requires lo <= hi,
    ensures tot(sv, ps, y, lo, hi + 1) == tot_plus(tot(sv, ps, y, lo, hi), line_tot(sv, ps, y, hi)),
{
}

/// Rows that do not qualify contribute nothing.
pub proof fn lemma_tot_gap(sv: StoresView, ps: Seq<Literal>, y: int, lo: int, hi: int)
    requires forall|l: int| lo <= l < hi ==> !#[trigger] line_q(sv, ps, l),
    ensures tot(sv, ps, y, lo, hi) == tot_zero(),
    decreases hi - lo,
{
    if hi > lo {
        lemma_tot_gap(sv, ps, y, lo, hi - 1);
        assert(!line_q(sv, ps, hi - 1));
    }
}

/// Counts and absolute sums are non-negative and bound the sums; the `$1` part is bounded by the whole.
pub proof fn lemma_tot_bounds(sv: StoresView, ps: Seq<Literal>, y: int, lo: int, hi: int)
    requires lo <= hi,
    ensures ({
        let t = tot(sv, ps, y, lo, hi);
        &&& 0 <= t.n_then <= t.cnt <= hi - lo
        &&& 0 <= t.a_then <= t.a_all
        &&& -t.a_all <= t.s_all <= t.a_all
        &&& -t.a_then <= t.s_then <= t.a_then
        &&& t.cnt == 0 ==> t.a_all == 0 && t.s_all == 0 && t.n_then == 0
        &&& t.n_then == 0 ==> t.a_then == 0 && t.s_then == 0
    }),
    decreases hi - lo,
{
    if hi > lo {
        lemma_tot_bounds(sv, ps, y, lo, hi - 1);
    }
}

} // verus!
