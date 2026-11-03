//! The fixed dates of the statement as day numbers (days since 2000-01-01) and the year of every day in the
//! shipping window: `l_shipdate BETWEEN DATE '1995-01-01' AND DATE '1996-12-31'` is days `[-1826, -1096]`, and
//! `EXTRACT(YEAR FROM d)` is 1995 below day -1461 (1996-01-01) and 1996 from it on.
use vstd::prelude::*;
use crate::spec::ast::*;
use crate::spec::value::*;
use crate::spec::eval::lit_val;
use crate::spec::datetime::*;
use crate::spec::fns::extract::extract_field;

verus! {

/// First day of the window (1995-01-01).
pub open spec fn win_lo() -> int { -1826 }
/// Last day of the window (1996-12-31).
pub open spec fn win_hi() -> int { -1096 }
/// First day of 1996.
pub open spec fn day_1996() -> int { -1461 }

/// The year of day `d` inside the window.
pub open spec fn win_year(d: int) -> int {
    if d < day_1996() { 1995 } else { 1996 }
}

/// Every day of `[d, hi]` has the window year (decided by evaluation).
pub open spec fn years_from(d: int, hi: int) -> bool
    decreases hi + 1 - d,
{
    if d > hi {
        true
    } else {
        extract_field(ScalarFn::ExtractYear, civil_from_date(d)) == win_year(d) && years_from(d + 1, hi)
    }
}

proof fn lemma_years_from(d: int, hi: int, x: int)
    requires years_from(d, hi), d <= x <= hi,
    ensures extract_field(ScalarFn::ExtractYear, civil_from_date(x)) == win_year(x),
    decreases x - d,
{
    if d < x {
        lemma_years_from(d + 1, hi, x);
    }
}

/// `EXTRACT(YEAR FROM d)` of a day of the window.
pub proof fn lemma_win_year(x: int)
    requires win_lo() <= x <= win_hi(),
    ensures extract_field(ScalarFn::ExtractYear, civil_from_date(x)) == win_year(x),
{
    if x < -1600 {
        assert(years_from(-1826, -1601)) by (compute_only);
        lemma_years_from(-1826, -1601, x);
    } else if x < -1350 {
        assert(years_from(-1600, -1351)) by (compute_only);
        lemma_years_from(-1600, -1351, x);
    } else {
        assert(years_from(-1350, -1096)) by (compute_only);
        lemma_years_from(-1350, -1096, x);
    }
}

/// The two date literals of the statement.
pub proof fn lemma_window_lits()
    ensures
        lit_val(Literal::Date { y: 1995, m: 1, d: 1 }) == Ok::<Val, SqlError>(Val::Date(win_lo())),
        lit_val(Literal::Date { y: 1996, m: 12, d: 31 }) == Ok::<Val, SqlError>(Val::Date(win_hi())),
{
    assert(lit_val(Literal::Date { y: 1995, m: 1, d: 1 }) == Ok::<Val, SqlError>(Val::Date(-1826))) by (compute);
    assert(lit_val(Literal::Date { y: 1996, m: 12, d: 31 }) == Ok::<Val, SqlError>(Val::Date(-1096))) by (compute);
}

} // verus!
