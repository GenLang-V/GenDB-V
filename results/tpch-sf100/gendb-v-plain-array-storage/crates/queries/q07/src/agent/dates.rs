//! Civil years of the stored ship dates in the statement's window `1995-01-01 ..= 1996-12-31` (stored days since
//! 1970-01-01: `9131 ..= 9861`; `1996-01-01` is day `9496`): `EXTRACT(YEAR ..)` is 1995 or 1996.
use vstd::prelude::*;
use crate::spec::datetime::*;

verus! {

/// Stored days of 1995 are in year 1995.
pub proof fn lemma_year_1995(d: int)
    requires 9131 <= d < 9496,
    ensures civil_from_unix_days(d).0 == 1995,
{
    let z1 = d + 719468;
    assert(z1 / 146097 == 4);
    let doe = z1 - 4 * 146097;
    assert(144211 <= doe < 144576);
    assert(doe / 36524 == 3);
    assert(doe / 146096 == 0);
    if doe < 144270 {
        assert(doe / 1460 == 98);
        assert((doe - 98 + 3 - 0) / 365 == 394);
        let doy = doe - (365 * 394int + 394int / 4 - 394int / 100);
        assert(306 <= doy < 365);
        let mp = (5 * doy + 2) / 153;
        assert(10 <= mp <= 11);
    } else if doe < 144540 {
        assert(doe / 1460 == 98);
        assert((doe - 98 + 3 - 0) / 365 == 395);
        let doy = doe - (365 * 395int + 395int / 4 - 395int / 100);
        assert(0 <= doy < 270);
        let mp = (5 * doy + 2) / 153;
        assert(0 <= mp < 10);
    } else {
        assert(doe / 1460 == 99);
        assert((doe - 99 + 3 - 0) / 365 == 395);
        let doy = doe - (365 * 395int + 395int / 4 - 395int / 100);
        assert(270 <= doy <= 305);
        let mp = (5 * doy + 2) / 153;
        assert(0 <= mp < 10);
    }
}

/// Stored days of 1996 (a leap year) are in year 1996.
pub proof fn lemma_year_1996(d: int)
    requires 9496 <= d <= 9861,
    ensures civil_from_unix_days(d).0 == 1996,
{
    let z1 = d + 719468;
    assert(z1 / 146097 == 4);
    let doe = z1 - 4 * 146097;
    assert(144576 <= doe <= 144941);
    assert(doe / 36524 == 3);
    assert(doe / 146096 == 0);
    assert(doe / 1460 == 99);
    if doe < 144636 {
        assert((doe - 99 + 3 - 0) / 365 == 395);
        let doy = doe - (365 * 395int + 395int / 4 - 395int / 100);
        assert(306 <= doy <= 365);
        let mp = (5 * doy + 2) / 153;
        assert(10 <= mp <= 11);
    } else {
        assert((doe - 99 + 3 - 0) / 365 == 396);
        let doy = doe - (365 * 396int + 396int / 4 - 396int / 100);
        assert(0 <= doy <= 305);
        let mp = (5 * doy + 2) / 153;
        assert(0 <= mp < 10);
    }
}

} // verus!
