//! The four `lineitem` columns Q6 reads, as whole stored parts (`&'static` slices of `n` rows), and their view as
//! the normal form's projected rows (`crow`): row `i` is (quantity, extendedprice, discount, shipdate), the
//! numerics as scale-2 coefficients and the date as days since 2000-01-01.
use vstd::prelude::*;
use crate::spec::value::*;

verus! {

/// Column slices of `lineitem` (`n` rows; stored dates are days since 1970-01-01).
#[derive(Clone, Copy)]
pub struct Cols {
    pub ship: &'static [i32],
    pub disc: &'static [i128],
    pub qty: &'static [i128],
    pub price: &'static [i128],
    pub n: usize,
}

/// Days since 2000-01-01 of a stored date (days since 1970-01-01).
pub open spec fn day_of(d: i32) -> int {
    d as int - 10957
}

/// Projected row `i`: (l_quantity, l_extendedprice, l_discount, l_shipdate).
pub open spec fn crow(c: Cols, i: int) -> Row {
    seq![
        Val::Num { coeff: c.qty@[i] as int, scale: 2 },
        Val::Num { coeff: c.price@[i] as int, scale: 2 },
        Val::Num { coeff: c.disc@[i] as int, scale: 2 },
        Val::Date(day_of(c.ship@[i]))
    ]
}

/// All projected rows.
pub open spec fn crows(c: Cols) -> Seq<Row> {
    Seq::new(c.n as nat, |i: int| crow(c, i))
}

/// Exclusive bound of the absolute coefficient of a numeric(15,2) value: `10^15`.
pub open spec fn coeff_bound() -> int {
    1_000_000_000_000_000
}

/// A numeric(15,2) coefficient.
pub open spec fn coeff_ok(x: i128) -> bool {
    -coeff_bound() < x < coeff_bound()
}

/// The slices hold `n` rows, and the factors of the summed product are numeric(15,2) coefficients.
pub open spec fn cols_wf(c: Cols) -> bool {
    &&& c.ship@.len() == c.n
    &&& c.disc@.len() == c.n
    &&& c.qty@.len() == c.n
    &&& c.price@.len() == c.n
    &&& forall|i: int| 0 <= i < c.n ==> coeff_ok(#[trigger] c.price@[i])
    &&& forall|i: int| 0 <= i < c.n ==> coeff_ok(#[trigger] c.disc@[i])
}

} // verus!
