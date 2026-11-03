//! The `lineitem` columns Q1 reads, as whole stored parts (`&'static` slices), and their view as the normal form's
//! projected rows (`crow`): row `i` is (quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate).
//! Text columns keep the stored offsets (`n + 1`, absolute positions in the bytes part) and the whole bytes part.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::query::{TextView, text_at, text_wf};
use crate::agent::normal::*;

verus! {

/// Column slices of `lineitem` (`n` rows).
#[derive(Clone, Copy)]
pub struct Cols {
    pub qty: &'static [i128],
    pub price: &'static [i128],
    pub disc: &'static [i128],
    pub tax: &'static [i128],
    pub rf_offsets: &'static [i64],
    pub rf_bytes: &'static [u8],
    pub ls_offsets: &'static [i64],
    pub ls_bytes: &'static [u8],
    pub ship: &'static [i32],
    pub n: usize,
}

pub open spec fn rf_view(c: Cols) -> TextView {
    TextView { offsets: c.rf_offsets@, bytes: c.rf_bytes@ }
}

pub open spec fn ls_view(c: Cols) -> TextView {
    TextView { offsets: c.ls_offsets@, bytes: c.ls_bytes@ }
}

/// Days since 2000-01-01 of a stored date (days since 1970-01-01).
pub open spec fn day_of(d: i32) -> int {
    d as int - 10957
}

/// Projected row `i` (the normal form's row).
pub open spec fn crow(c: Cols, i: int) -> Row {
    seq![
        Val::Num { coeff: c.qty@[i] as int, scale: 2 },
        Val::Num { coeff: c.price@[i] as int, scale: 2 },
        Val::Num { coeff: c.disc@[i] as int, scale: 2 },
        Val::Num { coeff: c.tax@[i] as int, scale: 2 },
        Val::Text(text_at(rf_view(c), i)),
        Val::Text(text_at(ls_view(c), i)),
        Val::Date(day_of(c.ship@[i]))
    ]
}

/// All projected rows.
pub open spec fn crows(c: Cols) -> Seq<Row> {
    Seq::new(c.n as nat, |i: int| crow(c, i))
}

/// A numeric(15,2) coefficient.
pub open spec fn coeff_ok(x: i128) -> bool {
    -coeff_bound() < x < coeff_bound()
}

/// The slices hold `n` rows: lengths, well-formed text columns, and numeric(15,2) coefficients.
pub open spec fn cols_wf(c: Cols) -> bool {
    &&& c.qty@.len() == c.n
    &&& c.price@.len() == c.n
    &&& c.disc@.len() == c.n
    &&& c.tax@.len() == c.n
    &&& c.ship@.len() == c.n
    &&& text_wf(rf_view(c), c.n as int)
    &&& text_wf(ls_view(c), c.n as int)
    &&& forall|i: int| 0 <= i < c.n ==> coeff_ok(#[trigger] c.qty@[i])
    &&& forall|i: int| 0 <= i < c.n ==> coeff_ok(#[trigger] c.price@[i])
    &&& forall|i: int| 0 <= i < c.n ==> coeff_ok(#[trigger] c.disc@[i])
    &&& forall|i: int| 0 <= i < c.n ==> coeff_ok(#[trigger] c.tax@[i])
}

/// The group key of row `i`.
pub open spec fn key_of(c: Cols, i: int) -> Row {
    q1_key(crow(c, i))
}

pub proof fn lemma_crow(c: Cols, i: int)
    ensures
        crow(c, i).len() == 7,
        crow(c, i)[0] == (Val::Num { coeff: c.qty@[i] as int, scale: 2 }),
        crow(c, i)[1] == (Val::Num { coeff: c.price@[i] as int, scale: 2 }),
        crow(c, i)[2] == (Val::Num { coeff: c.disc@[i] as int, scale: 2 }),
        crow(c, i)[3] == (Val::Num { coeff: c.tax@[i] as int, scale: 2 }),
        crow(c, i)[4] == Val::Text(text_at(rf_view(c), i)),
        crow(c, i)[5] == Val::Text(text_at(ls_view(c), i)),
        crow(c, i)[6] == Val::Date(day_of(c.ship@[i])),
        key_of(c, i) == seq![Val::Text(text_at(rf_view(c), i)), Val::Text(text_at(ls_view(c), i))],
{
}

/// Row `i` of well-formed columns is a well-formed projected row.
pub proof fn lemma_crow_ok(c: Cols, i: int)
    requires cols_wf(c), 0 <= i < c.n,
    ensures src_row_ok(crow(c, i)),
{
    lemma_crow(c, i);
    assert(coeff_ok(c.qty@[i]) && coeff_ok(c.price@[i]) && coeff_ok(c.disc@[i]) && coeff_ok(c.tax@[i]));
}

pub proof fn lemma_crows(c: Cols)
    ensures
        crows(c).len() == c.n,
        forall|i: int| 0 <= i < c.n ==> #[trigger] crows(c)[i] == crow(c, i),
{
}

} // verus!
