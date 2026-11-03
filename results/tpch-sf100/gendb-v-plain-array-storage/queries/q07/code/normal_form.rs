//! The statement in normal form over the joined rows of
//! `FROM supplier, lineitem, orders, customer, nation n1, nation n2`.
//!
//! A joined row is `S[s] ++ L[l] ++ O[o] ++ C[c] ++ N[a] ++ N[b]` (7 + 16 + 9 + 8 + 4 + 4 = 48 values, the
//! left-deep product `from6`). `q7_cols` projects the fifteen columns the statement reads, in this order:
//! `x = [s_suppkey, s_nationkey, l_orderkey, l_suppkey, l_extendedprice, l_discount, l_shipdate, o_orderkey,
//! o_custkey, c_custkey, c_nationkey, n1.n_nationkey, n1.n_name, n2.n_nationkey, n2.n_name]`. `q7_qual` is the WHERE
//! condition on such an `x`, `out4` the four projected columns `supp_nation, cust_nation, l_year, volume` of a
//! qualifying row; `g2` groups those four-column rows by their first three values and sums the fourth (scale 4).
//!
//! Dates: VERUS_SQL dates count days since 2000-01-01, the stored ones since 1970-01-01 (10957 days earlier). The
//! window `1995-01-01 ..= 1996-12-31` is `-1826 ..= -1096` in SQL days and `9131 ..= 9861` in stored days; 1996
//! starts at stored day 9496.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::relation::product_rows;
use crate::spec::datetime::civil_from_date;
use crate::spec::fns::extract::extract_field;
use crate::link::query::{QuerySpec, AggKind, proj};

verus! {

// ------------------------------------------------------------------------------------------------ parameters

/// `$1`: its bytes.
pub open spec fn p1_of(ps: Seq<Literal>) -> Seq<u8> {
    match ps[0] { Literal::Text(b) => b, _ => Seq::empty() }
}

/// `$2`: its bytes.
pub open spec fn p2_of(ps: Seq<Literal>) -> Seq<u8> {
    match ps[1] { Literal::Text(b) => b, _ => Seq::empty() }
}

// ------------------------------------------------------------------------------------------------ the ship window

/// Stored day `d` (days since 1970-01-01) lies in `1995-01-01 ..= 1996-12-31`.
pub open spec fn ship_in(d: int) -> bool { 9131 <= d <= 9861 }

/// The year of a stored day of the window: 1996 from stored day 9496 (1996-01-01) on.
pub open spec fn ship_year(d: int) -> int { if d < 9496 { 1995 } else { 1996 } }

// ------------------------------------------------------------------------------------------------ joined rows

/// `supplier x lineitem`.
pub open spec fn from2(db: Database) -> Seq<Row> { product_rows(db.tables[5], db.tables[0]) }

/// `.. x orders`.
pub open spec fn from3(db: Database) -> Seq<Row> { product_rows(from2(db), db.tables[1]) }

/// `.. x customer`.
pub open spec fn from4(db: Database) -> Seq<Row> { product_rows(from3(db), db.tables[2]) }

/// `.. x nation n1`.
pub open spec fn from5(db: Database) -> Seq<Row> { product_rows(from4(db), db.tables[6]) }

/// `.. x nation n2`: FROM's rows.
pub open spec fn from6(db: Database) -> Seq<Row> { product_rows(from5(db), db.tables[6]) }

/// Joined row of supplier `s`, lineitem `l`, orders `o`, customer `c`, nations `a` (n1) and `b` (n2).
pub open spec fn joined6(db: Database, s: int, l: int, o: int, c: int, a: int, b: int) -> Row {
    db.tables[5][s] + db.tables[0][l] + db.tables[1][o] + db.tables[2][c] + db.tables[6][a] + db.tables[6][b]
}

/// Positions of the fifteen columns read, in the 48-column joined row.
pub open spec fn q7_cols() -> Seq<nat> { seq![0nat, 3, 7, 9, 12, 13, 17, 23, 24, 32, 35, 40, 41, 44, 45] }

// ------------------------------------------------------------------------------------------------ WHERE and SELECT

pub open spec fn coeff_of(v: Val) -> int { match v { Val::Num { coeff, .. } => coeff, _ => 0 } }

/// `(n1.n_name = $1 AND n2.n_name = $2) OR (n1.n_name = $2 AND n2.n_name = $1)`.
pub open spec fn names_ok(x: Val, y: Val, p1: Seq<u8>, p2: Seq<u8>) -> bool {
    (x == Val::Text(p1) && y == Val::Text(p2)) || (x == Val::Text(p2) && y == Val::Text(p1))
}

/// `l_shipdate BETWEEN DATE '1995-01-01' AND DATE '1996-12-31'` (SQL days).
pub open spec fn date_in(v: Val) -> bool {
    match v { Val::Date(d) => -1826 <= d <= -1096, _ => false }
}

/// WHERE on a projected row `x` (two-valued: every operand is a non-NULL value of its column's type).
pub open spec fn q7_qual(p1: Seq<u8>, p2: Seq<u8>, x: Row) -> bool {
    &&& x[0] == x[3]
    &&& x[7] == x[2]
    &&& x[9] == x[8]
    &&& x[1] == x[11]
    &&& x[10] == x[13]
    &&& names_ok(x[12], x[14], p1, p2)
    &&& date_in(x[6])
}

/// WHERE on a joined row.
pub open spec fn qual_row(ps: Seq<Literal>, r: Row) -> bool { q7_qual(p1_of(ps), p2_of(ps), proj(r, q7_cols())) }

/// `EXTRACT(YEAR FROM d)`.
pub open spec fn year_val(v: Val) -> Val {
    match v {
        Val::Date(d) => Val::Num { coeff: extract_field(ScalarFn::ExtractYear, civil_from_date(d)), scale: 0 },
        _ => Val::Null,
    }
}

/// The SELECT list on a projected row: `n1.n_name, n2.n_name, EXTRACT(YEAR FROM l_shipdate),
/// l_extendedprice * (1 - l_discount)` (the volume at scale 4).
pub open spec fn out4(x: Row) -> Row {
    seq![x[12], x[14], year_val(x[6]), Val::Num { coeff: coeff_of(x[4]) * (100 - coeff_of(x[5])), scale: 4 }]
}

/// The SELECT list on a joined row.
pub open spec fn select_of(r: Row) -> Row { out4(proj(r, q7_cols())) }

/// The WHERE as a normal-form condition over projected joined rows (no aggregate of its own).
pub open spec fn g1(ps: Seq<Literal>) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| q7_qual(p1_of(ps), p2_of(ps), x),
        key: |x: Row| Seq::<Val>::empty(),
        arg: |j: int, x: Row| 0int,
        aggs: Seq::empty(),
        outs: Seq::empty(),
        grouped: true,
    }
}

/// GROUP BY the first three columns of the SELECT rows, SUM of the fourth (scale 4); output `key ++ [sum]`.
pub open spec fn g2() -> QuerySpec {
    QuerySpec {
        qual: |x: Row| true,
        key: |x: Row| seq![x[0], x[1], x[2]],
        arg: |j: int, x: Row| coeff_of(x[3]),
        aggs: seq![AggKind::Sum { scale: 4 }],
        outs: seq![0nat, 1, 2, 3],
        grouped: true,
    }
}

/// The identity projection of a SELECT row.
pub open spec fn c4() -> Seq<nat> { seq![0nat, 1, 2, 3] }

} // verus!
