//! The statement in normal form over the joined rows of `FROM part, supplier, lineitem, partsupp, orders, nation`.
//!
//! A joined row is `P[p] ++ S[s] ++ L[l] ++ PS[q] ++ O[o] ++ N[a]` (9 + 7 + 16 + 5 + 9 + 4 = 50 values, the
//! left-deep product `from6`). `q9_cols` projects the seventeen columns the statement reads, in this order:
//! `x = [p_partkey, p_name, s_suppkey, s_nationkey, l_orderkey, l_partkey, l_suppkey, l_quantity, l_extendedprice,
//! l_discount, ps_partkey, ps_suppkey, ps_supplycost, o_orderkey, o_orderdate, n_nationkey, n_name]`. `q9_qual` is
//! the WHERE condition on such an `x` (six key equalities and `p_name LIKE $1`), `out3` the three projected columns
//! `nation, o_year, amount` of a qualifying row; `g2` groups those three-column rows by their first two values and
//! sums the third (scale 4).
//!
//! `p_name LIKE $1` (escape backslash) is `like_res`: `Ok(Bool(b))` or the SQL error the matcher raises. The WHERE
//! is two-valued exactly when no part row's LIKE raises (`like_ok`); the statement's error otherwise is handled in
//! `agent::like_error`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::relation::product_rows;
use crate::spec::datetime::civil_from_date;
use crate::spec::fns::extract::extract_field;
use crate::spec::fns::like::like_value;
use crate::link::query::{QuerySpec, AggKind, proj};

verus! {

// ------------------------------------------------------------------------------------------------ parameters

/// `$1`: its bytes.
pub open spec fn pat_of(ps: Seq<Literal>) -> Seq<u8> {
    match ps[0] { Literal::Text(b) => b, _ => Seq::empty() }
}

/// The escape string of `LIKE` (a backslash, supplied by the frontend).
pub open spec fn esc_bytes() -> Seq<u8> { seq![92u8] }

/// `name LIKE pat ESCAPE '\'`: `Ok(Bool(_))` or the matcher's SQL error.
pub open spec fn like_res(name: Seq<u8>, pat: Seq<u8>) -> Result<Val, SqlError> {
    like_value(Val::Text(name), Val::Text(pat), Val::Text(esc_bytes()))
}

/// `name LIKE pat` holds.
pub open spec fn like_true(name: Seq<u8>, pat: Seq<u8>) -> bool {
    like_res(name, pat) == Ok::<Val, SqlError>(Val::Bool(true))
}

/// `name LIKE pat` evaluates without error.
pub open spec fn like_ok(name: Seq<u8>, pat: Seq<u8>) -> bool {
    like_res(name, pat) is Ok
}

// ------------------------------------------------------------------------------------------------ joined rows

/// `part x supplier`.
pub open spec fn from2(db: Database) -> Seq<Row> { product_rows(db.tables[3], db.tables[5]) }

/// `.. x lineitem`.
pub open spec fn from3(db: Database) -> Seq<Row> { product_rows(from2(db), db.tables[0]) }

/// `.. x partsupp`.
pub open spec fn from4(db: Database) -> Seq<Row> { product_rows(from3(db), db.tables[4]) }

/// `.. x orders`.
pub open spec fn from5(db: Database) -> Seq<Row> { product_rows(from4(db), db.tables[1]) }

/// `.. x nation`: FROM's rows.
pub open spec fn from6(db: Database) -> Seq<Row> { product_rows(from5(db), db.tables[6]) }

/// Joined row of part `p`, supplier `s`, lineitem `l`, partsupp `q`, orders `o` and nation `a`.
pub open spec fn joined6(db: Database, p: int, s: int, l: int, q: int, o: int, a: int) -> Row {
    db.tables[3][p] + db.tables[5][s] + db.tables[0][l] + db.tables[4][q] + db.tables[1][o] + db.tables[6][a]
}

/// Positions of the seventeen columns read, in the 50-column joined row.
pub open spec fn q9_cols() -> Seq<nat> { seq![0nat, 1, 9, 12, 16, 17, 18, 20, 21, 22, 32, 33, 35, 37, 41, 46, 47] }

// ------------------------------------------------------------------------------------------------ WHERE and SELECT

pub open spec fn coeff_of(v: Val) -> int { match v { Val::Num { coeff, .. } => coeff, _ => 0 } }

pub open spec fn text_of(v: Val) -> Seq<u8> { match v { Val::Text(b) => b, _ => Seq::empty() } }

/// WHERE on a projected row `x` (two-valued where the LIKE does not raise).
pub open spec fn q9_qual(pat: Seq<u8>, x: Row) -> bool {
    &&& x[2] == x[6]
    &&& x[11] == x[6]
    &&& x[10] == x[5]
    &&& x[0] == x[5]
    &&& x[13] == x[4]
    &&& x[3] == x[15]
    &&& like_true(text_of(x[1]), pat)
}

/// WHERE on a joined row.
pub open spec fn qual_row(ps: Seq<Literal>, r: Row) -> bool { q9_qual(pat_of(ps), proj(r, q9_cols())) }

/// `EXTRACT(YEAR FROM d)`.
pub open spec fn year_val(v: Val) -> Val {
    match v {
        Val::Date(d) => Val::Num { coeff: extract_field(ScalarFn::ExtractYear, civil_from_date(d)), scale: 0 },
        _ => Val::Null,
    }
}

/// `l_extendedprice * (1 - l_discount) - ps_supplycost * l_quantity` on coefficients (scale 4).
pub open spec fn amount(price: int, disc: int, cost: int, qty: int) -> int { price * (100 - disc) - cost * qty }

/// The SELECT list on a projected row: `n_name, EXTRACT(YEAR FROM o_orderdate), amount` (amount at scale 4).
pub open spec fn out3(x: Row) -> Row {
    seq![x[16], year_val(x[14]),
        Val::Num { coeff: amount(coeff_of(x[8]), coeff_of(x[9]), coeff_of(x[12]), coeff_of(x[7])), scale: 4 }]
}

/// The SELECT list on a joined row.
pub open spec fn select_of(r: Row) -> Row { out3(proj(r, q9_cols())) }

/// The WHERE as a normal-form condition over projected joined rows (no aggregate of its own).
pub open spec fn g1(ps: Seq<Literal>) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| q9_qual(pat_of(ps), x),
        key: |x: Row| Seq::<Val>::empty(),
        arg: |j: int, x: Row| 0int,
        aggs: Seq::empty(),
        outs: Seq::empty(),
        grouped: true,
    }
}

/// GROUP BY the first two columns of the SELECT rows, SUM of the third (scale 4); output `key ++ [sum]`.
pub open spec fn g2() -> QuerySpec {
    QuerySpec {
        qual: |x: Row| true,
        key: |x: Row| seq![x[0], x[1]],
        arg: |j: int, x: Row| coeff_of(x[2]),
        aggs: seq![AggKind::Sum { scale: 4 }],
        outs: seq![0nat, 1, 2],
        grouped: true,
    }
}

/// The identity projection of a SELECT row.
pub open spec fn c3() -> Seq<nat> { seq![0nat, 1, 2] }

} // verus!
