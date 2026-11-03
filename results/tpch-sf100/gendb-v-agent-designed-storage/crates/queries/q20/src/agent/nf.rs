//! The statement's normal form over the database's tables (independent of storage).
//!
//! - `like_of(t, pat)`: `t LIKE pat ESCAPE '\'` as a value; `part_err`: some part name raises an error (always
//!   22025, `InvalidEscapeSequence`); `part_hit(k)`: some part row of key `k` matches;
//! - `lsum(k, s)` / `lcnt(k, s)`: the l_quantity coefficients (scale 2) and the number of the lineitem rows of part
//!   `k` and supplier `s` shipped in `[d0, d1)` (`d1`: the day of `$2 + 1 year`);
//! - `ps_qual(r)`: partsupp row `r` passes the subquery's WHERE: its part matches, it has such lineitem rows and
//!   `ps_availqty > 0.5 * SUM`, i.e. `200 * ps_availqty > lsum` (`lcnt == 0` makes the SUM NULL: not kept);
//! - `sk_ok(s)`: some qualifying partsupp row has supplier `s`; `nat_ok(k)`: some nation row of key `k` is named `$3`;
//! - the result rows: `[s_name, s_address]` of every supplier row with `sk_ok` and `nat_ok`, in supplier order
//!   (`nf_rows`), unless the part LIKE fails while the outer product and partsupp are not empty (`nf_outcome`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::datetime::*;
use crate::spec::fns::like::like_value;
use crate::link::join::{keep, sum_of};
use crate::link::expr::{ival, tval};

verus! {

/// The text of a text literal.
pub open spec fn ptext(l: Literal) -> Seq<u8> {
    match l {
        Literal::Text(b) => b,
        _ => Seq::empty(),
    }
}

/// The pattern `$1`.
pub open spec fn pat_of(ps: Seq<Literal>) -> Seq<u8> {
    ptext(ps[0])
}

/// The nation name `$3`.
pub open spec fn nname_of(ps: Seq<Literal>) -> Seq<u8> {
    ptext(ps[2])
}

/// The day of `$2`.
pub open spec fn d0_of(ps: Seq<Literal>) -> int {
    match ps[1] {
        Literal::Date { y, m, d } => date_from_civil(y, m, d),
        _ => 0,
    }
}

/// The timestamp `$2 + 1 year`, when it is in range.
pub open spec fn hi_ts(ps: Seq<Literal>) -> Result<int, SqlError> {
    match date_to_ts(d0_of(ps)) {
        Err(e) => Err(e),
        Ok(t) => ts_add_interval(t, 12, 0, 0),
    }
}

/// `d1` is the day whose midnight is `$2 + 1 year`.
pub open spec fn d1_ok(ps: Seq<Literal>, d1: int) -> bool {
    hi_ts(ps) == Ok::<int, SqlError>(d1 * usecs_per_day())
}

/// `t LIKE pat ESCAPE '\'`.
pub open spec fn like_of(t: Seq<u8>, pat: Seq<u8>) -> Result<Val, SqlError> {
    like_value(Val::Text(t), Val::Text(pat), Val::Text(seq![92u8]))
}

/// `t LIKE pat` is true.
pub open spec fn like_hit(t: Seq<u8>, pat: Seq<u8>) -> bool {
    like_of(t, pat) == Ok::<Val, SqlError>(Val::Bool(true))
}

/// The part rows.
pub open spec fn pt(db: Database) -> Seq<Row> {
    db.tables[3]
}

/// Some part name raises an error.
pub open spec fn part_err(db: Database, pat: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < pt(db).len() && #[trigger] like_of(tval(pt(db)[i][1]), pat) is Err
}

/// Some part row of key `k` matches.
pub open spec fn part_hit(db: Database, pat: Seq<u8>, k: int) -> bool {
    exists|i: int| 0 <= i < pt(db).len() && pt(db)[i][0] == Val::Int(k) && #[trigger] like_hit(tval(pt(db)[i][1]), pat)
}

/// A lineitem row of part `k`, supplier `s`, shipped in `[d0, d1)`.
pub open spec fn lsel(k: int, s: int, d0: int, d1: int, r: Row) -> bool {
    r[1] == Val::Int(k) && r[2] == Val::Int(s) && d0 <= ival(r[10]) && ival(r[10]) < d1
}

/// Its l_quantity coefficient (0 for other rows).
pub open spec fn lq_term(k: int, s: int, d0: int, d1: int) -> spec_fn(Row) -> int {
    |r: Row| if lsel(k, s, d0, d1, r) { ival(r[4]) } else { 0int }
}

/// 1 (0 for other rows).
pub open spec fn lc_term(k: int, s: int, d0: int, d1: int) -> spec_fn(Row) -> int {
    |r: Row| if lsel(k, s, d0, d1, r) { 1int } else { 0int }
}

/// The lineitem rows.
pub open spec fn lt(db: Database) -> Seq<Row> {
    db.tables[0]
}

/// The l_quantity sum (coefficient of scale 2) of the lineitem rows of part `k`, supplier `s` in the window.
pub open spec fn lsum(db: Database, k: int, s: int, d0: int, d1: int) -> int {
    sum_of(lt(db), lq_term(k, s, d0, d1))
}

/// Their number.
pub open spec fn lcnt(db: Database, k: int, s: int, d0: int, d1: int) -> int {
    sum_of(lt(db), lc_term(k, s, d0, d1))
}

/// Partsupp row `r` passes the subquery's WHERE.
pub open spec fn ps_qual(db: Database, pat: Seq<u8>, d0: int, d1: int, r: Row) -> bool {
    let k = ival(r[0]);
    let s = ival(r[1]);
    &&& part_hit(db, pat, k)
    &&& lcnt(db, k, s, d0, d1) > 0
    &&& 200 * ival(r[2]) > lsum(db, k, s, d0, d1)
}

/// The partsupp rows.
pub open spec fn pst(db: Database) -> Seq<Row> {
    db.tables[4]
}

/// Some qualifying partsupp row has supplier `s`.
pub open spec fn sk_ok(db: Database, pat: Seq<u8>, d0: int, d1: int, s: int) -> bool {
    exists|i: int| 0 <= i < pst(db).len() && #[trigger] ps_qual(db, pat, d0, d1, pst(db)[i]) && pst(db)[i][1] == Val::Int(s)
}

/// The nation rows.
pub open spec fn nt(db: Database) -> Seq<Row> {
    db.tables[6]
}

/// Some nation row of key `k` is named `name`.
pub open spec fn nat_ok(db: Database, name: Seq<u8>, k: int) -> bool {
    exists|j: int| 0 <= j < nt(db).len() && #[trigger] nt(db)[j][0] == Val::Int(k) && nt(db)[j][1] == Val::Text(name)
}

/// The supplier rows.
pub open spec fn st(db: Database) -> Seq<Row> {
    db.tables[5]
}

/// Supplier row `r` is in the result.
pub open spec fn s_qual(db: Database, ps: Seq<Literal>, d1: int, r: Row) -> bool {
    sk_ok(db, pat_of(ps), d0_of(ps), d1, ival(r[0])) && nat_ok(db, nname_of(ps), ival(r[3]))
}

pub open spec fn s_qual_f(db: Database, ps: Seq<Literal>, d1: int) -> spec_fn(Row) -> bool {
    |r: Row| s_qual(db, ps, d1, r)
}

/// The output row of a supplier row: `[s_name, s_address]`.
pub open spec fn out_row(r: Row) -> Row {
    seq![r[1], r[2]]
}

/// The result rows in supplier order.
pub open spec fn nf_rows(db: Database, ps: Seq<Literal>, d1: int) -> Seq<Row> {
    keep(st(db), s_qual_f(db, ps, d1)).map_values(|r: Row| out_row(r))
}

/// The statement's body: an error when the part LIKE fails and it is evaluated, else the result rows.
pub open spec fn nf_outcome(db: Database, ps: Seq<Literal>, d1: int) -> Result<Seq<Row>, SqlError> {
    if st(db).len() > 0 && nt(db).len() > 0 && pst(db).len() > 0 && part_err(db, pat_of(ps)) {
        Err(SqlError::InvalidEscapeSequence)
    } else {
        Ok(nf_rows(db, ps, d1))
    }
}

} // verus!
