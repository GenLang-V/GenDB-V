//! The statement in normal form, at two levels.
//!
//! 1. Over the joined rows of `FROM customer, orders, lineitem` (`link::query::QuerySpec`): a joined row is
//!    `c ++ o ++ l` (8 + 9 + 16 values); `q3_cols` projects the ten columns the statement reads, in this order:
//!    `x = [c_custkey, c_mktsegment, o_orderkey, o_custkey, o_orderdate, o_shippriority, l_orderkey,
//!    l_extendedprice, l_discount, l_shipdate]`. `q3_spec(ps)` is the WHERE condition, the group key
//!    `(l_orderkey, o_orderdate, o_shippriority)` and the SUM argument coefficient (scale 4) on such `x`.
//! 2. Over the stored columns (`agent::tables`): an orders row `j` qualifies (`order_ok`) when its date is before
//!    `$2` and its customer has segment `$1`; a lineitem row `i` hits order `j` (`line_hit`) when its key is `j`'s
//!    key, it ships after `$2` and `j` qualifies. `order_sum(j, lo, hi)` is the exact sum of
//!    `l_extendedprice * (100 - l_discount)` (scale 4) over the lineitem rows `lo..hi` that hit `j`;
//!    `order_count` and `order_abs` count them and sum the absolute values.
//!
//! Dates: `$2` is `day_of(ps)` days since 2000-01-01 (VERUS_SQL); the stored dates count days since 1970-01-01, so
//! a stored date `x` is before `$2` exactly when `x < dl_of(ps) = day_of(ps) + 10957`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::datetime::*;
use crate::spec::numeric::abs;
use crate::spec::constraints::*;
use crate::spec::types::Constraint;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::link::query::{QuerySpec, AggKind};
use crate::agent::tables::*;

verus! {

// ------------------------------------------------------------------------------------------------ parameters

/// `$1`: the segment bytes.
pub open spec fn seg_of(ps: Seq<Literal>) -> Seq<u8> {
    match ps[0] { Literal::Text(b) => b, _ => Seq::empty() }
}

/// `$2`: days since 2000-01-01.
pub open spec fn day_of(ps: Seq<Literal>) -> int {
    match ps[1] { Literal::Date { y, m, d } => date_from_civil(y, m, d), _ => 0 }
}

/// `$2` in stored units (days since 1970-01-01).
pub open spec fn dl_of(ps: Seq<Literal>) -> int { day_of(ps) + 10957 }

// ------------------------------------------------------------------------------------------------ joined rows

/// Positions of the ten columns read, in the joined row `customer (0..8) ++ orders (8..17) ++ lineitem (17..33)`.
pub open spec fn q3_cols() -> Seq<nat> { seq![0nat, 6, 8, 9, 12, 15, 17, 22, 23, 27] }

pub open spec fn date_before(v: Val, p: int) -> bool { match v { Val::Date(d) => d < p, _ => false } }

pub open spec fn date_after(v: Val, p: int) -> bool { match v { Val::Date(d) => d > p, _ => false } }

pub open spec fn coeff_of(v: Val) -> int { match v { Val::Num { coeff, .. } => coeff, _ => 0 } }

/// WHERE on a projected row `x` (two-valued: every operand is a non-NULL value of its column's type).
pub open spec fn q3_qual(seg: Seq<u8>, p: int, x: Row) -> bool {
    &&& x[1] == Val::Text(seg)
    &&& x[0] == x[3]
    &&& x[6] == x[2]
    &&& date_before(x[4], p)
    &&& date_after(x[9], p)
}

/// GROUP BY l_orderkey, o_orderdate, o_shippriority.
pub open spec fn q3_key(x: Row) -> Row { seq![x[6], x[4], x[5]] }

/// Coefficient (scale 4) of `l_extendedprice * (1 - l_discount)`.
pub open spec fn q3_arg(x: Row) -> int { coeff_of(x[7]) * (100 - coeff_of(x[8])) }

/// The statement's normal form at binding `ps`: one SUM at scale 4; output `l_orderkey, revenue, o_orderdate,
/// o_shippriority` = positions 0, 3, 1, 2 of `key ++ [sum]`.
pub open spec fn q3_spec(ps: Seq<Literal>) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| q3_qual(seg_of(ps), day_of(ps), x),
        key: |x: Row| q3_key(x),
        arg: |j: int, x: Row| q3_arg(x),
        aggs: seq![AggKind::Sum { scale: 4 }],
        outs: seq![0nat, 3, 1, 2],
        grouped: true,
    }
}

// ------------------------------------------------------------------------------------------------ stored columns

/// Some customer row has key `key` and segment `seg`.
pub open spec fn cust_ok(sv: StoresView, seg: Seq<u8>, key: int) -> bool {
    exists|r: int| 0 <= r < n_c(sv) && ck(sv)[r] as int == key && #[trigger] cseg(sv, r) == seg
}

/// Orders row `j` qualifies: ordered before `$2` by a customer of segment `$1`.
pub open spec fn order_ok(sv: StoresView, seg: Seq<u8>, dl: int, j: int) -> bool {
    od(sv)[j] < dl && cust_ok(sv, seg, oc(sv)[j] as int)
}

/// Lineitem row `i` belongs to order `j`, ships after `$2`, and `j` qualifies.
pub open spec fn line_hit(sv: StoresView, seg: Seq<u8>, dl: int, i: int, j: int) -> bool {
    lk(sv)[i] == ok(sv)[j] && ls(sv)[i] > dl && order_ok(sv, seg, dl, j)
}

/// `l_extendedprice * (1 - l_discount)` of lineitem row `i` (coefficient at scale 4).
pub open spec fn line_value(sv: StoresView, i: int) -> int { lp(sv)[i] * (100 - ld(sv)[i]) }

/// Sum of `line_value` over the rows `lo..hi` that hit order `j`.
pub open spec fn order_sum(sv: StoresView, seg: Seq<u8>, dl: int, j: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else {
        order_sum(sv, seg, dl, j, lo, hi - 1) + if line_hit(sv, seg, dl, hi - 1, j) { line_value(sv, hi - 1) } else { 0 }
    }
}

/// Number of rows `lo..hi` that hit order `j`.
pub open spec fn order_count(sv: StoresView, seg: Seq<u8>, dl: int, j: int, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo { 0 } else {
        order_count(sv, seg, dl, j, lo, hi - 1) + if line_hit(sv, seg, dl, hi - 1, j) { 1nat } else { 0nat }
    }
}

/// Sum of `|line_value|` over the rows `lo..hi` that hit order `j`.
pub open spec fn order_abs(sv: StoresView, seg: Seq<u8>, dl: int, j: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else {
        order_abs(sv, seg, dl, j, lo, hi - 1) + if line_hit(sv, seg, dl, hi - 1, j) { abs(line_value(sv, hi - 1)) } else { 0 }
    }
}

/// The group key of orders row `j`.
pub open spec fn order_key(sv: StoresView, j: int) -> Row {
    seq![Val::Int(ok(sv)[j] as int), date32_val(od(sv)[j]), Val::Int(os(sv)[j] as int)]
}

/// The output row of orders row `j`'s group: `l_orderkey, revenue, o_orderdate, o_shippriority`.
pub open spec fn order_row(sv: StoresView, j: int, revenue: int) -> Row {
    seq![Val::Int(ok(sv)[j] as int), Val::Num { coeff: revenue, scale: 4 }, date32_val(od(sv)[j]), Val::Int(os(sv)[j] as int)]
}

// ------------------------------------------------------------------------------------------------ range laws

/// Adjacent ranges add.
pub proof fn lemma_order_split(sv: StoresView, seg: Seq<u8>, dl: int, j: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures
        order_sum(sv, seg, dl, j, lo, hi) == order_sum(sv, seg, dl, j, lo, mid) + order_sum(sv, seg, dl, j, mid, hi),
        order_count(sv, seg, dl, j, lo, hi) == order_count(sv, seg, dl, j, lo, mid) + order_count(sv, seg, dl, j, mid, hi),
        order_abs(sv, seg, dl, j, lo, hi) == order_abs(sv, seg, dl, j, lo, mid) + order_abs(sv, seg, dl, j, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_order_split(sv, seg, dl, j, lo, mid, hi - 1);
    }
}

/// Counts are bounded by the range length; the absolute sum is non-negative and bounds the sum.
pub proof fn lemma_order_bounds(sv: StoresView, seg: Seq<u8>, dl: int, j: int, lo: int, hi: int)
    requires lo <= hi,
    ensures
        order_count(sv, seg, dl, j, lo, hi) <= hi - lo,
        0 <= order_abs(sv, seg, dl, j, lo, hi),
        -order_abs(sv, seg, dl, j, lo, hi) <= order_sum(sv, seg, dl, j, lo, hi) <= order_abs(sv, seg, dl, j, lo, hi),
        order_count(sv, seg, dl, j, lo, hi) == 0 ==> order_sum(sv, seg, dl, j, lo, hi) == 0 && order_abs(sv, seg, dl, j, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_order_bounds(sv, seg, dl, j, lo, hi - 1);
    }
}

/// Rows of a non-qualifying order hit nothing.
pub proof fn lemma_order_not_ok(sv: StoresView, seg: Seq<u8>, dl: int, j: int, lo: int, hi: int)
    requires !order_ok(sv, seg, dl, j),
    ensures
        order_count(sv, seg, dl, j, lo, hi) == 0,
        order_sum(sv, seg, dl, j, lo, hi) == 0,
        order_abs(sv, seg, dl, j, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_order_not_ok(sv, seg, dl, j, lo, hi - 1);
    }
}

// ------------------------------------------------------------------------------------------------ primary keys

/// The values of a key column are pairwise distinct.
pub open spec fn keys_unique(s: Seq<i64>) -> bool {
    forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && #[trigger] s[a] == #[trigger] s[b] ==> a == b
}

/// PRIMARY KEY (o_orderkey) and PRIMARY KEY (c_custkey): the stored key columns of a bound database are unique.
pub proof fn lemma_keys_unique(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures keys_unique(ok(sv)), keys_unique(ck(sv)),
{
    lemma_parts_shape(sv, db);
    let ddb = declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    let kcols = seq![0nat];
    assert(ddb.schema[1].constraints[0] == (Constraint::Key { cols: kcols, primary: true, nulls_distinct: true }));
    assert(ddb.schema[2].constraints[0] == (Constraint::Key { cols: kcols, primary: true, nulls_distinct: true }));
    assert forall|a: int, b: int| 0 <= a < ok(sv).len() && 0 <= b < ok(sv).len() && #[trigger] ok(sv)[a] == #[trigger] ok(sv)[b]
        implies a == b by {
        lemma_orders_row(sv, db, a);
        lemma_orders_row(sv, db, b);
        let ka = key_of(db.tables[1][a], kcols);
        let kb = key_of(db.tables[1][b], kcols);
        assert(ka[0] == db.tables[1][a][0]);
        assert(kb[0] == db.tables[1][b][0]);
        assert(crate::spec::equality::val_not_distinct(ka[0], kb[0]));
        assert(crate::spec::equality::row_not_distinct(ka, kb));
        lemma_primary_key_identifies(ddb, 1, 0, kcols, true, a, b);
    }
    assert forall|a: int, b: int| 0 <= a < ck(sv).len() && 0 <= b < ck(sv).len() && #[trigger] ck(sv)[a] == #[trigger] ck(sv)[b]
        implies a == b by {
        lemma_customer_row(sv, db, a);
        lemma_customer_row(sv, db, b);
        let ka = key_of(db.tables[2][a], kcols);
        let kb = key_of(db.tables[2][b], kcols);
        assert(ka[0] == db.tables[2][a][0]);
        assert(kb[0] == db.tables[2][b][0]);
        assert(crate::spec::equality::val_not_distinct(ka[0], kb[0]));
        assert(crate::spec::equality::row_not_distinct(ka, kb));
        lemma_primary_key_identifies(ddb, 2, 0, kcols, true, a, b);
    }
}

} // verus!
