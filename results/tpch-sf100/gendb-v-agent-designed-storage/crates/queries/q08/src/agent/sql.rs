//! SQL meaning of TPC-H Q8 (statement `query_spec_at(ps)`), part 1: the statement's pieces, the value kinds of the
//! base tables, and the WHERE condition over the joined rows.
//!
//! The FROM list is `part, supplier, lineitem, orders, customer, nation n1, nation n2, region`, evaluated as the
//! left-deep product `jrows(db)` (tables 3, 5, 0, 1, 2, 6, 6, 7). A joined row `x` has 60 values at the offsets
//! part 0, supplier 9, lineitem 16, orders 32, customer 41, n1 49, n2 53, region 57. Every value the statement
//! reads is non-NULL (all columns are NOT NULL), so the WHERE condition is two-valued: `jqual(ps, x)`, stated with
//! value equality (keys are `Val::Int`, names `Val::Text`) and the order date in days.
//!
//! Day numbers (days since 2000-01-01): 1995-01-01 is -1826, 1996-01-01 is -1461, 1996-12-31 is -1096.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::eval::*;
use crate::spec::numeric::*;
use crate::spec::datetime::*;
use crate::spec::relation::*;
use crate::spec::typing::*;
use crate::spec::types::*;
use crate::link::expr::*;
use crate::query::{query_spec_at, param_domain, param_typed};
use crate::schema::schema_spec;

verus! {

// ------------------------------------------------------------------------------------------------ statement pieces

/// Bytes of a text literal (empty for other literals).
pub open spec fn txt(l: Literal) -> Seq<u8> {
    match l {
        Literal::Text(b) => b,
        _ => Seq::empty(),
    }
}

/// `Col(a) = Col(b)`.
pub open spec fn ceq(a: nat, b: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(a), b: Expr::Col(b) }
}

pub open spec fn pand(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

/// `Col(c) op Lit(l)`.
pub open spec fn clit(op: CmpOp, c: nat, l: Literal) -> Pred {
    Pred::Cmp { op, a: Expr::Col(c), b: Expr::Lit(l) }
}

pub open spec fn lit_d95() -> Literal {
    Literal::Date { y: 1995, m: 1, d: 1 }
}

pub open spec fn lit_d96e() -> Literal {
    Literal::Date { y: 1996, m: 12, d: 31 }
}

/// The key conditions `p_partkey = l_partkey .. n1.n_regionkey = r_regionkey`.
pub open spec fn pred_keys6() -> Pred {
    pand(pand(pand(pand(pand(ceq(0, 17), ceq(9, 18)), ceq(16, 32)), ceq(33, 41)), ceq(44, 49)), ceq(51, 57))
}

/// `.. AND r_name = $2 AND s_nationkey = n2.n_nationkey`.
pub open spec fn pred_keys8(ps: Seq<Literal>) -> Pred {
    pand(pand(pred_keys6(), clit(CmpOp::Eq, 58, ps[1])), ceq(12, 53))
}

/// `o_orderdate BETWEEN DATE '1995-01-01' AND DATE '1996-12-31'`.
pub open spec fn pred_date() -> Pred {
    pand(clit(CmpOp::Ge, 36, lit_d95()), clit(CmpOp::Le, 36, lit_d96e()))
}

/// The WHERE condition.
pub open spec fn where_pred(ps: Seq<Literal>) -> Pred {
    pand(pand(pred_keys8(ps), pred_date()), clit(CmpOp::Eq, 4, ps[2]))
}

pub open spec fn qprod(l: Query, r: Query) -> Query {
    Query::Product { left: Box::new(l), right: Box::new(r) }
}

/// The FROM list as a left-deep product.
pub open spec fn from_q() -> Query {
    qprod(qprod(qprod(qprod(qprod(qprod(qprod(Query::Table(3), Query::Table(5)), Query::Table(0)), Query::Table(1)),
        Query::Table(2)), Query::Table(6)), Query::Table(6)), Query::Table(7))
}

pub open spec fn filter_q(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: where_pred(ps), input: Box::new(from_q()) }
}

/// `1 - l_discount` (numeric).
pub open spec fn one_minus_disc() -> Expr {
    Expr::Arith {
        op: ArithOp::Sub,
        kind: NumKind::Numeric,
        a: Box::new(Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }),
        b: Box::new(Expr::Col(22)),
    }
}

/// `l_extendedprice * (1 - l_discount)`.
pub open spec fn volume_e() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(21)), b: Box::new(one_minus_disc()) }
}

/// `EXTRACT(YEAR FROM o_orderdate)`.
pub open spec fn year_e() -> Expr {
    Expr::Call { f: ScalarFn::ExtractYear, args: seq![Expr::Col(36)] }
}

/// The inner SELECT list `o_year, volume, nation`.
pub open spec fn inner_exprs() -> Seq<Expr> {
    seq![year_e(), volume_e(), Expr::Col(54)]
}

pub open spec fn inner_q(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: inner_exprs(), input: Box::new(filter_q(ps)) }
}

/// `CASE WHEN nation = $1 THEN volume ELSE 0 END`.
pub open spec fn case_e(ps: Seq<Literal>) -> Expr {
    Expr::If {
        cond: Box::new(clit(CmpOp::Eq, 2, ps[0])),
        then_e: Box::new(Expr::Col(1)),
        else_e: Box::new(Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 0, kind: IntKind::Int4 })) }),
    }
}

pub open spec fn group_aggs(ps: Seq<Literal>) -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: case_e(ps) }, Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(1) }]
}

pub open spec fn group_keys() -> Seq<Expr> {
    seq![Expr::Col(0)]
}

pub open spec fn group_q(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: group_keys(), aggs: group_aggs(ps), input: Box::new(inner_q(ps)) }
}

/// The outer SELECT list `o_year, SUM(..) / SUM(volume)`.
pub open spec fn outer_exprs() -> Seq<Expr> {
    seq![Expr::Col(0), Expr::Call { f: ScalarFn::DivNumeric, args: seq![Expr::Col(1), Expr::Col(2)] }]
}

pub open spec fn body_q(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: outer_exprs(), input: Box::new(group_q(ps)) }
}

pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 0, desc: false, nulls_first: false }]
}

/// The statement, piece by piece.
pub proof fn lemma_statement(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == body_q(ps),
        query_spec_at(ps).keys == order_keys(),
        query_spec_at(ps).offset == 0,
        query_spec_at(ps).limit is None,
{
}

// ------------------------------------------------------------------------------------------------ parameters

/// The three parameters are text literals whose values are their bytes.
pub proof fn lemma_params(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures
        ps.len() == 3,
        ps[0] == Literal::Text(txt(ps[0])),
        ps[1] == Literal::Text(txt(ps[1])),
        ps[2] == Literal::Text(txt(ps[2])),
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Text(txt(ps[0]))),
        lit_val(ps[1]) == Ok::<Val, SqlError>(Val::Text(txt(ps[1]))),
        lit_val(ps[2]) == Ok::<Val, SqlError>(Val::Text(txt(ps[2]))),
{
}

// ------------------------------------------------------------------------------------------------ dates

pub open spec fn d95() -> int { -1826 }
pub open spec fn d96() -> int { -1461 }
pub open spec fn d96e() -> int { -1096 }

/// The date literals' day numbers.
pub proof fn lemma_date_lits()
    ensures
        lit_val(lit_d95()) == Ok::<Val, SqlError>(Val::Date(d95())),
        lit_val(lit_d96e()) == Ok::<Val, SqlError>(Val::Date(d96e())),
        date_from_civil(1996, 1, 1) == d96(),
{
    assert(date_from_civil(1995, 1, 1) == -1826) by (compute_only);
    assert(date_from_civil(1996, 12, 31) == -1096) by (compute_only);
    assert(date_from_civil(1996, 1, 1) == -1461) by (compute_only);
    assert(date_valid(-1826)) by (compute_only);
    assert(date_valid(-1096)) by (compute_only);
    assert(valid_ymd(1995, 1, 1)) by (compute_only);
    assert(valid_ymd(1996, 12, 31)) by (compute_only);
}

/// The SQL year of a day number (`EXTRACT(YEAR FROM ..)`). Opaque: its civil-calendar arithmetic is revealed only
/// where a year is computed.
#[verifier::opaque]
pub open spec fn year_of(d: int) -> int {
    crate::spec::fns::extract::extract_field(ScalarFn::ExtractYear, civil_from_date(d))
}

/// Every day of `[lo, hi)` has year `y` (decided by evaluation).
pub open spec fn all_year(lo: int, hi: int, y: int) -> bool
    decreases hi - lo,
{
    if lo >= hi { true } else { year_of_raw(lo) == y && all_year(lo + 1, hi, y) }
}

/// `year_of` unfolded (for evaluation by `compute`).
pub open spec fn year_of_raw(d: int) -> int {
    crate::spec::fns::extract::extract_field(ScalarFn::ExtractYear, civil_from_date(d))
}

proof fn lemma_all_year(lo: int, hi: int, y: int, d: int)
    requires all_year(lo, hi, y), lo <= d < hi,
    ensures year_of(d) == y,
    decreases hi - lo,
{
    if lo < d {
        lemma_all_year(lo + 1, hi, y, d);
    } else {
        reveal(year_of);
    }
}

/// Days of 1995 have year 1995, days of 1996 year 1996.
pub proof fn lemma_years(d: int)
    requires d95() <= d <= d96e(),
    ensures year_of(d) == if d < d96() { 1995int } else { 1996int },
{
    assert(all_year(-1826, -1461, 1995)) by (compute_only);
    assert(all_year(-1461, -1095, 1996)) by (compute_only);
    if d < d96() {
        lemma_all_year(-1826, -1461, 1995, d);
    } else {
        lemma_all_year(-1461, -1095, 1996, d);
    }
}

// ------------------------------------------------------------------------------------------------ table typing

/// An `int8` value.
pub open spec fn i8v(v: Val) -> bool {
    v is Int && crate::spec::limits::int8_min() <= v->Int_0 <= crate::spec::limits::int8_max()
}

/// Value kinds of a lineitem row: keys, extended price and discount (numeric(15,2) coefficients).
pub open spec fn li_typed(r: Row) -> bool {
    &&& r.len() == 16
    &&& i8v(r[0]) && i8v(r[1]) && i8v(r[2])
    &&& r[5] is Num && r[5]->Num_scale == 2 && abs(r[5]->Num_coeff) < pow10(15)
    &&& r[6] is Num && r[6]->Num_scale == 2 && abs(r[6]->Num_coeff) < pow10(15)
}

pub open spec fn or_typed(r: Row) -> bool {
    &&& r.len() == 9
    &&& i8v(r[0]) && i8v(r[1])
    &&& r[4] is Date && crate::spec::datetime::date_valid(r[4]->Date_0)
}

pub open spec fn cu_typed(r: Row) -> bool {
    r.len() == 8 && i8v(r[0]) && i8v(r[3])
}

pub open spec fn pa_typed(r: Row) -> bool {
    r.len() == 9 && i8v(r[0]) && r[4] is Text
}

pub open spec fn su_typed(r: Row) -> bool {
    r.len() == 7 && i8v(r[0]) && i8v(r[3])
}

pub open spec fn na_typed(r: Row) -> bool {
    r.len() == 4 && i8v(r[0]) && r[1] is Text && i8v(r[2])
}

pub open spec fn re_typed(r: Row) -> bool {
    r.len() == 3 && i8v(r[0]) && r[1] is Text
}

/// The database facts every lemma here uses.
pub open spec fn db_ok(db: Database) -> bool {
    db.schema == schema_spec() && db_wf(db)
}

/// Value kinds of every table the statement reads.
pub open spec fn tables_typed(db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& forall|i: int| 0 <= i < db.tables[0].len() ==> li_typed(#[trigger] db.tables[0][i])
    &&& forall|i: int| 0 <= i < db.tables[1].len() ==> or_typed(#[trigger] db.tables[1][i])
    &&& forall|i: int| 0 <= i < db.tables[2].len() ==> cu_typed(#[trigger] db.tables[2][i])
    &&& forall|i: int| 0 <= i < db.tables[3].len() ==> pa_typed(#[trigger] db.tables[3][i])
    &&& forall|i: int| 0 <= i < db.tables[5].len() ==> su_typed(#[trigger] db.tables[5][i])
    &&& forall|i: int| 0 <= i < db.tables[6].len() ==> na_typed(#[trigger] db.tables[6][i])
    &&& forall|i: int| 0 <= i < db.tables[7].len() ==> re_typed(#[trigger] db.tables[7][i])
}

proof fn lemma_schema_cols()
    ensures
        schema_spec().len() == 8,
        schema_spec()[0].columns.len() == 16,
        schema_spec()[0].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[0].columns[1] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[0].columns[2] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[0].columns[5] == (Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }),
        schema_spec()[0].columns[6] == (Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }),
        schema_spec()[1].columns.len() == 9,
        schema_spec()[1].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[1].columns[1] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[1].columns[4] == (Column { ty: SqlType::Date, nullable: false }),
        schema_spec()[2].columns.len() == 8,
        schema_spec()[2].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[2].columns[3] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[3].columns.len() == 9,
        schema_spec()[3].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[3].columns[4] == (Column { ty: SqlType::Text, nullable: false }),
        schema_spec()[5].columns.len() == 7,
        schema_spec()[5].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[5].columns[3] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[6].columns.len() == 4,
        schema_spec()[6].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[6].columns[1] == (Column { ty: SqlType::Text, nullable: false }),
        schema_spec()[6].columns[2] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[7].columns.len() == 3,
        schema_spec()[7].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[7].columns[1] == (Column { ty: SqlType::Text, nullable: false }),
{
    assert(schema_spec().len() == 8) by (compute_only);
    assert(schema_spec()[0].columns.len() == 16) by (compute_only);
    assert(schema_spec()[0].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute_only);
    assert(schema_spec()[0].columns[1] == (Column { ty: SqlType::Int8, nullable: false })) by (compute_only);
    assert(schema_spec()[0].columns[2] == (Column { ty: SqlType::Int8, nullable: false })) by (compute_only);
    assert(schema_spec()[0].columns[5] == (Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false })) by (compute_only);
    assert(schema_spec()[0].columns[6] == (Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false })) by (compute_only);
    assert(schema_spec()[1].columns.len() == 9) by (compute_only);
    assert(schema_spec()[1].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute_only);
    assert(schema_spec()[1].columns[1] == (Column { ty: SqlType::Int8, nullable: false })) by (compute_only);
    assert(schema_spec()[1].columns[4] == (Column { ty: SqlType::Date, nullable: false })) by (compute_only);
    assert(schema_spec()[2].columns.len() == 8) by (compute_only);
    assert(schema_spec()[2].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute_only);
    assert(schema_spec()[2].columns[3] == (Column { ty: SqlType::Int8, nullable: false })) by (compute_only);
    assert(schema_spec()[3].columns.len() == 9) by (compute_only);
    assert(schema_spec()[3].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute_only);
    assert(schema_spec()[3].columns[4] == (Column { ty: SqlType::Text, nullable: false })) by (compute_only);
    assert(schema_spec()[5].columns.len() == 7) by (compute_only);
    assert(schema_spec()[5].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute_only);
    assert(schema_spec()[5].columns[3] == (Column { ty: SqlType::Int8, nullable: false })) by (compute_only);
    assert(schema_spec()[6].columns.len() == 4) by (compute_only);
    assert(schema_spec()[6].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute_only);
    assert(schema_spec()[6].columns[1] == (Column { ty: SqlType::Text, nullable: false })) by (compute_only);
    assert(schema_spec()[6].columns[2] == (Column { ty: SqlType::Int8, nullable: false })) by (compute_only);
    assert(schema_spec()[7].columns.len() == 3) by (compute_only);
    assert(schema_spec()[7].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute_only);
    assert(schema_spec()[7].columns[1] == (Column { ty: SqlType::Text, nullable: false })) by (compute_only);
}

pub proof fn lemma_tables_typed(db: Database)
    requires db_ok(db),
    ensures tables_typed(db),
{
    lemma_schema_cols();
    let s = schema_spec();
    assert(db.tables.len() == 8);
    assert forall|i: int| 0 <= i < db.tables[0].len() implies li_typed(#[trigger] db.tables[0][i]) by {
        let r = db.tables[0][i];
        assert(row_in_table(r, s[0]));
        assert(value_in_column(r[0], s[0].columns[0]));
        assert(value_in_column(r[1], s[0].columns[1]));
        assert(value_in_column(r[2], s[0].columns[2]));
        assert(value_in_column(r[5], s[0].columns[5]));
        assert(value_in_column(r[6], s[0].columns[6]));
    }
    assert forall|i: int| 0 <= i < db.tables[1].len() implies or_typed(#[trigger] db.tables[1][i]) by {
        let r = db.tables[1][i];
        assert(row_in_table(r, s[1]));
        assert(value_in_column(r[0], s[1].columns[0]));
        assert(value_in_column(r[1], s[1].columns[1]));
        assert(value_in_column(r[4], s[1].columns[4]));
    }
    assert forall|i: int| 0 <= i < db.tables[2].len() implies cu_typed(#[trigger] db.tables[2][i]) by {
        let r = db.tables[2][i];
        assert(row_in_table(r, s[2]));
        assert(value_in_column(r[0], s[2].columns[0]));
        assert(value_in_column(r[3], s[2].columns[3]));
    }
    assert forall|i: int| 0 <= i < db.tables[3].len() implies pa_typed(#[trigger] db.tables[3][i]) by {
        let r = db.tables[3][i];
        assert(row_in_table(r, s[3]));
        assert(value_in_column(r[0], s[3].columns[0]));
        assert(value_in_column(r[4], s[3].columns[4]));
    }
    assert forall|i: int| 0 <= i < db.tables[5].len() implies su_typed(#[trigger] db.tables[5][i]) by {
        let r = db.tables[5][i];
        assert(row_in_table(r, s[5]));
        assert(value_in_column(r[0], s[5].columns[0]));
        assert(value_in_column(r[3], s[5].columns[3]));
    }
    assert forall|i: int| 0 <= i < db.tables[6].len() implies na_typed(#[trigger] db.tables[6][i]) by {
        let r = db.tables[6][i];
        assert(row_in_table(r, s[6]));
        assert(value_in_column(r[0], s[6].columns[0]));
        assert(value_in_column(r[1], s[6].columns[1]));
        assert(value_in_column(r[2], s[6].columns[2]));
    }
    assert forall|i: int| 0 <= i < db.tables[7].len() implies re_typed(#[trigger] db.tables[7][i]) by {
        let r = db.tables[7][i];
        assert(row_in_table(r, s[7]));
        assert(value_in_column(r[0], s[7].columns[0]));
        assert(value_in_column(r[1], s[7].columns[1]));
    }
}

// ------------------------------------------------------------------------------------------------ joined rows

/// The joined relation of the FROM list (left-deep product, FROM order).
pub open spec fn jrows(db: Database) -> Seq<Row> {
    let t = db.tables;
    product_rows(product_rows(product_rows(product_rows(product_rows(product_rows(product_rows(t[3], t[5]), t[0]),
        t[1]), t[2]), t[6]), t[6]), t[7])
}

/// The joined row of one row of each FROM input.
pub open spec fn join8(p: Row, s: Row, l: Row, o: Row, c: Row, n1: Row, n2: Row, r: Row) -> Row {
    p + s + l + o + c + n1 + n2 + r
}

/// The values of a joined row the statement reads, by FROM input.
pub open spec fn jparts_typed(p: Row, s: Row, l: Row, o: Row, c: Row, n1: Row, n2: Row, r: Row) -> bool {
    pa_typed(p) && su_typed(s) && li_typed(l) && or_typed(o) && cu_typed(c) && na_typed(n1) && na_typed(n2) && re_typed(r)
}

/// A joined row is one row of each FROM input, each of its table's value kinds.
pub open spec fn jrow_ok(x: Row) -> bool {
    exists|p: Row, s: Row, l: Row, o: Row, c: Row, n1: Row, n2: Row, r: Row|
        #[trigger] join8(p, s, l, o, c, n1, n2, r) == x && jparts_typed(p, s, l, o, c, n1, n2, r)
}

/// Positions of a joined row.
pub proof fn lemma_join8_at(p: Row, s: Row, l: Row, o: Row, c: Row, n1: Row, n2: Row, r: Row)
    requires jparts_typed(p, s, l, o, c, n1, n2, r),
    ensures ({
        let x = join8(p, s, l, o, c, n1, n2, r);
        &&& x.len() == 60
        &&& x[0] == p[0] && x[4] == p[4]
        &&& x[9] == s[0] && x[12] == s[3]
        &&& x[16] == l[0] && x[17] == l[1] && x[18] == l[2] && x[21] == l[5] && x[22] == l[6]
        &&& x[32] == o[0] && x[33] == o[1] && x[36] == o[4]
        &&& x[41] == c[0] && x[44] == c[3]
        &&& x[49] == n1[0] && x[51] == n1[2]
        &&& x[53] == n2[0] && x[54] == n2[1]
        &&& x[57] == r[0] && x[58] == r[1]
    }),
{
}

/// Every row of a product is a left row followed by a right row.
proof fn lemma_product_elem(a: Seq<Row>, b: Seq<Row>, k: int)
    requires 0 <= k < product_rows(a, b).len(),
    ensures exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && product_rows(a, b)[k] == #[trigger] a[i] + #[trigger] b[j],
{
    crate::bridge::relation::lemma_product_rows_elems(a, b);
    assert(crate::bridge::relation::is_concat(product_rows(a, b)[k], a, b));
}

/// Every joined row is `jrow_ok`.
pub proof fn lemma_jrows_ok(db: Database, k: int)
    requires tables_typed(db), 0 <= k < jrows(db).len(),
    ensures jrow_ok(jrows(db)[k]),
{
    let t = db.tables;
    let j1 = product_rows(t[3], t[5]);
    let j2 = product_rows(j1, t[0]);
    let j3 = product_rows(j2, t[1]);
    let j4 = product_rows(j3, t[2]);
    let j5 = product_rows(j4, t[6]);
    let j6 = product_rows(j5, t[6]);
    let j7 = product_rows(j6, t[7]);
    assert(j7 == jrows(db));
    lemma_product_elem(j6, t[7], k);
    let (i7, r7) = choose|i: int, j: int| 0 <= i < j6.len() && 0 <= j < t[7].len() && j7[k] == #[trigger] j6[i] + #[trigger] t[7][j];
    lemma_product_elem(j5, t[6], i7);
    let (i6, r6) = choose|i: int, j: int| 0 <= i < j5.len() && 0 <= j < t[6].len() && j6[i7] == #[trigger] j5[i] + #[trigger] t[6][j];
    lemma_product_elem(j4, t[6], i6);
    let (i5, r5) = choose|i: int, j: int| 0 <= i < j4.len() && 0 <= j < t[6].len() && j5[i6] == #[trigger] j4[i] + #[trigger] t[6][j];
    lemma_product_elem(j3, t[2], i5);
    let (i4, r4) = choose|i: int, j: int| 0 <= i < j3.len() && 0 <= j < t[2].len() && j4[i5] == #[trigger] j3[i] + #[trigger] t[2][j];
    lemma_product_elem(j2, t[1], i4);
    let (i3, r3) = choose|i: int, j: int| 0 <= i < j2.len() && 0 <= j < t[1].len() && j3[i4] == #[trigger] j2[i] + #[trigger] t[1][j];
    lemma_product_elem(j1, t[0], i3);
    let (i2, r2) = choose|i: int, j: int| 0 <= i < j1.len() && 0 <= j < t[0].len() && j2[i3] == #[trigger] j1[i] + #[trigger] t[0][j];
    lemma_product_elem(t[3], t[5], i2);
    let (i1, r1) = choose|i: int, j: int| 0 <= i < t[3].len() && 0 <= j < t[5].len() && j1[i2] == #[trigger] t[3][i] + #[trigger] t[5][j];
    let (p, s, l, o, c, n1, n2, r) = (t[3][i1], t[5][r1], t[0][r2], t[1][r3], t[2][r4], t[6][r5], t[6][r6], t[7][r7]);
    assert(join8(p, s, l, o, c, n1, n2, r) == jrows(db)[k]);
    assert(jparts_typed(p, s, l, o, c, n1, n2, r));
}

// ------------------------------------------------------------------------------------------------ the WHERE condition

/// The day number of a date value (0 otherwise).
pub open spec fn dval(v: Val) -> int {
    match v {
        Val::Date(d) => d,
        _ => 0,
    }
}

/// The WHERE condition on a joined row (two-valued).
pub open spec fn jqual(ps: Seq<Literal>, x: Row) -> bool {
    &&& x[0] == x[17]
    &&& x[9] == x[18]
    &&& x[16] == x[32]
    &&& x[33] == x[41]
    &&& x[44] == x[49]
    &&& x[51] == x[57]
    &&& x[58] == Val::Text(txt(ps[1]))
    &&& x[12] == x[53]
    &&& d95() <= dval(x[36]) <= d96e()
    &&& x[4] == Val::Text(txt(ps[2]))
}

/// `Col(a) = Col(b)` on two integer values is their equality.
pub proof fn lemma_ceq_row(db: Database, x: Row, a: nat, b: nat)
    requires a < x.len(), b < x.len(), x[a as int] is Int, x[b as int] is Int,
    ensures eval_pred(db, x, ceq(a, b)) == Ok::<Truth, SqlError>(truth_of(x[a as int] == x[b as int])),
{
    let (va, vb) = (x[a as int], x[b as int]);
    lemma_expr_col(db, x, a);
    lemma_expr_col(db, x, b);
    lemma_compare_int(va->Int_0, vb->Int_0);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(a), Expr::Col(b), va, vb, va->Int_0, vb->Int_0);
}

/// `Col(c) = Lit(Text(t))` on a text value is byte equality.
pub proof fn lemma_ctext_row(db: Database, x: Row, c: nat, l: Literal)
    requires c < x.len(), x[c as int] is Text, l is Text,
    ensures eval_pred(db, x, clit(CmpOp::Eq, c, l)) == Ok::<Truth, SqlError>(truth_of(x[c as int] == Val::Text(txt(l)))),
{
    lemma_expr_col(db, x, c);
    lemma_expr_text(db, x, txt(l));
    assert(Expr::Lit(l) == Expr::Lit(Literal::Text(txt(l))));
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(c), Expr::Lit(l), x[c as int]->Text_0, txt(l));
}

/// The order-date window on a date value.
proof fn lemma_date_row(db: Database, x: Row)
    requires 36 < x.len(), x[36] is Date,
    ensures eval_pred(db, x, pred_date()) == Ok::<Truth, SqlError>(truth_of(d95() <= dval(x[36]) <= d96e())),
{
    hide(eval_expr);
    hide(eval_pred);
    let d = dval(x[36]);
    lemma_date_lits();
    lemma_expr_col(db, x, 36);
    crate::link::expr::lemma_compare_date(d, d95());
    crate::link::expr::lemma_compare_date(d, d96e());
    assert(eval_expr(db, x, Expr::Lit(lit_d95())) == lit_val(lit_d95())) by { reveal(eval_expr); }
    assert(eval_expr(db, x, Expr::Lit(lit_d96e())) == lit_val(lit_d96e())) by { reveal(eval_expr); }
    lemma_pred_cmp(db, x, CmpOp::Ge, Expr::Col(36), Expr::Lit(lit_d95()), x[36], Val::Date(d95()), d, d95());
    lemma_pred_cmp(db, x, CmpOp::Le, Expr::Col(36), Expr::Lit(lit_d96e()), x[36], Val::Date(d96e()), d, d96e());
    lemma_pred_and(db, x, clit(CmpOp::Ge, 36, lit_d95()), clit(CmpOp::Le, 36, lit_d96e()), d >= d95(), d <= d96e());
}

/// The WHERE condition evaluates (without error) to `jqual` on every joined row.
pub proof fn lemma_where_row(db: Database, ps: Seq<Literal>, x: Row)
    requires param_domain(ps), jrow_ok(x),
    ensures eval_pred(db, x, where_pred(ps)) == Ok::<Truth, SqlError>(truth_of(jqual(ps, x))),
{
    hide(eval_expr);
    hide(eval_pred);
    lemma_params(ps);
    let (p, s, l, o, c, n1, n2, r) = choose|p: Row, s: Row, l: Row, o: Row, c: Row, n1: Row, n2: Row, r: Row|
        #[trigger] join8(p, s, l, o, c, n1, n2, r) == x && jparts_typed(p, s, l, o, c, n1, n2, r);
    lemma_join8_at(p, s, l, o, c, n1, n2, r);
    lemma_ceq_row(db, x, 0, 17);
    lemma_ceq_row(db, x, 9, 18);
    lemma_ceq_row(db, x, 16, 32);
    lemma_ceq_row(db, x, 33, 41);
    lemma_ceq_row(db, x, 44, 49);
    lemma_ceq_row(db, x, 51, 57);
    lemma_ceq_row(db, x, 12, 53);
    lemma_ctext_row(db, x, 58, ps[1]);
    lemma_ctext_row(db, x, 4, ps[2]);
    lemma_date_row(db, x);
    let b1 = x[0] == x[17];
    let b2 = x[9] == x[18];
    let b3 = x[16] == x[32];
    let b4 = x[33] == x[41];
    let b5 = x[44] == x[49];
    let b6 = x[51] == x[57];
    let b7 = x[58] == Val::Text(txt(ps[1]));
    let b8 = x[12] == x[53];
    let b9 = d95() <= dval(x[36]) <= d96e();
    let b10 = x[4] == Val::Text(txt(ps[2]));
    lemma_pred_and(db, x, ceq(0, 17), ceq(9, 18), b1, b2);
    let q2 = pand(ceq(0, 17), ceq(9, 18));
    lemma_pred_and(db, x, q2, ceq(16, 32), b1 && b2, b3);
    let q3 = pand(q2, ceq(16, 32));
    lemma_pred_and(db, x, q3, ceq(33, 41), b1 && b2 && b3, b4);
    let q4 = pand(q3, ceq(33, 41));
    lemma_pred_and(db, x, q4, ceq(44, 49), b1 && b2 && b3 && b4, b5);
    let q5 = pand(q4, ceq(44, 49));
    lemma_pred_and(db, x, q5, ceq(51, 57), b1 && b2 && b3 && b4 && b5, b6);
    let q6 = pand(q5, ceq(51, 57));
    assert(q6 == pred_keys6());
    let c6 = b1 && b2 && b3 && b4 && b5 && b6;
    lemma_pred_and(db, x, q6, clit(CmpOp::Eq, 58, ps[1]), c6, b7);
    let q7 = pand(q6, clit(CmpOp::Eq, 58, ps[1]));
    lemma_pred_and(db, x, q7, ceq(12, 53), c6 && b7, b8);
    assert(pand(q7, ceq(12, 53)) == pred_keys8(ps));
    lemma_pred_and(db, x, pred_keys8(ps), pred_date(), c6 && b7 && b8, b9);
    lemma_pred_and(db, x, pand(pred_keys8(ps), pred_date()), clit(CmpOp::Eq, 4, ps[2]), c6 && b7 && b8 && b9, b10);
}

// ------------------------------------------------------------------------------------------------ FROM and WHERE

/// One unfolding step: a product of two evaluated inputs.
proof fn lemma_eval_qprod(db: Database, l: Query, r: Query, a: Seq<Row>, b: Seq<Row>)
    requires
        eval_query(db, Seq::empty(), l) == Ok::<Relation, SqlError>(a),
        eval_query(db, Seq::empty(), r) == Ok::<Relation, SqlError>(b),
    ensures eval_query(db, Seq::empty(), qprod(l, r)) == Ok::<Relation, SqlError>(product_rows(a, b)),
{
}

/// One unfolding step: a base table.
proof fn lemma_eval_table(db: Database, t: nat)
    requires t < db.tables.len(),
    ensures eval_query(db, Seq::empty(), Query::Table(t)) == Ok::<Relation, SqlError>(db.tables[t as int]),
{
}

/// The FROM list evaluates to the joined rows.
pub proof fn lemma_from(db: Database)
    requires db.tables.len() == 8,
    ensures eval_query(db, Seq::empty(), from_q()) == Ok::<Relation, SqlError>(jrows(db)),
{
    hide(eval_query);
    let t = db.tables;
    lemma_eval_table(db, 0);
    lemma_eval_table(db, 1);
    lemma_eval_table(db, 2);
    lemma_eval_table(db, 3);
    lemma_eval_table(db, 5);
    lemma_eval_table(db, 6);
    lemma_eval_table(db, 7);
    let q1 = qprod(Query::Table(3), Query::Table(5));
    lemma_eval_qprod(db, Query::Table(3), Query::Table(5), t[3], t[5]);
    let j1 = product_rows(t[3], t[5]);
    let q2 = qprod(q1, Query::Table(0));
    lemma_eval_qprod(db, q1, Query::Table(0), j1, t[0]);
    let j2 = product_rows(j1, t[0]);
    let q3 = qprod(q2, Query::Table(1));
    lemma_eval_qprod(db, q2, Query::Table(1), j2, t[1]);
    let j3 = product_rows(j2, t[1]);
    let q4 = qprod(q3, Query::Table(2));
    lemma_eval_qprod(db, q3, Query::Table(2), j3, t[2]);
    let j4 = product_rows(j3, t[2]);
    let q5 = qprod(q4, Query::Table(6));
    lemma_eval_qprod(db, q4, Query::Table(6), j4, t[6]);
    let j5 = product_rows(j4, t[6]);
    let q6 = qprod(q5, Query::Table(6));
    lemma_eval_qprod(db, q5, Query::Table(6), j5, t[6]);
    let j6 = product_rows(j5, t[6]);
    lemma_eval_qprod(db, q6, Query::Table(7), j6, t[7]);
}

/// The qualifying joined rows.
pub open spec fn kept(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    crate::link::join::keep(jrows(db), |x: Row| jqual(ps, x))
}

/// The WHERE clause keeps the joined rows satisfying `jqual`.
pub proof fn lemma_filter(db: Database, ps: Seq<Literal>)
    requires db_ok(db), param_domain(ps),
    ensures eval_query(db, Seq::empty(), filter_q(ps)) == Ok::<Relation, SqlError>(kept(db, ps)),
{
    hide(eval_query);
    hide(eval_pred);
    lemma_tables_typed(db);
    lemma_from(db);
    let rows = jrows(db);
    let all = |x: Row| true;
    let q = |x: Row| jqual(ps, x);
    crate::link::join::lemma_keep_all(rows, all);
    assert forall|i: int| 0 <= i < rows.len() && all(#[trigger] rows[i]) implies
        eval_pred(db, rows[i], where_pred(ps)) == Ok::<Truth, SqlError>(truth_of(q(rows[i]))) by {
        lemma_jrows_ok(db, i);
        lemma_where_row(db, ps, rows[i]);
    }
    crate::link::join::lemma_eval_filter(db, from_q(), rows, all, where_pred(ps), q, q);
}

// ------------------------------------------------------------------------------------------------ the inner SELECT

/// `l_extendedprice * (1 - l_discount)` as a scale-4 coefficient.
pub open spec fn vol_of(x: Row) -> int {
    ival(x[21]) * (100 - ival(x[22]))
}

/// The inner row `o_year, volume, nation` of a joined row.
pub open spec fn inner_row(x: Row) -> Row {
    seq![Val::Num { coeff: year_of(dval(x[36])), scale: 0 }, Val::Num { coeff: vol_of(x), scale: 4 }, x[54]]
}

proof fn lemma_pow10_small()
    ensures pow10(0) == 1, pow10(1) == 10, pow10(2) == 100, pow10(15) == 1_000_000_000_000_000,
        pow10(16) == 10_000_000_000_000_000,
{
    assert(pow10(0) == 1) by (compute_only);
    assert(pow10(1) == 10) by (compute_only);
    assert(pow10(2) == 100) by (compute_only);
    assert(pow10(15) == 1_000_000_000_000_000) by (compute_only);
    assert(pow10(16) == 10_000_000_000_000_000) by (compute_only);
}

/// `CAST(v AS numeric)` of a small int4 literal (one unfolding step).
pub proof fn lemma_cast_int_lit(db: Database, env: Row, v: int)
    requires -100 <= v <= 100,
    ensures
        eval_expr(db, env, Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v, kind: IntKind::Int4 })) })
            == Ok::<Val, SqlError>(Val::Num { coeff: v, scale: 0 }),
{
    hide(eval_expr);
    let l = Literal::Int { v, kind: IntKind::Int4 };
    assert(int_in_range(IntKind::Int4, v));
    assert(lit_val(l) == Ok::<Val, SqlError>(Val::Int(v)));
    lemma_expr_lit(db, env, l);
    lemma_expr_cast(db, env, CastOp::IntToNumeric, Expr::Lit(l));
}

/// One unfolding step: a literal.
pub proof fn lemma_expr_lit(db: Database, env: Row, l: Literal)
    ensures eval_expr(db, env, Expr::Lit(l)) == lit_val(l),
{
}

/// One unfolding step: a cast of an evaluated operand.
pub proof fn lemma_expr_cast(db: Database, env: Row, op: CastOp, a: Expr)
    ensures
        eval_expr(db, env, Expr::Cast { cast: op, arg: Box::new(a) }) == match eval_expr(db, env, a) {
            Err(err) => Err(err),
            Ok(v) => cast(op, v),
        },
{
}

/// One unfolding step: a list of expressions is the collection of their outcomes.
pub proof fn lemma_eval_exprs_def(db: Database, env: Row, es: Seq<Expr>)
    ensures eval_exprs(db, env, es) == collect(expr_results(db, env, es)),
{
}

/// One unfolding step: a scalar function call.
pub proof fn lemma_expr_call(db: Database, env: Row, f: ScalarFn, args: Seq<Expr>)
    ensures
        eval_expr(db, env, Expr::Call { f, args }) == match eval_exprs(db, env, args) {
            Err(err) => Err(err),
            Ok(vs) => crate::spec::fns::apply_fn(f, vs),
        },
{
}

/// `1 - l_discount` on a joined row.
proof fn lemma_one_minus_disc(db: Database, x: Row, d: int)
    requires x.len() == 60, x[22] == (Val::Num { coeff: d, scale: 2 }), abs(d) < pow10(15),
    ensures
        eval_expr(db, x, one_minus_disc()) == Ok::<Val, SqlError>(Val::Num { coeff: 100 - d, scale: 2 }),
        abs(100 - d) < pow10(16),
{
    hide(eval_expr);
    hide(pow10);
    lemma_pow10_small();
    let one = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) };
    lemma_cast_int_lit(db, x, 1);
    lemma_expr_col(db, x, 22);
    assert(max_nat(0, 2) == 2);
    assert(abs(1) < pow10(1));
    crate::link::query::lemma_node_add(db, x, ArithOp::Sub, one, Expr::Col(22), 1, 0, 1, d, 2, 15, 2, 100, 1, 16);
    assert(1 * 100 - d * 1 == 100 - d);
}

/// The volume on a joined row.
proof fn lemma_volume(db: Database, x: Row)
    requires
        x.len() == 60,
        x[21] is Num, x[21]->Num_scale == 2, abs(x[21]->Num_coeff) < pow10(15),
        x[22] is Num, x[22]->Num_scale == 2, abs(x[22]->Num_coeff) < pow10(15),
    ensures
        eval_expr(db, x, volume_e()) == Ok::<Val, SqlError>(Val::Num { coeff: vol_of(x), scale: 4 }),
        abs(vol_of(x)) < pow10(31),
{
    hide(eval_expr);
    hide(pow10);
    let d = ival(x[22]);
    assert(x[22] == Val::Num { coeff: d, scale: 2 });
    lemma_one_minus_disc(db, x, d);
    lemma_expr_col(db, x, 21);
    let p = ival(x[21]);
    assert(x[21] == Val::Num { coeff: p, scale: 2 });
    crate::link::query::lemma_node_mul(db, x, Expr::Col(21), one_minus_disc(), p, 2, 15, 100 - d, 2, 16);
}

/// The year on a joined row.
proof fn lemma_year(db: Database, x: Row)
    requires x.len() == 60, x[36] is Date,
    ensures eval_expr(db, x, year_e()) == Ok::<Val, SqlError>(Val::Num { coeff: year_of(dval(x[36])), scale: 0 }),
{
    hide(eval_expr);
    hide(eval_exprs);
    lemma_expr_col(db, x, 36);
    let args = seq![Expr::Col(36)];
    lemma_exprs1(db, x, Expr::Col(36), x[36]);
    lemma_expr_call(db, x, ScalarFn::ExtractYear, args);
    reveal(year_of);
}

/// A one-element expression list.
pub proof fn lemma_exprs1(db: Database, env: Row, a: Expr, va: Val)
    requires eval_expr(db, env, a) == Ok::<Val, SqlError>(va),
    ensures eval_exprs(db, env, seq![a]) == Ok::<Row, SqlError>(seq![va]),
{
    hide(eval_expr);
    hide(eval_exprs);
    let es = seq![a];
    crate::spec::eval::lemma_eval_exprs_empty(db, env);
    crate::spec::eval::lemma_eval_exprs_step(db, env, es);
    assert(es.drop_last() =~= Seq::<Expr>::empty());
    assert(Seq::<Val>::empty().push(va) =~= seq![va]);
}

/// A two-element expression list.
pub proof fn lemma_exprs2(db: Database, env: Row, a: Expr, b: Expr, va: Val, vb: Val)
    requires
        eval_expr(db, env, a) == Ok::<Val, SqlError>(va),
        eval_expr(db, env, b) == Ok::<Val, SqlError>(vb),
    ensures eval_exprs(db, env, seq![a, b]) == Ok::<Row, SqlError>(seq![va, vb]),
{
    hide(eval_expr);
    hide(eval_exprs);
    let es = seq![a, b];
    lemma_exprs1(db, env, a, va);
    crate::spec::eval::lemma_eval_exprs_step(db, env, es);
    assert(es.drop_last() =~= seq![a]);
    assert(seq![va].push(vb) =~= seq![va, vb]);
}

/// A three-element expression list.
pub proof fn lemma_exprs3(db: Database, env: Row, a: Expr, b: Expr, c: Expr, va: Val, vb: Val, vc: Val)
    requires
        eval_expr(db, env, a) == Ok::<Val, SqlError>(va),
        eval_expr(db, env, b) == Ok::<Val, SqlError>(vb),
        eval_expr(db, env, c) == Ok::<Val, SqlError>(vc),
    ensures eval_exprs(db, env, seq![a, b, c]) == Ok::<Row, SqlError>(seq![va, vb, vc]),
{
    hide(eval_expr);
    hide(eval_exprs);
    let es = seq![a, b, c];
    lemma_exprs2(db, env, a, b, va, vb);
    crate::spec::eval::lemma_eval_exprs_step(db, env, es);
    assert(es.drop_last() =~= seq![a, b]);
    assert(seq![va, vb].push(vc) =~= seq![va, vb, vc]);
}

/// The value kinds of a joined row that the inner SELECT reads.
pub open spec fn inner_typed(x: Row) -> bool {
    &&& x.len() == 60
    &&& x[21] is Num && x[21]->Num_scale == 2 && abs(x[21]->Num_coeff) < pow10(15)
    &&& x[22] is Num && x[22]->Num_scale == 2 && abs(x[22]->Num_coeff) < pow10(15)
    &&& x[36] is Date
    &&& x[54] is Text
}

pub proof fn lemma_jrow_inner_typed(x: Row)
    requires jrow_ok(x),
    ensures inner_typed(x),
{
    let (p, s, l, o, c, n1, n2, r) = choose|p: Row, s: Row, l: Row, o: Row, c: Row, n1: Row, n2: Row, r: Row|
        #[trigger] join8(p, s, l, o, c, n1, n2, r) == x && jparts_typed(p, s, l, o, c, n1, n2, r);
    lemma_join8_at(p, s, l, o, c, n1, n2, r);
}

/// The inner SELECT list on a joined row.
pub proof fn lemma_inner_row(db: Database, x: Row)
    requires jrow_ok(x),
    ensures eval_exprs(db, x, inner_exprs()) == Ok::<Row, SqlError>(inner_row(x)),
{
    hide(eval_expr);
    hide(eval_exprs);
    hide(pow10);
    lemma_jrow_inner_typed(x);
    lemma_year(db, x);
    lemma_volume(db, x);
    lemma_expr_col(db, x, 54);
    lemma_exprs3(db, x, year_e(), volume_e(), Expr::Col(54), Val::Num { coeff: year_of(dval(x[36])), scale: 0 },
        Val::Num { coeff: vol_of(x), scale: 4 }, x[54]);
}

/// The rows of the inner SELECT.
pub open spec fn inner_rows(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    kept(db, ps).map_values(|x: Row| inner_row(x))
}

/// Every qualifying joined row is a joined row (`jrow_ok`) satisfying `jqual`.
pub proof fn lemma_kept_rows(db: Database, ps: Seq<Literal>)
    requires db_ok(db),
    ensures forall|i: int| 0 <= i < kept(db, ps).len() ==> jrow_ok(#[trigger] kept(db, ps)[i]) && jqual(ps, kept(db, ps)[i]),
{
    lemma_tables_typed(db);
    let rows = jrows(db);
    let q = |x: Row| jqual(ps, x);
    crate::link::join::lemma_keep_members(rows, q);
    assert forall|i: int| 0 <= i < kept(db, ps).len() implies jrow_ok(#[trigger] kept(db, ps)[i]) && jqual(ps, kept(db, ps)[i]) by {
        let k = kept(db, ps)[i];
        assert(rows.contains(k) && q(k));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == k;
        lemma_jrows_ok(db, m);
    }
}

/// The inner SELECT evaluates to `inner_rows`.
pub proof fn lemma_inner(db: Database, ps: Seq<Literal>)
    requires db_ok(db), param_domain(ps),
    ensures eval_query(db, Seq::empty(), inner_q(ps)) == Ok::<Relation, SqlError>(inner_rows(db, ps)),
{
    hide(eval_query);
    hide(eval_exprs);
    lemma_filter(db, ps);
    lemma_kept_rows(db, ps);
    let k = kept(db, ps);
    let ctx = Seq::<Val>::empty();
    crate::exec::relational::domain::lemma_eval_project(db, ctx, inner_exprs(), Box::new(filter_q(ps)));
    let rs = crate::exec::relational::domain::project_results(db, ctx, k, inner_exprs());
    let vs = inner_rows(db, ps);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(vs[i]) by {
        assert(ctx + k[i] =~= k[i]);
        lemma_inner_row(db, k[i]);
    }
    crate::bridge::collect::lemma_collect_all(rs, vs);
}

} // verus!
