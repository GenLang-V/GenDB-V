//! The Q5 normal form.
//!
//! - The statement's AST pieces (copies of the nodes of `crate::query::query_spec_at`) and its shape.
//! - `Prm`: the bound parameters as values: region name bytes, the first day `lo` (days since 2000-01-01) and the
//!   exclusive end `hi` of the date window as a timestamp (microseconds since 2000-01-01).
//! - `Rels`: the stored relations the query reads (lineitem, orders, customer, supplier, nation, region), each a
//!   projection of its table on the stored columns; `xs_of` is their left-deep product in FROM order
//!   (customer, orders, lineitem, supplier, nation, region), 8 + 7 + 15 + 7 + 4 + 3 = 44 columns per row.
//! - `q5_g`: the accumulator normal form (`link::query::QuerySpec`) over those 44-column rows.
//! - `line_mult`: how many joined rows of group `k` one lineitem row takes part in, as nested sums over the other
//!   relations (the algebra layer proves the group accumulators are sums of `line_mult` over lineitem rows).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::datetime::*;
use crate::spec::relation::*;
use crate::link::query::*;
use crate::link::join::*;

verus! {

// ------------------------------------------------------------------------------------------- statement pieces

/// `l_extendedprice * (1 - l_discount)` over the full joined row (positions 22 and 23).
pub open spec fn rev_expr() -> Expr {
    Expr::Arith {
        op: ArithOp::Mul,
        kind: NumKind::Numeric,
        a: Box::new(Expr::Col(22)),
        b: Box::new(one_minus_disc()),
    }
}

/// `1 - l_discount` (the literal 1 is an int4 cast to numeric).
pub open spec fn one_minus_disc() -> Expr {
    Expr::Arith {
        op: ArithOp::Sub,
        kind: NumKind::Numeric,
        a: Box::new(one_num()),
        b: Box::new(Expr::Col(23)),
    }
}

/// `CAST(1 AS numeric)`.
pub open spec fn one_num() -> Expr {
    Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }
}

/// `SUM(l_extendedprice * (1 - l_discount))`.
pub open spec fn q5_agg() -> Agg {
    Agg::Sum { kind: NumKind::Numeric, arg: rev_expr() }
}

/// `Col(a) = Col(b)`.
pub open spec fn eq_cols(a: nat, b: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(a), b: Expr::Col(b) }
}

pub open spec fn and_p(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

/// The six join equalities, in statement order.
pub open spec fn join_pred() -> Pred {
    and_p(and_p(and_p(and_p(and_p(eq_cols(0, 9), eq_cols(17, 8)), eq_cols(19, 33)), eq_cols(3, 36)), eq_cols(36, 40)),
        eq_cols(42, 44))
}

/// `r_name = $1`.
pub open spec fn name_pred(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(45), b: Expr::Lit(ps[0]) }
}

/// `o_orderdate >= $2`.
pub open spec fn date_ge_pred(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(12), b: Expr::Lit(ps[1]) }
}

/// `$2 + INTERVAL '1' YEAR` (a timestamp).
pub open spec fn hi_expr(ps: Seq<Literal>) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(ps[1])) }),
        months: 12i32,
        days: 0i32,
        micros: 0i64,
    }
}

/// `o_orderdate < $2 + INTERVAL '1' YEAR`.
pub open spec fn date_lt_pred(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(12), b: hi_expr(ps) }
}

/// Everything before the last conjunct.
pub open spec fn pred_head(ps: Seq<Literal>) -> Pred {
    and_p(and_p(join_pred(), name_pred(ps)), date_ge_pred(ps))
}

/// The WHERE condition.
pub open spec fn q5_pred(ps: Seq<Literal>) -> Pred {
    and_p(pred_head(ps), date_lt_pred(ps))
}

/// `FROM customer, orders, lineitem, supplier, nation, region`.
pub open spec fn q5_from() -> Query {
    Query::Product {
        left: Box::new(Query::Product {
            left: Box::new(Query::Product {
                left: Box::new(Query::Product {
                    left: Box::new(Query::Product { left: Box::new(Query::Table(2)), right: Box::new(Query::Table(1)) }),
                    right: Box::new(Query::Table(0)),
                }),
                right: Box::new(Query::Table(5)),
            }),
            right: Box::new(Query::Table(6)),
        }),
        right: Box::new(Query::Table(7)),
    }
}

pub open spec fn q5_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: q5_pred(ps), input: Box::new(q5_from()) }
}

pub open spec fn q5_key_exprs() -> Seq<Expr> {
    seq![Expr::Col(41)]
}

pub open spec fn q5_aggs() -> Seq<Agg> {
    seq![q5_agg()]
}

/// The statement body: `GROUP BY n_name` over the filtered product.
pub open spec fn q5_body(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: q5_key_exprs(), aggs: q5_aggs(), input: Box::new(q5_filter(ps)) }
}

/// `ORDER BY revenue DESC`.
pub open spec fn q5_order() -> Seq<OrderKey> {
    seq![OrderKey { col: 1, desc: true, nulls_first: true }]
}

// ------------------------------------------------------------------------------------------- parameters

/// The bound parameters as values: `$1` bytes, the day `lo` of `$2`, and the timestamp `hi` of
/// `$2 + INTERVAL '1' YEAR` (when it evaluates).
pub struct Prm {
    pub name: Seq<u8>,
    pub lo: int,
    pub hi: int,
}

/// `o_orderdate >= lo` on a date value.
pub open spec fn day_ge(v: Val, lo: int) -> bool {
    match v {
        Val::Date(d) => d >= lo,
        _ => false,
    }
}

/// `o_orderdate < hi` on a date value against a timestamp (dates compare at midnight).
pub open spec fn day_lt_ts(v: Val, hi: int) -> bool {
    match v {
        Val::Date(d) => d * usecs_per_day() < hi,
        _ => false,
    }
}

/// The date window on an order row (stored or joined column 4 of the orders part).
pub open spec fn date_ok(o: Row, prm: Prm) -> bool {
    day_ge(o[4], prm.lo) && day_lt_ts(o[4], prm.hi)
}

// ------------------------------------------------------------------------------------------- relations

/// The stored relations of the six tables (columns in stored order, rows in canonical order).
pub struct Rels {
    pub l: Seq<Row>,
    pub o: Seq<Row>,
    pub c: Seq<Row>,
    pub s: Seq<Row>,
    pub n: Seq<Row>,
    pub r: Seq<Row>,
}

/// The relations in FROM order (customer, orders, lineitem, supplier, nation, region).
pub open spec fn pts_of(rs: Rels) -> Seq<Seq<Row>> {
    seq![rs.c, rs.o, rs.l, rs.s, rs.n, rs.r]
}

pub open spec fn inputs6() -> Seq<nat> {
    seq![0nat, 1, 2, 3, 4, 5]
}

/// The left-deep product of the stored relations in FROM order: the rows the normal form ranges over.
pub open spec fn xs_of(rs: Rels) -> Seq<Row> {
    product_rows(product_rows(product_rows(product_rows(product_rows(rs.c, rs.o), rs.l), rs.s), rs.n), rs.r)
}

/// Widths of the stored relations (customer 8, orders 7, lineitem 15, supplier 7, nation 4, region 3).
pub open spec fn rels_widths(rs: Rels) -> bool {
    &&& forall|i: int| 0 <= i < rs.c.len() ==> (#[trigger] rs.c[i]).len() == 8
    &&& forall|i: int| 0 <= i < rs.o.len() ==> (#[trigger] rs.o[i]).len() == 7
    &&& forall|i: int| 0 <= i < rs.l.len() ==> (#[trigger] rs.l[i]).len() == 15
    &&& forall|i: int| 0 <= i < rs.s.len() ==> (#[trigger] rs.s[i]).len() == 7
    &&& forall|i: int| 0 <= i < rs.n.len() ==> (#[trigger] rs.n[i]).len() == 4
    &&& forall|i: int| 0 <= i < rs.r.len() ==> (#[trigger] rs.r[i]).len() == 3
}

// ------------------------------------------------------------------------------------------- the normal form
// Positions in the 44-column joined stored row y = c ++ o ++ l ++ s ++ n ++ r:
//   c_custkey 0, c_nationkey 3, o_orderkey 8, o_custkey 9, o_orderdate 12, l_orderkey 15, l_suppkey 17,
//   l_extendedprice 20, l_discount 21, s_suppkey 30, s_nationkey 33, n_nationkey 37, n_name 38, n_regionkey 39,
//   r_regionkey 41, r_name 42.

/// The WHERE condition over a joined stored row.
pub open spec fn q5_qual(prm: Prm, y: Row) -> bool {
    &&& y[0] == y[9]
    &&& y[15] == y[8]
    &&& y[17] == y[30]
    &&& y[3] == y[33]
    &&& y[33] == y[37]
    &&& y[39] == y[41]
    &&& y[42] == Val::Text(prm.name)
    &&& day_ge(y[12], prm.lo)
    &&& day_lt_ts(y[12], prm.hi)
}

/// The group key `(n_name)`.
pub open spec fn q5_key(y: Row) -> Row {
    seq![y[38]]
}

/// The coefficient of a numeric value (0 otherwise).
pub open spec fn coeff_of(v: Val) -> int {
    match v {
        Val::Num { coeff, .. } => coeff,
        _ => 0,
    }
}

/// `l_extendedprice * (1 - l_discount)` at scale 4, from the scale-2 coefficients of a lineitem row (stored
/// columns 5 and 6).
pub open spec fn rev_of_line(l: Row) -> int {
    coeff_of(l[5]) * (100 - coeff_of(l[6]))
}

/// The lineitem part of a joined stored row.
pub open spec fn line_of(y: Row) -> Row {
    y.subrange(15, 30)
}

/// The argument of SUM in a joined stored row.
pub open spec fn q5_arg(y: Row) -> int {
    coeff_of(y[20]) * (100 - coeff_of(y[21]))
}

pub open spec fn q5_g(prm: Prm) -> QuerySpec {
    QuerySpec {
        qual: |y: Row| q5_qual(prm, y),
        key: |y: Row| q5_key(y),
        arg: |j: int, y: Row| q5_arg(y),
        aggs: seq![AggKind::Sum { scale: 4 }],
        outs: seq![0nat, 1nat],
        grouped: true,
    }
}

// ------------------------------------------------------------------------------------------- multiplicities
// Nested sums over the relations: for a lineitem row `l`, `line_mult` counts the (orders, customer, supplier,
// nation, region) combinations that join with it, satisfy the WHERE condition and fall in group `k`.

/// Region row `r` joins nation row `n` with `r_name = $1`.
pub open spec fn r_term(n: Row, name: Seq<u8>, r: Row) -> int {
    if n[2] == r[0] && r[1] == Val::Text(name) { 1int } else { 0int }
}

/// Region rows joining nation row `n` with `r_name = $1`.
pub open spec fn r_cnt(rr: Seq<Row>, n: Row, name: Seq<u8>) -> int {
    sum_of(rr, |r: Row| r_term(n, name, r))
}

/// Nation row `n` joins supplier row `s` in group `k`, weighted by its region rows.
pub open spec fn n_term(rs: Rels, s: Row, k: Row, name: Seq<u8>, n: Row) -> int {
    if s[3] == n[0] && seq![n[1]] == k { r_cnt(rs.r, n, name) } else { 0int }
}

/// Nation rows joining supplier row `s` in group `k`, weighted by their region rows.
pub open spec fn n_cnt(rs: Rels, s: Row, k: Row, name: Seq<u8>) -> int {
    sum_of(rs.n, |n: Row| n_term(rs, s, k, name, n))
}

/// Supplier row `s` joins lineitem row `l` and customer row `c`.
pub open spec fn s_term(rs: Rels, c: Row, l: Row, k: Row, name: Seq<u8>, s: Row) -> int {
    if l[2] == s[0] && c[3] == s[3] { n_cnt(rs, s, k, name) } else { 0int }
}

/// Supplier rows joining lineitem row `l` and customer row `c`.
pub open spec fn s_cnt(rs: Rels, c: Row, l: Row, k: Row, name: Seq<u8>) -> int {
    sum_of(rs.s, |s: Row| s_term(rs, c, l, k, name, s))
}

/// Customer row `c` joins order row `o`.
pub open spec fn c_term(rs: Rels, o: Row, l: Row, k: Row, name: Seq<u8>, c: Row) -> int {
    if c[0] == o[1] { s_cnt(rs, c, l, k, name) } else { 0int }
}

/// Customer rows joining order row `o`.
pub open spec fn c_cnt(rs: Rels, o: Row, l: Row, k: Row, name: Seq<u8>) -> int {
    sum_of(rs.c, |c: Row| c_term(rs, o, l, k, name, c))
}

/// Order row `o` joins lineitem row `l` inside the date window.
pub open spec fn o_term(rs: Rels, prm: Prm, k: Row, l: Row, o: Row) -> int {
    if l[0] == o[0] && date_ok(o, prm) { c_cnt(rs, o, l, k, prm.name) } else { 0int }
}

/// Joined rows of group `k` that lineitem row `l` takes part in.
#[verifier::opaque]
pub open spec fn line_mult(rs: Rels, prm: Prm, k: Row, l: Row) -> int {
    sum_of(rs.o, |o: Row| o_term(rs, prm, k, l, o))
}

/// Weights of the three accumulators: 0 count, 1 revenue, 2 absolute revenue.
pub open spec fn wsel(m: int, l: Row) -> int {
    if m == 0 { 1 } else if m == 1 { rev_of_line(l) } else { abs(rev_of_line(l)) }
}

/// Contribution of lineitem row `l` to accumulator `m` of group `k`.
pub open spec fn contrib(rs: Rels, prm: Prm, k: Row, m: int, l: Row) -> int {
    line_mult(rs, prm, k, l) * wsel(m, l)
}

pub open spec fn contrib_fn(rs: Rels, prm: Prm, k: Row, m: int) -> spec_fn(Row) -> int {
    |l: Row| contrib(rs, prm, k, m, l)
}

/// The group key of a nation name.
pub open spec fn name_key(b: Seq<u8>) -> Row {
    seq![Val::Text(b)]
}

} // verus!
