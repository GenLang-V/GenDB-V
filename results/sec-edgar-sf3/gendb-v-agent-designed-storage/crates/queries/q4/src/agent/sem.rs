//! The statement's FROM / WHERE in closed form: the joined relation `num x sub x tag x pre` (left-deep product,
//! canonical row order) kept by one two-valued condition `qual` on the 48 joined values.
//!
//! Joined row layout (positions): num 0..9 (adsh 0, tag 1, version 2, uom 5, value 7), sub 9..29 (adsh 9, cik 10,
//! sic 12), tag 29..38 (tag 29, version 30, abstract 32, tlabel 36), pre 38..48 (adsh 38, stmt 41, tag 44,
//! version 45). The WHERE condition can be Unknown (NULL stmt or sic); a row is kept exactly when it is True, so the
//! filter lemma here is three-valued (`lemma_eval_filter3`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::typing::*;
use crate::spec::text::lex_cmp;
use crate::schema::schema_spec;
use crate::query::{query_spec_at, param_domain};
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::link::join::{keep, lemma_keep_members, lemma_keep_keep, lemma_keep_ext, lemma_eval_product, lemma_eval_table,
    left_of, right_of};

verus! {

// ------------------------------------------------------------------------------------------------ the binding

/// The binding of the four parameters as literals (`Params::view` has exactly this shape).
pub open spec fn ps_of(b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int) -> Seq<Literal> {
    seq![Literal::Text(b0), Literal::Text(b1), Literal::Int { v: lo, kind: IntKind::Int4 }, Literal::Int { v: hi, kind: IntKind::Int4 }]
}

/// The binding is in the parameter domain exactly when both integers are int4.
pub open spec fn bind_ok(lo: int, hi: int) -> bool {
    int_in_range(IntKind::Int4, lo) && int_in_range(IntKind::Int4, hi)
}

// ------------------------------------------------------------------------------------------------ the AST, by parts

pub open spec fn col(i: nat) -> Expr { Expr::Col(i) }

pub open spec fn eq_cols(i: nat, j: nat) -> Pred { Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Col(j) } }

/// `n.adsh = s.adsh`.
pub open spec fn pred_n62() -> Pred { eq_cols(0, 9) }

/// `n.tag = t.tag AND n.version = t.version`.
pub open spec fn pred_n59() -> Pred { Pred::And(Box::new(eq_cols(1, 29)), Box::new(eq_cols(2, 30))) }

/// `n.adsh = p.adsh AND n.tag = p.tag AND n.version = p.version`.
pub open spec fn pred_n52() -> Pred {
    Pred::And(Box::new(Pred::And(Box::new(eq_cols(0, 38)), Box::new(eq_cols(1, 44)))), Box::new(eq_cols(2, 45)))
}

pub open spec fn pred_n17(ps: Seq<Literal>) -> Pred { Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(ps[0]) } }
pub open spec fn pred_n21(ps: Seq<Literal>) -> Pred { Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(41), b: Expr::Lit(ps[1]) } }
pub open spec fn pred_n26(ps: Seq<Literal>) -> Pred { Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(12), b: Expr::Lit(ps[2]) } }
pub open spec fn pred_n30(ps: Seq<Literal>) -> Pred { Pred::Cmp { op: CmpOp::Le, a: Expr::Col(12), b: Expr::Lit(ps[3]) } }
pub open spec fn pred_n35() -> Pred { Pred::Not(Box::new(Pred::IsNull(Expr::Col(7)))) }
pub open spec fn pred_n40() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(32), b: Expr::Lit(Literal::Int { v: 0, kind: IntKind::Int4 }) }
}

/// The WHERE condition.
pub open spec fn pred_n41(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::And(
                Box::new(Pred::And(Box::new(pred_n17(ps)), Box::new(pred_n21(ps)))),
                Box::new(Pred::And(Box::new(pred_n26(ps)), Box::new(pred_n30(ps)))),
            )),
            Box::new(pred_n35()),
        )),
        Box::new(pred_n40()),
    )
}

pub open spec fn q66() -> Query {
    Query::Filter { pred: pred_n62(), input: Box::new(Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) }) }
}

pub open spec fn q69() -> Query {
    Query::Filter { pred: pred_n59(), input: Box::new(Query::Product { left: Box::new(q66()), right: Box::new(Query::Table(2)) }) }
}

pub open spec fn q72() -> Query {
    Query::Filter { pred: pred_n52(), input: Box::new(Query::Product { left: Box::new(q69()), right: Box::new(Query::Table(3)) }) }
}

/// FROM .. WHERE.
pub open spec fn q73(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: pred_n41(ps), input: Box::new(q72()) }
}

pub open spec fn gb_keys() -> Seq<Expr> { seq![Expr::Col(12), Expr::Col(36), Expr::Col(41)] }

pub open spec fn gb_aggs() -> Seq<Agg> {
    seq![
        Agg::DistinctAgg(Box::new(Agg::Count(Expr::Col(10)))),
        Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(7) },
        Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(7) },
    ]
}

/// GROUP BY s.sic, t.tlabel, p.stmt with COUNT(DISTINCT s.cik), SUM(n.value), AVG(n.value).
pub open spec fn q74(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: gb_keys(), aggs: gb_aggs(), input: Box::new(q73(ps)) }
}

/// HAVING COUNT(DISTINCT s.cik) >= 2.
pub open spec fn pred_n3() -> Pred {
    Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(3), b: Expr::Lit(Literal::Int { v: 2, kind: IntKind::Int4 }) }
}

pub open spec fn q75(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: pred_n3(), input: Box::new(q74(ps)) }
}

pub open spec fn order_keys() -> Seq<OrderKey> { seq![OrderKey { col: 4, desc: true, nulls_first: true }] }

/// The generated statement, by parts.
pub proof fn lemma_query_parts(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: q75(ps), keys: order_keys(), limit: Some(500nat), offset: 0nat }),
{
    assert(gb_keys() =~= seq![Expr::Col(12), Expr::Col(36), Expr::Col(41)]);
}

// ------------------------------------------------------------------------------------------------ row typing

pub open spec fn is_text(v: Val) -> bool { v is Text }

/// Typed `num` row (the columns the statement reads).
pub open spec fn num_ok(r: Row) -> bool {
    r.len() == 9 && r[0] is Text && r[1] is Text && r[2] is Text && r[5] is Text && r[7] is Num && r[7]->Num_scale == 4
}

pub open spec fn sub_ok(r: Row) -> bool {
    r.len() == 20 && r[0] is Text && r[1] is Int && int_in_range(IntKind::Int4, r[1]->Int_0) && (r[3] is Int || r[3] is Null)
}

pub open spec fn tag_ok(r: Row) -> bool {
    r.len() == 9 && r[0] is Text && r[1] is Text && r[3] is Int && (r[7] is Text || r[7] is Null)
}

pub open spec fn pre_ok(r: Row) -> bool {
    r.len() == 10 && r[0] is Text && r[6] is Text && r[7] is Text && (r[3] is Text || r[3] is Null)
}

/// On a well-formed database of the schema every row of the four tables is typed.
pub proof fn lemma_rows_typed(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures
        db.tables.len() == 4,
        forall|i: int| 0 <= i < db.tables[1].len() ==> num_ok(#[trigger] db.tables[1][i]),
        forall|i: int| 0 <= i < db.tables[0].len() ==> sub_ok(#[trigger] db.tables[0][i]),
        forall|i: int| 0 <= i < db.tables[2].len() ==> tag_ok(#[trigger] db.tables[2][i]),
        forall|i: int| 0 <= i < db.tables[3].len() ==> pre_ok(#[trigger] db.tables[3][i]),
{
    let s = schema_spec();
    assert(s.len() == 4);
    assert forall|i: int| 0 <= i < db.tables[1].len() implies num_ok(#[trigger] db.tables[1][i]) by {
        let r = db.tables[1][i];
        assert(row_in_table(r, s[1]));
        assert(value_in_column(r[0], s[1].columns[0]) && value_in_column(r[1], s[1].columns[1]));
        assert(value_in_column(r[2], s[1].columns[2]) && value_in_column(r[5], s[1].columns[5]));
        assert(value_in_column(r[7], s[1].columns[7]));
    }
    assert forall|i: int| 0 <= i < db.tables[0].len() implies sub_ok(#[trigger] db.tables[0][i]) by {
        let r = db.tables[0][i];
        assert(row_in_table(r, s[0]));
        assert(value_in_column(r[0], s[0].columns[0]) && value_in_column(r[1], s[0].columns[1]));
        assert(value_in_column(r[3], s[0].columns[3]));
    }
    assert forall|i: int| 0 <= i < db.tables[2].len() implies tag_ok(#[trigger] db.tables[2][i]) by {
        let r = db.tables[2][i];
        assert(row_in_table(r, s[2]));
        assert(value_in_column(r[0], s[2].columns[0]) && value_in_column(r[1], s[2].columns[1]));
        assert(value_in_column(r[3], s[2].columns[3]) && value_in_column(r[7], s[2].columns[7]));
    }
    assert forall|i: int| 0 <= i < db.tables[3].len() implies pre_ok(#[trigger] db.tables[3][i]) by {
        let r = db.tables[3][i];
        assert(row_in_table(r, s[3]));
        assert(value_in_column(r[0], s[3].columns[0]) && value_in_column(r[6], s[3].columns[6]));
        assert(value_in_column(r[7], s[3].columns[7]) && value_in_column(r[3], s[3].columns[3]));
    }
}

// ------------------------------------------------------------------------------------------------ the condition

/// Integer of a value (0 for others).
pub open spec fn ival(v: Val) -> int { match v { Val::Int(x) => x, _ => 0 } }

/// The WHERE condition on a joined row, two-valued: kept exactly when the SQL condition is True.
pub open spec fn where_ok(b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int, x: Row) -> bool {
    &&& x[5] == Val::Text(b0)
    &&& x[41] == Val::Text(b1)
    &&& x[12] is Int && lo <= ival(x[12]) <= hi
    &&& x[32] == Val::Int(0)
}

/// Join conditions of the three ON clauses.
pub open spec fn join_ok(x: Row) -> bool {
    &&& x[0] == x[9]
    &&& x[1] == x[29] && x[2] == x[30]
    &&& x[0] == x[38] && x[1] == x[44] && x[2] == x[45]
}

// Kept-row conditions of each level of the FROM tree (`link::join` style: the left part, then the right part).
pub open spec fn f2(x: Row) -> bool { num_ok(left_of(x, 9)) && sub_ok(right_of(x, 9)) }
pub open spec fn g2(x: Row) -> bool { f2(x) && x[0] == x[9] }
pub open spec fn f3(x: Row) -> bool { g2(left_of(x, 29)) && tag_ok(right_of(x, 29)) }
pub open spec fn g3(x: Row) -> bool { f3(x) && x[1] == x[29] && x[2] == x[30] }
pub open spec fn f4(x: Row) -> bool { g3(left_of(x, 38)) && pre_ok(right_of(x, 38)) }
pub open spec fn g4(x: Row) -> bool { f4(x) && x[0] == x[38] && x[1] == x[44] && x[2] == x[45] }

/// The kept joined rows' condition.
pub open spec fn qual(b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int, x: Row) -> bool {
    g4(x) && where_ok(b0, b1, lo, hi, x)
}

/// The joined relation (left-deep product, canonical order).
pub open spec fn joined(db: Database) -> Seq<Row> {
    product_rows(product_rows(product_rows(db.tables[1], db.tables[0]), db.tables[2]), db.tables[3])
}

// ------------------------------------------------------------------------------------------------ product row lengths

/// Every row of a product has the sum of the widths.
pub proof fn lemma_product_widths(a: Seq<Row>, b: Seq<Row>, wa: nat, wb: nat)
    requires
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == wa,
        forall|j: int| 0 <= j < b.len() ==> (#[trigger] b[j]).len() == wb,
    ensures
        forall|k: int| 0 <= k < product_rows(a, b).len() ==> (#[trigger] product_rows(a, b)[k]).len() == wa + wb,
    decreases a.len(),
{
    if a.len() > 0 {
        let ai = a.drop_last();
        assert forall|i: int| 0 <= i < ai.len() implies (#[trigger] ai[i]).len() == wa by {
            assert(ai[i] == a[i]);
        }
        lemma_product_widths(ai, b, wa, wb);
        let p0 = product_rows(ai, b);
        let m = b.map_values(|r: Row| a.last() + r);
        assert(product_rows(a, b) == p0 + m);
        assert(a.last() == a[a.len() - 1]);
        assert forall|k: int| 0 <= k < product_rows(a, b).len() implies (#[trigger] product_rows(a, b)[k]).len() == wa + wb by {
            if k < p0.len() {
                assert(product_rows(a, b)[k] == p0[k]);
            } else {
                assert(product_rows(a, b)[k] == m[k - p0.len()]);
                assert(b[k - p0.len()].len() == wb);
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ predicate evaluation

/// `Col(i) = Col(j)` on two text values is their equality.
pub proof fn lemma_eval_eq_text(db: Database, x: Row, i: nat, j: nat)
    requires i < x.len(), j < x.len(), x[i as int] is Text, x[j as int] is Text,
    ensures eval_pred(db, x, eq_cols(i, j)) == Ok::<Truth, SqlError>(truth_of(x[i as int] == x[j as int])),
{
    let (a, b) = (x[i as int]->Text_0, x[j as int]->Text_0);
    lemma_lex_cmp_zero(a, b);
    assert(eval_expr(db, x, Expr::Col(i)) == Ok::<Val, SqlError>(x[i as int]));
    assert(eval_expr(db, x, Expr::Col(j)) == Ok::<Val, SqlError>(x[j as int]));
    assert(compare(x[i as int], x[j as int]) == Some(lex_cmp(a, b)));
    assert(cmp_truth(CmpOp::Eq, x[i as int], x[j as int]) == Ok::<Truth, SqlError>(truth_of(x[i as int] == x[j as int])));
}

/// Kleene conjunction of two evaluated conditions.
pub proof fn lemma_eval_and(db: Database, x: Row, a: Pred, b: Pred, ta: Truth, tb: Truth)
    requires eval_pred(db, x, a) == Ok::<Truth, SqlError>(ta), eval_pred(db, x, b) == Ok::<Truth, SqlError>(tb),
    ensures eval_pred(db, x, Pred::And(Box::new(a), Box::new(b))) == Ok::<Truth, SqlError>(truth_and(ta, tb)),
{
}

/// `Col(i) op Lit(Int v)` on an int4 literal: Unknown on NULL, else the integer comparison.
pub proof fn lemma_eval_cmp_int(db: Database, x: Row, i: nat, op: CmpOp, v: int)
    requires i < x.len(), x[i as int] is Int || x[i as int] is Null, int_in_range(IntKind::Int4, v),
    ensures
        eval_pred(db, x, Pred::Cmp { op, a: Expr::Col(i), b: Expr::Lit(Literal::Int { v, kind: IntKind::Int4 }) })
            == Ok::<Truth, SqlError>(if x[i as int] is Null { Truth::Unknown } else { truth_of(cmp_holds(op, sign(ival(x[i as int]) - v))) }),
{
    let l = Literal::Int { v, kind: IntKind::Int4 };
    assert(eval_expr(db, x, Expr::Col(i)) == Ok::<Val, SqlError>(x[i as int]));
    assert(lit_val(l) == Ok::<Val, SqlError>(Val::Int(v)));
    assert(eval_expr(db, x, Expr::Lit(l)) == Ok::<Val, SqlError>(Val::Int(v)));
    if x[i as int] is Int {
        assert(compare(x[i as int], Val::Int(v)) == Some(sign(ival(x[i as int]) - v)));
    }
}

/// `Col(i) = Lit(Text b)` on a text or NULL value: Unknown on NULL, else byte equality.
pub proof fn lemma_eval_eq_lit_text(db: Database, x: Row, i: nat, b: Seq<u8>)
    requires i < x.len(), x[i as int] is Text || x[i as int] is Null,
    ensures
        eval_pred(db, x, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Lit(Literal::Text(b)) })
            == Ok::<Truth, SqlError>(if x[i as int] is Null { Truth::Unknown } else { truth_of(x[i as int] == Val::Text(b)) }),
{
    assert(eval_expr(db, x, Expr::Col(i)) == Ok::<Val, SqlError>(x[i as int]));
    assert(eval_expr(db, x, Expr::Lit(Literal::Text(b))) == Ok::<Val, SqlError>(Val::Text(b)));
    if x[i as int] is Text {
        let a = x[i as int]->Text_0;
        lemma_lex_cmp_zero(a, b);
        assert(compare(x[i as int], Val::Text(b)) == Some(lex_cmp(a, b)));
    }
}

/// Truth value of the WHERE condition (three-valued, from the parts).
pub open spec fn where_truth(b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int, x: Row) -> Truth {
    let t17 = truth_of(x[5] == Val::Text(b0));
    let t21 = if x[41] is Null { Truth::Unknown } else { truth_of(x[41] == Val::Text(b1)) };
    let t26 = if x[12] is Null { Truth::Unknown } else { truth_of(cmp_holds(CmpOp::Ge, sign(ival(x[12]) - lo))) };
    let t30 = if x[12] is Null { Truth::Unknown } else { truth_of(cmp_holds(CmpOp::Le, sign(ival(x[12]) - hi))) };
    let t35 = truth_not(truth_of(x[7] is Null));
    let t40 = truth_of(cmp_holds(CmpOp::Eq, sign(ival(x[32]) - 0)));
    truth_and(truth_and(truth_and(truth_and(t17, t21), truth_and(t26, t30)), t35), t40)
}

/// The WHERE condition evaluates (no error) on a typed joined row, to `where_truth`.
pub proof fn lemma_eval_where(db: Database, b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int, x: Row)
    requires
        bind_ok(lo, hi),
        x.len() == 48,
        x[5] is Text, x[41] is Text || x[41] is Null, x[12] is Int || x[12] is Null, x[7] is Num, x[32] is Int,
    ensures
        eval_pred(db, x, pred_n41(ps_of(b0, b1, lo, hi))) == Ok::<Truth, SqlError>(where_truth(b0, b1, lo, hi, x)),
{
    hide(eval_pred);
    let ps = ps_of(b0, b1, lo, hi);
    assert(ps[0] == Literal::Text(b0) && ps[1] == Literal::Text(b1));
    assert(ps[2] == (Literal::Int { v: lo, kind: IntKind::Int4 }) && ps[3] == (Literal::Int { v: hi, kind: IntKind::Int4 }));
    lemma_eval_eq_lit_text(db, x, 5, b0);
    lemma_eval_eq_lit_text(db, x, 41, b1);
    lemma_eval_cmp_int(db, x, 12, CmpOp::Ge, lo);
    lemma_eval_cmp_int(db, x, 12, CmpOp::Le, hi);
    lemma_eval_cmp_int(db, x, 32, CmpOp::Eq, 0);
    let t17 = truth_of(x[5] == Val::Text(b0));
    let t21 = if x[41] is Null { Truth::Unknown } else { truth_of(x[41] == Val::Text(b1)) };
    let t26 = if x[12] is Null { Truth::Unknown } else { truth_of(cmp_holds(CmpOp::Ge, sign(ival(x[12]) - lo))) };
    let t30 = if x[12] is Null { Truth::Unknown } else { truth_of(cmp_holds(CmpOp::Le, sign(ival(x[12]) - hi))) };
    let t35 = truth_not(truth_of(x[7] is Null));
    let t40 = truth_of(cmp_holds(CmpOp::Eq, sign(ival(x[32]) - 0)));
    assert(eval_pred(db, x, pred_n35()) == Ok::<Truth, SqlError>(t35)) by {
        reveal(eval_pred);
        assert(eval_expr(db, x, Expr::Col(7)) == Ok::<Val, SqlError>(x[7]));
        assert(eval_pred(db, x, Pred::IsNull(Expr::Col(7))) == Ok::<Truth, SqlError>(truth_of(x[7] is Null)));
    }
    lemma_eval_and(db, x, pred_n17(ps), pred_n21(ps), t17, t21);
    lemma_eval_and(db, x, pred_n26(ps), pred_n30(ps), t26, t30);
    let p22 = Pred::And(Box::new(pred_n17(ps)), Box::new(pred_n21(ps)));
    let p31 = Pred::And(Box::new(pred_n26(ps)), Box::new(pred_n30(ps)));
    lemma_eval_and(db, x, p22, p31, truth_and(t17, t21), truth_and(t26, t30));
    let p32 = Pred::And(Box::new(p22), Box::new(p31));
    lemma_eval_and(db, x, p32, pred_n35(), truth_and(truth_and(t17, t21), truth_and(t26, t30)), t35);
    let p36 = Pred::And(Box::new(p32), Box::new(pred_n35()));
    lemma_eval_and(db, x, p36, pred_n40(), truth_and(truth_and(truth_and(t17, t21), truth_and(t26, t30)), t35), t40);
}

/// `where_truth` is True exactly when `where_ok` holds.
pub proof fn lemma_where_truth(b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int, x: Row)
    requires x[7] is Num, x[32] is Int, x[12] is Int || x[12] is Null,
    ensures (where_truth(b0, b1, lo, hi, x) is True) == where_ok(b0, b1, lo, hi, x),
{
    if x[32] is Int {
        assert((sign(ival(x[32]) - 0) == 0) == (x[32] == Val::Int(0)));
    }
}

// ------------------------------------------------------------------------------------------------ three-valued filter

/// Rows of a WHERE: `keep_true` of three-valued truths keeps the rows whose truth is True.
pub proof fn lemma_keep_true3(rows: Seq<Row>, truths: Seq<Truth>, h: spec_fn(Row) -> bool)
    requires
        truths.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] truths[i] is True) == h(rows[i]),
    ensures keep_true(rows, truths) == keep(rows, h),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < ri.len() implies (#[trigger] ti[i] is True) == h(ri[i]) by {
            assert(ti[i] == truths[i] && ri[i] == rows[i]);
        }
        lemma_keep_true3(ri, ti, h);
        assert((truths[rows.len() - 1] is True) == h(rows[rows.len() - 1]));
    }
}

/// A WHERE over an input evaluating to `keep(rows, f)`, with a condition that evaluates without error on every
/// kept row to a truth value that is True exactly when `h` holds: the rows kept by `f && h`.
pub proof fn lemma_eval_filter3(db: Database, src: Query, rows: Seq<Row>, f: spec_fn(Row) -> bool, pred: Pred,
    t: spec_fn(Row) -> Truth, h: spec_fn(Row) -> bool, fh: spec_fn(Row) -> bool)
    requires
        eval_query(db, Seq::empty(), src) == Ok::<Relation, SqlError>(keep(rows, f)),
        forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) ==>
            eval_pred(db, rows[i], pred) == Ok::<Truth, SqlError>(t(rows[i])) && (t(rows[i]) is True) == h(rows[i]),
        forall|i: int| 0 <= i < rows.len() ==> fh(#[trigger] rows[i]) == (f(rows[i]) && h(rows[i])),
    ensures
        eval_query(db, Seq::empty(), Query::Filter { pred, input: Box::new(src) }) == Ok::<Relation, SqlError>(keep(rows, fh)),
{
    let kept = keep(rows, f);
    let ctx = Seq::<Val>::empty();
    lemma_keep_members(rows, f);
    let truths = Seq::new(kept.len(), |i: int| t(kept[i]));
    let prs = Seq::new(kept.len(), |i: int| eval_pred(db, ctx + kept[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(ctx + kept[i] =~= kept[i]);
        assert(rows.contains(kept[i]) && f(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(f(rows[m]));
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    assert(collect(Seq::new(kept.len(), |i: int| eval_pred(db, ctx + kept[i], pred))) == Ok::<Seq<Truth>, SqlError>(truths));
    assert forall|i: int| 0 <= i < kept.len() implies (#[trigger] truths[i] is True) == h(kept[i]) by {
        assert(rows.contains(kept[i]) && f(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(f(rows[m]));
    }
    lemma_keep_true3(kept, truths, h);
    lemma_keep_keep(rows, f, h);
    lemma_keep_ext(rows, |x: Row| f(x) && h(x), fh);
}

// ------------------------------------------------------------------------------------------------ FROM .. WHERE

/// Joined-row widths of each level.
pub open spec fn p2(db: Database) -> Seq<Row> { product_rows(db.tables[1], db.tables[0]) }
pub open spec fn p3(db: Database) -> Seq<Row> { product_rows(p2(db), db.tables[2]) }

/// The FROM tree with its three ON conditions evaluates to the joined relation kept by `g4`.
pub proof fn lemma_eval_join(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures eval_query(db, Seq::empty(), q72()) == Ok::<Relation, SqlError>(keep(joined(db), |x: Row| g4(x))),
{
    hide(eval_pred);
    lemma_rows_typed(db);
    let (num, sub, tag, pre) = (db.tables[1], db.tables[0], db.tables[2], db.tables[3]);
    // Tables.
    lemma_eval_table(db, 1, |r: Row| num_ok(r));
    lemma_eval_table(db, 0, |r: Row| sub_ok(r));
    lemma_eval_table(db, 2, |r: Row| tag_ok(r));
    lemma_eval_table(db, 3, |r: Row| pre_ok(r));
    // num x sub, ON n.adsh = s.adsh.
    let rows2 = p2(db);
    lemma_eval_product(db, Query::Table(1), Query::Table(0), num, |r: Row| num_ok(r), 9, sub, |r: Row| sub_ok(r),
        rows2, |x: Row| f2(x));
    lemma_product_widths(num, sub, 9, 20);
    assert forall|i: int| 0 <= i < rows2.len() && f2(#[trigger] rows2[i]) implies
        eval_pred(db, rows2[i], pred_n62()) == Ok::<Truth, SqlError>(truth_of(rows2[i][0] == rows2[i][9]))
        && (truth_of(rows2[i][0] == rows2[i][9]) is True) == (rows2[i][0] == rows2[i][9]) by {
        let x = rows2[i];
        assert(x.len() == 29);
        assert(left_of(x, 9)[0] == x[0] && right_of(x, 9)[0] == x[9]);
        lemma_eval_eq_text(db, x, 0, 9);
    }
    lemma_eval_filter3(db, Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) },
        rows2, |x: Row| f2(x), pred_n62(), |x: Row| truth_of(x[0] == x[9]), |x: Row| x[0] == x[9], |x: Row| g2(x));
    // (num x sub) x tag, ON n.tag = t.tag AND n.version = t.version.
    let rows3 = p3(db);
    assert forall|i: int| 0 <= i < rows2.len() implies (#[trigger] rows2[i]).len() == 29 by {}
    lemma_eval_product(db, q66(), Query::Table(2), rows2, |x: Row| g2(x), 29, tag, |r: Row| tag_ok(r),
        rows3, |x: Row| f3(x));
    lemma_product_widths(rows2, tag, 29, 9);
    let t59 = |x: Row| truth_and(truth_of(x[1] == x[29]), truth_of(x[2] == x[30]));
    let h59 = |x: Row| x[1] == x[29] && x[2] == x[30];
    assert forall|i: int| 0 <= i < rows3.len() && f3(#[trigger] rows3[i]) implies
        eval_pred(db, rows3[i], pred_n59()) == Ok::<Truth, SqlError>(t59(rows3[i])) && (t59(rows3[i]) is True) == h59(rows3[i]) by {
        let x = rows3[i];
        assert(x.len() == 38);
        let l = left_of(x, 29);
        assert(l.len() == 29 && left_of(l, 9).len() == 9);
        assert(left_of(l, 9)[1] == x[1] && left_of(l, 9)[2] == x[2]);
        assert(right_of(x, 29)[0] == x[29] && right_of(x, 29)[1] == x[30]);
        lemma_eval_eq_text(db, x, 1, 29);
        lemma_eval_eq_text(db, x, 2, 30);
        lemma_eval_and(db, x, eq_cols(1, 29), eq_cols(2, 30), truth_of(x[1] == x[29]), truth_of(x[2] == x[30]));
    }
    lemma_eval_filter3(db, Query::Product { left: Box::new(q66()), right: Box::new(Query::Table(2)) },
        rows3, |x: Row| f3(x), pred_n59(), t59, h59, |x: Row| g3(x));
    // ((num x sub) x tag) x pre, ON n.adsh = p.adsh AND n.tag = p.tag AND n.version = p.version.
    let rows4 = joined(db);
    assert forall|i: int| 0 <= i < rows3.len() implies (#[trigger] rows3[i]).len() == 38 by {}
    lemma_eval_product(db, q69(), Query::Table(3), rows3, |x: Row| g3(x), 38, pre, |r: Row| pre_ok(r),
        rows4, |x: Row| f4(x));
    lemma_product_widths(rows3, pre, 38, 10);
    let t52 = |x: Row| truth_and(truth_and(truth_of(x[0] == x[38]), truth_of(x[1] == x[44])), truth_of(x[2] == x[45]));
    let h52 = |x: Row| x[0] == x[38] && x[1] == x[44] && x[2] == x[45];
    assert forall|i: int| 0 <= i < rows4.len() && f4(#[trigger] rows4[i]) implies
        eval_pred(db, rows4[i], pred_n52()) == Ok::<Truth, SqlError>(t52(rows4[i])) && (t52(rows4[i]) is True) == h52(rows4[i]) by {
        let x = rows4[i];
        assert(x.len() == 48);
        let l = left_of(x, 38);
        let ll = left_of(l, 29);
        assert(l.len() == 38 && ll.len() == 29 && left_of(ll, 9).len() == 9);
        assert(left_of(ll, 9)[0] == x[0] && left_of(ll, 9)[1] == x[1] && left_of(ll, 9)[2] == x[2]);
        let p = right_of(x, 38);
        assert(p[0] == x[38] && p[6] == x[44] && p[7] == x[45]);
        lemma_eval_eq_text(db, x, 0, 38);
        lemma_eval_eq_text(db, x, 1, 44);
        lemma_eval_eq_text(db, x, 2, 45);
        lemma_eval_and(db, x, eq_cols(0, 38), eq_cols(1, 44), truth_of(x[0] == x[38]), truth_of(x[1] == x[44]));
        lemma_eval_and(db, x, Pred::And(Box::new(eq_cols(0, 38)), Box::new(eq_cols(1, 44))), eq_cols(2, 45),
            truth_and(truth_of(x[0] == x[38]), truth_of(x[1] == x[44])), truth_of(x[2] == x[45]));
    }
    lemma_eval_filter3(db, Query::Product { left: Box::new(q69()), right: Box::new(Query::Table(3)) },
        rows4, |x: Row| f4(x), pred_n52(), t52, h52, |x: Row| g4(x));
}

/// The rows of the joined relation have 48 values.
pub proof fn lemma_joined_widths(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures forall|k: int| 0 <= k < joined(db).len() ==> (#[trigger] joined(db)[k]).len() == 48,
{
    lemma_rows_typed(db);
    lemma_product_widths(db.tables[1], db.tables[0], 9, 20);
    lemma_product_widths(p2(db), db.tables[2], 29, 9);
    lemma_product_widths(p3(db), db.tables[3], 38, 10);
}

/// FROM .. WHERE evaluates to the joined relation kept by `qual`.
pub proof fn lemma_eval_where_rows(db: Database, b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int)
    requires db.schema == schema_spec(), db_wf(db), bind_ok(lo, hi),
    ensures
        eval_query(db, Seq::empty(), q73(ps_of(b0, b1, lo, hi)))
            == Ok::<Relation, SqlError>(keep(joined(db), |x: Row| qual(b0, b1, lo, hi, x))),
{
    hide(eval_pred);
    lemma_eval_join(db);
    lemma_joined_widths(db);
    let rows = joined(db);
    let t = |x: Row| where_truth(b0, b1, lo, hi, x);
    let h = |x: Row| where_ok(b0, b1, lo, hi, x);
    assert forall|i: int| 0 <= i < rows.len() && g4(#[trigger] rows[i]) implies
        eval_pred(db, rows[i], pred_n41(ps_of(b0, b1, lo, hi))) == Ok::<Truth, SqlError>(t(rows[i])) && (t(rows[i]) is True) == h(rows[i]) by {
        let x = rows[i];
        assert(x.len() == 48);
        let l = left_of(x, 38);
        let ll = left_of(l, 29);
        let n = left_of(ll, 9);
        let s = right_of(ll, 9);
        let tg = right_of(l, 29);
        let p = right_of(x, 38);
        assert(n[5] == x[5] && n[7] == x[7]);
        assert(s[3] == x[12]);
        assert(tg[3] == x[32]);
        assert(p[3] == x[41]);
        lemma_eval_where(db, b0, b1, lo, hi, x);
        lemma_where_truth(b0, b1, lo, hi, x);
    }
    lemma_eval_filter3(db, q72(), rows, |x: Row| g4(x), pred_n41(ps_of(b0, b1, lo, hi)), t, h,
        |x: Row| qual(b0, b1, lo, hi, x));
}

} // verus!
