//! The WHERE condition and the derived table, row by row, and the two nodes they form.
//!
//! - On every joined row `row8(t, l)` the condition evaluates without error to the truth of `keep8`
//!   (`lemma_pred_row8`), so the filter is `keep(p8, keep8)` (`lemma_eval_filter`).
//! - On every kept row the derived table's expressions evaluate to `inner_row` (`lemma_inner_row8`): the year of
//!   the order date (`date_year`, 1995 or 1996 inside the window, `lemma_window_year`), the volume coefficient
//!   at scale 4, and the supplier nation's name; so the derived table is `keep(p8, keep8)` mapped by `inner_row`
//!   (`lemma_eval_inner`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::datetime::*;
use crate::spec::text::lex_cmp;
use crate::spec::fns::extract::extract_field;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::source_check::date32_val;
use crate::query::param_domain;
use crate::link::join::keep;
use crate::link::query::{lemma_node_add, lemma_node_mul};
use crate::link::expr::ival;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::ast::*;
use crate::agent::from::*;
use crate::agent::common::relations::*;

verus! {

// ------------------------------------------------------------------------------------------------ evaluator steps

pub proof fn lemma_eval_col(db: Database, r: Row, k: nat)
    requires k < r.len(),
    ensures eval_expr(db, r, Expr::Col(k)) == Ok::<Val, SqlError>(r[k as int]),
{
}

pub proof fn lemma_eval_cmp(db: Database, r: Row, op: CmpOp, a: Expr, b: Expr, va: Val, vb: Val)
    requires eval_expr(db, r, a) == Ok::<Val, SqlError>(va), eval_expr(db, r, b) == Ok::<Val, SqlError>(vb),
    ensures eval_pred(db, r, Pred::Cmp { op, a, b }) == cmp_truth(op, va, vb),
{
}

pub proof fn lemma_eval_and(db: Database, r: Row, a: Pred, b: Pred, x: bool, y: bool)
    requires eval_pred(db, r, a) == Ok::<Truth, SqlError>(truth_of(x)), eval_pred(db, r, b) == Ok::<Truth, SqlError>(truth_of(y)),
    ensures eval_pred(db, r, and(a, b)) == Ok::<Truth, SqlError>(truth_of(x && y)),
{
}

/// `x = y` on two integers.
pub proof fn lemma_cmp_int_eq(x: int, y: int)
    ensures cmp_truth(CmpOp::Eq, Val::Int(x), Val::Int(y)) == Ok::<Truth, SqlError>(truth_of(x == y)),
{
}

/// `x = y` on two texts (byte equality).
pub proof fn lemma_cmp_text(x: Seq<u8>, y: Seq<u8>)
    ensures cmp_truth(CmpOp::Eq, Val::Text(x), Val::Text(y)) == Ok::<Truth, SqlError>(truth_of(x == y)),
{
    lemma_lex_cmp_zero(x, y);
}

/// `x >= y` and `x <= y` on two dates.
pub proof fn lemma_cmp_date(x: int, y: int)
    ensures
        cmp_truth(CmpOp::Ge, Val::Date(x), Val::Date(y)) == Ok::<Truth, SqlError>(truth_of(x >= y)),
        cmp_truth(CmpOp::Le, Val::Date(x), Val::Date(y)) == Ok::<Truth, SqlError>(truth_of(x <= y)),
{
}

/// A column comparison `Col(i) = Col(j)` of two integer values.
pub proof fn lemma_eq_cols(db: Database, r: Row, i: nat, j: nat, x: int, y: int)
    requires i < r.len(), j < r.len(), r[i as int] == Val::Int(x), r[j as int] == Val::Int(y),
    ensures eval_pred(db, r, eq_cols(i, j)) == Ok::<Truth, SqlError>(truth_of(r[i as int] == r[j as int])),
{
    lemma_eval_col(db, r, i);
    lemma_eval_col(db, r, j);
    lemma_eval_cmp(db, r, CmpOp::Eq, Expr::Col(i), Expr::Col(j), Val::Int(x), Val::Int(y));
    lemma_cmp_int_eq(x, y);
}

/// A text column compared with a text literal.
pub proof fn lemma_eq_text(db: Database, r: Row, i: nat, lit: Literal, s: Seq<u8>, b: Seq<u8>)
    requires i < r.len(), r[i as int] == Val::Text(s), lit == Literal::Text(b),
    ensures
        eval_pred(db, r, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Lit(lit) })
            == Ok::<Truth, SqlError>(truth_of(r[i as int] == Val::Text(b))),
{
    lemma_eval_col(db, r, i);
    assert(eval_expr(db, r, Expr::Lit(lit)) == Ok::<Val, SqlError>(Val::Text(b)));
    lemma_eval_cmp(db, r, CmpOp::Eq, Expr::Col(i), Expr::Lit(lit), Val::Text(s), Val::Text(b));
    lemma_cmp_text(s, b);
}

/// The two date literals of the window (days since 2000-01-01).
pub proof fn lemma_window_lits()
    ensures
        lit_val(Literal::Date { y: 1995, m: 1, d: 1 }) == Ok::<Val, SqlError>(Val::Date(-1826)),
        lit_val(Literal::Date { y: 1996, m: 12, d: 31 }) == Ok::<Val, SqlError>(Val::Date(-1096)),
{
    assert(valid_ymd(1995, 1, 1) && date_valid(date_from_civil(1995, 1, 1)) && date_from_civil(1995, 1, 1) == -1826) by (compute);
    assert(valid_ymd(1996, 12, 31) && date_valid(date_from_civil(1996, 12, 31)) && date_from_civil(1996, 12, 31) == -1096) by (compute);
}

/// The window condition on a date value.
pub proof fn lemma_date_pred(db: Database, r: Row, d: int)
    requires 36 < r.len(), r[36] == Val::Date(d),
    ensures eval_pred(db, r, date_pred()) == Ok::<Truth, SqlError>(truth_of(date_val_in(r[36]))),
{
    lemma_window_lits();
    let lo = Expr::Lit(Literal::Date { y: 1995, m: 1, d: 1 });
    let hi = Expr::Lit(Literal::Date { y: 1996, m: 12, d: 31 });
    lemma_eval_col(db, r, 36);
    lemma_eval_cmp(db, r, CmpOp::Ge, Expr::Col(36), lo, Val::Date(d), Val::Date(-1826));
    lemma_eval_cmp(db, r, CmpOp::Le, Expr::Col(36), hi, Val::Date(d), Val::Date(-1096));
    lemma_cmp_date(d, -1826);
    lemma_cmp_date(d, -1096);
    lemma_eval_and(db, r, Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(36), b: lo },
        Pred::Cmp { op: CmpOp::Le, a: Expr::Col(36), b: hi }, d >= -1826, d <= -1096);
}

// ------------------------------------------------------------------------------------------------ the condition

/// The literals of the three parameters.
pub proof fn lemma_params(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures
        ps[0] == Literal::Text(nat_of(ps)),
        ps[1] == Literal::Text(reg_of(ps)),
        ps[2] == Literal::Text(typ_of(ps)),
{
}

/// The WHERE condition on a joined row of the database.
pub proof fn lemma_pred_row8(db: Database, sv: StoresView, ps: Seq<Literal>, t: Tup, l: int)
    requires param_domain(ps), tup_in(sv, t), 0 <= l < n_l(sv),
    ensures eval_pred(db, row8(sv, t, l), q8_pred(ps)) == Ok::<Truth, SqlError>(truth_of((keep8(ps))(row8(sv, t, l)))),
{
    let x = row8(sv, t, l);
    lemma_row8(sv, t, l);
    lemma_params(ps);
    lemma_eq_cols(db, x, 0, 17, p_key(sv)[t.p] as int, l_pkey(sv)[l] as int);
    lemma_eq_cols(db, x, 9, 18, s_key(sv)[t.s] as int, l_skey(sv)[l] as int);
    lemma_eq_cols(db, x, 16, 32, l_okey(sv)[l] as int, o_key(sv)[t.o] as int);
    lemma_eq_cols(db, x, 33, 41, o_cust(sv)[t.o] as int, c_key(sv)[t.c] as int);
    lemma_eq_cols(db, x, 44, 49, c_nat(sv)[t.c] as int, n_key(sv)[t.n1] as int);
    lemma_eq_cols(db, x, 51, 57, n_reg(sv)[t.n1] as int, r_key(sv)[t.r] as int);
    lemma_eq_cols(db, x, 12, 53, s_nat(sv)[t.s] as int, n_key(sv)[t.n2] as int);
    lemma_eq_text(db, x, 58, ps[1], r_name(sv, t.r), reg_of(ps));
    lemma_eq_text(db, x, 4, ps[2], p_type(sv, t.p), typ_of(ps));
    lemma_date_pred(db, x, o_date(sv)[t.o] as int - 10957);
    let (e1, e2, e3, e4, e5, e6) = (x[0] == x[17], x[9] == x[18], x[16] == x[32], x[33] == x[41], x[44] == x[49], x[51] == x[57]);
    lemma_eval_and(db, x, eq_cols(0, 17), eq_cols(9, 18), e1, e2);
    let a2 = and(eq_cols(0, 17), eq_cols(9, 18));
    lemma_eval_and(db, x, a2, eq_cols(16, 32), e1 && e2, e3);
    let a3 = and(a2, eq_cols(16, 32));
    lemma_eval_and(db, x, a3, eq_cols(33, 41), e1 && e2 && e3, e4);
    let a4 = and(a3, eq_cols(33, 41));
    lemma_eval_and(db, x, a4, eq_cols(44, 49), e1 && e2 && e3 && e4, e5);
    let a5 = and(a4, eq_cols(44, 49));
    lemma_eval_and(db, x, a5, eq_cols(51, 57), e1 && e2 && e3 && e4 && e5, e6);
    assert(join_pred() == and(a5, eq_cols(51, 57)));
    let j = e1 && e2 && e3 && e4 && e5 && e6;
    let e7 = x[58] == Val::Text(reg_of(ps));
    lemma_eval_and(db, x, join_pred(), reg_cmp(ps), j, e7);
    let e8 = x[12] == x[53];
    lemma_eval_and(db, x, and(join_pred(), reg_cmp(ps)), eq_cols(12, 53), j && e7, e8);
    let e9 = date_val_in(x[36]);
    lemma_eval_and(db, x, and(and(join_pred(), reg_cmp(ps)), eq_cols(12, 53)), date_pred(), j && e7 && e8, e9);
    let e10 = x[4] == Val::Text(typ_of(ps));
    lemma_eval_and(db, x, and(and(and(join_pred(), reg_cmp(ps)), eq_cols(12, 53)), date_pred()), type_cmp(ps),
        j && e7 && e8 && e9, e10);
}

/// The filter keeps exactly the joined rows satisfying `keep8`.
pub proof fn lemma_eval_filter(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), param_domain(ps),
    ensures eval_query(db, Seq::empty(), q8_filter(ps)) == Ok::<Relation, SqlError>(keep(p8(sv), keep8(ps))),
{
    lemma_eval_from(sv, db);
    let rows = p8(sv);
    let ctx = Seq::<Val>::empty();
    let pred = q8_pred(ps);
    let f = keep8(ps);
    let truths = Seq::new(rows.len(), |i: int| truth_of(f(rows[i])));
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(ctx + rows[i] =~= rows[i]);
        assert(rows.contains(rows[i]));
        lemma_p8_contains(sv, rows[i]);
        let (t, l) = choose|t: Tup, l: int| tup_in(sv, t) && 0 <= l < n_l(sv) && rows[i] == #[trigger] row8(sv, t, l);
        lemma_pred_row8(db, sv, ps, t, l);
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    assert(collect(Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred))) == Ok::<Seq<Truth>, SqlError>(truths));
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] truths[i] is True) == f(rows[i]) by {}
    lemma_keep_true_is_true(rows, truths, f);
}

// ------------------------------------------------------------------------------------------------ the derived table

/// `EXTRACT(YEAR FROM d)` of a date value (opaque: its calendar arithmetic is revealed only where computed).
#[verifier::opaque]
pub open spec fn date_year(v: Val) -> int {
    match v { Val::Date(d) => extract_field(ScalarFn::ExtractYear, civil_from_date(d)), _ => 0 }
}

/// The derived table's row of a kept joined row: `o_year, volume, nation`.
pub open spec fn inner_row(x: Row) -> Row {
    seq![Val::Num { coeff: date_year(x[36]), scale: 0 }, Val::Num { coeff: ival(x[21]) * (100 - ival(x[22])), scale: 4 }, x[54]]
}

/// The year is correct for every day of `lo..hi` (days since 2000-01-01), decided by evaluation.
pub open spec fn years_ok(lo: int, hi: int) -> bool
    decreases hi - lo,
{
    if lo >= hi {
        true
    } else {
        extract_field(ScalarFn::ExtractYear, civil_from_date(lo)) == (if lo < -1461 { 1995int } else { 1996int })
            && years_ok(lo + 1, hi)
    }
}

proof fn lemma_years_ok(lo: int, hi: int, d: int)
    requires years_ok(lo, hi), lo <= d < hi,
    ensures extract_field(ScalarFn::ExtractYear, civil_from_date(d)) == (if d < -1461 { 1995int } else { 1996int }),
    decreases hi - lo,
{
    if d > lo {
        lemma_years_ok(lo + 1, hi, d);
    }
}

/// Inside the window the year of a stored day `x` (days since 1970-01-01) is `year_of_day(x)`.
pub proof fn lemma_window_year(x: i32)
    requires date_in(x),
    ensures date_year(date32_val(x)) == year_of_day(x),
{
    reveal(date_year);
    assert(years_ok(-1826, -1095)) by (compute_only);
    lemma_years_ok(-1826, -1095, x as int - 10957);
}

/// `l_extendedprice * (1 - l_discount)` on prices and discounts of numeric(15,2).
pub proof fn lemma_vol_expr(db: Database, r: Row, price: int, disc: int)
    requires
        22 < r.len(),
        r[21] == (Val::Num { coeff: price, scale: 2 }),
        r[22] == (Val::Num { coeff: disc, scale: 2 }),
        abs(price) < pow10(15), abs(disc) < pow10(15),
    ensures eval_expr(db, r, vol_expr()) == Ok::<Val, SqlError>(Val::Num { coeff: price * (100 - disc), scale: 4 }),
{
    let one = num_one();
    assert(lit_val(Literal::Int { v: 1, kind: IntKind::Int4 }) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(eval_expr(db, r, Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(eval_expr(db, r, one) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }));
    lemma_eval_col(db, r, 21);
    lemma_eval_col(db, r, 22);
    assert(pow10(1) == 10 && pow10(2) == 100 && pow10(0) == 1) by (compute);
    assert(crate::spec::limits::numeric_int_digits_max() >= 100) by (compute);
    lemma_node_add(db, r, ArithOp::Sub, one, Expr::Col(22), 1, 0, 1, disc, 2, 15, 2, 100, 1, 16);
    let sub = Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(one), b: Box::new(Expr::Col(22)) };
    assert(1 * 100 - disc * 1 == 100 - disc);
    lemma_node_mul(db, r, Expr::Col(21), sub, price, 2, 15, 100 - disc, 2, 16);
}

/// `EXTRACT(YEAR FROM o_orderdate)` on a date value.
pub proof fn lemma_year_expr(db: Database, r: Row, d: int)
    requires 36 < r.len(), r[36] == Val::Date(d),
    ensures eval_expr(db, r, year_expr()) == Ok::<Val, SqlError>(Val::Num { coeff: date_year(r[36]), scale: 0 }),
{
    reveal(date_year);
    let args = seq![Expr::Col(36)];
    lemma_eval_col(db, r, 36);
    lemma_expr_list1(db, r, Expr::Col(36), Val::Date(d));
    assert(args == seq![Expr::Col(36)]);
}

/// A one-element expression list.
pub proof fn lemma_expr_list1(db: Database, r: Row, e: Expr, v: Val)
    requires eval_expr(db, r, e) == Ok::<Val, SqlError>(v),
    ensures eval_exprs(db, r, seq![e]) == Ok::<Row, SqlError>(seq![v]),
{
    let rs = expr_results(db, r, seq![e]);
    lemma_expr_results_index(db, r, seq![e]);
    lemma_collect_all(rs, seq![v]);
}

/// A three-element expression list.
pub proof fn lemma_expr_list3(db: Database, r: Row, a: Expr, b: Expr, c: Expr, va: Val, vb: Val, vc: Val)
    requires
        eval_expr(db, r, a) == Ok::<Val, SqlError>(va),
        eval_expr(db, r, b) == Ok::<Val, SqlError>(vb),
        eval_expr(db, r, c) == Ok::<Val, SqlError>(vc),
    ensures eval_exprs(db, r, seq![a, b, c]) == Ok::<Row, SqlError>(seq![va, vb, vc]),
{
    let rs = expr_results(db, r, seq![a, b, c]);
    lemma_expr_results_index(db, r, seq![a, b, c]);
    lemma_collect_all(rs, seq![va, vb, vc]);
}

/// The derived table's expressions on a kept joined row.
pub proof fn lemma_inner_row8(db: Database, sv: StoresView, ps: Seq<Literal>, t: Tup, l: int)
    requires domains_ok(sv), tup_in(sv, t), 0 <= l < n_l(sv),
    ensures eval_exprs(db, row8(sv, t, l), inner_exprs()) == Ok::<Row, SqlError>(inner_row(row8(sv, t, l))),
{
    let x = row8(sv, t, l);
    lemma_row8(sv, t, l);
    let price = l_price(sv)[l] as int;
    let disc = l_disc(sv)[l] as int;
    assert(num15(l_price(sv)[l]) && num15(l_disc(sv)[l]));
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
    lemma_vol_expr(db, x, price, disc);
    lemma_year_expr(db, x, o_date(sv)[t.o] as int - 10957);
    lemma_eval_col(db, x, 54);
    let vy = Val::Num { coeff: date_year(x[36]), scale: 0 };
    let vv = Val::Num { coeff: price * (100 - disc), scale: 4 };
    let vn = x[54];
    lemma_expr_list3(db, x, year_expr(), vol_expr(), Expr::Col(54), vy, vv, vn);
    assert(inner_exprs() == seq![year_expr(), vol_expr(), Expr::Col(54)]);
    assert(ival(x[21]) == price && ival(x[22]) == disc);
    assert(inner_row(x) =~= seq![vy, vv, vn]);
}

/// The kept rows of the filter.
pub open spec fn kept8(sv: StoresView, ps: Seq<Literal>) -> Seq<Row> { keep(p8(sv), keep8(ps)) }

/// The derived table's rows.
pub open spec fn zrows(sv: StoresView, ps: Seq<Literal>) -> Seq<Row> {
    kept8(sv, ps).map_values(|x: Row| inner_row(x))
}

/// Every kept row is the joined row of an ok tuple.
pub proof fn lemma_kept_row(sv: StoresView, ps: Seq<Literal>, x: Row)
    requires kept8(sv, ps).contains(x),
    ensures exists|t: Tup, l: int| 0 <= l < n_l(sv) && tup_ok(sv, ps, l, t) && x == #[trigger] row8(sv, t, l),
{
    lemma_keep_contains(p8(sv), keep8(ps), x);
    lemma_p8_contains(sv, x);
    let (t, l) = choose|t: Tup, l: int| tup_in(sv, t) && 0 <= l < n_l(sv) && x == #[trigger] row8(sv, t, l);
    lemma_keep8(sv, ps, t, l);
}

/// The derived table evaluates to `zrows`.
pub proof fn lemma_eval_inner(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), param_domain(ps), domains_ok(sv),
    ensures eval_query(db, Seq::empty(), q8_inner(ps)) == Ok::<Relation, SqlError>(zrows(sv, ps)),
{
    lemma_eval_filter(db, sv, ps);
    let rows = kept8(sv, ps);
    let ctx = Seq::<Val>::empty();
    let rs = Seq::new(rows.len(), |i: int| eval_exprs(db, ctx + rows[i], inner_exprs()));
    let vs = zrows(sv, ps);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(vs[i]) by {
        assert(ctx + rows[i] =~= rows[i]);
        assert(rows.contains(rows[i]));
        lemma_kept_row(sv, ps, rows[i]);
        let (t, l) = choose|t: Tup, l: int| 0 <= l < n_l(sv) && tup_ok(sv, ps, l, t) && rows[i] == #[trigger] row8(sv, t, l);
        lemma_inner_row8(db, sv, ps, t, l);
    }
    lemma_collect_all(rs, vs);
    lemma_collect_pointwise::<Row>();
}

} // verus!
