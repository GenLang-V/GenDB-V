//! FROM and WHERE over the joined rows `jrows(sv) = lineitem x part` (left-major, `row2(l, a)` = lineitem row `l`
//! then part row `a`; 25 values).
//!
//! - On a joined row (`jshape`), each conjunct of a branch evaluates without error to a two-valued truth
//!   (`lemma_key` .. `lemma_instr`), so branch `k` is `jb(ps, k, x)` when `$k + 10` stays inside int4 (`add_ok`,
//!   `lemma_branch`) and fails with `NumericValueOutOfRange` otherwise (`lemma_branch_err`); the WHERE condition is
//!   `jq(ps)` when every `add_ok` holds (`lemma_pred_ok`), else that error (`lemma_pred_err`).
//! - So the filter is `keep(jrows, jq(ps))` (`lemma_eval_filter`), or that error on a non-empty product
//!   (`lemma_filter_err`).
//! - On `row2(l, a)` the condition is the key match and `line::lq(ps, a, l)` (`lemma_jq_row2`); sums over the kept
//!   rows of the joined-row terms `jt_*` are the per-lineitem totals `line::tot` (`lemma_kept_sums`): the part key
//!   column is duplicate-free, so each lineitem row meets at most one part row (`common::sum_pick`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::gendb_entry::stores::StoresView;
use crate::link::join::{keep, sum_of, lemma_keep_true_keep, lemma_keep_members, lemma_sum_of_keep};
use crate::link::expr::{ival, tval, lemma_pred_cmp, lemma_pred_and, lemma_pred_or, lemma_pred_text_cmp, lemma_compare_int,
    lemma_compare_num, lemma_align_same, lemma_align_by};
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::link::capacity::lemma_filter_err as lemma_filter_err_uniform;
use crate::query::param_domain;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::ast::*;
use crate::agent::bind::{adds_ok, lemma_params};
use crate::agent::common::selection::*;
use crate::agent::common::sum_pick::*;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_part::interface as pi;

verus! {

// ------------------------------------------------------------------------------------------------ joined rows

/// The FROM relation.
pub open spec fn jrows(sv: StoresView) -> Seq<Row> { product_rows(line_rows(sv), part_rows(sv)) }

/// The joined row of lineitem row `l` and part row `a`.
pub open spec fn row2(sv: StoresView, l: int, a: int) -> Row { line_rows(sv)[l] + part_rows(sv)[a] }

/// The values a joined row holds at the positions the statement reads.
pub open spec fn jshape(x: Row) -> bool {
    &&& x.len() == 25
    &&& x[1] is Int && x[16] is Int && x[21] is Int
    &&& x[4] is Num && x[4]->Num_scale == 2
    &&& x[5] is Num && x[5]->Num_scale == 2 && abs(x[5]->Num_coeff) < pow10(15)
    &&& x[6] is Num && x[6]->Num_scale == 2 && abs(x[6]->Num_coeff) < pow10(15)
    &&& x[13] is Text && x[14] is Text && x[19] is Text && x[22] is Text
}

/// The values of a joined row of the database.
pub proof fn lemma_row2(sv: StoresView, l: int, a: int)
    requires 0 <= l < n_l(sv), 0 <= a < n_p(sv),
    ensures ({
        let x = row2(sv, l, a);
        &&& x.len() == 25
        &&& x[1] == Val::Int(l_pkey(sv)[l] as int)
        &&& x[4] == (Val::Num { coeff: l_qty(sv)[l] as int, scale: 2 })
        &&& x[5] == (Val::Num { coeff: l_price(sv)[l] as int, scale: 2 })
        &&& x[6] == (Val::Num { coeff: l_disc(sv)[l] as int, scale: 2 })
        &&& x[13] == Val::Text(l_instr(sv, l))
        &&& x[14] == Val::Text(l_mode(sv, l))
        &&& x[16] == Val::Int(p_key(sv)[a] as int)
        &&& x[19] == Val::Text(p_brand(sv, a))
        &&& x[21] == Val::Int(p_size(sv)[a] as int)
        &&& x[22] == Val::Text(p_cont(sv, a))
    }),
{
    let lr = line_rows(sv)[l];
    let pr = part_rows(sv)[a];
    assert(lr == li::row_at(sv.flat_lineitem, l));
    assert(pr == pi::row_at(sv.flat_part, a));
    let x = lr + pr;
    assert(x[1] == lr[1] && x[4] == lr[4] && x[5] == lr[5] && x[6] == lr[6] && x[13] == lr[13] && x[14] == lr[14]);
    assert(x[16] == pr[0] && x[19] == pr[3] && x[21] == pr[5] && x[22] == pr[6]);
}

/// A joined row of the database has the shape the statement reads.
pub proof fn lemma_row2_shape(sv: StoresView, l: int, a: int)
    requires domains_ok(sv), 0 <= l < n_l(sv), 0 <= a < n_p(sv),
    ensures jshape(row2(sv, l, a)),
{
    lemma_row2(sv, l, a);
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
    assert(num15(l_price(sv)[l]) && num15(l_disc(sv)[l]));
}

/// Every joined row is `row2(l, a)` for a lineitem row `l` and a part row `a`.
pub proof fn lemma_jrows_elem(sv: StoresView, k: int)
    requires 0 <= k < jrows(sv).len(),
    ensures exists|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && jrows(sv)[k] == #[trigger] row2(sv, l, a),
{
    lemma_product_rows_elems(line_rows(sv), part_rows(sv));
    assert(is_concat(jrows(sv)[k], line_rows(sv), part_rows(sv)));
    let (l, a) = choose|i: int, j: int| 0 <= i < line_rows(sv).len() && 0 <= j < part_rows(sv).len()
        && jrows(sv)[k] == #[trigger] line_rows(sv)[i] + #[trigger] part_rows(sv)[j];
    assert(jrows(sv)[k] == row2(sv, l, a));
}

/// The product has a row exactly when both tables do.
pub proof fn lemma_jrows_len(sv: StoresView)
    ensures jrows(sv).len() == n_l(sv) * n_p(sv), (jrows(sv).len() == 0) == (n_l(sv) == 0 || n_p(sv) == 0),
{
    lemma_product_rows_elems(line_rows(sv), part_rows(sv));
    let (x, y) = (n_l(sv) as int, n_p(sv) as int);
    assert((x * y == 0) == (x == 0 || y == 0)) by (nonlinear_arith) requires x >= 0, y >= 0;
}

/// FROM evaluates to the joined rows.
pub proof fn lemma_eval_from(sv: StoresView, db: Database)
    requires tables_of(sv, db),
    ensures eval_query(db, Seq::empty(), q_from()) == Ok::<Relation, SqlError>(jrows(sv)),
{
    let e = Seq::<Val>::empty();
    assert(eval_query(db, e, Query::Table(0)) == Ok::<Relation, SqlError>(line_rows(sv)));
    assert(eval_query(db, e, Query::Table(3)) == Ok::<Relation, SqlError>(part_rows(sv)));
}

// ------------------------------------------------------------------------------------------------ the conjuncts

/// `$k + 10` stays inside int4.
pub open spec fn add_ok(ps: Seq<Literal>, k: int) -> bool { pv(ps, k) + 10 <= 0x7fff_ffff }

/// Branch `k` on a joined row (two-valued: every operand is a non-NULL value).
pub open spec fn jb(ps: Seq<Literal>, k: int, x: Row) -> bool {
    &&& ival(x[16]) == ival(x[1])
    &&& tval(x[19]) == pb(ps, k)
    &&& cont_ok(k, tval(x[22]))
    &&& 100 * pv(ps, k) <= ival(x[4]) && ival(x[4]) <= 100 * (pv(ps, k) + 10)
    &&& 1 <= ival(x[21]) && ival(x[21]) <= size_hi(k)
    &&& (tval(x[14]) == air_lit() || tval(x[14]) == air_reg_lit())
    &&& tval(x[13]) == dip_lit()
}

/// The WHERE condition on a joined row.
pub open spec fn jq(ps: Seq<Literal>) -> spec_fn(Row) -> bool {
    |x: Row| jb(ps, 0, x) || jb(ps, 1, x) || jb(ps, 2, x)
}

/// `Col(c) = '<text>'` on a text value.
proof fn lemma_col_text(db: Database, x: Row, c: nat, t: Seq<u8>)
    requires c < x.len(), x[c as int] is Text,
    ensures eval_pred(db, x, col_eq_text(c, t)) == Ok::<Truth, SqlError>(truth_of(tval(x[c as int]) == t)),
{
    assert(eval_expr(db, x, Expr::Col(c)) == Ok::<Val, SqlError>(x[c as int]));
    assert(eval_expr(db, x, Expr::Lit(Literal::Text(t))) == Ok::<Val, SqlError>(Val::Text(t)));
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(c), Expr::Lit(Literal::Text(t)), tval(x[c as int]), t);
}

/// `p_partkey = l_partkey`.
proof fn lemma_key(db: Database, x: Row)
    requires jshape(x),
    ensures eval_pred(db, x, key_pred()) == Ok::<Truth, SqlError>(truth_of(ival(x[16]) == ival(x[1]))),
{
    assert(eval_expr(db, x, Expr::Col(16)) == Ok::<Val, SqlError>(x[16]));
    assert(eval_expr(db, x, Expr::Col(1)) == Ok::<Val, SqlError>(x[1]));
    lemma_compare_int(ival(x[16]), ival(x[1]));
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(16), Expr::Col(1), x[16], x[1], ival(x[16]), ival(x[1]));
}

/// `p_brand = $k`.
proof fn lemma_brand(db: Database, x: Row, b: Seq<u8>)
    requires jshape(x),
    ensures eval_pred(db, x, brand_pred(Literal::Text(b))) == Ok::<Truth, SqlError>(truth_of(tval(x[19]) == b)),
{
    lemma_col_text(db, x, 19, b);
}

/// The container list of branch `k`.
proof fn lemma_cont(db: Database, x: Row, k: int)
    requires jshape(x),
    ensures eval_pred(db, x, cont_pred(k)) == Ok::<Truth, SqlError>(truth_of(cont_ok(k, tval(x[22])))),
{
    let s = tval(x[22]);
    lemma_col_text(db, x, 22, cont_lit(k, 0));
    lemma_col_text(db, x, 22, cont_lit(k, 1));
    lemma_col_text(db, x, 22, cont_lit(k, 2));
    lemma_col_text(db, x, 22, cont_lit(k, 3));
    lemma_pred_or(db, x, col_eq_text(22, cont_lit(k, 0)), col_eq_text(22, cont_lit(k, 1)), s == cont_lit(k, 0), s == cont_lit(k, 1));
    let o1 = or(col_eq_text(22, cont_lit(k, 0)), col_eq_text(22, cont_lit(k, 1)));
    lemma_pred_or(db, x, o1, col_eq_text(22, cont_lit(k, 2)), s == cont_lit(k, 0) || s == cont_lit(k, 1), s == cont_lit(k, 2));
    let o2 = or(o1, col_eq_text(22, cont_lit(k, 2)));
    lemma_pred_or(db, x, o2, col_eq_text(22, cont_lit(k, 3)),
        s == cont_lit(k, 0) || s == cont_lit(k, 1) || s == cont_lit(k, 2), s == cont_lit(k, 3));
}

/// `CAST(v AS numeric)` of an int4 literal.
proof fn lemma_cast_lit(db: Database, x: Row, v: int)
    requires -0x8000_0000 <= v <= 0x7fff_ffff,
    ensures
        eval_expr(db, x, Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(int4(v))) })
            == Ok::<Val, SqlError>(Val::Num { coeff: v, scale: 0 }),
{
    assert(int_in_range(IntKind::Int4, v));
    assert(eval_expr(db, x, Expr::Lit(int4(v))) == Ok::<Val, SqlError>(Val::Int(v)));
}

/// A quantity (scale 2) against an integer `v` cast to numeric: the order of `q` and `100 v`.
proof fn lemma_qty_cmp(q: int, v: int)
    ensures compare(Val::Num { coeff: q, scale: 2 }, Val::Num { coeff: v, scale: 0 }) == Some(sign(q - 100 * v)),
{
    lemma_compare_num(q, 2, v, 0);
    assert(max_nat(2, 0) == 2);
    lemma_align_same(q, 2);
    assert(pow10(2) == 100) by (compute);
    lemma_align_by(v, 0, 2, 100);
    assert(v * 100 == 100 * v);
}

/// `l_quantity >= $k`.
proof fn lemma_qge(db: Database, x: Row, v: int)
    requires jshape(x), -0x8000_0000 <= v <= 0x7fff_ffff,
    ensures eval_pred(db, x, qge_pred(int4(v))) == Ok::<Truth, SqlError>(truth_of(ival(x[4]) >= 100 * v)),
{
    let q = ival(x[4]);
    let cst = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(int4(v))) };
    lemma_cast_lit(db, x, v);
    assert(eval_expr(db, x, Expr::Col(4)) == Ok::<Val, SqlError>(x[4]));
    lemma_qty_cmp(q, v);
    lemma_pred_cmp(db, x, CmpOp::Ge, Expr::Col(4), cst, x[4], Val::Num { coeff: v, scale: 0 }, q, 100 * v);
}

/// `$k + 10` on an int4 literal: the sum, or `NumericValueOutOfRange` past int4.
proof fn lemma_plus10(db: Database, x: Row, v: int)
    requires -0x8000_0000 <= v <= 0x7fff_ffff,
    ensures
        v + 10 <= 0x7fff_ffff ==> eval_expr(db, x, plus10(int4(v))) == Ok::<Val, SqlError>(Val::Int(v + 10)),
        v + 10 > 0x7fff_ffff ==> eval_expr(db, x, plus10(int4(v))) == Err::<Val, SqlError>(SqlError::NumericValueOutOfRange),
{
    assert(int_in_range(IntKind::Int4, v));
    assert(int_in_range(IntKind::Int4, 10));
    assert(eval_expr(db, x, Expr::Lit(int4(v))) == Ok::<Val, SqlError>(Val::Int(v)));
    assert(eval_expr(db, x, Expr::Lit(int4(10))) == Ok::<Val, SqlError>(Val::Int(10)));
    assert(arith(ArithOp::Add, NumKind::Int4, Val::Int(v), Val::Int(10)) == int_result(IntKind::Int4, v + 10));
}

/// `l_quantity <= $k + 10` inside int4.
proof fn lemma_qle(db: Database, x: Row, v: int)
    requires jshape(x), -0x8000_0000 <= v, v + 10 <= 0x7fff_ffff,
    ensures eval_pred(db, x, qle_pred(int4(v))) == Ok::<Truth, SqlError>(truth_of(ival(x[4]) <= 100 * (v + 10))),
{
    let q = ival(x[4]);
    let cst = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(plus10(int4(v))) };
    lemma_plus10(db, x, v);
    assert(eval_expr(db, x, cst) == Ok::<Val, SqlError>(Val::Num { coeff: v + 10, scale: 0 }));
    assert(eval_expr(db, x, Expr::Col(4)) == Ok::<Val, SqlError>(x[4]));
    lemma_qty_cmp(q, v + 10);
    lemma_pred_cmp(db, x, CmpOp::Le, Expr::Col(4), cst, x[4], Val::Num { coeff: v + 10, scale: 0 }, q, 100 * (v + 10));
}

/// `l_quantity <= $k + 10` past int4: the error.
proof fn lemma_qle_err(db: Database, x: Row, v: int)
    requires jshape(x), v <= 0x7fff_ffff, v + 10 > 0x7fff_ffff,
    ensures eval_pred(db, x, qle_pred(int4(v))) == Err::<Truth, SqlError>(SqlError::NumericValueOutOfRange),
{
    let cst = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(plus10(int4(v))) };
    lemma_plus10(db, x, v);
    assert(eval_expr(db, x, cst) == Err::<Val, SqlError>(SqlError::NumericValueOutOfRange));
    assert(eval_expr(db, x, Expr::Col(4)) == Ok::<Val, SqlError>(x[4]));
}

/// `p_size BETWEEN 1 AND hi`.
proof fn lemma_size(db: Database, x: Row, hi: int)
    requires jshape(x), 1 <= hi <= 15,
    ensures eval_pred(db, x, size_pred(hi)) == Ok::<Truth, SqlError>(truth_of(1 <= ival(x[21]) && ival(x[21]) <= hi)),
{
    let z = ival(x[21]);
    assert(int_in_range(IntKind::Int4, 1));
    assert(int_in_range(IntKind::Int4, hi));
    assert(eval_expr(db, x, Expr::Col(21)) == Ok::<Val, SqlError>(x[21]));
    assert(eval_expr(db, x, Expr::Lit(int4(1))) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(eval_expr(db, x, Expr::Lit(int4(hi))) == Ok::<Val, SqlError>(Val::Int(hi)));
    lemma_compare_int(z, 1);
    lemma_compare_int(z, hi);
    let ge = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(21), b: Expr::Lit(int4(1)) };
    let le = Pred::Cmp { op: CmpOp::Le, a: Expr::Col(21), b: Expr::Lit(int4(hi)) };
    lemma_pred_cmp(db, x, CmpOp::Ge, Expr::Col(21), Expr::Lit(int4(1)), x[21], Val::Int(1), z, 1);
    lemma_pred_cmp(db, x, CmpOp::Le, Expr::Col(21), Expr::Lit(int4(hi)), x[21], Val::Int(hi), z, hi);
    lemma_pred_and(db, x, ge, le, z >= 1, z <= hi);
}

/// `l_shipmode IN ('AIR', 'AIR REG')`.
proof fn lemma_mode(db: Database, x: Row)
    requires jshape(x),
    ensures eval_pred(db, x, mode_pred()) == Ok::<Truth, SqlError>(truth_of(tval(x[14]) == air_lit() || tval(x[14]) == air_reg_lit())),
{
    lemma_col_text(db, x, 14, air_lit());
    lemma_col_text(db, x, 14, air_reg_lit());
    lemma_pred_or(db, x, col_eq_text(14, air_lit()), col_eq_text(14, air_reg_lit()),
        tval(x[14]) == air_lit(), tval(x[14]) == air_reg_lit());
}

/// `l_shipinstruct = 'DELIVER IN PERSON'`.
proof fn lemma_instr(db: Database, x: Row)
    requires jshape(x),
    ensures eval_pred(db, x, instr_pred()) == Ok::<Truth, SqlError>(truth_of(tval(x[13]) == dip_lit())),
{
    lemma_col_text(db, x, 13, dip_lit());
}

/// The parameters of branch `k` as literals.
proof fn lemma_branch_params(ps: Seq<Literal>, k: int)
    requires param_domain(ps), 0 <= k < 3,
    ensures
        ps[2 * k] == Literal::Text(pb(ps, k)),
        ps[2 * k + 1] == int4(pv(ps, k)),
        -0x8000_0000 <= pv(ps, k) <= 0x7fff_ffff,
{
    lemma_params(ps);
    if k == 0 {} else if k == 1 {} else {}
}

/// The first four conjuncts of branch `k`.
proof fn lemma_head4(db: Database, x: Row, ps: Seq<Literal>, k: int)
    requires jshape(x), param_domain(ps), 0 <= k < 3,
    ensures ({
        let pbl = ps[2 * k];
        let pvl = ps[2 * k + 1];
        eval_pred(db, x, and(and(and(key_pred(), brand_pred(pbl)), cont_pred(k)), qge_pred(pvl)))
            == Ok::<Truth, SqlError>(truth_of(ival(x[16]) == ival(x[1]) && tval(x[19]) == pb(ps, k)
                && cont_ok(k, tval(x[22])) && ival(x[4]) >= 100 * pv(ps, k)))
    }),
{
    lemma_branch_params(ps, k);
    let v = pv(ps, k);
    lemma_key(db, x);
    lemma_brand(db, x, pb(ps, k));
    lemma_cont(db, x, k);
    lemma_qge(db, x, v);
    let a1 = ival(x[16]) == ival(x[1]);
    let a2 = tval(x[19]) == pb(ps, k);
    let a3 = cont_ok(k, tval(x[22]));
    let a4 = ival(x[4]) >= 100 * v;
    lemma_pred_and(db, x, key_pred(), brand_pred(ps[2 * k]), a1, a2);
    lemma_pred_and(db, x, and(key_pred(), brand_pred(ps[2 * k])), cont_pred(k), a1 && a2, a3);
    lemma_pred_and(db, x, and(and(key_pred(), brand_pred(ps[2 * k])), cont_pred(k)), qge_pred(ps[2 * k + 1]), a1 && a2 && a3, a4);
}

/// Branch `k` on a joined row, inside int4.
pub proof fn lemma_branch(db: Database, x: Row, ps: Seq<Literal>, k: int)
    requires jshape(x), param_domain(ps), 0 <= k < 3, add_ok(ps, k),
    ensures eval_pred(db, x, branch(k, ps[2 * k], ps[2 * k + 1])) == Ok::<Truth, SqlError>(truth_of(jb(ps, k, x))),
{
    lemma_branch_params(ps, k);
    let v = pv(ps, k);
    let pbl = ps[2 * k];
    let pvl = ps[2 * k + 1];
    lemma_head4(db, x, ps, k);
    let h4 = and(and(and(key_pred(), brand_pred(pbl)), cont_pred(k)), qge_pred(pvl));
    let b4 = ival(x[16]) == ival(x[1]) && tval(x[19]) == pb(ps, k) && cont_ok(k, tval(x[22])) && ival(x[4]) >= 100 * v;
    lemma_qle(db, x, v);
    let b5 = ival(x[4]) <= 100 * (v + 10);
    lemma_pred_and(db, x, h4, qle_pred(pvl), b4, b5);
    assert(head5(k, pbl, pvl) == and(h4, qle_pred(pvl)));
    lemma_size(db, x, 5 * (k + 1));
    let b6 = 1 <= ival(x[21]) && ival(x[21]) <= 5 * (k + 1);
    lemma_pred_and(db, x, head5(k, pbl, pvl), size_pred(5 * (k + 1)), b4 && b5, b6);
    lemma_mode(db, x);
    let b7 = tval(x[14]) == air_lit() || tval(x[14]) == air_reg_lit();
    lemma_pred_and(db, x, and(head5(k, pbl, pvl), size_pred(5 * (k + 1))), mode_pred(), b4 && b5 && b6, b7);
    lemma_instr(db, x);
    let b8 = tval(x[13]) == dip_lit();
    lemma_pred_and(db, x, and(and(head5(k, pbl, pvl), size_pred(5 * (k + 1))), mode_pred()), instr_pred(),
        b4 && b5 && b6 && b7, b8);
}

/// Branch `k` on a joined row, past int4: the error of `$k + 10`.
pub proof fn lemma_branch_err(db: Database, x: Row, ps: Seq<Literal>, k: int)
    requires jshape(x), param_domain(ps), 0 <= k < 3, !add_ok(ps, k),
    ensures eval_pred(db, x, branch(k, ps[2 * k], ps[2 * k + 1])) == Err::<Truth, SqlError>(SqlError::NumericValueOutOfRange),
{
    lemma_branch_params(ps, k);
    let v = pv(ps, k);
    let pbl = ps[2 * k];
    let pvl = ps[2 * k + 1];
    lemma_head4(db, x, ps, k);
    lemma_qle_err(db, x, v);
    let h4 = and(and(and(key_pred(), brand_pred(pbl)), cont_pred(k)), qge_pred(pvl));
    assert(eval_pred(db, x, and(h4, qle_pred(pvl))) == Err::<Truth, SqlError>(SqlError::NumericValueOutOfRange));
    assert(head5(k, pbl, pvl) == and(h4, qle_pred(pvl)));
    let h6 = and(head5(k, pbl, pvl), size_pred(5 * (k + 1)));
    assert(eval_pred(db, x, h6) == Err::<Truth, SqlError>(SqlError::NumericValueOutOfRange));
    assert(eval_pred(db, x, and(h6, mode_pred())) == Err::<Truth, SqlError>(SqlError::NumericValueOutOfRange));
}

/// The WHERE condition on a joined row when every `$k + 10` stays inside int4.
pub proof fn lemma_pred_ok(db: Database, x: Row, ps: Seq<Literal>)
    requires jshape(x), param_domain(ps), adds_ok(ps),
    ensures eval_pred(db, x, q_pred(ps)) == Ok::<Truth, SqlError>(truth_of((jq(ps))(x))),
{
    lemma_branch(db, x, ps, 0);
    lemma_branch(db, x, ps, 1);
    lemma_branch(db, x, ps, 2);
    let b0 = branch(0, ps[0], ps[1]);
    let b1 = branch(1, ps[2], ps[3]);
    let b2 = branch(2, ps[4], ps[5]);
    assert(2 * 0 == 0 && 2 * 0 + 1 == 1 && 2 * 1 == 2 && 2 * 1 + 1 == 3 && 2 * 2 == 4 && 2 * 2 + 1 == 5);
    lemma_pred_or(db, x, b0, b1, jb(ps, 0, x), jb(ps, 1, x));
    lemma_pred_or(db, x, or(b0, b1), b2, jb(ps, 0, x) || jb(ps, 1, x), jb(ps, 2, x));
}

/// The WHERE condition on a joined row when some `$k + 10` leaves int4: that error.
pub proof fn lemma_pred_err(db: Database, x: Row, ps: Seq<Literal>)
    requires jshape(x), param_domain(ps), !adds_ok(ps),
    ensures eval_pred(db, x, q_pred(ps)) == Err::<Truth, SqlError>(SqlError::NumericValueOutOfRange),
{
    let e = SqlError::NumericValueOutOfRange;
    let b0 = branch(0, ps[0], ps[1]);
    let b1 = branch(1, ps[2], ps[3]);
    let b2 = branch(2, ps[4], ps[5]);
    assert(2 * 0 == 0 && 2 * 0 + 1 == 1 && 2 * 1 == 2 && 2 * 1 + 1 == 3 && 2 * 2 == 4 && 2 * 2 + 1 == 5);
    if !add_ok(ps, 0) {
        lemma_branch_err(db, x, ps, 0);
        assert(eval_pred(db, x, or(b0, b1)) == Err::<Truth, SqlError>(e));
    } else if !add_ok(ps, 1) {
        lemma_branch(db, x, ps, 0);
        lemma_branch_err(db, x, ps, 1);
        assert(eval_pred(db, x, or(b0, b1)) == Err::<Truth, SqlError>(e));
    } else {
        assert(!add_ok(ps, 2));
        lemma_branch(db, x, ps, 0);
        lemma_branch(db, x, ps, 1);
        lemma_pred_or(db, x, b0, b1, jb(ps, 0, x), jb(ps, 1, x));
        lemma_branch_err(db, x, ps, 2);
    }
}

// ------------------------------------------------------------------------------------------------ the filter

/// The filter keeps exactly the joined rows satisfying `jq(ps)`.
pub proof fn lemma_eval_filter(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), domains_ok(sv), param_domain(ps), adds_ok(ps),
    ensures eval_query(db, Seq::empty(), q_filter(ps)) == Ok::<Relation, SqlError>(keep(jrows(sv), jq(ps))),
{
    lemma_eval_from(sv, db);
    let rows = jrows(sv);
    let ctx = Seq::<Val>::empty();
    let pred = q_pred(ps);
    let f = jq(ps);
    let truths = Seq::new(rows.len(), |i: int| truth_of(f(rows[i])));
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(ctx + rows[i] =~= rows[i]);
        lemma_jrows_elem(sv, i);
        let (l, a) = choose|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && rows[i] == #[trigger] row2(sv, l, a);
        lemma_row2_shape(sv, l, a);
        lemma_pred_ok(db, rows[i], ps);
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    assert(collect(Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred))) == Ok::<Seq<Truth>, SqlError>(truths));
    lemma_keep_true_keep(rows, truths, f);
}

/// An empty product: the filter keeps nothing, whatever the condition.
pub proof fn lemma_eval_filter_empty(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), jrows(sv).len() == 0,
    ensures eval_query(db, Seq::empty(), q_filter(ps)) == Ok::<Relation, SqlError>(keep(jrows(sv), jq(ps))),
{
    lemma_eval_from(sv, db);
    let rows = jrows(sv);
    let ctx = Seq::<Val>::empty();
    let pred = q_pred(ps);
    assert(Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred)) =~= Seq::<Result<Truth, SqlError>>::empty());
    assert(keep(rows, jq(ps)) =~= Seq::<Row>::empty());
    assert(keep_true(rows, Seq::<Truth>::empty()) =~= Seq::<Row>::empty());
}

/// Some `$k + 10` leaves int4 on a non-empty product: the filter is that error.
pub proof fn lemma_filter_err(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), domains_ok(sv), param_domain(ps), !adds_ok(ps), jrows(sv).len() > 0,
    ensures eval_query(db, Seq::empty(), q_filter(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    let e = SqlError::NumericValueOutOfRange;
    let ctx = Seq::<Val>::empty();
    let rows = jrows(sv);
    let pred = q_pred(ps);
    lemma_eval_from(sv, db);
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, ctx + rows[k], pred) == Err::<Truth, SqlError>(e) by {
        assert(ctx + rows[k] =~= rows[k]);
        lemma_jrows_elem(sv, k);
        let (l, a) = choose|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && rows[k] == #[trigger] row2(sv, l, a);
        lemma_row2_shape(sv, l, a);
        lemma_pred_err(db, rows[k], ps);
    }
    assert(eval_pred(db, ctx + rows[0], pred) == Err::<Truth, SqlError>(e));
    lemma_filter_err_uniform(db, ctx, pred, Box::new(q_from()), rows, e, 0);
}

// ------------------------------------------------------------------------------------------------ sums

/// On `row2(l, a)` the condition is the key match and some branch holding on the part and lineitem rows.
pub proof fn lemma_jq_row2(sv: StoresView, ps: Seq<Literal>, l: int, a: int)
    requires 0 <= l < n_l(sv), 0 <= a < n_p(sv),
    ensures (jq(ps))(row2(sv, l, a)) == (p_key(sv)[a] == l_pkey(sv)[l] && lq(sv, ps, a, l)),
{
    lemma_row2(sv, l, a);
}

/// `l_extendedprice * (1 - l_discount)` of a joined row (scale-4 coefficient).
pub open spec fn jvol(x: Row) -> int { ival(x[5]) * (100 - ival(x[6])) }

/// Joined-row terms of the three totals (zero off the condition).
pub open spec fn jt_cnt(ps: Seq<Literal>) -> spec_fn(Row) -> int { |x: Row| if (jq(ps))(x) { 1int } else { 0int } }
pub open spec fn jt_all(ps: Seq<Literal>) -> spec_fn(Row) -> int { |x: Row| if (jq(ps))(x) { jvol(x) } else { 0int } }
pub open spec fn jt_abs(ps: Seq<Literal>) -> spec_fn(Row) -> int { |x: Row| if (jq(ps))(x) { abs(jvol(x)) } else { 0int } }

/// The sum over a sequence built by `Seq::new` is the range sum of the terms of its elements.
pub proof fn lemma_sum_of_new(n: nat, g: spec_fn(int) -> Row, h: spec_fn(Row) -> int)
    ensures sum_of(Seq::new(n, g), h) == range_sum(0, n as int, |i: int| h(g(i))),
    decreases n,
{
    if n > 0 {
        let s = Seq::new(n, g);
        lemma_sum_of_new((n - 1) as nat, g, h);
        assert(s.drop_last() =~= Seq::new((n - 1) as nat, g));
    } else {
        assert(Seq::new(n, g) =~= Seq::<Row>::empty());
    }
}

/// A sum over the joined rows whose terms vanish off the key match is the range sum of the term at each lineitem
/// row's part row (0 for a lineitem row without a part).
pub proof fn lemma_jsum(sv: StoresView, h: spec_fn(Row) -> int, f: spec_fn(int) -> int)
    requires
        keys_unique(p_key(sv)),
        forall|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && h(#[trigger] row2(sv, l, a)) != 0
            ==> p_key(sv)[a] == l_pkey(sv)[l],
        forall|l: int| 0 <= l < n_l(sv) ==> #[trigger] f(l) == if has_part(sv, l) { h(row2(sv, l, part_of(sv, l))) } else { 0 },
    ensures sum_of(jrows(sv), h) == range_sum(0, n_l(sv) as int, f),
{
    let lr = line_rows(sv);
    let pr = part_rows(sv);
    assert(col_unique(pr, 0)) by {
        assert forall|p: int, q: int| 0 <= p < pr.len() && 0 <= q < pr.len() && #[trigger] pr[p][0] == #[trigger] pr[q][0] implies p == q by {
            assert(pr[p] == pi::row_at(sv.flat_part, p));
            assert(pr[q] == pi::row_at(sv.flat_part, q));
        }
    }
    assert forall|p: int, q: int| 0 <= p < lr.len() && 0 <= q < pr.len() && h(#[trigger] lr[p] + #[trigger] pr[q]) != 0
        implies pr[q][0] == lr[p][1] by {
        assert(lr[p] + pr[q] == row2(sv, p, q));
        lemma_row2(sv, p, q);
        assert((lr[p] + pr[q])[1] == lr[p][1] && (lr[p] + pr[q])[16] == pr[q][0]);
    }
    lemma_sum_product_right(lr, pr, h, 1, 0);
    let phi = |x: Row| at_pick(pr, 0, x[1], |y: Row| h(x + y));
    let g = |i: int| li::row_at(sv.flat_lineitem, i);
    assert(lr == Seq::new(n_l(sv), g));
    lemma_sum_of_new(n_l(sv), g, phi);
    let gl = |i: int| phi(g(i));
    assert forall|l: int| 0 <= l < n_l(sv) implies #[trigger] gl(l) == f(l) by {
        let x = lr[l];
        assert(g(l) == x);
        let hx = |y: Row| h(x + y);
        let v = Val::Int(l_pkey(sv)[l] as int);
        assert(x == li::row_at(sv.flat_lineitem, l));
        assert(x[1] == v);
        assert(gl(l) == at_pick(pr, 0, v, hx));
        lemma_pick(pr, 0, v);
        if has_part(sv, l) {
            lemma_part_of(sv, l);
            let a0 = part_of(sv, l);
            assert(pr[a0] == pi::row_at(sv.flat_part, a0));
            assert(pr[a0][0] == v);
            assert(has_pick(pr, 0, v));
            assert(pick(pr, 0, v) == a0);
            assert(hx(pr[a0]) == h(row2(sv, l, a0)));
        } else {
            assert(!has_pick(pr, 0, v)) by {
                if has_pick(pr, 0, v) {
                    let q = choose|q: int| 0 <= q < pr.len() && #[trigger] pr[q][0] == v;
                    assert(pr[q] == pi::row_at(sv.flat_part, q));
                    assert(p_key(sv)[q] == l_pkey(sv)[l]);
                }
            }
        }
    }
    lemma_range_sum_ext(0, n_l(sv) as int, gl, f);
}

/// The joined row of a lineitem row and its part row: the condition is `lq`, the volume the lineitem row's.
pub proof fn lemma_row2_part(sv: StoresView, ps: Seq<Literal>, l: int)
    requires keys_unique(p_key(sv)), 0 <= l < n_l(sv), has_part(sv, l),
    ensures ({
        let x = row2(sv, l, part_of(sv, l));
        &&& (jq(ps))(x) == qual(sv, ps, l)
        &&& jvol(x) == vol(sv, l)
    }),
{
    lemma_part_of(sv, l);
    let a = part_of(sv, l);
    lemma_row2(sv, l, a);
    lemma_jq_row2(sv, ps, l, a);
}

/// A joined-row term vanishing off the condition sums, over the kept rows, to the range sum of `f`.
proof fn lemma_term(sv: StoresView, ps: Seq<Literal>, jt: spec_fn(Row) -> int, f: spec_fn(int) -> int)
    requires
        keys_unique(p_key(sv)),
        forall|x: Row| !(#[trigger] (jq(ps))(x)) ==> jt(x) == 0,
        forall|l: int| 0 <= l < n_l(sv) ==> #[trigger] f(l) == if has_part(sv, l) { jt(row2(sv, l, part_of(sv, l))) } else { 0 },
    ensures sum_of(keep(jrows(sv), jq(ps)), jt) == range_sum(0, n_l(sv) as int, f),
{
    let rows = jrows(sv);
    assert forall|i: int| 0 <= i < rows.len() && !(jq(ps))(#[trigger] rows[i]) implies jt(rows[i]) == 0 by {}
    lemma_sum_of_keep(rows, jq(ps), jt);
    assert forall|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && jt(#[trigger] row2(sv, l, a)) != 0
        implies p_key(sv)[a] == l_pkey(sv)[l] by {
        lemma_jq_row2(sv, ps, l, a);
    }
    lemma_jsum(sv, jt, f);
}

/// The sums of the three joined-row terms over the kept rows are the per-lineitem totals.
pub proof fn lemma_kept_sums(sv: StoresView, ps: Seq<Literal>)
    requires keys_unique(p_key(sv)),
    ensures ({
        let k = keep(jrows(sv), jq(ps));
        let t = tot(sv, ps, 0, n_l(sv) as int);
        &&& sum_of(k, jt_cnt(ps)) == t.cnt
        &&& sum_of(k, jt_all(ps)) == t.s_all
        &&& sum_of(k, jt_abs(ps)) == t.a_all
    }),
{
    assert forall|l: int| 0 <= l < n_l(sv) && has_part(sv, l) implies {
        let x = row2(sv, l, part_of(sv, l));
        &&& (jq(ps))(x) == qual(sv, ps, l)
        &&& jvol(x) == vol(sv, l)
    } by {
        lemma_row2_part(sv, ps, l);
    }
    lemma_term(sv, ps, jt_cnt(ps), f_cnt(sv, ps));
    lemma_term(sv, ps, jt_all(ps), f_all(sv, ps));
    lemma_term(sv, ps, jt_abs(ps), f_abs(sv, ps));
}

/// Every kept row is the joined row of a lineitem row and a part row, and satisfies the condition.
pub proof fn lemma_kept_rows(sv: StoresView, ps: Seq<Literal>)
    ensures
        forall|i: int| 0 <= i < keep(jrows(sv), jq(ps)).len() ==> (jq(ps))(#[trigger] keep(jrows(sv), jq(ps))[i])
            && exists|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && keep(jrows(sv), jq(ps))[i] == #[trigger] row2(sv, l, a),
{
    let rows = jrows(sv);
    let k = keep(rows, jq(ps));
    lemma_keep_members(rows, jq(ps));
    assert forall|i: int| 0 <= i < k.len() implies (jq(ps))(#[trigger] k[i])
        && exists|l: int, a: int| 0 <= l < n_l(sv) && 0 <= a < n_p(sv) && k[i] == #[trigger] row2(sv, l, a) by {
        assert(rows.contains(k[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == k[i];
        lemma_jrows_elem(sv, m);
    }
}

} // verus!
