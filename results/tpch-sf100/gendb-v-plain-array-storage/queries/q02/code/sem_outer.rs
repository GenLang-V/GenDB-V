//! The outer query: the rows of `FROM part, supplier, partsupp, nation, region` (`from5`, the `row5` of index
//! tuples), the WHERE condition on each row (`lemma_outer_row`: a `LIKE` error of the row's part is the row's
//! error, otherwise the row is kept exactly when `outer_keep` holds), and the body's value: without `LIKE` errors
//! the projection of `keep(from5, outer_keep)` (`lemma_body_ok`), otherwise the first `LIKE` error in part-row
//! order when every other table is non-empty (`lemma_body_err`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::chars::*;
use crate::spec::fns::*;
use crate::spec::fns::like::*;
use crate::link::join::{keep, lemma_product_index, lemma_product_assoc};
use crate::link::expr::{lemma_pred_cmp, lemma_pred_text_cmp, lemma_pred_and, lemma_compare_int, ival, tval};
use crate::link::query::{select, lemma_project_cols};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise, lemma_collect_first_err};
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem_ast::*;
use crate::agent::sem_sub::*;
use crate::agent::common::relations::*;
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_partsupp::interface as psi;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_region::interface as ri;

verus! {

/// A row of the outer FROM: part `a`, supplier `b`, partsupp `c`, nation `d`, region `e`.
pub open spec fn row5(sv: StoresView, a: int, b: int, c: int, d: int, e: int) -> Row {
    part_rows(sv)[a] + supp_rows(sv)[b] + ps_rows(sv)[c] + nat_rows(sv)[d] + reg_rows(sv)[e]
}

pub open spec fn in5(sv: StoresView, a: int, b: int, c: int, d: int, e: int) -> bool {
    0 <= a < part_n(sv) && 0 <= b < supp_n(sv) && 0 <= c < ps_n(sv) && 0 <= d < nat_n(sv) && 0 <= e < reg_n(sv)
}

/// The outer FROM relation (left-deep product).
pub open spec fn from5(sv: StoresView) -> Seq<Row> {
    product_rows(product_rows(product_rows(product_rows(part_rows(sv), supp_rows(sv)), ps_rows(sv)), nat_rows(sv)), reg_rows(sv))
}

/// `s LIKE pat` (escape backslash) on a text value.
pub open spec fn like_res(s: Seq<u8>, pat: Seq<u8>) -> Result<Val, SqlError> {
    like_value(Val::Text(s), Val::Text(pat), Val::Text(backslash()))
}

/// Part row `a` passes the part conditions `p_size = v AND p_type LIKE pat`.
pub open spec fn part_ok(sv: StoresView, v: int, pat: Seq<u8>, a: int) -> bool {
    p_sizes(sv)[a] == v && like_res(p_type(sv, a), pat) == Ok::<Val, SqlError>(Val::Bool(true))
}

/// The outer WHERE as a two-valued condition on a row (meaningful on `row5` rows without a `LIKE` error).
pub open spec fn outer_keep(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>) -> spec_fn(Row) -> bool {
    |x: Row| x[0] == x[16] && x[9] == x[17] && x[5] == Val::Int(v)
        && like_res(tval(x[4]), pat) == Ok::<Val, SqlError>(Val::Bool(true))
        && x[12] == x[21] && x[23] == x[25] && x[26] == Val::Text(rp)
        && is_min_cost(sv, rp, ival(x[0]), ival(x[19]))
}

// ------------------------------------------------------------------------------------------ rows

/// The values of an outer FROM row that the query reads.
pub proof fn lemma_row5(sv: StoresView, a: int, b: int, c: int, d: int, e: int)
    requires stores_wf(sv), in5(sv, a, b, c, d, e),
    ensures
        row5(sv, a, b, c, d, e).len() == 28,
        row5(sv, a, b, c, d, e)[0] == Val::Int(p_keys(sv)[a] as int),
        row5(sv, a, b, c, d, e)[2] == part_rows(sv)[a][2],
        row5(sv, a, b, c, d, e)[4] == Val::Text(p_type(sv, a)),
        row5(sv, a, b, c, d, e)[5] == Val::Int(p_sizes(sv)[a] as int),
        row5(sv, a, b, c, d, e)[9] == Val::Int(s_keys(sv)[b] as int),
        row5(sv, a, b, c, d, e)[10] == supp_rows(sv)[b][1],
        row5(sv, a, b, c, d, e)[11] == supp_rows(sv)[b][2],
        row5(sv, a, b, c, d, e)[12] == Val::Int(s_nks(sv)[b] as int),
        row5(sv, a, b, c, d, e)[13] == supp_rows(sv)[b][4],
        row5(sv, a, b, c, d, e)[14] == (Val::Num { coeff: s_accts(sv)[b] as int, scale: 2 }),
        row5(sv, a, b, c, d, e)[15] == supp_rows(sv)[b][6],
        row5(sv, a, b, c, d, e)[16] == Val::Int(ps_pkeys(sv)[c] as int),
        row5(sv, a, b, c, d, e)[17] == Val::Int(ps_skeys(sv)[c] as int),
        row5(sv, a, b, c, d, e)[19] == (Val::Num { coeff: ps_costs(sv)[c] as int, scale: 2 }),
        row5(sv, a, b, c, d, e)[21] == Val::Int(n_keys(sv)[d] as int),
        row5(sv, a, b, c, d, e)[22] == nat_rows(sv)[d][1],
        row5(sv, a, b, c, d, e)[23] == Val::Int(n_rks(sv)[d] as int),
        row5(sv, a, b, c, d, e)[25] == Val::Int(r_keys(sv)[e] as int),
        row5(sv, a, b, c, d, e)[26] == Val::Text(r_name(sv, e)),
{
    let p = part_rows(sv)[a];
    let s = supp_rows(sv)[b];
    let q = ps_rows(sv)[c];
    let n = nat_rows(sv)[d];
    let r = reg_rows(sv)[e];
    assert(p == pi::row_at(sv.flat_part, a));
    assert(s == si::row_at(sv.flat_supplier, b));
    assert(q == psi::row_at(sv.flat_partsupp, c));
    assert(n == ni::row_at(sv.flat_nation, d));
    assert(r == ri::row_at(sv.flat_region, e));
    assert(p.len() == 9 && s.len() == 7 && q.len() == 5 && n.len() == 4 && r.len() == 3);
    let x = row5(sv, a, b, c, d, e);
    assert(x[0] == p[0] && x[2] == p[2] && x[4] == p[4] && x[5] == p[5]);
    assert(x[9] == s[0] && x[10] == s[1] && x[11] == s[2] && x[12] == s[3] && x[13] == s[4] && x[14] == s[5] && x[15] == s[6]);
    assert(x[16] == q[0] && x[17] == q[1] && x[19] == q[3]);
    assert(x[21] == n[0] && x[22] == n[1] && x[23] == n[2]);
    assert(x[25] == r[0] && x[26] == r[1]);
}

/// The rows of the outer FROM are exactly the `row5` of index tuples in range.
pub proof fn lemma_from5_contains(sv: StoresView, x: Row)
    requires stores_wf(sv),
    ensures from5(sv).contains(x) <==> exists|a: int, b: int, c: int, d: int, e: int| in5(sv, a, b, c, d, e) && x == #[trigger] row5(sv, a, b, c, d, e),
{
    let (p, s, q, n, r) = (part_rows(sv), supp_rows(sv), ps_rows(sv), nat_rows(sv), reg_rows(sv));
    let l1 = product_rows(p, s);
    let l2 = product_rows(l1, q);
    let l3 = product_rows(l2, n);
    lemma_product_contains(l3, r, x);
    if from5(sv).contains(x) {
        let (i3, e) = choose|i: int, e: int| 0 <= i < l3.len() && 0 <= e < r.len() && x == #[trigger] l3[i] + #[trigger] r[e];
        assert(l3.contains(l3[i3]));
        lemma_product_contains(l2, n, l3[i3]);
        let (i2, d) = choose|i: int, d: int| 0 <= i < l2.len() && 0 <= d < n.len() && l3[i3] == #[trigger] l2[i] + #[trigger] n[d];
        assert(l2.contains(l2[i2]));
        lemma_product_contains(l1, q, l2[i2]);
        let (i1, c) = choose|i: int, c: int| 0 <= i < l1.len() && 0 <= c < q.len() && l2[i2] == #[trigger] l1[i] + #[trigger] q[c];
        assert(l1.contains(l1[i1]));
        lemma_product_contains(p, s, l1[i1]);
        let (a, b) = choose|a: int, b: int| 0 <= a < p.len() && 0 <= b < s.len() && l1[i1] == #[trigger] p[a] + #[trigger] s[b];
        assert(x == row5(sv, a, b, c, d, e));
    }
    if exists|a: int, b: int, c: int, d: int, e: int| in5(sv, a, b, c, d, e) && x == #[trigger] row5(sv, a, b, c, d, e) {
        let (a, b, c, d, e) = choose|a: int, b: int, c: int, d: int, e: int| in5(sv, a, b, c, d, e) && x == #[trigger] row5(sv, a, b, c, d, e);
        let x1 = p[a] + s[b];
        let x2 = x1 + q[c];
        let x3 = x2 + n[d];
        lemma_product_contains(p, s, x1);
        lemma_product_contains(l1, q, x2);
        lemma_product_contains(l2, n, x3);
        let i1 = choose|i: int| 0 <= i < l1.len() && l1[i] == x1;
        assert(l2.contains(x2)) by { assert(x2 == l1[i1] + q[c]); }
        let i2 = choose|i: int| 0 <= i < l2.len() && l2[i] == x2;
        assert(l3.contains(x3)) by { assert(x3 == l2[i2] + n[d]); }
        let i3 = choose|i: int| 0 <= i < l3.len() && l3[i] == x3;
        assert(x == l3[i3] + r[e]);
    }
}

/// `FROM part, supplier, partsupp, nation, region` evaluates to `from5`.
pub proof fn lemma_eval_from5(db: Database, sv: StoresView)
    requires tables_of(sv, db),
    ensures eval_query(db, Seq::empty(), outer_from()) == Ok::<Relation, SqlError>(from5(sv)),
{
    let ctx = Seq::<Val>::empty();
    assert(eval_query(db, ctx, Query::Table(3)) == Ok::<Relation, SqlError>(part_rows(sv)));
    assert(eval_query(db, ctx, Query::Table(4)) == Ok::<Relation, SqlError>(ps_rows(sv)));
    assert(eval_query(db, ctx, Query::Table(5)) == Ok::<Relation, SqlError>(supp_rows(sv)));
    assert(eval_query(db, ctx, Query::Table(6)) == Ok::<Relation, SqlError>(nat_rows(sv)));
    assert(eval_query(db, ctx, Query::Table(7)) == Ok::<Relation, SqlError>(reg_rows(sv)));
    let q1 = prod(Query::Table(3), Query::Table(5));
    let q2 = prod(q1, Query::Table(4));
    let q3 = prod(q2, Query::Table(6));
    let l1 = product_rows(part_rows(sv), supp_rows(sv));
    let l2 = product_rows(l1, ps_rows(sv));
    assert(eval_query(db, ctx, q1) == Ok::<Relation, SqlError>(l1));
    assert(eval_query(db, ctx, q2) == Ok::<Relation, SqlError>(l2));
    assert(eval_query(db, ctx, q3) == Ok::<Relation, SqlError>(product_rows(l2, nat_rows(sv))));
}

// ------------------------------------------------------------------------------------------ the WHERE on one row

/// The escape string is one character, so `like_res` is a boolean or the matcher's error.
pub proof fn lemma_like_res(s: Seq<u8>, pat: Seq<u8>)
    ensures
        like_res(s, pat) is Ok ==> like_res(s, pat)->Ok_0 is Bool,
        chars(backslash()) == seq![backslash()],
{
    let bs = backslash();
    assert(bs.drop_last() =~= Seq::<u8>::empty());
    assert(chars(Seq::<u8>::empty()) == Seq::<Seq<u8>>::empty());
    assert(!is_cont(bs.last()));
    assert(chars(bs) =~= seq![bs]);
}

/// The three arguments of `p_type LIKE $2` evaluate to the type, the pattern and the escape.
proof fn lemma_like_args(db: Database, x: Row, pat: Seq<u8>, s: Seq<u8>)
    requires x.len() == 28, x[4] == Val::Text(s),
    ensures
        eval_exprs(db, x, seq![Expr::Col(4), Expr::Lit(Literal::Text(pat)), Expr::Lit(Literal::Text(backslash()))])
            == Ok::<Row, SqlError>(seq![Val::Text(s), Val::Text(pat), Val::Text(backslash())]),
{
    let e0 = Expr::Col(4);
    let e1 = Expr::Lit(Literal::Text(pat));
    let e2 = Expr::Lit(Literal::Text(backslash()));
    let a1 = seq![e0];
    let a2 = seq![e0, e1];
    let a3 = seq![e0, e1, e2];
    lemma_eval_exprs_empty(db, x);
    assert(a1.drop_last() =~= Seq::<Expr>::empty());
    lemma_eval_exprs_step(db, x, a1);
    assert(eval_exprs(db, x, a1) == Ok::<Row, SqlError>(seq![Val::Text(s)])) by {
        assert(Seq::<Val>::empty().push(Val::Text(s)) =~= seq![Val::Text(s)]);
    }
    assert(a2.drop_last() =~= a1);
    lemma_eval_exprs_step(db, x, a2);
    assert(eval_exprs(db, x, a2) == Ok::<Row, SqlError>(seq![Val::Text(s), Val::Text(pat)])) by {
        assert(seq![Val::Text(s)].push(Val::Text(pat)) =~= seq![Val::Text(s), Val::Text(pat)]);
    }
    assert(a3.drop_last() =~= a2);
    lemma_eval_exprs_step(db, x, a3);
    assert(seq![Val::Text(s), Val::Text(pat)].push(Val::Text(backslash())) =~= seq![Val::Text(s), Val::Text(pat), Val::Text(backslash())]);
}

/// `p_type LIKE $2` as a condition on row `x`.
proof fn lemma_like_pred(db: Database, x: Row, v: int, pat: Seq<u8>, rp: Seq<u8>, s: Seq<u8>)
    requires x.len() == 28, x[4] == Val::Text(s),
    ensures
        like_res(s, pat) matches Err(err) ==> eval_pred(db, x, Pred::OfBool(like_expr(lits(v, pat, rp)))) == Err::<Truth, SqlError>(err),
        like_res(s, pat) matches Ok(Val::Bool(lb)) ==> eval_pred(db, x, Pred::OfBool(like_expr(lits(v, pat, rp)))) == Ok::<Truth, SqlError>(truth_of(lb)),
{
    hide(like_value);
    let ps = lits(v, pat, rp);
    assert(ps[1] == Literal::Text(pat));
    let args = seq![Expr::Col(4), Expr::Lit(Literal::Text(pat)), Expr::Lit(Literal::Text(backslash()))];
    assert(like_expr(ps) == Expr::Call { f: ScalarFn::Like, args });
    lemma_like_args(db, x, pat, s);
    let vals = seq![Val::Text(s), Val::Text(pat), Val::Text(backslash())];
    assert(apply_fn(ScalarFn::Like, vals) == like_res(s, pat));
    assert(eval_expr(db, x, like_expr(ps)) == like_res(s, pat));
}

/// An error of the left operand of `AND` is the conjunction's error.
proof fn lemma_and_err(db: Database, env: Row, p: Pred, q: Pred, err: SqlError)
    requires eval_pred(db, env, p) == Err::<Truth, SqlError>(err),
    ensures eval_pred(db, env, and(p, q)) == Err::<Truth, SqlError>(err),
{
}

/// An error of the right operand after a value of the left is the conjunction's error.
proof fn lemma_and_err_right(db: Database, env: Row, p: Pred, q: Pred, t: Truth, err: SqlError)
    requires eval_pred(db, env, p) == Ok::<Truth, SqlError>(t), eval_pred(db, env, q) == Err::<Truth, SqlError>(err),
    ensures eval_pred(db, env, and(p, q)) == Err::<Truth, SqlError>(err),
{
}

/// A two-valued left operand and a three-valued right one: the conjunction is true exactly when both are.
proof fn lemma_and_true(db: Database, env: Row, p: Pred, q: Pred, x: bool, t: Truth)
    requires eval_pred(db, env, p) == Ok::<Truth, SqlError>(truth_of(x)), eval_pred(db, env, q) == Ok::<Truth, SqlError>(t),
    ensures
        eval_pred(db, env, and(p, q)) is Ok,
        (eval_pred(db, env, and(p, q))->Ok_0 is True) == (x && t is True),
{
}

/// The seven conditions of the outer WHERE before the subquery comparison, on row `x` with the given values.
pub open spec fn filters_hold(x: Row, v: int, pat: Seq<u8>, rp: Seq<u8>) -> bool {
    x[0] == x[16] && x[9] == x[17] && x[5] == Val::Int(v)
        && like_res(tval(x[4]), pat) == Ok::<Val, SqlError>(Val::Bool(true))
        && x[12] == x[21] && x[23] == x[25] && x[26] == Val::Text(rp)
}

/// The conditions before the subquery comparison on row `row5(a, b, c, d, e)`.
proof fn lemma_outer_filters(db: Database, sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>,
    a: int, b: int, c: int, d: int, e: int)
    requires
        stores_wf(sv),
        in5(sv, a, b, c, d, e),
        int_in_range(IntKind::Int4, v),
    ensures
        like_res(p_type(sv, a), pat) matches Err(err) ==>
            eval_pred(db, row5(sv, a, b, c, d, e), outer_filters(lits(v, pat, rp))) == Err::<Truth, SqlError>(err),
        like_res(p_type(sv, a), pat) is Ok ==>
            eval_pred(db, row5(sv, a, b, c, d, e), outer_filters(lits(v, pat, rp)))
                == Ok::<Truth, SqlError>(truth_of(filters_hold(row5(sv, a, b, c, d, e), v, pat, rp))),
{
    hide(like_value);
    let x = row5(sv, a, b, c, d, e);
    let ps = lits(v, pat, rp);
    lemma_row5(sv, a, b, c, d, e);
    let (pk, sz, sk, snk) = (p_keys(sv)[a] as int, p_sizes(sv)[a] as int, s_keys(sv)[b] as int, s_nks(sv)[b] as int);
    let (cpk, csk) = (ps_pkeys(sv)[c] as int, ps_skeys(sv)[c] as int);
    let (nk, nrk, rk) = (n_keys(sv)[d] as int, n_rks(sv)[d] as int, r_keys(sv)[e] as int);
    lemma_compare_int(pk, cpk);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(0), Expr::Col(16), Val::Int(pk), Val::Int(cpk), pk, cpk);
    lemma_compare_int(sk, csk);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(9), Expr::Col(17), Val::Int(sk), Val::Int(csk), sk, csk);
    lemma_compare_int(sz, v);
    assert(ps[0] == Literal::Int { v, kind: IntKind::Int4 });
    assert(eval_expr(db, x, Expr::Lit(ps[0])) == Ok::<Val, SqlError>(Val::Int(v)));
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(5), Expr::Lit(ps[0]), Val::Int(sz), Val::Int(v), sz, v);
    lemma_compare_int(snk, nk);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(12), Expr::Col(21), Val::Int(snk), Val::Int(nk), snk, nk);
    lemma_compare_int(nrk, rk);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(23), Expr::Col(25), Val::Int(nrk), Val::Int(rk), nrk, rk);
    assert(ps[2] == Literal::Text(rp));
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(26), Expr::Lit(Literal::Text(rp)), r_name(sv, e), rp);
    lemma_like_pred(db, x, v, pat, rp, p_type(sv, a));
    lemma_like_res(p_type(sv, a), pat);
    let p1 = and(eq_cols(0, 16), eq_cols(9, 17));
    let p2 = and(p1, eq_lit(5, ps[0]));
    let pl = Pred::OfBool(like_expr(ps));
    let p3 = and(p2, pl);
    let p4 = and(p3, eq_cols(12, 21));
    let p5 = and(p4, eq_cols(23, 25));
    let pf = and(p5, eq_lit(26, ps[2]));
    assert(outer_filters(ps) == pf);
    lemma_pred_and(db, x, eq_cols(0, 16), eq_cols(9, 17), pk == cpk, sk == csk);
    let c2 = pk == cpk && sk == csk && sz == v;
    lemma_pred_and(db, x, p1, eq_lit(5, ps[0]), pk == cpk && sk == csk, sz == v);
    match like_res(p_type(sv, a), pat) {
        Err(err) => {
            lemma_and_err_right(db, x, p2, pl, truth_of(c2), err);
            lemma_and_err(db, x, p3, eq_cols(12, 21), err);
            lemma_and_err(db, x, p4, eq_cols(23, 25), err);
            lemma_and_err(db, x, p5, eq_lit(26, ps[2]), err);
        },
        Ok(lv) => {
            let lb = lv->Bool_0;
            lemma_pred_and(db, x, p2, pl, c2, lb);
            lemma_pred_and(db, x, p3, eq_cols(12, 21), c2 && lb, snk == nk);
            lemma_pred_and(db, x, p4, eq_cols(23, 25), c2 && lb && snk == nk, nrk == rk);
            lemma_pred_and(db, x, p5, eq_lit(26, ps[2]), c2 && lb && snk == nk && nrk == rk, r_name(sv, e) == rp);
            assert(tval(x[4]) == p_type(sv, a));
            assert((like_res(tval(x[4]), pat) == Ok::<Val, SqlError>(Val::Bool(true))) == lb);
        },
    }
}

/// The outer WHERE on row `row5(a, b, c, d, e)`: the part's `LIKE` error, or a truth that is `True` exactly when
/// `outer_keep` holds.
pub proof fn lemma_outer_row(db: Database, sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>,
    a: int, b: int, c: int, d: int, e: int)
    requires
        tables_of(sv, db),
        stores_wf(sv),
        in5(sv, a, b, c, d, e),
        int_in_range(IntKind::Int4, v),
    ensures
        like_res(p_type(sv, a), pat) matches Err(err) ==>
            eval_pred(db, row5(sv, a, b, c, d, e), outer_pred(lits(v, pat, rp))) == Err::<Truth, SqlError>(err),
        like_res(p_type(sv, a), pat) is Ok ==> {
            &&& eval_pred(db, row5(sv, a, b, c, d, e), outer_pred(lits(v, pat, rp))) is Ok
            &&& (eval_pred(db, row5(sv, a, b, c, d, e), outer_pred(lits(v, pat, rp)))->Ok_0 is True)
                == (outer_keep(sv, v, pat, rp))(row5(sv, a, b, c, d, e))
        },
{
    hide(like_value);
    hide(is_min_cost);
    hide(filters_hold);
    hide(outer_filters);
    hide(cost_eq_min);
    let x = row5(sv, a, b, c, d, e);
    let ps = lits(v, pat, rp);
    lemma_row5(sv, a, b, c, d, e);
    lemma_outer_filters(db, sv, v, pat, rp, a, b, c, d, e);
    let pf = outer_filters(ps);
    assert(outer_pred(ps) == and(pf, cost_eq_min(ps)));
    match like_res(p_type(sv, a), pat) {
        Err(err) => {
            lemma_and_err(db, x, pf, cost_eq_min(ps), err);
        },
        Ok(lv) => {
            let pk = p_keys(sv)[a] as int;
            let cost = ps_costs(sv)[c] as int;
            lemma_cost_eq_min(db, sv, v, pat, rp, x, pk, cost);
            let t2 = eval_pred(db, x, cost_eq_min(ps))->Ok_0;
            lemma_and_true(db, x, pf, cost_eq_min(ps), filters_hold(x, v, pat, rp), t2);
            assert(ival(x[0]) == pk && ival(x[19]) == cost);
            reveal(filters_hold);
        },
    }
}

// ------------------------------------------------------------------------------------------ the body

/// No row of the FROM has a part with a `LIKE` error.
pub open spec fn like_total(sv: StoresView, pat: Seq<u8>) -> bool {
    forall|a: int, b: int, c: int, d: int, e: int| #[trigger] in5(sv, a, b, c, d, e) ==> like_res(p_type(sv, a), pat) is Ok
}

/// Without `LIKE` errors, the WHERE keeps `keep(from5, outer_keep)`.
pub proof fn lemma_filter_ok(db: Database, sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>)
    requires
        tables_of(sv, db),
        stores_wf(sv),
        int_in_range(IntKind::Int4, v),
        like_total(sv, pat),
    ensures
        eval_query(db, Seq::empty(), filtered(lits(v, pat, rp))) == Ok::<Relation, SqlError>(keep(from5(sv), outer_keep(sv, v, pat, rp))),
{
    hide(like_value);
    hide(is_min_cost);
    let ctx = Seq::<Val>::empty();
    let rows = from5(sv);
    let f = outer_keep(sv, v, pat, rp);
    let pred = outer_pred(lits(v, pat, rp));
    lemma_eval_from5(db, sv);
    let rs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred));
    let truths = Seq::new(rows.len(), |i: int| rs[i]->Ok_0);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(truths[i]) && ((truths[i] is True) == f(rows[i])) by {
        assert(ctx + rows[i] =~= rows[i]);
        assert(rows.contains(rows[i]));
        lemma_from5_contains(sv, rows[i]);
        let (a, b, c, d, e) = choose|a: int, b: int, c: int, d: int, e: int| in5(sv, a, b, c, d, e) && rows[i] == #[trigger] row5(sv, a, b, c, d, e);
        assert(in5(sv, a, b, c, d, e));
        lemma_outer_row(db, sv, v, pat, rp, a, b, c, d, e);
    }
    lemma_collect_all(rs, truths);
    lemma_collect_pointwise::<Truth>();
    lemma_keep_true_is_true(rows, truths, f);
}

/// Every kept row is a `row5` of 28 values.
pub proof fn lemma_kept_rows(sv: StoresView, f: spec_fn(Row) -> bool, x: Row)
    requires stores_wf(sv), keep(from5(sv), f).contains(x),
    ensures
        exists|a: int, b: int, c: int, d: int, e: int| in5(sv, a, b, c, d, e) && x == #[trigger] row5(sv, a, b, c, d, e) && f(x),
        x.len() == 28,
{
    lemma_keep_contains(from5(sv), f, x);
    lemma_from5_contains(sv, x);
    let (a, b, c, d, e) = choose|a: int, b: int, c: int, d: int, e: int| in5(sv, a, b, c, d, e) && x == #[trigger] row5(sv, a, b, c, d, e);
    lemma_row5(sv, a, b, c, d, e);
}

/// The output row of a FROM row: the selected columns.
pub open spec fn out_row(x: Row) -> Row {
    select(x, out_cols())
}

/// Without `LIKE` errors, the body is the output rows of `keep(from5, outer_keep)`, in that order.
pub proof fn lemma_body_ok(db: Database, sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>)
    requires
        tables_of(sv, db),
        stores_wf(sv),
        int_in_range(IntKind::Int4, v),
        like_total(sv, pat),
    ensures
        eval_query(db, Seq::empty(), body(lits(v, pat, rp)))
            == Ok::<Relation, SqlError>(keep(from5(sv), outer_keep(sv, v, pat, rp)).map_values(|x: Row| out_row(x))),
{
    hide(like_value);
    hide(is_min_cost);
    let kept = keep(from5(sv), outer_keep(sv, v, pat, rp));
    lemma_filter_ok(db, sv, v, pat, rp);
    assert forall|i: int| 0 <= i < kept.len() implies (#[trigger] kept[i]).len() == 28 by {
        assert(kept.contains(kept[i]));
        lemma_kept_rows(sv, outer_keep(sv, v, pat, rp), kept[i]);
    }
    let outs = out_cols();
    assert forall|m: int| 0 <= m < outs.len() implies #[trigger] outs[m] < 28 by {
        if m == 0 {} else if m == 1 {} else if m == 2 {} else if m == 3 {} else if m == 4 {} else if m == 5 {} else if m == 6 {} else {}
    }
    lemma_project_cols(db, filtered(lits(v, pat, rp)), kept, outs, 28);
    assert(kept.map_values(|r: Row| select(r, outs)) =~= kept.map_values(|x: Row| out_row(x)));
}

/// The outer FROM re-associated as `part x (supplier x (partsupp x (nation x region)))`.
pub open spec fn rest4(sv: StoresView) -> Seq<Row> {
    product_rows(supp_rows(sv), product_rows(ps_rows(sv), product_rows(nat_rows(sv), reg_rows(sv))))
}

proof fn lemma_from5_assoc(sv: StoresView)
    ensures from5(sv) == product_rows(part_rows(sv), rest4(sv)),
{
    let (p, s, q, n, r) = (part_rows(sv), supp_rows(sv), ps_rows(sv), nat_rows(sv), reg_rows(sv));
    let nr = product_rows(n, r);
    let y = product_rows(q, nr);
    lemma_product_assoc(product_rows(product_rows(p, s), q), n, r);
    lemma_product_assoc(product_rows(p, s), q, nr);
    lemma_product_assoc(p, s, y);
}

/// A row of `rest4` follows a part row as a `row5`.
proof fn lemma_rest4_row(sv: StoresView, a: int, j: int)
    requires stores_wf(sv), 0 <= a < part_n(sv), 0 <= j < rest4(sv).len(),
    ensures exists|b: int, c: int, d: int, e: int| in5(sv, a, b, c, d, e) && part_rows(sv)[a] + rest4(sv)[j] == #[trigger] row5(sv, a, b, c, d, e),
{
    let (p, s, q, n, r) = (part_rows(sv), supp_rows(sv), ps_rows(sv), nat_rows(sv), reg_rows(sv));
    let nr = product_rows(n, r);
    let y = product_rows(q, nr);
    let z = rest4(sv)[j];
    assert(rest4(sv).contains(z));
    lemma_product_contains(s, y, z);
    let (b, iy) = choose|b: int, iy: int| 0 <= b < s.len() && 0 <= iy < y.len() && z == #[trigger] s[b] + #[trigger] y[iy];
    assert(y.contains(y[iy]));
    lemma_product_contains(q, nr, y[iy]);
    let (c, inr) = choose|c: int, inr: int| 0 <= c < q.len() && 0 <= inr < nr.len() && y[iy] == #[trigger] q[c] + #[trigger] nr[inr];
    assert(nr.contains(nr[inr]));
    lemma_product_contains(n, r, nr[inr]);
    let (d, e) = choose|d: int, e: int| 0 <= d < n.len() && 0 <= e < r.len() && nr[inr] == #[trigger] n[d] + #[trigger] r[e];
    assert(p[a] + z =~= row5(sv, a, b, c, d, e));
}

/// With a `LIKE` error at part row `a0` (the first one) and every other table non-empty, the body is that error.
pub proof fn lemma_body_err(db: Database, sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, a0: int, err: SqlError)
    requires
        tables_of(sv, db),
        stores_wf(sv),
        int_in_range(IntKind::Int4, v),
        0 <= a0 < part_n(sv),
        like_res(p_type(sv, a0), pat) == Err::<Val, SqlError>(err),
        forall|a: int| 0 <= a < a0 ==> #[trigger] like_res(p_type(sv, a), pat) is Ok,
        supp_n(sv) > 0, ps_n(sv) > 0, nat_n(sv) > 0, reg_n(sv) > 0,
    ensures
        eval_query(db, Seq::empty(), body(lits(v, pat, rp))) == Err::<Relation, SqlError>(err),
{
    hide(like_value);
    hide(is_min_cost);
    hide(outer_pred);
    let ctx = Seq::<Val>::empty();
    let rows = from5(sv);
    let pred = outer_pred(lits(v, pat, rp));
    let p = part_rows(sv);
    let rest = rest4(sv);
    lemma_eval_from5(db, sv);
    lemma_from5_assoc(sv);
    lemma_product_index(p, rest);
    let nr = product_rows(nat_rows(sv), reg_rows(sv));
    let y = product_rows(ps_rows(sv), nr);
    crate::bridge::relation::lemma_product_rows_elems(nat_rows(sv), reg_rows(sv));
    crate::bridge::relation::lemma_product_rows_elems(ps_rows(sv), nr);
    crate::bridge::relation::lemma_product_rows_elems(supp_rows(sv), y);
    let m = rest.len() as int;
    assert(nr.len() > 0) by { assert(nr.len() == nat_n(sv) * reg_n(sv)) ; vstd::arithmetic::mul::lemma_mul_strictly_positive(nat_n(sv) as int, reg_n(sv) as int); }
    assert(y.len() > 0) by { vstd::arithmetic::mul::lemma_mul_strictly_positive(ps_n(sv) as int, nr.len() as int); }
    assert(m > 0) by { vstd::arithmetic::mul::lemma_mul_strictly_positive(supp_n(sv) as int, y.len() as int); }
    let rs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred));
    let i0 = a0 * m;
    assert(0 <= i0 < rows.len()) by {
        assert(rows.len() == p.len() * m);
        assert(a0 * m < p.len() * m) by (nonlinear_arith) requires 0 <= a0 < p.len(), m > 0;
        assert(0 <= a0 * m) by (nonlinear_arith) requires 0 <= a0, m > 0;
    }
    // The first row of part `a0` fails with `err`.
    assert(rows[i0] == p[a0] + rest[0]);
    lemma_rest4_row(sv, a0, 0);
    assert(rs[i0] == Err::<Truth, SqlError>(err)) by {
        let (b, c, d, e) = choose|b: int, c: int, d: int, e: int| in5(sv, a0, b, c, d, e) && p[a0] + rest[0] == #[trigger] row5(sv, a0, b, c, d, e);
        assert(ctx + rows[i0] =~= rows[i0]);
        lemma_outer_row(db, sv, v, pat, rp, a0, b, c, d, e);
    }
    // Every earlier row belongs to an earlier part, which has no `LIKE` error.
    assert forall|j: int| 0 <= j < i0 implies #[trigger] rs[j] is Ok by {
        let a = j / m;
        let jj = j % m;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, m);
        assert(0 <= jj < m) by { vstd::arithmetic::div_mod::lemma_mod_bound(j, m); }
        assert(0 <= a) by { vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, m); }
        assert(a < a0) by {
            assert(a * m <= j) by (nonlinear_arith) requires j == m * a + jj, 0 <= jj;
            assert(a * m < a0 * m);
            if a >= a0 {
                assert(a * m >= a0 * m) by (nonlinear_arith) requires a >= a0, m > 0;
            }
        }
        assert(j == a * m + jj) by (nonlinear_arith) requires j == m * a + jj;
        assert(rows[j] == p[a] + rest[jj]);
        lemma_rest4_row(sv, a, jj);
        let (b, c, d, e) = choose|b: int, c: int, d: int, e: int| in5(sv, a, b, c, d, e) && p[a] + rest[jj] == #[trigger] row5(sv, a, b, c, d, e);
        assert(ctx + rows[j] =~= rows[j]);
        lemma_outer_row(db, sv, v, pat, rp, a, b, c, d, e);
    }
    lemma_collect_first_err(rs, i0);
    lemma_collect_pointwise::<Truth>();
    reveal(outer_pred);
    assert(eval_query(db, ctx, filtered(lits(v, pat, rp))) == Err::<Relation, SqlError>(err));
}

// ------------------------------------------------------------------------------------------ duplicate-free rows

/// Rows of a table with unique keys in column 0 are pairwise different.
proof fn lemma_rows_nodup_by_key(rows: Seq<Row>, keys: Seq<i64>)
    requires
        rows.len() == keys.len(),
        crate::agent::scan_part::keys_unique(keys),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() > 0 && rows[i][0] == Val::Int(keys[i] as int),
    ensures rows.no_duplicates(),
{
    assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && i != j implies rows[i] != rows[j] by {
        assert(rows[i][0] == Val::Int(keys[i] as int) && rows[j][0] == Val::Int(keys[j] as int));
    }
}

proof fn lemma_part_rows_nodup(sv: StoresView)
    requires stores_wf(sv), keys_ok(sv),
    ensures part_rows(sv).no_duplicates(),
{
    assert forall|i: int| 0 <= i < part_rows(sv).len() implies (#[trigger] part_rows(sv)[i]).len() > 0 && part_rows(sv)[i][0] == Val::Int(p_keys(sv)[i] as int) by {
        assert(part_rows(sv)[i] == pi::row_at(sv.flat_part, i));
    }
    lemma_rows_nodup_by_key(part_rows(sv), p_keys(sv));
}

proof fn lemma_supp_rows_nodup(sv: StoresView)
    requires stores_wf(sv), keys_ok(sv),
    ensures supp_rows(sv).no_duplicates(),
{
    assert forall|i: int| 0 <= i < supp_rows(sv).len() implies (#[trigger] supp_rows(sv)[i]).len() > 0 && supp_rows(sv)[i][0] == Val::Int(s_keys(sv)[i] as int) by {
        assert(supp_rows(sv)[i] == si::row_at(sv.flat_supplier, i));
    }
    lemma_rows_nodup_by_key(supp_rows(sv), s_keys(sv));
}

proof fn lemma_nat_rows_nodup(sv: StoresView)
    requires stores_wf(sv), keys_ok(sv),
    ensures nat_rows(sv).no_duplicates(),
{
    assert forall|i: int| 0 <= i < nat_rows(sv).len() implies (#[trigger] nat_rows(sv)[i]).len() > 0 && nat_rows(sv)[i][0] == Val::Int(n_keys(sv)[i] as int) by {
        assert(nat_rows(sv)[i] == ni::row_at(sv.flat_nation, i));
    }
    lemma_rows_nodup_by_key(nat_rows(sv), n_keys(sv));
}

proof fn lemma_reg_rows_nodup(sv: StoresView)
    requires stores_wf(sv), keys_ok(sv),
    ensures reg_rows(sv).no_duplicates(),
{
    assert forall|i: int| 0 <= i < reg_rows(sv).len() implies (#[trigger] reg_rows(sv)[i]).len() > 0 && reg_rows(sv)[i][0] == Val::Int(r_keys(sv)[i] as int) by {
        assert(reg_rows(sv)[i] == ri::row_at(sv.flat_region, i));
    }
    lemma_rows_nodup_by_key(reg_rows(sv), r_keys(sv));
}

proof fn lemma_ps_rows_nodup(sv: StoresView)
    requires stores_wf(sv), keys_ok(sv),
    ensures ps_rows(sv).no_duplicates(),
{
    let q = ps_rows(sv);
    assert forall|i: int, j: int| 0 <= i < q.len() && 0 <= j < q.len() && i != j implies q[i] != q[j] by {
        assert(q[i] == psi::row_at(sv.flat_partsupp, i));
        assert(q[j] == psi::row_at(sv.flat_partsupp, j));
        assert(q[i][0] == Val::Int(ps_pkeys(sv)[i] as int) && q[i][1] == Val::Int(ps_skeys(sv)[i] as int));
        assert(q[j][0] == Val::Int(ps_pkeys(sv)[j] as int) && q[j][1] == Val::Int(ps_skeys(sv)[j] as int));
        assert(ps_pkeys(sv)[i] != ps_pkeys(sv)[j] || ps_skeys(sv)[i] != ps_skeys(sv)[j]);
    }
}

/// Rows of a product of relations with rows of widths `wa` and `wb` have width `wa + wb`.
proof fn lemma_product_width(a: Seq<Row>, b: Seq<Row>, wa: nat, wb: nat)
    requires
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == wa,
        forall|i: int| 0 <= i < b.len() ==> (#[trigger] b[i]).len() == wb,
    ensures forall|i: int| 0 <= i < product_rows(a, b).len() ==> (#[trigger] product_rows(a, b)[i]).len() == wa + wb,
{
    crate::bridge::relation::lemma_product_rows_elems(a, b);
    let p = product_rows(a, b);
    assert forall|i: int| 0 <= i < p.len() implies (#[trigger] p[i]).len() == wa + wb by {
        assert(crate::bridge::relation::is_concat(p[i], a, b));
        let (x, y) = choose|x: int, y: int| 0 <= x < a.len() && 0 <= y < b.len() && p[i] == #[trigger] a[x] + #[trigger] b[y];
    }
}

/// The rows of the outer FROM are pairwise different (every table has a primary key).
pub proof fn lemma_from5_nodup(sv: StoresView)
    requires stores_wf(sv), keys_ok(sv),
    ensures from5(sv).no_duplicates(),
{
    let (p, s, q, n, r) = (part_rows(sv), supp_rows(sv), ps_rows(sv), nat_rows(sv), reg_rows(sv));
    lemma_part_rows_nodup(sv);
    lemma_supp_rows_nodup(sv);
    lemma_ps_rows_nodup(sv);
    lemma_nat_rows_nodup(sv);
    lemma_reg_rows_nodup(sv);
    assert forall|i: int| 0 <= i < p.len() implies (#[trigger] p[i]).len() == 9 by { assert(p[i] == pi::row_at(sv.flat_part, i)); }
    assert forall|i: int| 0 <= i < s.len() implies (#[trigger] s[i]).len() == 7 by { assert(s[i] == si::row_at(sv.flat_supplier, i)); }
    assert forall|i: int| 0 <= i < q.len() implies (#[trigger] q[i]).len() == 5 by { assert(q[i] == psi::row_at(sv.flat_partsupp, i)); }
    assert forall|i: int| 0 <= i < n.len() implies (#[trigger] n[i]).len() == 4 by { assert(n[i] == ni::row_at(sv.flat_nation, i)); }
    let l1 = product_rows(p, s);
    let l2 = product_rows(l1, q);
    let l3 = product_rows(l2, n);
    lemma_product_nodup(p, s, 9);
    lemma_product_width(p, s, 9, 7);
    lemma_product_nodup(l1, q, 16);
    lemma_product_width(l1, q, 16, 5);
    lemma_product_nodup(l2, n, 21);
    lemma_product_width(l2, n, 21, 4);
    lemma_product_nodup(l3, r, 25);
}

} // verus!
