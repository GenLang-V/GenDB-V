//! The statement's AST, named node by node (`lemma_query_shape`), and the value of every condition of its FROM and
//! WHERE on a joined row `num ++ sub ++ tag ++ pre` (48 columns: num 0..9, sub 9..29, tag 29..38, pre 38..48):
//! the three join conditions are two-valued equalities of text cells; the WHERE is never an error and is `True`
//! exactly when `uom = $1`, `stmt` is not NULL and equals `$2`, `sic` is not NULL and lies in `[$3, $4]` and
//! `abstract = 0` (`value` is never NULL).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::scalar::*;
use crate::spec::int::*;
use crate::link::expr::*;
use crate::agent::cols::*;

verus! {

// ------------------------------------------------------------------------------------------------ AST nodes

pub open spec fn eqc(a: nat, b: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(a), b: Expr::Col(b) }
}

pub open spec fn and2(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

/// `n.adsh = s.adsh`.
pub open spec fn p_ns() -> Pred { eqc(0, 9) }

/// `n.tag = t.tag AND n.version = t.version`.
pub open spec fn p_nt() -> Pred { and2(eqc(1, 29), eqc(2, 30)) }

/// `n.adsh = p.adsh AND n.tag = p.tag AND n.version = p.version`.
pub open spec fn p_np() -> Pred { and2(and2(eqc(0, 38), eqc(1, 44)), eqc(2, 45)) }

/// The WHERE condition at the binding `ps`.
pub open spec fn p_where(ps: Seq<Literal>) -> Pred {
    and2(
        and2(
            and2(
                and2(
                    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(ps[0]) },
                    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(41), b: Expr::Lit(ps[1]) },
                ),
                and2(
                    Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(12), b: Expr::Lit(ps[2]) },
                    Pred::Cmp { op: CmpOp::Le, a: Expr::Col(12), b: Expr::Lit(ps[3]) },
                ),
            ),
            Pred::Not(Box::new(Pred::IsNull(Expr::Col(7)))),
        ),
        Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(32), b: Expr::Lit(Literal::Int { v: 0, kind: IntKind::Int4 }) },
    )
}

/// `HAVING COUNT(DISTINCT s.cik) >= 2`.
pub open spec fn p_having() -> Pred {
    Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(3), b: Expr::Lit(Literal::Int { v: 2, kind: IntKind::Int4 }) }
}

pub open spec fn q_ns() -> Query {
    Query::Filter { pred: p_ns(), input: Box::new(Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) }) }
}

pub open spec fn q_nst() -> Query {
    Query::Filter { pred: p_nt(), input: Box::new(Query::Product { left: Box::new(q_ns()), right: Box::new(Query::Table(2)) }) }
}

pub open spec fn q_nstp() -> Query {
    Query::Filter { pred: p_np(), input: Box::new(Query::Product { left: Box::new(q_nst()), right: Box::new(Query::Table(3)) }) }
}

pub open spec fn q_where(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: p_where(ps), input: Box::new(q_nstp()) }
}

pub open spec fn g_keys() -> Seq<Expr> {
    seq![Expr::Col(12), Expr::Col(36), Expr::Col(41)]
}

pub open spec fn g_aggs() -> Seq<Agg> {
    seq![
        Agg::DistinctAgg(Box::new(Agg::Count(Expr::Col(10)))),
        Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(7) },
        Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(7) },
    ]
}

pub open spec fn q_group(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: g_keys(), aggs: g_aggs(), input: Box::new(q_where(ps)) }
}

pub open spec fn q_body(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: p_having(), input: Box::new(q_group(ps)) }
}

pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 4, desc: true, nulls_first: true }]
}

/// The generated statement, named node by node.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures
        crate::query::query_spec_at(ps).body == q_body(ps),
        crate::query::query_spec_at(ps).keys == order_keys(),
        crate::query::query_spec_at(ps).limit == Some(500nat),
        crate::query::query_spec_at(ps).offset == 0,
{
}

/// The binding: `$1 = uom`, `$2 = stmt` (texts), `$3 = lo`, `$4 = hi` (int4).
pub open spec fn lits_ok(c: Ctx, ps: Seq<Literal>) -> bool {
    &&& ps.len() == 4
    &&& ps[0] == Literal::Text(c.uom)
    &&& ps[1] == Literal::Text(c.stmt)
    &&& ps[2] == (Literal::Int { v: c.lo, kind: IntKind::Int4 })
    &&& ps[3] == (Literal::Int { v: c.hi, kind: IntKind::Int4 })
    &&& int_in_range(IntKind::Int4, c.lo) && int_in_range(IntKind::Int4, c.hi)
}

// ------------------------------------------------------------------------------------------------ joined rows

pub open spec fn ns_row(c: Ctx, i: int, s: int) -> Row { nrow(c, i) + srow(c, s) }
pub open spec fn nst_row(c: Ctx, i: int, s: int, k: int) -> Row { nrow(c, i) + srow(c, s) + trow(c, k) }
pub open spec fn full_row(c: Ctx, i: int, s: int, k: int, l: int) -> Row { nrow(c, i) + srow(c, s) + trow(c, k) + prow(c, l) }

/// The cells of a joined row the statement reads.
pub proof fn lemma_full_cells(c: Ctx, i: int, s: int, k: int, l: int)
    ensures ({
        let x = full_row(c, i, s, k, l);
        &&& x.len() == 48
        &&& x[0] == Val::Text(n_adsh(c, i)) && x[1] == Val::Text(n_tag(c, i)) && x[2] == Val::Text(n_ver(c, i))
        &&& x[5] == Val::Text(n_uom(c, i)) && x[7] == (Val::Num { coeff: n_val(c, i), scale: 4 })
        &&& x[9] == Val::Text(s_adsh(c, s)) && x[10] == Val::Int(s_cik(c, s))
        &&& x[12] == (if s_sic_valid(c, s) { Val::Int(s_sic(c, s)) } else { Val::Null })
        &&& x[29] == Val::Text(t_tag(c, k)) && x[30] == Val::Text(t_ver(c, k)) && x[32] == Val::Int(t_abs(c, k))
        &&& x[36] == t_label(c, k)
        &&& x[38] == Val::Text(p_adsh(c, l))
        &&& x[41] == (if p_stmt_valid(c, l) { Val::Text(p_stmt(c, l)) } else { Val::Null })
        &&& x[44] == Val::Text(p_tag(c, l)) && x[45] == Val::Text(p_ver(c, l))
    }),
{
    lemma_cells(c, i, s, k, l);
    let x = full_row(c, i, s, k, l);
    let (a, b, t, p) = (nrow(c, i), srow(c, s), trow(c, k), prow(c, l));
    assert(x[0] == a[0] && x[1] == a[1] && x[2] == a[2] && x[5] == a[5] && x[7] == a[7]);
    assert(x[9] == b[0] && x[10] == b[1] && x[12] == b[3]);
    assert(x[29] == t[0] && x[30] == t[1] && x[32] == t[3] && x[36] == t[7]);
    assert(x[38] == p[0] && x[41] == p[3] && x[44] == p[6] && x[45] == p[7]);
}

pub proof fn lemma_ns_cells(c: Ctx, i: int, s: int)
    ensures ({
        let x = ns_row(c, i, s);
        &&& x.len() == 29
        &&& x[0] == Val::Text(n_adsh(c, i)) && x[9] == Val::Text(s_adsh(c, s))
    }),
{
    lemma_cells(c, i, s, 0, 0);
    let x = ns_row(c, i, s);
    assert(x[0] == nrow(c, i)[0] && x[9] == srow(c, s)[0]);
}

pub proof fn lemma_nst_cells(c: Ctx, i: int, s: int, k: int)
    ensures ({
        let x = nst_row(c, i, s, k);
        &&& x.len() == 38
        &&& x[1] == Val::Text(n_tag(c, i)) && x[2] == Val::Text(n_ver(c, i))
        &&& x[29] == Val::Text(t_tag(c, k)) && x[30] == Val::Text(t_ver(c, k))
    }),
{
    lemma_cells(c, i, s, k, 0);
    let x = nst_row(c, i, s, k);
    assert(x[1] == nrow(c, i)[1] && x[2] == nrow(c, i)[2] && x[29] == trow(c, k)[0] && x[30] == trow(c, k)[1]);
}

// ------------------------------------------------------------------------------------------------ conditions

/// A text equality of two text cells is two-valued.
pub proof fn lemma_eqc(db: Database, env: Row, a: nat, b: nat, x: Seq<u8>, y: Seq<u8>)
    requires a < env.len(), b < env.len(), env[a as int] == Val::Text(x), env[b as int] == Val::Text(y),
    ensures eval_pred(db, env, eqc(a, b)) == Ok::<Truth, SqlError>(truth_of(x == y)),
{
    lemma_expr_col(db, env, a);
    lemma_expr_col(db, env, b);
    lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(a), Expr::Col(b), x, y);
}

pub proof fn lemma_eval_ns(db: Database, c: Ctx, i: int, s: int)
    ensures eval_pred(db, ns_row(c, i, s), p_ns()) == Ok::<Truth, SqlError>(truth_of(n_adsh(c, i) == s_adsh(c, s))),
{
    lemma_ns_cells(c, i, s);
    lemma_eqc(db, ns_row(c, i, s), 0, 9, n_adsh(c, i), s_adsh(c, s));
}

pub proof fn lemma_eval_nt(db: Database, c: Ctx, i: int, s: int, k: int)
    ensures eval_pred(db, nst_row(c, i, s, k), p_nt())
        == Ok::<Truth, SqlError>(truth_of(n_tag(c, i) == t_tag(c, k) && n_ver(c, i) == t_ver(c, k))),
{
    let x = nst_row(c, i, s, k);
    lemma_nst_cells(c, i, s, k);
    lemma_eqc(db, x, 1, 29, n_tag(c, i), t_tag(c, k));
    lemma_eqc(db, x, 2, 30, n_ver(c, i), t_ver(c, k));
    lemma_pred_and(db, x, eqc(1, 29), eqc(2, 30), n_tag(c, i) == t_tag(c, k), n_ver(c, i) == t_ver(c, k));
}

pub proof fn lemma_eval_np(db: Database, c: Ctx, i: int, s: int, k: int, l: int)
    ensures eval_pred(db, full_row(c, i, s, k, l), p_np())
        == Ok::<Truth, SqlError>(truth_of(n_adsh(c, i) == p_adsh(c, l) && n_tag(c, i) == p_tag(c, l) && n_ver(c, i) == p_ver(c, l))),
{
    let x = full_row(c, i, s, k, l);
    lemma_full_cells(c, i, s, k, l);
    lemma_eqc(db, x, 0, 38, n_adsh(c, i), p_adsh(c, l));
    lemma_eqc(db, x, 1, 44, n_tag(c, i), p_tag(c, l));
    lemma_eqc(db, x, 2, 45, n_ver(c, i), p_ver(c, l));
    lemma_pred_and(db, x, eqc(0, 38), eqc(1, 44), n_adsh(c, i) == p_adsh(c, l), n_tag(c, i) == p_tag(c, l));
    lemma_pred_and(db, x, and2(eqc(0, 38), eqc(1, 44)), eqc(2, 45),
        n_adsh(c, i) == p_adsh(c, l) && n_tag(c, i) == p_tag(c, l), n_ver(c, i) == p_ver(c, l));
}

/// The WHERE holds on the joined row of `num` row `i`, sub row `s`, tag row `k` and pre row `l`.
pub open spec fn where_ok(c: Ctx, i: int, s: int, k: int, l: int) -> bool {
    &&& n_uom(c, i) == c.uom
    &&& p_stmt_valid(c, l) && p_stmt(c, l) == c.stmt
    &&& s_sic_valid(c, s) && c.lo <= s_sic(c, s) <= c.hi
    &&& t_abs(c, k) == 0
}

/// `x op $k` for an integer-or-NULL cell and an int4 literal.
pub proof fn lemma_int_lit(db: Database, env: Row, op: CmpOp, idx: nat, v: int)
    requires idx < env.len(), env[idx as int] is Null || env[idx as int] is Int, int_in_range(IntKind::Int4, v),
    ensures eval_pred(db, env, Pred::Cmp { op, a: Expr::Col(idx), b: Expr::Lit(Literal::Int { v, kind: IntKind::Int4 }) })
        == Ok::<Truth, SqlError>(if env[idx as int] is Null { Truth::Unknown } else { truth_of(int_cmp(op, env[idx as int]->Int_0, v)) }),
{
    lemma_expr_col(db, env, idx);
    let b = Expr::Lit(Literal::Int { v, kind: IntKind::Int4 });
    assert(eval_expr(db, env, b) == Ok::<Val, SqlError>(Val::Int(v)));
    if env[idx as int] is Int {
        let x = env[idx as int]->Int_0;
        lemma_compare_int(x, v);
        lemma_pred_cmp(db, env, op, Expr::Col(idx), b, env[idx as int], Val::Int(v), x, v);
    }
}

/// `x = $k` for a text-or-NULL cell and a text literal.
proof fn lemma_text_lit(db: Database, env: Row, idx: nat, t: Seq<u8>)
    requires idx < env.len(), env[idx as int] is Null || env[idx as int] is Text,
    ensures eval_pred(db, env, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(idx), b: Expr::Lit(Literal::Text(t)) })
        == Ok::<Truth, SqlError>(if env[idx as int] is Null { Truth::Unknown } else { truth_of(env[idx as int]->Text_0 == t) }),
{
    lemma_expr_col(db, env, idx);
    lemma_expr_text(db, env, t);
    if env[idx as int] is Text {
        lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(idx), Expr::Lit(Literal::Text(t)), env[idx as int]->Text_0, t);
    }
}

/// The WHERE on a row with the cells it reads: never an error; `True` exactly when every comparison is.
#[verifier::spinoff_prover]
proof fn lemma_where_env(db: Database, env: Row, c: Ctx, ps: Seq<Literal>, u: Seq<u8>, st: Val, sic: Val, ab: int)
    requires
        lits_ok(c, ps), env.len() == 48,
        env[5] == Val::Text(u), env[41] == st, st is Null || st is Text, env[12] == sic, sic is Null || sic is Int,
        env[7] is Num, env[32] == Val::Int(ab),
    ensures
        eval_pred(db, env, p_where(ps)) is Ok,
        (eval_pred(db, env, p_where(ps)) == Ok::<Truth, SqlError>(Truth::True))
            == (u == c.uom && st == Val::Text(c.stmt) && sic is Int && c.lo <= sic->Int_0 <= c.hi && ab == 0),
{
    let a1 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(ps[0]) };
    let a2 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(41), b: Expr::Lit(ps[1]) };
    let a3 = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(12), b: Expr::Lit(ps[2]) };
    let a4 = Pred::Cmp { op: CmpOp::Le, a: Expr::Col(12), b: Expr::Lit(ps[3]) };
    let a5 = Pred::Not(Box::new(Pred::IsNull(Expr::Col(7))));
    let a6 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(32), b: Expr::Lit(Literal::Int { v: 0, kind: IntKind::Int4 }) };
    lemma_text_lit(db, env, 5, c.uom);
    lemma_text_lit(db, env, 41, c.stmt);
    lemma_int_lit(db, env, CmpOp::Ge, 12, c.lo);
    lemma_int_lit(db, env, CmpOp::Le, 12, c.hi);
    lemma_int_lit(db, env, CmpOp::Eq, 32, 0);
    lemma_expr_col(db, env, 7);
    assert(eval_pred(db, env, Pred::IsNull(Expr::Col(7))) == Ok::<Truth, SqlError>(Truth::False));
    let t1 = truth_of(u == c.uom);
    let t2 = if st is Null { Truth::Unknown } else { truth_of(st->Text_0 == c.stmt) };
    let t3 = if sic is Null { Truth::Unknown } else { truth_of(sic->Int_0 >= c.lo) };
    let t4 = if sic is Null { Truth::Unknown } else { truth_of(sic->Int_0 <= c.hi) };
    let t6 = truth_of(ab == 0);
    assert(eval_pred(db, env, a1) == Ok::<Truth, SqlError>(t1));
    assert(eval_pred(db, env, a2) == Ok::<Truth, SqlError>(t2));
    assert(eval_pred(db, env, a3) == Ok::<Truth, SqlError>(t3));
    assert(eval_pred(db, env, a4) == Ok::<Truth, SqlError>(t4));
    assert(eval_pred(db, env, a5) == Ok::<Truth, SqlError>(Truth::True));
    assert(eval_pred(db, env, a6) == Ok::<Truth, SqlError>(t6));
    assert(eval_pred(db, env, and2(a1, a2)) == Ok::<Truth, SqlError>(truth_and(t1, t2)));
    assert(eval_pred(db, env, and2(a3, a4)) == Ok::<Truth, SqlError>(truth_and(t3, t4)));
    assert(eval_pred(db, env, and2(and2(a1, a2), and2(a3, a4)))
        == Ok::<Truth, SqlError>(truth_and(truth_and(t1, t2), truth_and(t3, t4))));
    assert(eval_pred(db, env, and2(and2(and2(a1, a2), and2(a3, a4)), a5))
        == Ok::<Truth, SqlError>(truth_and(truth_and(truth_and(t1, t2), truth_and(t3, t4)), Truth::True)));
    assert(p_where(ps) == and2(and2(and2(and2(a1, a2), and2(a3, a4)), a5), a6));
}

/// The WHERE on a joined row: never an error, `True` exactly when `where_ok`.
pub proof fn lemma_eval_where(db: Database, c: Ctx, ps: Seq<Literal>, i: int, s: int, k: int, l: int)
    requires lits_ok(c, ps),
    ensures
        eval_pred(db, full_row(c, i, s, k, l), p_where(ps)) is Ok,
        (eval_pred(db, full_row(c, i, s, k, l), p_where(ps)) == Ok::<Truth, SqlError>(Truth::True)) == where_ok(c, i, s, k, l),
{
    let x = full_row(c, i, s, k, l);
    lemma_full_cells(c, i, s, k, l);
    lemma_where_env(db, x, c, ps, n_uom(c, i), x[41], x[12], t_abs(c, k));
}

} // verus!
