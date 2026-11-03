//! The statement's AST (`crate::query::query_spec_at`) assembled from named pieces (`lemma_query_shape`), the FROM
//! relation of both query blocks (`from_rows`: partsupp x supplier x nation, left-major) and the per-row
//! evaluation of the WHERE condition, the group key and the SUM argument (`lemma_row_eval`).
//!
//! Environments: a FROM row is `P[a] ++ S[b] ++ N[d]` (`row3`, 16 positions: partsupp 0..5 (ps_partkey 0,
//! ps_suppkey 1, ps_availqty 2, ps_supplycost 3), supplier 5..12 (s_suppkey 5, s_nationkey 8), nation 12..16
//! (n_nationkey 12, n_name 13)). The outer block evaluates its rows with an empty context (offset 0); the HAVING
//! subquery evaluates them after the group row `(ps_partkey, value)` (offset 2). `where_pred(o, ..)` and
//! `arg_expr(o)` are the condition and the SUM argument at offset `o`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::product_rows;
use crate::query::query_spec_at;
use crate::link::expr::{lemma_pred_cmp, lemma_pred_text_cmp, lemma_pred_and, lemma_expr_col, lemma_expr_text,
    lemma_compare_int, int_cmp, text_cmp, ival};
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::gendb_entry::stores::StoresView;
use crate::stores::flat_partsupp::interface as psi;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::agent::model::*;

verus! {

// ------------------------------------------------------------------------------------------ the AST

/// `col i = col j`.
pub open spec fn eq_cols(i: nat, j: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Col(j) }
}

/// `col i = literal`.
pub open spec fn eq_lit(i: nat, l: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Lit(l) }
}

pub open spec fn and(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

pub open spec fn prod(l: Query, r: Query) -> Query {
    Query::Product { left: Box::new(l), right: Box::new(r) }
}

/// `FROM partsupp, supplier, nation`.
pub open spec fn from3() -> Query {
    prod(prod(Query::Table(4), Query::Table(5)), Query::Table(6))
}

/// `ps_suppkey = s_suppkey AND s_nationkey = n_nationkey AND n_name = $1` at offset `o`.
pub open spec fn where_pred(o: nat, l: Literal) -> Pred {
    and(and(eq_cols((o + 1) as nat, (o + 5) as nat), eq_cols((o + 8) as nat, (o + 12) as nat)), eq_lit((o + 13) as nat, l))
}

/// `ps_supplycost * ps_availqty` (the integer cast to numeric) at offset `o`.
pub open spec fn arg_expr(o: nat) -> Expr {
    Expr::Arith {
        op: ArithOp::Mul,
        kind: NumKind::Numeric,
        a: Box::new(Expr::Col((o + 3) as nat)),
        b: Box::new(Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Col((o + 2) as nat)) }),
    }
}

/// `SUM(ps_supplycost * ps_availqty)` at offset `o`.
pub open spec fn sum_agg(o: nat) -> Agg {
    Agg::Sum { kind: NumKind::Numeric, arg: arg_expr(o) }
}

/// The WHERE over the FROM relation at offset `o`.
pub open spec fn filtered(o: nat, l: Literal) -> Query {
    Query::Filter { pred: where_pred(o, l), input: Box::new(from3()) }
}

/// The subquery's aggregate `SELECT SUM(..) FROM .. WHERE ..` (offset 2).
pub open spec fn sub_agg(l: Literal) -> Query {
    Query::Aggregate { aggs: seq![sum_agg(2)], input: Box::new(filtered(2, l)) }
}

/// `SUM(..) * $2` over the aggregate row (position 2 after the group row).
pub open spec fn scaled(l2: Literal) -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(2)), b: Box::new(Expr::Lit(l2)) }
}

/// The HAVING subquery.
pub open spec fn sub_query(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: seq![scaled(ps[1])], input: Box::new(sub_agg(ps[0])) }
}

/// `HAVING SUM(..) > (subquery)` over the group row `(ps_partkey, value)`.
pub open spec fn having(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(1), b: Expr::Subquery(Box::new(sub_query(ps))) }
}

/// `GROUP BY ps_partkey` with `SUM(..)` over the outer WHERE (offset 0).
pub open spec fn grouped(l: Literal) -> Query {
    Query::GroupBy { keys: seq![Expr::Col(0)], aggs: seq![sum_agg(0)], input: Box::new(filtered(0, l)) }
}

/// The statement body: the groups kept by HAVING.
pub open spec fn body(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: having(ps), input: Box::new(grouped(ps[0])) }
}

/// The binding `($1, $2)` with `$1 = p` and `$2 = c2 * 10^-10`.
pub open spec fn params_of(p: Seq<u8>, c2: int) -> Seq<Literal> {
    seq![Literal::Text(p), Literal::Num { coeff: c2, scale: 10 }]
}

/// `ORDER BY value DESC`.
pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 1, desc: true, nulls_first: true }]
}

/// The fixed statement is the assembly above.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: body(ps), keys: order_keys(), limit: None, offset: 0 }),
{
}

// ------------------------------------------------------------------------------------------ the FROM relation

/// `P[a] ++ S[b] ++ N[d]`.
pub open spec fn row3(sv: StoresView, a: int, b: int, d: int) -> Row {
    ps_rows(sv)[a] + supp_rows(sv)[b] + nat_rows(sv)[d]
}

/// The FROM relation (left-major product of the three stored tables).
pub open spec fn from_rows(sv: StoresView) -> Seq<Row> {
    product_rows(product_rows(ps_rows(sv), supp_rows(sv)), nat_rows(sv))
}

/// The FROM relation of every bound database, in any context.
pub proof fn lemma_eval_from(db: Database, sv: StoresView, ctx: Row)
    requires tables_of(sv, db),
    ensures eval_query(db, ctx, from3()) == Ok::<Relation, SqlError>(from_rows(sv)),
{
    let t4 = Query::Table(4);
    let t5 = Query::Table(5);
    let t6 = Query::Table(6);
    assert(eval_query(db, ctx, t4) == Ok::<Relation, SqlError>(ps_rows(sv)));
    assert(eval_query(db, ctx, t5) == Ok::<Relation, SqlError>(supp_rows(sv)));
    assert(eval_query(db, ctx, t6) == Ok::<Relation, SqlError>(nat_rows(sv)));
    assert(eval_query(db, ctx, prod(t4, t5)) == Ok::<Relation, SqlError>(product_rows(ps_rows(sv), supp_rows(sv))));
}

/// Every FROM row is `row3(a, b, d)` for some rows `a`, `b`, `d`.
pub proof fn lemma_from_elem(sv: StoresView, m: int) -> (abd: (int, int, int))
    requires 0 <= m < from_rows(sv).len(),
    ensures
        0 <= abd.0 < ps_n(sv), 0 <= abd.1 < supp_n(sv), 0 <= abd.2 < nat_n(sv),
        from_rows(sv)[m] == row3(sv, abd.0, abd.1, abd.2),
{
    let (p, s, n) = (ps_rows(sv), supp_rows(sv), nat_rows(sv));
    let ab = product_rows(p, s);
    lemma_product_rows_elems(ab, n);
    assert(is_concat(from_rows(sv)[m], ab, n));
    let (i, d) = choose|i: int, d: int| 0 <= i < ab.len() && 0 <= d < n.len() && from_rows(sv)[m] == #[trigger] ab[i] + #[trigger] n[d];
    lemma_product_rows_elems(p, s);
    assert(is_concat(ab[i], p, s));
    let (a, b) = choose|a: int, b: int| 0 <= a < p.len() && 0 <= b < s.len() && ab[i] == #[trigger] p[a] + #[trigger] s[b];
    (a, b, d)
}

// ------------------------------------------------------------------------------------------ one FROM row

/// The WHERE condition on `row3(a, b, d)`, in terms of the stored columns.
pub open spec fn qual3(sv: StoresView, p: Seq<u8>, a: int, b: int, d: int) -> bool {
    &&& ps_skeys(sv)[a] == s_keys(sv)[b]
    &&& s_nks(sv)[b] == n_keys(sv)[d]
    &&& n_name(sv, d) == p
}

/// The WHERE condition on a FROM row as a Boolean of its values (the normal form's qualification).
pub open spec fn qualx(p: Seq<u8>, x: Row) -> bool {
    x[1] == x[5] && x[8] == x[12] && x[13] == Val::Text(p)
}

/// The positions of `row3` the query reads.
pub proof fn lemma_row3(sv: StoresView, a: int, b: int, d: int)
    requires stores_wf(sv), 0 <= a < ps_n(sv), 0 <= b < supp_n(sv), 0 <= d < nat_n(sv),
    ensures ({
        let x = row3(sv, a, b, d);
        &&& x.len() == 16
        &&& x.subrange(0, 5) == ps_rows(sv)[a]
        &&& x[0] == Val::Int(ps_pkeys(sv)[a] as int)
        &&& x[1] == Val::Int(ps_skeys(sv)[a] as int)
        &&& x[2] == Val::Int(ps_aqs(sv)[a] as int)
        &&& x[3] == Val::Num { coeff: ps_costs(sv)[a] as int, scale: 2 }
        &&& x[5] == Val::Int(s_keys(sv)[b] as int)
        &&& x[8] == Val::Int(s_nks(sv)[b] as int)
        &&& x[12] == Val::Int(n_keys(sv)[d] as int)
        &&& x[13] == Val::Text(n_name(sv, d))
    }),
{
    let pa = ps_rows(sv)[a];
    let sb = supp_rows(sv)[b];
    let nd = nat_rows(sv)[d];
    assert(pa == psi::row_at(sv.flat_partsupp, a));
    assert(sb == si::row_at(sv.flat_supplier, b));
    assert(nd == ni::row_at(sv.flat_nation, d));
    let x = pa + sb + nd;
    assert(pa.len() == 5 && sb.len() == 7 && nd.len() == 4);
    assert(x.subrange(0, 5) =~= pa);
}

/// `qualx` on `row3` is `qual3`.
pub proof fn lemma_qualx_row3(sv: StoresView, p: Seq<u8>, a: int, b: int, d: int)
    requires stores_wf(sv), 0 <= a < ps_n(sv), 0 <= b < supp_n(sv), 0 <= d < nat_n(sv),
    ensures qualx(p, row3(sv, a, b, d)) == qual3(sv, p, a, b, d),
{
    lemma_row3(sv, a, b, d);
}

/// `|ps_supplycost| < 10^15` and `ps_availqty` an `i64`: the exact product is far inside `i128` (`|v| < 2^113`).
pub proof fn lemma_val_bound(sv: StoresView, c: int)
    requires stores_wf(sv), bounds_ok(sv), 0 <= c < ps_n(sv),
    ensures -0x2_0000_0000_0000_0000_0000_0000_0000 < val(sv, c) < 0x2_0000_0000_0000_0000_0000_0000_0000,
{
    let x = ps_costs(sv)[c] as int;
    let y = ps_aqs(sv)[c] as int;
    assert(-cost_bound() < x < cost_bound());
    lemma_product_bound(x, y);
}

/// `|x| < 10^15` and `y` an `i64`: `|x * y| < 2^113`.
pub proof fn lemma_product_bound(x: int, y: int)
    requires -1_000_000_000_000_000 < x < 1_000_000_000_000_000, -0x8000_0000_0000_0000 <= y <= 0x7fff_ffff_ffff_ffff,
    ensures -0x2_0000_0000_0000_0000_0000_0000_0000 < x * y < 0x2_0000_0000_0000_0000_0000_0000_0000,
{
    let bx: int = 0x4_0000_0000_0000;
    let by: int = 0x8000_0000_0000_0000;
    assert(-bx < x < bx);
    assert(-by <= y <= by);
    assert(bx * by == 0x2_0000_0000_0000_0000_0000_0000_0000);
    assert(-bx * by < x * y < bx * by) by (nonlinear_arith)
        requires -bx < x < bx, -by <= y <= by, bx > 0, by > 0;
}

/// The WHERE condition, the group key and the SUM argument on `pre ++ row3(a, b, d)` with the condition and the
/// argument at offset `|pre|`.
pub proof fn lemma_row_eval(db: Database, sv: StoresView, p: Seq<u8>, pre: Row, a: int, b: int, d: int)
    requires stores_wf(sv), bounds_ok(sv), 0 <= a < ps_n(sv), 0 <= b < supp_n(sv), 0 <= d < nat_n(sv),
    ensures ({
        let env = pre + row3(sv, a, b, d);
        let o = pre.len();
        &&& eval_pred(db, env, where_pred(o, Literal::Text(p))) == Ok::<Truth, SqlError>(truth_of(qual3(sv, p, a, b, d)))
        &&& eval_expr(db, env, arg_expr(o)) == Ok::<Val, SqlError>(Val::Num { coeff: val(sv, a), scale: 2 })
        &&& eval_expr(db, env, Expr::Col(o)) == Ok::<Val, SqlError>(Val::Int(ps_pkeys(sv)[a] as int))
    }),
{
    lemma_row3(sv, a, b, d);
    let x = row3(sv, a, b, d);
    let env = pre + x;
    let o = pre.len();
    assert forall|i: int| 0 <= i < 16 implies #[trigger] env[o + i] == x[i] by {}
    let (c1, c5, c8, c12, c13) = ((o + 1) as nat, (o + 5) as nat, (o + 8) as nat, (o + 12) as nat, (o + 13) as nat);
    assert(env[c1 as int] == x[1] && env[c5 as int] == x[5] && env[c8 as int] == x[8]);
    assert(env[c12 as int] == x[12] && env[c13 as int] == x[13]);
    // ps_suppkey = s_suppkey
    lemma_expr_col(db, env, c1);
    lemma_expr_col(db, env, c5);
    let (sk, skey) = (ps_skeys(sv)[a] as int, s_keys(sv)[b] as int);
    lemma_compare_int(sk, skey);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(c1), Expr::Col(c5), Val::Int(sk), Val::Int(skey), sk, skey);
    // s_nationkey = n_nationkey
    lemma_expr_col(db, env, c8);
    lemma_expr_col(db, env, c12);
    let (nk, nkey) = (s_nks(sv)[b] as int, n_keys(sv)[d] as int);
    lemma_compare_int(nk, nkey);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(c8), Expr::Col(c12), Val::Int(nk), Val::Int(nkey), nk, nkey);
    lemma_pred_and(db, env, eq_cols(c1, c5), eq_cols(c8, c12), sk == skey, nk == nkey);
    // n_name = $1
    lemma_expr_col(db, env, c13);
    lemma_expr_text(db, env, p);
    lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(c13), Expr::Lit(Literal::Text(p)), n_name(sv, d), p);
    lemma_pred_and(db, env, and(eq_cols(c1, c5), eq_cols(c8, c12)), eq_lit(c13, Literal::Text(p)),
        sk == skey && nk == nkey, n_name(sv, d) == p);
    // ps_supplycost * ps_availqty
    let (c2, c3) = ((o + 2) as nat, (o + 3) as nat);
    assert(env[c2 as int] == x[2] && env[c3 as int] == x[3]);
    lemma_expr_col(db, env, c2);
    lemma_expr_col(db, env, c3);
    let cast_e = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Col(c2)) };
    assert(eval_expr(db, env, cast_e) == Ok::<Val, SqlError>(Val::Num { coeff: ps_aqs(sv)[a] as int, scale: 0 }));
    lemma_val_bound(sv, a);
    lemma_num_in_range_small(val(sv, a), 2);
    assert(num_arith(ArithOp::Mul, ps_costs(sv)[a] as int, 2, ps_aqs(sv)[a] as int, 0) == (val(sv, a), 2nat));
    assert(eval_expr(db, env, arg_expr(o)) == Ok::<Val, SqlError>(Val::Num { coeff: val(sv, a), scale: 2 }));
    // ps_partkey
    assert(env[o as int] == x[0]);
    lemma_expr_col(db, env, o);
}

} // verus!
