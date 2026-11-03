//! The statement's FROM/WHERE tree on a database whose `sub`, `num` and `pre` tables are the flat parts (`db_ok`):
//! its input to GROUP BY evaluates to the rows of `num x sub x pre` kept by `qual` (`lemma_input`), and `qual` of
//! a joined row is `joined_ok` of its three source rows (`lemma_qual_cells`).
//!
//! Proof outline: the tree `((num x sub) WHERE n.adsh = s.adsh) x pre`, filtered by the ON condition of `pre` and
//! by the WHERE clause, is composed with `link::join` (`lemma_eval_table`, `lemma_eval_product`,
//! `lemma_eval_filter`). The WHERE clause is three-valued (`stmt` and `fy` may be NULL), so its filter keeps the
//! rows whose condition is `True` (`lemma_filter_true`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::scalar::*;
use crate::spec::int::*;
use crate::spec::constraints::*;
use crate::spec::types::Constraint;
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::bridge::equality::lemma_row_not_distinct_refl;
use crate::exec::relational::domain::lemma_collect_pointwise;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::{proj, text_wf};
use crate::link::source::lemma_proj_all_index;
use crate::link::join::*;
use crate::link::expr::*;
use crate::stores::flat_num::interface as ni;
use crate::stores::flat_sub::interface as si;
use crate::stores::flat_pre::interface as pi;
use crate::agent::ctx::*;

verus! {

// ------------------------------------------------------------------------------------------------ AST nodes

/// `n.adsh = s.adsh` on `num x sub`.
pub open spec fn p_ns() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) }
}

pub open spec fn q_ns() -> Query {
    Query::Filter { pred: p_ns(), input: Box::new(Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) }) }
}

/// The ON condition of `pre`: same adsh, tag and version.
pub open spec fn p_on() -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(29) }),
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(1), b: Expr::Col(35) }),
        )),
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(2), b: Expr::Col(36) }),
    )
}

pub open spec fn q_nsp() -> Query {
    Query::Product { left: Box::new(q_ns()), right: Box::new(Query::Table(3)) }
}

pub open spec fn q_on() -> Query {
    Query::Filter { pred: p_on(), input: Box::new(q_nsp()) }
}

/// The WHERE clause: `uom = $1 AND stmt = $2 AND fy = $3 AND value IS NOT NULL`.
pub open spec fn p_w(l0: Literal, l1: Literal, l2: Literal) -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::And(
                Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(l0) }),
                Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(32), b: Expr::Lit(l1) }),
            )),
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Lit(l2) }),
        )),
        Box::new(Pred::Not(Box::new(Pred::IsNull(Expr::Col(7))))),
    )
}

pub open spec fn q_input(l0: Literal, l1: Literal, l2: Literal) -> Query {
    Query::Filter { pred: p_w(l0, l1, l2), input: Box::new(q_on()) }
}

pub open spec fn g_keys() -> Seq<Expr> {
    seq![Expr::Col(11), Expr::Col(32), Expr::Col(1), Expr::Col(37)]
}

pub open spec fn g_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(7) }, Agg::CountStar]
}

pub open spec fn q_body(l0: Literal, l1: Literal, l2: Literal) -> Query {
    Query::GroupBy { keys: g_keys(), aggs: g_aggs(), input: Box::new(q_input(l0, l1, l2)) }
}

pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 4, desc: true, nulls_first: true }]
}

/// The generated statement, named node by node.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures
        crate::query::query_spec_at(ps).body == q_body(ps[0], ps[1], ps[2]),
        crate::query::query_spec_at(ps).keys == order_keys(),
        crate::query::query_spec_at(ps).limit == Some(200nat),
        crate::query::query_spec_at(ps).offset == 0,
{
}

// ------------------------------------------------------------------------------------------------ the database

#[verifier::opaque]
pub open spec fn nrow(c: Ctx, i: int) -> Row {
    ni::row_at(c.np, i)
}

#[verifier::opaque]
pub open spec fn srow(c: Ctx, s: int) -> Row {
    si::row_at(c.sp, s)
}

#[verifier::opaque]
pub open spec fn prow(c: Ctx, k: int) -> Row {
    pi::row_at(c.pp, k)
}

/// The `sub` rows' adsh identify them (the declared primary key of `sub`).
pub open spec fn sub_key(c: Ctx) -> bool {
    forall|s1: int, s2: int| 0 <= s1 < c.m && 0 <= s2 < c.m && #[trigger] s_adsh(c, s1) == #[trigger] s_adsh(c, s2)
        ==> s1 == s2
}

/// `db`'s `sub`, `num` and `pre` tables are the rows of the parts of `c`, and `sub`'s adsh identifies its rows.
pub open spec fn db_ok(db: Database, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& db.tables.len() == 4
    &&& db.tables[1].len() == c.n
    &&& db.tables[0].len() == c.m
    &&& db.tables[3].len() == c.q
    &&& forall|i: int| 0 <= i < c.n ==> #[trigger] db.tables[1][i] == nrow(c, i)
    &&& forall|s: int| 0 <= s < c.m ==> #[trigger] db.tables[0][s] == srow(c, s)
    &&& forall|k: int| 0 <= k < c.q ==> #[trigger] db.tables[3][k] == prow(c, k)
    &&& sub_key(c)
}

/// The binding: `$1` and `$2` are the texts `c.uom` and `c.stmt`, `$3` the int4 `c.fy`.
pub open spec fn lits_ok(c: Ctx, ps: Seq<Literal>) -> bool {
    &&& ps.len() == 3
    &&& ps[0] == Literal::Text(c.uom)
    &&& ps[1] == Literal::Text(c.stmt)
    &&& ps[2] == (Literal::Int { v: c.fy, kind: IntKind::Int4 })
    &&& int_in_range(IntKind::Int4, c.fy)
}

/// The value cells of the three source rows.
pub proof fn lemma_cells(c: Ctx, i: int, s: int, k: int)
    ensures
        nrow(c, i).len() == 9,
        nrow(c, i)[0] == Val::Text(n_adsh(c, i)),
        nrow(c, i)[1] == Val::Text(n_tag(c, i)),
        nrow(c, i)[2] == Val::Text(n_ver(c, i)),
        nrow(c, i)[5] == Val::Text(n_uom(c, i)),
        nrow(c, i)[7] == (Val::Num { coeff: n_val(c, i), scale: 4 }),
        srow(c, s).len() == 20,
        srow(c, s)[0] == Val::Text(s_adsh(c, s)),
        srow(c, s)[2] == Val::Text(s_name(c, s)),
        srow(c, s)[10] == (if s_fyv_s(c)[s] == 0 { Val::Null } else { Val::Int(s_fy_s(c)[s] as int) }),
        prow(c, k).len() == 10,
        prow(c, k)[0] == Val::Text(p_adsh(c, k)),
        prow(c, k)[3] == (if p_stmtv_s(c)[k] == 0 { Val::Null } else { Val::Text(p_stmt(c, k)) }),
        prow(c, k)[6] == Val::Text(p_tag(c, k)),
        prow(c, k)[7] == Val::Text(p_ver(c, k)),
        prow(c, k)[8] == p_plabel_val(c, k),
{
    reveal(nrow);
    reveal(srow);
    reveal(prow);
}

/// Every database bound to the parts of `c` is `db_ok` for `c`.
pub proof fn lemma_bound(sv: StoresView, db: Database, c: Ctx)
    requires
        crate::gendb_entry::bound_db(sv, db),
        ctx_ok(c),
        c.np == sv.flat_num,
        c.sp == sv.flat_sub,
        c.pp == sv.flat_pre,
    ensures db_ok(db, c),
{
    reveal(ctx_ok);
    reveal(nrow);
    reveal(srow);
    reveal(prow);
    let nrels = crate::stores::flat_num::declaration::stored_relations(db);
    let srels = crate::stores::flat_sub::declaration::stored_relations(db);
    let prels = crate::stores::flat_pre::declaration::stored_relations(db);
    crate::stores::flat_num::declaration::lemma_declared_schema();
    crate::stores::flat_sub::declaration::lemma_declared_schema();
    crate::stores::flat_pre::declaration::lemma_declared_schema();
    let nn = db.tables[1];
    let ss = db.tables[0];
    let pp = db.tables[3];
    let ncols = crate::stores::flat_num::declaration::stored_cols_t0();
    let scols = crate::stores::flat_sub::declaration::stored_cols_t0();
    let pcols = crate::stores::flat_pre::declaration::stored_cols_t0();
    lemma_proj_all_index(nn, ncols);
    lemma_proj_all_index(ss, scols);
    lemma_proj_all_index(pp, pcols);
    // Row counts: the parts determine them.
    assert(ni::text_view(c.np, ni::ADSH_OFFSETS as int, ni::ADSH_BYTES as int).offsets.len() == nrels[0].len() + 1);
    assert(ni::text_view(c.np, ni::ADSH_OFFSETS as int, ni::ADSH_BYTES as int).offsets.len() == c.n + 1);
    assert(si::text_view(c.sp, si::ADSH_OFFSETS as int, si::ADSH_BYTES as int).offsets.len() == srels[0].len() + 1);
    assert(si::text_view(c.sp, si::ADSH_OFFSETS as int, si::ADSH_BYTES as int).offsets.len() == c.m + 1);
    assert(pi::text_view(c.pp, pi::ADSH_OFFSETS as int, pi::ADSH_BYTES as int).offsets.len() == prels[0].len() + 1);
    assert(pi::text_view(c.pp, pi::ADSH_OFFSETS as int, pi::ADSH_BYTES as int).offsets.len() == c.q + 1);
    assert forall|i: int| 0 <= i < c.n implies #[trigger] db.tables[1][i] == nrow(c, i) by {
        assert(crate::spec::typing::row_in_table(nn[i], db.schema[1]));
        assert(nn[i].len() == 9);
        assert(nrels[0][i] == ni::row_at(c.np, i));
        assert(proj(nn[i], ncols) =~= nn[i]);
    }
    assert forall|s: int| 0 <= s < c.m implies #[trigger] db.tables[0][s] == srow(c, s) by {
        assert(crate::spec::typing::row_in_table(ss[s], db.schema[0]));
        assert(ss[s].len() == 20);
        assert(srels[0][s] == si::row_at(c.sp, s));
        assert(proj(ss[s], scols) =~= ss[s]);
    }
    assert forall|k: int| 0 <= k < c.q implies #[trigger] db.tables[3][k] == prow(c, k) by {
        assert(crate::spec::typing::row_in_table(pp[k], db.schema[3]));
        assert(pp[k].len() == 10);
        assert(prels[0][k] == pi::row_at(c.pp, k));
        assert(proj(pp[k], pcols) =~= pp[k]);
    }
    // The primary key of sub.
    let ddb = crate::gendb_constraints::declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    assert(ddb.schema[0].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert forall|s1: int, s2: int| 0 <= s1 < c.m && 0 <= s2 < c.m && #[trigger] s_adsh(c, s1) == #[trigger] s_adsh(c, s2)
        implies s1 == s2 by {
        assert(ss[s1] == srow(c, s1));
        assert(ss[s2] == srow(c, s2));
        lemma_cells(c, 0, s1, 0);
        lemma_cells(c, 0, s2, 0);
        assert(ddb.tables[0][s1][0] == ddb.tables[0][s2][0]);
        let k1 = key_of(ddb.tables[0][s1], seq![0nat]);
        let k2 = key_of(ddb.tables[0][s2], seq![0nat]);
        assert(k1 =~= k2);
        lemma_row_not_distinct_refl(k1);
        crate::bridge::constraints::lemma_primary_key_identifies(ddb, 0, 0, seq![0nat], true, s1, s2);
    }
}


// ------------------------------------------------------------------------------------------------ joined rows

/// The joined relation `(num x sub) x pre` of `db`.
pub open spec fn jrows(db: Database) -> Seq<Row> {
    product_rows(product_rows(db.tables[1], db.tables[0]), db.tables[3])
}

/// `num` row `i`, `sub` row `s` and `pre` row `k` satisfy the join and WHERE conditions.
pub open spec fn joined_ok(c: Ctx, i: int, s: int, k: int) -> bool {
    &&& n_adsh(c, i) == s_adsh(c, s)
    &&& n_adsh(c, i) == p_adsh(c, k)
    &&& n_tag(c, i) == p_tag(c, k)
    &&& n_ver(c, i) == p_ver(c, k)
    &&& n_uom(c, i) == c.uom
    &&& p_stmtv_s(c)[k] != 0
    &&& p_stmt(c, k) == c.stmt
    &&& s_fyv_s(c)[s] != 0
    &&& s_fy_s(c)[s] as int == c.fy
}

/// `n.adsh = s.adsh` on a `num x sub` row.
pub open spec fn f_ns(y: Row) -> bool {
    y[0] == y[9]
}

/// The ON condition of `pre` on a joined row.
pub open spec fn f_on(x: Row) -> bool {
    x[0] == x[29] && x[1] == x[35] && x[2] == x[36]
}

/// The WHERE clause is `True` on a joined row.
pub open spec fn f_w(c: Ctx, x: Row) -> bool {
    x[5] == Val::Text(c.uom) && x[32] == Val::Text(c.stmt) && x[19] == Val::Int(c.fy)
}

/// The qualifying condition of a joined row (the conjunction of all conditions of the tree).
pub open spec fn qual_of(c: Ctx) -> spec_fn(Row) -> bool {
    |x: Row| f_ns(left_of(x, 29)) && f_on(x) && f_w(c, x)
}

pub open spec fn tt() -> spec_fn(Row) -> bool {
    |r: Row| true
}

/// A joined row with its source rows.
pub open spec fn jrow(c: Ctx, i: int, s: int, k: int) -> Row {
    nrow(c, i) + srow(c, s) + prow(c, k)
}

/// The cells of a joined row the conditions, keys and arguments read.
pub proof fn lemma_jcells(c: Ctx, i: int, s: int, k: int)
    ensures ({
        let x = jrow(c, i, s, k);
        &&& x.len() == 39
        &&& x[0] == Val::Text(n_adsh(c, i))
        &&& x[1] == Val::Text(n_tag(c, i))
        &&& x[2] == Val::Text(n_ver(c, i))
        &&& x[5] == Val::Text(n_uom(c, i))
        &&& x[7] == (Val::Num { coeff: n_val(c, i), scale: 4 })
        &&& x[9] == Val::Text(s_adsh(c, s))
        &&& x[11] == Val::Text(s_name(c, s))
        &&& x[19] == (if s_fyv_s(c)[s] == 0 { Val::Null } else { Val::Int(s_fy_s(c)[s] as int) })
        &&& x[29] == Val::Text(p_adsh(c, k))
        &&& x[32] == (if p_stmtv_s(c)[k] == 0 { Val::Null } else { Val::Text(p_stmt(c, k)) })
        &&& x[35] == Val::Text(p_tag(c, k))
        &&& x[36] == Val::Text(p_ver(c, k))
        &&& x[37] == p_plabel_val(c, k)
        &&& left_of(x, 29) == nrow(c, i) + srow(c, s)
        &&& right_of(x, 29) == prow(c, k)
    }),
{
    lemma_cells(c, i, s, k);
    let x = jrow(c, i, s, k);
    let ns = nrow(c, i) + srow(c, s);
    assert(x[0] == nrow(c, i)[0]);
    assert(x[1] == nrow(c, i)[1]);
    assert(x[2] == nrow(c, i)[2]);
    assert(x[5] == nrow(c, i)[5]);
    assert(x[7] == nrow(c, i)[7]);
    assert(x[9] == srow(c, s)[0]);
    assert(x[11] == srow(c, s)[2]);
    assert(x[19] == srow(c, s)[10]);
    assert(x[29] == prow(c, k)[0]);
    assert(x[32] == prow(c, k)[3]);
    assert(x[35] == prow(c, k)[6]);
    assert(x[36] == prow(c, k)[7]);
    assert(x[37] == prow(c, k)[8]);
    assert(left_of(x, 29) =~= ns);
    assert(right_of(x, 29) =~= prow(c, k));
}

/// The qualifying condition of a joined row is `joined_ok` of its source rows.
pub proof fn lemma_qual_cells(c: Ctx, i: int, s: int, k: int)
    ensures (qual_of(c))(jrow(c, i, s, k)) == joined_ok(c, i, s, k),
{
    lemma_jcells(c, i, s, k);
    let x = jrow(c, i, s, k);
    let ns = nrow(c, i) + srow(c, s);
    lemma_cells(c, i, s, k);
    assert(ns[0] == nrow(c, i)[0]);
    assert(ns[9] == srow(c, s)[0]);
}

/// Every row of the joined relation is a joined row of source rows.
pub proof fn lemma_jrow_of(db: Database, c: Ctx, x: Row) -> (r: (int, int, int))
    requires db_ok(db, c), jrows(db).contains(x),
    ensures
        0 <= r.0 < c.n, 0 <= r.1 < c.m, 0 <= r.2 < c.q,
        x == jrow(c, r.0, r.1, r.2),
{
    let ns = product_rows(db.tables[1], db.tables[0]);
    let jr = jrows(db);
    lemma_product_rows_elems(ns, db.tables[3]);
    lemma_product_rows_elems(db.tables[1], db.tables[0]);
    let t = choose|t: int| 0 <= t < jr.len() && jr[t] == x;
    assert(is_concat(jr[t], ns, db.tables[3]));
    let (a, k) = choose|a: int, k: int| 0 <= a < ns.len() && 0 <= k < db.tables[3].len() && jr[t] == #[trigger] ns[a] + #[trigger] db.tables[3][k];
    assert(is_concat(ns[a], db.tables[1], db.tables[0]));
    let (i, s) = choose|i: int, s: int| 0 <= i < db.tables[1].len() && 0 <= s < db.tables[0].len() && ns[a] == #[trigger] db.tables[1][i] + #[trigger] db.tables[0][s];
    (i, s, k)
}

// ------------------------------------------------------------------------------------------------ conditions

/// `n.adsh = s.adsh` on a `num x sub` row is two-valued.
pub proof fn lemma_ns_cond(db: Database, c: Ctx, i: int, s: int)
    ensures eval_pred(db, nrow(c, i) + srow(c, s), p_ns()) == Ok::<Truth, SqlError>(truth_of(f_ns(nrow(c, i) + srow(c, s)))),
{
    lemma_cells(c, i, s, 0);
    let y = nrow(c, i) + srow(c, s);
    assert(y[0] == nrow(c, i)[0]);
    assert(y[9] == srow(c, s)[0]);
    lemma_expr_col(db, y, 0);
    lemma_expr_col(db, y, 9);
    lemma_pred_text_cmp(db, y, CmpOp::Eq, Expr::Col(0), Expr::Col(9), n_adsh(c, i), s_adsh(c, s));
}

/// The ON condition of `pre` on a joined row is two-valued.
pub proof fn lemma_on_cond(db: Database, c: Ctx, i: int, s: int, k: int)
    ensures eval_pred(db, jrow(c, i, s, k), p_on()) == Ok::<Truth, SqlError>(truth_of(f_on(jrow(c, i, s, k)))),
{
    lemma_jcells(c, i, s, k);
    let x = jrow(c, i, s, k);
    lemma_expr_col(db, x, 0);
    lemma_expr_col(db, x, 1);
    lemma_expr_col(db, x, 2);
    lemma_expr_col(db, x, 29);
    lemma_expr_col(db, x, 35);
    lemma_expr_col(db, x, 36);
    let a1 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(29) };
    let a2 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(1), b: Expr::Col(35) };
    let a3 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(2), b: Expr::Col(36) };
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(0), Expr::Col(29), n_adsh(c, i), p_adsh(c, k));
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(1), Expr::Col(35), n_tag(c, i), p_tag(c, k));
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(2), Expr::Col(36), n_ver(c, i), p_ver(c, k));
    lemma_pred_and(db, x, a1, a2, n_adsh(c, i) == p_adsh(c, k), n_tag(c, i) == p_tag(c, k));
    lemma_pred_and(db, x, Pred::And(Box::new(a1), Box::new(a2)), a3,
        n_adsh(c, i) == p_adsh(c, k) && n_tag(c, i) == p_tag(c, k), n_ver(c, i) == p_ver(c, k));
}

/// A text-or-NULL cell compared with a text literal: `Unknown` for NULL, else equality.
pub proof fn lemma_text_lit_cmp(db: Database, env: Row, col: nat, b: Seq<u8>)
    requires col < env.len(), env[col as int] is Null || env[col as int] is Text,
    ensures
        eval_pred(db, env, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(col), b: Expr::Lit(Literal::Text(b)) })
            == Ok::<Truth, SqlError>(if env[col as int] is Null { Truth::Unknown } else { truth_of(env[col as int] == Val::Text(b)) }),
{
    lemma_expr_col(db, env, col);
    lemma_expr_text(db, env, b);
    if env[col as int] is Text {
        lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(col), Expr::Lit(Literal::Text(b)), env[col as int]->Text_0, b);
    }
}

/// An int4-or-NULL cell compared with an int4 literal: `Unknown` for NULL, else equality.
pub proof fn lemma_int_lit_cmp(db: Database, env: Row, col: nat, v: int)
    requires col < env.len(), env[col as int] is Null || env[col as int] is Int, int_in_range(IntKind::Int4, v),
    ensures
        eval_pred(db, env, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(col), b: Expr::Lit(Literal::Int { v, kind: IntKind::Int4 }) })
            == Ok::<Truth, SqlError>(if env[col as int] is Null { Truth::Unknown } else { truth_of(env[col as int] == Val::Int(v)) }),
{
    let l = Literal::Int { v, kind: IntKind::Int4 };
    lemma_expr_col(db, env, col);
    assert(eval_expr(db, env, Expr::Lit(l)) == Ok::<Val, SqlError>(Val::Int(v)));
    if env[col as int] is Int {
        let x = env[col as int]->Int_0;
        lemma_compare_int(x, v);
        lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(col), Expr::Lit(l), env[col as int], Val::Int(v), x, v);
    }
}

/// The WHERE clause on a joined row: never an error, `True` exactly when `f_w`.
#[verifier::spinoff_prover]
pub proof fn lemma_w_cond(db: Database, c: Ctx, ps: Seq<Literal>, i: int, s: int, k: int)
    requires lits_ok(c, ps),
    ensures
        eval_pred(db, jrow(c, i, s, k), p_w(ps[0], ps[1], ps[2])) is Ok,
        (eval_pred(db, jrow(c, i, s, k), p_w(ps[0], ps[1], ps[2])) == Ok::<Truth, SqlError>(Truth::True))
            == f_w(c, jrow(c, i, s, k)),
{
    lemma_jcells(c, i, s, k);
    let x = jrow(c, i, s, k);
    let a1 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(ps[0]) };
    let a2 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(32), b: Expr::Lit(ps[1]) };
    let a3 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Lit(ps[2]) };
    let a4 = Pred::Not(Box::new(Pred::IsNull(Expr::Col(7))));
    lemma_text_lit_cmp(db, x, 5, c.uom);
    lemma_text_lit_cmp(db, x, 32, c.stmt);
    lemma_int_lit_cmp(db, x, 19, c.fy);
    lemma_expr_col(db, x, 7);
    assert(eval_pred(db, x, Pred::IsNull(Expr::Col(7))) == Ok::<Truth, SqlError>(Truth::False));
    assert(eval_pred(db, x, a4) == Ok::<Truth, SqlError>(Truth::True));
    let t1 = truth_of(x[5] == Val::Text(c.uom));
    let t2 = if x[32] is Null { Truth::Unknown } else { truth_of(x[32] == Val::Text(c.stmt)) };
    let t3 = if x[19] is Null { Truth::Unknown } else { truth_of(x[19] == Val::Int(c.fy)) };
    assert(eval_pred(db, x, Pred::And(Box::new(a1), Box::new(a2))) == Ok::<Truth, SqlError>(truth_and(t1, t2)));
    assert(eval_pred(db, x, Pred::And(Box::new(Pred::And(Box::new(a1), Box::new(a2))), Box::new(a3)))
        == Ok::<Truth, SqlError>(truth_and(truth_and(t1, t2), t3)));
    assert(eval_pred(db, x, p_w(ps[0], ps[1], ps[2])) == Ok::<Truth, SqlError>(truth_and(truth_and(truth_and(t1, t2), t3), Truth::True)));
}

// ------------------------------------------------------------------------------------------------ filters

/// SQL WHERE keeps the rows whose truth is `True`.
pub proof fn lemma_keep_true_is(rows: Seq<Row>, truths: Seq<Truth>, f: spec_fn(Row) -> bool)
    requires
        truths.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] truths[i] is True) == f(rows[i]),
    ensures keep_true(rows, truths) == keep(rows, f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < ri.len() implies (#[trigger] ti[i] is True) == f(ri[i]) by {
            assert(ti[i] == truths[i] && ri[i] == rows[i]);
        }
        lemma_keep_true_is(ri, ti, f);
        assert((truths[rows.len() - 1] is True) == f(rows[rows.len() - 1]));
    }
}

/// A WHERE over kept rows whose condition evaluates without error: the rows kept by both conditions.
pub proof fn lemma_filter_true(db: Database, src: Query, rows: Seq<Row>, f: spec_fn(Row) -> bool, pred: Pred, fh: spec_fn(Row) -> bool)
    requires
        eval_query(db, Seq::empty(), src) == Ok::<Relation, SqlError>(keep(rows, f)),
        forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) ==> eval_pred(db, rows[i], pred) is Ok,
        forall|i: int| 0 <= i < rows.len() ==> fh(#[trigger] rows[i])
            == (f(rows[i]) && eval_pred(db, rows[i], pred) == Ok::<Truth, SqlError>(Truth::True)),
    ensures
        eval_query(db, Seq::empty(), Query::Filter { pred, input: Box::new(src) }) == Ok::<Relation, SqlError>(keep(rows, fh)),
{
    let kept = keep(rows, f);
    let ctx = Seq::<Val>::empty();
    let h = |x: Row| eval_pred(db, x, pred) == Ok::<Truth, SqlError>(Truth::True);
    lemma_keep_members(rows, f);
    let truths = Seq::new(kept.len(), |i: int| eval_pred(db, kept[i], pred)->Ok_0);
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
    lemma_keep_true_is(kept, truths, h);
    lemma_keep_keep(rows, f, h);
    lemma_keep_ext(rows, |x: Row| f(x) && h(x), fh);
}

/// Row `a` of `num x sub` is a `num` row followed by a `sub` row (29 columns).
pub proof fn lemma_ns_row_of(db: Database, c: Ctx, a: int) -> (r: (int, int))
    requires db_ok(db, c), 0 <= a < product_rows(db.tables[1], db.tables[0]).len(),
    ensures
        0 <= r.0 < c.n, 0 <= r.1 < c.m,
        product_rows(db.tables[1], db.tables[0])[a] == nrow(c, r.0) + srow(c, r.1),
        product_rows(db.tables[1], db.tables[0])[a].len() == 29,
{
    let ns = product_rows(db.tables[1], db.tables[0]);
    lemma_product_rows_elems(db.tables[1], db.tables[0]);
    assert(is_concat(ns[a], db.tables[1], db.tables[0]));
    let (i, s) = choose|i: int, s: int| 0 <= i < db.tables[1].len() && 0 <= s < db.tables[0].len() && ns[a] == #[trigger] db.tables[1][i] + #[trigger] db.tables[0][s];
    assert(db.tables[1][i] == nrow(c, i) && db.tables[0][s] == srow(c, s));
    lemma_cells(c, i, s, 0);
    (i, s)
}

/// The input of the GROUP BY: the joined rows kept by `qual_of(c)`.
#[verifier::spinoff_prover]
pub proof fn lemma_input(db: Database, c: Ctx, ps: Seq<Literal>)
    requires db_ok(db, c), lits_ok(c, ps),
    ensures eval_query(db, Seq::empty(), q_input(ps[0], ps[1], ps[2])) == Ok::<Relation, SqlError>(keep(jrows(db), qual_of(c))),
{
    let nn = db.tables[1];
    let ss = db.tables[0];
    let pp = db.tables[3];
    let ns = product_rows(nn, ss);
    let jr = jrows(db);
    let t = tt();
    lemma_eval_table(db, 1, t);
    lemma_eval_table(db, 0, t);
    lemma_eval_table(db, 3, t);
    assert forall|i: int| 0 <= i < nn.len() implies (#[trigger] nn[i]).len() == 9 by {
        lemma_cells(c, i, 0, 0);
    }
    assert forall|a: int| 0 <= a < ns.len() implies (#[trigger] ns[a]).len() == 29 by {
        lemma_ns_row_of(db, c, a);
    }
    // num x sub
    lemma_eval_product(db, Query::Table(1), Query::Table(0), nn, t, 9, ss, t, ns, t);
    // WHERE n.adsh = s.adsh
    assert forall|a: int| 0 <= a < ns.len() && t(#[trigger] ns[a]) implies
        eval_pred(db, ns[a], p_ns()) == Ok::<Truth, SqlError>(truth_of(f_ns(ns[a]))) by {
        let (i, s) = lemma_ns_row_of(db, c, a);
        lemma_ns_cond(db, c, i, s);
    }
    lemma_eval_filter(db, Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) }, ns, t, p_ns(),
        |y: Row| f_ns(y), |y: Row| f_ns(y));
    assert(eval_query(db, Seq::empty(), q_ns()) == Ok::<Relation, SqlError>(keep(ns, |y: Row| f_ns(y))));
    // x pre
    let fp = |x: Row| f_ns(left_of(x, 29));
    lemma_product_rows_elems(ns, pp);
    assert forall|r: int| 0 <= r < jr.len() implies #[trigger] fp(jr[r]) == ((|y: Row| f_ns(y))(left_of(jr[r], 29)) && t(right_of(jr[r], 29))) by {}
    lemma_eval_product(db, q_ns(), Query::Table(3), ns, |y: Row| f_ns(y), 29, pp, t, jr, fp);
    // ON
    let f2 = |x: Row| fp(x) && f_on(x);
    assert forall|r: int| 0 <= r < jr.len() && fp(#[trigger] jr[r]) implies
        eval_pred(db, jr[r], p_on()) == Ok::<Truth, SqlError>(truth_of(f_on(jr[r]))) by {
        assert(jr.contains(jr[r]));
        let (i, s, k) = lemma_jrow_of(db, c, jr[r]);
        lemma_on_cond(db, c, i, s, k);
    }
    lemma_eval_filter(db, q_nsp(), jr, fp, p_on(), |x: Row| f_on(x), f2);
    // WHERE
    let q = qual_of(c);
    assert forall|r: int| 0 <= r < jr.len() implies
        (f2(#[trigger] jr[r]) ==> eval_pred(db, jr[r], p_w(ps[0], ps[1], ps[2])) is Ok)
        && q(jr[r]) == (f2(jr[r]) && eval_pred(db, jr[r], p_w(ps[0], ps[1], ps[2])) == Ok::<Truth, SqlError>(Truth::True)) by {
        assert(jr.contains(jr[r]));
        let (i, s, k) = lemma_jrow_of(db, c, jr[r]);
        lemma_w_cond(db, c, ps, i, s, k);
    }
    lemma_filter_true(db, q_on(), jr, f2, p_w(ps[0], ps[1], ps[2]), q);
}

} // verus!
