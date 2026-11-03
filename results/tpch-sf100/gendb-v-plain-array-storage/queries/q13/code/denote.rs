//! The statement's meaning in terms of the normal form (`agent::normal`), for every database bound to the stored
//! parts.
//!
//! The body is `GroupBy[c_count](GroupBy[c_custkey](customer LEFT JOIN orders ON c_custkey = o_custkey AND NOT
//! o_comment LIKE $1))` (`q_outer`, `q_inner`, `q_join`). Steps:
//! 1. the ON condition of customer row `i` and orders row `j` is `c_custkey = o_custkey AND counted(j)` when the
//!    row's `LIKE` does not raise, else the `LIKE`'s error (`lemma_on`);
//! 2. the LEFT JOIN is `left_join_rows` of the tables under these truths (`lemma_join`), or 22025 when some
//!    `LIKE` raises and there is a customer (`lemma_join_err`);
//! 3. the join is one block of rows per customer, all with that customer's key; the keys are distinct (PRIMARY
//!    KEY), so the inner GROUP BY's groups are the customers in row order and each group's members are its block
//!    (`lemma_blocks`, `common::groups`); a block's non-NULL `o_orderkey` count is `ccnt` (`lemma_block_count`).
//!    Hence the inner GROUP BY is the per-customer outcome of `int_result(ccnt)` (`lemma_inner`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::fns::*;
use crate::spec::fns::like::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::query::{query_spec_at, param_domain};
use crate::schema::schema_spec;
use crate::bridge::collect::*;
use crate::exec::relational::domain::*;
use crate::link::expr::*;
use crate::link::capacity::{lemma_collect_uniform_err, lemma_group_prepared};
use crate::link::query::lemma_keep_true_member;
use crate::agent::common::segments::like_of;
use crate::agent::common::groups::*;
use crate::agent::tables::*;
use crate::agent::normal::*;

verus! {

// ------------------------------------------------------------------------------------------------ the AST

/// `c_custkey = o_custkey AND NOT o_comment LIKE $1` over a joined row (customer's 8 columns, then orders' 9).
pub open spec fn q_like(ps: Seq<Literal>) -> Expr {
    Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(16), Expr::Lit(ps[0]), Expr::Lit(Literal::Text(seq![92u8]))] }
}
pub open spec fn q_eq() -> Pred { Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) } }
pub open spec fn q_on(ps: Seq<Literal>) -> Pred {
    Pred::And(Box::new(q_eq()), Box::new(Pred::Not(Box::new(Pred::OfBool(q_like(ps))))))
}
pub open spec fn q_join(ps: Seq<Literal>) -> Query {
    Query::LeftJoin { left: Box::new(Query::Table(2)), right: Box::new(Query::Table(1)), on: q_on(ps) }
}
pub open spec fn q_inner_keys() -> Seq<Expr> { seq![Expr::Col(0)] }
pub open spec fn q_inner_aggs() -> Seq<Agg> { seq![Agg::Count(Expr::Col(8))] }
pub open spec fn q_inner(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: q_inner_keys(), aggs: q_inner_aggs(), input: Box::new(q_join(ps)) }
}
pub open spec fn q_outer_keys() -> Seq<Expr> { seq![Expr::Col(1)] }
pub open spec fn q_outer_aggs() -> Seq<Agg> { seq![Agg::CountStar] }
pub open spec fn q_outer(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: q_outer_keys(), aggs: q_outer_aggs(), input: Box::new(q_inner(ps)) }
}
/// `ORDER BY custdist DESC, c_count DESC`.
pub open spec fn q_order() -> Seq<OrderKey> {
    seq![OrderKey { col: 1, desc: true, nulls_first: true }, OrderKey { col: 0, desc: true, nulls_first: true }]
}

/// The statement at binding `ps`.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: q_outer(ps), keys: q_order(), limit: None, offset: 0nat }),
{
}

// ------------------------------------------------------------------------------------------------ the ON condition

/// The truth of the ON condition of customer row `i` and orders row `j` (when the row's `LIKE` does not raise).
pub open spec fn on_truth(sv: StoresView, pat: Seq<u8>, i: int, j: int) -> Truth {
    truth_of(cck(sv)[i] == ock(sv)[j] && counted(sv, pat, j))
}

/// The truths of every customer row against every orders row.
pub open spec fn truths(sv: StoresView, pat: Seq<u8>) -> Seq<Seq<Truth>> {
    Seq::new(n_c(sv) as nat, |i: int| Seq::new(n_o(sv) as nat, |j: int| on_truth(sv, pat, i, j)))
}

/// `$1` is the text `pat_of(ps)`.
proof fn lemma_param(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures ps[0] == Literal::Text(pat_of(ps)), lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Text(pat_of(ps))),
{
}

/// The `LIKE` call over a joined row whose comment is `t`.
proof fn lemma_like_call(db: Database, env: Row, ps: Seq<Literal>, t: Seq<u8>)
    requires param_domain(ps), env.len() == 17, env[16] == Val::Text(t),
    ensures eval_expr(db, env, q_like(ps)) == like_of(t, pat_of(ps)),
{
    hide(like_value);
    lemma_param(ps);
    let args = seq![Expr::Col(16), Expr::Lit(ps[0]), Expr::Lit(Literal::Text(seq![92u8]))];
    let vs = seq![Val::Text(t), Val::Text(pat_of(ps)), Val::Text(seq![92u8])];
    lemma_expr_col(db, env, 16);
    lemma_expr_text(db, env, seq![92u8]);
    lemma_expr_results_index(db, env, args);
    let rs = expr_results(db, env, args);
    assert forall|k: int| 0 <= k < rs.len() implies #[trigger] rs[k] == Ok::<Val, SqlError>(vs[k]) by {
        assert(rs[k] == eval_expr(db, env, args[k]));
    }
    lemma_collect_all(rs, vs);
    assert(eval_exprs(db, env, args) == Ok::<Row, SqlError>(vs));
    assert(apply_fn(ScalarFn::Like, vs) == like_of(t, pat_of(ps)));
}

/// The ON condition of customer row `i` and orders row `j`.
pub proof fn lemma_on(sv: StoresView, db: Database, ps: Seq<Literal>, i: int, j: int)
    requires bound_db(sv, db), param_domain(ps), 0 <= i < n_c(sv), 0 <= j < n_o(sv),
    ensures ({
        let env = Seq::<Val>::empty() + db.tables[2][i] + db.tables[1][j];
        let pat = pat_of(ps);
        &&& like_j(sv, pat, j) is Ok ==> eval_pred(db, env, q_on(ps)) == Ok::<Truth, SqlError>(on_truth(sv, pat, i, j))
        &&& like_j(sv, pat, j) is Err ==> eval_pred(db, env, q_on(ps)) == Err::<Truth, SqlError>(like_j(sv, pat, j)->Err_0)
    }),
{
    let pat = pat_of(ps);
    lemma_customer_row(sv, db, i);
    lemma_orders_row(sv, db, j);
    let (c, o) = (db.tables[2][i], db.tables[1][j]);
    let env = Seq::<Val>::empty() + c + o;
    assert(env =~= c + o);
    assert(env.len() == 17);
    assert(env[0] == c[0] && env[9] == o[1] && env[16] == o[8]);
    // c_custkey = o_custkey
    lemma_expr_col(db, env, 0);
    lemma_expr_col(db, env, 9);
    lemma_compare_int(cck(sv)[i] as int, ock(sv)[j] as int);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(0), Expr::Col(9), Val::Int(cck(sv)[i] as int), Val::Int(ock(sv)[j] as int),
        cck(sv)[i] as int, ock(sv)[j] as int);
    // NOT o_comment LIKE $1
    lemma_like_call(db, env, ps, cmt(sv, j));
    lemma_like_kinds(cmt(sv, j), pat);
    if like_j(sv, pat, j) is Ok {
        let b = choose|b: bool| like_of(cmt(sv, j), pat) == Ok::<Val, SqlError>(Val::Bool(b));
        assert(eval_pred(db, env, Pred::OfBool(q_like(ps))) == Ok::<Truth, SqlError>(truth_of(b)));
        lemma_pred_not(db, env, Pred::OfBool(q_like(ps)), b);
        lemma_pred_and(db, env, q_eq(), Pred::Not(Box::new(Pred::OfBool(q_like(ps)))), cck(sv)[i] == ock(sv)[j], !b);
        assert(counted(sv, pat, j) == !b);
    }
}

// ------------------------------------------------------------------------------------------------ the LEFT JOIN

/// The tables of a bound database.
proof fn lemma_tables(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        eval_query(db, Seq::empty(), Query::Table(2)) == Ok::<Relation, SqlError>(db.tables[2]),
        eval_query(db, Seq::empty(), Query::Table(1)) == Ok::<Relation, SqlError>(db.tables[1]),
        query_arity(db.schema, Query::Table(1)) == 9,
        db.tables[2].len() == n_c(sv), db.tables[1].len() == n_o(sv),
{
    lemma_table_lens(sv, db);
    crate::stores::flat_orders::declaration::lemma_declared_schema();
}

/// The LEFT JOIN when no `LIKE` raises (or there is no customer).
pub proof fn lemma_join(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), n_c(sv) == 0 || likes_ok(sv, pat_of(ps)),
    ensures
        eval_query(db, Seq::empty(), q_join(ps))
            == Ok::<Relation, SqlError>(left_join_rows(db.tables[2], db.tables[1], truths(sv, pat_of(ps)), 9)),
{
    let pat = pat_of(ps);
    lemma_tables(sv, db);
    let (l, r) = (db.tables[2], db.tables[1]);
    let ctx = Seq::<Val>::empty();
    let on = q_on(ps);
    let tt = truths(sv, pat);
    let rs = left_join_results(db, ctx, l, r, on);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Seq<Truth>, SqlError>(tt[i]) by {
        let inner = Seq::new(r.len(), |j: int| eval_pred(db, ctx + l[i] + r[j], on));
        assert forall|j: int| 0 <= j < inner.len() implies #[trigger] inner[j] == Ok::<Truth, SqlError>(tt[i][j]) by {
            lemma_on(sv, db, ps, i, j);
            assert(like_j(sv, pat, j) is Ok);
        }
        lemma_collect_all(inner, tt[i]);
    }
    lemma_collect_all(rs, tt);
    lemma_eval_left_join(db, ctx, Box::new(Query::Table(2)), Box::new(Query::Table(1)), on);
}

/// Customer row `i` against every orders row: the truths, or 22025 when some `LIKE` raises.
proof fn lemma_join_row(sv: StoresView, db: Database, ps: Seq<Literal>, i: int)
    requires bound_db(sv, db), param_domain(ps), 0 <= i < n_c(sv),
    ensures ({
        let inner = Seq::new(db.tables[1].len(), |j: int| eval_pred(db, Seq::<Val>::empty() + db.tables[2][i] + db.tables[1][j], q_on(ps)));
        &&& collect(inner) is Ok || collect(inner) == Err::<Seq<Truth>, SqlError>(SqlError::InvalidEscapeSequence)
        &&& forall|j0: int| 0 <= j0 < n_o(sv) && #[trigger] like_j(sv, pat_of(ps), j0) is Err
                ==> collect(inner) == Err::<Seq<Truth>, SqlError>(SqlError::InvalidEscapeSequence)
    }),
{
    let pat = pat_of(ps);
    let e = SqlError::InvalidEscapeSequence;
    lemma_tables(sv, db);
    let (l, r) = (db.tables[2], db.tables[1]);
    let ctx = Seq::<Val>::empty();
    let inner = Seq::new(r.len(), |j: int| eval_pred(db, ctx + l[i] + r[j], q_on(ps)));
    assert forall|j: int| 0 <= j < inner.len() implies #[trigger] inner[j] is Ok || inner[j] == Err::<Truth, SqlError>(e) by {
        lemma_on(sv, db, ps, i, j);
        lemma_like_kinds(cmt(sv, j), pat);
    }
    if exists|j: int| 0 <= j < inner.len() && #[trigger] inner[j] is Err {
        let j = choose|j: int| 0 <= j < inner.len() && #[trigger] inner[j] is Err;
        lemma_collect_uniform_err(inner, e, j);
    } else {
        assert forall|j: int| 0 <= j < inner.len() implies #[trigger] inner[j] is Ok by {}
        lemma_collect_ok(inner);
        assert forall|j0: int| 0 <= j0 < n_o(sv) && #[trigger] like_j(sv, pat, j0) is Err implies false by {
            lemma_on(sv, db, ps, i, j0);
            assert(inner[j0] is Ok);
        }
    }
}

/// When there is a customer and some `LIKE` raises, the LEFT JOIN is 22025.
pub proof fn lemma_join_err(sv: StoresView, db: Database, ps: Seq<Literal>, j0: int)
    requires bound_db(sv, db), param_domain(ps), n_c(sv) > 0, 0 <= j0 < n_o(sv), like_j(sv, pat_of(ps), j0) is Err,
    ensures eval_query(db, Seq::empty(), q_join(ps)) == Err::<Relation, SqlError>(SqlError::InvalidEscapeSequence),
{
    let e = SqlError::InvalidEscapeSequence;
    lemma_tables(sv, db);
    let (l, r) = (db.tables[2], db.tables[1]);
    let ctx = Seq::<Val>::empty();
    let on = q_on(ps);
    let rs = left_join_results(db, ctx, l, r, on);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] is Ok || rs[i] == Err::<Seq<Truth>, SqlError>(e) by {
        lemma_join_row(sv, db, ps, i);
    }
    lemma_join_row(sv, db, ps, 0);
    assert(rs[0] == Err::<Seq<Truth>, SqlError>(e));
    lemma_collect_uniform_err(rs, e, 0);
    lemma_eval_left_join(db, ctx, Box::new(Query::Table(2)), Box::new(Query::Table(1)), on);
}

} // verus!
