//! The SQL meaning of Q13, step by step over the statement's AST (`query_spec_at`):
//! - `outer_q` = GROUP BY c_count, COUNT(*) over `inner_q`;
//! - `inner_q` = GROUP BY c_custkey, COUNT(o_orderkey) over `lj_q`;
//! - `lj_q` = customer LEFT JOIN orders ON c_custkey = o_custkey AND NOT (o_comment LIKE $1 ESCAPE '\').
//!
//! Over the customer rows `C` (`ctab`) and orders rows `O` (`otab`) of a database with typed rows and distinct
//! customer keys (`db_facts`, from `db_wf` and the declared primary key): the ON condition of a customer row `c`
//! and an orders row `o` raises exactly the matcher's error, otherwise it is `c[0] == o[1] && !olike(o)`
//! (`lemma_on_pred`); the LEFT JOIN raises 22025 when there is a customer and some comment makes the matcher raise
//! (`lemma_lj_err`), otherwise it is `left_join_rows` of those truths (`lemma_lj_ok`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::typing::*;
use crate::spec::types::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::spec::fns::apply_fn;
use crate::spec::numeric::sign;
use crate::spec::constraints::*;
use crate::link::expr::*;
use crate::link::capacity::lemma_collect_uniform_err;
use crate::bridge::collect::*;
use crate::bridge::collect::lemma_collect_pointwise;
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::bridge::equality::lemma_row_not_distinct_refl;
use crate::query::{query_spec_at, param_typed};
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};
use super::like::{lemma_mt_err};

verus! {

// ------------------------------------------------------------------------------------------------ vocabulary

/// The orders rows.
pub open spec fn otab(db: Database) -> Seq<Row> {
    db.tables[1]
}

/// The customer rows.
pub open spec fn ctab(db: Database) -> Seq<Row> {
    db.tables[2]
}

/// The pattern `$1`.
pub open spec fn pat_of(ps: Seq<Literal>) -> Seq<u8> {
    match ps[0] {
        Literal::Text(b) => b,
        _ => Seq::empty(),
    }
}

/// The tokens of `$1` with escape `\`.
pub open spec fn toks_of(ps: Seq<Literal>) -> Seq<LikeTok> {
    like_tokens(chars(pat_of(ps)), Some(seq![92u8]), 0)
}

/// o_comment of an orders row.
pub open spec fn otext(o: Row) -> Seq<u8> {
    match o[8] {
        Val::Text(b) => b,
        _ => Seq::empty(),
    }
}

/// The matcher's outcome on an orders row.
pub open spec fn ores(o: Row, ps: Seq<Literal>) -> Result<LikeRes, SqlError> {
    like_mt(chars(otext(o)), toks_of(ps), 0, 0)
}

/// `o_comment LIKE $1` holds on an orders row.
pub open spec fn olike(o: Row, ps: Seq<Literal>) -> bool {
    ores(o, ps) == Ok::<LikeRes, SqlError>(LikeRes::Match)
}

/// Some orders row makes the matcher raise.
pub open spec fn some_err(db: Database, ps: Seq<Literal>) -> bool {
    exists|j: int| 0 <= j < otab(db).len() && #[trigger] ores(otab(db)[j], ps) is Err
}

/// Typed rows and distinct customer keys.
pub open spec fn db_facts(db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& db.schema == schema_spec()
    &&& forall|j: int| 0 <= j < otab(db).len() ==> {
            &&& (#[trigger] otab(db)[j]).len() == 9
            &&& otab(db)[j][0] is Int
            &&& otab(db)[j][1] is Int
            &&& i64::MIN <= ival(otab(db)[j][1]) <= i64::MAX
            &&& otab(db)[j][8] is Text
        }
    &&& forall|i: int| 0 <= i < ctab(db).len() ==> {
            &&& (#[trigger] ctab(db)[i]).len() == 8
            &&& ctab(db)[i][0] is Int
            &&& i64::MIN <= ival(ctab(db)[i][0]) <= i64::MAX
        }
    &&& forall|i: int, i2: int| 0 <= i < ctab(db).len() && 0 <= i2 < ctab(db).len() && i != i2 ==>
            #[trigger] ctab(db)[i][0] != #[trigger] ctab(db)[i2][0]
}

/// The schema columns the statement reads.
proof fn lemma_columns()
    ensures
        schema_spec().len() == 8,
        schema_spec()[1].columns.len() == 9,
        schema_spec()[2].columns.len() == 8,
        schema_spec()[1].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[1].columns[1] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[1].columns[8] == (Column { ty: SqlType::Text, nullable: false }),
        schema_spec()[2].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
{
    assert(schema_spec().len() == 8) by (compute);
    assert(schema_spec()[1].columns.len() == 9) by (compute);
    assert(schema_spec()[2].columns.len() == 8) by (compute);
    assert(schema_spec()[1].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[1].columns[1] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[1].columns[8] == (Column { ty: SqlType::Text, nullable: false })) by (compute);
    assert(schema_spec()[2].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
}

/// The declared primary key of customer.
proof fn lemma_customer_pk()
    ensures
        declared_schema().len() == 8,
        declared_schema()[2].constraints.len() >= 1,
        declared_schema()[2].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }),
{
    assert(declared_schema().len() == 8) by (compute);
    assert(declared_schema()[2].constraints.len() >= 1) by (compute);
    assert(declared_schema()[2].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true })) by (compute);
}

/// `db_facts` of a database bound to the statement's schema.
pub proof fn lemma_db_facts(db: Database)
    requires
        db.schema == schema_spec(),
        db_wf(db),
        constraints_hold(declared_db(db)),
    ensures
        db_facts(db),
{
    lemma_columns();
    let s = schema_spec();
    assert forall|j: int| 0 <= j < otab(db).len() implies {
        &&& (#[trigger] otab(db)[j]).len() == 9
        &&& otab(db)[j][0] is Int
        &&& otab(db)[j][1] is Int
        &&& i64::MIN <= ival(otab(db)[j][1]) <= i64::MAX
        &&& otab(db)[j][8] is Text
    } by {
        assert(row_in_table(db.tables[1][j], db.schema[1]));
        assert(value_in_column(db.tables[1][j][0], s[1].columns[0]));
        assert(value_in_column(db.tables[1][j][1], s[1].columns[1]));
        assert(value_in_column(db.tables[1][j][8], s[1].columns[8]));
    }
    assert forall|i: int| 0 <= i < ctab(db).len() implies {
        &&& (#[trigger] ctab(db)[i]).len() == 8
        &&& ctab(db)[i][0] is Int
        &&& i64::MIN <= ival(ctab(db)[i][0]) <= i64::MAX
    } by {
        assert(row_in_table(db.tables[2][i], db.schema[2]));
        assert(value_in_column(db.tables[2][i][0], s[2].columns[0]));
    }
    lemma_customer_pk();
    let ddb = declared_db(db);
    assert forall|i: int, i2: int| 0 <= i < ctab(db).len() && 0 <= i2 < ctab(db).len() && i != i2 implies
        #[trigger] ctab(db)[i][0] != #[trigger] ctab(db)[i2][0] by {
        if ctab(db)[i][0] == ctab(db)[i2][0] {
            let cols = seq![0nat];
            assert(key_of(ddb.tables[2][i], cols) =~= seq![ctab(db)[i][0]]);
            assert(key_of(ddb.tables[2][i2], cols) =~= seq![ctab(db)[i2][0]]);
            lemma_row_not_distinct_refl(seq![ctab(db)[i][0]]);
            lemma_primary_key_identifies(ddb, 2, 0, cols, true, i, i2);
        }
    }
}

// ------------------------------------------------------------------------------------------------ the AST

/// The ON condition.
pub open spec fn on_pred(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) }),
        Box::new(Pred::Not(Box::new(Pred::OfBool(like_expr(ps))))),
    )
}

/// `o_comment LIKE $1 ESCAPE '\'`.
pub open spec fn like_expr(ps: Seq<Literal>) -> Expr {
    Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(16), Expr::Lit(ps[0]), Expr::Lit(Literal::Text(seq![92u8]))] }
}

/// customer LEFT JOIN orders ON ...
pub open spec fn lj_q(ps: Seq<Literal>) -> Query {
    Query::LeftJoin { left: Box::new(Query::Table(2)), right: Box::new(Query::Table(1)), on: on_pred(ps) }
}

/// GROUP BY c_custkey, COUNT(o_orderkey).
pub open spec fn inner_q(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: seq![Expr::Col(0)], aggs: seq![Agg::Count(Expr::Col(8))], input: Box::new(lj_q(ps)) }
}

/// GROUP BY c_count, COUNT(*).
pub open spec fn outer_q(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: seq![Expr::Col(1)], aggs: seq![Agg::CountStar], input: Box::new(inner_q(ps)) }
}

/// The ORDER BY keys: custdist DESC, c_count DESC.
pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 1, desc: true, nulls_first: true }, OrderKey { col: 0, desc: true, nulls_first: true }]
}

/// The statement is `outer_q` ordered by `order_keys`, without LIMIT or OFFSET.
pub proof fn lemma_statement(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == outer_q(ps),
        query_spec_at(ps).keys == order_keys(),
        query_spec_at(ps).limit is None,
        query_spec_at(ps).offset == 0,
{
    assert(query_spec_at(ps).body == outer_q(ps));
    assert(query_spec_at(ps).keys =~= order_keys());
}

// ------------------------------------------------------------------------------------------------ ON condition

/// The arguments of the LIKE call: o_comment, `$1` and the escape `\`.
proof fn lemma_like_args(db: Database, ps: Seq<Literal>, env: Row)
    requires
        param_typed(ps),
        env.len() > 16,
    ensures
        eval_exprs(db, env, seq![Expr::Col(16), Expr::Lit(ps[0]), Expr::Lit(Literal::Text(seq![92u8]))])
            == Ok::<Row, SqlError>(seq![env[16], Val::Text(pat_of(ps)), Val::Text(seq![92u8])]),
{
    let pat = pat_of(ps);
    assert(ps[0] == Literal::Text(pat));
    let args = seq![Expr::Col(16), Expr::Lit(ps[0]), Expr::Lit(Literal::Text(seq![92u8]))];
    let vs = seq![env[16], Val::Text(pat), Val::Text(seq![92u8])];
    lemma_expr_col(db, env, 16);
    lemma_expr_text(db, env, pat);
    lemma_expr_text(db, env, seq![92u8]);
    lemma_expr_results_index(db, env, args);
    lemma_collect_all(expr_results(db, env, args), vs);
}

/// The escape string `\` is the one character `\`.
pub proof fn lemma_chars_esc()
    ensures chars(seq![92u8]) == seq![seq![92u8]],
{
    let b = seq![92u8];
    assert(b.drop_last() =~= Seq::<u8>::empty());
    assert(chars(Seq::<u8>::empty()) == Seq::<Seq<u8>>::empty());
    assert(b.last() == 92u8);
    assert(!is_cont(92u8));
    assert(chars(b) == chars(b.drop_last()).push(seq![b.last()]));
    assert(Seq::<Seq<u8>>::empty().push(seq![92u8]) =~= seq![seq![92u8]]);
}

/// `LIKE` on a text subject, a text pattern and the escape `\`: the matcher's outcome as a Boolean.
proof fn lemma_like_value(t: Seq<u8>, ps: Seq<Literal>)
    ensures
        like_value(Val::Text(t), Val::Text(pat_of(ps)), Val::Text(seq![92u8])) == match like_mt(chars(t), toks_of(ps), 0, 0) {
            Err(e) => Err::<Val, SqlError>(e),
            Ok(r) => Ok::<Val, SqlError>(Val::Bool(r is Match)),
        },
{
    hide(like_mt);
    hide(chars);
    lemma_chars_esc();
    assert(escape_of(chars(seq![92u8])) == Some(seq![92u8]));
}

/// The scalar function dispatch of LIKE.
proof fn lemma_apply_like(vs: Seq<Val>)
    requires vs.len() == 3,
    ensures apply_fn(ScalarFn::Like, vs) == like_value(vs[0], vs[1], vs[2]),
{
    hide(like_value);
}

/// The value of the LIKE call in an environment whose position 16 is o_comment of `o`.
proof fn lemma_like_call(db: Database, ps: Seq<Literal>, env: Row, o: Row)
    requires
        param_typed(ps),
        env.len() > 16,
        env[16] == o[8],
        o[8] is Text,
    ensures
        eval_expr(db, env, like_expr(ps)) == match ores(o, ps) {
            Err(e) => Err::<Val, SqlError>(e),
            Ok(r) => Ok::<Val, SqlError>(Val::Bool(r is Match)),
        },
{
    hide(like_value);
    hide(apply_fn);
    hide(like_mt);
    let vs = seq![o[8], Val::Text(pat_of(ps)), Val::Text(seq![92u8])];
    lemma_like_args(db, ps, env);
    lemma_like_value(otext(o), ps);
    assert(vs[0] == Val::Text(otext(o)));
    lemma_apply_like(vs);
}

/// `OfBool` of a Boolean (or an error) expression.
proof fn lemma_ofbool(db: Database, env: Row, e: Expr, r: Result<Val, SqlError>)
    requires
        eval_expr(db, env, e) == r,
        r matches Ok(v) ==> v is Bool,
    ensures
        eval_pred(db, env, Pred::OfBool(e)) == match r {
            Err(err) => Err::<Truth, SqlError>(err),
            Ok(v) => Ok::<Truth, SqlError>(truth_of(v->Bool_0)),
        },
{
}

/// `NOT` of an error is the error.
proof fn lemma_not_err(db: Database, env: Row, a: Pred, e: SqlError)
    requires eval_pred(db, env, a) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, Pred::Not(Box::new(a))) == Err::<Truth, SqlError>(e),
{
}

/// `AND` with an erring right operand after a value is the error.
proof fn lemma_and_err(db: Database, env: Row, a: Pred, b: Pred, t: Truth, e: SqlError)
    requires
        eval_pred(db, env, a) == Ok::<Truth, SqlError>(t),
        eval_pred(db, env, b) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, Pred::And(Box::new(a), Box::new(b))) == Err::<Truth, SqlError>(e),
{
}

/// The ON condition of a customer row `c` and an orders row `o`.
pub proof fn lemma_on_pred(db: Database, ps: Seq<Literal>, c: Row, o: Row)
    requires
        param_typed(ps),
        c.len() == 8,
        c[0] is Int,
        o.len() == 9,
        o[1] is Int,
        o[8] is Text,
    ensures
        eval_pred(db, c + o, on_pred(ps)) == match ores(o, ps) {
            Err(e) => Err::<Truth, SqlError>(e),
            Ok(r) => Ok::<Truth, SqlError>(truth_of(c[0] == o[1] && !(r is Match))),
        },
{
    let env = c + o;
    assert(env[0] == c[0]);
    assert(env[9] == o[1]);
    assert(env[16] == o[8]);
    lemma_like_call(db, ps, env, o);
    lemma_expr_col(db, env, 0);
    lemma_expr_col(db, env, 9);
    let (x, y) = (ival(c[0]), ival(o[1]));
    lemma_compare_int(x, y);
    let cmp = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(0), Expr::Col(9), c[0], o[1], x, y);
    assert(int_cmp(CmpOp::Eq, x, y) == (c[0] == o[1]));
    let lk = Pred::OfBool(like_expr(ps));
    let lr = match ores(o, ps) {
        Err(e) => Err::<Val, SqlError>(e),
        Ok(r) => Ok::<Val, SqlError>(Val::Bool(r is Match)),
    };
    lemma_ofbool(db, env, like_expr(ps), lr);
    match ores(o, ps) {
        Err(e) => {
            lemma_not_err(db, env, lk, e);
            lemma_and_err(db, env, cmp, Pred::Not(Box::new(lk)), truth_of(c[0] == o[1]), e);
        },
        Ok(r) => {
            lemma_pred_not(db, env, lk, r is Match);
            lemma_pred_and(db, env, cmp, Pred::Not(Box::new(lk)), c[0] == o[1], !(r is Match));
        },
    }
}

// ------------------------------------------------------------------------------------------------ LEFT JOIN

/// The ON truths of customer row `i` against every orders row (no matcher error).
pub open spec fn lj_row_truths(db: Database, ps: Seq<Literal>, i: int) -> Seq<Truth> {
    Seq::new(otab(db).len(), |j: int| truth_of(ctab(db)[i][0] == otab(db)[j][1] && !olike(otab(db)[j], ps)))
}

/// The ON truths of every customer row.
pub open spec fn lj_truths(db: Database, ps: Seq<Literal>) -> Seq<Seq<Truth>> {
    Seq::new(ctab(db).len(), |i: int| lj_row_truths(db, ps, i))
}

/// The per-pair ON outcomes of customer row `i` (as the LEFT JOIN denotation evaluates them).
pub open spec fn lj_row_results(db: Database, ps: Seq<Literal>, i: int) -> Seq<Result<Truth, SqlError>> {
    Seq::new(otab(db).len(), |j: int| eval_pred(db, Seq::<Val>::empty() + ctab(db)[i] + otab(db)[j], on_pred(ps)))
}

/// One customer row's ON outcomes: each is the matcher's error or the two-valued truth.
proof fn lemma_row_results(db: Database, ps: Seq<Literal>, i: int)
    requires
        db_facts(db),
        param_typed(ps),
        0 <= i < ctab(db).len(),
    ensures
        forall|j: int| 0 <= j < otab(db).len() ==> #[trigger] lj_row_results(db, ps, i)[j] == match ores(otab(db)[j], ps) {
            Err(e) => Err::<Truth, SqlError>(e),
            Ok(r) => Ok::<Truth, SqlError>(truth_of(ctab(db)[i][0] == otab(db)[j][1] && !(r is Match))),
        },
{
    assert forall|j: int| 0 <= j < otab(db).len() implies #[trigger] lj_row_results(db, ps, i)[j] == match ores(otab(db)[j], ps) {
        Err(e) => Err::<Truth, SqlError>(e),
        Ok(r) => Ok::<Truth, SqlError>(truth_of(ctab(db)[i][0] == otab(db)[j][1] && !(r is Match))),
    } by {
        let (c, o) = (ctab(db)[i], otab(db)[j]);
        assert(Seq::<Val>::empty() + c + o =~= c + o);
        lemma_on_pred(db, ps, c, o);
    }
}

/// The schema arity of orders.
proof fn lemma_orders_arity(db: Database)
    requires db_facts(db),
    ensures query_arity(db.schema, Query::Table(1)) == 9,
{
    lemma_columns();
}

/// One step of the LEFT JOIN denotation: its input tables and the nested collection of ON outcomes.
proof fn lemma_lj_unfold(db: Database, ps: Seq<Literal>)
    requires db_facts(db),
    ensures
        eval_query(db, Seq::empty(), lj_q(ps)) == match collect(Seq::new(ctab(db).len(), |i: int| collect(lj_row_results(db, ps, i)))) {
            Err(err) => Err::<Relation, SqlError>(err),
            Ok(truths) => Ok::<Relation, SqlError>(left_join_rows(ctab(db), otab(db), truths, query_arity(db.schema, Query::Table(1)))),
        },
{
    let (c, o) = (ctab(db), otab(db));
    assert(eval_query(db, Seq::empty(), Query::Table(2)) == Ok::<Relation, SqlError>(c));
    assert(eval_query(db, Seq::empty(), Query::Table(1)) == Ok::<Relation, SqlError>(o));
    let ctx = Seq::<Val>::empty();
    let nested = Seq::new(c.len(), |i: int| collect(Seq::new(o.len(), |j: int| eval_pred(db, ctx + c[i] + o[j], on_pred(ps)))));
    let mine = Seq::new(c.len(), |i: int| collect(lj_row_results(db, ps, i)));
    lemma_collect_pointwise::<Truth>();
    lemma_collect_pointwise::<Seq<Truth>>();
    assert forall|i: int| 0 <= i < c.len() implies #[trigger] nested[i] == mine[i] by {
        assert(Seq::new(o.len(), |j: int| eval_pred(db, ctx + c[i] + o[j], on_pred(ps))) =~= lj_row_results(db, ps, i));
    }
    assert(nested =~= mine);
}

/// Without matcher errors (or without customers) the LEFT JOIN is `left_join_rows` of the ON truths.
pub proof fn lemma_lj_ok(db: Database, ps: Seq<Literal>)
    requires
        db_facts(db),
        param_typed(ps),
        !(ctab(db).len() > 0 && some_err(db, ps)),
    ensures
        eval_query(db, Seq::empty(), lj_q(ps)) == Ok::<Relation, SqlError>(left_join_rows(ctab(db), otab(db), lj_truths(db, ps), 9)),
{
    lemma_orders_arity(db);
    let (c, o) = (ctab(db), otab(db));
    let outer = Seq::new(c.len(), |i: int| collect(lj_row_results(db, ps, i)));
    assert forall|i: int| 0 <= i < c.len() implies #[trigger] outer[i] == Ok::<Seq<Truth>, SqlError>(lj_truths(db, ps)[i]) by {
        lemma_row_results(db, ps, i);
        let rs = lj_row_results(db, ps, i);
        let ts = lj_truths(db, ps)[i];
        assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Truth, SqlError>(ts[j]) by {
            if ores(o[j], ps) is Err {
                assert(some_err(db, ps));
            }
        }
        lemma_collect_all(rs, ts);
    }
    lemma_collect_all(outer, lj_truths(db, ps));
    lemma_lj_unfold(db, ps);
}

/// With a customer and a matcher error, the LEFT JOIN raises 22025.
pub proof fn lemma_lj_err(db: Database, ps: Seq<Literal>)
    requires
        db_facts(db),
        param_typed(ps),
        ctab(db).len() > 0,
        some_err(db, ps),
    ensures
        eval_query(db, Seq::empty(), lj_q(ps)) == Err::<Relation, SqlError>(SqlError::InvalidEscapeSequence),
{
    let (c, o) = (ctab(db), otab(db));
    let j0 = choose|j: int| 0 <= j < o.len() && #[trigger] ores(o[j], ps) is Err;
    lemma_row_results(db, ps, 0);
    let rs = lj_row_results(db, ps, 0);
    assert forall|k: int| 0 <= k < rs.len() implies #[trigger] rs[k] is Ok || rs[k] == Err::<Truth, SqlError>(SqlError::InvalidEscapeSequence) by {
        lemma_mt_err(chars(otext(o[k])), toks_of(ps), 0, 0);
    }
    lemma_mt_err(chars(otext(o[j0])), toks_of(ps), 0, 0);
    lemma_collect_uniform_err(rs, SqlError::InvalidEscapeSequence, j0);
    let outer = Seq::new(c.len(), |i: int| collect(lj_row_results(db, ps, i)));
    lemma_collect_first_err(outer, 0);
    lemma_lj_unfold(db, ps);
}

} // verus!
