//! The statement's AST in named pieces (`q_body`, `outer_pred`, `sub_q`, ...; `lemma_query_shape` identifies them
//! with the fixed `query_spec_at`) and the evaluation of its WHERE condition on one row.
//!
//! Outer rows (`xrow_ok`) are `partsupp ++ part` (14 values); the NOT IN subquery's rows are supplier rows
//! evaluated after the outer row (environment `x ++ s`, so `s_comment` is column 20). `lemma_sub_eval`: the subquery
//! is the `s_suppkey` of every supplier row whose comment matches `%Customer%Complaints%` (that LIKE never fails);
//! `lemma_outer_pred`: the WHERE is the row's `p_type LIKE $2` error when there is one, else a two-valued truth that is
//! `True` exactly when `pre_q` holds and `ps_suppkey` is not a subquery key.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::query::{query_spec_at, param_domain};
use crate::link::expr::{lemma_pred_cmp, lemma_pred_and, lemma_pred_or, lemma_pred_not, lemma_pred_text_cmp, ival};
use crate::link::join::{keep, lemma_keep_true_keep, lemma_keep_members};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};

verus! {

// ------------------------------------------------------------------------------------------------ AST pieces

/// `Col(a) = Col(b)`.
pub open spec fn ceq(a: nat, b: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(a), b: Expr::Col(b) }
}

/// `Col(c) = literal`.
pub open spec fn clit(c: nat, l: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(c), b: Expr::Lit(l) }
}

pub open spec fn cand(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

pub open spec fn cor(a: Pred, b: Pred) -> Pred {
    Pred::Or(Box::new(a), Box::new(b))
}

/// `p_brand <> $1`.
pub open spec fn brand_pred(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Ne, a: Expr::Col(8), b: Expr::Lit(ps[0]) }
}

/// The escape `\` of every LIKE of the statement.
pub open spec fn esc() -> Seq<u8> {
    seq![92u8]
}

/// `p_type LIKE $2`.
pub open spec fn like_expr(ps: Seq<Literal>) -> Expr {
    Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(9), Expr::Lit(ps[1]), Expr::Lit(Literal::Text(esc()))] }
}

/// `p_type NOT LIKE $2`.
pub open spec fn type_pred(ps: Seq<Literal>) -> Pred {
    Pred::Not(Box::new(Pred::OfBool(like_expr(ps))))
}

/// `p_size IN ($3, ..., $10)` as the frontend's OR chain.
pub open spec fn size_pred(ps: Seq<Literal>) -> Pred {
    cor(cor(cor(cor(cor(cor(cor(clit(10, ps[2]), clit(10, ps[3])), clit(10, ps[4])), clit(10, ps[5])), clit(10, ps[6])),
        clit(10, ps[7])), clit(10, ps[8])), clit(10, ps[9]))
}

/// The subquery's pattern `%Customer%Complaints%`.
pub open spec fn cc_bytes() -> Seq<u8> {
    seq![37u8, 67u8, 117u8, 115u8, 116u8, 111u8, 109u8, 101u8, 114u8, 37u8, 67u8, 111u8, 109u8, 112u8, 108u8, 97u8,
        105u8, 110u8, 116u8, 115u8, 37u8]
}

/// `s_comment LIKE '%Customer%Complaints%'` (environment: outer row ++ supplier row).
pub open spec fn sub_like() -> Expr {
    Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(20), Expr::Lit(Literal::Text(cc_bytes())), Expr::Lit(Literal::Text(esc()))] }
}

/// `SELECT s_suppkey FROM supplier WHERE s_comment LIKE '%Customer%Complaints%'`.
pub open spec fn sub_q() -> Query {
    Query::Project {
        exprs: seq![Expr::Col(14)],
        input: Box::new(Query::Filter { pred: Pred::OfBool(sub_like()), input: Box::new(Query::Table(5)) }),
    }
}

/// `ps_suppkey NOT IN (subquery)`.
pub open spec fn notin_pred() -> Pred {
    Pred::Not(Box::new(Pred::AnyCmp { op: CmpOp::Eq, e: Expr::Col(1), q: Box::new(sub_q()) }))
}

/// The WHERE without the NOT IN.
pub open spec fn pre_pred(ps: Seq<Literal>) -> Pred {
    cand(cand(cand(ceq(5, 0), brand_pred(ps)), type_pred(ps)), size_pred(ps))
}

/// The WHERE.
pub open spec fn outer_pred(ps: Seq<Literal>) -> Pred {
    cand(pre_pred(ps), notin_pred())
}

/// FROM partsupp, part.
pub open spec fn q_from() -> Query {
    Query::Product { left: Box::new(Query::Table(4)), right: Box::new(Query::Table(3)) }
}

pub open spec fn q_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: outer_pred(ps), input: Box::new(q_from()) }
}

/// GROUP BY p_brand, p_type, p_size.
pub open spec fn key_exprs() -> Seq<Expr> {
    seq![Expr::Col(8), Expr::Col(9), Expr::Col(10)]
}

/// `COUNT(DISTINCT ps_suppkey)`.
pub open spec fn q_aggs() -> Seq<Agg> {
    seq![Agg::DistinctAgg(Box::new(Agg::Count(Expr::Col(1))))]
}

pub open spec fn q_body(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: key_exprs(), aggs: q_aggs(), input: Box::new(q_filter(ps)) }
}

/// ORDER BY supplier_cnt DESC, p_brand, p_type, p_size.
pub open spec fn q_keys() -> Seq<OrderKey> {
    seq![
        OrderKey { col: 3, desc: true, nulls_first: true },
        OrderKey { col: 0, desc: false, nulls_first: false },
        OrderKey { col: 1, desc: false, nulls_first: false },
        OrderKey { col: 2, desc: false, nulls_first: false },
    ]
}

/// The fixed statement is these pieces.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: q_body(ps), keys: q_keys(), limit: None, offset: 0nat }),
{
}

// ------------------------------------------------------------------------------------------------ parameters

/// The bound parameters: `$1` (brand), `$2` (the type pattern) and `$3 .. $10` (the sizes).
pub struct Prm {
    pub brand: Seq<u8>,
    pub pat: Seq<u8>,
    pub sizes: Seq<int>,
}

pub open spec fn prm_of(ps: Seq<Literal>) -> Prm {
    Prm {
        brand: match ps[0] { Literal::Text(b) => b, _ => Seq::empty() },
        pat: match ps[1] { Literal::Text(b) => b, _ => Seq::empty() },
        sizes: Seq::new(8, |z: int| match ps[z + 2] { Literal::Int { v, .. } => v, _ => 0 }),
    }
}

/// Slot `k` holds an int4 literal in range.
pub open spec fn int_slot(ps: Seq<Literal>, k: int) -> bool {
    ps[k] matches Literal::Int { v, kind } && kind == IntKind::Int4 && int_in_range(kind, v)
}

/// The parameters' values: `$1` and `$2` texts, `$3 .. $10` int4 literals.
pub open spec fn params_ok(ps: Seq<Literal>) -> bool {
    &&& ps.len() == 10
    &&& ps[0] is Text
    &&& ps[1] is Text
    &&& forall|k: int| 2 <= k < 10 ==> #[trigger] int_slot(ps, k)
}

pub proof fn lemma_params_ok(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures params_ok(ps),
{
    assert(int_slot(ps, 2));
    assert(int_slot(ps, 3));
    assert(int_slot(ps, 4));
    assert(int_slot(ps, 5));
    assert(int_slot(ps, 6));
    assert(int_slot(ps, 7));
    assert(int_slot(ps, 8));
    assert(int_slot(ps, 9));
}

// ------------------------------------------------------------------------------------------------ comparisons

/// Equality of two integer columns.
pub proof fn lemma_eq_int(db: Database, env: Row, a: nat, b: nat)
    requires a < env.len(), b < env.len(), env[a as int] is Int, env[b as int] is Int,
    ensures eval_pred(db, env, ceq(a, b)) == Ok::<Truth, SqlError>(truth_of(env[a as int] == env[b as int])),
{
    let (x, y) = (ival(env[a as int]), ival(env[b as int]));
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(a), Expr::Col(b), env[a as int], env[b as int], x, y);
}

/// Equality of an integer column with an int4 literal.
pub proof fn lemma_eq_int_lit(db: Database, env: Row, c: nat, l: Literal)
    requires c < env.len(), env[c as int] is Int, l matches Literal::Int { v, kind } && int_in_range(kind, v),
    ensures eval_pred(db, env, clit(c, l)) == Ok::<Truth, SqlError>(truth_of(env[c as int] == Val::Int(l->v))),
{
    let (x, y) = (ival(env[c as int]), l->v);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(c), Expr::Lit(l), env[c as int], Val::Int(y), x, y);
}

/// `p_brand <> $1` on a text brand.
pub proof fn lemma_brand_pred(db: Database, ps: Seq<Literal>, x: Row)
    requires params_ok(ps), x.len() > 8, x[8] is Text,
    ensures eval_pred(db, x, brand_pred(ps)) == Ok::<Truth, SqlError>(truth_of(x[8] != Val::Text(prm_of(ps).brand))),
{
    let a = x[8]->Text_0;
    let b = ps[0]->Text_0;
    lemma_pred_text_cmp(db, x, CmpOp::Ne, Expr::Col(8), Expr::Lit(ps[0]), a, b);
}

/// The values of the IN list: `v` is one of the eight sizes.
pub open spec fn in_sizes(m: Prm, v: Val) -> bool {
    v is Int && m.sizes.contains(v->Int_0)
}

/// `p_size IN ($3, ..., $10)` on an integer size.
pub proof fn lemma_size_pred(db: Database, ps: Seq<Literal>, x: Row)
    requires params_ok(ps), x.len() > 10, x[10] is Int,
    ensures eval_pred(db, x, size_pred(ps)) == Ok::<Truth, SqlError>(truth_of(in_sizes(prm_of(ps), x[10]))),
{
    let m = prm_of(ps);
    let v = x[10];
    assert forall|k: int| 2 <= k < 10 implies eval_pred(db, x, #[trigger] clit(10, ps[k]))
        == Ok::<Truth, SqlError>(truth_of(v == Val::Int(m.sizes[k - 2]))) by {
        assert(int_slot(ps, k));
        lemma_eq_int_lit(db, x, 10, ps[k]);
    }
    let e = |k: int| v == Val::Int(m.sizes[k - 2]);
    let p2 = cor(clit(10, ps[2]), clit(10, ps[3]));
    let p3 = cor(p2, clit(10, ps[4]));
    let p4 = cor(p3, clit(10, ps[5]));
    let p5 = cor(p4, clit(10, ps[6]));
    let p6 = cor(p5, clit(10, ps[7]));
    let p7 = cor(p6, clit(10, ps[8]));
    lemma_pred_or(db, x, clit(10, ps[2]), clit(10, ps[3]), e(2), e(3));
    lemma_pred_or(db, x, p2, clit(10, ps[4]), e(2) || e(3), e(4));
    lemma_pred_or(db, x, p3, clit(10, ps[5]), e(2) || e(3) || e(4), e(5));
    lemma_pred_or(db, x, p4, clit(10, ps[6]), e(2) || e(3) || e(4) || e(5), e(6));
    lemma_pred_or(db, x, p5, clit(10, ps[7]), e(2) || e(3) || e(4) || e(5) || e(6), e(7));
    lemma_pred_or(db, x, p6, clit(10, ps[8]), e(2) || e(3) || e(4) || e(5) || e(6) || e(7), e(8));
    lemma_pred_or(db, x, p7, clit(10, ps[9]), e(2) || e(3) || e(4) || e(5) || e(6) || e(7) || e(8), e(9));
    let any = e(2) || e(3) || e(4) || e(5) || e(6) || e(7) || e(8) || e(9);
    assert(any == in_sizes(m, v)) by {
        if in_sizes(m, v) {
            let z = choose|z: int| 0 <= z < m.sizes.len() && m.sizes[z] == v->Int_0;
            assert(e(z + 2));
        }
        if any {
            if e(2) { assert(m.sizes[0] == v->Int_0); }
            if e(3) { assert(m.sizes[1] == v->Int_0); }
            if e(4) { assert(m.sizes[2] == v->Int_0); }
            if e(5) { assert(m.sizes[3] == v->Int_0); }
            if e(6) { assert(m.sizes[4] == v->Int_0); }
            if e(7) { assert(m.sizes[5] == v->Int_0); }
            if e(8) { assert(m.sizes[6] == v->Int_0); }
            if e(9) { assert(m.sizes[7] == v->Int_0); }
        }
    }
}

// ------------------------------------------------------------------------------------------------ LIKE

/// `v LIKE pat` with the statement's escape `\`.
pub open spec fn like_res(v: Val, pat: Seq<u8>) -> Result<Val, SqlError> {
    like_value(v, Val::Text(pat), Val::Text(esc()))
}

pub open spec fn like_true(v: Val, pat: Seq<u8>) -> bool {
    like_res(v, pat) == Ok::<Val, SqlError>(Val::Bool(true))
}

/// The escape `\` is one character.
pub proof fn lemma_chars_backslash()
    ensures chars(esc()) == seq![esc()],
{
    reveal_with_fuel(chars, 2);
    assert(esc().drop_last() =~= Seq::<u8>::empty());
    assert(chars(esc()) =~= seq![esc()]);
}

/// `s LIKE pat` on a text value is a boolean or the matcher's error.
pub proof fn lemma_like_shape(s: Seq<u8>, pat: Seq<u8>)
    ensures
        like_res(Val::Text(s), pat) is Err || like_res(Val::Text(s), pat) == Ok::<Val, SqlError>(Val::Bool(true))
            || like_res(Val::Text(s), pat) == Ok::<Val, SqlError>(Val::Bool(false)),
        like_res(Val::Text(s), pat) == match like_mt(chars(s), like_tokens(chars(pat), Some(esc()), 0), 0, 0) {
            Ok(r) => Ok::<Val, SqlError>(Val::Bool(r is Match)),
            Err(e) => Err(e),
        },
{
    lemma_chars_backslash();
    assert(escape_of(chars(esc())) == Some(esc()));
}

/// A LIKE call `Col(c) LIKE literal ESCAPE '\'` on a row is `like_res` of the column.
pub proof fn lemma_like_call(db: Database, x: Row, c: nat, pat: Seq<u8>)
    requires c < x.len(),
    ensures
        eval_expr(db, x, Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(c), Expr::Lit(Literal::Text(pat)),
            Expr::Lit(Literal::Text(esc()))] }) == like_res(x[c as int], pat),
{
    hide(like_value);
    let args = seq![Expr::Col(c), Expr::Lit(Literal::Text(pat)), Expr::Lit(Literal::Text(esc()))];
    let vs = seq![x[c as int], Val::Text(pat), Val::Text(esc())];
    let rs = expr_results(db, x, args);
    lemma_expr_results_index(db, x, args);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        assert(rs[i] == eval_expr(db, x, args[i]));
    }
    lemma_collect_all(rs, vs);
    assert(eval_exprs(db, x, args) == Ok::<Row, SqlError>(vs));
    let call = Expr::Call { f: ScalarFn::Like, args };
    assert(eval_expr(db, x, call) == crate::spec::fns::apply_fn(ScalarFn::Like, vs));
    assert(crate::spec::fns::apply_fn(ScalarFn::Like, vs) == like_value(vs[0], vs[1], vs[2]));
}

/// `p_type NOT LIKE $2`: the LIKE error, or the negated two-valued `like_true`.
pub proof fn lemma_type_pred(db: Database, ps: Seq<Literal>, x: Row)
    requires params_ok(ps), x.len() > 9, x[9] is Text,
    ensures
        like_res(x[9], prm_of(ps).pat) matches Err(e) ==> eval_pred(db, x, type_pred(ps)) == Err::<Truth, SqlError>(e),
        like_res(x[9], prm_of(ps).pat) is Ok ==> eval_pred(db, x, type_pred(ps))
            == Ok::<Truth, SqlError>(truth_of(!like_true(x[9], prm_of(ps).pat))),
{
    hide(like_value);
    let m = prm_of(ps);
    assert(ps[1] == Literal::Text(m.pat));
    lemma_like_call(db, x, 9, m.pat);
    lemma_like_shape(x[9]->Text_0, m.pat);
    let r = like_res(x[9], m.pat);
    let lp = Pred::OfBool(like_expr(ps));
    assert(eval_expr(db, x, like_expr(ps)) == r);
    match r {
        Err(e) => {
            assert(eval_pred(db, x, lp) == Err::<Truth, SqlError>(e));
        },
        Ok(v) => {
            assert(eval_pred(db, x, lp) == truth_of_val(v));
            assert(eval_pred(db, x, lp) == Ok::<Truth, SqlError>(truth_of(like_true(x[9], m.pat))));
            lemma_pred_not(db, x, lp, like_true(x[9], m.pat));
        },
    }
}

// ------------------------------------------------------------------------------------------------ the subquery

/// The subquery's pattern is ASCII: every character is one byte (no continuation byte).
pub open spec fn ascii(b: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < b.len() ==> (#[trigger] b[i]) < 0x80u8
}

/// The characters of ASCII bytes are the bytes one by one.
pub proof fn lemma_chars_ascii(b: Seq<u8>)
    requires ascii(b),
    ensures chars(b) == b.map_values(|x: u8| seq![x]),
    decreases b.len(),
{
    if b.len() > 0 {
        let d = b.drop_last();
        assert(ascii(d)) by {
            assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]) < 0x80u8 by { assert(d[i] == b[i]); }
        }
        lemma_chars_ascii(d);
        assert(!is_cont(b.last()));
        assert(b.map_values(|x: u8| seq![x]) =~= d.map_values(|x: u8| seq![x]).push(seq![b.last()]));
    }
}

/// Tokens of a pattern without the escape character have no dangling escape.
pub proof fn lemma_tokens_no_dangling(pc: Seq<Seq<u8>>, e: Seq<u8>, k: int)
    requires forall|i: int| 0 <= i < pc.len() ==> #[trigger] pc[i] != e,
    ensures crate::bridge::fns::like::no_dangling(like_tokens(pc, Some(e), k)),
    decreases pc.len() - k,
{
    let ts = like_tokens(pc, Some(e), k);
    if 0 <= k < pc.len() {
        lemma_tokens_no_dangling(pc, e, k + 1);
        let rest = like_tokens(pc, Some(e), k + 1);
        assert forall|q: int| 0 <= q < ts.len() implies !(#[trigger] ts[q] is Dangling) by {
            if q > 0 {
                assert(ts[q] == rest[q - 1]);
            }
        }
    }
}

/// The subquery's LIKE on a text never fails: a boolean.
pub proof fn lemma_cc_like(s: Seq<u8>)
    ensures
        like_res(Val::Text(s), cc_bytes()) == Ok::<Val, SqlError>(Val::Bool(true))
            || like_res(Val::Text(s), cc_bytes()) == Ok::<Val, SqlError>(Val::Bool(false)),
{
    let cc = cc_bytes();
    assert(ascii(cc)) by {
        assert forall|i: int| 0 <= i < cc.len() implies (#[trigger] cc[i]) < 0x80u8 by {
            assert(cc[i] < 0x80u8) by (compute);
        }
    }
    lemma_chars_ascii(cc);
    let pc = chars(cc);
    assert forall|i: int| 0 <= i < pc.len() implies #[trigger] pc[i] != esc() by {
        assert(pc[i] == seq![cc[i]]);
        assert(cc[i] != 92u8);
        assert(pc[i][0] != esc()[0]);
    }
    lemma_tokens_no_dangling(pc, esc(), 0);
    crate::bridge::fns::like::lemma_like_mt_std(chars(s), like_tokens(pc, Some(esc()), 0));
    lemma_like_shape(s, cc);
}

/// A supplier row matches the subquery's pattern.
pub open spec fn cc_true(v: Val) -> bool {
    like_true(v, cc_bytes())
}

/// The subquery's rows over supplier rows `srows`: the suppkey of every matching row, in order.
pub open spec fn sub_rows(srows: Seq<Row>) -> Seq<Row> {
    keep(srows, |s: Row| cc_true(s[6])).map_values(|s: Row| seq![s[0]])
}

/// A supplier row with its key and comment.
pub open spec fn s_shape(s: Row) -> bool {
    s.len() == 7 && s[0] is Int && s[6] is Text
}

/// The subquery in the environment of an outer row `x` (14 values).
pub proof fn lemma_sub_eval(db: Database, x: Row)
    requires
        db.tables.len() > 5,
        x.len() == 14,
        forall|j: int| 0 <= j < db.tables[5].len() ==> #[trigger] s_shape(db.tables[5][j]),
    ensures
        eval_query(db, x, sub_q()) == Ok::<Relation, SqlError>(sub_rows(db.tables[5])),
{
    let srows = db.tables[5];
    let f = |s: Row| cc_true(s[6]);
    let fq = Query::Filter { pred: Pred::OfBool(sub_like()), input: Box::new(Query::Table(5)) };
    assert(eval_query(db, x, Query::Table(5)) == Ok::<Relation, SqlError>(srows));
    // The filter.
    let rs = Seq::new(srows.len(), |i: int| eval_pred(db, x + srows[i], Pred::OfBool(sub_like())));
    let tv = Seq::new(srows.len(), |i: int| truth_of(f(srows[i])));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(tv[i]) by {
        let env = x + srows[i];
        assert(s_shape(srows[i]));
        assert(env[20] == srows[i][6]);
        lemma_like_call(db, env, 20, cc_bytes());
        lemma_cc_like(srows[i][6]->Text_0);
    }
    lemma_collect_all(rs, tv);
    lemma_collect_pointwise::<Truth>();
    lemma_keep_true_keep(srows, tv, f);
    let kept = keep(srows, f);
    assert(eval_query(db, x, fq) == Ok::<Relation, SqlError>(kept));
    // The projection.
    lemma_keep_members(srows, f);
    let outs = kept.map_values(|s: Row| seq![s[0]]);
    let prs = Seq::new(kept.len(), |i: int| eval_exprs(db, x + kept[i], seq![Expr::Col(14)]));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Row, SqlError>(outs[i]) by {
        let env = x + kept[i];
        assert(srows.contains(kept[i]));
        let j = choose|j: int| 0 <= j < srows.len() && srows[j] == kept[i];
        assert(s_shape(srows[j]));
        assert(env[14] == kept[i][0]);
        let one = expr_results(db, env, seq![Expr::Col(14)]);
        lemma_expr_results_index(db, env, seq![Expr::Col(14)]);
        assert(one[0] == Ok::<Val, SqlError>(env[14]));
        lemma_collect_all(one, seq![env[14]]);
    }
    lemma_collect_all(prs, outs);
    lemma_collect_pointwise::<Row>();
}

/// `v = ANY (rows)` over rows whose first value is an integer: two-valued membership.
pub proof fn lemma_any_eq(v: int, rows: Seq<Row>)
    requires forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() >= 1 && rows[i][0] is Int,
    ensures
        any_cmp_truth(CmpOp::Eq, Val::Int(v), rows)
            == Ok::<Truth, SqlError>(truth_of(exists|i: int| 0 <= i < rows.len() && (#[trigger] rows[i])[0] == Val::Int(v))),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let d = rows.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]).len() >= 1 && d[i][0] is Int by {
            assert(d[i] == rows[i]);
        }
        lemma_any_eq(v, d);
        let last = rows.last();
        assert(first_col(last) == Ok::<Val, SqlError>(last[0]));
        let y = last[0]->Int_0;
        assert(cmp_truth(CmpOp::Eq, Val::Int(v), last[0]) == Ok::<Truth, SqlError>(truth_of(v == y)));
        let a = exists|i: int| 0 <= i < d.len() && (#[trigger] d[i])[0] == Val::Int(v);
        let b = exists|i: int| 0 <= i < rows.len() && (#[trigger] rows[i])[0] == Val::Int(v);
        assert(b == (a || v == y)) by {
            if a {
                let i = choose|i: int| 0 <= i < d.len() && (#[trigger] d[i])[0] == Val::Int(v);
                assert(rows[i] == d[i]);
            }
            if v == y {
                assert(rows[rows.len() - 1][0] == Val::Int(v));
            }
            if b {
                let i = choose|i: int| 0 <= i < rows.len() && (#[trigger] rows[i])[0] == Val::Int(v);
                if i < d.len() {
                    assert(d[i] == rows[i]);
                }
            }
        }
    }
}

/// Some supplier row matching the pattern has key `v`.
pub open spec fn in_sub(srows: Seq<Row>, v: Val) -> bool {
    exists|j: int| 0 <= j < srows.len() && #[trigger] srows[j][0] == v && cc_true(srows[j][6])
}

/// `ps_suppkey NOT IN (subquery)` on an outer row with an integer suppkey.
pub proof fn lemma_notin_pred(db: Database, x: Row)
    requires
        db.tables.len() > 5,
        x.len() == 14, x[1] is Int,
        forall|j: int| 0 <= j < db.tables[5].len() ==> #[trigger] s_shape(db.tables[5][j]),
    ensures
        eval_pred(db, x, notin_pred()) == Ok::<Truth, SqlError>(truth_of(!in_sub(db.tables[5], x[1]))),
{
    let srows = db.tables[5];
    let f = |s: Row| cc_true(s[6]);
    lemma_sub_eval(db, x);
    let rows = sub_rows(srows);
    let kept = keep(srows, f);
    lemma_keep_members(srows, f);
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] rows[i]).len() >= 1 && rows[i][0] is Int by {
        assert(srows.contains(kept[i]));
        let j = choose|j: int| 0 <= j < srows.len() && srows[j] == kept[i];
        assert(s_shape(srows[j]));
    }
    let v = x[1]->Int_0;
    lemma_any_eq(v, rows);
    let ex = exists|i: int| 0 <= i < rows.len() && (#[trigger] rows[i])[0] == Val::Int(v);
    assert(ex == in_sub(srows, x[1])) by {
        if ex {
            let i = choose|i: int| 0 <= i < rows.len() && (#[trigger] rows[i])[0] == Val::Int(v);
            assert(srows.contains(kept[i]) && f(kept[i]));
            let j = choose|j: int| 0 <= j < srows.len() && srows[j] == kept[i];
            assert(rows[i] == seq![kept[i][0]]);
            assert(srows[j][0] == x[1]);
        }
        if in_sub(srows, x[1]) {
            let j = choose|j: int| 0 <= j < srows.len() && #[trigger] srows[j][0] == x[1] && cc_true(srows[j][6]);
            super::common::relops::lemma_keep_has(srows, f, srows[j]);
            let i = choose|i: int| 0 <= i < kept.len() && kept[i] == srows[j];
            assert(rows[i][0] == Val::Int(v));
        }
    }
    let aq = Pred::AnyCmp { op: CmpOp::Eq, e: Expr::Col(1), q: Box::new(sub_q()) };
    assert(eval_expr(db, x, Expr::Col(1)) == Ok::<Val, SqlError>(x[1]));
    assert(x[1] == Val::Int(v));
    assert(any_cmp_truth(CmpOp::Eq, x[1], rows) == Ok::<Truth, SqlError>(truth_of(ex)));
    assert(eval_pred(db, x, aq) == Ok::<Truth, SqlError>(truth_of(ex)));
    lemma_pred_not(db, x, aq, ex);
}

// ------------------------------------------------------------------------------------------------ the WHERE

/// An outer row: partsupp (5) ++ part (9), with the types the condition and the grouping read.
pub open spec fn xrow_ok(x: Row) -> bool {
    &&& x.len() == 14
    &&& x[0] is Int && x[1] is Int && x[5] is Int
    &&& x[8] is Text && x[9] is Text && x[10] is Int
}

/// The WHERE without the NOT IN, on rows whose LIKE does not fail.
pub open spec fn pre_q(m: Prm, x: Row) -> bool {
    &&& x[5] == x[0]
    &&& x[8] != Val::Text(m.brand)
    &&& !like_true(x[9], m.pat)
    &&& in_sizes(m, x[10])
}

/// An error of the left operand of AND is the outcome.
pub proof fn lemma_and_err_left(db: Database, env: Row, a: Pred, b: Pred, e: SqlError)
    requires eval_pred(db, env, a) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, cand(a, b)) == Err::<Truth, SqlError>(e),
{
}

/// An error of the right operand of AND after a value of the left one is the outcome.
pub proof fn lemma_and_err_right(db: Database, env: Row, a: Pred, b: Pred, t: Truth, e: SqlError)
    requires eval_pred(db, env, a) == Ok::<Truth, SqlError>(t), eval_pred(db, env, b) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, cand(a, b)) == Err::<Truth, SqlError>(e),
{
}

/// The WHERE without the NOT IN on one row.
pub proof fn lemma_pre_pred(db: Database, ps: Seq<Literal>, x: Row)
    requires params_ok(ps), xrow_ok(x),
    ensures
        like_res(x[9], prm_of(ps).pat) matches Err(e) ==> eval_pred(db, x, pre_pred(ps)) == Err::<Truth, SqlError>(e),
        like_res(x[9], prm_of(ps).pat) is Ok ==> eval_pred(db, x, pre_pred(ps)) == Ok::<Truth, SqlError>(truth_of(pre_q(prm_of(ps), x))),
{
    let m = prm_of(ps);
    lemma_eq_int(db, x, 5, 0);
    lemma_brand_pred(db, ps, x);
    lemma_type_pred(db, ps, x);
    lemma_size_pred(db, ps, x);
    let b1 = x[5] == x[0];
    let b2 = x[8] != Val::Text(m.brand);
    let b4 = in_sizes(m, x[10]);
    let p2 = cand(ceq(5, 0), brand_pred(ps));
    let p3 = cand(p2, type_pred(ps));
    lemma_pred_and(db, x, ceq(5, 0), brand_pred(ps), b1, b2);
    match like_res(x[9], m.pat) {
        Err(e) => {
            lemma_and_err_right(db, x, p2, type_pred(ps), truth_of(b1 && b2), e);
            lemma_and_err_left(db, x, p3, size_pred(ps), e);
        },
        Ok(v) => {
            let b3 = !like_true(x[9], m.pat);
            lemma_pred_and(db, x, p2, type_pred(ps), b1 && b2, b3);
            lemma_pred_and(db, x, p3, size_pred(ps), b1 && b2 && b3, b4);
        },
    }
}

/// The WHERE on one row: the LIKE error, or `True` exactly under `pre_q` and NOT IN.
pub proof fn lemma_outer_pred(db: Database, ps: Seq<Literal>, x: Row)
    requires
        params_ok(ps), xrow_ok(x),
        db.tables.len() > 5,
        forall|j: int| 0 <= j < db.tables[5].len() ==> #[trigger] s_shape(db.tables[5][j]),
    ensures
        like_res(x[9], prm_of(ps).pat) matches Err(e) ==> eval_pred(db, x, outer_pred(ps)) == Err::<Truth, SqlError>(e),
        like_res(x[9], prm_of(ps).pat) is Ok ==> eval_pred(db, x, outer_pred(ps))
            == Ok::<Truth, SqlError>(truth_of(pre_q(prm_of(ps), x) && !in_sub(db.tables[5], x[1]))),
{
    lemma_pre_pred(db, ps, x);
    lemma_notin_pred(db, x);
    match like_res(x[9], prm_of(ps).pat) {
        Err(e) => {
            lemma_and_err_left(db, x, pre_pred(ps), notin_pred(), e);
        },
        Ok(v) => {
            lemma_pred_and(db, x, pre_pred(ps), notin_pred(), pre_q(prm_of(ps), x), !in_sub(db.tables[5], x[1]));
        },
    }
}

} // verus!
