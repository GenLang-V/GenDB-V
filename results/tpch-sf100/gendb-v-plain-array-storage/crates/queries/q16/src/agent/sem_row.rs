//! The WHERE condition on one row of `FROM partsupp, part` (partsupp row `c`, part row `a`, `prow`): when the
//! part's `p_type LIKE $2` is a value, the condition evaluates to the normal form `qual` (`lemma_where_row`);
//! otherwise to that `LIKE`'s error (AND evaluates both operands, so the error is raised on every such row).
//!
//! Normal form: `part_ok(a)` (brand differs from `$1`, type does not match `$2`, size among `$3..$10`) and `qual(c, a)`
//! (`ps_partkey = p_partkey`, `part_ok(a)`, and the supplier key not `excluded`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::query::param_domain;
use crate::link::expr::{lemma_pred_cmp, lemma_pred_text_cmp, lemma_pred_and, lemma_pred_or, lemma_pred_not, lemma_compare_int};
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem_ast::*;
use crate::agent::sem_sub::*;
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_partsupp::interface as psi;

verus! {

/// The parameter values: `$1`, `$2` (texts) and `$(3 + i)` (integers).
pub open spec fn brand_lit(ps: Seq<Literal>) -> Seq<u8> { ps[0]->Text_0 }
pub open spec fn pat_lit(ps: Seq<Literal>) -> Seq<u8> { ps[1]->Text_0 }
pub open spec fn size_lit(ps: Seq<Literal>, i: int) -> int { ps[2 + i]->Int_v }

/// `s` is one of the first `n` sizes `$3..`.
pub open spec fn size_match(ps: Seq<Literal>, n: int, s: int) -> bool
    decreases n,
{
    if n <= 1 { s == size_lit(ps, 0) } else { size_match(ps, n - 1, s) || s == size_lit(ps, n - 1) }
}

/// `p_type LIKE $2` of part row `a`.
pub open spec fn type_res(sv: StoresView, ps: Seq<Literal>, a: int) -> Result<Val, SqlError> {
    like_res(p_type(sv, a), pat_lit(ps))
}

pub open spec fn type_hit(sv: StoresView, ps: Seq<Literal>, a: int) -> bool {
    type_res(sv, ps, a) == Ok::<Val, SqlError>(Val::Bool(true))
}

/// The part conditions: brand differs from `$1`, type does not match `$2`, size among `$3..$10`.
pub open spec fn part_ok(sv: StoresView, ps: Seq<Literal>, a: int) -> bool {
    &&& p_brand(sv, a) != brand_lit(ps)
    &&& !type_hit(sv, ps, a)
    &&& size_match(ps, 8, p_sizes(sv)[a] as int)
}

/// Row `(c, a)` of the product satisfies the WHERE condition.
pub open spec fn qual(sv: StoresView, ps: Seq<Literal>, c: int, a: int) -> bool {
    &&& ps_pkeys(sv)[c] == p_keys(sv)[a]
    &&& part_ok(sv, ps, a)
    &&& !excluded(sv, ps_skeys(sv)[c] as int)
}

/// Row `(c, a)` of the product.
pub open spec fn prow(sv: StoresView, c: int, a: int) -> Row {
    ps_rows(sv)[c] + part_rows(sv)[a]
}

/// The parameters of the domain have their declared literal forms.
pub proof fn lemma_params(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures
        ps.len() == 10,
        ps[0] == Literal::Text(brand_lit(ps)),
        ps[1] == Literal::Text(pat_lit(ps)),
        forall|i: int| 0 <= i < 8 ==> #[trigger] ps[2 + i] == (Literal::Int { v: size_lit(ps, i), kind: IntKind::Int4 })
            && int_in_range(IntKind::Int4, size_lit(ps, i)),
{
    assert forall|i: int| 0 <= i < 8 implies #[trigger] ps[2 + i] == (Literal::Int { v: size_lit(ps, i), kind: IntKind::Int4 })
        && int_in_range(IntKind::Int4, size_lit(ps, i)) by {
        if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {} else if i == 5 {} else if i == 6 {} else {}
    }
}

/// The values of a product row that the query reads.
pub proof fn lemma_prow(sv: StoresView, c: int, a: int)
    requires stores_wf(sv), 0 <= c < ps_n(sv), 0 <= a < part_n(sv),
    ensures
        prow(sv, c, a).len() == 14,
        prow(sv, c, a)[0] == Val::Int(ps_pkeys(sv)[c] as int),
        prow(sv, c, a)[1] == Val::Int(ps_skeys(sv)[c] as int),
        prow(sv, c, a)[5] == Val::Int(p_keys(sv)[a] as int),
        prow(sv, c, a)[8] == Val::Text(p_brand(sv, a)),
        prow(sv, c, a)[9] == Val::Text(p_type(sv, a)),
        prow(sv, c, a)[10] == Val::Int(p_sizes(sv)[a] as int),
{
    let q = ps_rows(sv)[c];
    let p = part_rows(sv)[a];
    assert(q == psi::row_at(sv.flat_partsupp, c));
    assert(p == pi::row_at(sv.flat_part, a));
    let r = prow(sv, c, a);
    assert(r[0] == q[0] && r[1] == q[1]);
    assert(r[5] == p[0] && r[8] == p[3] && r[9] == p[4] && r[10] == p[5]);
}

/// One disjunct `p_size = $(3 + i)` on a row with size `sz`.
#[verifier::spinoff_prover]
proof fn lemma_size_eq(db: Database, env: Row, ps: Seq<Literal>, i: int, sz: int)
    requires param_domain(ps), 0 <= i < 8, env.len() == 14, env[10] == Val::Int(sz),
    ensures eval_pred(db, env, size_eq(ps, i)) == Ok::<Truth, SqlError>(truth_of(sz == size_lit(ps, i))),
{
    lemma_params(ps);
    let v = size_lit(ps, i);
    assert(ps[2 + i] == (Literal::Int { v, kind: IntKind::Int4 }));
    assert(eval_expr(db, env, Expr::Lit(ps[2 + i])) == Ok::<Val, SqlError>(Val::Int(v)));
    lemma_compare_int(sz, v);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(10), Expr::Lit(ps[2 + i]), Val::Int(sz), Val::Int(v), sz, v);
}

/// The first `n` disjuncts of `p_size IN (..)` on a row with size `sz`.
proof fn lemma_size_in(db: Database, env: Row, ps: Seq<Literal>, n: int, sz: int)
    requires param_domain(ps), 1 <= n <= 8, env.len() == 14, env[10] == Val::Int(sz),
    ensures eval_pred(db, env, size_in(ps, n)) == Ok::<Truth, SqlError>(truth_of(size_match(ps, n, sz))),
    decreases n,
{
    if n == 1 {
        lemma_size_eq(db, env, ps, 0, sz);
    } else {
        lemma_size_in(db, env, ps, n - 1, sz);
        lemma_size_eq(db, env, ps, n - 1, sz);
        lemma_pred_or(db, env, size_in(ps, n - 1), size_eq(ps, n - 1), size_match(ps, n - 1, sz), sz == size_lit(ps, n - 1));
    }
}

/// `p_partkey = ps_partkey` and `p_brand <> $1` (node n13).
#[verifier::spinoff_prover]
proof fn lemma_where1(db: Database, sv: StoresView, ps: Seq<Literal>, c: int, a: int)
    requires stores_wf(sv), param_domain(ps), 0 <= c < ps_n(sv), 0 <= a < part_n(sv),
    ensures
        eval_pred(db, prow(sv, c, a), where1(ps))
            == Ok::<Truth, SqlError>(truth_of(ps_pkeys(sv)[c] == p_keys(sv)[a] && p_brand(sv, a) != brand_lit(ps))),
{
    let env = prow(sv, c, a);
    lemma_prow(sv, c, a);
    lemma_params(ps);
    let (pk, qk) = (p_keys(sv)[a] as int, ps_pkeys(sv)[c] as int);
    lemma_compare_int(pk, qk);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(5), Expr::Col(0), Val::Int(pk), Val::Int(qk), pk, qk);
    assert(eval_expr(db, env, Expr::Lit(ps[0])) == Ok::<Val, SqlError>(Val::Text(brand_lit(ps))));
    lemma_pred_text_cmp(db, env, CmpOp::Ne, Expr::Col(8), Expr::Lit(ps[0]), p_brand(sv, a), brand_lit(ps));
    lemma_pred_and(db, env, key_eq(), brand_ne(ps), pk == qk, p_brand(sv, a) != brand_lit(ps));
}

/// `p_type NOT LIKE $2` (node n21): the negated boolean, or the `LIKE` error.
#[verifier::spinoff_prover]
proof fn lemma_not_like(db: Database, sv: StoresView, ps: Seq<Literal>, c: int, a: int)
    requires stores_wf(sv), param_domain(ps), 0 <= c < ps_n(sv), 0 <= a < part_n(sv),
    ensures
        type_res(sv, ps, a) matches Err(e) ==> eval_pred(db, prow(sv, c, a), type_not_like(ps)) == Err::<Truth, SqlError>(e),
        type_res(sv, ps, a) is Ok ==> type_res(sv, ps, a)->Ok_0 is Bool
            && eval_pred(db, prow(sv, c, a), type_not_like(ps)) == Ok::<Truth, SqlError>(truth_of(!type_hit(sv, ps, a))),
{
    let env = prow(sv, c, a);
    lemma_prow(sv, c, a);
    lemma_params(ps);
    assert(type_like(ps) == like_call(9, pat_lit(ps)));
    lemma_like_pred(db, env, 9, pat_lit(ps), p_type(sv, a));
    if type_res(sv, ps, a) is Ok {
        let b = type_res(sv, ps, a)->Ok_0->Bool_0;
        lemma_pred_not(db, env, Pred::OfBool(type_like(ps)), b);
    }
}

/// The WHERE condition on product row `(c, a)`: `qual`, or the part's `LIKE` error.
#[verifier::spinoff_prover]
pub proof fn lemma_where_row(db: Database, sv: StoresView, ps: Seq<Literal>, c: int, a: int)
    requires tables_of(sv, db), stores_wf(sv), param_domain(ps), 0 <= c < ps_n(sv), 0 <= a < part_n(sv),
    ensures
        type_res(sv, ps, a) matches Err(e) ==> eval_pred(db, prow(sv, c, a), where_pred(ps)) == Err::<Truth, SqlError>(e),
        type_res(sv, ps, a) is Ok ==> eval_pred(db, prow(sv, c, a), where_pred(ps)) == Ok::<Truth, SqlError>(truth_of(qual(sv, ps, c, a))),
{
    let env = prow(sv, c, a);
    lemma_prow(sv, c, a);
    lemma_where1(db, sv, ps, c, a);
    lemma_not_like(db, sv, ps, c, a);
    let k1 = ps_pkeys(sv)[c] == p_keys(sv)[a] && p_brand(sv, a) != brand_lit(ps);
    if type_res(sv, ps, a) is Ok {
        let sz = p_sizes(sv)[a] as int;
        lemma_size_in(db, env, ps, 8, sz);
        lemma_in_sub(db, sv, env, ps_skeys(sv)[c] as int);
        lemma_pred_not(db, env, in_sub(), excluded(sv, ps_skeys(sv)[c] as int));
        lemma_pred_and(db, env, where1(ps), type_not_like(ps), k1, !type_hit(sv, ps, a));
        lemma_pred_and(db, env, where2(ps), size_in(ps, 8), k1 && !type_hit(sv, ps, a), size_match(ps, 8, sz));
        lemma_pred_and(db, env, where3(ps), not_in(), k1 && !type_hit(sv, ps, a) && size_match(ps, 8, sz),
            !excluded(sv, ps_skeys(sv)[c] as int));
    } else {
        let e = type_res(sv, ps, a)->Err_0;
        assert(eval_pred(db, env, where2(ps)) == Err::<Truth, SqlError>(e));
        assert(eval_pred(db, env, where3(ps)) == Err::<Truth, SqlError>(e));
        assert(eval_pred(db, env, where_pred(ps)) == Err::<Truth, SqlError>(e));
    }
}

} // verus!
