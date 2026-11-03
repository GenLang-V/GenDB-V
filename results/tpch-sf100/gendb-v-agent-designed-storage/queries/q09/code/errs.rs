//! LIKE's errors. With the escape `\` the only error `p_name LIKE $1` can raise is 22025 (`lemma_like_err`), so when
//! some part name raises and the FROM product is nonempty, every failing WHERE evaluation fails with that one error
//! and the statement's outcome is it (`lemma_q9_err`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::relation::product_rows;
use crate::spec::fns::like::*;
use crate::query::query_spec_at;
use crate::link::query::proj;
use crate::link::capacity::lemma_filter_err;
use crate::link::outcome::lemma_outcome_err;
use crate::bridge::relation::lemma_product_rows_elems;
use super::model::*;
use super::qspec::*;
use super::sqlrow::*;
use super::sqllink::*;
use super::answer::bound_ok;

verus! {

pub open spec fn ies() -> SqlError {
    SqlError::InvalidEscapeSequence
}

pub open spec fn ies_or_ok<T>(r: Result<T, SqlError>) -> bool {
    r is Ok || r == Err::<T, SqlError>(ies())
}

proof fn lemma_end_ok(p: Seq<LikeTok>, j: int)
    ensures like_end(p, j) is Ok,
    decreases p.len() - j,
{
    if 0 <= j < p.len() {
        if p[j] is Any {
            lemma_end_ok(p, j + 1);
        }
    }
}

proof fn lemma_mt_err(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    ensures ies_or_ok(like_mt(t, p, i, j)),
    decreases p.len() - j, 0int, t.len() - i,
{
    if 0 <= i < t.len() && 0 <= j < p.len() {
        match p[j] {
            LikeTok::Dangling => {},
            LikeTok::Lit(c) => {
                if t[i] == c {
                    lemma_mt_err(t, p, i + 1, j + 1);
                }
            },
            LikeTok::One => lemma_mt_err(t, p, i + 1, j + 1),
            LikeTok::Any => lemma_any_err(t, p, i, j + 1),
        }
    } else if 0 <= i < t.len() {
    } else {
        lemma_end_ok(p, j);
    }
}

proof fn lemma_any_err(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    ensures ies_or_ok(like_any(t, p, i, j)),
    decreases p.len() - j, 2int, t.len() - i,
{
    if 0 <= j < p.len() {
        match p[j] {
            LikeTok::Any => lemma_any_err(t, p, i, j + 1),
            LikeTok::One => {
                if 0 <= i < t.len() {
                    lemma_any_err(t, p, i + 1, j + 1);
                }
            },
            LikeTok::Dangling => {},
            LikeTok::Lit(_) => lemma_scan_err(t, p, i, j),
        }
    }
}

proof fn lemma_scan_err(t: Seq<Seq<u8>>, p: Seq<LikeTok>, k: int, j: int)
    ensures ies_or_ok(like_scan(t, p, k, j)),
    decreases p.len() - j, 1int, t.len() - k,
{
    if 0 <= k < t.len() {
        lemma_mt_err(t, p, k, j);
        if like_mt(t, p, k, j) == Ok::<LikeRes, SqlError>(LikeRes::NoMatch) {
            lemma_scan_err(t, p, k + 1, j);
        }
    }
}

/// `s LIKE pat ESCAPE '\'` on a text raises only 22025.
pub proof fn lemma_like_err(s: Val, pat: Seq<u8>)
    requires s is Text,
    ensures ies_or_ok(like_value(s, Val::Text(pat), Val::Text(esc()))),
{
    let ec = crate::spec::chars::chars(esc());
    if ec.len() <= 1 {
        let sb = s->Text_0;
        lemma_mt_err(crate::spec::chars::chars(sb), like_tokens(crate::spec::chars::chars(pat), escape_of(ec), 0), 0, 0);
    }
}

/// `l[a] ++ r[b]` is a row of the product.
proof fn lemma_product_at(l: Seq<Row>, r: Seq<Row>, a: int, b: int) -> (k: int)
    requires 0 <= a < l.len(), 0 <= b < r.len(),
    ensures 0 <= k < product_rows(l, r).len(), product_rows(l, r)[k] == l[a] + r[b],
    decreases l.len(),
{
    let init = l.drop_last();
    lemma_product_rows_elems(init, r);
    lemma_product_rows_elems(l, r);
    let pi = product_rows(init, r);
    assert(product_rows(l, r) == pi + r.map_values(|x: Row| l.last() + x));
    if a == l.len() - 1 {
        let k = pi.len() + b;
        assert(product_rows(l, r)[k] == l.last() + r[b]);
        k
    } else {
        let k = lemma_product_at(init, r, a, b);
        assert(init[a] == l[a]);
        k
    }
}

/// A FROM row whose part is row `c`.
proof fn lemma_from_part(db: Database, m: M, c: int) -> (i: int)
    requires
        db_ok(db), rel_ok(m, db), 0 <= c < m.p_n,
        m.s_n > 0, m.l_n > 0, m.t_n > 0, m.o_n > 0, m.n_n > 0,
    ensures
        0 <= i < from_rows(db).len(),
        from_rows(db)[i][1] == Val::Text(pname(m, c)),
{
    lemma_widths(db);
    let (t3, t5, t0, t4, t1, t6) = (db.tables[3], db.tables[5], db.tables[0], db.tables[4], db.tables[1], db.tables[6]);
    let a1 = product_rows(t3, t5);
    let a2 = product_rows(a1, t0);
    let a3 = product_rows(a2, t4);
    let a4 = product_rows(a3, t1);
    let k1 = lemma_product_at(t3, t5, c, 0);
    let k2 = lemma_product_at(a1, t0, k1, 0);
    let k3 = lemma_product_at(a2, t4, k2, 0);
    let k4 = lemma_product_at(a3, t1, k3, 0);
    let k5 = lemma_product_at(a4, t6, k4, 0);
    assert(proj(t3[c], pcols()) == prow(m, c));
    assert(proj(t3[c], pcols())[1] == t3[c][1]);
    assert(t3[c].len() == 9);
    assert(a1[k1][1] == t3[c][1]);
    assert(a2[k2][1] == t3[c][1]);
    assert(a3[k3][1] == t3[c][1]);
    assert(a4[k4][1] == t3[c][1]);
    assert(from_rows(db)[k5][1] == t3[c][1]);
    k5
}

/// Every WHERE evaluation is two-valued or raises 22025; on a FROM row of part `c` it raises when `plike` does.
proof fn lemma_pred_errs(db: Database, m: M, ps: Seq<Literal>)
    requires bound_ok(db, m, ps),
    ensures
        forall|i: int| 0 <= i < from_rows(db).len() ==> ies_or_ok(#[trigger] eval_pred(db, from_rows(db)[i], q9_pred(ps))),
        forall|i: int| 0 <= i < from_rows(db).len() && (#[trigger] from_rows(db)[i])[1] is Text
            && like_value(from_rows(db)[i][1], Val::Text(qp_of(ps).pat), Val::Text(esc())) is Err
            ==> eval_pred(db, from_rows(db)[i], q9_pred(ps)) == Err::<Truth, SqlError>(ies()),
{
    let rows = from_rows(db);
    let p = qp_of(ps);
    assert forall|i: int| 0 <= i < rows.len() implies ies_or_ok(#[trigger] eval_pred(db, rows[i], q9_pred(ps)))
        && (like_value(rows[i][1], Val::Text(p.pat), Val::Text(esc())) is Err
            ==> eval_pred(db, rows[i], q9_pred(ps)) == Err::<Truth, SqlError>(ies())) by {
        let (c, s, j, t, q, n) = lemma_from_row(db, m, i);
        lemma_jrow_typed(m, c, s, j, t, q, n);
        let x = jrow(m, c, s, j, t, q, n);
        lemma_pred_eval(db, rows[i], x, ps);
        lemma_like_err(x[1], p.pat);
        lemma_xs_product(db);
        assert(x[1] == rows[i][1]);
    }
}

/// When some part name raises in LIKE and the FROM product is nonempty, the statement's outcome is 22025.
pub proof fn lemma_q9_err(db: Database, m: M, ps: Seq<Literal>, c: int)
    requires
        bound_ok(db, m, ps), 0 <= c < m.p_n, plike(m, qp_of(ps), c) is Err,
        m.s_n > 0, m.l_n > 0, m.t_n > 0, m.o_n > 0, m.n_n > 0,
    ensures ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(ies())),
{
    let rows = from_rows(db);
    let ctx = Seq::<Val>::empty();
    lemma_widths(db);
    lemma_from_eval(db);
    lemma_pred_errs(db, m, ps);
    let i = lemma_from_part(db, m, c);
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, ctx + rows[k], q9_pred(ps)) is Ok
        || eval_pred(db, ctx + rows[k], q9_pred(ps)) == Err::<Truth, SqlError>(ies()) by {
        assert(ctx + rows[k] =~= rows[k]);
    }
    assert(ctx + rows[i] =~= rows[i]);
    lemma_filter_err(db, ctx, q9_pred(ps), Box::new(q9_from()), rows, ies(), i);
    assert(eval_query(db, ctx, q9_filter(ps)) == Err::<Relation, SqlError>(ies()));
    assert(eval_query(db, ctx, q9_project(ps)) == Err::<Relation, SqlError>(ies()));
    assert(eval_query(db, ctx, q9_body(ps)) == Err::<Relation, SqlError>(ies()));
    lemma_q9_shape(ps);
    lemma_outcome_err(db, query_spec_at(ps), ies());
}

} // verus!
