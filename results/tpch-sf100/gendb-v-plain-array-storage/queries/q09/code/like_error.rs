//! The statement's outcome when FROM is empty or a part name's `LIKE` raises.
//!
//! The matcher's only error is 22025 (`InvalidEscapeSequence`, a dangling escape reached; `lemma_like_err_kind`). The
//! WHERE evaluates the `LIKE` on every joined row (`AND` evaluates both sides), so when every table is non-empty and
//! some part row's `LIKE` raises, the joined row of that part with the first row of every other table raises, every
//! other row succeeds or raises the same code, and the statement's meaning is that error
//! (`lemma_like_error_outcome`). When some table is empty, FROM is empty and the statement has no rows
//! (`lemma_empty_outcome`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::link::join::lemma_product_index;
use crate::link::capacity::{lemma_filter_err, lemma_first_input};
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::denotation::*;
use crate::agent::lines::*;
use crate::agent::groups::*;

verus! {

// ------------------------------------------------------------------------------------------------ the matcher's error

/// `like_end` never raises.
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

/// `like_mt` raises only 22025.
proof fn lemma_mt_err(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    ensures like_mt(t, p, i, j) is Err ==> like_mt(t, p, i, j) == Err::<LikeRes, SqlError>(SqlError::InvalidEscapeSequence),
    decreases p.len() - j, 0int, t.len() - i,
{
    if 0 <= i < t.len() && 0 <= j < p.len() {
        match p[j] {
            LikeTok::Dangling => {},
            LikeTok::Lit(c) => { if t[i] == c { lemma_mt_err(t, p, i + 1, j + 1); } },
            LikeTok::One => { lemma_mt_err(t, p, i + 1, j + 1); },
            LikeTok::Any => { lemma_any_err(t, p, i, j + 1); },
        }
    } else if 0 <= i < t.len() {
    } else {
        lemma_end_ok(p, j);
    }
}

/// `like_any` raises only 22025.
proof fn lemma_any_err(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    ensures like_any(t, p, i, j) is Err ==> like_any(t, p, i, j) == Err::<LikeRes, SqlError>(SqlError::InvalidEscapeSequence),
    decreases p.len() - j, 2int, t.len() - i,
{
    if 0 <= j < p.len() {
        match p[j] {
            LikeTok::Any => { lemma_any_err(t, p, i, j + 1); },
            LikeTok::One => { if 0 <= i < t.len() { lemma_any_err(t, p, i + 1, j + 1); } },
            LikeTok::Dangling => {},
            LikeTok::Lit(_) => { lemma_scan_err(t, p, i, j); },
        }
    }
}

/// `like_scan` raises only 22025.
proof fn lemma_scan_err(t: Seq<Seq<u8>>, p: Seq<LikeTok>, k: int, j: int)
    ensures like_scan(t, p, k, j) is Err ==> like_scan(t, p, k, j) == Err::<LikeRes, SqlError>(SqlError::InvalidEscapeSequence),
    decreases p.len() - j, 1int, t.len() - k,
{
    if 0 <= k < t.len() {
        lemma_mt_err(t, p, k, j);
        if like_mt(t, p, k, j) == Ok::<LikeRes, SqlError>(LikeRes::NoMatch) {
            lemma_scan_err(t, p, k + 1, j);
        }
    }
}

/// `p_name LIKE $1` raises only 22025 (the escape string has one character, so the matcher decides).
pub proof fn lemma_like_err_kind(name: Seq<u8>, pat: Seq<u8>)
    ensures !like_ok(name, pat) ==> like_res(name, pat) == Err::<Val, SqlError>(SqlError::InvalidEscapeSequence),
{
    let b = esc_bytes();
    assert(b.drop_last() =~= Seq::<u8>::empty());
    assert(chars(b.drop_last()) == Seq::<Seq<u8>>::empty());
    assert(!is_cont(b.last()));
    assert(chars(b).len() == 1);
    lemma_mt_err(chars(name), like_tokens(chars(pat), escape_of(chars(b)), 0), 0, 0);
}

// ------------------------------------------------------------------------------------------------ FROM

/// A product of two relations has `|a| * |b|` rows, and row `i * |b| + j` is `a[i] ++ b[j]`.
proof fn lemma_product_at(a: Seq<Row>, b: Seq<Row>, i: int, j: int)
    requires 0 <= i < a.len(), 0 <= j < b.len(),
    ensures
        0 <= i * b.len() + j < product_rows(a, b).len(),
        product_rows(a, b)[i * b.len() + j] == a[i] + b[j],
{
    lemma_product_index(a, b);
    let nb = b.len() as int;
    assert(0 <= i * nb + j < a.len() * nb) by (nonlinear_arith) requires 0 <= i < a.len(), 0 <= j < nb;
}

/// A product with an empty side is empty.
proof fn lemma_product_empty(a: Seq<Row>, b: Seq<Row>)
    requires a.len() == 0 || b.len() == 0,
    ensures product_rows(a, b).len() == 0,
{
    lemma_product_index(a, b);
    assert(a.len() * b.len() == 0) by (nonlinear_arith) requires a.len() == 0 || b.len() == 0;
}

/// Some table empty: FROM is empty.
pub proof fn lemma_from_empty(sv: StoresView, db: Database)
    requires
        bound_db(sv, db),
        n_p(sv) == 0 || n_s(sv) == 0 || n_l(sv) == 0 || n_ps(sv) == 0 || n_o(sv) == 0 || n_n(sv) == 0,
    ensures from6(db).len() == 0,
{
    lemma_parts_shape(sv, db);
    if n_p(sv) == 0 || n_s(sv) == 0 {
        lemma_product_empty(db.tables[3], db.tables[5]);
    }
    if from2(db).len() == 0 || n_l(sv) == 0 {
        lemma_product_empty(from2(db), db.tables[0]);
    }
    if from3(db).len() == 0 || n_ps(sv) == 0 {
        lemma_product_empty(from3(db), db.tables[4]);
    }
    if from4(db).len() == 0 || n_o(sv) == 0 {
        lemma_product_empty(from4(db), db.tables[1]);
    }
    lemma_product_empty(from5(db), db.tables[6]);
}

/// Every table non-empty: the joined row of part `p` with the first row of every other table is a row of FROM.
proof fn lemma_from_has(sv: StoresView, db: Database, p: int) -> (k: int)
    requires
        bound_db(sv, db), 0 <= p < n_p(sv),
        n_s(sv) > 0, n_l(sv) > 0, n_ps(sv) > 0, n_o(sv) > 0, n_n(sv) > 0,
    ensures 0 <= k < from6(db).len(), from6(db)[k] == joined6(db, p, 0, 0, 0, 0, 0),
{
    lemma_parts_shape(sv, db);
    lemma_product_at(db.tables[3], db.tables[5], p, 0);
    let k2 = p * db.tables[5].len();
    lemma_product_at(from2(db), db.tables[0], k2, 0);
    let k3 = k2 * db.tables[0].len();
    lemma_product_at(from3(db), db.tables[4], k3, 0);
    let k4 = k3 * db.tables[4].len();
    lemma_product_at(from4(db), db.tables[1], k4, 0);
    let k5 = k4 * db.tables[1].len();
    lemma_product_at(from5(db), db.tables[6], k5, 0);
    k5 * db.tables[6].len()
}

// ------------------------------------------------------------------------------------------------ the outcomes

/// Every table non-empty and part row `p0`'s `LIKE` raises: the statement's meaning is 22025.
pub proof fn lemma_like_error_outcome(sv: StoresView, db: Database, ps: Seq<Literal>, p0: int)
    requires
        bound_db(sv, db), param_domain(ps), 0 <= p0 < n_p(sv), !like_ok(pname(sv, p0), pat_of(ps)),
        n_s(sv) > 0, n_l(sv) > 0, n_ps(sv) > 0, n_o(sv) > 0, n_n(sv) > 0,
    ensures
        denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(SqlError::InvalidEscapeSequence),
        ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::InvalidEscapeSequence)),
{
    let e = SqlError::InvalidEscapeSequence;
    let rows = from6(db);
    let ctx = Seq::<Val>::empty();
    let pred = q9_pred(ps);
    lemma_eval_from(sv, db);
    lemma_query_shape(ps);
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, ctx + rows[k], pred) is Ok
        || eval_pred(db, ctx + rows[k], pred) == Err::<Truth, SqlError>(e) by {
        let (p, s, l, q, o, a) = lemma_from6_witness(sv, db, k);
        lemma_joined_shape(sv, db, p, s, l, q, o, a);
        assert(ctx + rows[k] =~= rows[k]);
        lemma_pred_shape(sv, db, ps, rows[k], p, s, l, q, o, a);
        lemma_like_err_kind(pname(sv, p), pat_of(ps));
    }
    let k0 = lemma_from_has(sv, db, p0);
    lemma_joined_shape(sv, db, p0, 0, 0, 0, 0, 0);
    assert(ctx + rows[k0] =~= rows[k0]);
    lemma_pred_shape(sv, db, ps, rows[k0], p0, 0, 0, 0, 0, 0);
    lemma_like_err_kind(pname(sv, p0), pat_of(ps));
    lemma_filter_err(db, ctx, pred, Box::new(q9_from()), rows, e, k0);
    assert(eval_query(db, ctx, q9_filter(ps)) == Err::<Relation, SqlError>(e));
    lemma_first_input(db, ctx, q9_project(ps));
    lemma_first_input(db, ctx, q9_body(ps));
}

/// FROM is empty: the statement has no rows.
pub proof fn lemma_empty_outcome(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), from6(db).len() == 0,
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(Seq::<Row>::empty())),
{
    let (g, xs) = (g2(), sel_rows(db, ps));
    assert(likes_ok(sv, db, ps));
    // no row is kept, so every group is empty
    assert(kept(db, ps).len() == 0) by {
        lemma_kept_rows(g1(ps), from6(db), q9_cols());
        lemma_proj_all_index_len(from6(db));
    }
    assert(xs.len() == 0);
    assert forall|k: Row| #![trigger gcount(g, xs, k)] #![trigger gabs(g, xs, k, 0)] gcount(g, xs, k) == 0 && gabs(g, xs, k, 0) == 0 by {}
    assert(group_caps(g, xs));
    lemma_denotation(sv, db, ps);
    let ks = Seq::<Row>::empty();
    let full = Seq::<Row>::empty();
    assert forall|k: Row| #[trigger] ks.contains(k) <==> gcount(g, xs, k) > 0 by {}
    lemma_result_from_keys(g, q9_order_keys(), 0, None, xs, ks, full);
    lemma_slice_all(full);
    lemma_query_shape(ps);
    lemma_ordered_link(db, query_spec_at(ps), g, xs, full);
}

/// `proj_all` keeps the number of rows.
proof fn lemma_proj_all_index_len(rows: Seq<Row>)
    ensures proj_all(rows, q9_cols()).len() == rows.len(),
{
    crate::link::source::lemma_proj_all_index(rows, q9_cols());
}

} // verus!
