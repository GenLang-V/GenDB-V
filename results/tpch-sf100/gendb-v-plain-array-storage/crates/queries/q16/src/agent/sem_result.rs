//! The statement's meaning over the stored columns, as the three outcomes the query can answer:
//! - `lemma_answer_rows`: when no part's `LIKE` fails (or FROM is empty) and every group count fits int8, any
//!   duplicate-free output sorted by the ORDER BY keys that holds exactly the rows `out_row(k)` of the groups
//!   (`is_group`) is an allowed output;
//! - `lemma_answer_like_err`: with partsupp non-empty, the error of the first part row whose `LIKE` fails;
//! - `lemma_answer_count_err`: 22003 when some group count leaves int8.
//!
//! A group key is `krow(a) = (p_brand, p_type, p_size)` of a part row `a` that qualifies with some partsupp row
//! (`qual`); its count `gcount(k)` is the number of distinct supplier keys of those qualifying rows
//! (`lemma_vals_contains`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::limits::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::eval::*;
use crate::spec::equality::distinct_rows;
use crate::query::{param_domain, query_spec_at};
use crate::link::join::{keep, lemma_keep_members, lemma_keep_none};
use crate::link::query::lemma_nodup_same_multiset;
use crate::link::outcome::lemma_outcome_sorted;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem_ast::*;
use crate::agent::sem_sub::*;
use crate::agent::sem_row::*;
use crate::agent::sem_body::*;
use crate::agent::sem_sub::lemma_keep_has;
use crate::agent::common::group_distinct::*;

verus! {

/// The group key of part row `a`.
pub open spec fn krow(sv: StoresView, a: int) -> Row {
    seq![Val::Text(p_brand(sv, a)), Val::Text(p_type(sv, a)), Val::Int(p_sizes(sv)[a] as int)]
}

/// `k` is the key of some qualifying product row.
pub open spec fn is_group(sv: StoresView, ps: Seq<Literal>, k: Row) -> bool {
    exists|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a) && krow(sv, a) == k
}

/// The supplier key `v` occurs in a qualifying row of group `k`.
pub open spec fn in_vals(sv: StoresView, ps: Seq<Literal>, k: Row, v: Val) -> bool {
    exists|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a) && krow(sv, a) == k
        && v == Val::Int(ps_skeys(sv)[c] as int)
}

/// The distinct supplier keys of group `k` and their number.
pub open spec fn gvals(sv: StoresView, ps: Seq<Literal>, k: Row) -> Set<Val> {
    group_vals(grp_keys(sv, ps), grp_args(sv, ps), k)
}

pub open spec fn gcount(sv: StoresView, ps: Seq<Literal>, k: Row) -> nat {
    gvals(sv, ps, k).len()
}

/// The output row of group `k`: its key and count.
pub open spec fn out_row(sv: StoresView, ps: Seq<Literal>, k: Row) -> Row {
    k + seq![Val::Int(gcount(sv, ps, k) as int)]
}

/// Every group count fits int8.
pub open spec fn counts_fit(sv: StoresView, ps: Seq<Literal>) -> bool {
    forall|k: Row| #[trigger] is_group(sv, ps, k) ==> gcount(sv, ps, k) <= int8_max()
}

/// The kept rows are exactly the qualifying product rows.
pub proof fn lemma_kept_contains(sv: StoresView, ps: Seq<Literal>, r: Row)
    requires stores_wf(sv),
    ensures kept_rows(sv, ps).contains(r) <==> exists|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv)
        && #[trigger] qual(sv, ps, c, a) && r == prow(sv, c, a),
{
    let rows = from_rows(sv);
    let f = |x: Row| row_qual(sv, ps, x);
    lemma_keep_members(rows, f);
    if kept_rows(sv, ps).contains(r) {
        let x = choose|x: int| 0 <= x < kept_rows(sv, ps).len() && kept_rows(sv, ps)[x] == r;
        assert(rows.contains(r) && f(r));
        let j = choose|j: int| 0 <= j < rows.len() && rows[j] == r;
        lemma_from_index(sv, j);
        let np = part_n(sv) as int;
        lemma_row_qual(sv, ps, j / np, j % np);
        assert(qual(sv, ps, j / np, j % np));
    }
    if exists|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a) && r == prow(sv, c, a) {
        let (c, a) = choose|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a)
            && r == prow(sv, c, a);
        crate::link::join::lemma_product_index(ps_rows(sv), part_rows(sv));
        let np = part_n(sv) as int;
        let j = c * np + a;
        assert(0 <= j < rows.len()) by (nonlinear_arith)
            requires 0 <= c < ps_n(sv), 0 <= a < np, rows.len() == ps_n(sv) * np, j == c * np + a;
        assert(rows[j] == prow(sv, c, a));
        lemma_row_qual(sv, ps, c, a);
        lemma_keep_has(rows, f, j);
    }
}

/// The GROUP BY inputs are key rows of three plain values and one-integer argument rows.
pub proof fn lemma_grp_shape(sv: StoresView, ps: Seq<Literal>)
    requires stores_wf(sv),
    ensures
        grp_keys(sv, ps).len() == grp_args(sv, ps).len(),
        key_rows(grp_keys(sv, ps), 3),
        int_args(grp_args(sv, ps)),
{
    let kept = kept_rows(sv, ps);
    let (ks, ar) = (grp_keys(sv, ps), grp_args(sv, ps));
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] plain_row(ks[i]) && ks[i].len() == 3 by {
        assert(kept.contains(kept[i]));
        lemma_kept_contains(sv, ps, kept[i]);
        let (c, a) = choose|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a)
            && kept[i] == prow(sv, c, a);
        lemma_prow(sv, c, a);
        assert(ks[i] == key_of_row(kept[i]));
        assert forall|j: int| 0 <= j < ks[i].len() implies #[trigger] plain_val(ks[i][j]) by {
            if j == 0 {} else if j == 1 {} else {}
        }
    }
    assert forall|i: int| 0 <= i < ar.len() implies (#[trigger] ar[i]).len() == 1 && ar[i][0] is Int by {
        assert(kept.contains(kept[i]));
        lemma_kept_contains(sv, ps, kept[i]);
        let (c, a) = choose|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a)
            && kept[i] == prow(sv, c, a);
        lemma_prow(sv, c, a);
    }
}

/// The group keys are exactly the keys of the qualifying rows.
pub proof fn lemma_keys_contains(sv: StoresView, ps: Seq<Literal>, k: Row)
    requires stores_wf(sv),
    ensures grp_keys(sv, ps).contains(k) == is_group(sv, ps, k),
{
    let kept = kept_rows(sv, ps);
    let ks = grp_keys(sv, ps);
    if ks.contains(k) {
        let i = choose|i: int| 0 <= i < ks.len() && ks[i] == k;
        assert(kept.contains(kept[i]));
        lemma_kept_contains(sv, ps, kept[i]);
        let (c, a) = choose|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a)
            && kept[i] == prow(sv, c, a);
        lemma_prow(sv, c, a);
        assert(key_of_row(kept[i]) =~= krow(sv, a));
    }
    if is_group(sv, ps, k) {
        let (c, a) = choose|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a)
            && krow(sv, a) == k;
        lemma_kept_contains(sv, ps, prow(sv, c, a));
        let i = choose|i: int| 0 <= i < kept.len() && kept[i] == prow(sv, c, a);
        lemma_prow(sv, c, a);
        assert(ks[i] =~= k);
    }
}

/// The values of group `k` are exactly the supplier keys of its qualifying rows.
pub proof fn lemma_vals_contains(sv: StoresView, ps: Seq<Literal>, k: Row, v: Val)
    requires stores_wf(sv),
    ensures gvals(sv, ps, k).contains(v) == in_vals(sv, ps, k, v),
{
    let kept = kept_rows(sv, ps);
    let (ks, ar) = (grp_keys(sv, ps), grp_args(sv, ps));
    lemma_group_vals_contains(ks, ar, k, v);
    if in_group(ks, ar, k, v) {
        let i = choose|i: int| 0 <= i < ks.len() && 0 <= i < ar.len() && ks[i] == k && #[trigger] ar[i][0] == v;
        assert(kept.contains(kept[i]));
        lemma_kept_contains(sv, ps, kept[i]);
        let (c, a) = choose|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a)
            && kept[i] == prow(sv, c, a);
        lemma_prow(sv, c, a);
        assert(key_of_row(kept[i]) =~= krow(sv, a));
        assert(ar[i] == arg_of_row(kept[i]));
    }
    if in_vals(sv, ps, k, v) {
        let (c, a) = choose|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a)
            && krow(sv, a) == k && v == Val::Int(ps_skeys(sv)[c] as int);
        lemma_kept_contains(sv, ps, prow(sv, c, a));
        let i = choose|i: int| 0 <= i < kept.len() && kept[i] == prow(sv, c, a);
        lemma_prow(sv, c, a);
        assert(ks[i] =~= k);
        assert(ar[i][0] == v);
    }
}

/// With an empty FROM, the WHERE keeps nothing (no condition is evaluated).
#[verifier::spinoff_prover]
proof fn lemma_filter_empty(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), stores_wf(sv), ps_n(sv) == 0 || part_n(sv) == 0,
    ensures eval_query(db, Seq::empty(), filtered(ps)) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
{
    lemma_eval_from(db, sv);
    crate::link::join::lemma_product_index(ps_rows(sv), part_rows(sv));
    let rows = from_rows(sv);
    assert(rows.len() == 0) by (nonlinear_arith) requires rows.len() == ps_n(sv) * part_n(sv), ps_n(sv) == 0 || part_n(sv) == 0;
    let ctx = Seq::<Val>::empty();
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], where_pred(ps)));
    crate::bridge::collect::lemma_collect_all(prs, Seq::<Truth>::empty());
    crate::bridge::collect::lemma_collect_pointwise::<Truth>();
    assert(keep_true(rows, Seq::<Truth>::empty()) == Seq::<Row>::empty());
}

/// GROUP BY over no rows has no groups.
#[verifier::spinoff_prover]
proof fn lemma_group_empty(db: Database, ps: Seq<Literal>)
    requires eval_query(db, Seq::empty(), filtered(ps)) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
    ensures eval_query(db, Seq::empty(), body(ps)) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
{
    hide(eval_exprs);
    hide(agg_args);
    let ctx = Seq::<Val>::empty();
    let empty = Seq::<Row>::empty();
    let ins = Seq::new(empty.len(), |i: int|
        match eval_exprs(db, ctx + empty[i], group_keys()) {
            Err(err) => Err(err),
            Ok(k) => match agg_args(db, ctx + empty[i], group_aggs()) {
                Err(err) => Err(err),
                Ok(a) => Ok((k, a)),
            },
        });
    crate::bridge::collect::lemma_collect_all(ins, Seq::<(Row, Row)>::empty());
    crate::bridge::collect::lemma_collect_pointwise::<(Row, Row)>();
    let pe = Seq::<(Row, Row)>::empty();
    assert(pe.map_values(|p: (Row, Row)| p.0) =~= Seq::<Row>::empty());
    assert(pe.map_values(|p: (Row, Row)| p.1) =~= Seq::<Row>::empty());
    assert(distinct_rows(Seq::<Row>::empty()) == Seq::<Row>::empty());
    let gs = Seq::new(0, |g: int| match agg_row(group_aggs(), group_members(Seq::<Row>::empty(), Seq::<Row>::empty(), Seq::<Row>::empty()[g])) {
        Ok(a) => Ok(Seq::<Row>::empty()[g] + a),
        Err(err) => Err(err),
    });
    crate::bridge::collect::lemma_collect_all(gs, Seq::<Row>::empty());
    crate::bridge::collect::lemma_collect_pointwise::<Row>();
}

/// With an empty FROM, the body is the empty relation.
pub proof fn lemma_body_empty(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires tables_of(sv, db), stores_wf(sv), ps_n(sv) == 0 || part_n(sv) == 0,
    ensures eval_query(db, Seq::empty(), body(ps)) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
{
    lemma_filter_empty(db, sv, ps);
    lemma_group_empty(db, ps);
}

/// The body when no part's `LIKE` fails and the counts fit: a duplicate-free sequence of exactly the group rows.
pub proof fn lemma_body_rows(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires
        tables_of(sv, db), stores_wf(sv), param_domain(ps),
        forall|a: int| 0 <= a < part_n(sv) ==> #[trigger] type_res(sv, ps, a) is Ok,
        counts_fit(sv, ps),
    ensures ({
        let b = eval_query(db, Seq::empty(), body(ps));
        &&& b is Ok
        &&& b->Ok_0.no_duplicates()
        &&& forall|r: Row| #[trigger] b->Ok_0.contains(r) <==> exists|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k)
    }),
{
    lemma_body_ok(db, sv, ps);
    lemma_group_aggs();
    let (ks, ar) = (grp_keys(sv, ps), grp_args(sv, ps));
    lemma_grp_shape(sv, ps);
    assert forall|k: Row| #[trigger] ks.contains(k) implies group_vals(ks, ar, k).len() <= int8_max() by {
        lemma_keys_contains(sv, ps, k);
    }
    lemma_group_rows(Expr::Col(1), ks, ar, 3);
    let out = group_rows(count_distinct_aggs(Expr::Col(1)), ks, ar)->Ok_0;
    assert forall|r: Row| #[trigger] out.contains(r) <==> exists|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k) by {
        if out.contains(r) {
            let k = choose|k: Row| #[trigger] ks.contains(k) && r == count_row(ks, ar, k);
            lemma_keys_contains(sv, ps, k);
        }
        if exists|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k) {
            let k = choose|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k);
            lemma_keys_contains(sv, ps, k);
            assert(r == count_row(ks, ar, k));
        }
    }
}

/// An allowed output: when no part's `LIKE` fails or FROM is empty, every count fits, and `out` is a
/// duplicate-free sorted sequence of exactly the group rows.
pub proof fn lemma_answer_rows(sv: StoresView, ps: Seq<Literal>, out: Seq<Row>)
    requires
        stores_wf(sv), param_domain(ps),
        (ps_n(sv) == 0 || part_n(sv) == 0) || forall|a: int| 0 <= a < part_n(sv) ==> #[trigger] type_res(sv, ps, a) is Ok,
        counts_fit(sv, ps),
        out.no_duplicates(),
        sorted_by(order_keys(), out),
        forall|r: Row| #[trigger] out.contains(r) <==> exists|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db)
        implies ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)) by {
        lemma_tables(sv, db);
        lemma_query_shape(ps);
        let oq = query_spec_at(ps);
        if ps_n(sv) == 0 || part_n(sv) == 0 {
            lemma_body_empty(db, sv, ps);
            assert forall|r: Row| !out.contains(r) by {
                if out.contains(r) {
                    let k = choose|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k);
                    let (c, a) = choose|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv)
                        && #[trigger] qual(sv, ps, c, a) && krow(sv, a) == k;
                }
            }
            if out.len() > 0 { assert(out.contains(out[0])); }
            assert(out =~= Seq::<Row>::empty());
            lemma_outcome_sorted(db, oq, Seq::<Row>::empty(), out);
        } else {
            lemma_body_rows(db, sv, ps);
            let rows = eval_query(db, Seq::empty(), body(ps))->Ok_0;
            lemma_nodup_same_multiset(out, rows);
            lemma_outcome_sorted(db, oq, rows, out);
        }
        assert(slice_rows(out, 0, None) =~= out);
    }
}

/// The error of the first part row whose `LIKE` fails, with partsupp non-empty, is the statement's value.
pub proof fn lemma_answer_like_err(sv: StoresView, ps: Seq<Literal>, a0: int)
    requires
        stores_wf(sv), param_domain(ps),
        ps_n(sv) > 0, 0 <= a0 < part_n(sv),
        type_res(sv, ps, a0) is Err,
        forall|a: int| 0 <= a < a0 ==> #[trigger] type_res(sv, ps, a) is Ok,
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db)
            ==> ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(type_res(sv, ps, a0)->Err_0)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db)
        implies ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(type_res(sv, ps, a0)->Err_0)) by {
        lemma_tables(sv, db);
        lemma_query_shape(ps);
        lemma_body_err(db, sv, ps, a0);
    }
}

/// A group count beyond int8 (no `LIKE` failing) makes the statement's value 22003.
pub proof fn lemma_answer_count_err(sv: StoresView, ps: Seq<Literal>, k: Row)
    requires
        stores_wf(sv), param_domain(ps),
        forall|a: int| 0 <= a < part_n(sv) ==> #[trigger] type_res(sv, ps, a) is Ok,
        is_group(sv, ps, k), gcount(sv, ps, k) > int8_max(),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db)
            ==> ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db)
        implies ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)) by {
        lemma_tables(sv, db);
        lemma_query_shape(ps);
        lemma_body_ok(db, sv, ps);
        lemma_group_aggs();
        let (ks, ar) = (grp_keys(sv, ps), grp_args(sv, ps));
        lemma_grp_shape(sv, ps);
        lemma_keys_contains(sv, ps, k);
        lemma_group_rows(Expr::Col(1), ks, ar, 3);
    }
}

} // verus!
