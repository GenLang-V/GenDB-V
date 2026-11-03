//! The filtered product `lineitem x part` and its sums.
//!
//! For a database bound to the parts, the FROM product filtered by the WHERE condition evaluates to the rows of
//! `product_rows(lineitem, part)` whose query values satisfy `terms::zq` (`lemma_eval_filter_q`). A sum of any of
//! the accumulator terms over those rows is the stored total `terms::tot` over all stored lineitem rows
//! (`lemma_sum_chain`): the terms vanish off the condition, the product of the projected relations is the
//! projection of the product (`link::join::lemma_proj_product`), its sum is a sum of per-lineitem sums over the part
//! rows (`lemma_sum_of_product`), the projected part rows are the stored part rows, and the projected lineitem rows
//! are a permutation of the stored lineitem rows.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::product_rows;
use crate::spec::typing::db_wf;
use crate::link::query::{proj, proj_all};
use crate::link::join::*;
use crate::link::source::lemma_proj_all_index;
use crate::schema::schema_spec;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use super::model::*;
use super::terms::*;
use super::sqlrow::*;
use super::bind::*;
use super::answer::win_ok;

verus! {

/// The FROM product of a database.
pub open spec fn prod_of(db: Database) -> Seq<Row> {
    product_rows(db.tables[0], db.tables[3])
}

/// The WHERE condition on product rows.
pub open spec fn qx(lo: int, hi: int) -> spec_fn(Row) -> bool {
    |x: Row| zq(lo, hi, zx(x))
}

/// The rows of the product that satisfy the WHERE condition.
pub open spec fn kept_of(db: Database, lo: int, hi: int) -> Seq<Row> {
    keep(prod_of(db), qx(lo, hi))
}

/// Accumulator `k`'s term on product rows.
pub open spec fn tx(k: int, lo: int, hi: int) -> spec_fn(Row) -> int {
    |x: Row| term(k, lo, hi)(zx(x))
}

/// The typed rows of a database.
pub open spec fn rows_typed(db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& forall|i: int| 0 <= i < db.tables[0].len() ==> lrow_typed(#[trigger] db.tables[0][i])
    &&& forall|i: int| 0 <= i < db.tables[3].len() ==> prow9_typed(#[trigger] db.tables[3][i])
}

/// Every row of the product is a lineitem row followed by a part row, typed.
pub proof fn lemma_prod_typed(db: Database)
    requires rows_typed(db),
    ensures forall|i: int| 0 <= i < prod_of(db).len() ==> prow_typed(#[trigger] prod_of(db)[i]),
{
    let (l, p) = (db.tables[0], db.tables[3]);
    let pr = prod_of(db);
    lemma_product_index(l, p);
    assert forall|i: int| 0 <= i < pr.len() implies prow_typed(#[trigger] pr[i]) by {
        let np = p.len() as int;
        assert(np > 0) by {
            if np == 0 {
                assert(pr.len() == l.len() * 0);
            }
        }
        let a = i / np;
        let b = i % np;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, np);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(i, np);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(i, np);
        assert(i == a * np + b) by (nonlinear_arith) requires i == np * a + b;
        assert(a < l.len()) by (nonlinear_arith)
            requires i == a * np + b, 0 <= b, i < l.len() * np, np > 0;
        assert(pr[a * np + b] == l[a] + p[b]);
        lemma_prow_typed(l[a], p[b]);
    }
}

/// The FROM product evaluates to the product of the two tables.
pub proof fn lemma_eval_product_q(db: Database)
    requires rows_typed(db),
    ensures eval_query(db, Seq::empty(), product_q()) == Ok::<Relation, SqlError>(keep(prod_of(db), |x: Row| true)),
{
    let (l, p) = (db.tables[0], db.tables[3]);
    let t = |r: Row| true;
    lemma_eval_table(db, 0, t);
    lemma_eval_table(db, 3, t);
    assert forall|i: int| 0 <= i < l.len() implies (#[trigger] l[i]).len() == 16 by {
        assert(lrow_typed(l[i]));
    }
    lemma_eval_product(db, Query::Table(0), Query::Table(3), l, t, 16, p, t, prod_of(db), |x: Row| true);
}

/// The filtered product evaluates to the rows satisfying the condition.
pub proof fn lemma_eval_filter_q(db: Database, ps: Seq<Literal>, lo: int, hi: int)
    requires
        rows_typed(db),
        win_ok(ps, lo, hi),
    ensures
        eval_query(db, Seq::empty(), filter_q(ps)) == Ok::<Relation, SqlError>(kept_of(db, lo, hi)),
{
    let pr = prod_of(db);
    lemma_eval_product_q(db);
    lemma_prod_typed(db);
    assert forall|i: int| 0 <= i < pr.len() && (|x: Row| true)(#[trigger] pr[i]) implies
        eval_pred(db, pr[i], pred_q(ps)) == Ok::<Truth, SqlError>(truth_of(qx(lo, hi)(pr[i]))) by {
        lemma_row_pred(db, pr[i], ps, lo, hi);
    }
    lemma_eval_filter(db, product_q(), pr, |x: Row| true, pred_q(ps), qx(lo, hi), qx(lo, hi));
}

/// With an empty product, the filtered product is empty whatever the condition.
pub proof fn lemma_eval_filter_empty(db: Database, ps: Seq<Literal>)
    requires
        rows_typed(db),
        prod_of(db).len() == 0,
    ensures
        eval_query(db, Seq::empty(), filter_q(ps)) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
{
    let pr = prod_of(db);
    lemma_eval_product_q(db);
    lemma_eval_filter(db, product_q(), pr, |x: Row| true, pred_q(ps), |x: Row| false, |x: Row| false);
    lemma_keep_none(pr, |x: Row| false);
}

// ------------------------------------------------------------------------------------------------ the sum chain

/// The query values of the product are the product of the projected tables.
pub proof fn lemma_proj_prod(db: Database)
    requires rows_typed(db),
    ensures proj_all(prod_of(db), c6()) == product_rows(proj_all(db.tables[0], ca()), proj_all(db.tables[3], seq![0nat, 4nat])),
{
    let (l, p) = (db.tables[0], db.tables[3]);
    assert forall|i: int| 0 <= i < l.len() implies (#[trigger] l[i]).len() == 16 by {
        assert(lrow_typed(l[i]));
    }
    assert forall|i: int| 0 <= i < p.len() implies (#[trigger] p[i]).len() == 9 by {
        assert(prow9_typed(p[i]));
    }
    assert(ca() + shift(seq![0nat, 4nat], 16) =~= c6());
    lemma_proj_product(l, p, ca(), seq![0nat, 4nat], 16, 9);
}

/// A sum of an accumulator's terms over the kept rows is the stored total over all lineitem rows.
pub proof fn lemma_sum_chain(sv: StoresView, db: Database, k: int, lo: int, hi: int)
    requires bound_db(sv, db),
    ensures
        sum_of(kept_of(db, lo, hi), tx(k, lo, hi)) == tot(sv.facts, sv.custpart, k, lo, hi, 0, n_li(sv.facts)),
{
    let (fp, cp) = (sv.facts, sv.custpart);
    let pr = prod_of(db);
    let f = tx(k, lo, hi);
    let t = term(k, lo, hi);
    lemma_rows_typed(db);
    lemma_li_link(sv, db);
    lemma_pa_link(sv, db);
    // the terms vanish off the condition
    assert forall|i: int| 0 <= i < pr.len() && !qx(lo, hi)(#[trigger] pr[i]) implies f(pr[i]) == 0 by {}
    lemma_sum_of_keep(pr, qx(lo, hi), f);
    // the sum over the projected product
    let m = |r: Row| proj(r, c6());
    lemma_sum_of_map(pr, m, t);
    assert(proj_all(pr, c6()) == pr.map_values(m));
    lemma_sum_of_ext(pr, |r: Row| t(m(r)), f);
    lemma_proj_prod(db);
    let a = proj_all(db.tables[0], ca());
    let b = proj_all(db.tables[3], seq![0nat, 4nat]);
    lemma_sum_of_product(a, b, t);
    assert(b == pa_rows(cp));
    let g = |x: Row| sum_of(b, |y: Row| t(x + y));
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] g(a[i]) == inner(cp, k, lo, hi)(a[i]) by {}
    lemma_sum_of_ext(a, g, inner(cp, k, lo, hi));
    lemma_sum_of_perm(a, li_rows(fp), inner(cp, k, lo, hi));
    assert(li_rows(fp).subrange(0, n_li(fp)) =~= li_rows(fp));
}

/// A sum of ones is the length.
pub proof fn lemma_sum_ones(rows: Seq<Row>, f: spec_fn(Row) -> int)
    requires forall|i: int| 0 <= i < rows.len() ==> f(#[trigger] rows[i]) == 1,
    ensures sum_of(rows, f) == rows.len(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let d = rows.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies f(#[trigger] d[i]) == 1 by {
            assert(d[i] == rows[i]);
        }
        lemma_sum_ones(d, f);
    }
}

/// The number of kept rows is the count accumulator.
pub proof fn lemma_kept_count(sv: StoresView, db: Database, lo: int, hi: int)
    requires bound_db(sv, db),
    ensures kept_of(db, lo, hi).len() == tot(sv.facts, sv.custpart, 0, lo, hi, 0, n_li(sv.facts)),
{
    let ks = kept_of(db, lo, hi);
    lemma_keep_members(prod_of(db), qx(lo, hi));
    assert forall|i: int| 0 <= i < ks.len() implies tx(0, lo, hi)(#[trigger] ks[i]) == 1 by {
        assert(qx(lo, hi)(ks[i]));
    }
    lemma_sum_ones(ks, tx(0, lo, hi));
    lemma_sum_chain(sv, db, 0, lo, hi);
}

} // verus!
