//! The filtered product `lineitem x part` and its sums.
//!
//! For a database of the schema, the FROM product evaluates to every row of `product_rows(lineitem, part)`; the
//! WHERE condition keeps the rows whose query values satisfy `terms::wq` (`lemma_eval_filter_q`), or errs with
//! 22003 on a non-empty product when some `$q + 10` leaves int4 (`lemma_eval_filter_err`). A sum of an accumulator's
//! terms over the kept rows is the stored total `terms::tot` over every stored part row (`lemma_sum_chain`): the
//! terms vanish off the condition, the projected product is the product of the projected tables
//! (`link::join::lemma_proj_product`), summed right-major (part rows outside, `lemma_sum_of_product_swap`); the
//! projected part rows are the stored part rows and the projected lineitem rows a permutation of the stored ones.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::product_rows;
use crate::link::query::{proj, proj_all};
use crate::link::join::*;
use crate::link::source::lemma_proj_all_index;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::query::param_domain;
use super::model::*;
use super::terms::*;
use super::sqlrow::*;
use super::bind::*;

verus! {

/// The FROM product of a database.
pub open spec fn prod_of(db: Database) -> Seq<Row> {
    product_rows(db.tables[0], db.tables[3])
}

/// The WHERE condition on product rows.
pub open spec fn qx(ps: Seq<Literal>) -> spec_fn(Row) -> bool {
    |x: Row| wq(ps, zx(x))
}

/// The rows of the product that satisfy the WHERE condition.
pub open spec fn kept_of(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    keep(prod_of(db), qx(ps))
}

/// Accumulator `k`'s term on product rows.
pub open spec fn tx(ps: Seq<Literal>, k: int) -> spec_fn(Row) -> int {
    |x: Row| term(ps, k)(zx(x))
}

/// A product row of a typed lineitem row and a typed part row is typed.
pub proof fn lemma_xrow_typed(l: Row, p: Row)
    requires lrow_typed(l), prow_typed(p),
    ensures xrow_typed(l + p),
{
    let x = l + p;
    assert(x[1] == l[1] && x[4] == l[4] && x[5] == l[5] && x[6] == l[6] && x[13] == l[13] && x[14] == l[14]);
    assert(x[16] == p[0] && x[19] == p[3] && x[21] == p[5] && x[22] == p[6]);
}

/// Every row of the product is typed.
pub proof fn lemma_prod_typed(db: Database)
    requires rows_typed(db),
    ensures forall|i: int| 0 <= i < prod_of(db).len() ==> xrow_typed(#[trigger] prod_of(db)[i]),
{
    let (l, p) = (db.tables[0], db.tables[3]);
    let pr = prod_of(db);
    lemma_product_index(l, p);
    assert forall|i: int| 0 <= i < pr.len() implies xrow_typed(#[trigger] pr[i]) by {
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
        lemma_xrow_typed(l[a], p[b]);
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

/// The filtered product, every `$q + 10` inside int4: the rows satisfying the condition.
pub proof fn lemma_eval_filter_q(db: Database, ps: Seq<Literal>)
    requires
        rows_typed(db),
        param_domain(ps),
        !ovf(ps, 0), !ovf(ps, 1), !ovf(ps, 2),
    ensures
        eval_query(db, Seq::empty(), filter_q(ps)) == Ok::<Relation, SqlError>(kept_of(db, ps)),
{
    let pr = prod_of(db);
    lemma_eval_product_q(db);
    lemma_prod_typed(db);
    assert forall|i: int| 0 <= i < pr.len() && (|x: Row| true)(#[trigger] pr[i]) implies
        eval_pred(db, pr[i], pred_q(ps)) == Ok::<Truth, SqlError>(truth_of(qx(ps)(pr[i]))) by {
        lemma_row_pred(db, pr[i], ps);
    }
    lemma_eval_filter(db, product_q(), pr, |x: Row| true, pred_q(ps), qx(ps), qx(ps));
}

/// The filtered product, some `$q + 10` outside int4, on a non-empty product: the error 22003.
pub proof fn lemma_eval_filter_err(db: Database, ps: Seq<Literal>)
    requires
        rows_typed(db),
        param_domain(ps),
        ovf(ps, 0) || ovf(ps, 1) || ovf(ps, 2),
        prod_of(db).len() > 0,
    ensures
        eval_query(db, Seq::empty(), filter_q(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    let pr = prod_of(db);
    let ctx = Seq::<Val>::empty();
    let e = SqlError::NumericValueOutOfRange;
    lemma_eval_product_q(db);
    lemma_keep_all(pr, |x: Row| true);
    lemma_prod_typed(db);
    assert forall|i: int| 0 <= i < pr.len() implies #[trigger] eval_pred(db, ctx + pr[i], pred_q(ps)) == Err::<Truth, SqlError>(e) by {
        assert(ctx + pr[i] =~= pr[i]);
        lemma_row_pred_err(db, pr[i], ps);
    }
    crate::link::capacity::lemma_filter_err(db, ctx, pred_q(ps), Box::new(product_q()), pr, e, 0);
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
    ensures proj_all(prod_of(db), c10()) == product_rows(proj_all(db.tables[0], lcols()), proj_all(db.tables[3], pcols())),
{
    let (l, p) = (db.tables[0], db.tables[3]);
    assert forall|i: int| 0 <= i < l.len() implies (#[trigger] l[i]).len() == 16 by {
        assert(lrow_typed(l[i]));
    }
    assert forall|i: int| 0 <= i < p.len() implies (#[trigger] p[i]).len() == 9 by {
        assert(prow_typed(p[i]));
    }
    assert(lcols() + shift(pcols(), 16) =~= c10());
    lemma_proj_product(l, p, lcols(), pcols(), 16, 9);
}

/// A sum of an accumulator's terms over the kept rows is the stored total over every part row.
pub proof fn lemma_sum_chain(sv: StoresView, db: Database, ps: Seq<Literal>, k: int)
    requires bound_db(sv, db),
    ensures
        sum_of(kept_of(db, ps), tx(ps, k)) == tot(sv.facts, sv.custpart, ps, k, 0, n_pa(sv.custpart)),
{
    let (fp, cp) = (sv.facts, sv.custpart);
    let pr = prod_of(db);
    let f = tx(ps, k);
    let t = term(ps, k);
    lemma_rows_typed(db);
    lemma_li_link(sv, db);
    lemma_pa_link(sv, db);
    // the terms vanish off the condition
    assert forall|i: int| 0 <= i < pr.len() && !qx(ps)(#[trigger] pr[i]) implies f(pr[i]) == 0 by {}
    lemma_sum_of_keep(pr, qx(ps), f);
    // the sum over the projected product
    let m = |r: Row| proj(r, c10());
    lemma_sum_of_map(pr, m, t);
    assert(proj_all(pr, c10()) == pr.map_values(m));
    lemma_sum_of_ext(pr, |r: Row| t(m(r)), f);
    lemma_proj_prod(db);
    let a = proj_all(db.tables[0], lcols());
    let b = proj_all(db.tables[3], pcols());
    lemma_sum_of_product_swap(a, b, t);
    assert(b == pa_rows(cp));
    let g = |z: Row| sum_of(a, |y: Row| t(y + z));
    assert forall|i: int| 0 <= i < b.len() implies #[trigger] g(b[i]) == pin(fp, ps, k)(b[i]) by {
        let z = b[i];
        lemma_sum_of_ext(a, |y: Row| t(y + z), jt(ps, k, z));
        lemma_sum_of_perm(a, li_rows(fp), jt(ps, k, z));
    }
    lemma_sum_of_ext(b, g, pin(fp, ps, k));
    assert(pa_rows(cp).subrange(0, n_pa(cp)) =~= pa_rows(cp));
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
pub proof fn lemma_kept_count(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db),
    ensures kept_of(db, ps).len() == tot(sv.facts, sv.custpart, ps, 0, 0, n_pa(sv.custpart)),
{
    let ks = kept_of(db, ps);
    lemma_keep_members(prod_of(db), qx(ps));
    assert forall|i: int| 0 <= i < ks.len() implies tx(ps, 0)(#[trigger] ks[i]) == 1 by {
        assert(qx(ps)(ks[i]));
    }
    lemma_sum_ones(ks, tx(ps, 0));
    lemma_sum_chain(sv, db, ps, 0);
}

} // verus!
