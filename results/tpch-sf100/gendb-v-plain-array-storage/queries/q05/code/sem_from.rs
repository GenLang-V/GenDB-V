//! The FROM relation `customer x orders x lineitem x supplier x nation x region` (left-deep product, `from6`): its
//! rows are exactly the `row6` of index tuples in range (`lemma_from6_contains`), the values the query reads at
//! each position (`lemma_row6`), its evaluation (`lemma_eval_from6`) and, every table having a primary key, its
//! duplicate-freedom (`lemma_from6_nodup`).
//!
//! Index tuples are written `(i, j, c, d, e, f)`: customer row `i`, orders row `j`, lineitem row `c`, supplier row
//! `d`, nation row `e`, region row `f`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::source_check::date32_val;
use crate::agent::model::*;
use crate::agent::sem_ast::*;
use crate::agent::common::relations::*;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_region::interface as ri;

verus! {

/// A row of the FROM: customer `i`, orders `j`, lineitem `c`, supplier `d`, nation `e`, region `f`.
pub open spec fn row6(sv: StoresView, i: int, j: int, c: int, d: int, e: int, f: int) -> Row {
    c_rows(sv)[i] + o_rows(sv)[j] + l_rows(sv)[c] + s_rows(sv)[d] + n_rows(sv)[e] + r_rows(sv)[f]
}

pub open spec fn in6(sv: StoresView, i: int, j: int, c: int, d: int, e: int, f: int) -> bool {
    &&& 0 <= i < nc(sv)
    &&& 0 <= j < no(sv)
    &&& 0 <= c < nl(sv)
    &&& 0 <= d < ns(sv)
    &&& 0 <= e < nn(sv)
    &&& 0 <= f < nr(sv)
}

/// Partial products of the FROM, left to right.
pub open spec fn from2(sv: StoresView) -> Seq<Row> { product_rows(c_rows(sv), o_rows(sv)) }
pub open spec fn from3(sv: StoresView) -> Seq<Row> { product_rows(from2(sv), l_rows(sv)) }
pub open spec fn from4(sv: StoresView) -> Seq<Row> { product_rows(from3(sv), s_rows(sv)) }
pub open spec fn from5(sv: StoresView) -> Seq<Row> { product_rows(from4(sv), n_rows(sv)) }

/// The FROM relation.
pub open spec fn from6(sv: StoresView) -> Seq<Row> { product_rows(from5(sv), r_rows(sv)) }

// ------------------------------------------------------------------------------------------ rows

/// The values of a FROM row that the query reads.
pub proof fn lemma_row6(sv: StoresView, i: int, j: int, c: int, d: int, e: int, f: int)
    requires stores_wf(sv), in6(sv, i, j, c, d, e, f),
    ensures ({
        let x = row6(sv, i, j, c, d, e, f);
        &&& x.len() == 47
        &&& x[0] == Val::Int(c_ck(sv)[i] as int)
        &&& x[3] == Val::Int(c_nk(sv)[i] as int)
        &&& x[8] == Val::Int(o_ok(sv)[j] as int)
        &&& x[9] == Val::Int(o_ck(sv)[j] as int)
        &&& x[12] == date32_val(o_date(sv)[j])
        &&& x[17] == Val::Int(l_ok(sv)[c] as int)
        &&& x[19] == Val::Int(l_sk(sv)[c] as int)
        &&& x[20] == Val::Int(l_ln(sv)[c] as int)
        &&& x[22] == (Val::Num { coeff: l_ext(sv)[c] as int, scale: 2 })
        &&& x[23] == (Val::Num { coeff: l_disc(sv)[c] as int, scale: 2 })
        &&& x[33] == Val::Int(s_sk(sv)[d] as int)
        &&& x[36] == Val::Int(s_nk(sv)[d] as int)
        &&& x[40] == Val::Int(n_nk(sv)[e] as int)
        &&& x[41] == Val::Text(n_name(sv, e))
        &&& x[42] == Val::Int(n_rk(sv)[e] as int)
        &&& x[44] == Val::Int(r_rk(sv)[f] as int)
        &&& x[45] == Val::Text(r_name(sv, f))
    }),
{
    let cr = c_rows(sv)[i];
    let or = o_rows(sv)[j];
    let lr = l_rows(sv)[c];
    let sr = s_rows(sv)[d];
    let nr_ = n_rows(sv)[e];
    let rr = r_rows(sv)[f];
    assert(cr == ci::row_at(sv.flat_customer, i));
    assert(or == oi::row_at(sv.flat_orders, j));
    assert(lr == li::row_at(sv.flat_lineitem, c));
    assert(sr == si::row_at(sv.flat_supplier, d));
    assert(nr_ == ni::row_at(sv.flat_nation, e));
    assert(rr == ri::row_at(sv.flat_region, f));
    assert(cr.len() == 8 && or.len() == 9 && lr.len() == 16 && sr.len() == 7 && nr_.len() == 4 && rr.len() == 3);
    let x = row6(sv, i, j, c, d, e, f);
    assert(x[0] == cr[0] && x[3] == cr[3]);
    assert(x[8] == or[0] && x[9] == or[1] && x[12] == or[4]);
    assert(x[17] == lr[0] && x[19] == lr[2] && x[20] == lr[3] && x[22] == lr[5] && x[23] == lr[6]);
    assert(x[33] == sr[0] && x[36] == sr[3]);
    assert(x[40] == nr_[0] && x[41] == nr_[1] && x[42] == nr_[2]);
    assert(x[44] == rr[0] && x[45] == rr[1]);
}

/// Rows of a product of relations with rows of widths `wa` and `wb` have width `wa + wb`.
proof fn lemma_product_width(a: Seq<Row>, b: Seq<Row>, wa: nat, wb: nat)
    requires
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == wa,
        forall|i: int| 0 <= i < b.len() ==> (#[trigger] b[i]).len() == wb,
    ensures forall|i: int| 0 <= i < product_rows(a, b).len() ==> (#[trigger] product_rows(a, b)[i]).len() == wa + wb,
{
    crate::bridge::relation::lemma_product_rows_elems(a, b);
    let p = product_rows(a, b);
    assert forall|i: int| 0 <= i < p.len() implies (#[trigger] p[i]).len() == wa + wb by {
        assert(crate::bridge::relation::is_concat(p[i], a, b));
        let (x, y) = choose|x: int, y: int| 0 <= x < a.len() && 0 <= y < b.len() && p[i] == #[trigger] a[x] + #[trigger] b[y];
    }
}

/// The rows of the FROM are exactly the `row6` of index tuples in range.
pub proof fn lemma_from6_contains(sv: StoresView, x: Row)
    requires stores_wf(sv),
    ensures from6(sv).contains(x) <==> exists|i: int, j: int, c: int, d: int, e: int, f: int|
        in6(sv, i, j, c, d, e, f) && x == #[trigger] row6(sv, i, j, c, d, e, f),
{
    let (cr, or, lr, sr, nr_, rr) = (c_rows(sv), o_rows(sv), l_rows(sv), s_rows(sv), n_rows(sv), r_rows(sv));
    let l2 = from2(sv);
    let l3 = from3(sv);
    let l4 = from4(sv);
    let l5 = from5(sv);
    lemma_product_contains(l5, rr, x);
    if from6(sv).contains(x) {
        let (k5, f) = choose|k: int, f: int| 0 <= k < l5.len() && 0 <= f < rr.len() && x == #[trigger] l5[k] + #[trigger] rr[f];
        assert(l5.contains(l5[k5]));
        lemma_product_contains(l4, nr_, l5[k5]);
        let (k4, e) = choose|k: int, e: int| 0 <= k < l4.len() && 0 <= e < nr_.len() && l5[k5] == #[trigger] l4[k] + #[trigger] nr_[e];
        assert(l4.contains(l4[k4]));
        lemma_product_contains(l3, sr, l4[k4]);
        let (k3, d) = choose|k: int, d: int| 0 <= k < l3.len() && 0 <= d < sr.len() && l4[k4] == #[trigger] l3[k] + #[trigger] sr[d];
        assert(l3.contains(l3[k3]));
        lemma_product_contains(l2, lr, l3[k3]);
        let (k2, c) = choose|k: int, c: int| 0 <= k < l2.len() && 0 <= c < lr.len() && l3[k3] == #[trigger] l2[k] + #[trigger] lr[c];
        assert(l2.contains(l2[k2]));
        lemma_product_contains(cr, or, l2[k2]);
        let (i, j) = choose|i: int, j: int| 0 <= i < cr.len() && 0 <= j < or.len() && l2[k2] == #[trigger] cr[i] + #[trigger] or[j];
        assert(x == row6(sv, i, j, c, d, e, f));
    }
    if exists|i: int, j: int, c: int, d: int, e: int, f: int| in6(sv, i, j, c, d, e, f) && x == #[trigger] row6(sv, i, j, c, d, e, f) {
        let (i, j, c, d, e, f) = choose|i: int, j: int, c: int, d: int, e: int, f: int|
            in6(sv, i, j, c, d, e, f) && x == #[trigger] row6(sv, i, j, c, d, e, f);
        let x2 = cr[i] + or[j];
        let x3 = x2 + lr[c];
        let x4 = x3 + sr[d];
        let x5 = x4 + nr_[e];
        lemma_product_contains(cr, or, x2);
        lemma_product_contains(l2, lr, x3);
        lemma_product_contains(l3, sr, x4);
        lemma_product_contains(l4, nr_, x5);
        let k2 = choose|k: int| 0 <= k < l2.len() && l2[k] == x2;
        assert(l3.contains(x3)) by { assert(x3 == l2[k2] + lr[c]); }
        let k3 = choose|k: int| 0 <= k < l3.len() && l3[k] == x3;
        assert(l4.contains(x4)) by { assert(x4 == l3[k3] + sr[d]); }
        let k4 = choose|k: int| 0 <= k < l4.len() && l4[k] == x4;
        assert(l5.contains(x5)) by { assert(x5 == l4[k4] + nr_[e]); }
        let k5 = choose|k: int| 0 <= k < l5.len() && l5[k] == x5;
        assert(x == l5[k5] + rr[f]);
    }
}

/// `FROM customer, orders, lineitem, supplier, nation, region` evaluates to `from6`.
pub proof fn lemma_eval_from6(db: Database, sv: StoresView)
    requires tables_of(sv, db),
    ensures eval_query(db, Seq::empty(), from_q()) == Ok::<Relation, SqlError>(from6(sv)),
{
    let ctx = Seq::<Val>::empty();
    assert(eval_query(db, ctx, Query::Table(2)) == Ok::<Relation, SqlError>(c_rows(sv)));
    assert(eval_query(db, ctx, Query::Table(1)) == Ok::<Relation, SqlError>(o_rows(sv)));
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(l_rows(sv)));
    assert(eval_query(db, ctx, Query::Table(5)) == Ok::<Relation, SqlError>(s_rows(sv)));
    assert(eval_query(db, ctx, Query::Table(6)) == Ok::<Relation, SqlError>(n_rows(sv)));
    assert(eval_query(db, ctx, Query::Table(7)) == Ok::<Relation, SqlError>(r_rows(sv)));
    let q2 = prod(Query::Table(2), Query::Table(1));
    let q3 = prod(q2, Query::Table(0));
    let q4 = prod(q3, Query::Table(5));
    let q5 = prod(q4, Query::Table(6));
    assert(eval_query(db, ctx, q2) == Ok::<Relation, SqlError>(from2(sv)));
    assert(eval_query(db, ctx, q3) == Ok::<Relation, SqlError>(from3(sv)));
    assert(eval_query(db, ctx, q4) == Ok::<Relation, SqlError>(from4(sv)));
    assert(eval_query(db, ctx, q5) == Ok::<Relation, SqlError>(from5(sv)));
}

/// An empty table makes the FROM empty; otherwise the FROM has a row.
pub proof fn lemma_from6_len(sv: StoresView)
    ensures from6(sv).len() == nc(sv) * no(sv) * nl(sv) * ns(sv) * nn(sv) * nr(sv),
{
    crate::bridge::relation::lemma_product_rows_elems(c_rows(sv), o_rows(sv));
    crate::bridge::relation::lemma_product_rows_elems(from2(sv), l_rows(sv));
    crate::bridge::relation::lemma_product_rows_elems(from3(sv), s_rows(sv));
    crate::bridge::relation::lemma_product_rows_elems(from4(sv), n_rows(sv));
    crate::bridge::relation::lemma_product_rows_elems(from5(sv), r_rows(sv));
}

// ------------------------------------------------------------------------------------------ duplicate-free rows

/// Rows of a table with unique keys in column 0 are pairwise different.
proof fn lemma_rows_nodup_by_key(rows: Seq<Row>, keys: Seq<i64>)
    requires
        rows.len() == keys.len(),
        keys_unique(keys),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() > 0 && rows[i][0] == Val::Int(keys[i] as int),
    ensures rows.no_duplicates(),
{
    assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && i != j implies rows[i] != rows[j] by {
        assert(rows[i][0] == Val::Int(keys[i] as int) && rows[j][0] == Val::Int(keys[j] as int));
        assert(keys[i] != keys[j]);
    }
}

proof fn lemma_tables_nodup(sv: StoresView)
    requires stores_wf(sv), keys_ok(sv),
    ensures
        c_rows(sv).no_duplicates(),
        o_rows(sv).no_duplicates(),
        l_rows(sv).no_duplicates(),
        s_rows(sv).no_duplicates(),
        n_rows(sv).no_duplicates(),
        r_rows(sv).no_duplicates(),
{
    assert forall|i: int| 0 <= i < c_rows(sv).len() implies (#[trigger] c_rows(sv)[i]).len() > 0 && c_rows(sv)[i][0] == Val::Int(c_ck(sv)[i] as int) by {
        assert(c_rows(sv)[i] == ci::row_at(sv.flat_customer, i));
    }
    lemma_rows_nodup_by_key(c_rows(sv), c_ck(sv));
    assert forall|i: int| 0 <= i < o_rows(sv).len() implies (#[trigger] o_rows(sv)[i]).len() > 0 && o_rows(sv)[i][0] == Val::Int(o_ok(sv)[i] as int) by {
        assert(o_rows(sv)[i] == oi::row_at(sv.flat_orders, i));
    }
    lemma_rows_nodup_by_key(o_rows(sv), o_ok(sv));
    assert forall|i: int| 0 <= i < s_rows(sv).len() implies (#[trigger] s_rows(sv)[i]).len() > 0 && s_rows(sv)[i][0] == Val::Int(s_sk(sv)[i] as int) by {
        assert(s_rows(sv)[i] == si::row_at(sv.flat_supplier, i));
    }
    lemma_rows_nodup_by_key(s_rows(sv), s_sk(sv));
    assert forall|i: int| 0 <= i < n_rows(sv).len() implies (#[trigger] n_rows(sv)[i]).len() > 0 && n_rows(sv)[i][0] == Val::Int(n_nk(sv)[i] as int) by {
        assert(n_rows(sv)[i] == ni::row_at(sv.flat_nation, i));
    }
    lemma_rows_nodup_by_key(n_rows(sv), n_nk(sv));
    assert forall|i: int| 0 <= i < r_rows(sv).len() implies (#[trigger] r_rows(sv)[i]).len() > 0 && r_rows(sv)[i][0] == Val::Int(r_rk(sv)[i] as int) by {
        assert(r_rows(sv)[i] == ri::row_at(sv.flat_region, i));
    }
    lemma_rows_nodup_by_key(r_rows(sv), r_rk(sv));
    let q = l_rows(sv);
    assert forall|i: int, j: int| 0 <= i < q.len() && 0 <= j < q.len() && i != j implies q[i] != q[j] by {
        lemma_l_row(sv, i);
        lemma_l_row(sv, j);
        assert(q[i] == li::row_at(sv.flat_lineitem, i));
        assert(q[j] == li::row_at(sv.flat_lineitem, j));
        assert(l_ok(sv)[i] != l_ok(sv)[j] || l_ln(sv)[i] != l_ln(sv)[j]);
    }
}

/// The rows of the FROM are pairwise different (every table has a primary key).
pub proof fn lemma_from6_nodup(sv: StoresView)
    requires stores_wf(sv), keys_ok(sv),
    ensures from6(sv).no_duplicates(),
{
    let (cr, or, lr, sr, nr_, rr) = (c_rows(sv), o_rows(sv), l_rows(sv), s_rows(sv), n_rows(sv), r_rows(sv));
    lemma_tables_nodup(sv);
    assert forall|i: int| 0 <= i < cr.len() implies (#[trigger] cr[i]).len() == 8 by { assert(cr[i] == ci::row_at(sv.flat_customer, i)); }
    assert forall|i: int| 0 <= i < or.len() implies (#[trigger] or[i]).len() == 9 by { assert(or[i] == oi::row_at(sv.flat_orders, i)); }
    assert forall|i: int| 0 <= i < lr.len() implies (#[trigger] lr[i]).len() == 16 by { lemma_l_row(sv, i); assert(lr[i] == li::row_at(sv.flat_lineitem, i)); }
    assert forall|i: int| 0 <= i < sr.len() implies (#[trigger] sr[i]).len() == 7 by { assert(sr[i] == si::row_at(sv.flat_supplier, i)); }
    assert forall|i: int| 0 <= i < nr_.len() implies (#[trigger] nr_[i]).len() == 4 by { assert(nr_[i] == ni::row_at(sv.flat_nation, i)); }
    lemma_product_nodup(cr, or, 8);
    lemma_product_width(cr, or, 8, 9);
    lemma_product_nodup(from2(sv), lr, 17);
    lemma_product_width(from2(sv), lr, 17, 16);
    lemma_product_nodup(from3(sv), sr, 33);
    lemma_product_width(from3(sv), sr, 33, 7);
    lemma_product_nodup(from4(sv), nr_, 40);
    lemma_product_width(from4(sv), nr_, 40, 4);
    lemma_product_nodup(from5(sv), rr, 44);
}

} // verus!
