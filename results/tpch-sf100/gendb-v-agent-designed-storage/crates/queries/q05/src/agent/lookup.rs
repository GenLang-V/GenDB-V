//! Key lookups in the nested counts of `q5spec`: every dimension relation (orders, customer, supplier, nation,
//! region) has a unique column 0 under its declared PRIMARY KEY (`lemma_pk_unique`), so a sum over its rows of a
//! term that vanishes off one key is the term of the one row holding that key, or 0 when no row holds it.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::scalar::*;
use crate::spec::equality::*;
use crate::spec::constraints::*;
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::link::query::*;
use crate::link::join::*;
use crate::agent::q5spec::*;
use crate::agent::sqlrow::*;
use crate::agent::common::sums::*;

verus! {

/// Column 0 identifies the row.
pub open spec fn keys_unique(rows: Seq<Row>) -> bool {
    forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && #[trigger] rows[i][0] == #[trigger] rows[j][0] ==> i == j
}

/// The declared PRIMARY KEY of orders, customer, supplier, nation and region is their column 0.
proof fn lemma_declared_pk(t: int)
    requires t == 1 || t == 2 || t == 5 || t == 6 || t == 7,
    ensures
        declared_schema().len() == 8,
        declared_schema()[t].constraints.len() >= 1,
        declared_schema()[t].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }),
{
    assert(declared_schema().len() == 8) by (compute);
    if t == 1 {
        assert(declared_schema()[1].constraints.len() >= 1) by (compute);
        assert(declared_schema()[1].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true })) by (compute);
    } else if t == 2 {
        assert(declared_schema()[2].constraints.len() >= 1) by (compute);
        assert(declared_schema()[2].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true })) by (compute);
    } else if t == 5 {
        assert(declared_schema()[5].constraints.len() >= 1) by (compute);
        assert(declared_schema()[5].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true })) by (compute);
    } else if t == 6 {
        assert(declared_schema()[6].constraints.len() >= 1) by (compute);
        assert(declared_schema()[6].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true })) by (compute);
    } else {
        assert(declared_schema()[7].constraints.len() >= 1) by (compute);
        assert(declared_schema()[7].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true })) by (compute);
    }
}

/// Column 0 of a dimension table's stored projection is unique.
pub proof fn lemma_pk_unique(db: Database, t: int, cols: Seq<nat>)
    requires
        db.schema == schema_spec(), db_wf(db), constraints_hold(declared_db(db)),
        t == 1 || t == 2 || t == 5 || t == 6 || t == 7,
        cols.len() >= 1, cols[0] == 0,
    ensures keys_unique(proj_all(db.tables[t], cols)),
{
    lemma_declared_pk(t);
    lemma_schema_cols();
    assert(schema_spec().len() == 8) by (compute);
    let ddb = declared_db(db);
    let rows = proj_all(db.tables[t], cols);
    assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && #[trigger] rows[i][0] == #[trigger] rows[j][0]
        implies i == j by {
        let (ri, rj) = (db.tables[t][i], db.tables[t][j]);
        assert(rows[i][0] == ri[0] && rows[j][0] == rj[0]);
        assert(row_in_table(ri, schema_spec()[t]));
        assert(value_in_column(ri[0], schema_spec()[t].columns[0]));
        let (ki, kj) = (key_of(ri, seq![0nat]), key_of(rj, seq![0nat]));
        assert(ki =~= seq![ri[0]]);
        assert(kj =~= seq![rj[0]]);
        assert(ri[0] is Int);
        assert(compare(ri[0], rj[0]) == Some(0int));
        assert(val_not_distinct(ki[0], kj[0]));
        assert(row_not_distinct(ki, kj));
        lemma_primary_key_identifies(ddb, t, 0, seq![0nat], true, i, j);
    }
}

// ------------------------------------------------------------------------------------------- generic lookups

/// A term that vanishes on every row whose key (column 0) differs from `key`, over rows with unique keys and a
/// row `i` holding `key`: the sum is row `i`'s term.
pub proof fn lemma_key_sum(rows: Seq<Row>, f: spec_fn(Row) -> int, key: Val, i: int)
    requires
        keys_unique(rows),
        0 <= i < rows.len(),
        rows[i][0] == key,
        forall|j: int| 0 <= j < rows.len() && #[trigger] rows[j][0] != key ==> f(rows[j]) == 0,
    ensures sum_of(rows, f) == f(rows[i]),
{
    assert forall|j: int| 0 <= j < rows.len() && j != i implies f(#[trigger] rows[j]) == 0 by {
        if rows[j][0] == key {
            assert(rows[j][0] == rows[i][0]);
        }
    }
    lemma_sum_single(rows, f, i);
}

/// A term that vanishes on every row: the sum is 0.
pub proof fn lemma_zero_sum(rows: Seq<Row>, f: spec_fn(Row) -> int)
    requires forall|j: int| 0 <= j < rows.len() ==> f(#[trigger] rows[j]) == 0,
    ensures sum_of(rows, f) == 0,
{
    lemma_sum_of_zero(rows, f);
}

// ------------------------------------------------------------------------------------------- the nested counts

/// At most one region row joins a nation row.
pub proof fn lemma_r_cnt_le1(rr: Seq<Row>, n: Row, name: Seq<u8>)
    requires keys_unique(rr),
    ensures 0 <= r_cnt(rr, n, name) <= 1,
{
    let f = |r: Row| r_term(n, name, r);
    if exists|i: int| 0 <= i < rr.len() && rr[i][0] == n[2] {
        let i = choose|i: int| 0 <= i < rr.len() && rr[i][0] == n[2];
        assert forall|j: int| 0 <= j < rr.len() && #[trigger] rr[j][0] != n[2] implies f(rr[j]) == 0 by {}
        lemma_key_sum(rr, f, n[2], i);
    } else {
        assert forall|j: int| 0 <= j < rr.len() implies f(#[trigger] rr[j]) == 0 by {}
        lemma_zero_sum(rr, f);
    }
}

/// The nation row holding a supplier's nation key.
pub proof fn lemma_n_cnt_found(rs: Rels, s: Row, k: Row, name: Seq<u8>, ni: int)
    requires keys_unique(rs.n), 0 <= ni < rs.n.len(), rs.n[ni][0] == s[3],
    ensures n_cnt(rs, s, k, name) == n_term(rs, s, k, name, rs.n[ni]),
{
    let f = |n: Row| n_term(rs, s, k, name, n);
    assert forall|j: int| 0 <= j < rs.n.len() && #[trigger] rs.n[j][0] != s[3] implies f(rs.n[j]) == 0 by {}
    lemma_key_sum(rs.n, f, s[3], ni);
}

/// No nation row with a supplier's nation key joins a region row named `$1`.
pub proof fn lemma_n_cnt_zero(rs: Rels, s: Row, k: Row, name: Seq<u8>)
    requires forall|i: int| 0 <= i < rs.n.len() && #[trigger] rs.n[i][0] == s[3] ==> r_cnt(rs.r, rs.n[i], name) == 0,
    ensures n_cnt(rs, s, k, name) == 0,
{
    let f = |n: Row| n_term(rs, s, k, name, n);
    assert forall|j: int| 0 <= j < rs.n.len() implies f(#[trigger] rs.n[j]) == 0 by {
        if rs.n[j][0] == s[3] {
            assert(r_cnt(rs.r, rs.n[j], name) == 0);
        }
    }
    lemma_zero_sum(rs.n, f);
}

/// The supplier row of a lineitem row.
pub proof fn lemma_s_cnt_found(rs: Rels, c: Row, l: Row, k: Row, name: Seq<u8>, si: int)
    requires keys_unique(rs.s), 0 <= si < rs.s.len(), rs.s[si][0] == l[2],
    ensures s_cnt(rs, c, l, k, name) == s_term(rs, c, l, k, name, rs.s[si]),
{
    let f = |s: Row| s_term(rs, c, l, k, name, s);
    assert forall|j: int| 0 <= j < rs.s.len() && #[trigger] rs.s[j][0] != l[2] implies f(rs.s[j]) == 0 by {}
    lemma_key_sum(rs.s, f, l[2], si);
}

/// No supplier row holds a lineitem row's supplier key.
pub proof fn lemma_s_cnt_none(rs: Rels, c: Row, l: Row, k: Row, name: Seq<u8>)
    requires forall|i: int| 0 <= i < rs.s.len() ==> #[trigger] rs.s[i][0] != l[2],
    ensures s_cnt(rs, c, l, k, name) == 0,
{
    let f = |s: Row| s_term(rs, c, l, k, name, s);
    assert forall|j: int| 0 <= j < rs.s.len() implies f(#[trigger] rs.s[j]) == 0 by {}
    lemma_zero_sum(rs.s, f);
}

/// Without a qualifying nation for the customer's nation key, no supplier contributes.
pub proof fn lemma_s_cnt_zero_nation(rs: Rels, c: Row, l: Row, k: Row, name: Seq<u8>)
    requires forall|i: int| 0 <= i < rs.n.len() && #[trigger] rs.n[i][0] == c[3] ==> r_cnt(rs.r, rs.n[i], name) == 0,
    ensures s_cnt(rs, c, l, k, name) == 0,
{
    let f = |s: Row| s_term(rs, c, l, k, name, s);
    assert forall|j: int| 0 <= j < rs.s.len() implies f(#[trigger] rs.s[j]) == 0 by {
        let s = rs.s[j];
        if l[2] == s[0] && c[3] == s[3] {
            lemma_n_cnt_zero(rs, s, k, name);
        }
    }
    lemma_zero_sum(rs.s, f);
}

/// The customer row of an order.
pub proof fn lemma_c_cnt_found(rs: Rels, o: Row, l: Row, k: Row, name: Seq<u8>, ci: int)
    requires keys_unique(rs.c), 0 <= ci < rs.c.len(), rs.c[ci][0] == o[1],
    ensures c_cnt(rs, o, l, k, name) == s_cnt(rs, rs.c[ci], l, k, name),
{
    let f = |c: Row| c_term(rs, o, l, k, name, c);
    assert forall|j: int| 0 <= j < rs.c.len() && #[trigger] rs.c[j][0] != o[1] implies f(rs.c[j]) == 0 by {}
    lemma_key_sum(rs.c, f, o[1], ci);
}

/// No customer row holds an order's customer key.
pub proof fn lemma_c_cnt_none(rs: Rels, o: Row, l: Row, k: Row, name: Seq<u8>)
    requires forall|i: int| 0 <= i < rs.c.len() ==> #[trigger] rs.c[i][0] != o[1],
    ensures c_cnt(rs, o, l, k, name) == 0,
{
    let f = |c: Row| c_term(rs, o, l, k, name, c);
    assert forall|j: int| 0 <= j < rs.c.len() implies f(#[trigger] rs.c[j]) == 0 by {}
    lemma_zero_sum(rs.c, f);
}

/// The order row of a lineitem row.
pub proof fn lemma_mult_order(rs: Rels, prm: Prm, k: Row, l: Row, oi: int)
    requires keys_unique(rs.o), 0 <= oi < rs.o.len(), rs.o[oi][0] == l[0],
    ensures line_mult(rs, prm, k, l) == if date_ok(rs.o[oi], prm) { c_cnt(rs, rs.o[oi], l, k, prm.name) } else { 0int },
{
    reveal(line_mult);
    let f = |o: Row| o_term(rs, prm, k, l, o);
    assert forall|j: int| 0 <= j < rs.o.len() && #[trigger] rs.o[j][0] != l[0] implies f(rs.o[j]) == 0 by {}
    lemma_key_sum(rs.o, f, l[0], oi);
}

/// No order row holds a lineitem row's order key.
pub proof fn lemma_mult_no_order(rs: Rels, prm: Prm, k: Row, l: Row)
    requires forall|i: int| 0 <= i < rs.o.len() ==> #[trigger] rs.o[i][0] != l[0],
    ensures line_mult(rs, prm, k, l) == 0,
{
    reveal(line_mult);
    let f = |o: Row| o_term(rs, prm, k, l, o);
    assert forall|j: int| 0 <= j < rs.o.len() implies f(#[trigger] rs.o[j]) == 0 by {}
    lemma_zero_sum(rs.o, f);
}

/// The order of a lineitem row exists but lies outside the date window.
pub proof fn lemma_mult_out_of_window(rs: Rels, prm: Prm, k: Row, l: Row, oi: int)
    requires keys_unique(rs.o), 0 <= oi < rs.o.len(), rs.o[oi][0] == l[0], !date_ok(rs.o[oi], prm),
    ensures line_mult(rs, prm, k, l) == 0,
{
    lemma_mult_order(rs, prm, k, l, oi);
}

} // verus!
