//! Example: ORDER BY with LIMIT answered by a top-k selection over rows in another order (O5).
//!
//! `SELECT * FROM outer ORDER BY qty DESC LIMIT k`. The plan scans the outer rows in any order (for example a
//! storage's reordered copy: rows bag-equal to the table) and keeps the `k` largest quantities, sorted, without
//! sorting the rest. Proof route: the sort key is a numeric of every row (`lemma_example_rows`, family 1), then
//! `topk::lemma_topk_ok`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::bridge::order::{key_ok, keys_ok, all_keys_ok, key_val};
use crate::bridge::typing::val_family;
use crate::engine_link::bag::bag_eq;
use crate::engine_link::topk::*;
use crate::engine_pins::schema::*;

verus! {

/// `SELECT * FROM outer ORDER BY qty DESC LIMIT k`.
pub open spec fn top_qty(k: nat) -> OrderedQuery {
    OrderedQuery {
        body: Query::Table(0),
        keys: seq![OrderKey { col: 2, desc: true, nulls_first: false }],
        limit: Some(k),
        offset: 0,
    }
}

/// Rows bag-equal to the outer table, of which `t` is a top-`k` selection, answer the statement with `t`.
pub proof fn example_top_k(db: Database, k: nat, rows: Seq<Row>, t: Seq<Row>, rest: Seq<Row>)
    requires
        example_db(db),
        rows.to_multiset() == db.tables[0].to_multiset(),
        topk_of(top_qty(k).keys, rows, t, rest, k),
    ensures ordered_ok(db, top_qty(k), Ok::<Relation, SqlError>(t)),
{
    lemma_example_rows(db);
    let oq = top_qty(k);
    let body = db.tables[0];
    assert(denote_body(db, oq) == Ok::<Relation, SqlError>(body));
    let fams = seq![1int];
    assert(all_keys_ok(oq.keys, fams, body)) by {
        assert forall|i: int| 0 <= i < body.len() implies keys_ok(oq.keys, fams, #[trigger] body[i]) by {
            assert(body[i][2] is Num);
            assert(key_val(oq.keys[0], body[i]) == body[i][2]);
            assert(key_ok(oq.keys[0], fams[0], body[i]));
        }
    }
    assert(bag_eq(Ok::<Relation, SqlError>(rows), denote_body(db, oq)));
    assert(front_len(oq, rows.len()) == k);
    lemma_topk_ok(db, oq, Ok::<Relation, SqlError>(rows), t, rest, fams);
    assert(slice_rows(t, 0, Some(k)) =~= t);
}

} // verus!
