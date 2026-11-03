//! Top level: sort and top-k over a bag-equal result give an allowed output (engine toolkit, obligation O5; nothing
//! here names a query, a table or a column).
//!
//! `spec::order::ordered_ok` allows any sorted permutation of the body's rows, then OFFSET and LIMIT (ties in any
//! order, any tie choice at the LIMIT boundary). A plan that produced rows bag-equal to the body (`bag::bag_eq`, O1)
//! may then:
//! - sort them all (`bag::lemma_bag_eq_ordered`, `link::outcome::lemma_outcome_sorted`), or
//! - keep only the first `OFFSET + LIMIT` of a sorted order without sorting the rest (`topk_of`,
//!   `lemma_topk_ok`): a sorted front `t` and the other rows `rest`, every front row not after any other row.
//!
//! The proof sorts the rest only in the proof (`spec::order::sort_rows`, `bridge::order::lemma_sort_rows`), which
//! needs every body row's key values to be of the key's family (`all_keys_ok`); `lemma_body_keys_ok` gives the
//! families for a well-typed statement on a well-formed database.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::typing::*;
use crate::bridge::typing::{row_typed, val_has_family, lemma_query_family};
use crate::bridge::order::{key_ok, keys_ok, all_keys_ok, key_families, lemma_keys_in_range, lemma_sort_rows};
use crate::engine_link::bag::{bag_eq, lemma_bag_contains, lemma_concat_bag, lemma_bag_eq_ordered};

verus! {

/// The number of leading rows of the sorted order a statement outputs from (OFFSET + LIMIT; all rows without LIMIT).
pub open spec fn front_len(oq: OrderedQuery, n: nat) -> nat {
    match oq.limit {
        Some(l) => oq.offset + l,
        None => n,
    }
}

/// `t` is a top-`k` selection of `rows` with remainder `rest`: together they are `rows` (as a bag), `t` has the
/// first `min(k, |rows|)` rows of a sorted order, sorted, and no front row is after any remaining row.
pub open spec fn topk_of(keys: Seq<OrderKey>, rows: Seq<Row>, t: Seq<Row>, rest: Seq<Row>, k: nat) -> bool {
    &&& (t + rest).to_multiset() == rows.to_multiset()
    &&& t.len() == if k <= rows.len() { k } else { rows.len() }
    &&& sorted_by(keys, t)
    &&& forall|i: int, j: int| 0 <= i < t.len() && 0 <= j < rest.len() ==> keys_cmp(keys, #[trigger] t[i], #[trigger] rest[j]) <= 0
}

/// The families of the ORDER BY keys hold for every body row of a well-typed statement on a well-formed database.
pub proof fn lemma_body_keys_ok(db: Database, oq: OrderedQuery) -> (fams: Seq<int>)
    requires db_wf(db), wf_ordered(db.schema, oq),
    ensures denote_body(db, oq) matches Ok(rows) ==> all_keys_ok(oq.keys, fams, rows),
{
    let tys = type_query(db.schema, Seq::empty(), oq.body)->0;
    let fams = key_families(oq.keys, tys);
    if let Ok(rows) = denote_body(db, oq) {
        assert(row_typed(Seq::empty(), Seq::empty()));
        lemma_query_family(db, Seq::empty(), Seq::empty(), oq.body);
        assert forall|i: int| 0 <= i < rows.len() implies keys_ok(oq.keys, fams, #[trigger] rows[i]) by {
            assert(row_typed(rows[i], tys));
            assert forall|j: int| 0 <= j < oq.keys.len() implies #[trigger] key_ok(oq.keys[j], fams[j], rows[i]) by {
                lemma_keys_in_range(oq.keys, tys.len(), j);
                let c = oq.keys[j].col as int;
                assert(val_has_family(rows[i][c], tys[c].ty));
            }
        }
    }
    fams
}

/// O5, top-k: rows bag-equal to the body, of which `t` is a top-(OFFSET + LIMIT) selection, give the allowed output
/// `slice_rows(t, offset, limit)`; an error is the body's error. With an empty `rest` this is the full sort.
pub proof fn lemma_topk_ok(db: Database, oq: OrderedQuery, x: Result<Relation, SqlError>, t: Seq<Row>, rest: Seq<Row>, fams: Seq<int>)
    requires
        bag_eq(x, denote_body(db, oq)),
        denote_body(db, oq) matches Ok(body) ==> all_keys_ok(oq.keys, fams, body),
        x matches Ok(rows) ==> topk_of(oq.keys, rows, t, rest, front_len(oq, rows.len())),
    ensures
        match x {
            Err(e) => ordered_ok(db, oq, Err::<Relation, SqlError>(e)),
            Ok(_) => ordered_ok(db, oq, Ok::<Relation, SqlError>(slice_rows(t, oq.offset, oq.limit))),
        },
{
    if let Ok(rows) = x {
        let keys = oq.keys;
        let body = denote_body(db, oq)->Ok_0;
        // every remaining row is a body row, so its key values have the keys' families
        lemma_concat_bag(t, rest);
        assert(all_keys_ok(keys, fams, rest)) by {
            assert forall|j: int| 0 <= j < rest.len() implies keys_ok(keys, fams, #[trigger] rest[j]) by {
                let tr = t + rest;
                assert(tr[t.len() + j] == rest[j]);
                let b = lemma_bag_contains(body, tr, t.len() + j);
            }
        }
        let sr = sort_rows(keys, rest);
        lemma_sort_rows(keys, fams, rest);
        let p = t + sr;
        // a permutation of the rows
        lemma_concat_bag(t, sr);
        assert(p.to_multiset() == rows.to_multiset());
        // sorted: within the front, within the sorted rest, and across (every front row is not after any rest row)
        assert(sorted_by(keys, p)) by {
            assert forall|i: int, j: int| 0 <= i < j < p.len() implies keys_cmp(keys, #[trigger] p[i], #[trigger] p[j]) <= 0 by {
                if j < t.len() {
                    assert(p[i] == t[i] && p[j] == t[j]);
                } else if i >= t.len() {
                    assert(p[i] == sr[i - t.len()] && p[j] == sr[j - t.len()]);
                } else {
                    let l = lemma_bag_contains(rest, sr, j - t.len());
                    assert(p[i] == t[i] && p[j] == rest[l]);
                }
            }
        }
        // the slice of `p` is the slice of the front
        let n = rows.len();
        assert(p.len() == n) by {
            (t + rest).to_multiset_ensures();
            rows.to_multiset_ensures();
            sr.to_multiset_ensures();
            rest.to_multiset_ensures();
        }
        assert(slice_rows(p, oq.offset, oq.limit) == slice_rows(t, oq.offset, oq.limit)) by {
            if t.len() == n {
                assert(rest.len() == 0);
                assert(sr.len() == 0) by {
                    sr.to_multiset_ensures();
                    rest.to_multiset_ensures();
                }
                assert(p =~= t);
            } else {
                assert(oq.limit is Some);
                assert(slice_rows(p, oq.offset, oq.limit) =~= slice_rows(t, oq.offset, oq.limit));
            }
        }
        lemma_bag_eq_ordered(db, oq, x, p);
    } else {
        lemma_bag_eq_ordered(db, oq, x, t);
    }
}

} // verus!
