// AUTHOR MODULE ROOT (crate::agent): `SELECT COUNT(*) AS n FROM readings WHERE value > $1`.
//
// Plan: read the whole `value` column of the flat storage `flat_readings` (one extent of `n` i64 values, row `i` at
// position `i`) and count, in one serial pass, the values greater than `$1`. The answer is one row `[count]`, or the
// SQL error 22003 when the count exceeds int8 (only possible beyond 2^63 rows). No structure is built.
//
// Proof: the loop keeps `count == gcount(count_spec(p), rels[0][0..i], [])` (the normal form's count over the
// first `i` stored rows); `normal_form::lemma_body` turns the final count into the statement's meaning for every
// database bound to the stored parts.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::order::denote_body;
use crate::exec::value::EVal;
use crate::query::query_spec_at;
use crate::gendb_params::Params;
use crate::gendb_entry::{Answer, answer_meets, bound_db, stores_ready};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::stores::Stores;
use crate::link::query::{gcount, hit, lemma_range_step, lemma_empty, lemma_full_range, view_rows};
use crate::link::outcome::{lemma_outcome_rows, lemma_outcome_err};
use crate::stores::flat_readings::interface::{represents, lemma_represents_determines, read_value, stored_rows};
use crate::stores::flat_readings::declaration::stored_relations;

pub mod normal_form;

use normal_form::{count_spec, binding, lemma_body};

verus! {

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        crate::query::param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    // The stored relations: those of any bound database (the parts determine them).
    let ghost db0 = choose|db: Database| bound_db(old(stores)@, db);
    let ghost rels = stored_relations(db0);
    let ghost parts = old(stores)@.flat_readings;
    let p = params.p0;
    let ghost g = count_spec(p as int);
    let ghost xs = rels[0];

    let n = stored_rows(&stores.flat_readings, Ghost(rels));
    let values = read_value(&mut stores.flat_readings, 0, n, Ghost(rels));

    // Count the stored rows `i < n` with `values[i] > p`.
    let mut count: usize = 0;
    let mut i: usize = 0;
    proof { lemma_empty(g, xs, 0, Seq::<Val>::empty(), 0); }
    while i < n
        invariant
            g == count_spec(p as int),
            n == xs.len(),
            values@.len() == n,
            forall|j: int| 0 <= j < n ==> #[trigger] xs[0 + j][0] == (Val::Int(values@[j] as int)),
            i <= n,
            count <= i,
            count == gcount(g, xs.subrange(0, i as int), Seq::<Val>::empty()),
        decreases n - i,
    {
        proof {
            lemma_range_step(g, xs, 0, i as int, Seq::<Val>::empty(), 0);
            // Row `i` qualifies exactly when its value exceeds `p` (the key is always the empty row).
            assert(xs[0 + i as int][0] == Val::Int(values@[i as int] as int));
            assert(hit(g, xs[i as int], Seq::<Val>::empty()) == (values@[i as int] > p)) by {
                assert(0 + i as int == i as int);
                assert(normal_form::above(xs[i as int], p as int) == (values@[i as int] > p));
            }
        }
        if values[i] > p {
            count = count + 1;
        }
        i = i + 1;
    }
    proof { lemma_full_range(xs); }

    let c = count as u64;
    let r = if c > 0x7fff_ffff_ffff_ffffu64 {
        Ok(Answer::SqlError(SqlError::NumericValueOutOfRange))
    } else {
        let out = vec![vec![EVal::Int(c as i64)]];
        proof {
            assert(view_rows(out@) =~= seq![seq![Val::Int(count as int)]]) by {
                assert(out@[0]@.map_values(|v: EVal| v@) =~= seq![Val::Int(count as int)]);
            }
        }
        Ok(Answer::Rows(out))
    };

    // The answer meets the claim for every bound database.
    proof {
        assert(params@ == binding(p as int));
        assert forall|db: Database| #[trigger] bound_db(old(stores)@, db) implies
            crate::gendb_entry::outcome_ok(db, query_spec_at(params@), r) by {
            lemma_represents_determines(parts, stored_relations(db), rels);
            lemma_body(db, parts, rels, p as int);
            let oq = query_spec_at(params@);
            assert(denote_body(db, oq) == crate::spec::eval::eval_query(db, Seq::empty(), oq.body));
            if c > 0x7fff_ffff_ffff_ffffu64 {
                lemma_outcome_err(db, oq, SqlError::NumericValueOutOfRange);
            } else {
                lemma_outcome_rows(db, oq, seq![seq![Val::Int(count as int)]]);
            }
        }
    }
    r
}

} // verus!
