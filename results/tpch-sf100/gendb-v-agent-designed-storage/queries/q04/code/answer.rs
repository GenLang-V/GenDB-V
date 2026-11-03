//! The Q4 answer from per-dictionary-entry counts: one row `[o_orderpriority, COUNT]` per entry with a nonzero count,
//! in dictionary order (the dictionary is sorted bytewise, which is the ORDER BY order of text), is an allowed
//! output of the statement on every database bound to the parts (`lemma_rows_answer`); a count beyond int8 is the
//! statement's error 22003 (`lemma_count_overflow`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::{Answer, answer_meets, bound_db, outcome_ok};
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::runtime::QueryError;
use crate::exec::value::{EVal, view_row};
use crate::link::query::view_rows;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::scalar::compare;
use crate::spec::order::*;
use crate::spec::limits::int8_max;
use crate::spec::text::lex_cmp;
use crate::link::query::{gcount, QuerySpec};
use crate::query::{query_spec_at, param_typed};
use crate::stores::facts::interface::common::colfmt::*;
use super::model::*;
use super::sql::*;
use super::bind::*;

verus! {

/// The counts `totals` are the normal form's group counts of every dictionary entry.
pub open spec fn totals_ok(db: Database, ps: Seq<Literal>, hi: int, doffs: Seq<u64>, dbytes: Seq<u8>, totals: Seq<usize>) -> bool {
    &&& totals.len() == doffs.len() - 1
    &&& forall|d: int| 0 <= d < totals.len() ==>
            #[trigger] totals[d] as int == gcount(qspec(lrel_of(db), lo_of(ps), hi), orel_of(db), key_d(doffs, dbytes, d))
}

/// The entries `ds` are exactly the dictionary entries with a nonzero count, in increasing order.
pub open spec fn entries_ok(totals: Seq<usize>, ds: Seq<int>) -> bool {
    &&& forall|i: int| 0 <= i < ds.len() ==> 0 <= #[trigger] ds[i] < totals.len() && totals[ds[i]] > 0
    &&& forall|i: int, j: int| 0 <= i < j < ds.len() ==> #[trigger] ds[i] < #[trigger] ds[j]
    &&& forall|d: int| 0 <= d < totals.len() && #[trigger] totals[d] > 0 ==> ds.contains(d)
}

/// The output row of dictionary entry `d`.
pub open spec fn entry_row(doffs: Seq<u64>, dbytes: Seq<u8>, totals: Seq<usize>, d: int) -> Row {
    seq![Val::Text(text_of(doffs, dbytes, d)), Val::Int(totals[d] as int)]
}

proof fn lemma_sorted_out(doffs: Seq<u64>, dbytes: Seq<u8>, totals: Seq<usize>, ds: Seq<int>, out: Seq<Row>)
    requires
        dict_sorted(doffs, dbytes, doffs.len() - 1),
        totals.len() == doffs.len() - 1,
        entries_ok(totals, ds),
        out.len() == ds.len(),
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == entry_row(doffs, dbytes, totals, ds[i]),
    ensures sorted_by(order_keys(), out),
{
    let k = doffs.len() - 1;
    assert forall|i: int, j: int| 0 <= i < j < out.len() implies keys_cmp(order_keys(), #[trigger] out[i], #[trigger] out[j]) <= 0 by {
        let (a, b) = (text_of(doffs, dbytes, ds[i]), text_of(doffs, dbytes, ds[j]));
        lemma_dict_order(doffs, dbytes, k, ds[i], ds[j]);
        assert(out[i][0] == Val::Text(a) && out[j][0] == Val::Text(b));
        assert(compare(Val::Text(a), Val::Text(b)) == Some(lex_cmp(a, b)));
        let key = order_keys()[0];
        assert(key_cmp(key, out[i], out[j]) == lex_cmp(a, b));
        assert(keys_cmp(order_keys(), out[i], out[j]) == key_cmp(key, out[i], out[j]));
    }
}

/// The answer rows are an allowed output on database `db`.
pub proof fn lemma_rows_answer(db: Database, parts: Seq<PartView>, c: Cols, doffs: Seq<u64>, dbytes: Seq<u8>,
    ps: Seq<Literal>, hi: int, totals: Seq<usize>, ds: Seq<int>, out: Seq<Row>)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
        parts[p_odo()] == PartView::U64(doffs),
        parts[p_ody()] == PartView::U8(dbytes),
        param_typed(ps),
        db.tables[1].len() > 0 ==> hi_ok(lo_of(ps), hi),
        totals_ok(db, ps, hi, doffs, dbytes, totals),
        forall|d: int| 0 <= d < totals.len() ==> #[trigger] totals[d] <= int8_max(),
        entries_ok(totals, ds),
        out.len() == ds.len(),
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == entry_row(doffs, dbytes, totals, ds[i]),
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    let lo = lo_of(ps);
    let g = qspec(lrel_of(db), lo, hi);
    let xs = orel_of(db);
    let k = doffs.len() - 1;
    lemma_orders_cols(db, parts, c, doffs, dbytes);
    // Every group count fits int8: a non-empty group is some entry's group.
    assert forall|kr: Row| #[trigger] gcount(g, xs, kr) <= int8_max() by {
        if gcount(g, xs, kr) > 0 {
            lemma_keys_complete(db, parts, c, doffs, dbytes, lo, hi, kr);
            let d = choose|d: int| 0 <= d < k && kr == key_d(doffs, dbytes, d);
            assert(totals[d] as int == gcount(g, xs, key_d(doffs, dbytes, d)));
        }
    }
    lemma_db_ok(db, parts);
    lemma_body(db, ps, hi);
    let ks = ds.map_values(|d: int| key_d(doffs, dbytes, d));
    assert forall|i: int, j: int| 0 <= i < ks.len() && 0 <= j < ks.len() && i != j implies ks[i] != ks[j] by {
        if i < j {
            lemma_dict_distinct(doffs, dbytes, k, ds[i], ds[j]);
        } else {
            lemma_dict_distinct(doffs, dbytes, k, ds[j], ds[i]);
        }
        assert(ks[i][0] != ks[j][0]);
    }
    assert(ks.no_duplicates());
    assert forall|kr: Row| #[trigger] ks.contains(kr) <==> gcount(g, xs, kr) > 0 by {
        if ks.contains(kr) {
            let i = choose|i: int| 0 <= i < ks.len() && ks[i] == kr;
            assert(totals[ds[i]] as int == gcount(g, xs, key_d(doffs, dbytes, ds[i])));
        }
        if gcount(g, xs, kr) > 0 {
            lemma_keys_complete(db, parts, c, doffs, dbytes, lo, hi, kr);
            let d = choose|d: int| 0 <= d < k && kr == key_d(doffs, dbytes, d);
            assert(totals[d] as int == gcount(g, xs, key_d(doffs, dbytes, d)));
            assert(ds.contains(d));
            let i = choose|i: int| 0 <= i < ds.len() && ds[i] == d;
            assert(ks[i] == kr);
        }
    }
    assert forall|i: int| 0 <= i < ks.len() implies (#[trigger] ks[i]).len() == 1 by {}
    assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i] == group_row(g, xs, ks[i]) by {
        let d = ds[i];
        assert(totals[d] as int == gcount(g, xs, key_d(doffs, dbytes, d)));
        assert(out[i] =~= group_row(g, xs, ks[i]));
    }
    lemma_sorted_out(doffs, dbytes, totals, ds, out);
    lemma_answer(db, ps, hi, ks, out);
}

/// A count beyond int8 is the statement's error 22003 on database `db`.
pub proof fn lemma_count_overflow(db: Database, parts: Seq<PartView>, doffs: Seq<u64>, dbytes: Seq<u8>,
    ps: Seq<Literal>, hi: int, totals: Seq<usize>, d: int)
    requires
        bound(db, parts),
        param_typed(ps),
        db.tables[1].len() > 0 ==> hi_ok(lo_of(ps), hi),
        totals_ok(db, ps, hi, doffs, dbytes, totals),
        0 <= d < totals.len(),
        totals[d] > int8_max(),
    ensures
        ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)),
{
    lemma_db_ok(db, parts);
    lemma_body_count_err(db, ps, hi, key_d(doffs, dbytes, d));
}

// ------------------------------------------------------------------------------------------------ every database

/// The parts of storage facts inside storage li_ordruns (the parts every read uses).
pub open spec fn fparts(sv: StoresView) -> Seq<PartView> {
    crate::stores::li_ordruns::interface::facts_parts(sv.li_ordruns)
}

/// The entry's `bound_db` gives `bound` over facts' parts inside li_ordruns, and `bound2`.
pub proof fn lemma_bound(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures bound(db, fparts(sv)), bound2(db, sv.li_ordruns),
{
    lemma_bound2(db, sv.li_ordruns);
}

/// On non-empty orders, an error of `$1 + 3 months` answers every bound database.
pub proof fn lemma_meets_date_err(sv: StoresView, ps: Seq<Literal>, e: SqlError)
    requires
        param_typed(ps),
        parts_shape(fparts(sv)),
        u64s(fparts(sv)[p_ol()])[0] > 0,
        hi_value(lo_of(ps)) == Err::<int, SqlError>(e),
    ensures
        answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::SqlError(e))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(e))) by {
        lemma_bound(sv, db);
        lemma_parts_shape(db, fparts(sv));
        lemma_stored_positions(db);
        lemma_db_ok(db, fparts(sv));
        lemma_body_date_err(db, ps);
    }
}

/// The model's counts over every stored orders row are the group counts of every bound database.
pub proof fn lemma_meets_totals(sv: StoresView, c: Cols, doffs: Seq<u64>, dbytes: Seq<u8>, ps: Seq<Literal>, hi: int,
    totals: Seq<usize>)
    requires
        cols_from_parts(c, fparts(sv)),
        fparts(sv)[p_odo()] == PartView::U64(doffs),
        fparts(sv)[p_ody()] == PartView::U8(dbytes),
        totals.len() == doffs.len() - 1,
        forall|d: int| 0 <= d < totals.len() ==> #[trigger] totals[d] as int == count_raw(c, lo_of(ps), hi, d, 0, c.n_o as int),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> totals_ok(db, ps, hi, doffs, dbytes, totals),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies totals_ok(db, ps, hi, doffs, dbytes, totals) by {
        lemma_bound(sv, db);
        assert forall|d: int| 0 <= d < totals.len() implies #[trigger] totals[d] as int
            == gcount(qspec(lrel_of(db), lo_of(ps), hi), orel_of(db), key_d(doffs, dbytes, d)) by {
            lemma_count_gcount(db, fparts(sv), c, doffs, dbytes, lo_of(ps), hi, d);
        }
    }
}

/// A count beyond int8 answers every bound database with error 22003.
pub proof fn lemma_meets_overflow(sv: StoresView, doffs: Seq<u64>, dbytes: Seq<u8>, ps: Seq<Literal>, hi: int,
    totals: Seq<usize>, d: int)
    requires
        param_typed(ps),
        parts_shape(fparts(sv)),
        u64s(fparts(sv)[p_ol()])[0] > 0 ==> hi_ok(lo_of(ps), hi),
        forall|db: Database| #[trigger] bound_db(sv, db) ==> totals_ok(db, ps, hi, doffs, dbytes, totals),
        0 <= d < totals.len(),
        totals[d] > int8_max(),
    ensures
        answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))) by {
        lemma_bound(sv, db);
        lemma_parts_shape(db, fparts(sv));
        lemma_stored_positions(db);
        lemma_count_overflow(db, fparts(sv), doffs, dbytes, ps, hi, totals, d);
    }
}

/// The answer rows answer every bound database.
pub proof fn lemma_meets_rows(sv: StoresView, c: Cols, doffs: Seq<u64>, dbytes: Seq<u8>, ps: Seq<Literal>, hi: int,
    totals: Seq<usize>, ds: Seq<int>, rows: Vec<Vec<EVal>>)
    requires
        cols_from_parts(c, fparts(sv)),
        fparts(sv)[p_odo()] == PartView::U64(doffs),
        fparts(sv)[p_ody()] == PartView::U8(dbytes),
        param_typed(ps),
        u64s(fparts(sv)[p_ol()])[0] > 0 ==> hi_ok(lo_of(ps), hi),
        forall|db: Database| #[trigger] bound_db(sv, db) ==> totals_ok(db, ps, hi, doffs, dbytes, totals),
        forall|d: int| 0 <= d < totals.len() ==> #[trigger] totals[d] <= int8_max(),
        entries_ok(totals, ds),
        rows@.len() == ds.len(),
        forall|i: int| 0 <= i < rows@.len() ==> #[trigger] view_row(rows@[i]@) == entry_row(doffs, dbytes, totals, ds[i]),
    ensures
        answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Rows(rows))),
{
    crate::link::outcome::lemma_view_rows(rows@);
    let out = view_rows(rows@);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
        lemma_bound(sv, db);
        lemma_parts_shape(db, fparts(sv));
        lemma_stored_positions(db);
        lemma_rows_answer(db, fparts(sv), c, doffs, dbytes, ps, hi, totals, ds, out);
    }
}

/// `bound` includes `db_ok`.
pub proof fn lemma_db_ok(db: Database, parts: Seq<PartView>)
    requires bound(db, parts),
    ensures db_ok(db),
{
}

} // verus!
