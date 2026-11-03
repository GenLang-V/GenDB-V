//! From the per-slot totals to the fixed claim. The answer lists, in slot order, the row `code, count, sum` of
//! every parameter slot with a qualifying row (`slot_rows`): such a slot is the first one holding its text
//! (`lemma_slot_rep`), so the slots' texts are distinct and are exactly the non-empty groups of the GROUP BY
//! (`lemma_rep_keys_groups`), and each row is that group's output row (`lemma_slot_rows_map`). Sorted by the code,
//! this is an allowed output of the statement (`lemma_answer`) for every database bound to the stored parts
//! (`lemma_outcome`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::limits::*;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::query::query_spec_at;
use crate::link::query::*;
use crate::bridge::order::{lemma_sort_rows, all_keys_ok, keys_ok, key_ok};
use crate::bridge::typing::val_family;
use crate::agent::common::rsum::*;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::ast::*;
use crate::agent::body::*;

verus! {

/// The answer's row of slot `g`: its text, count and balance sum (scale 2).
pub open spec fn slot_row(sv: StoresView, ps: Seq<Literal>, g: int) -> Row {
    seq![Val::Text(pt(ps, g)), Val::Int(gcnt(sv, ps, g)), Val::Num { coeff: gsm(sv, ps, g), scale: 2 }]
}

/// The group keys of the slots `< n` with a qualifying row, in slot order.
pub open spec fn rep_keys(sv: StoresView, ps: Seq<Literal>, n: int) -> Seq<Row>
    decreases n,
{
    if n <= 0 {
        Seq::empty()
    } else if gcnt(sv, ps, n - 1) > 0 {
        rep_keys(sv, ps, n - 1).push(seq![Val::Text(pt(ps, n - 1))])
    } else {
        rep_keys(sv, ps, n - 1)
    }
}

/// The answer rows of the slots `< n` with a qualifying row, in slot order.
pub open spec fn slot_rows(sv: StoresView, ps: Seq<Literal>, n: int) -> Seq<Row>
    decreases n,
{
    if n <= 0 {
        Seq::empty()
    } else if gcnt(sv, ps, n - 1) > 0 {
        slot_rows(sv, ps, n - 1).push(slot_row(sv, ps, n - 1))
    } else {
        slot_rows(sv, ps, n - 1)
    }
}

/// A non-zero range sum has a non-zero term.
#[verifier::spinoff_prover]
pub proof fn lemma_range_sum_witness(lo: int, hi: int, f: spec_fn(int) -> int) -> (r: int)
    requires range_sum(lo, hi, f) != 0,
    ensures lo <= r < hi, f(r) != 0,
    decreases hi - lo,
{
    if hi <= lo {
        assert(false);
        lo
    } else if f(hi - 1) != 0 {
        hi - 1
    } else {
        lemma_range_sum_witness(lo, hi - 1, f)
    }
}

/// A slot with a qualifying row holds the text of that row's code and is the first slot holding it.
#[verifier::spinoff_prover]
pub proof fn lemma_slot_rep(sv: StoresView, ps: Seq<Literal>, g: int) -> (i: int)
    requires gcnt(sv, ps, g) > 0,
    ensures
        0 <= i < n_c(sv), qual(sv, ps, i), grp(ps, code_of(sv, i)) == g, code_of(sv, i) == pt(ps, g),
        0 <= g < 7, grp(ps, pt(ps, g)) == g,
{
    let i = lemma_range_sum_witness(0, n_c(sv) as int, gcnt_term(sv, ps, g));
    lemma_grp(ps, code_of(sv, i));
    i
}

/// Without an AVG population no row qualifies: every slot is empty.
#[verifier::spinoff_prover]
pub proof fn lemma_no_population(sv: StoresView, ps: Seq<Literal>, g: int)
    requires avg_n(sv, ps) == 0,
    ensures gcnt(sv, ps, g) == 0,
{
    lemma_range_sum_bounds(0, n_c(sv) as int, gcnt_term(sv, ps, g), 0, 0);
}

/// The keys of the slots `< n`: distinct, and exactly the texts of the non-empty slots `< n`.
#[verifier::spinoff_prover]
proof fn lemma_rep_keys(sv: StoresView, ps: Seq<Literal>, n: int)
    requires 0 <= n <= 7,
    ensures
        rep_keys(sv, ps, n).no_duplicates(),
        forall|k: Row| #[trigger] rep_keys(sv, ps, n).contains(k)
            <==> exists|g: int| 0 <= g < n && gcnt(sv, ps, g) > 0 && k == seq![Val::Text(#[trigger] pt(ps, g))],
    decreases n,
{
    if n > 0 {
        lemma_rep_keys(sv, ps, n - 1);
        let s = rep_keys(sv, ps, n - 1);
        if gcnt(sv, ps, n - 1) > 0 {
            let x = seq![Val::Text(pt(ps, n - 1))];
            let _i = lemma_slot_rep(sv, ps, n - 1);
            // the new key is not among the earlier ones: an earlier non-empty slot with the same text would be the
            // first slot holding it
            assert(!s.contains(x)) by {
                if s.contains(x) {
                    let g = choose|g: int| 0 <= g < n - 1 && gcnt(sv, ps, g) > 0 && x == seq![Val::Text(#[trigger] pt(ps, g))];
                    let _j = lemma_slot_rep(sv, ps, g);
                    assert(x[0] == Val::Text(pt(ps, g)));
                    assert(pt(ps, g) == pt(ps, n - 1));
                }
            }
            assert forall|a: int, b: int| 0 <= a < b < s.push(x).len() implies s.push(x)[a] != s.push(x)[b] by {
                if b == s.len() {
                    assert(s.contains(s[a]));
                }
            }
            assert forall|k: Row| #[trigger] s.push(x).contains(k)
                <==> exists|g: int| 0 <= g < n && gcnt(sv, ps, g) > 0 && k == seq![Val::Text(#[trigger] pt(ps, g))] by {
                if s.push(x).contains(k) {
                    let m = choose|m: int| 0 <= m < s.push(x).len() && s.push(x)[m] == k;
                    if m < s.len() {
                        assert(s.contains(k));
                    }
                }
                if exists|g: int| 0 <= g < n && gcnt(sv, ps, g) > 0 && k == seq![Val::Text(#[trigger] pt(ps, g))] {
                    let g = choose|g: int| 0 <= g < n && gcnt(sv, ps, g) > 0 && k == seq![Val::Text(#[trigger] pt(ps, g))];
                    if g < n - 1 {
                        assert(s.contains(k));
                        let m = choose|m: int| 0 <= m < s.len() && s[m] == k;
                        assert(s.push(x)[m] == k);
                    } else {
                        assert(s.push(x)[s.len() as int] == k);
                    }
                }
            }
        } else {
            assert forall|k: Row| #[trigger] s.contains(k)
                <==> exists|g: int| 0 <= g < n && gcnt(sv, ps, g) > 0 && k == seq![Val::Text(#[trigger] pt(ps, g))] by {
                if exists|g: int| 0 <= g < n && gcnt(sv, ps, g) > 0 && k == seq![Val::Text(#[trigger] pt(ps, g))] {
                    let g = choose|g: int| 0 <= g < n && gcnt(sv, ps, g) > 0 && k == seq![Val::Text(#[trigger] pt(ps, g))];
                    assert(g < n - 1);
                }
            }
        }
    }
}

/// The slot keys are exactly the non-empty groups of the GROUP BY.
#[verifier::spinoff_prover]
proof fn lemma_rep_keys_groups(sv: StoresView, ps: Seq<Literal>)
    requires model_ok(sv),
    ensures
        rep_keys(sv, ps, 7).no_duplicates(),
        forall|k: Row| #[trigger] rep_keys(sv, ps, 7).contains(k) <==> gcount(qspec(), grows(sv, ps), k) > 0,
{
    lemma_rep_keys(sv, ps, 7);
    assert forall|k: Row| #[trigger] rep_keys(sv, ps, 7).contains(k) <==> gcount(qspec(), grows(sv, ps), k) > 0 by {
        if rep_keys(sv, ps, 7).contains(k) {
            let g = choose|g: int| 0 <= g < 7 && gcnt(sv, ps, g) > 0 && k == seq![Val::Text(#[trigger] pt(ps, g))];
            let _i = lemma_slot_rep(sv, ps, g);
            lemma_group_totals(sv, ps, g);
        }
        if gcount(qspec(), grows(sv, ps), k) > 0 {
            lemma_group_witness(sv, ps, k);
            let i = choose|i: int| 0 <= i < n_c(sv) && qual(sv, ps, i) && k == seq![Val::Text(#[trigger] code_of(sv, i))];
            lemma_group_nonempty(sv, ps, i);
            let g = grp(ps, code_of(sv, i));
            assert(k == seq![Val::Text(pt(ps, g))]);
        }
    }
}

/// The output row of a non-empty slot's group is the slot's answer row.
#[verifier::spinoff_prover]
proof fn lemma_slot_out_row(sv: StoresView, ps: Seq<Literal>, g: int)
    requires model_ok(sv), gcnt(sv, ps, g) > 0,
    ensures out_row(qspec(), grows(sv, ps), seq![Val::Text(pt(ps, g))]) == slot_row(sv, ps, g),
{
    let _i = lemma_slot_rep(sv, ps, g);
    lemma_group_totals(sv, ps, g);
    let q = qspec();
    let xs = grows(sv, ps);
    let k = seq![Val::Text(pt(ps, g))];
    let full = full_row(q, xs, k);
    assert(agg_outs(q, xs, k) =~= seq![Val::Int(gcnt(sv, ps, g)), Val::Num { coeff: gsm(sv, ps, g), scale: 2 }]);
    assert(full =~= slot_row(sv, ps, g));
    lemma_select_identity(full, q.outs);
}

/// The answer rows are the output rows of the slot keys.
#[verifier::spinoff_prover]
proof fn lemma_slot_rows_map(sv: StoresView, ps: Seq<Literal>, n: int)
    requires model_ok(sv), 0 <= n <= 7,
    ensures slot_rows(sv, ps, n) == rep_keys(sv, ps, n).map_values(|k: Row| out_row(qspec(), grows(sv, ps), k)),
    decreases n,
{
    let f = |k: Row| out_row(qspec(), grows(sv, ps), k);
    if n > 0 {
        lemma_slot_rows_map(sv, ps, n - 1);
        if gcnt(sv, ps, n - 1) > 0 {
            lemma_slot_out_row(sv, ps, n - 1);
            let s = rep_keys(sv, ps, n - 1);
            let x = seq![Val::Text(pt(ps, n - 1))];
            assert(s.push(x).map_values(f) =~= s.map_values(f).push(f(x)));
        }
    } else {
        assert(rep_keys(sv, ps, n).map_values(f) =~= Seq::<Row>::empty());
    }
}

/// The answer rows have a text code first.
#[verifier::spinoff_prover]
proof fn lemma_slot_rows_keys(sv: StoresView, ps: Seq<Literal>, n: int)
    requires 0 <= n <= 7,
    ensures all_keys_ok(order_keys(), seq![3int], slot_rows(sv, ps, n)),
    decreases n,
{
    if n > 0 {
        lemma_slot_rows_keys(sv, ps, n - 1);
        let s = slot_rows(sv, ps, n - 1);
        if gcnt(sv, ps, n - 1) > 0 {
            let r = slot_row(sv, ps, n - 1);
            assert(key_ok(order_keys()[0], 3, r));
            assert(keys_ok(order_keys(), seq![3int], r));
            assert forall|i: int| 0 <= i < s.push(r).len() implies keys_ok(order_keys(), seq![3int], #[trigger] s.push(r)[i]) by {
                if i < s.len() {
                    assert(s.push(r)[i] == s[i]);
                }
            }
        }
    }
}

/// The sorted answer rows are an allowed output of the normal form.
#[verifier::spinoff_prover]
pub proof fn lemma_answer(sv: StoresView, ps: Seq<Literal>, out: Seq<Row>)
    requires model_ok(sv), out == sort_rows(order_keys(), slot_rows(sv, ps, 7)),
    ensures result_ok(qspec(), order_keys(), 0, None, grows(sv, ps), out),
{
    let q = qspec();
    let xs = grows(sv, ps);
    let u = slot_rows(sv, ps, 7);
    let f = |k: Row| out_row(q, xs, k);
    lemma_rep_keys_groups(sv, ps);
    lemma_gkeys(q, xs);
    lemma_nodup_same_multiset(rep_keys(sv, ps, 7), gkeys(q, xs));
    lemma_map_multiset(rep_keys(sv, ps, 7), gkeys(q, xs), f);
    lemma_slot_rows_map(sv, ps, 7);
    assert(result_rows(q, xs) == gkeys(q, xs).map_values(f));
    lemma_slot_rows_keys(sv, ps, 7);
    lemma_sort_rows(order_keys(), seq![3int], u);
    lemma_result_ok_from(q, order_keys(), 0, None, xs, out);
    lemma_slice_all(out);
}

/// An allowed output of the normal form is an allowed output of the statement on every bound database.
#[verifier::spinoff_prover]
pub proof fn lemma_outcome(sv: StoresView, ps: Seq<Literal>, out: Seq<Row>)
    requires model_ok(sv), sizes_ok(sv), ps_ok(ps), result_ok(qspec(), order_keys(), 0, None, grows(sv, ps), out),
    ensures forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)) by {
        lemma_model(sv, db);
        lemma_body(db, sv, ps);
        lemma_query_shape(ps);
        let oq = query_spec_at(ps);
        assert(denote_body(db, oq) == Ok::<Relation, SqlError>(result_rows(qspec(), grows(sv, ps))));
        lemma_ordered_link(db, oq, qspec(), grows(sv, ps), out);
    }
}

} // verus!
