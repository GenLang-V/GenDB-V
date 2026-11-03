//! Q0's answer from the per-code accumulators of the stored layout.
//!
//! For a group code `g`: `rr` rows, `rc` sub-runs (distinct filings) and `rv` exact line sum over all sub-runs. A
//! code is `selected` when its stmt is not NULL and it has rows; it is `code_ok` when its two counts fit int8 and
//! its AVG division is inside the executable domain; then its output row is `prow`. `lemma_group_result` gives the
//! GROUP BY's result and domain for the group of a selected code; `lemma_success`: when every selected code is
//! `code_ok`, the body's rows are the `prow` of the selected codes (as a multiset).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::limits::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::equality::distinct_rows;
use crate::spec::fns::div::*;
use crate::spec::typing::db_wf;
use crate::schema::schema_spec;
use crate::query::query_spec;
use crate::gendb_entry::layout::PartView;
use crate::exec::relational::domain::{fits_query, group_results, groups_fs, agg_value_results, agg_value_fs, fits_agg_row, fits_each, ok_before, lemma_each_capacity, lemma_agg_row};
use crate::bridge::collect::*;
use crate::link::query::{gkeys, lemma_gkeys, avg_of, lemma_nodup_same_multiset};
use crate::stores::pre::interface::*;
use crate::stores::pre::declaration::*;
use super::canon::*;
use super::store::*;
use super::runs::*;
use super::values::*;

verus! {

pub open spec fn rr(p: Seq<PartView>, g: int) -> int { run_rows(st_of(p), sg_of(p), g, 0, sub_count(p)) }
pub open spec fn rc(p: Seq<PartView>, g: int) -> int { run_count(sg_of(p), g, 0, sub_count(p)) }
pub open spec fn rv(p: Seq<PartView>, g: int) -> int { run_vals(st_of(p), sg_of(p), ln_of(p), g, 0, sub_count(p)) }

/// Code `g` is a group of the statement: stmt not NULL and at least one row.
pub open spec fn selected(p: Seq<PartView>, g: int) -> bool {
    0 <= g < group_count(p) && live_of(p, g) && rr(p, g) > 0
}

/// Code `g`'s aggregates are all values: both counts fit int8 and AVG's division is executable.
pub open spec fn code_ok(p: Seq<PartView>, g: int) -> bool {
    rr(p, g) <= int8_max() && rc(p, g) <= int8_max() && num_div_fits(rv(p, g), 0, rr(p, g), 0)
}

/// A count of code `g` leaves int8 (SQL error 22003, before its AVG).
pub open spec fn count_err(p: Seq<PartView>, g: int) -> bool {
    rr(p, g) > int8_max() || rc(p, g) > int8_max()
}

/// The output row of code `g`: stmt, rfile, COUNT(*), COUNT(DISTINCT adsh), AVG(line).
pub open spec fn prow(p: Seq<PartView>, g: int) -> Row {
    key_of(p, g) + seq![Val::Int(rr(p, g)), Val::Int(rc(p, g)), avg_of(rv(p, g), 0, rr(p, g) as nat)]
}

/// The database is one the parts are bound to (the parts of `pre` represent its stored relation).
pub open spec fn bound(p: Seq<PartView>, db: Database) -> bool {
    &&& db.schema == schema_spec()
    &&& db_wf(db)
    &&& represents(p, stored_relations(db))
}

pub open spec fn grs(db: Database) -> Seq<Result<Row, SqlError>> {
    group_results(q_aggs(), qk(db), qa(db))
}

pub open spec fn gfs(db: Database) -> Seq<bool> {
    groups_fs(q_aggs(), qk(db), qa(db))
}

/// The GROUP BY's groups are `gkeys`, one result and one domain predicate per group.
pub proof fn lemma_group_shape(p: Seq<PartView>, db: Database)
    requires bound(p, db),
    ensures
        grs(db).len() == gkeys(gq(), xs_of(db)).len(),
        gfs(db).len() == gkeys(gq(), xs_of(db)).len(),
        gkeys(gq(), xs_of(db)).no_duplicates(),
{
    lemma_table_typed(db);
    lemma_groups(xs_of(db));
    lemma_gkeys(gq(), xs_of(db));
}

/// The GROUP BY result and domain of the group at index `h`, the group of selected code `g`.
pub proof fn lemma_group_result(p: Seq<PartView>, db: Database, h: int, g: int)
    requires
        bound(p, db),
        0 <= h < gkeys(gq(), xs_of(db)).len(),
        selected(p, g),
        key_of(p, g) == gkeys(gq(), xs_of(db))[h],
    ensures
        code_ok(p, g) ==> grs(db)[h] == Ok::<Row, SqlError>(prow(p, g)) && gfs(db)[h],
        count_err(p, g) ==> grs(db)[h] == Err::<Row, SqlError>(SqlError::NumericValueOutOfRange),
        !code_ok(p, g) && !count_err(p, g) ==> !gfs(db)[h],
{
    let xs = xs_of(db);
    let k = key_of(p, g);
    lemma_table_typed(db);
    lemma_layout_facts(p);
    lemma_ys_perm(p, db);
    lemma_groups(xs);
    lemma_group_shape(p, db);
    assert(gkeys(gq(), xs).contains(k));
    lemma_group_of_code(p, db, g);
    let d = adsh_runs(p, g, sub_count(p));
    lemma_group_values(xs, k, d);
    let m = members_of(xs, k);
    let vr = agg_value_results(q_aggs(), m);
    let vf = agg_value_fs(q_aggs(), m);
    assert(distinct_rows(qk(db))[h] == k);
    assert(group_members(qk(db), qa(db), k) == m);
    lemma_agg_row(q_aggs(), m);
    assert(grs(db)[h] == match agg_row(q_aggs(), m) { Ok(a) => Ok(k + a), Err(e) => Err::<Row, SqlError>(e) });
    assert(gfs(db)[h] == fits_agg_row(q_aggs(), m));
    if code_ok(p, g) {
        let vals = seq![Val::Int(rr(p, g)), Val::Int(rc(p, g)), avg_of(rv(p, g), 0, rr(p, g) as nat)];
        assert forall|j: int| 0 <= j < vr.len() implies #[trigger] vr[j] == Ok::<Val, SqlError>(vals[j]) by {
            if j == 0 {} else if j == 1 {} else {}
        }
        lemma_collect_all(vr, vals);
        assert(k + vals =~= prow(p, g));
        assert(fits_each(vr, vf)) by {
            assert forall|j: int| 0 <= j < vf.len() && ok_before(vr, j) implies #[trigger] vf[j] by {
                if j == 0 {} else if j == 1 {} else {}
            }
        }
    }
    if rr(p, g) > int8_max() {
        lemma_collect_first_err(vr, 0);
    } else if rc(p, g) > int8_max() {
        assert forall|j: int| 0 <= j < 1 implies #[trigger] vr[j] is Ok by {}
        lemma_collect_first_err(vr, 1);
    } else if !code_ok(p, g) {
        assert(ok_before(vr, 2)) by {
            assert forall|j: int| 0 <= j < 2 implies #[trigger] vr[j] is Ok by { if j == 0 {} else {} }
        }
        lemma_each_capacity(vr, vf, 2);
    }
}

/// Every group of the GROUP BY is the group of a selected code.
pub proof fn lemma_group_code(p: Seq<PartView>, db: Database, h: int) -> (g: int)
    requires bound(p, db), 0 <= h < gkeys(gq(), xs_of(db)).len(),
    ensures selected(p, g), key_of(p, g) == gkeys(gq(), xs_of(db))[h],
{
    let k = gkeys(gq(), xs_of(db))[h];
    lemma_gkeys_codes(p, db, k);
    choose|g: int| 0 <= g < group_count(p) && live_of(p, g)
        && run_rows(st_of(p), sg_of(p), g, 0, sub_count(p)) > 0 && #[trigger] key_of(p, g) == k
}

/// The rows of a list of distinct selected codes have no duplicates.
proof fn lemma_prows_distinct(p: Seq<PartView>, codes: Seq<int>)
    requires
        pre_layout_ok(p),
        forall|i: int| 0 <= i < codes.len() ==> selected(p, #[trigger] codes[i]),
        forall|i: int, j: int| 0 <= i < j < codes.len() ==> #[trigger] codes[i] < #[trigger] codes[j],
    ensures codes.map_values(|g: int| prow(p, g)).no_duplicates(),
{
    let rows = codes.map_values(|g: int| prow(p, g));
    assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && i != j implies rows[i] != rows[j] by {
        let (gi, gj) = (codes[i], codes[j]);
        if rows[i] == rows[j] {
            assert(prow(p, gi)[0] == prow(p, gj)[0] && prow(p, gi)[1] == prow(p, gj)[1]);
            assert(key_of(p, gi) =~= key_of(p, gj));
            lemma_key_injective(p, gi, gj);
            if i < j { assert(gi < gj); } else { assert(gj < gi); }
        }
    }
}

/// The statement's body is the collected group results; leaving the groups' domain leaves the capacity domain.
pub proof fn lemma_denote(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures
        denote_body(db, query_spec()) == collect(grs(db)),
        !fits_each(grs(db), gfs(db)) ==> !fits_query(db, Seq::empty(), query_spec().body),
{
    lemma_statement();
    lemma_body(db);
}

/// When every selected code is `code_ok`, every group result is the row of its code.
proof fn lemma_all_ok(p: Seq<PartView>, db: Database)
    requires
        bound(p, db),
        forall|g: int| #[trigger] selected(p, g) ==> code_ok(p, g),
    ensures
        collect(grs(db)) is Ok,
        collect(grs(db))->Ok_0.len() == gkeys(gq(), xs_of(db)).len(),
        forall|h: int| 0 <= h < gkeys(gq(), xs_of(db)).len()
            ==> #[trigger] collect(grs(db))->Ok_0[h] == prow(p, code_at(p, db, h)),
{
    let rs = grs(db);
    lemma_group_shape(p, db);
    assert forall|h: int| 0 <= h < rs.len() implies #[trigger] rs[h] == Ok::<Row, SqlError>(prow(p, code_at(p, db, h))) by {
        lemma_code_at(p, db, h);
        lemma_group_result(p, db, h, code_at(p, db, h));
    }
    lemma_collect_ok(rs);
    assert forall|h: int| 0 <= h < rs.len() implies #[trigger] collect(rs)->Ok_0[h] == prow(p, code_at(p, db, h)) by {
        assert(rs[h] == Ok::<Row, SqlError>(collect(rs)->Ok_0[h]));
    }
}

/// When every selected code is `code_ok`, the body is `Ok` and its rows are the rows of the selected codes.
pub proof fn lemma_success(p: Seq<PartView>, db: Database, codes: Seq<int>)
    requires
        bound(p, db),
        forall|g: int| #[trigger] selected(p, g) ==> code_ok(p, g),
        forall|i: int| 0 <= i < codes.len() ==> selected(p, #[trigger] codes[i]),
        forall|i: int, j: int| 0 <= i < j < codes.len() ==> #[trigger] codes[i] < #[trigger] codes[j],
        forall|g: int| #[trigger] selected(p, g) ==> codes.contains(g),
    ensures
        denote_body(db, query_spec()) is Ok,
        denote_body(db, query_spec())->Ok_0.to_multiset() == codes.map_values(|g: int| prow(p, g)).to_multiset(),
{
    hide(denote_body);
    hide(grs);
    let xs = xs_of(db);
    let gk = gkeys(gq(), xs);
    lemma_denote(db);
    lemma_all_ok(p, db);
    lemma_group_shape(p, db);
    let body = collect(grs(db))->Ok_0;
    let mine = codes.map_values(|g: int| prow(p, g));
    // Both sides are duplicate-free with the same rows.
    assert(body.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < body.len() && 0 <= b < body.len() && a != b implies body[a] != body[b] by {
            lemma_code_at(p, db, a);
            lemma_code_at(p, db, b);
            let (ga, gb) = (code_at(p, db, a), code_at(p, db, b));
            if body[a] == body[b] {
                assert(prow(p, ga)[0] == prow(p, gb)[0] && prow(p, ga)[1] == prow(p, gb)[1]);
                assert(key_of(p, ga) =~= key_of(p, gb));
                assert(gk[a] == gk[b]);
            }
        }
    }
    lemma_prows_distinct(p, codes);
    assert forall|x: Row| body.contains(x) <==> mine.contains(x) by {
        if body.contains(x) {
            let h = choose|h: int| 0 <= h < body.len() && body[h] == x;
            lemma_code_at(p, db, h);
            let g = code_at(p, db, h);
            assert(codes.contains(g));
            let i = choose|i: int| 0 <= i < codes.len() && codes[i] == g;
            assert(mine[i] == x);
        }
        if mine.contains(x) {
            let i = choose|i: int| 0 <= i < mine.len() && mine[i] == x;
            let g = codes[i];
            assert(selected(p, g));
            lemma_gkeys_codes(p, db, key_of(p, g));
            assert(gk.contains(key_of(p, g)));
            let h = choose|h: int| 0 <= h < gk.len() && gk[h] == key_of(p, g);
            lemma_code_at(p, db, h);
            let g2 = code_at(p, db, h);
            lemma_key_injective(p, g, g2);
            assert(body[h] == x);
        }
    }
    lemma_nodup_same_multiset(body, mine);
}

/// The selected code of the group at index `h` (a spec choice).
pub open spec fn code_at(p: Seq<PartView>, db: Database, h: int) -> int {
    choose|g: int| selected(p, g) && key_of(p, g) == gkeys(gq(), xs_of(db))[h]
}

pub proof fn lemma_code_at(p: Seq<PartView>, db: Database, h: int)
    requires bound(p, db), 0 <= h < gkeys(gq(), xs_of(db)).len(),
    ensures
        selected(p, code_at(p, db, h)),
        key_of(p, code_at(p, db, h)) == gkeys(gq(), xs_of(db))[h],
{
    let g = lemma_group_code(p, db, h);
    assert(selected(p, g) && key_of(p, g) == gkeys(gq(), xs_of(db))[h]);
}

} // verus!
