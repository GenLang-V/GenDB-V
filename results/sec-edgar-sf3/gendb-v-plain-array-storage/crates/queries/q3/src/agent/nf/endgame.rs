//! The final step: for every database bound to the stored parts, the answer computed from the views (scan
//! totals, groups, AVG, picked groups) is an allowed outcome of the statement.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::relation::*;
use crate::spec::aggs::avg::*;
use crate::spec::fns::div::*;
use crate::exec::relational::domain::*;
use crate::exec::aggs::avg::fits_avg_value;
use crate::link::query::{text_wf, view_rows, gsum, gcount, gkeys, lemma_gkeys};
use crate::link::capacity::lemma_num_sum_bound;
use crate::gendb_entry::{bound_db, capacity_domain};
use crate::gendb_entry::stores::StoresView;
use crate::query::query_spec_at;
use crate::stores::flat_sub::interface as si;
use crate::stores::flat_num::interface as ni;
use crate::agent::common::wide::*;
use crate::agent::scan::NumCols;
use crate::agent::keys::{SubCols, lemma_qlist};
use crate::agent::groups::*;
use crate::agent::groups;
use crate::agent::run::totals_ok;
use crate::agent::answer::*;
use crate::agent::nf::ast::*;
use crate::agent::nf::rows::*;
use crate::agent::nf::fromwhere::*;
use crate::agent::nf::sums::*;
use crate::agent::nf::glue::*;
use crate::agent::nf::gfacts::*;
use crate::agent::nf::body::*;
use crate::agent::nf::cap::*;
use crate::agent::nf::order::*;

verus! {

/// The stored rows have the shapes the normal form reads.
pub proof fn lemma_shaped(sv: StoresView, db: Database)
    requires tables_are(sv, db),
    ensures tables_shaped(db),
{
    assert forall|i: int| 0 <= i < db.tables[1].len() implies shape_num(#[trigger] db.tables[1][i]) by {
        assert(db.tables[1][i] == ni::row_at(sv.flat_num, i));
    }
    assert forall|j: int| 0 <= j < db.tables[0].len() implies shape_sub(#[trigger] db.tables[0][j]) by {
        assert(db.tables[0][j] == si::row_at(sv.flat_sub, j));
        assert(db.tables[0][j][10] == si::fy_value(sv.flat_sub, j));
    }
}

/// The views and the inputs of the grouping for one database.
pub open spec fn views_ok(sv: StoresView, num: &NumCols, sub: &SubCols, kc: &KeyCols, p0: Seq<u8>, p1: int,
    qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, g: &Groups) -> bool {
    &&& cols_of(sv, num, sub, kc)
    &&& num.wf()
    &&& sub.p1 as int == p1
    &&& num.uom_off@.len() == num.n + 1
    &&& sub.adsh_off@.len() == sub.n + 1
    &&& totals_ok(num, sub, p0, tot, seen, num.n as int)
    &&& qr.len() == sub.qlist(sub.n as int).len()
    &&& forall|t: int| 0 <= t < qr.len() ==> #[trigger] qr[t] as int == sub.qlist(sub.n as int)[t]
    &&& groups_ok(g, kc, qr, tot, seen, qr.len() as int)
    &&& groups_cols(g, kc)
    &&& seen.len() == qr.len()
}

/// A bound database: its tables are the views'.
proof fn lemma_db(sv: StoresView, db: Database, num: &NumCols, sub: &SubCols, kc: &KeyCols, p0: Seq<u8>, p1: int,
    qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, g: &Groups)
    requires bound_db(sv, db), views_ok(sv, num, sub, kc, p0, p1, qr, tot, seen, g),
    ensures
        world(db, num, sub, kc, p0, p1, qr, tot, seen),
        vals_ok(db),
{
    lemma_bound_facts(sv, db);
    let (n_sub, n_num) = (db.tables[0].len(), db.tables[1].len());
    assert(text_wf(ni::text_view(sv.flat_num, ni::UOM_OFFSETS as int, ni::UOM_BYTES as int), n_num as int));
    assert(text_wf(si::text_view(sv.flat_sub, si::ADSH_OFFSETS as int, si::ADSH_BYTES as int), n_sub as int));
    assert(num.n == n_num);
    assert(sub.n == n_sub);
    lemma_rows_view(sv, db, num, sub, kc, p1);
    lemma_shaped(sv, db);
    assert forall|i: int| 0 <= i < db.tables[1].len() implies {
        &&& (#[trigger] db.tables[1][i])[7] is Num
        &&& db.tables[1][i][7]->Num_scale == 4
        &&& abs(db.tables[1][i][7]->Num_coeff) < pow10(28)
    } by {
        assert(abs(num.val(i)) < pow10(28));
    }
}

/// The groups' keys are the outer GROUP BY's, with the same SUMs.
proof fn lemma_keys(db: Database, num: &NumCols, sub: &SubCols, kc: &KeyCols, p0: Seq<u8>, p1: int,
    qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, g: &Groups)
    requires world(db, num, sub, kc, p0, p1, qr, tot, seen), groups_ok(g, kc, qr, tot, seen, qr.len() as int),
        seen.len() == qr.len(),
    ensures ({
        let ks = gks(kc, qr, seen, qr.len() as int);
        &&& ks.no_duplicates()
        &&& ks.len() == g.rep@.len()
        &&& forall|k: Row| #[trigger] ks.contains(k) <==> gkeys(g_out(p0, p1), joined(db)).contains(k)
        &&& forall|i: int| 0 <= i < ks.len() ==> #[trigger] ks[i] == kc.okey(g.rep@[i] as int)
        &&& forall|i: int| 0 <= i < ks.len() ==> osum(db, p0, p1, #[trigger] ks[i]) == wval(g.sum@[i])
    }),
{
    let nq = qr.len() as int;
    let ks = gks(kc, qr, seen, nq);
    lemma_groups_facts(g, kc, qr, tot, seen, nq);
    lemma_gks(kc, qr, seen, nq);
    lemma_gkeys(g_out(p0, p1), joined(db));
    assert forall|k: Row| #[trigger] ks.contains(k) <==> gkeys(g_out(p0, p1), joined(db)).contains(k) by {
        lemma_outer_group(db, num, sub, kc, p0, p1, qr, tot, seen, k);
    }
    assert forall|i: int| 0 <= i < ks.len() implies osum(db, p0, p1, #[trigger] ks[i]) == wval(g.sum@[i]) by {
        lemma_outer_group(db, num, sub, kc, p0, p1, qr, tot, seen, ks[i]);
        assert(group_key(g, kc, i) == ks[i]);
    }
    assert forall|i: int| 0 <= i < ks.len() implies #[trigger] ks[i] == kc.okey(g.rep@[i] as int) by {
        assert(group_key(g, kc, i) == ks[i]);
    }
}

/// The AVG input: one numeric SUM per distinct cik, adding up to the total.
proof fn lemma_avg_value(db: Database, num: &NumCols, sub: &SubCols, kc: &KeyCols, p0: Seq<u8>, p1: int,
    qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, g: &Groups)
    requires world(db, num, sub, kc, p0, p1, qr, tot, seen), groups_ok(g, kc, qr, tot, seen, qr.len() as int),
        seen.len() == qr.len(), g.rep@.len() > 0,
    ensures ({
        let vs = in_sums(db, p0, p1);
        let tt = wval(g.total);
        &&& vs.len() == g.ncik && g.ncik > 0
        &&& all_of_kind(NumKind::Numeric, vs) && count_non_null(vs) == vs.len()
        &&& avg_sum(NumKind::Numeric, vs) == (tt, 4nat)
        &&& abs(tt) <= sum_mass(NumKind::Numeric, vs)
        &&& in128(tt) ==> avg_in(db, p0, p1) == num_div(tt, 4, g.ncik as int, 0)
    }),
{
    let nq = qr.len() as int;
    let gi = g_in(p0, p1);
    let xs = joined(db);
    let vs = in_sums(db, p0, p1);
    let ks = gkeys(gi, xs);
    let tt = wval(g.total);
    lemma_groups_facts(g, kc, qr, tot, seen, nq);
    lemma_inner_keys(db, num, sub, kc, p0, p1, qr, tot, seen);
    // some rank has rows, so some cik is listed
    lemma_gks(kc, qr, seen, nq);
    let k0 = gks(kc, qr, seen, nq)[0];
    assert(gks(kc, qr, seen, nq).contains(k0));
    let id = choose|id: int| 0 <= id < nq && seen[id] && #[trigger] kc.okey(qr[id] as int) == k0;
    lemma_dciks(kc, qr, seen, nq);
    assert(dciks(kc, qr, seen, nq).contains(kc.cik(qr[id] as int)));
    lemma_in_sums_numeric(db, p0, p1);
    let cs = ks.map_values(|k: Row| gsum(gi, xs, k, 0));
    assert forall|t: int| 0 <= t < vs.len() implies #[trigger] vs[t] == (Val::Num { coeff: cs[t], scale: 4 }) by {}
    lemma_num_sum_scale4(vs, cs);
    lemma_ksum_csum(gi, xs, ks);
    lemma_ksum_total(gi, xs);
    lemma_total(db, num, sub, kc, p0, p1, qr, tot, seen);
    assert(num_sum(vs) == (tt, 4nat));
    lemma_num_sum_bound(vs);
    if in128(tt) {
        lemma_num_in_range_small(tt, 4);
    }
}

/// Every answer is an allowed outcome for a bound database.
pub proof fn lemma_final(sv: StoresView, db: Database, ps: Seq<Literal>, num: &NumCols, sub: &SubCols, kc: &KeyCols,
    p0: Seq<u8>, p1: int, qr: Seq<usize>, tot: Seq<Wide>, seen: Seq<bool>, g: &Groups, ans: &Outcome3,
    cand: Seq<int>, pick: Seq<int>, ac: int, asc: nat)
    requires
        bound_db(sv, db), binding(ps, p0, p1),
        views_ok(sv, num, sub, kc, p0, p1, qr, tot, seen, g),
        answer_ok(g, kc, ans, cand, pick, ac, asc),
        g.rep@.len() <= usize::MAX,
    ensures
        ans matches Outcome3::Rows(out) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(view_rows(out@))),
        ans matches Outcome3::Err(e) ==> ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(*e)),
        ans is Capacity ==> !capacity_domain(db, query_spec_at(ps)),
{
    let oq = query_spec_at(ps);
    lemma_query_parts(ps);
    lemma_db(sv, db, num, sub, kc, p0, p1, qr, tot, seen, g);
    lemma_keys(db, num, sub, kc, p0, p1, qr, tot, seen, g);
    let nq = qr.len() as int;
    let ks = gks(kc, qr, seen, nq);
    let gk = gkeys(g_out(p0, p1), joined(db));
    lemma_gkeys(g_out(p0, p1), joined(db));
    let ng = g.rep@.len() as int;
    if ng == 0 {
        assert(gb_rows(db, p0, p1).len() == 0) by {
            if gk.len() > 0 {
                assert(gk.contains(gk[0]));
                assert(ks.contains(gk[0]));
            }
        }
        lemma_body_empty(db, ps, p0, p1);
        match ans {
            Outcome3::Rows(out) => {
                assert(view_rows(out@) =~= Seq::<Row>::empty());
                crate::link::outcome::lemma_outcome_sorted(db, oq, Seq::<Row>::empty(), Seq::<Row>::empty());
                assert(slice_rows(Seq::<Row>::empty(), 0, Some(100nat)) =~= Seq::<Row>::empty());
            },
            _ => {},
        }
    } else {
        lemma_avg_value(db, num, sub, kc, p0, p1, qr, tot, seen, g);
        let tt = wval(g.total);
        let n = g.ncik as int;
        let vs = in_sums(db, p0, p1);
        assert(gb_rows(db, p0, p1).len() > 0) by {
            assert(ks.contains(ks[0]));
            assert(gk.contains(ks[0]));
        }
        match ans {
            Outcome3::Rows(out) => {
                assert(avg_in(db, p0, p1) == Ok::<Val, SqlError>(Val::Num { coeff: ac, scale: asc }));
                lemma_picked(db, p0, p1, ac, asc, ks, cand, pick, g, kc);
                lemma_answer_ok(db, ps, p0, p1, ac, asc, ks, cand, pick);
                lemma_rows_eq(db, p0, p1, ks, pick, g, kc);
            },
            Outcome3::Err(e) => {
                lemma_body_err(db, ps, p0, p1, *e);
                crate::link::outcome::lemma_outcome_err(db, oq, *e);
            },
            Outcome3::Capacity => {
                if exists|i: int| 0 <= i < ng && !#[trigger] in128(wval(g.sum@[i])) {
                    let i = choose|i: int| 0 <= i < ng && !#[trigger] in128(wval(g.sum@[i]));
                    assert(ks.contains(ks[i]));
                    lemma_cap_group(db, ps, p0, p1, ks[i]);
                } else {
                    assert(!fits_avg_value(NumKind::Numeric, vs));
                    lemma_cap_avg(db, ps, p0, p1);
                }
            },
        }
    }
}

/// The picked groups as an answer over the outer GROUP BY's keys.
proof fn lemma_picked(db: Database, p0: Seq<u8>, p1: int, ac: int, asc: nat, ks: Seq<Row>, cand: Seq<int>, pick: Seq<int>,
    g: &Groups, kc: &KeyCols)
    requires
        ks.no_duplicates(), ks.len() == g.rep@.len(),
        forall|k: Row| #[trigger] ks.contains(k) <==> gkeys(g_out(p0, p1), joined(db)).contains(k),
        forall|i: int| 0 <= i < ks.len() ==> osum(db, p0, p1, #[trigger] ks[i]) == wval(g.sum@[i]),
        pick_facts(gsums(g), g.rep@.len() as int, ac, asc, cand, pick),
    ensures picked_ok(db, p0, p1, ac, asc, ks, cand, pick),
{
    let sf = gsums(g);
    assert forall|i: int| 0 <= i < ks.len() implies ((num_cmp(osum(db, p0, p1, #[trigger] ks[i]), 4, ac, asc) > 0) == cand.contains(i)) by {
        assert(sf(i) == osum(db, p0, p1, ks[i]));
    }
    assert forall|u: int, v: int| 0 <= u < v < pick.len() implies
        osum(db, p0, p1, ks[#[trigger] pick[u]]) >= osum(db, p0, p1, ks[#[trigger] pick[v]]) by {
        assert(cand.contains(pick[u]) && cand.contains(pick[v]));
        let a = choose|a: int| 0 <= a < cand.len() && cand[a] == pick[u];
        let b = choose|b: int| 0 <= b < cand.len() && cand[b] == pick[v];
        assert(sf(pick[u]) >= sf(pick[v]));
    }
    assert forall|u: int, t: int| 0 <= u < pick.len() && 0 <= t < cand.len() && !pick.contains(cand[t]) implies
        osum(db, p0, p1, ks[#[trigger] pick[u]]) >= osum(db, p0, p1, ks[#[trigger] cand[t]]) by {
        assert(cand.contains(pick[u]));
        let a = choose|a: int| 0 <= a < cand.len() && cand[a] == pick[u];
        assert(sf(pick[u]) >= sf(cand[t]));
    }
}

/// The picked groups' rows are the answer's rows.
proof fn lemma_rows_eq(db: Database, p0: Seq<u8>, p1: int, ks: Seq<Row>, pick: Seq<int>, g: &Groups, kc: &KeyCols)
    requires
        tables_shaped(db),
        ks.len() == g.rep@.len(),
        forall|k: Row| #[trigger] ks.contains(k) ==> gkeys(g_out(p0, p1), joined(db)).contains(k),
        forall|i: int| 0 <= i < ks.len() ==> #[trigger] ks[i] == kc.okey(g.rep@[i] as int),
        forall|i: int| 0 <= i < ks.len() ==> osum(db, p0, p1, #[trigger] ks[i]) == wval(g.sum@[i]),
        forall|u: int| 0 <= u < pick.len() ==> 0 <= #[trigger] pick[u] < ks.len(),
    ensures rows_at(db, p0, p1, ks, pick) == pick.map_values(|i: int| grow(g, kc, i)),
{
    let a = rows_at(db, p0, p1, ks, pick);
    let b = pick.map_values(|i: int| grow(g, kc, i));
    assert forall|u: int| 0 <= u < a.len() implies a[u] == b[u] by {
        let i = pick[u];
        assert(ks.contains(ks[i]));
        lemma_orow(db, p0, p1, ks[i]);
        assert(a[u] =~= b[u]);
    }
    assert(a =~= b);
}

} // verus!
