//! From per-(nation group, year) sums to the fixed claim (`lemma_answer`).
//!
//! Nation rows with equal names form one group, named by its first row (`nrep`); a lineitem row's group is its
//! supplier nation's (`grp`) and its year its order's (`yr`). `tsum(a, y, w, lo, hi)` sums over the lineitem rows
//! `lo..hi` of group `a` and year `y` the count (`w == 0`), amount (`w == 1`) or absolute amount (`w == 2`); `msum`
//! is the absolute amount of all qualifying rows, which bounds every group's (`lemma_tsum_le_msum`).
//!
//! The executable code produces a list of output entries `(a, y)` (`answer_ok`): exactly the non-empty groups (`a` a
//! group's first row), in ORDER BY order (names ascending, then years descending), with every group's absolute
//! amount within `i128`. The statement's group key `(n_name, o_year)` of entry `(a, y)` collects exactly that
//! group's rows (`lemma_ksum_tsum`), so with the denotation (`denotation::lemma_denotation`) and the product collapse
//! (`groups::lemma_group_sums`) the entries' rows are the statement's rows, sorted (`link::query::lemma_result_from_keys`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::scalar::compare;
use crate::spec::numeric::*;
use crate::spec::text::lex_cmp;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::link::expr::{i128_max, lemma_compare_num};
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::denotation::*;
use crate::agent::lines::*;
use crate::agent::groups::*;

verus! {

// ------------------------------------------------------------------------------------------------ nation groups

/// The first nation row `b..a` (from `b`) whose name equals row `a`'s, or `a` itself.
pub open spec fn rep_from(sv: StoresView, a: int, b: int) -> int
    decreases a - b,
{
    if b >= a { a } else if nname(sv, b) == nname(sv, a) { b } else { rep_from(sv, a, b + 1) }
}

/// The first nation row with the name of row `a` (the group of `a`).
pub open spec fn nrep(sv: StoresView, a: int) -> int { rep_from(sv, a, 0) }

proof fn lemma_rep_from(sv: StoresView, a: int, b: int)
    requires 0 <= b <= a, forall|c: int| 0 <= c < b ==> nname(sv, c) != nname(sv, a),
    ensures
        0 <= rep_from(sv, a, b) <= a,
        nname(sv, rep_from(sv, a, b)) == nname(sv, a),
        forall|c: int| 0 <= c < rep_from(sv, a, b) ==> nname(sv, c) != nname(sv, a),
    decreases a - b,
{
    if b < a && nname(sv, b) != nname(sv, a) {
        lemma_rep_from(sv, a, b + 1);
    }
}

/// The group of `a` is a row at most `a` with `a`'s name, and no earlier row has that name.
pub proof fn lemma_nrep(sv: StoresView, a: int)
    requires 0 <= a,
    ensures
        0 <= nrep(sv, a) <= a,
        nname(sv, nrep(sv, a)) == nname(sv, a),
        forall|c: int| 0 <= c < nrep(sv, a) ==> nname(sv, c) != nname(sv, a),
{
    lemma_rep_from(sv, a, 0);
}

/// Two rows are in one group exactly when their names are equal; a group's first row is its own group.
pub proof fn lemma_nrep_eq(sv: StoresView, a: int, c: int)
    requires 0 <= a, 0 <= c,
    ensures
        (nrep(sv, a) == nrep(sv, c)) == (nname(sv, a) == nname(sv, c)),
        nrep(sv, nrep(sv, a)) == nrep(sv, a),
{
    lemma_nrep(sv, a);
    lemma_nrep(sv, c);
    let (r1, r2) = (nrep(sv, a), nrep(sv, c));
    if nname(sv, a) == nname(sv, c) {
        if r1 < r2 { assert(nname(sv, r1) == nname(sv, c)); }
        if r2 < r1 { assert(nname(sv, r2) == nname(sv, a)); }
    }
    lemma_nrep(sv, r1);
    let r3 = nrep(sv, r1);
    if r3 < r1 { assert(nname(sv, r3) == nname(sv, a)); }
}

// ------------------------------------------------------------------------------------------------ group sums

/// The group of lineitem row `l` (its supplier nation's).
pub open spec fn grp(sv: StoresView, l: int) -> int { nrep(sv, l_nat(sv, l)) }

/// The year of lineitem row `l` (its order's).
pub open spec fn yr(sv: StoresView, l: int) -> int { day_year(od(sv)[l_ord(sv, l)]) }

/// Contribution of lineitem row `l` to group `a`, year `y`.
pub open spec fn tterm(sv: StoresView, ps: Seq<Literal>, a: int, y: int, w: int, l: int) -> int {
    if line_qual(sv, ps, l) && grp(sv, l) == a && yr(sv, l) == y { wval(w, line_val(sv, l)) } else { 0 }
}

/// Sum of the contributions of the lineitem rows `lo..hi` to group `a`, year `y`.
pub open spec fn tsum(sv: StoresView, ps: Seq<Literal>, a: int, y: int, w: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { tsum(sv, ps, a, y, w, lo, hi - 1) + tterm(sv, ps, a, y, w, hi - 1) }
}

/// Absolute amount of lineitem row `l` when it qualifies.
pub open spec fn mterm(sv: StoresView, ps: Seq<Literal>, l: int) -> int {
    if line_qual(sv, ps, l) { abs(line_val(sv, l)) } else { 0 }
}

/// Absolute amount of the qualifying lineitem rows `lo..hi`.
pub open spec fn msum(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { msum(sv, ps, lo, hi - 1) + mterm(sv, ps, hi - 1) }
}

/// Adjacent ranges add.
pub proof fn lemma_tsum_split(sv: StoresView, ps: Seq<Literal>, a: int, y: int, w: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures tsum(sv, ps, a, y, w, lo, hi) == tsum(sv, ps, a, y, w, lo, mid) + tsum(sv, ps, a, y, w, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_tsum_split(sv, ps, a, y, w, lo, mid, hi - 1);
    }
}

/// Adjacent ranges add.
pub proof fn lemma_msum_split(sv: StoresView, ps: Seq<Literal>, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures msum(sv, ps, lo, hi) == msum(sv, ps, lo, mid) + msum(sv, ps, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_msum_split(sv, ps, lo, mid, hi - 1);
    }
}

/// Counts and absolute sums are non-negative, bound the sums and are bounded by `msum`; a zero count means zero sums.
pub proof fn lemma_tsum_bounds(sv: StoresView, ps: Seq<Literal>, a: int, y: int, lo: int, hi: int)
    ensures
        tsum(sv, ps, a, y, 0, lo, hi) >= 0,
        0 <= tsum(sv, ps, a, y, 2, lo, hi) <= msum(sv, ps, lo, hi),
        -tsum(sv, ps, a, y, 2, lo, hi) <= tsum(sv, ps, a, y, 1, lo, hi) <= tsum(sv, ps, a, y, 2, lo, hi),
        tsum(sv, ps, a, y, 0, lo, hi) == 0 ==> tsum(sv, ps, a, y, 1, lo, hi) == 0 && tsum(sv, ps, a, y, 2, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_tsum_bounds(sv, ps, a, y, lo, hi - 1);
    }
}

/// `msum` is non-negative.
pub proof fn lemma_msum_nonneg(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int)
    ensures msum(sv, ps, lo, hi) >= 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_msum_nonneg(sv, ps, lo, hi - 1);
    }
}

// ------------------------------------------------------------------------------------------------ keys and groups

/// The statement's group key of group `a`, year `y`.
pub open spec fn okey(sv: StoresView, a: int, y: int) -> Row {
    seq![Val::Text(nname(sv, a)), Val::Num { coeff: y, scale: 0 }]
}

/// A qualifying row's supplier nation exists.
proof fn lemma_nat_range(sv: StoresView, ps: Seq<Literal>, l: int)
    requires line_qual(sv, ps, l),
    ensures 0 <= l_nat(sv, l) < n_n(sv),
{
    lemma_key_row(nk(sv), sn(sv)[l_supp(sv, l)]);
}

/// A qualifying row's key is its group's key.
pub proof fn lemma_line_key_grp(sv: StoresView, ps: Seq<Literal>, l: int)
    requires line_qual(sv, ps, l),
    ensures line_key(sv, l) == okey(sv, grp(sv, l), yr(sv, l)), 0 <= grp(sv, l) < n_n(sv), nrep(sv, grp(sv, l)) == grp(sv, l),
{
    lemma_nat_range(sv, ps, l);
    lemma_nrep(sv, l_nat(sv, l));
    lemma_nrep_eq(sv, l_nat(sv, l), l_nat(sv, l));
    assert(line_key(sv, l) =~= okey(sv, grp(sv, l), yr(sv, l)));
}

/// The key of a group's first row collects exactly that group's rows.
pub proof fn lemma_ksum_tsum(sv: StoresView, ps: Seq<Literal>, a: int, y: int, w: int, n: int)
    requires 0 <= a, nrep(sv, a) == a, n >= 0,
    ensures ksum(sv, ps, okey(sv, a, y), w, n) == tsum(sv, ps, a, y, w, 0, n),
    decreases n,
{
    if n > 0 {
        lemma_ksum_tsum(sv, ps, a, y, w, n - 1);
        let l = n - 1;
        if line_qual(sv, ps, l) {
            lemma_line_key_grp(sv, ps, l);
            lemma_nrep_eq(sv, l_nat(sv, l), a);
            lemma_nrep_eq(sv, grp(sv, l), a);
            lemma_nrep(sv, l_nat(sv, l));
            let k = okey(sv, a, y);
            if line_key(sv, l) == k {
                assert(line_key(sv, l)[0] == k[0] && line_key(sv, l)[1] == k[1]);
                assert(nname(sv, grp(sv, l)) == nname(sv, a));
            }
            if grp(sv, l) == a && yr(sv, l) == y {
                assert(line_key(sv, l) == k);
            }
        }
    }
}

/// A key with a qualifying row is the key of that row.
pub proof fn lemma_key_witness(sv: StoresView, ps: Seq<Literal>, k: Row, n: int) -> (l: int)
    requires ksum(sv, ps, k, 0, n) > 0,
    ensures 0 <= l < n, line_qual(sv, ps, l), line_key(sv, l) == k,
    decreases n,
{
    if ksum(sv, ps, k, 0, n - 1) > 0 {
        lemma_key_witness(sv, ps, k, n - 1)
    } else {
        n - 1
    }
}

// ------------------------------------------------------------------------------------------------ the answer

/// Entries `ent` (group, year) are the output of the first `n` lineitem rows: exactly the non-empty groups, named by
/// their first rows, in ORDER BY order; every group's absolute amount fits `i128`.
pub open spec fn answer_ok(sv: StoresView, ps: Seq<Literal>, ent: Seq<(int, int)>, n: int) -> bool {
    &&& forall|i: int| 0 <= i < ent.len() ==> 0 <= (#[trigger] ent[i]).0 < n_n(sv) && nrep(sv, ent[i].0) == ent[i].0
            && tsum(sv, ps, ent[i].0, ent[i].1, 0, 0, n) > 0
    &&& forall|a: int, y: int| 0 <= a < n_n(sv) && nrep(sv, a) == a && #[trigger] tsum(sv, ps, a, y, 0, 0, n) > 0
            ==> ent.contains((a, y))
    &&& forall|i: int, j: int| 0 <= i < j < ent.len() ==> entry_lt(sv, #[trigger] ent[i], #[trigger] ent[j])
    &&& forall|a: int, y: int| #[trigger] tsum(sv, ps, a, y, 2, 0, n) <= i128_max()
}

/// Entry `e` comes before entry `f`: a smaller name, or the same group with a later year.
pub open spec fn entry_lt(sv: StoresView, e: (int, int), f: (int, int)) -> bool {
    lex_cmp(nname(sv, e.0), nname(sv, f.0)) < 0 || (e.0 == f.0 && e.1 > f.1)
}

/// The output row of entry `e`.
pub open spec fn entry_row(sv: StoresView, ps: Seq<Literal>, e: (int, int)) -> Row {
    okey(sv, e.0, e.1).push(Val::Num { coeff: tsum(sv, ps, e.0, e.1, 1, 0, n_l(sv)), scale: 4 })
}

/// The output rows of the entries.
pub open spec fn answer_rows(sv: StoresView, ps: Seq<Literal>, ent: Seq<(int, int)>) -> Seq<Row> {
    ent.map_values(|e: (int, int)| entry_row(sv, ps, e))
}

/// The ORDER BY comparison of two output rows: by name, then by year descending.
proof fn lemma_rows_cmp(sv: StoresView, ps: Seq<Literal>, e: (int, int), f: (int, int))
    requires entry_lt(sv, e, f),
    ensures keys_cmp(q9_order_keys(), entry_row(sv, ps, e), entry_row(sv, ps, f)) < 0,
{
    let keys = q9_order_keys();
    let (r1, r2) = (entry_row(sv, ps, e), entry_row(sv, ps, f));
    let k1 = keys.drop_first();
    assert(k1 =~= seq![keys[1]]);
    assert(k1.drop_first() =~= Seq::<OrderKey>::empty());
    assert(r1[0] == Val::Text(nname(sv, e.0)) && r2[0] == Val::Text(nname(sv, f.0)));
    assert(r1[1] == (Val::Num { coeff: e.1, scale: 0 }) && r2[1] == (Val::Num { coeff: f.1, scale: 0 }));
    let c0 = lex_cmp(nname(sv, e.0), nname(sv, f.0));
    assert(key_cmp(keys[0], r1, r2) == c0);
    if c0 < 0 {
        assert(keys_cmp(keys, r1, r2) == c0);
    } else {
        assert(e.0 == f.0 && e.1 > f.1);
        lemma_lex_cmp_zero(nname(sv, e.0), nname(sv, e.0));
        assert(c0 == 0);
        lemma_compare_num(e.1, 0, f.1, 0);
        let z: nat = (0nat - 0nat) as nat;
        assert(z == 0);
        assert(pow10(z) == 1);
        assert(align(e.1, 0, 0) == e.1 * pow10(z));
        assert(align(f.1, 0, 0) == f.1 * pow10(z));
        assert(max_nat(0, 0) == 0);
        assert(key_cmp(k1[0], r1, r2) == -1);
        assert(keys_cmp(k1.drop_first(), r1, r2) == 0);
        assert(keys_cmp(k1, r1, r2) == -1);
        assert(keys_cmp(keys, r1, r2) == keys_cmp(k1, r1, r2));
    }
}

/// The statement's output row of a non-empty group's key is the entry's row.
proof fn lemma_out_row(sv: StoresView, db: Database, ps: Seq<Literal>, e: (int, int))
    requires bound_db(sv, db), 0 <= e.0, nrep(sv, e.0) == e.0, tsum(sv, ps, e.0, e.1, 0, 0, n_l(sv)) > 0,
    ensures
        out_row(g2(), sel_rows(db, ps), okey(sv, e.0, e.1)) == entry_row(sv, ps, e),
        gcount(g2(), sel_rows(db, ps), okey(sv, e.0, e.1)) > 0,
{
    let (gg, xs, k) = (g2(), sel_rows(db, ps), okey(sv, e.0, e.1));
    lemma_parts_shape(sv, db);
    lemma_group_sums(sv, db, ps, k);
    lemma_ksum_tsum(sv, ps, e.0, e.1, 0, n_l(sv));
    lemma_ksum_tsum(sv, ps, e.0, e.1, 1, n_l(sv));
    let full = full_row(gg, xs, k);
    assert(agg_outs(gg, xs, k) =~= seq![Val::Num { coeff: tsum(sv, ps, e.0, e.1, 1, 0, n_l(sv)), scale: 4 }]);
    assert(full =~= entry_row(sv, ps, e));
    lemma_select_identity(full, gg.outs);
}

/// A key with a qualifying row is an entry's key.
proof fn lemma_key_entry(sv: StoresView, db: Database, ps: Seq<Literal>, ent: Seq<(int, int)>, k: Row) -> (i: int)
    requires bound_db(sv, db), answer_ok(sv, ps, ent, n_l(sv)), gcount(g2(), sel_rows(db, ps), k) > 0,
    ensures 0 <= i < ent.len(), okey(sv, ent[i].0, ent[i].1) == k,
{
    lemma_group_sums(sv, db, ps, k);
    let l = lemma_key_witness(sv, ps, k, n_l(sv));
    lemma_line_key_grp(sv, ps, l);
    let (a, y) = (grp(sv, l), yr(sv, l));
    lemma_ksum_tsum(sv, ps, a, y, 0, n_l(sv));
    assert(tsum(sv, ps, a, y, 0, 0, n_l(sv)) > 0);
    assert(ent.contains((a, y)));
    choose|i: int| 0 <= i < ent.len() && ent[i] == (a, y)
}

/// `group_caps` of the statement's GROUP BY: every key's absolute amount is its group's.
proof fn lemma_caps(sv: StoresView, db: Database, ps: Seq<Literal>, ent: Seq<(int, int)>)
    requires bound_db(sv, db), answer_ok(sv, ps, ent, n_l(sv)),
    ensures group_caps(g2(), sel_rows(db, ps)),
{
    let (g, xs) = (g2(), sel_rows(db, ps));
    lemma_parts_shape(sv, db);
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
        assert(j == 0);
        lemma_group_sums(sv, db, ps, k);
        lemma_ksum_bounds(sv, ps, k, n_l(sv));
        if ksum(sv, ps, k, 0, n_l(sv)) > 0 {
            let l = lemma_key_witness(sv, ps, k, n_l(sv));
            lemma_line_key_grp(sv, ps, l);
            lemma_ksum_tsum(sv, ps, grp(sv, l), yr(sv, l), 2, n_l(sv));
            assert(tsum(sv, ps, grp(sv, l), yr(sv, l), 2, 0, n_l(sv)) <= i128_max());
        }
    }
}

/// The statement's group keys of the entries.
pub open spec fn entry_keys(sv: StoresView, ent: Seq<(int, int)>) -> Seq<Row> {
    ent.map_values(|e: (int, int)| okey(sv, e.0, e.1))
}

/// The entries' keys are pairwise different (different names, or one group with different years).
proof fn lemma_keys_distinct(sv: StoresView, ps: Seq<Literal>, ent: Seq<(int, int)>)
    requires answer_ok(sv, ps, ent, n_l(sv)),
    ensures entry_keys(sv, ent).no_duplicates(),
{
    let ks = entry_keys(sv, ent);
    assert forall|i: int, j: int| 0 <= i < ks.len() && 0 <= j < ks.len() && i != j implies ks[i] != ks[j] by {
        let (e, f) = (ent[i], ent[j]);
        if ks[i] == ks[j] {
            assert(ks[i][0] == ks[j][0] && ks[i][1] == ks[j][1]);
            assert(nname(sv, e.0) == nname(sv, f.0));
            lemma_lex_cmp_zero(nname(sv, e.0), nname(sv, f.0));
            if i < j { assert(entry_lt(sv, e, f)); } else { assert(entry_lt(sv, f, e)); }
        }
    }
}

/// The entries' keys are exactly the statement's non-empty groups.
proof fn lemma_keys_groups(sv: StoresView, db: Database, ps: Seq<Literal>, ent: Seq<(int, int)>)
    requires bound_db(sv, db), answer_ok(sv, ps, ent, n_l(sv)),
    ensures forall|k: Row| #[trigger] entry_keys(sv, ent).contains(k) <==> gcount(g2(), sel_rows(db, ps), k) > 0,
{
    let ks = entry_keys(sv, ent);
    assert forall|k: Row| #[trigger] ks.contains(k) <==> gcount(g2(), sel_rows(db, ps), k) > 0 by {
        if ks.contains(k) {
            let i = choose|i: int| 0 <= i < ks.len() && ks[i] == k;
            lemma_out_row(sv, db, ps, ent[i]);
        }
        if gcount(g2(), sel_rows(db, ps), k) > 0 {
            let i = lemma_key_entry(sv, db, ps, ent, k);
            assert(ks[i] == k);
        }
    }
}

/// The entries' rows are the statement's output rows of their keys, sorted by the ORDER BY keys.
proof fn lemma_rows_sorted(sv: StoresView, db: Database, ps: Seq<Literal>, ent: Seq<(int, int)>)
    requires bound_db(sv, db), answer_ok(sv, ps, ent, n_l(sv)),
    ensures
        answer_rows(sv, ps, ent).len() == entry_keys(sv, ent).len(),
        forall|i: int| 0 <= i < answer_rows(sv, ps, ent).len() ==> #[trigger] answer_rows(sv, ps, ent)[i]
            == out_row(g2(), sel_rows(db, ps), entry_keys(sv, ent)[i]),
        sorted_by(q9_order_keys(), answer_rows(sv, ps, ent)),
{
    let out = answer_rows(sv, ps, ent);
    let ks = entry_keys(sv, ent);
    assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i] == out_row(g2(), sel_rows(db, ps), ks[i]) by {
        lemma_out_row(sv, db, ps, ent[i]);
    }
    assert forall|i: int, j: int| 0 <= i < j < out.len() implies keys_cmp(q9_order_keys(), #[trigger] out[i], #[trigger] out[j]) <= 0 by {
        lemma_rows_cmp(sv, ps, ent[i], ent[j]);
    }
}

/// Under the column-level facts, the entries' rows are an allowed output of the statement on every bound database
/// (when no part name's `LIKE` raises).
pub proof fn lemma_answer(sv: StoresView, db: Database, ps: Seq<Literal>, ent: Seq<(int, int)>)
    requires bound_db(sv, db), param_domain(ps), likes_ok(sv, db, ps), answer_ok(sv, ps, ent, n_l(sv)),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(answer_rows(sv, ps, ent))),
{
    let (g, xs) = (g2(), sel_rows(db, ps));
    let out = answer_rows(sv, ps, ent);
    let ks = entry_keys(sv, ent);
    lemma_caps(sv, db, ps, ent);
    lemma_denotation(sv, db, ps);
    lemma_keys_distinct(sv, ps, ent);
    lemma_keys_groups(sv, db, ps, ent);
    lemma_rows_sorted(sv, db, ps, ent);
    lemma_result_from_keys(g, q9_order_keys(), 0, None, xs, ks, out);
    lemma_slice_all(out);
    lemma_query_shape(ps);
    lemma_ordered_link(db, query_spec_at(ps), g, xs, out);
}

} // verus!
