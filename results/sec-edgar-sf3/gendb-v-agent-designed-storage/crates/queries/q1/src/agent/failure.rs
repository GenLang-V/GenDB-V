//! The answer when some selected code is not `code_ok` (a count beyond int8 or an AVG division outside the
//! executable domain; impossible below about 10^17 rows, but part of the claim). The canonical evaluation stops at
//! the first such group in first-occurrence order: a count beyond int8 is SQL error 22003, an AVG outside its
//! domain leaves the capacity domain.
//!
//! `first_at(p, g, f)`: `f` is the smallest canonical row number (`orig`) of the stored rows of code `g`; then
//! canonical row `f` is the first row of the group (`lemma_first_row`). The failing code with the smallest such
//! `f` is the first failing group (`lemma_failure`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::order::*;
use crate::gendb_entry::layout::PartView;
use crate::exec::relational::domain::{fits_query, fits_each, ok_before, lemma_each_capacity};
use crate::bridge::collect::lemma_collect_first_err;
use crate::link::query::{gkeys, lemma_gkeys, hit};
use crate::query::query_spec;
use crate::stores::pre::interface::*;
use crate::stores::pre::interface::common::cols::u64s;
use crate::stores::pre::interface::common::runs::*;
use crate::stores::pre::interface::common::perm::*;
use crate::stores::pre::declaration::*;
use super::canon::*;
use super::store::*;
use super::answer::*;
use super::common::first::lemma_gkeys_order;

verus! {

/// Stored row `i` lies in sub-run `s` of code `g`.
pub open spec fn in_code(p: Seq<PartView>, g: int, s: int, i: int) -> bool {
    0 <= s < sub_count(p) && st_of(p)[s] <= i < st_of(p)[s + 1] && sg_of(p)[s] == g
}

/// `f` is the smallest canonical row number of the stored rows of code `g`.
pub open spec fn first_at(p: Seq<PartView>, g: int, f: int) -> bool {
    &&& exists|s: int, i: int| #[trigger] in_code(p, g, s, i) && u64s(p, P_ORIG)[i] == f
    &&& forall|s: int, i: int| #[trigger] in_code(p, g, s, i) ==> f <= u64s(p, P_ORIG)[i]
}

/// Canonical row `f` is the first row of the group of live code `g`.
pub proof fn lemma_first_row(p: Seq<PartView>, db: Database, g: int, f: int)
    requires bound(p, db), 0 <= g < group_count(p), live_of(p, g), first_at(p, g, f),
    ensures
        0 <= f < xs_of(db).len(),
        hit(gq(), xs_of(db)[f], key_of(p, g)),
        forall|j: int| 0 <= j < f ==> !hit(gq(), #[trigger] xs_of(db)[j], key_of(p, g)),
{
    let rels = stored_relations(db);
    let xs = xs_of(db);
    let ys = ys_of(p, rels);
    let orig = u64s(p, P_ORIG);
    let n = row_count(p);
    lemma_layout_facts(p);
    lemma_ys_perm(p, db);
    let (s, i) = choose|s: int, i: int| #[trigger] in_code(p, g, s, i) && orig[i] == f;
    lemma_ys_row(p, rels, s, i);
    lemma_yrow_hit(p, s, i, g);
    assert(xs[orig[i] as int] == ys[i]);
    assert forall|j: int| 0 <= j < f implies !hit(gq(), #[trigger] xs[j], key_of(p, g)) by {
        if hit(gq(), xs[j], key_of(p, g)) {
            lemma_permutation_facts(orig, n as nat);
            let i2 = position_of(orig, j);
            assert(0 <= i2 < n && orig[i2] == j);
            assert(xs[orig[i2] as int] == ys[i2]);
            assert(runs_partition_ok(st_of(p), sub_count(p), n));
            lemma_run_of(st_of(p), sub_count(p), n, i2);
            let s2 = run_of(st_of(p), sub_count(p), i2);
            lemma_ys_row(p, rels, s2, i2);
            lemma_yrow_hit(p, s2, i2, g);
            assert(in_code(p, g, s2, i2));
        }
    }
}

/// The first failing group decides: with `gs` failing and its first row `ja` before every row of every other
/// failing code, a count beyond int8 of `gs` is the statement's error 22003, otherwise the statement leaves the
/// capacity domain.
pub proof fn lemma_failure(p: Seq<PartView>, db: Database, gs: int, ja: int)
    requires
        bound(p, db),
        selected(p, gs),
        !code_ok(p, gs),
        0 <= ja < xs_of(db).len(),
        hit(gq(), xs_of(db)[ja], key_of(p, gs)),
        forall|c: int, j: int| #![trigger hit(gq(), xs_of(db)[j], key_of(p, c))]
            selected(p, c) && !code_ok(p, c) && c != gs && 0 <= j <= ja ==> !hit(gq(), xs_of(db)[j], key_of(p, c)),
    ensures
        count_err(p, gs) ==> denote_body(db, query_spec()) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
        !count_err(p, gs) ==> !fits_query(db, Seq::empty(), query_spec().body),
{
    let xs = xs_of(db);
    let gk = gkeys(gq(), xs);
    let rs = grs(db);
    let fs = gfs(db);
    lemma_layout_facts(p);
    lemma_group_shape(p, db);
    lemma_denote(db);
    lemma_gkeys_codes(p, db, key_of(p, gs));
    assert(gk.contains(key_of(p, gs)));
    let hs = choose|h: int| 0 <= h < gk.len() && gk[h] == key_of(p, gs);
    lemma_group_result(p, db, hs, gs);
    assert(ok_before(rs, hs)) by {
        assert forall|h: int| 0 <= h < hs implies #[trigger] rs[h] is Ok by {
            lemma_code_at(p, db, h);
            let g = code_at(p, db, h);
            if !code_ok(p, g) {
                if g == gs {
                    assert(gk[h] == gk[hs]);
                } else {
                    assert forall|j: int| 0 <= j <= ja implies !hit(gq(), #[trigger] xs[j], key_of(p, g)) by {}
                    lemma_gkeys_order(gq(), xs, key_of(p, gs), key_of(p, g), ja, hs, h);
                }
            }
            lemma_group_result(p, db, h, g);
        }
    }
    if count_err(p, gs) {
        assert forall|h: int| 0 <= h < hs implies #[trigger] rs[h] is Ok by {}
        lemma_collect_first_err(rs, hs);
    } else {
        lemma_each_capacity(rs, fs, hs);
    }
}

} // verus!
