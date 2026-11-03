//! The per-filing sums of `nf` from the `num` storage: the `num` rows of filing `adsh = a` and unit `$1` are exactly
//! the rows of the one run whose `(uom, adsh)` is `($1, a)` (runs have distinct keys), so `fsum` is a sum over that
//! run's stored positions (`lemma_fsum_run`), or 0 when no run has that key (`lemma_fsum_none`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::gendb_entry::layout::PartView;
use crate::link::query::{proj, proj_all};
use crate::link::join::{sum_of, lemma_sum_of_perm};
use crate::stores::num::interface::*;
use crate::stores::num::interface::common::runs::*;
use crate::stores::num::interface::common::text::lemma_dict_codes;
use crate::stores::num::interface::common::cols::i128_part;
use crate::stores::num::declaration::stored_cols_t0;
use crate::agent::common::sums::*;
use crate::agent::nf::*;

verus! {

/// The stored `value` coefficient at stored position `i`.
pub open spec fn value_at(np: Seq<PartView>, i: int) -> int {
    i128_part(np[P_VALUE as int])[i] as int
}

/// Run `r` holds unit `p0` and filing `a`.
pub open spec fn run_key_is(np: Seq<PartView>, r: int, p0: Seq<u8>, a: Seq<u8>) -> bool {
    run_uom_of(np, r) == p0 && run_adsh_of(np, r) == a
}

/// First and end stored position of run `r`.
pub open spec fn run_lo(np: Seq<PartView>, r: int) -> int {
    u64s(np, P_RUN_START)[r] as int
}

pub open spec fn run_hi(np: Seq<PartView>, r: int) -> int {
    u64s(np, P_RUN_START)[r + 1] as int
}

/// Sum, absolute mass and row count of the values of run `r`.
pub open spec fn val_term(np: Seq<PartView>) -> spec_fn(int) -> int {
    |i: int| value_at(np, i)
}

pub open spec fn abs_term_at(np: Seq<PartView>) -> spec_fn(int) -> int {
    |i: int| abs(value_at(np, i))
}

pub open spec fn run_sum(np: Seq<PartView>, r: int) -> int {
    rsum(run_lo(np, r), run_hi(np, r), val_term(np))
}

pub open spec fn run_mass(np: Seq<PartView>, r: int) -> int {
    rsum(run_lo(np, r), run_hi(np, r), abs_term_at(np))
}

/// The stored relation of `num` is the table itself (all 9 columns, rows of 9 values).
pub proof fn lemma_num_rel(db: Database)
    requires rows_ok(db),
    ensures crate::stores::num::declaration::stored_relations(db)[0] == num_rel(db),
{
    let nr = num_rel(db);
    let cols = stored_cols_t0();
    assert forall|i: int| 0 <= i < nr.len() implies #[trigger] proj_all(nr, cols)[i] == nr[i] by {
        assert(num_row_ok(nr[i]));
        assert(proj(nr[i], cols) =~= nr[i]);
    }
    assert(proj_all(nr, cols) =~= nr);
}

/// `sum_of` is `ssum`.
pub proof fn lemma_sum_of_ssum(rows: Seq<Row>, f: spec_fn(Row) -> int)
    ensures sum_of(rows, f) == ssum(rows, f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_sum_of_ssum(rows.drop_last(), f);
    }
}

/// Two runs with the same key are the same run.
pub proof fn lemma_run_key_unique(np: Seq<PartView>, r1: int, r2: int, p0: Seq<u8>, a: Seq<u8>)
    requires
        num_layout_ok(np),
        0 <= r1 < run_count(np), 0 <= r2 < run_count(np),
        run_key_is(np, r1, p0, a), run_key_is(np, r2, p0, a),
    ensures r1 == r2,
{
    let ru = u64s(np, P_RUN_UOM);
    let ra = u64s(np, P_RUN_ADSH);
    assert(ru[r1] < uom_count(np) && ra[r1] < adsh_count(np));
    assert(ru[r2] < uom_count(np) && ra[r2] < adsh_count(np));
    lemma_dict_codes(u64s(np, P_UOM_OFF), crate::stores::num::interface::common::text::u8_part(np[P_UOM_BYTES as int]),
        uom_count(np), ru[r1] as int, ru[r2] as int);
    lemma_dict_codes(u64s(np, P_ADSH_OFF), crate::stores::num::interface::common::text::u8_part(np[P_ADSH_BYTES as int]),
        adsh_count(np), ra[r1] as int, ra[r2] as int);
    if r1 < r2 {
        assert(pair_lt(ru[r1], ra[r1], ru[r2], ra[r2]));
    } else if r2 < r1 {
        assert(pair_lt(ru[r2], ra[r2], ru[r1], ra[r1]));
    }
}

/// The stored row at position `i` of run `r` holds the run's key and the stored value.
pub proof fn lemma_stored_row_facts(np: Seq<PartView>, rels: Seq<Seq<Row>>, r: int, i: int)
    requires represents(np, rels), 0 <= r < run_count(np), run_lo(np, r) <= i < run_hi(np, r),
    ensures
        stored_row(np, rels, i)[0] == Val::Text(run_adsh_of(np, r)),
        stored_row(np, rels, i)[5] == Val::Text(run_uom_of(np, r)),
        stored_row(np, rels, i)[7] == (Val::Num { coeff: value_at(np, i), scale: 4 }),
{
    let start = u64s(np, P_RUN_START);
    assert(start[0] == 0 && start[run_count(np)] == row_count(np));
    assert(start[r + 1] <= start[run_count(np)]);
    assert(run_cols_ok(np, stored_row(np, rels, i), r));
    assert(stored_cols_ok(np, stored_row(np, rels, i), i));
}

/// The per-filing sum as a range sum over the stored positions.
proof fn lemma_fsum_stored(db: Database, np: Seq<PartView>, p0: Seq<u8>, s: Row, w: spec_fn(Row) -> int)
    requires
        rows_ok(db),
        represents(np, crate::stores::num::declaration::stored_relations(db)),
    ensures ({
        let rels = crate::stores::num::declaration::stored_relations(db);
        fsum(p0, num_rel(db), s, w) == rsum(0, row_count(np),
            |i: int| if nmatch(p0, stored_row(np, rels, i), s) { w(stored_row(np, rels, i)) } else { 0int })
    }),
{
    let rels = crate::stores::num::declaration::stored_relations(db);
    lemma_num_rel(db);
    lemma_stored_rows_multiset(np, rels);
    let sr = Seq::new(row_count(np) as nat, |i: int| stored_row(np, rels, i));
    let f = |n: Row| if nmatch(p0, n, s) { w(n) } else { 0int };
    lemma_sum_of_perm(sr, num_rel(db), f);
    lemma_sum_of_ssum(sr, f);
    lemma_ssum_index(sr, f);
    lemma_rsum_ext(0, row_count(np), |i: int| f(sr[i]),
        |i: int| if nmatch(p0, stored_row(np, rels, i), s) { w(stored_row(np, rels, i)) } else { 0int });
}

/// The run of every stored position, and the positions of a run: `run_of(i) == r` exactly inside `[lo(r), hi(r))`.
proof fn lemma_in_run(np: Seq<PartView>, r: int, i: int)
    requires num_layout_ok(np), 0 <= r < run_count(np), 0 <= i < row_count(np),
    ensures
        0 <= run_of(u64s(np, P_RUN_START), run_count(np), i) < run_count(np),
        run_lo(np, run_of(u64s(np, P_RUN_START), run_count(np), i)) <= i
            < run_hi(np, run_of(u64s(np, P_RUN_START), run_count(np), i)),
        (run_of(u64s(np, P_RUN_START), run_count(np), i) == r) == (run_lo(np, r) <= i < run_hi(np, r)),
{
    let start = u64s(np, P_RUN_START);
    lemma_run_of(start, run_count(np), row_count(np), i);
    if run_lo(np, r) <= i < run_hi(np, r) {
        assert(in_run(start, r, i));
    }
}

/// The run with key `(p0, a)` holds exactly the `num` rows of filing `a` and unit `p0`: the per-filing sum of any
/// weight is the sum over the run's stored positions.
pub proof fn lemma_fsum_run(db: Database, np: Seq<PartView>, p0: Seq<u8>, s: Row, a: Seq<u8>, r: int,
    w: spec_fn(Row) -> int)
    requires
        rows_ok(db),
        represents(np, crate::stores::num::declaration::stored_relations(db)),
        s[0] == Val::Text(a),
        0 <= r < run_count(np),
        run_key_is(np, r, p0, a),
    ensures ({
        let rels = crate::stores::num::declaration::stored_relations(db);
        &&& 0 <= run_lo(np, r) < run_hi(np, r) <= row_count(np)
        &&& fsum(p0, num_rel(db), s, w) == rsum(run_lo(np, r), run_hi(np, r), |i: int| w(stored_row(np, rels, i)))
    }),
{
    let rels = crate::stores::num::declaration::stored_relations(db);
    let start = u64s(np, P_RUN_START);
    let n = row_count(np);
    let nr = run_count(np);
    assert(start[0] == 0 && start[nr] == n);
    assert(start[r] < start[r + 1]);
    assert(start[r + 1] <= start[nr]) by {
        if r + 1 < nr {
            assert(start[r + 1] < start[nr]);
        }
    }
    assert(start[0] <= start[r]) by {
        if r > 0 {
            assert(start[0] < start[r]);
        }
    }
    lemma_fsum_stored(db, np, p0, s, w);
    let g = |i: int| if nmatch(p0, stored_row(np, rels, i), s) { w(stored_row(np, rels, i)) } else { 0int };
    let (lo, hi) = (run_lo(np, r), run_hi(np, r));
    assert forall|i: int| 0 <= i < n && !(lo <= i < hi) implies #[trigger] g(i) == 0 by {
        lemma_in_run(np, r, i);
        let ri = run_of(start, nr, i);
        lemma_stored_row_facts(np, rels, ri, i);
        if nmatch(p0, stored_row(np, rels, i), s) {
            assert(run_key_is(np, ri, p0, a));
            lemma_run_key_unique(np, ri, r, p0, a);
        }
    }
    lemma_rsum_split(0, lo, n, g);
    lemma_rsum_split(lo, hi, n, g);
    lemma_rsum_zero(0, lo, g);
    lemma_rsum_zero(hi, n, g);
    assert forall|i: int| lo <= i < hi implies #[trigger] g(i) == w(stored_row(np, rels, i)) by {
        lemma_stored_row_facts(np, rels, r, i);
    }
    lemma_rsum_ext(lo, hi, g, |i: int| w(stored_row(np, rels, i)));
}

/// No run with key `(p0, a)`: no `num` row of filing `a` has unit `p0`.
pub proof fn lemma_fsum_none(db: Database, np: Seq<PartView>, p0: Seq<u8>, s: Row, a: Seq<u8>, w: spec_fn(Row) -> int)
    requires
        rows_ok(db),
        represents(np, crate::stores::num::declaration::stored_relations(db)),
        s[0] == Val::Text(a),
        forall|r: int| 0 <= r < run_count(np) ==> !#[trigger] run_key_is(np, r, p0, a),
    ensures fsum(p0, num_rel(db), s, w) == 0,
{
    let rels = crate::stores::num::declaration::stored_relations(db);
    let start = u64s(np, P_RUN_START);
    let n = row_count(np);
    lemma_fsum_stored(db, np, p0, s, w);
    let g = |i: int| if nmatch(p0, stored_row(np, rels, i), s) { w(stored_row(np, rels, i)) } else { 0int };
    assert forall|i: int| 0 <= i < n implies #[trigger] g(i) == 0 by {
        let ri = run_of(start, run_count(np), i);
        lemma_run_of(start, run_count(np), n, i);
        lemma_stored_row_facts(np, rels, ri, i);
        if nmatch(p0, stored_row(np, rels, i), s) {
            assert(run_key_is(np, ri, p0, a));
        }
    }
    lemma_rsum_zero(0, n, g);
}

/// The weights of `nf` on the stored rows of a run: value, absolute value, one.
pub proof fn lemma_run_weights(db: Database, np: Seq<PartView>, r: int)
    requires
        represents(np, crate::stores::num::declaration::stored_relations(db)),
        0 <= r < run_count(np),
    ensures ({
        let rels = crate::stores::num::declaration::stored_relations(db);
        &&& rsum(run_lo(np, r), run_hi(np, r), |i: int| w_val()(stored_row(np, rels, i))) == run_sum(np, r)
        &&& rsum(run_lo(np, r), run_hi(np, r), |i: int| w_abs()(stored_row(np, rels, i))) == run_mass(np, r)
        &&& rsum(run_lo(np, r), run_hi(np, r), |i: int| w_one()(stored_row(np, rels, i)))
            == run_hi(np, r) - run_lo(np, r)
    }),
{
    let rels = crate::stores::num::declaration::stored_relations(db);
    let (lo, hi) = (run_lo(np, r), run_hi(np, r));
    assert forall|i: int| lo <= i < hi implies w_val()(#[trigger] stored_row(np, rels, i)) == val_term(np)(i) by {
        lemma_stored_row_facts(np, rels, r, i);
    }
    lemma_rsum_ext(lo, hi, |i: int| w_val()(stored_row(np, rels, i)), val_term(np));
    assert forall|i: int| lo <= i < hi implies w_abs()(#[trigger] stored_row(np, rels, i)) == abs_term_at(np)(i) by {
        lemma_stored_row_facts(np, rels, r, i);
    }
    lemma_rsum_ext(lo, hi, |i: int| w_abs()(stored_row(np, rels, i)), abs_term_at(np));
    lemma_rsum_count(lo, hi, |i: int| w_one()(stored_row(np, rels, i)));
}

/// A sum of ones counts the range.
pub proof fn lemma_rsum_count(lo: int, hi: int, f: spec_fn(int) -> int)
    requires lo <= hi, forall|i: int| lo <= i < hi ==> #[trigger] f(i) == 1,
    ensures rsum(lo, hi, f) == hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_rsum_count(lo, hi - 1, f);
    }
}

} // verus!
