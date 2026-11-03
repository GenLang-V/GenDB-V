//! The Q1 scan of a row range `[lo, hi)`: the WHERE filter, the group lookup and the accumulation of every
//! qualifying row into a fixed-capacity group table (no allocation, so it runs in a worker).
//!
//! Group table: `slots[0..ng)` holds one `Acc` per group key met so far, identified by a representative row
//! (`rep`); keys are pairwise distinct and every qualifying row of `[lo, i)` has its key in the table
//! (`table_ok`). Keys of one-byte returnflag and linestatus (the common case) are found through `idx`, a direct
//! table of 65536 entries indexed by `256 * rf + ls` holding `slot + 1` (0 = absent) (`idx_ok`); other keys are
//! found by comparing bytes with every slot.
//!
//! The scan stops early when a new key does not fit (`Full`: the caller may grow `slots` and resume at the stop
//! row) or when a qualifying row's charge product leaves `i128` (`RowOverflow`: outside the capacity domain).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::query::*;
use crate::link::expr::{i128_max, fits_i128, ival};
use crate::gendb_entry::work::text_eq;
use crate::agent::normal::*;
use crate::agent::columns::*;
use crate::agent::accum::*;

verus! {

/// Entries of the one-byte key index.
pub const IDX_LEN: usize = 65536;

/// Why a scan stopped.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Stop {
    /// Every row of the range was scanned.
    Done,
    /// The row at the stop position has a new key and the table is full.
    Full,
    /// The row at the stop position qualifies and its charge product overflows `i128`.
    RowOverflow,
    /// The row at the stop position has a product outside 64 bits: the small mode does not apply.
    NeedExact,
}

/// Every used slot is in mode `small`.
pub open spec fn mode_ok(slots: Seq<Acc>, ng: int, small: bool) -> bool {
    forall|s: int| 0 <= s < ng ==> (#[trigger] slots[s]).small == small
}

/// A product inside 64 bits (exec).
#[inline(always)]
pub fn fits64(v: i128) -> (b: bool)
    ensures b == fits_i64(v as int),
    no_unwind
{
    -0x8000_0000_0000_0000i128 <= v && v <= 0x7fff_ffff_ffff_ffffi128
}

/// Returnflag and linestatus of row `r` are one byte each.
pub open spec fn short_key(c: Cols, r: int) -> bool {
    text_at(rf_view(c), r).len() == 1 && text_at(ls_view(c), r).len() == 1
}

/// Index code `256 * rf + ls` of a short key.
pub open spec fn row_code(c: Cols, r: int) -> int {
    text_at(rf_view(c), r)[0] as int * 256 + text_at(ls_view(c), r)[0] as int
}

/// The key of a slot.
pub open spec fn slot_key(c: Cols, a: Acc) -> Row {
    key_of(c, a.rep as int)
}

/// Rows `[lo, i)` of the normal form.
pub open spec fn range_rows(c: Cols, lo: int, i: int) -> Seq<Row> {
    crows(c).subrange(lo, i)
}

/// The group table after scanning `[lo, i)`.
pub open spec fn table_ok(pd: int, c: Cols, lo: int, i: int, slots: Seq<Acc>, ng: int) -> bool {
    &&& 0 <= ng <= slots.len()
    &&& forall|s: int| 0 <= s < ng ==> lo <= (#[trigger] slots[s]).rep < i && q1_qual(pd, crow(c, slots[s].rep as int))
    &&& forall|s: int| 0 <= s < ng ==> acc_ok(pd, range_rows(c, lo, i), slot_key(c, #[trigger] slots[s]), slots[s])
    &&& forall|s: int| 0 <= s < ng ==> (#[trigger] slots[s]).cnt <= i - lo
    &&& forall|s: int, t: int| 0 <= s < ng && 0 <= t < ng && s != t ==> slot_key(c, #[trigger] slots[s]) != slot_key(c, #[trigger] slots[t])
    &&& forall|r: int| lo <= r < i && q1_qual(pd, #[trigger] crow(c, r)) ==>
            exists|s: int| 0 <= s < ng && key_of(c, r) == slot_key(c, #[trigger] slots[s])
}

/// The one-byte key index of the table.
pub open spec fn idx_ok(c: Cols, slots: Seq<Acc>, ng: int, idx: Seq<usize>) -> bool {
    &&& idx.len() == IDX_LEN
    &&& forall|code: int| 0 <= code < IDX_LEN && #[trigger] idx[code] != 0 ==>
            idx[code] - 1 < ng && short_key(c, slots[idx[code] - 1].rep as int) && row_code(c, slots[idx[code] - 1].rep as int) == code
    &&& forall|s: int| 0 <= s < ng && short_key(c, (#[trigger] slots[s]).rep as int) ==> idx[row_code(c, slots[s].rep as int)] == s + 1
}

/// Short keys are equal exactly when their codes are.
pub proof fn lemma_short_keys(c: Cols, r1: int, r2: int)
    requires short_key(c, r1), short_key(c, r2),
    ensures (key_of(c, r1) == key_of(c, r2)) == (row_code(c, r1) == row_code(c, r2)),
{
    lemma_crow(c, r1);
    lemma_crow(c, r2);
    let (a1, b1) = (text_at(rf_view(c), r1), text_at(ls_view(c), r1));
    let (a2, b2) = (text_at(rf_view(c), r2), text_at(ls_view(c), r2));
    if row_code(c, r1) == row_code(c, r2) {
        assert(a1[0] == a2[0] && b1[0] == b2[0]) by (nonlinear_arith)
            requires
                a1[0] as int * 256 + b1[0] as int == a2[0] as int * 256 + b2[0] as int,
                0 <= a1[0] < 256, 0 <= a2[0] < 256, 0 <= b1[0] < 256, 0 <= b2[0] < 256;
        assert(a1 =~= a2);
        assert(b1 =~= b2);
    }
    if key_of(c, r1) == key_of(c, r2) {
        assert(key_of(c, r1)[0] == key_of(c, r2)[0]);
        assert(key_of(c, r1)[1] == key_of(c, r2)[1]);
        assert(a1 == a2);
        assert(b1 == b2);
    }
}

/// A key with the same text lengths as a short key is short.
pub proof fn lemma_short_same_key(c: Cols, r1: int, r2: int)
    requires key_of(c, r1) == key_of(c, r2),
    ensures short_key(c, r1) == short_key(c, r2), short_key(c, r1) ==> row_code(c, r1) == row_code(c, r2),
{
    lemma_crow(c, r1);
    lemma_crow(c, r2);
    assert(key_of(c, r1)[0] == key_of(c, r2)[0]);
    assert(key_of(c, r1)[1] == key_of(c, r2)[1]);
}

/// Indexing the scanned rows.
pub proof fn lemma_range_rows(c: Cols, lo: int, i: int)
    requires 0 <= lo <= i < c.n,
    ensures
        range_rows(c, lo, i + 1) == range_rows(c, lo, i).push(crow(c, i)),
        range_rows(c, lo, i).len() == i - lo,
        forall|j: int| 0 <= j < i - lo ==> #[trigger] range_rows(c, lo, i)[j] == crow(c, lo + j),
{
    lemma_crows(c);
    assert(range_rows(c, lo, i + 1) =~= range_rows(c, lo, i).push(crow(c, i)));
}

/// No row of `[lo, i)` belongs to group `k`: its accumulators are zero.
pub proof fn lemma_acc_absent(pd: int, c: Cols, lo: int, i: int, k: Row, rep: usize, small: bool)
    requires
        0 <= lo <= i <= c.n,
        forall|r: int| lo <= r < i ==> !hit(q1_spec(pd), #[trigger] crow(c, r), k),
    ensures acc_ok(pd, range_rows(c, lo, i), k, acc_zero(rep, small)),
    decreases i - lo,
{
    lemma_crows(c);
    if i == lo {
        assert(range_rows(c, lo, i) =~= Seq::<Row>::empty());
        lemma_acc_empty(pd, k, rep, small);
    } else {
        lemma_acc_absent(pd, c, lo, i - 1, k, rep, small);
        lemma_range_rows(c, lo, i - 1);
        lemma_acc_miss(pd, range_rows(c, lo, i - 1), crow(c, i - 1), k, acc_zero(rep, small));
    }
}

/// The empty table before any row.
pub proof fn lemma_table_init(pd: int, c: Cols, lo: int, slots: Seq<Acc>, idx: Seq<usize>)
    requires idx.len() == IDX_LEN, forall|code: int| 0 <= code < IDX_LEN ==> #[trigger] idx[code] == 0,
    ensures table_ok(pd, c, lo, lo, slots, 0), idx_ok(c, slots, 0, idx),
{
}

/// A row that does not qualify leaves the table unchanged.
pub proof fn lemma_table_skip(pd: int, c: Cols, lo: int, i: int, slots: Seq<Acc>, ng: int)
    requires
        0 <= lo <= i < c.n,
        table_ok(pd, c, lo, i, slots, ng),
        !q1_qual(pd, crow(c, i)),
    ensures table_ok(pd, c, lo, i + 1, slots, ng),
{
    lemma_range_rows(c, lo, i);
    let g = q1_spec(pd);
    assert forall|s: int| 0 <= s < ng implies acc_ok(pd, range_rows(c, lo, i + 1), slot_key(c, #[trigger] slots[s]), slots[s]) by {
        lemma_acc_miss(pd, range_rows(c, lo, i), crow(c, i), slot_key(c, slots[s]), slots[s]);
    }
}

/// The accumulator a qualifying row of key `key_of(c, i)` starts from: its slot's, or zero for a new key.
pub proof fn lemma_table_hit(pd: int, c: Cols, lo: int, i: int, slots: Seq<Acc>, ng: int, s0: int, b: Acc, ng2: int, small: bool)
    requires
        0 <= lo <= i < c.n,
        table_ok(pd, c, lo, i, slots, ng),
        q1_qual(pd, crow(c, i)),
        0 <= s0 < slots.len(),
        (s0 < ng && ng2 == ng && slot_key(c, slots[s0]) == key_of(c, i))
            || (s0 == ng && ng2 == ng + 1 && forall|t: int| 0 <= t < ng ==> slot_key(c, #[trigger] slots[t]) != key_of(c, i)),
        b.rep == (if s0 < ng { slots[s0].rep } else { i as usize }),
        acc_step(if s0 < ng { slots[s0] } else { acc_zero(i as usize, small) }, b,
            q1_arg(0, crow(c, i)), q1_arg(1, crow(c, i)), q1_arg(6, crow(c, i)), q1_arg(2, crow(c, i)), q1_arg(3, crow(c, i))),
    ensures table_ok(pd, c, lo, i + 1, slots.update(s0, b), ng2),
{
    let g = q1_spec(pd);
    let rs = range_rows(c, lo, i);
    let x = crow(c, i);
    let k = key_of(c, i);
    let s2 = slots.update(s0, b);
    lemma_range_rows(c, lo, i);
    lemma_crows(c);
    assert(slot_key(c, b) == k);
    let a0 = if s0 < ng { slots[s0] } else { acc_zero(i as usize, small) };
    if s0 == ng {
        assert forall|r: int| lo <= r < i implies !hit(g, #[trigger] crow(c, r), k) by {
            if hit(g, crow(c, r), k) {
                let t = choose|t: int| 0 <= t < ng && key_of(c, r) == slot_key(c, #[trigger] slots[t]);
                assert(slot_key(c, slots[t]) != k);
            }
        }
        lemma_acc_absent(pd, c, lo, i, k, i as usize, small);
    }
    assert(acc_ok(pd, rs, k, a0));
    assert(hit(g, x, k));
    lemma_acc_hit(pd, rs, x, k, a0, b);
    assert forall|s: int| 0 <= s < ng2 implies acc_ok(pd, range_rows(c, lo, i + 1), slot_key(c, #[trigger] s2[s]), s2[s]) by {
        if s != s0 {
            assert(s2[s] == slots[s]);
            assert(slot_key(c, slots[s]) != k);
            lemma_acc_miss(pd, rs, x, slot_key(c, slots[s]), slots[s]);
        }
    }
    assert forall|s: int| 0 <= s < ng2 implies (#[trigger] s2[s]).cnt <= i + 1 - lo by {
        if s != s0 {
            assert(s2[s] == slots[s]);
        }
    }
    assert forall|s: int, t: int| 0 <= s < ng2 && 0 <= t < ng2 && s != t implies
        slot_key(c, #[trigger] s2[s]) != slot_key(c, #[trigger] s2[t]) by {
        if s == s0 {
            assert(s2[t] == slots[t]);
        } else if t == s0 {
            assert(s2[s] == slots[s]);
        } else {
            assert(s2[s] == slots[s] && s2[t] == slots[t]);
        }
    }
    assert forall|r: int| lo <= r < i + 1 && q1_qual(pd, #[trigger] crow(c, r)) implies
        exists|s: int| 0 <= s < ng2 && key_of(c, r) == slot_key(c, #[trigger] s2[s]) by {
        if r == i {
            assert(key_of(c, r) == slot_key(c, s2[s0]));
        } else {
            let t = choose|t: int| 0 <= t < ng && key_of(c, r) == slot_key(c, #[trigger] slots[t]);
            if t == s0 {
                assert(slot_key(c, s2[s0]) == slot_key(c, slots[s0]));
            } else {
                assert(s2[t] == slots[t]);
            }
        }
    }
    assert forall|s: int| 0 <= s < ng2 implies lo <= (#[trigger] s2[s]).rep < i + 1 && q1_qual(pd, crow(c, s2[s].rep as int)) by {
        if s != s0 {
            assert(s2[s] == slots[s]);
        }
    }
}

/// One slot of the table: its accumulators, its count bound and its representative.
pub proof fn lemma_table_slot(pd: int, c: Cols, lo: int, i: int, slots: Seq<Acc>, ng: int, s: int)
    requires table_ok(pd, c, lo, i, slots, ng), 0 <= s < ng,
    ensures
        acc_ok(pd, range_rows(c, lo, i), slot_key(c, slots[s]), slots[s]),
        slots[s].cnt <= i - lo,
        lo <= slots[s].rep < i,
        ng <= slots.len(),
{
}

/// The index after an update of slot `s0` (an existing slot keeps its key; a new slot of a short key is entered).
pub proof fn lemma_idx_hit(c: Cols, slots: Seq<Acc>, ng: int, idx: Seq<usize>, s0: int, b: Acc, ng2: int, idx2: Seq<usize>)
    requires
        idx_ok(c, slots, ng, idx),
        0 <= s0 < slots.len(),
        0 <= ng <= slots.len(),
        (s0 < ng && ng2 == ng && slot_key(c, b) == slot_key(c, slots[s0]) && b.rep == slots[s0].rep && idx2 == idx)
            || (s0 == ng && ng2 == ng + 1 && forall|t: int| 0 <= t < ng ==> slot_key(c, #[trigger] slots[t]) != slot_key(c, b)),
        s0 == ng ==> (if short_key(c, b.rep as int) {
            0 <= row_code(c, b.rep as int) < IDX_LEN && idx2 == idx.update(row_code(c, b.rep as int), (s0 + 1) as usize)
        } else {
            idx2 == idx
        }),
        ng2 <= usize::MAX,
    ensures idx_ok(c, slots.update(s0, b), ng2, idx2),
{
    let s2 = slots.update(s0, b);
    if s0 < ng {
        assert forall|code: int| 0 <= code < IDX_LEN && #[trigger] idx2[code] != 0 implies
            idx2[code] - 1 < ng2 && short_key(c, s2[idx2[code] - 1].rep as int) && row_code(c, s2[idx2[code] - 1].rep as int) == code by {
            let t = idx[code] - 1;
            if t != s0 {
                assert(s2[t] == slots[t]);
            }
        }
        assert forall|s: int| 0 <= s < ng2 && short_key(c, (#[trigger] s2[s]).rep as int) implies idx2[row_code(c, s2[s].rep as int)] == s + 1 by {
            if s != s0 {
                assert(s2[s] == slots[s]);
            }
        }
    } else {
        let r = b.rep as int;
        assert forall|code: int| 0 <= code < IDX_LEN && #[trigger] idx2[code] != 0 implies
            idx2[code] - 1 < ng2 && short_key(c, s2[idx2[code] - 1].rep as int) && row_code(c, s2[idx2[code] - 1].rep as int) == code by {
            if short_key(c, r) && code == row_code(c, r) {
                assert(idx2[code] == s0 + 1);
            } else {
                assert(idx2[code] == idx[code]);
                let t = idx[code] - 1;
                assert(t < ng);
                assert(s2[t] == slots[t]);
            }
        }
        assert forall|s: int| 0 <= s < ng2 && short_key(c, (#[trigger] s2[s]).rep as int) implies idx2[row_code(c, s2[s].rep as int)] == s + 1 by {
            if s != s0 {
                assert(s2[s] == slots[s]);
                let rt = slots[s].rep as int;
                if short_key(c, r) {
                    if row_code(c, rt) == row_code(c, r) {
                        lemma_short_keys(c, rt, r);
                        assert(slot_key(c, slots[s]) == slot_key(c, b));
                    }
                }
            }
        }
    }
}

/// The two numeric(15,2) products of one row: `dp = e * (100 - d)` always fits `i128`.
pub proof fn lemma_dp_bound(e: int, d: int)
    requires coeff_ok_int(e), coeff_ok_int(d),
    ensures
        -0x7fff_ffff_ffff_ffff <= e <= 0x7fff_ffff_ffff_ffff,
        -0x7fff_ffff_ffff_ffff <= 100 - d <= 0x7fff_ffff_ffff_ffff,
        -0x4000_0000_0000_0000_0000_0000_0000_0000 < e * (100 - d) < 0x4000_0000_0000_0000_0000_0000_0000_0000,
{
    let m = 100 - d;
    assert(-1_000_000_000_000_100 < m < 1_000_000_000_000_100);
    assert(-1_000_000_000_000_100 * 1_000_000_000_000_100 < e * m < 1_000_000_000_000_100 * 1_000_000_000_000_100) by (nonlinear_arith)
        requires -1_000_000_000_000_000 < e < 1_000_000_000_000_000, -1_000_000_000_000_100 < m < 1_000_000_000_000_100;
}

/// A product of a 64-bit value and a value below 2^62 in absolute value fits `i128`.
pub proof fn lemma_small_product(a: int, b: int)
    requires
        -0x8000_0000_0000_0000 <= a <= 0x7fff_ffff_ffff_ffff,
        -0x4000_0000_0000_0000 <= b <= 0x4000_0000_0000_0000,
    ensures -0x2000_0000_0000_0000_0000_0000_0000_0000 <= a * b <= 0x2000_0000_0000_0000_0000_0000_0000_0000,
{
    assert(-0x2000_0000_0000_0000_0000_0000_0000_0000 <= a * b <= 0x2000_0000_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
        requires -0x8000_0000_0000_0000 <= a <= 0x8000_0000_0000_0000, -0x4000_0000_0000_0000 <= b <= 0x4000_0000_0000_0000;
}

/// Row `i`'s normal-form arguments are its column coefficients and products.
pub proof fn lemma_row_args(c: Cols, i: int)
    ensures
        q1_arg(0, crow(c, i)) == c.qty@[i] as int,
        q1_arg(1, crow(c, i)) == c.price@[i] as int,
        q1_arg(6, crow(c, i)) == c.disc@[i] as int,
        q1_arg(2, crow(c, i)) == c.price@[i] as int * (100 - c.disc@[i] as int),
        q1_arg(3, crow(c, i)) == c.price@[i] as int * (100 - c.disc@[i] as int) * (100 + c.tax@[i] as int),
        charge(crow(c, i)) == q1_arg(3, crow(c, i)),
        q1_qual(0, crow(c, i)) == (day_of(c.ship@[i]) <= 0),
{
    lemma_crow(c, i);
}

/// The row's key in the table: `Some(slot)` with the same key, or `None` when no slot has it; and the row's index
/// code (`IDX_LEN` when the key is not short).
#[inline(always)]
fn find_slot(c: &Cols, i: usize, slots: &Vec<Acc>, ng: usize, idx: &Vec<usize>) -> (r: (Option<usize>, usize))
    requires
        cols_wf(*c),
        i < c.n,
        ng <= slots.len(),
        forall|s: int| 0 <= s < ng ==> (#[trigger] slots@[s]).rep < c.n,
        idx_ok(*c, slots@, ng as int, idx@),
    ensures
        r.0 matches Some(s) ==> s < ng && slot_key(*c, slots@[s as int]) == key_of(*c, i as int),
        r.0 is None ==> forall|t: int| 0 <= t < ng ==> slot_key(*c, #[trigger] slots@[t]) != key_of(*c, i as int),
        r.1 <= IDX_LEN,
        r.1 < IDX_LEN <==> short_key(*c, i as int),
        r.1 < IDX_LEN ==> r.1 == row_code(*c, i as int),
    no_unwind
{
    let ghost rv = rf_view(*c);
    let ghost lv = ls_view(*c);
    proof {
        lemma_crow(*c, i as int);
        assert(0 <= rv.offsets[i as int] <= rv.offsets[i + 1] <= rv.bytes.len());
        assert(0 <= lv.offsets[i as int] <= lv.offsets[i + 1] <= lv.bytes.len());
    }
    let a0 = c.rf_offsets[i];
    let a1 = c.rf_offsets[i + 1];
    let b0 = c.ls_offsets[i];
    let b1 = c.ls_offsets[i + 1];
    if a1 - a0 == 1 && b1 - b0 == 1 {
        let x = c.rf_bytes[a0 as usize];
        let y = c.ls_bytes[b0 as usize];
        let code = (x as usize) * 256 + (y as usize);
        proof {
            assert(code < IDX_LEN) by (nonlinear_arith) requires code == x as int * 256 + y as int, 0 <= x < 256, 0 <= y < 256;
            assert(text_at(rv, i as int)[0] == x);
            assert(text_at(lv, i as int)[0] == y);
            assert(short_key(*c, i as int));
            assert(row_code(*c, i as int) == code);
        }
        let s = idx[code];
        if s != 0 {
            proof {
                lemma_short_keys(*c, slots@[s - 1].rep as int, i as int);
            }
            return (Some((s - 1) as usize), code);
        }
        proof {
            assert forall|t: int| 0 <= t < ng implies slot_key(*c, #[trigger] slots@[t]) != key_of(*c, i as int) by {
                if slot_key(*c, slots@[t]) == key_of(*c, i as int) {
                    lemma_short_same_key(*c, slots@[t].rep as int, i as int);
                }
            }
        }
        return (None, code);
    }
    // A key that is not one byte each: compare bytes with every slot.
    proof {
        assert(!short_key(*c, i as int));
    }
    let rf = crate::link::query::TextCol { offsets: c.rf_offsets, bytes: c.rf_bytes };
    let ls = crate::link::query::TextCol { offsets: c.ls_offsets, bytes: c.ls_bytes };
    let mut t: usize = 0;
    while t < ng
        invariant
            t <= ng,
            ng <= slots.len(),
            cols_wf(*c),
            i < c.n,
            rf@ == rv,
            ls@ == lv,
            rv == rf_view(*c),
            lv == ls_view(*c),
            !short_key(*c, i as int),
            forall|s: int| 0 <= s < ng ==> (#[trigger] slots@[s]).rep < c.n,
            forall|s: int| 0 <= s < t ==> slot_key(*c, #[trigger] slots@[s]) != key_of(*c, i as int),
        decreases ng - t,
    {
        let r = slots[t].rep;
        proof {
            assert(slots@[t as int].rep < c.n);
            assert(0 <= rv.offsets[r as int] <= rv.offsets[r + 1] <= rv.bytes.len());
            assert(0 <= lv.offsets[r as int] <= lv.offsets[r + 1] <= lv.bytes.len());
            lemma_crow(*c, r as int);
        }
        if text_eq(&rf, r, &rf, i) && text_eq(&ls, r, &ls, i) {
            return (Some(t), IDX_LEN);
        }
        proof {
            if slot_key(*c, slots@[t as int]) == key_of(*c, i as int) {
                assert(key_of(*c, r as int)[0] == key_of(*c, i as int)[0]);
                assert(key_of(*c, r as int)[1] == key_of(*c, i as int)[1]);
            }
        }
        t = t + 1;
    }
    (None, IDX_LEN)
}

/// The two products of a row from its numeric(15,2) coefficients: `dp = e * (100 - d)` (always in `i128`) and
/// `ch = dp * (100 + t)`, or `None` when `ch` leaves `i128`.
#[inline(always)]
fn products(e: i64, d: i64, t: i64) -> (r: Option<(i128, i128)>)
    requires coeff_ok_int(e as int), coeff_ok_int(d as int), coeff_ok_int(t as int),
    ensures
        r matches Some(v) ==> v.0 as int == e as int * (100 - d as int) && v.1 as int == e as int * (100 - d as int) * (100 + t as int)
            && v.0 != i128::MIN,
        r is None ==> !fits_i128(e as int * (100 - d as int) * (100 + t as int)),
    no_unwind
{
    proof {
        lemma_dp_bound(e as int, d as int);
    }
    // e * (100 - d): both factors fit 64 bits (|e| < 10^15), so this is one widening multiply.
    let dp: i128 = (e as i128) * ((100 - d) as i128);
    let w: i64 = 100 + t;
    if -0x8000_0000_0000_0000i128 <= dp && dp <= 0x7fff_ffff_ffff_ffffi128 {
        proof {
            lemma_small_product(dp as int, w as int);
        }
        Some((dp, (dp as i64 as i128) * (w as i128)))
    } else {
        match dp.checked_mul(w as i128) {
            Some(v) => Some((dp, v)),
            None => None,
        }
    }
}

/// A numeric(15,2) coefficient as a 64-bit value.
#[inline(always)]
pub fn c64(x: i128) -> (r: i64)
    requires coeff_ok(x),
    ensures r as int == x as int, coeff_ok_int(r as int),
    no_unwind
{
    x as i64
}

/// The aggregate inputs of row `i`: quantity, price, discount, disc_price and charge coefficients, or `None` when
/// the charge product leaves `i128`.
#[inline(always)]
fn row_values(c: &Cols, i: usize) -> (r: Option<(i64, i64, i64, i128, i128)>)
    requires cols_wf(*c), i < c.n,
    ensures
        r matches Some(v) ==> {
            &&& v.0 as int == c.qty@[i as int] as int && v.1 as int == c.price@[i as int] as int && v.2 as int == c.disc@[i as int] as int
            &&& v.3 as int == q1_arg(2, crow(*c, i as int)) && v.4 as int == q1_arg(3, crow(*c, i as int))
            &&& v.3 != i128::MIN
            &&& coeff_ok_int(v.0 as int) && coeff_ok_int(v.1 as int) && coeff_ok_int(v.2 as int)
        },
        r is None ==> !fits_i128(charge(crow(*c, i as int))),
    no_unwind
{
    proof {
        lemma_crow(*c, i as int);
        lemma_row_args(*c, i as int);
        assert(coeff_ok(c.qty@[i as int]) && coeff_ok(c.price@[i as int]));
        assert(coeff_ok(c.disc@[i as int]) && coeff_ok(c.tax@[i as int]));
    }
    let q = c64(c.qty[i]);
    let e = c64(c.price[i]);
    let d = c64(c.disc[i]);
    let t = c64(c.tax[i]);
    match products(e, d, t) {
        Some((dp, ch)) => Some((q, e, d, dp, ch)),
        None => None,
    }
}

/// Accumulates one qualifying row `i` into the table (or reports `Full` / `RowOverflow` without changing it).
#[inline(always)]
fn add_qualifying_row(
    c: &Cols,
    lo: usize,
    i: usize,
    Ghost(pd): Ghost<int>,
    small: bool,
    slots: &mut Vec<Acc>,
    ng: &mut usize,
    idx: &mut Vec<usize>,
) -> (r: Stop)
    requires
        cols_wf(*c),
        lo <= i < c.n,
        q1_qual(pd, crow(*c, i as int)),
        table_ok(pd, *c, lo as int, i as int, old(slots)@, *old(ng) as int),
        idx_ok(*c, old(slots)@, *old(ng) as int, old(idx)@),
        mode_ok(old(slots)@, *old(ng) as int, small),
    ensures
        final(slots)@.len() == old(slots)@.len(),
        r == Stop::Done ==> table_ok(pd, *c, lo as int, i + 1, final(slots)@, *final(ng) as int)
            && idx_ok(*c, final(slots)@, *final(ng) as int, final(idx)@)
            && mode_ok(final(slots)@, *final(ng) as int, small),
        r == Stop::NeedExact ==> small,
        r != Stop::Done ==> final(slots)@ == old(slots)@ && *final(ng) == *old(ng) && final(idx)@ == old(idx)@,
        *final(ng) >= *old(ng),
        r == Stop::Full ==> *final(ng) == final(slots)@.len(),
        r == Stop::RowOverflow ==> !fits_i128(charge(crow(*c, i as int))),
    no_unwind
{
    let cap = slots.len();
    let (q, e, d, dp, ch) = match row_values(c, i) {
        Some(v) => v,
        None => return Stop::RowOverflow,
    };
    if small && !(fits64(dp) && fits64(ch)) {
        return Stop::NeedExact;
    }
    proof {
        lemma_crow(*c, i as int);
        lemma_row_args(*c, i as int);
        assert forall|s: int| 0 <= s < *ng implies (#[trigger] slots@[s]).rep < c.n by {}
    }
    let (found, code) = find_slot(c, i, slots, *ng, idx);
    let ghost slots0 = slots@;
    let ghost ng0 = *ng as int;
    let ghost idx0 = idx@;
    match found {
        Some(s) => {
            proof {
                lemma_acc_inv(pd, range_rows(*c, lo as int, i as int), slot_key(*c, slots@[s as int]), slots@[s as int]);
                assert(slots@[s as int].cnt <= i - lo);
            }
            add_row_at(slots, s, q, e, d, dp, ch);
            proof {
                let b = slots@[s as int];
                assert(slots@ == slots0.update(s as int, b));
                lemma_table_hit(pd, *c, lo as int, i as int, slots0, ng0, s as int, b, ng0, small);
                lemma_idx_hit(*c, slots0, ng0, idx0, s as int, b, ng0, idx@);
                assert forall|t: int| 0 <= t < ng0 implies (#[trigger] slots@[t]).small == small by {
                    if t != s { assert(slots@[t] == slots0[t]); }
                }
            }
        },
        None => {
            if *ng == cap {
                return Stop::Full;
            }
            let s0 = *ng;
            slots[s0] = new_acc(i, small);
            add_row_at(slots, s0, q, e, d, dp, ch);
            if code < IDX_LEN {
                idx[code] = s0 + 1;
            }
            *ng = s0 + 1;
            proof {
                let b = slots@[s0 as int];
                assert(slots@ =~= slots0.update(s0 as int, b));
                assert(slot_key(*c, b) == key_of(*c, i as int));
                lemma_table_hit(pd, *c, lo as int, i as int, slots0, ng0, s0 as int, b, *ng as int, small);
                lemma_idx_hit(*c, slots0, ng0, idx0, s0 as int, b, *ng as int, idx@);
                assert forall|t: int| 0 <= t < *ng implies (#[trigger] slots@[t]).small == small by {
                    if t != s0 { assert(slots@[t] == slots0[t]); }
                }
            }
        },
    }
    Stop::Done
}

/// The columns of rows `[lo, hi)` as sub-slices: index `j` is row `lo + j` (offsets: `hi - lo + 1` entries); the
/// bytes parts are whole. Indexing sub-slices of the loop's length lets the compiler drop bounds checks.
#[derive(Clone, Copy)]
pub struct Span {
    pub qty: &'static [i128],
    pub price: &'static [i128],
    pub disc: &'static [i128],
    pub tax: &'static [i128],
    pub ship: &'static [i32],
    pub rf_offsets: &'static [i64],
    pub ls_offsets: &'static [i64],
    pub rf_bytes: &'static [u8],
    pub ls_bytes: &'static [u8],
}

pub open spec fn span_ok(c: Cols, lo: int, hi: int, sp: Span) -> bool {
    &&& sp.qty@ == c.qty@.subrange(lo, hi)
    &&& sp.price@ == c.price@.subrange(lo, hi)
    &&& sp.disc@ == c.disc@.subrange(lo, hi)
    &&& sp.tax@ == c.tax@.subrange(lo, hi)
    &&& sp.ship@ == c.ship@.subrange(lo, hi)
    &&& sp.rf_offsets@ == c.rf_offsets@.subrange(lo, hi + 1)
    &&& sp.ls_offsets@ == c.ls_offsets@.subrange(lo, hi + 1)
    &&& sp.rf_bytes@ == c.rf_bytes@
    &&& sp.ls_bytes@ == c.ls_bytes@
}

/// Elements `[lo, hi)` of a slice.
#[inline(always)]
pub fn sub<T>(s: &'static [T], lo: usize, hi: usize) -> (r: &'static [T])
    requires lo <= hi <= s@.len(),
    ensures r@ == s@.subrange(lo as int, hi as int),
    no_unwind
{
    let (_, t) = s.split_at(lo);
    let (r, _) = t.split_at(hi - lo);
    proof {
        assert(r@ =~= s@.subrange(lo as int, hi as int));
    }
    r
}

/// The span of rows `[lo, hi)`.
#[inline(always)]
pub fn span_of(c: &Cols, lo: usize, hi: usize) -> (sp: Span)
    requires cols_wf(*c), lo <= hi <= c.n,
    ensures span_ok(*c, lo as int, hi as int, sp),
    no_unwind
{
    proof {
        vstd::slice::axiom_spec_len(c.rf_offsets);
    }
    Span {
        qty: sub(c.qty, lo, hi),
        price: sub(c.price, lo, hi),
        disc: sub(c.disc, lo, hi),
        tax: sub(c.tax, lo, hi),
        ship: sub(c.ship, lo, hi),
        rf_offsets: sub(c.rf_offsets, lo, hi + 1),
        ls_offsets: sub(c.ls_offsets, lo, hi + 1),
        rf_bytes: c.rf_bytes,
        ls_bytes: c.ls_bytes,
    }
}

/// The index code of row `lo + j` when its returnflag and linestatus are one byte each.
#[inline(always)]
pub fn short_code(c: &Cols, sp: &Span, lo: usize, hi: usize, j: usize, a0: i64, a1: i64, b0: i64, b1: i64) -> (r: Option<usize>)
    requires
        cols_wf(*c),
        lo <= hi <= c.n,
        j < hi - lo,
        span_ok(*c, lo as int, hi as int, *sp),
        a0 == sp.rf_offsets@[j as int], a1 == sp.rf_offsets@[j + 1],
        b0 == sp.ls_offsets@[j as int], b1 == sp.ls_offsets@[j + 1],
    ensures
        r matches Some(code) ==> code < IDX_LEN && short_key(*c, lo + j) && row_code(*c, lo + j) == code,
    no_unwind
{
    let ghost i = lo + j;
    let ghost rv = rf_view(*c);
    let ghost lv = ls_view(*c);
    proof {
        assert(0 <= rv.offsets[i] <= rv.offsets[i + 1] <= rv.bytes.len());
        assert(0 <= lv.offsets[i] <= lv.offsets[i + 1] <= lv.bytes.len());
        assert(sp.rf_offsets@[j as int] == rv.offsets[i] && sp.rf_offsets@[j + 1] == rv.offsets[i + 1]);
        assert(sp.ls_offsets@[j as int] == lv.offsets[i] && sp.ls_offsets@[j + 1] == lv.offsets[i + 1]);
    }
    if a1 - a0 != 1 || b1 - b0 != 1 {
        return None;
    }
    let x = sp.rf_bytes[a0 as usize];
    let y = sp.ls_bytes[b0 as usize];
    let code = (x as usize) * 256 + (y as usize);
    proof {
        assert(code < IDX_LEN) by (nonlinear_arith) requires code == x as int * 256 + y as int, 0 <= x < 256, 0 <= y < 256;
        assert(text_at(rv, i)[0] == x);
        assert(text_at(lv, i)[0] == y);
    }
    Some(code)
}

/// Fast path for a qualifying row `i = lo + j` whose one-byte key already has a slot: `0` added, `1` not handled
/// here (the general path takes the row), `2` the charge overflows `i128`.
#[inline(always)]
fn add_known_row(
    c: &Cols,
    sp: &Span,
    lo: usize,
    hi: usize,
    j: usize,
    a0: i64,
    a1: i64,
    b0: i64,
    b1: i64,
    Ghost(pd): Ghost<int>,
    small: bool,
    slots: &mut Vec<Acc>,
    ng: usize,
    idx: &Vec<usize>,
) -> (r: u8)
    requires
        cols_wf(*c),
        lo <= hi <= c.n,
        j < hi - lo,
        span_ok(*c, lo as int, hi as int, *sp),
        a0 == sp.rf_offsets@[j as int], a1 == sp.rf_offsets@[j + 1],
        b0 == sp.ls_offsets@[j as int], b1 == sp.ls_offsets@[j + 1],
        q1_qual(pd, crow(*c, lo + j)),
        table_ok(pd, *c, lo as int, lo + j, old(slots)@, ng as int),
        idx_ok(*c, old(slots)@, ng as int, idx@),
        mode_ok(old(slots)@, ng as int, small),
    ensures
        final(slots)@.len() == old(slots)@.len(),
        r == 0 ==> table_ok(pd, *c, lo as int, lo + j + 1, final(slots)@, ng as int) && idx_ok(*c, final(slots)@, ng as int, idx@)
            && mode_ok(final(slots)@, ng as int, small),
        r != 0 ==> final(slots)@ == old(slots)@,
        r == 2 ==> !fits_i128(charge(crow(*c, lo + j))),
        r == 3 ==> small,
    no_unwind
{
    hide(table_ok);
    hide(crow);
    let ghost i = lo + j;
    let code = match short_code(c, sp, lo, hi, j, a0, a1, b0, b1) {
        Some(code) => code,
        None => return 1,
    };
    let s = idx[code];
    if s == 0 {
        return 1;
    }
    let s = s - 1;
    proof {
        lemma_crow(*c, i);
        lemma_row_args(*c, i);
        lemma_short_keys(*c, slots@[s as int].rep as int, i);
        assert(sp.qty@[j as int] == c.qty@[i] && sp.price@[j as int] == c.price@[i]);
        assert(sp.disc@[j as int] == c.disc@[i] && sp.tax@[j as int] == c.tax@[i]);
        assert(coeff_ok(c.qty@[i]) && coeff_ok(c.price@[i]) && coeff_ok(c.disc@[i]) && coeff_ok(c.tax@[i]));
    }
    let q = c64(sp.qty[j]);
    let e = c64(sp.price[j]);
    let d = c64(sp.disc[j]);
    let (dp, ch) = match products(e, d, c64(sp.tax[j])) {
        Some(v) => v,
        None => return 2,
    };
    if small && !(fits64(dp) && fits64(ch)) {
        return 3;
    }
    let ghost slots0 = slots@;
    proof {
        lemma_table_slot(pd, *c, lo as int, i, slots@, ng as int, s as int);
        lemma_acc_inv(pd, range_rows(*c, lo as int, i), slot_key(*c, slots@[s as int]), slots@[s as int]);
    }
    add_row_at(slots, s, q, e, d, dp, ch);
    proof {
        let b = slots@[s as int];
        assert(slots@ == slots0.update(s as int, b));
        lemma_table_hit(pd, *c, lo as int, i, slots0, ng as int, s as int, b, ng as int, small);
        lemma_idx_hit(*c, slots0, ng as int, idx@, s as int, b, ng as int, idx@);
        assert forall|t: int| 0 <= t < ng implies (#[trigger] slots@[t]).small == small by {
            if t != s { assert(slots@[t] == slots0[t]); }
        }
    }
    0
}

/// Accumulates rows `[start, hi)` of the range that began at `lo` into the table; see the module header.
pub fn scan_range(
    c: &Cols,
    lo: usize,
    start: usize,
    hi: usize,
    limit: i32,
    Ghost(pd): Ghost<int>,
    small: bool,
    slots: &mut Vec<Acc>,
    ng: &mut usize,
    idx: &mut Vec<usize>,
) -> (r: (Stop, usize))
    requires
        cols_wf(*c),
        lo <= start <= hi <= c.n,
        limit as int == pd + 10957,
        table_ok(pd, *c, lo as int, start as int, old(slots)@, *old(ng) as int),
        idx_ok(*c, old(slots)@, *old(ng) as int, old(idx)@),
        mode_ok(old(slots)@, *old(ng) as int, small),
    ensures
        final(slots)@.len() == old(slots)@.len(),
        start <= r.1 <= hi,
        table_ok(pd, *c, lo as int, r.1 as int, final(slots)@, *final(ng) as int),
        idx_ok(*c, final(slots)@, *final(ng) as int, final(idx)@),
        mode_ok(final(slots)@, *final(ng) as int, small),
        r.0 == Stop::NeedExact ==> r.1 < hi && small,
        r.0 == Stop::Done ==> r.1 == hi,
        r.0 == Stop::Full ==> r.1 < hi && *final(ng) == final(slots)@.len(),
        r.0 == Stop::Full && *old(ng) < old(slots)@.len() ==> r.1 > start,
        r.0 == Stop::RowOverflow ==> r.1 < hi && q1_qual(pd, crow(*c, r.1 as int)) && !fits_i128(charge(crow(*c, r.1 as int))),
    no_unwind
{
    hide(table_ok);
    hide(idx_ok);
    hide(mode_ok);
    let cap = slots.len();
    let sp = span_of(c, lo, hi);
    let len = hi - lo;
    let mut j = start - lo;
    proof {
        assert(sp.rf_offsets@.len() == len + 1 && sp.ls_offsets@.len() == len + 1);
    }
    // Row j's start offsets, carried from the previous row's end offsets.
    let mut a0 = sp.rf_offsets[j];
    let mut b0 = sp.ls_offsets[j];
    while j < len
        invariant
            cols_wf(*c),
            lo <= start <= hi <= c.n,
            len == hi - lo,
            start - lo <= j <= len,
            span_ok(*c, lo as int, hi as int, sp),
            sp.rf_offsets@.len() == len + 1 && sp.ls_offsets@.len() == len + 1,
            a0 == sp.rf_offsets@[j as int],
            b0 == sp.ls_offsets@[j as int],
            limit as int == pd + 10957,
            slots@.len() == cap,
            cap == old(slots)@.len(),
            j == start - lo ==> *ng == *old(ng),
            table_ok(pd, *c, lo as int, lo + j, slots@, *ng as int),
            idx_ok(*c, slots@, *ng as int, idx@),
            mode_ok(slots@, *ng as int, small),
        decreases len - j,
    {
        proof {
            lemma_crow(*c, lo + j);
            assert(sp.ship@[j as int] == c.ship@[lo + j]);
        }
        let a1 = sp.rf_offsets[j + 1];
        let b1 = sp.ls_offsets[j + 1];
        if sp.ship[j] > limit {
            proof {
                lemma_table_skip(pd, *c, lo as int, lo + j, slots@, *ng as int);
            }
        } else {
            proof {
                assert(q1_qual(pd, crow(*c, lo + j)));
            }
            match add_known_row(c, &sp, lo, hi, j, a0, a1, b0, b1, Ghost(pd), small, slots, *ng, idx) {
                0 => {},
                2 => return (Stop::RowOverflow, lo + j),
                3 => return (Stop::NeedExact, lo + j),
                _ => {
                    match add_qualifying_row(c, lo, lo + j, Ghost(pd), small, slots, ng, idx) {
                        Stop::Done => {},
                        Stop::Full => return (Stop::Full, lo + j),
                        Stop::RowOverflow => return (Stop::RowOverflow, lo + j),
                        Stop::NeedExact => return (Stop::NeedExact, lo + j),
                    }
                },
            }
        }
        a0 = a1;
        b0 = b1;
        j = j + 1;
    }
    (Stop::Done, hi)
}

} // verus!
