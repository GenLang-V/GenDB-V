//! Merging group tables of adjacent row ranges: the global table over `[0, lo)` and a worker's table over
//! `[lo, hi)` become the global table over `[0, hi)` (`merge_table`). Each worker slot is looked up in the global
//! table by its key bytes; a match combines the two accumulators (`combine`), a new key is appended (its rows all
//! lie in `[lo, hi)`). The global table keeps every slot in use (`table_ok` with `ng = len`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::query::*;
use crate::link::expr::i128_max;
use crate::gendb_entry::work::text_eq;
use crate::agent::normal::*;
use crate::agent::columns::*;
use crate::agent::accum::*;
use crate::agent::scan::*;

verus! {

/// Group `k` has no row in `rs`.
pub open spec fn no_hit(pd: int, rs: Seq<Row>, k: Row) -> bool {
    forall|j: int| 0 <= j < rs.len() ==> !hit(q1_spec(pd), #[trigger] rs[j], k)
}

/// No row of `rs` belongs to `k`: its accumulators are zero.
pub proof fn lemma_no_hit_zero(pd: int, rs: Seq<Row>, k: Row)
    requires no_hit(pd, rs, k),
    ensures
        gcount(q1_spec(pd), rs, k) == 0,
        forall|j: int| #[trigger] gsum(q1_spec(pd), rs, k, j) == 0,
        forall|j: int| #[trigger] gabs(q1_spec(pd), rs, k, j) == 0,
    decreases rs.len(),
{
    let g = q1_spec(pd);
    if rs.len() > 0 {
        let d = rs.drop_last();
        assert forall|j: int| 0 <= j < d.len() implies !hit(g, #[trigger] d[j], k) by {
            assert(d[j] == rs[j]);
        }
        lemma_no_hit_zero(pd, d, k);
        assert(!hit(g, rs[rs.len() - 1], k));
    }
    assert forall|j: int| #[trigger] gsum(g, rs, k, j) == 0 by {
        lemma_zero_count(g, rs, k, j);
    }
    assert forall|j: int| #[trigger] gabs(g, rs, k, j) == 0 by {
        lemma_zero_count(g, rs, k, j);
    }
}

/// Accumulators over `rs1` stay those over `rs1 + rs2` when `rs2` has no row of the group, and accumulators over
/// `rs2` are those over `rs1 + rs2` when `rs1` has none.
pub proof fn lemma_acc_extend(pd: int, rs1: Seq<Row>, rs2: Seq<Row>, k: Row, a: Acc)
    ensures
        acc_ok(pd, rs1, k, a) && no_hit(pd, rs2, k) ==> acc_ok(pd, rs1 + rs2, k, a),
        acc_ok(pd, rs2, k, a) && no_hit(pd, rs1, k) ==> acc_ok(pd, rs1 + rs2, k, a),
{
    let g = q1_spec(pd);
    lemma_append(g, rs1, rs2, k, 0);
    lemma_append(g, rs1, rs2, k, 1);
    lemma_append(g, rs1, rs2, k, 2);
    lemma_append(g, rs1, rs2, k, 3);
    lemma_append(g, rs1, rs2, k, 6);
    if no_hit(pd, rs2, k) {
        lemma_no_hit_zero(pd, rs2, k);
    }
    if no_hit(pd, rs1, k) {
        lemma_no_hit_zero(pd, rs1, k);
    }
}

/// A group has at most as many rows as the relation.
pub proof fn lemma_gcount_le(pd: int, rs: Seq<Row>, k: Row)
    ensures gcount(q1_spec(pd), rs, k) <= rs.len(),
    decreases rs.len(),
{
    if rs.len() > 0 {
        lemma_gcount_le(pd, rs.drop_last(), k);
    }
}

/// `b` combines `a1` (rows `rs1`) and `a2` (rows `rs2`), both in the same mode.
pub open spec fn combined(a1: Acc, a2: Acc, b: Acc) -> bool {
    &&& b.rep == a1.rep
    &&& b.small == a1.small
    &&& b.cnt as int == a1.cnt as int + a2.cnt as int
    &&& b.sum_qty as int == a1.sum_qty as int + a2.sum_qty as int
    &&& b.sum_price as int == a1.sum_price as int + a2.sum_price as int
    &&& b.sum_disc as int == a1.sum_disc as int + a2.sum_disc as int
    &&& within(b.sum_qty, b.cnt) && within(b.sum_price, b.cnt) && within(b.sum_disc, b.cnt)
    &&& if a1.small {
        &&& !b.over_dp && !b.over_ch
        &&& b.sum_dp as int == a1.sum_dp as int + a2.sum_dp as int
        &&& b.sum_ch as int == a1.sum_ch as int + a2.sum_ch as int
    } else {
        &&& b.over_dp == (a1.over_dp || a2.over_dp || a1.mass_dp as int + a2.mass_dp as int > i128_max())
        &&& (!b.over_dp ==> b.mass_dp as int == a1.mass_dp as int + a2.mass_dp as int && b.sum_dp as int == a1.sum_dp as int + a2.sum_dp as int)
        &&& b.over_ch == (a1.over_ch || a2.over_ch || a1.mass_ch as int + a2.mass_ch as int > i128_max())
        &&& (!b.over_ch ==> b.mass_ch as int == a1.mass_ch as int + a2.mass_ch as int && b.sum_ch as int == a1.sum_ch as int + a2.sum_ch as int)
    }
}

/// Combined accumulators are the accumulators of the concatenated rows.
pub proof fn lemma_combined(pd: int, rs1: Seq<Row>, rs2: Seq<Row>, k: Row, a1: Acc, a2: Acc, b: Acc)
    requires acc_ok(pd, rs1, k, a1), acc_ok(pd, rs2, k, a2), a1.small == a2.small, combined(a1, a2, b),
    ensures acc_ok(pd, rs1 + rs2, k, b),
{
    let g = q1_spec(pd);
    lemma_append(g, rs1, rs2, k, 0);
    lemma_append(g, rs1, rs2, k, 1);
    lemma_append(g, rs1, rs2, k, 2);
    lemma_append(g, rs1, rs2, k, 3);
    lemma_append(g, rs1, rs2, k, 6);
    lemma_abs_bound(g, rs1, k, 2);
    lemma_abs_bound(g, rs1, k, 3);
    lemma_abs_bound(g, rs2, k, 2);
    lemma_abs_bound(g, rs2, k, 3);
    if a1.small {
        assert(small_bound(b.cnt) == small_bound(a1.cnt) + small_bound(a2.cnt)) by (nonlinear_arith)
            requires b.cnt as int == a1.cnt as int + a2.cnt as int;
    }
}

/// Product accumulators of two parts: checked mass, overflow if either part overflowed.
fn prod_combine(o1: bool, s1: i128, m1: i128, o2: bool, s2: i128, m2: i128) -> (r: (bool, i128, i128))
    requires prod_inv(o1, s1, m1), prod_inv(o2, s2, m2),
    ensures
        r.0 == (o1 || o2 || m1 as int + m2 as int > i128_max()),
        !r.0 ==> r.2 as int == m1 as int + m2 as int && r.1 as int == s1 as int + s2 as int,
        prod_inv(r.0, r.1, r.2),
{
    if o1 || o2 {
        return (true, s1, m1);
    }
    match m1.checked_add(m2) {
        Some(m) => (false, s1 + s2, m),
        None => (true, s1, m1),
    }
}

/// Combines the accumulators of two parts of the rows (`a1` keeps its representative).
pub fn combine(a1: Acc, a2: Acc) -> (b: Acc)
    requires acc_inv(a1), acc_inv(a2), a1.small == a2.small, a1.cnt as int + a2.cnt as int <= u64::MAX,
    ensures combined(a1, a2, b), acc_inv(b),
{
    if a1.small {
        proof {
            assert(small_bound((a1.cnt + a2.cnt) as u64) == small_bound(a1.cnt) + small_bound(a2.cnt)) by (nonlinear_arith)
                requires a1.cnt as int + a2.cnt as int <= u64::MAX;
            assert(small_bound((a1.cnt + a2.cnt) as u64) <= 0xffff_ffff_ffff_ffff * p63()) by (nonlinear_arith)
                requires a1.cnt as int + a2.cnt as int <= u64::MAX;
        }
        return Acc {
            rep: a1.rep,
            cnt: a1.cnt + a2.cnt,
            sum_qty: a1.sum_qty + a2.sum_qty,
            sum_price: a1.sum_price + a2.sum_price,
            sum_disc: a1.sum_disc + a2.sum_disc,
            small: true,
            sum_dp: a1.sum_dp + a2.sum_dp,
            mass_dp: 0,
            over_dp: false,
            sum_ch: a1.sum_ch + a2.sum_ch,
            mass_ch: 0,
            over_ch: false,
        };
    }
    let (over_dp, sum_dp, mass_dp) = prod_combine(a1.over_dp, a1.sum_dp, a1.mass_dp, a2.over_dp, a2.sum_dp, a2.mass_dp);
    let (over_ch, sum_ch, mass_ch) = prod_combine(a1.over_ch, a1.sum_ch, a1.mass_ch, a2.over_ch, a2.sum_ch, a2.mass_ch);
    Acc {
        rep: a1.rep,
        cnt: a1.cnt + a2.cnt,
        sum_qty: a1.sum_qty + a2.sum_qty,
        sum_price: a1.sum_price + a2.sum_price,
        sum_disc: a1.sum_disc + a2.sum_disc,
        small: false,
        sum_dp,
        mass_dp,
        over_dp,
        sum_ch,
        mass_ch,
        over_ch,
    }
}

/// Byte equality of the keys of rows `r1` and `r2`.
fn same_key(c: &Cols, r1: usize, r2: usize) -> (b: bool)
    requires cols_wf(*c), r1 < c.n, r2 < c.n,
    ensures b == (key_of(*c, r1 as int) == key_of(*c, r2 as int)),
{
    let ghost rv = rf_view(*c);
    let ghost lv = ls_view(*c);
    proof {
        assert(0 <= rv.offsets[r1 as int] <= rv.offsets[r1 + 1] <= rv.bytes.len());
        assert(0 <= lv.offsets[r1 as int] <= lv.offsets[r1 + 1] <= lv.bytes.len());
        assert(0 <= rv.offsets[r2 as int] <= rv.offsets[r2 + 1] <= rv.bytes.len());
        assert(0 <= lv.offsets[r2 as int] <= lv.offsets[r2 + 1] <= lv.bytes.len());
        lemma_crow(*c, r1 as int);
        lemma_crow(*c, r2 as int);
    }
    let rf = crate::link::query::TextCol { offsets: c.rf_offsets, bytes: c.rf_bytes };
    let ls = crate::link::query::TextCol { offsets: c.ls_offsets, bytes: c.ls_bytes };
    let b = text_eq(&rf, r1, &rf, r2) && text_eq(&ls, r1, &ls, r2);
    proof {
        if key_of(*c, r1 as int) == key_of(*c, r2 as int) {
            assert(key_of(*c, r1 as int)[0] == key_of(*c, r2 as int)[0]);
            assert(key_of(*c, r1 as int)[1] == key_of(*c, r2 as int)[1]);
        }
    }
    b
}

/// A key of the worker's slots `[0, s)`.
pub open spec fn done_key(c: Cols, w: Seq<Acc>, s: int, k: Row) -> bool {
    exists|t: int| 0 <= t < s && slot_key(c, #[trigger] w[t]) == k
}

/// The merge state after the worker slots `[0, s)`: a group already met in them is over `[0, hi)`, any other over
/// `[0, lo)`.
pub open spec fn merge_ok(pd: int, c: Cols, lo: int, hi: int, w: Seq<Acc>, s: int, gt: Seq<Acc>) -> bool {
    &&& forall|g: int| 0 <= g < gt.len() ==> (#[trigger] gt[g]).rep < hi && q1_qual(pd, crow(c, gt[g].rep as int))
    &&& forall|g: int| 0 <= g < gt.len() ==> acc_ok(pd,
            range_rows(c, 0, if done_key(c, w, s, slot_key(c, #[trigger] gt[g])) { hi } else { lo }), slot_key(c, gt[g]), gt[g])
    &&& forall|g: int| 0 <= g < gt.len() ==> (#[trigger] gt[g]).cnt <= hi
    &&& forall|g: int, h: int| 0 <= g < gt.len() && 0 <= h < gt.len() && g != h ==> slot_key(c, #[trigger] gt[g]) != slot_key(c, #[trigger] gt[h])
    &&& forall|r: int| 0 <= r < lo && q1_qual(pd, #[trigger] crow(c, r)) ==>
            exists|g: int| 0 <= g < gt.len() && key_of(c, r) == slot_key(c, #[trigger] gt[g])
    &&& forall|t: int| 0 <= t < s ==> exists|g: int| 0 <= g < gt.len() && slot_key(c, #[trigger] w[t]) == slot_key(c, #[trigger] gt[g])
}

/// The rows of `[0, hi)` split at `lo`.
pub proof fn lemma_split_rows(c: Cols, lo: int, hi: int)
    requires 0 <= lo <= hi <= c.n,
    ensures range_rows(c, 0, hi) == range_rows(c, 0, lo) + range_rows(c, lo, hi),
{
    lemma_crows(c);
    assert(range_rows(c, 0, hi) =~= range_rows(c, 0, lo) + range_rows(c, lo, hi));
}

/// A key that no table slot has has no qualifying row in the table's range.
pub proof fn lemma_absent_no_hit(pd: int, c: Cols, lo: int, hi: int, w: Seq<Acc>, nw: int, k: Row)
    requires
        0 <= lo <= hi <= c.n,
        table_ok(pd, c, lo, hi, w, nw),
        forall|t: int| 0 <= t < nw ==> slot_key(c, #[trigger] w[t]) != k,
    ensures no_hit(pd, range_rows(c, lo, hi), k),
{
    lemma_crows(c);
    let rs = range_rows(c, lo, hi);
    assert forall|j: int| 0 <= j < rs.len() implies !hit(q1_spec(pd), #[trigger] rs[j], k) by {
        assert(rs[j] == crow(c, lo + j));
        if hit(q1_spec(pd), rs[j], k) {
            let t = choose|t: int| 0 <= t < nw && key_of(c, lo + j) == slot_key(c, #[trigger] w[t]);
        }
    }
}

/// Merges worker slot `s` into the global table.
fn merge_slot(c: &Cols, lo: usize, hi: usize, Ghost(pd): Ghost<int>, Ghost(small): Ghost<bool>, gt: &mut Vec<Acc>, w: &Vec<Acc>, s: usize)
    requires
        cols_wf(*c),
        lo <= hi <= c.n,
        s < w@.len(),
        mode_ok(w@, w@.len() as int, small),
        mode_ok(old(gt)@, old(gt)@.len() as int, small),
        table_ok(pd, *c, lo as int, hi as int, w@, w@.len() as int),
        merge_ok(pd, *c, lo as int, hi as int, w@, s as int, old(gt)@),
        range_rows(*c, 0, hi as int) == range_rows(*c, 0, lo as int) + range_rows(*c, lo as int, hi as int),
    ensures
        merge_ok(pd, *c, lo as int, hi as int, w@, s + 1, final(gt)@),
        mode_ok(final(gt)@, final(gt)@.len() as int, small),
{
    let ws = w[s];
    let ghost k = slot_key(*c, ws);
    proof {
        assert(lo <= ws.rep < hi);
        assert forall|h: int| 0 <= h < gt@.len() implies (#[trigger] gt@[h]).rep < c.n by {}
    }
    // Look the key up in the global table.
    let mut g: usize = 0;
    let mut found = false;
    while g < gt.len() && !found
        invariant
            cols_wf(*c),
            ws.rep < c.n,
            g <= gt@.len(),
            forall|h: int| 0 <= h < gt@.len() ==> (#[trigger] gt@[h]).rep < c.n,
            forall|h: int| 0 <= h < g ==> slot_key(*c, #[trigger] gt@[h]) != k,
            k == slot_key(*c, ws),
            found ==> g < gt@.len() && slot_key(*c, gt@[g as int]) == k,
        decreases gt@.len() - g + (if found { 0int } else { 1int }),
    {
        if same_key(c, gt[g].rep, ws.rep) {
            found = true;
        } else {
            g = g + 1;
        }
    }
    let ghost gt_before = gt@;
    let ghost r1 = range_rows(*c, 0, lo as int);
    let ghost r2 = range_rows(*c, lo as int, hi as int);
    proof {
        lemma_crows(*c);
        // The worker's keys are distinct: `k` was not met in slots `[0, s)`.
        assert forall|t: int| 0 <= t < s implies slot_key(*c, #[trigger] w@[t]) != k by {
            assert(t != s as int);
        }
        assert(!done_key(*c, w@, s as int, k));
        assert(acc_ok(pd, r2, k, ws));
        lemma_acc_inv(pd, r2, k, ws);
        lemma_gcount_le(pd, r2, k);
        assert(r2.len() == hi - lo);
    }
    if found {
        let a = gt[g];
        proof {
            assert(acc_ok(pd, r1, k, a));
            lemma_acc_inv(pd, r1, k, a);
            lemma_gcount_le(pd, r1, k);
            assert(r1.len() == lo);
        }
        let b = combine(a, ws);
        gt.set(g, b);
        proof {
            lemma_combined(pd, r1, r2, k, a, ws, b);
            lemma_gcount_le(pd, r1 + r2, k);
            lemma_merge_step_found(pd, *c, lo as int, hi as int, w@, s as int, gt_before, g as int, b);
        }
    } else {
        proof {
            assert forall|h: int| 0 <= h < gt@.len() implies slot_key(*c, #[trigger] gt@[h]) != k by {}
            lemma_merge_absent(pd, *c, lo as int, hi as int, w@, s as int, gt@, k);
            lemma_acc_extend(pd, r1, r2, k, ws);
        }
        gt.push(ws);
        proof {
            lemma_merge_step_new(pd, *c, lo as int, hi as int, w@, s as int, gt_before, ws);
        }
    }
}

/// Merges the worker table `w[0..nw)` over `[lo, hi)` into the global table over `[0, lo)`.
pub fn merge_table(c: &Cols, lo: usize, hi: usize, Ghost(pd): Ghost<int>, Ghost(small): Ghost<bool>, gt: &mut Vec<Acc>, w: &Vec<Acc>, nw: usize)
    requires
        cols_wf(*c),
        lo <= hi <= c.n,
        nw == w@.len(),
        table_ok(pd, *c, 0, lo as int, old(gt)@, old(gt)@.len() as int),
        table_ok(pd, *c, lo as int, hi as int, w@, nw as int),
        mode_ok(old(gt)@, old(gt)@.len() as int, small),
        mode_ok(w@, nw as int, small),
    ensures
        table_ok(pd, *c, 0, hi as int, final(gt)@, final(gt)@.len() as int),
        mode_ok(final(gt)@, final(gt)@.len() as int, small),
{
    proof {
        lemma_split_rows(*c, lo as int, hi as int);
        assert forall|g: int| 0 <= g < gt@.len() implies !done_key(*c, w@, 0, slot_key(*c, #[trigger] gt@[g])) by {}
        lemma_merge_init(pd, *c, lo as int, hi as int, w@, gt@);
    }
    let mut s: usize = 0;
    while s < nw
        invariant
            cols_wf(*c),
            lo <= hi <= c.n,
            s <= nw == w@.len(),
            table_ok(pd, *c, lo as int, hi as int, w@, nw as int),
            merge_ok(pd, *c, lo as int, hi as int, w@, s as int, gt@),
            mode_ok(gt@, gt@.len() as int, small),
            mode_ok(w@, nw as int, small),
            range_rows(*c, 0, hi as int) == range_rows(*c, 0, lo as int) + range_rows(*c, lo as int, hi as int),
        decreases nw - s,
    {
        merge_slot(c, lo, hi, Ghost(pd), Ghost(small), gt, w, s);
        s = s + 1;
    }
    proof {
        lemma_merge_done(pd, *c, lo as int, hi as int, w@, nw as int, gt@);
    }
}

/// The merge state before any worker slot: the global table over `[0, lo)`.
pub proof fn lemma_merge_init(pd: int, c: Cols, lo: int, hi: int, w: Seq<Acc>, gt: Seq<Acc>)
    requires
        0 <= lo <= hi,
        table_ok(pd, c, 0, lo, gt, gt.len() as int),
        forall|g: int| 0 <= g < gt.len() ==> !done_key(c, w, 0, slot_key(c, #[trigger] gt[g])),
    ensures merge_ok(pd, c, lo, hi, w, 0, gt),
{
    assert forall|g: int| 0 <= g < gt.len() implies acc_ok(pd,
        range_rows(c, 0, if done_key(c, w, 0, slot_key(c, #[trigger] gt[g])) { hi } else { lo }), slot_key(c, gt[g]), gt[g]) by {}
}

/// A key absent from the global table has no qualifying row in `[0, lo)`.
pub proof fn lemma_merge_absent(pd: int, c: Cols, lo: int, hi: int, w: Seq<Acc>, s: int, gt: Seq<Acc>, k: Row)
    requires
        0 <= lo <= hi <= c.n,
        merge_ok(pd, c, lo, hi, w, s, gt),
        forall|h: int| 0 <= h < gt.len() ==> slot_key(c, #[trigger] gt[h]) != k,
    ensures no_hit(pd, range_rows(c, 0, lo), k),
{
    lemma_crows(c);
    let rs = range_rows(c, 0, lo);
    assert forall|j: int| 0 <= j < rs.len() implies !hit(q1_spec(pd), #[trigger] rs[j], k) by {
        assert(rs[j] == crow(c, j));
        if hit(q1_spec(pd), rs[j], k) {
            let h = choose|h: int| 0 <= h < gt.len() && key_of(c, j) == slot_key(c, #[trigger] gt[h]);
        }
    }
}

/// Merge step: worker slot `s` combined into global slot `g`.
pub proof fn lemma_merge_step_found(pd: int, c: Cols, lo: int, hi: int, w: Seq<Acc>, s: int, gt: Seq<Acc>, g: int, b: Acc)
    requires
        0 <= lo <= hi <= c.n,
        0 <= s < w.len(),
        table_ok(pd, c, lo, hi, w, w.len() as int),
        merge_ok(pd, c, lo, hi, w, s, gt),
        0 <= g < gt.len(),
        slot_key(c, gt[g]) == slot_key(c, w[s]),
        !done_key(c, w, s, slot_key(c, w[s])),
        b.rep == gt[g].rep,
        b.cnt <= hi,
        acc_ok(pd, range_rows(c, 0, lo) + range_rows(c, lo, hi), slot_key(c, w[s]), b),
        range_rows(c, 0, hi) == range_rows(c, 0, lo) + range_rows(c, lo, hi),
    ensures merge_ok(pd, c, lo, hi, w, s + 1, gt.update(g, b)),
{
    let k = slot_key(c, w[s]);
    let g2 = gt.update(g, b);
    assert(done_key(c, w, s + 1, k)) by {
        assert(slot_key(c, w[s]) == k);
    }
    assert forall|h: int| 0 <= h < g2.len() implies acc_ok(pd,
        range_rows(c, 0, if done_key(c, w, s + 1, slot_key(c, #[trigger] g2[h])) { hi } else { lo }), slot_key(c, g2[h]), g2[h]) by {
        if h != g {
            assert(g2[h] == gt[h]);
            let kh = slot_key(c, gt[h]);
            assert(kh != k);
            if done_key(c, w, s + 1, kh) {
                let t = choose|t: int| 0 <= t < s + 1 && slot_key(c, #[trigger] w[t]) == kh;
                assert(done_key(c, w, s, kh));
            }
        }
    }
    assert forall|r: int| 0 <= r < lo && q1_qual(pd, #[trigger] crow(c, r)) implies
        exists|h: int| 0 <= h < g2.len() && key_of(c, r) == slot_key(c, #[trigger] g2[h]) by {
        let h = choose|h: int| 0 <= h < gt.len() && key_of(c, r) == slot_key(c, #[trigger] gt[h]);
        assert(slot_key(c, g2[h]) == slot_key(c, gt[h]));
    }
    assert forall|t: int| 0 <= t < s + 1 implies exists|h: int| 0 <= h < g2.len() && slot_key(c, #[trigger] w[t]) == slot_key(c, #[trigger] g2[h]) by {
        if t == s {
            assert(slot_key(c, g2[g]) == k);
        } else {
            let h = choose|h: int| 0 <= h < gt.len() && slot_key(c, #[trigger] w[t]) == slot_key(c, #[trigger] gt[h]);
            assert(slot_key(c, g2[h]) == slot_key(c, gt[h]));
        }
    }
    assert forall|h1: int, h2: int| 0 <= h1 < g2.len() && 0 <= h2 < g2.len() && h1 != h2 implies
        slot_key(c, #[trigger] g2[h1]) != slot_key(c, #[trigger] g2[h2]) by {
        assert(slot_key(c, g2[h1]) == slot_key(c, gt[h1]));
        assert(slot_key(c, g2[h2]) == slot_key(c, gt[h2]));
    }
    assert forall|h: int| 0 <= h < g2.len() implies (#[trigger] g2[h]).rep < hi && q1_qual(pd, crow(c, g2[h].rep as int)) by {
        assert(g2[h].rep == gt[h].rep);
    }
    assert forall|h: int| 0 <= h < g2.len() implies (#[trigger] g2[h]).cnt <= hi by {
        if h != g {
            assert(g2[h] == gt[h]);
        }
    }
}

/// Merge step: worker slot `s` appended as a new global slot.
pub proof fn lemma_merge_step_new(pd: int, c: Cols, lo: int, hi: int, w: Seq<Acc>, s: int, gt: Seq<Acc>, ws: Acc)
    requires
        0 <= lo <= hi <= c.n,
        0 <= s < w.len(),
        ws == w[s],
        table_ok(pd, c, lo, hi, w, w.len() as int),
        merge_ok(pd, c, lo, hi, w, s, gt),
        forall|h: int| 0 <= h < gt.len() ==> slot_key(c, #[trigger] gt[h]) != slot_key(c, ws),
        acc_ok(pd, range_rows(c, 0, lo) + range_rows(c, lo, hi), slot_key(c, ws), ws),
        range_rows(c, 0, hi) == range_rows(c, 0, lo) + range_rows(c, lo, hi),
    ensures merge_ok(pd, c, lo, hi, w, s + 1, gt.push(ws)),
{
    let k = slot_key(c, ws);
    let g2 = gt.push(ws);
    let n0 = gt.len() as int;
    assert(done_key(c, w, s + 1, k)) by {
        assert(slot_key(c, w[s]) == k);
    }
    assert forall|h: int| 0 <= h < g2.len() implies acc_ok(pd,
        range_rows(c, 0, if done_key(c, w, s + 1, slot_key(c, #[trigger] g2[h])) { hi } else { lo }), slot_key(c, g2[h]), g2[h]) by {
        if h != n0 {
            assert(g2[h] == gt[h]);
            let kh = slot_key(c, gt[h]);
            assert(kh != k);
            if done_key(c, w, s + 1, kh) {
                let t = choose|t: int| 0 <= t < s + 1 && slot_key(c, #[trigger] w[t]) == kh;
                assert(done_key(c, w, s, kh));
            }
        }
    }
    assert forall|r: int| 0 <= r < lo && q1_qual(pd, #[trigger] crow(c, r)) implies
        exists|h: int| 0 <= h < g2.len() && key_of(c, r) == slot_key(c, #[trigger] g2[h]) by {
        let h = choose|h: int| 0 <= h < gt.len() && key_of(c, r) == slot_key(c, #[trigger] gt[h]);
        assert(g2[h] == gt[h]);
    }
    assert forall|t: int| 0 <= t < s + 1 implies exists|h: int| 0 <= h < g2.len() && slot_key(c, #[trigger] w[t]) == slot_key(c, #[trigger] g2[h]) by {
        if t == s {
            assert(g2[n0] == ws);
        } else {
            let h = choose|h: int| 0 <= h < gt.len() && slot_key(c, #[trigger] w[t]) == slot_key(c, #[trigger] gt[h]);
            assert(g2[h] == gt[h]);
        }
    }
    assert forall|h1: int, h2: int| 0 <= h1 < g2.len() && 0 <= h2 < g2.len() && h1 != h2 implies
        slot_key(c, #[trigger] g2[h1]) != slot_key(c, #[trigger] g2[h2]) by {
        if h1 < n0 && h2 < n0 {
            assert(g2[h1] == gt[h1] && g2[h2] == gt[h2]);
        } else if h1 < n0 {
            assert(g2[h1] == gt[h1]);
        } else {
            assert(g2[h2] == gt[h2]);
        }
    }
    assert forall|h: int| 0 <= h < g2.len() implies (#[trigger] g2[h]).rep < hi && q1_qual(pd, crow(c, g2[h].rep as int)) by {
        if h < n0 {
            assert(g2[h] == gt[h]);
        }
    }
    assert forall|h: int| 0 <= h < g2.len() implies (#[trigger] g2[h]).cnt <= hi by {
        if h < n0 {
            assert(g2[h] == gt[h]);
        }
    }
}

/// After every worker slot: the global table over `[0, hi)`.
pub proof fn lemma_merge_done(pd: int, c: Cols, lo: int, hi: int, w: Seq<Acc>, nw: int, gt: Seq<Acc>)
    requires
        0 <= lo <= hi <= c.n,
        table_ok(pd, c, lo, hi, w, nw),
        merge_ok(pd, c, lo, hi, w, nw, gt),
        range_rows(c, 0, hi) == range_rows(c, 0, lo) + range_rows(c, lo, hi),
    ensures table_ok(pd, c, 0, hi, gt, gt.len() as int),
{
    assert forall|g: int| 0 <= g < gt.len() implies acc_ok(pd, range_rows(c, 0, hi), slot_key(c, #[trigger] gt[g]), gt[g]) by {
        let k = slot_key(c, gt[g]);
        if !done_key(c, w, nw, k) {
            assert forall|t: int| 0 <= t < nw implies slot_key(c, #[trigger] w[t]) != k by {}
            lemma_absent_no_hit(pd, c, lo, hi, w, nw, k);
            lemma_acc_extend(pd, range_rows(c, 0, lo), range_rows(c, lo, hi), k, gt[g]);
        }
    }
    assert forall|r: int| 0 <= r < hi && q1_qual(pd, #[trigger] crow(c, r)) implies
        exists|g: int| 0 <= g < gt.len() && key_of(c, r) == slot_key(c, #[trigger] gt[g]) by {
        if r >= lo {
            let t = choose|t: int| 0 <= t < nw && key_of(c, r) == slot_key(c, #[trigger] w[t]);
            let g = choose|g: int| 0 <= g < gt.len() && slot_key(c, #[trigger] w[t]) == slot_key(c, #[trigger] gt[g]);
        }
    }
}

} // verus!
