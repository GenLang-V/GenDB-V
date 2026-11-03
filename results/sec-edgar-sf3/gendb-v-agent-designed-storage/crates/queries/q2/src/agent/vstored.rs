//! The candidates in value order. Storage `num_vord` lists the stored rows of every unit by value descending
//! (`vorder`). The candidate of stored num row `i` (`row_emit`) is `(name, tag, value)` when the row's run is of unit
//! `$1`, its filing is a sub row (`sub_of`, unique by sub's primary key) of fiscal year `$2`, and the row holds the
//! largest value of its tag in its run (`seg_max`). `v_emits(lo, q)` concatenates the candidates of the rows at
//! `vorder` positions `[lo, q)`. `lemma_v_count`: over the unit's positions their bag is the bag of the SQL body
//! (`sem::body_count`); `lemma_no_unit_count`: without the unit the body is empty.
use vstd::prelude::*;
use vstd::multiset::Multiset;
use crate::spec::value::*;
use crate::link::join::*;
use crate::gendb_entry::layout::PartView;
use crate::stores::num_vord::interface as numi;
use crate::stores::sub::interface as subi;
use crate::stores::num_vord::interface::common::text::{u64_part, u8_part, lemma_dict_codes};
use crate::stores::num_vord::interface::common::runs::*;
use crate::agent::sem::*;
use crate::agent::stored::*;
use crate::agent::common::rel::*;

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms, vstd::seq_lib::lemma_multiset_commutative};

/// The value order of the stored rows.
pub open spec fn vord(np: Seq<PartView>) -> Seq<u64> {
    numi::u64s(np, numi::P_VORDER)
}

/// The run holding stored row `i`.
pub open spec fn run_at(np: Seq<PartView>, i: int) -> int {
    run_of(n_start(np), numi::run_count(np), i)
}

/// Some sub row has adsh `a`.
pub open spec fn has_sub(sp: Seq<PartView>, a: Seq<u8>) -> bool {
    exists|j: int| 0 <= j < subi::row_count(sp) && #[trigger] subi::adsh_bytes(sp, j) == a
}

/// The sub row with adsh `a` (when there is one).
pub open spec fn sub_of(sp: Seq<PartView>, a: Seq<u8>) -> int {
    choose|j: int| 0 <= j < subi::row_count(sp) && #[trigger] subi::adsh_bytes(sp, j) == a
}

/// The candidate of stored row `i`: none, or its output row.
pub open spec fn row_emit(np: Seq<PartView>, sp: Seq<PartView>, u: Seq<u8>, y: int, i: int) -> Seq<Row> {
    let r = run_at(np, i);
    let a = numi::run_adsh_of(np, r);
    let j = sub_of(sp, a);
    if numi::run_uom_of(np, r) == u && has_sub(sp, a) && fy_ok(sp, y, j) && seg_max(np, r, i) {
        seq![cand_row(np, sp, j, i)]
    } else {
        Seq::empty()
    }
}

/// The candidates of the rows at `vorder` positions `[lo, q)`.
pub open spec fn v_emits(np: Seq<PartView>, sp: Seq<PartView>, u: Seq<u8>, y: int, lo: int, q: int) -> Seq<Row>
    decreases q - lo,
{
    if q <= lo {
        Seq::empty()
    } else {
        v_emits(np, sp, u, y, lo, q - 1) + row_emit(np, sp, u, y, vord(np)[q - 1] as int)
    }
}

/// Positions `[lo, hi)` split at `mid`.
pub proof fn lemma_v_emits_split(np: Seq<PartView>, sp: Seq<PartView>, u: Seq<u8>, y: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures v_emits(np, sp, u, y, lo, hi) == v_emits(np, sp, u, y, lo, mid) + v_emits(np, sp, u, y, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_v_emits_split(np, sp, u, y, lo, mid, hi - 1);
        assert(v_emits(np, sp, u, y, lo, mid) + v_emits(np, sp, u, y, mid, hi)
            =~= v_emits(np, sp, u, y, lo, mid) + v_emits(np, sp, u, y, mid, hi - 1)
                + row_emit(np, sp, u, y, vord(np)[hi - 1] as int));
    } else {
        assert(v_emits(np, sp, u, y, lo, mid) + v_emits(np, sp, u, y, mid, hi) =~= v_emits(np, sp, u, y, lo, mid));
    }
}

// ------------------------------------------------------------------ sums over position lists

/// `f(s[0]) + .. + f(s[len - 1])`.
pub open spec fn sum_list(s: Seq<u64>, f: spec_fn(int) -> int) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { sum_list(s.drop_last(), f) + f(s.last() as int) }
}

proof fn lemma_sum_list_append(a: Seq<u64>, b: Seq<u64>, f: spec_fn(int) -> int)
    ensures sum_list(a + b, f) == sum_list(a, f) + sum_list(b, f),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_sum_list_append(a, b.drop_last(), f);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

proof fn lemma_sum_list_remove(s: Seq<u64>, i: int, f: spec_fn(int) -> int)
    requires 0 <= i < s.len(),
    ensures sum_list(s, f) == sum_list(s.remove(i), f) + f(s[i] as int),
{
    let a = s.subrange(0, i);
    let b = s.subrange(i + 1, s.len() as int);
    assert(s =~= a + seq![s[i]] + b);
    assert(s.remove(i) =~= a + b);
    lemma_sum_list_append(a + seq![s[i]], b, f);
    lemma_sum_list_append(a, seq![s[i]], f);
    lemma_sum_list_append(a, b, f);
    assert(seq![s[i]].drop_last() =~= Seq::<u64>::empty());
    assert(seq![s[i]].last() == s[i]);
    assert(sum_list(Seq::<u64>::empty(), f) == 0);
    assert(sum_list(seq![s[i]], f) == sum_list(seq![s[i]].drop_last(), f) + f(seq![s[i]].last() as int));
}

/// The same multiset gives the same sum.
proof fn lemma_sum_list_perm(a: Seq<u64>, b: Seq<u64>, f: spec_fn(int) -> int)
    requires a.to_multiset() == b.to_multiset(),
    ensures sum_list(a, f) == sum_list(b, f),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(b.to_multiset().len() == 0);
        assert(b.len() == 0);
    } else {
        let x = a.last();
        let ai = a.drop_last();
        assert(ai.push(x) =~= a);
        assert(a.to_multiset().count(x) > 0);
        assert(b.contains(x));
        let i = choose|i: int| 0 <= i < b.len() && b[i] == x;
        let bi = b.remove(i);
        assert(bi.to_multiset() =~= b.to_multiset().remove(x));
        assert(ai.to_multiset() =~= a.to_multiset().remove(x));
        lemma_sum_list_perm(ai, bi, f);
        lemma_sum_list_remove(b, i, f);
    }
}

/// Over the span `[lo, hi)` the list sum is the index sum.
proof fn lemma_sum_list_span(lo: int, hi: int, f: spec_fn(int) -> int)
    requires 0 <= lo <= hi <= u64::MAX,
    ensures sum_list(numi::span(lo, hi), f) == sum_idx(lo, hi, f),
    decreases hi - lo,
{
    if hi > lo {
        lemma_sum_list_span(lo, hi - 1, f);
        assert(numi::span(lo, hi).drop_last() =~= numi::span(lo, hi - 1));
    } else {
        assert(numi::span(lo, hi) =~= Seq::<u64>::empty());
    }
}

/// The multiplicity of `t` among the candidates of positions `[lo, q)` is the list sum over `vorder[lo..q)`.
proof fn lemma_v_emits_list(np: Seq<PartView>, sp: Seq<PartView>, u: Seq<u8>, y: int, t: Row, lo: int, q: int)
    requires 0 <= lo <= q <= vord(np).len(),
    ensures
        v_emits(np, sp, u, y, lo, q).to_multiset().count(t)
            == sum_list(vord(np).subrange(lo, q), |i: int| row_emit(np, sp, u, y, i).to_multiset().count(t) as int),
    decreases q - lo,
{
    if q > lo {
        lemma_v_emits_list(np, sp, u, y, t, lo, q - 1);
        assert(vord(np).subrange(lo, q).drop_last() =~= vord(np).subrange(lo, q - 1));
        let a = v_emits(np, sp, u, y, lo, q - 1);
        let b = row_emit(np, sp, u, y, vord(np)[q - 1] as int);
        assert((a + b).to_multiset() =~= a.to_multiset().add(b.to_multiset()));
    } else {
        assert(vord(np).subrange(lo, q) =~= Seq::<u64>::empty());
    }
}

// ------------------------------------------------------------------ one stored row

/// Unit starts over the run layout: `g` the unit directory over the run units `k0`, `st` the run starts.
proof fn lemma_unit_span(g: Seq<u64>, k0: Seq<u64>, st: Seq<u64>, nr: int, n: int, nu: int, uc: int)
    requires runs_partition_ok(st, nr, n), group_starts_ok(g, k0, nu), k0.len() == nr, 0 <= uc < nu,
    ensures
        g[uc] <= g[uc + 1] <= nr,
        0 <= st[g[uc] as int] <= st[g[uc + 1] as int] <= n,
{
    assert(g[uc] <= k0.len() && g[uc + 1] <= k0.len());
    if g[uc + 1] < g[uc] {
        let r = g[uc + 1] as int;
        assert(r < g[uc] <==> k0[r] < uc);
        assert(r < g[uc + 1] <==> k0[r] < uc + 1);
    }
    let (a, b) = (g[uc] as int, g[uc + 1] as int);
    if a < nr { assert(st[a] < st[nr]); }
    if b < nr { assert(st[b] < st[nr]); }
    if a < b { assert(st[a] < st[b]); }
    if a > 0 { assert(st[0] < st[a]); }
}

/// Row `i` of run `r` is in the rows of unit `uc` exactly when the run is of unit `uc`.
proof fn lemma_unit_member(g: Seq<u64>, k0: Seq<u64>, st: Seq<u64>, nr: int, n: int, nu: int, uc: int, r: int, i: int)
    requires
        runs_partition_ok(st, nr, n), group_starts_ok(g, k0, nu), k0.len() == nr, 0 <= uc < nu,
        0 <= r < nr, st[r] <= i < st[r + 1],
    ensures (k0[r] == uc) == (st[g[uc] as int] <= i < st[g[uc + 1] as int]),
{
    lemma_unit_span(g, k0, st, nr, n, nu, uc);
    let (a, b) = (g[uc] as int, g[uc + 1] as int);
    assert(r < a <==> k0[r] < uc);
    assert(r < b <==> k0[r] < uc + 1);
    if a <= r < b {
        if a < r { assert(st[a] < st[r]); }
        if r + 1 < b { assert(st[r + 1] < st[b]); }
    } else if r < a {
        if r + 1 < a { assert(st[r + 1] < st[a]); }
    } else {
        if b < r { assert(st[b] < st[r]); }
    }
}

/// The run layout facts of num.
proof fn lemma_run_layout(np: Seq<PartView>)
    requires numi::num_layout_ok(np),
    ensures
        runs_partition_ok(n_start(np), numi::run_count(np), numi::row_count(np)),
        group_starts_ok(numi::u64s(np, numi::P_UOM_RUNS), numi::u64s(np, numi::P_RUN_UOM), numi::uom_count(np)),
        numi::u64s(np, numi::P_RUN_UOM).len() == numi::run_count(np),
{
}

/// Stored rows of unit code `uc` are the rows `[unit_row(uc), unit_row(uc + 1))`: exactly those in runs of the unit.
pub proof fn lemma_unit_rows(np: Seq<PartView>, sp: Seq<PartView>, db: Database, uc: int, i: int)
    requires parts_bound(np, sp, db), 0 <= uc < numi::uom_count(np), 0 <= i < numi::row_count(np),
    ensures
        (numi::u64s(np, numi::P_RUN_UOM)[run_at(np, i)] == uc) == (numi::unit_row(np, uc) <= i < numi::unit_row(np, uc + 1)),
{
    lemma_bound_layouts(np, sp, db);
    lemma_run_layout(np);
    lemma_pos_run(np, sp, db, i);
    lemma_unit_member(numi::u64s(np, numi::P_UOM_RUNS), numi::u64s(np, numi::P_RUN_UOM), n_start(np), numi::run_count(np),
        numi::row_count(np), numi::uom_count(np), uc, run_at(np, i), i);
}

/// The rows of unit code `uc` lie in `[0, n)`.
pub proof fn lemma_unit_bounds(np: Seq<PartView>, uc: int)
    requires numi::num_layout_ok(np), 0 <= uc < numi::uom_count(np),
    ensures 0 <= numi::unit_row(np, uc) <= numi::unit_row(np, uc + 1) <= numi::row_count(np),
{
    lemma_run_layout(np);
    lemma_unit_span(numi::u64s(np, numi::P_UOM_RUNS), numi::u64s(np, numi::P_RUN_UOM), n_start(np), numi::run_count(np),
        numi::row_count(np), numi::uom_count(np), uc);
}

/// The row's hits over all sub rows are the multiplicity of `t` among its candidates.
proof fn lemma_row_hits(np: Seq<PartView>, sp: Seq<PartView>, db: Database, u: Seq<u8>, y: int, t: Row, i: int)
    requires parts_bound(np, sp, db), 0 <= i < numi::row_count(np),
    ensures
        sub_hits(db.tables[1], db.tables[0], u, y, t)(srow(np, db, i)) == row_emit(np, sp, u, y, i).to_multiset().count(t),
{
    let (nums, subs) = (db.tables[1], db.tables[0]);
    let x = srow(np, db, i);
    let h = |s: Row| pair_hit(nums, u, y, t, x, s);
    lemma_pos_run(np, sp, db, i);
    let r = run_at(np, i);
    lemma_srow(np, sp, db, r, i);
    lemma_bound_layouts(np, sp, db);
    let a = numi::run_adsh_of(np, r);
    let em = row_emit(np, sp, u, y, i);
    assert(sub_hits(nums, subs, u, y, t)(x) == sum_of(subs, h));
    if numi::run_uom_of(np, r) == u && has_sub(sp, a) {
        let j = sub_of(sp, a);
        lemma_qual_seg(np, sp, db, u, r, i);
        lemma_sub_row(np, sp, db, y, j);
        assert forall|j2: int| 0 <= j2 < subs.len() && j2 != j implies h(#[trigger] subs[j2]) == 0 by {
            lemma_sub_row(np, sp, db, y, j2);
            if h(subs[j2]) != 0 {
                lemma_sub_pk(np, sp, db, j, j2);
            }
        }
        lemma_sum_of_single(subs, h, j);
        assert(out_row(x, subs[j]) =~= cand_row(np, sp, j, i));
        if fy_ok(sp, y, j) && seg_max(np, r, i) {
            assert(em.to_multiset() =~= Multiset::empty().insert(cand_row(np, sp, j, i))) by {
                assert(em == Seq::<Row>::empty().push(cand_row(np, sp, j, i)));
            }
        } else {
            assert(em.to_multiset() =~= Multiset::<Row>::empty());
        }
    } else {
        assert forall|j2: int| 0 <= j2 < subs.len() implies h(#[trigger] subs[j2]) == 0 by {
            lemma_sub_row(np, sp, db, y, j2);
            if h(subs[j2]) != 0 {
                assert(subi::adsh_bytes(sp, j2) == a);
                assert(has_sub(sp, a));
            }
        }
        lemma_sum_of_zero(subs, h);
        assert(em.to_multiset() =~= Multiset::<Row>::empty());
    }
}

/// The body's multiplicity of `t` is the sum of the stored rows' candidate multiplicities.
proof fn lemma_rows_sum(np: Seq<PartView>, sp: Seq<PartView>, db: Database, u: Seq<u8>, y: int, t: Row)
    requires parts_bound(np, sp, db),
    ensures
        body_count(db.tables[1], db.tables[0], u, y, t)
            == sum_idx(0, numi::row_count(np), |i: int| row_emit(np, sp, u, y, i).to_multiset().count(t) as int),
{
    let (nums, subs) = (db.tables[1], db.tables[0]);
    let n = numi::row_count(np);
    let f = sub_hits(nums, subs, u, y, t);
    lemma_stored_sum(np, sp, db, f);
    let c = |i: int| row_emit(np, sp, u, y, i).to_multiset().count(t) as int;
    assert forall|i: int| 0 <= i < n implies #[trigger] f(srow(np, db, i)) == c(i) by {
        lemma_row_hits(np, sp, db, u, y, t, i);
    }
    lemma_sum_idx_ext(0, n, |i: int| f(srow(np, db, i)), c);
}

/// The candidates of unit code `uc`'s positions `[unit_row(uc), unit_row(uc + 1))` have the bag of the SQL body.
pub proof fn lemma_v_count(np: Seq<PartView>, sp: Seq<PartView>, db: Database, u: Seq<u8>, y: int, t: Row, uc: int)
    requires
        parts_bound(np, sp, db),
        0 <= uc < numi::uom_count(np),
        numi::dict_entry(np, numi::P_UOM_OFF, uc) == u,
    ensures
        v_emits(np, sp, u, y, numi::unit_row(np, uc), numi::unit_row(np, uc + 1)).to_multiset().count(t)
            == body_count(db.tables[1], db.tables[0], u, y, t),
{
    lemma_bound_layouts(np, sp, db);
    let n = numi::row_count(np);
    let (lo, hi) = (numi::unit_row(np, uc), numi::unit_row(np, uc + 1));
    let c = |i: int| row_emit(np, sp, u, y, i).to_multiset().count(t) as int;
    lemma_rows_sum(np, sp, db, u, y, t);
    assert(numi::unit_order_ok(np, uc));
    // Rows outside the unit have another unit: no candidates.
    lemma_unit_bounds(np, uc);
    assert forall|i: int| (0 <= i < lo || hi <= i < n) implies #[trigger] c(i) == 0 by {
        lemma_unit_rows(np, sp, db, uc, i);
        lemma_pos_run(np, sp, db, i);
        let r = run_at(np, i);
        let ru = numi::u64s(np, numi::P_RUN_UOM);
        if numi::run_uom_of(np, r) == u {
            lemma_dict_codes(u64_part(np[numi::P_UOM_OFF as int]), u8_part(np[numi::P_UOM_OFF + 1]), numi::uom_count(np),
                ru[r] as int, uc);
        }
        assert(row_emit(np, sp, u, y, i).to_multiset() =~= Multiset::<Row>::empty());
    }
    lemma_sum_idx_split(0, lo, n, c);
    lemma_sum_idx_split(lo, hi, n, c);
    lemma_sum_idx_zero(0, lo, c);
    lemma_sum_idx_zero(hi, n, c);
    // The unit's rows in value order: the same multiset of positions.
    lemma_sum_list_span(lo, hi, c);
    lemma_sum_list_perm(vord(np).subrange(lo, hi), numi::span(lo, hi), c);
    lemma_v_emits_list(np, sp, u, y, t, lo, hi);
}

/// Without unit `u` in the unit dictionary, no row has candidates: the body is empty.
pub proof fn lemma_no_unit_count(np: Seq<PartView>, sp: Seq<PartView>, db: Database, u: Seq<u8>, y: int, t: Row)
    requires
        parts_bound(np, sp, db),
        forall|k: int| 0 <= k < numi::uom_count(np) ==> numi::dict_entry(np, numi::P_UOM_OFF, k) != u,
    ensures body_count(db.tables[1], db.tables[0], u, y, t) == 0,
{
    lemma_bound_layouts(np, sp, db);
    let n = numi::row_count(np);
    let c = |i: int| row_emit(np, sp, u, y, i).to_multiset().count(t) as int;
    lemma_rows_sum(np, sp, db, u, y, t);
    assert forall|i: int| 0 <= i < n implies #[trigger] c(i) == 0 by {
        lemma_pos_run(np, sp, db, i);
        let r = run_at(np, i);
        assert(numi::u64s(np, numi::P_RUN_UOM)[r] < numi::uom_count(np));
        assert(row_emit(np, sp, u, y, i).to_multiset() =~= Multiset::<Row>::empty());
    }
    lemma_sum_idx_zero(0, n, c);
}

} // verus!
