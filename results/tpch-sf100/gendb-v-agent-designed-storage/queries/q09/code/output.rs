//! The result rows: one row `(n_name, o_year, sum_profit)` per group entry with a joining lineitem row
//! (`build_rows`), sorted by nation, o_year DESC with the framework's sort; with every group merged through all
//! lineitem rows (`groups::keys_on`), they are an allowed output of the statement (`lemma_final`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::query::query_spec_at;
use crate::exec::value::{EVal, ERow, view_row};
use crate::exec::ast::EOrderKey;
use crate::exec::relational::order::{sort_rows_exec, view_keys};
use crate::link::query::view_rows;
use crate::link::outcome::{lemma_view_rows, lemma_view_rows_push};
use crate::link::expr::i128_max;
use crate::bridge::order::{keys_ok, key_ok, all_keys_ok, lemma_sort_rows};
use super::common::isum::*;
use super::model::*;
use super::qspec::*;
use super::cols::*;
use super::cells::Cell;
use super::sqlrow::q9_keys;
use super::sqlsum::jkey;
use super::answer::*;
use super::groups::*;
use super::prep::name_bytes;

verus! {

/// The result row of an entry.
pub open spec fn erow(m: M, e: Ent) -> Row {
    seq![Val::Text(ename(m, e)), Val::Num { coeff: e.y as int, scale: 0 }, Val::Num { coeff: e.cell.sum as int, scale: 4 }]
}

/// The rows are exactly the rows of the entries `es[0 .. k]` with a joining row, without duplicates.
pub open spec fn rows_ok(m: M, es: Seq<Ent>, k: int, rows: Seq<Row>) -> bool {
    &&& rows.no_duplicates()
    &&& forall|r: Row| #[trigger] rows.contains(r) <==> exists|i: int| 0 <= i < k && es[i].cell.cnt > 0 && r == erow(m, es[i])
    &&& forall|i: int| 0 <= i < rows.len() ==> keys_ok(q9_keys(), seq![3int, 1int], #[trigger] rows[i])
}

/// Entries of the same row are the same entry.
proof fn lemma_erow_inj(m: M, nrep: Seq<u64>, es: Seq<Ent>, a: int, b: int)
    requires nrep_ok(m, nrep), ents_wf(m, nrep, es), 0 <= a < es.len(), 0 <= b < es.len(), erow(m, es[a]) == erow(m, es[b]),
    ensures a == b,
{
    let (ra, rb) = (erow(m, es[a]), erow(m, es[b]));
    assert(ra[0] == rb[0] && ra[1] == rb[1]);
    assert(ename(m, es[a]) == ename(m, es[b]) && es[a].y == es[b].y);
    if a != b {
        assert(is_at(m, es, ename(m, es[a]), es[a].y as int, a));
        assert(is_at(m, es, ename(m, es[a]), es[a].y as int, b));
        // two entries of one group would be one entry (lemma_val_at's uniqueness)
        assert(nrep[es[a].r as int] == es[a].r && nrep[es[b].r as int] == es[b].r);
        assert(nname(m, es[a].r as int) == nname(m, es[b].r as int));
        assert(es[a].r == es[b].r) by {
            if es[a].r < es[b].r {
                assert(nname(m, es[a].r as int) != nname(m, es[b].r as int));
            } else if es[b].r < es[a].r {
                assert(nname(m, es[b].r as int) != nname(m, es[a].r as int));
            }
        }
    }
}

/// The result rows of the entries with a joining row, in entry order.
pub fn build_rows(c: &Cols, es: &Vec<Ent>, Ghost(m): Ghost<M>, Ghost(nrep): Ghost<Seq<u64>>) -> (rows: Vec<ERow>)
    requires cols_ok(*c, m), shapes_ok(m), nrep_ok(m, nrep), ents_wf(m, nrep, es@),
    ensures rows_ok(m, es@, es@.len() as int, view_rows(rows@)),
{
    let mut rows: Vec<ERow> = Vec::new();
    let mut i: usize = 0;
    while i < es.len()
        invariant
            cols_ok(*c, m), shapes_ok(m), nrep_ok(m, nrep), ents_wf(m, nrep, es@),
            i <= es@.len(),
            rows_ok(m, es@, i as int, view_rows(rows@)),
        decreases es@.len() - i,
    {
        let e = es[i];
        if e.cell.cnt > 0 {
            proof { assert(es@[i as int] == e); }
            let name = name_bytes(c, e.r as usize, Ghost(m));
            let row: ERow = vec![
                EVal::Text(name),
                EVal::Num { coeff: e.y as i128, scale: 0 },
                EVal::Num { coeff: e.cell.sum, scale: 4 },
            ];
            let ghost r0 = rows@;
            proof {
                assert(view_row(row@) =~= erow(m, e));
            }
            rows.push(row);
            proof {
                lemma_view_rows_push(r0, row);
                let v0 = view_rows(r0);
                let v1 = view_rows(rows@);
                assert(v1 == v0.push(erow(m, e)));
                assert(!v0.contains(erow(m, e))) by {
                    if v0.contains(erow(m, e)) {
                        let i2 = choose|i2: int| 0 <= i2 < i && es@[i2].cell.cnt > 0 && erow(m, e) == erow(m, es@[i2]);
                        lemma_erow_inj(m, nrep, es@, i2, i as int);
                    }
                }
                assert forall|a: int, b: int| 0 <= a < v1.len() && 0 <= b < v1.len() && a != b implies v1[a] != v1[b] by {
                    if a < v0.len() && b < v0.len() {
                        assert(v1[a] == v0[a] && v1[b] == v0[b]);
                    } else if a < v0.len() {
                        assert(v0.contains(v1[a]));
                    } else {
                        assert(v0.contains(v1[b]));
                    }
                }
                assert forall|r: Row| #[trigger] v1.contains(r) <==> exists|i2: int| 0 <= i2 < i + 1 && es@[i2].cell.cnt > 0 && r == erow(m, es@[i2]) by {
                    if v1.contains(r) {
                        let t = choose|t: int| 0 <= t < v1.len() && v1[t] == r;
                        if t < v0.len() {
                            assert(v0.contains(r));
                        } else {
                            assert(r == erow(m, es@[i as int]));
                        }
                    }
                    if exists|i2: int| 0 <= i2 < i + 1 && es@[i2].cell.cnt > 0 && r == erow(m, es@[i2]) {
                        let i2 = choose|i2: int| 0 <= i2 < i + 1 && es@[i2].cell.cnt > 0 && r == erow(m, es@[i2]);
                        if i2 < i {
                            assert(v0.contains(r));
                            let t = choose|t: int| 0 <= t < v0.len() && v0[t] == r;
                            assert(v1[t] == r);
                        } else {
                            assert(v1[v0.len() as int] == r);
                        }
                    }
                }
                assert forall|t: int| 0 <= t < v1.len() implies keys_ok(q9_keys(), seq![3int, 1int], #[trigger] v1[t]) by {
                    if t < v0.len() {
                        assert(v1[t] == v0[t]);
                    } else {
                        let r = v1[t];
                        assert(r == erow(m, e));
                        assert(key_ok(q9_keys()[0], 3, r));
                        assert(key_ok(q9_keys()[1], 1, r));
                    }
                }
            }
        } else {
            proof {
                let v0 = view_rows(rows@);
                assert forall|r: Row| #[trigger] v0.contains(r) <==> exists|i2: int| 0 <= i2 < i + 1 && es@[i2].cell.cnt > 0 && r == erow(m, es@[i2]) by {
                    if exists|i2: int| 0 <= i2 < i + 1 && es@[i2].cell.cnt > 0 && r == erow(m, es@[i2]) {
                        let i2 = choose|i2: int| 0 <= i2 < i + 1 && es@[i2].cell.cnt > 0 && r == erow(m, es@[i2]);
                        assert(i2 < i);
                    }
                }
            }
        }
        i = i + 1;
    }
    rows
}

/// ORDER BY nation, o_year DESC as executable keys.
pub fn order_keys() -> (keys: Vec<EOrderKey>)
    ensures view_keys(keys@) == q9_keys(),
{
    let mut keys: Vec<EOrderKey> = Vec::new();
    keys.push(EOrderKey { col: 0, desc: false, nulls_first: false });
    keys.push(EOrderKey { col: 1, desc: true, nulls_first: true });
    proof { assert(view_keys(keys@) =~= q9_keys()); }
    keys
}

/// A group with a joining lineitem row is a (name, year) group.
proof fn lemma_key_form(m: M, p: QP, k: Row)
    requires exists|j: int| 0 <= j < m.l_n && jok(m, p, j) && jkey(m, j) == k,
    ensures k == gkey(k[0]->Text_0, k[1]->Num_coeff), k[0] is Text, k[1] is Num,
{
    let j = choose|j: int| 0 <= j < m.l_n && jok(m, p, j) && jkey(m, j) == k;
    assert(k == gkey(nname(m, jn(m, j)), jyear(m, j)));
}

/// Without a joining row, a group's sums are zero.
proof fn lemma_no_rows(m: M, p: QP, k: Row)
    requires !exists|j: int| 0 <= j < m.l_n && jok(m, p, j) && jkey(m, j) == k,
    ensures kcnt(m, p, k) == 0, ksum(m, p, k) == 0, kabs(m, p, k) == 0,
{
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] kcnt_f(m, p, k)(j) == 0 by {}
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] ksum_f(m, p, k)(j) == 0 by {}
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] kabs_f(m, p, k)(j) == 0 by {}
    lemma_isum_zero(m.l_n, kcnt_f(m, p, k));
    lemma_isum_zero(m.l_n, ksum_f(m, p, k));
    lemma_isum_zero(m.l_n, kabs_f(m, p, k));
}

/// A merged group's sums through every lineitem row are the statement's group sums.
proof fn lemma_group_val(m: M, p: QP, es: Seq<Ent>, name: Seq<u8>, y: int)
    requires keys_on(m, p, es, m.l_n), m.l_n >= 0,
    ensures
        val(m, es, name, y).cnt as int == kcnt(m, p, gkey(name, y)),
        val(m, es, name, y).sum as int == ksum(m, p, gkey(name, y)),
        val(m, es, name, y).ab as int == kabs(m, p, gkey(name, y)),
        kabs(m, p, gkey(name, y)) <= i128_max(),
{
    assert(key_is(m, p, es, name, y, m.l_n, m.n_n, m.l_n));
    lemma_dsum_empty(gc_f(m, p, name, y, m.n_n), m.l_n);
    lemma_dsum_empty(gs_f(m, p, name, y, m.n_n), m.l_n);
    lemma_dsum_empty(ga_f(m, p, name, y, m.n_n), m.l_n);
    lemma_g_total(m, p, name, y);
}

/// Every group's absolute mass fits `i128` once every group is merged.
proof fn lemma_caps(m: M, p: QP, es: Seq<Ent>)
    requires keys_on(m, p, es, m.l_n), m.l_n >= 0,
    ensures caps_ok(m, p),
{
    assert forall|k: Row| #[trigger] kabs(m, p, k) <= i128_max() by {
        if exists|j: int| 0 <= j < m.l_n && jok(m, p, j) && jkey(m, j) == k {
            lemma_key_form(m, p, k);
            lemma_group_val(m, p, es, k[0]->Text_0, k[1]->Num_coeff);
        } else {
            lemma_no_rows(m, p, k);
        }
    }
}

/// With every group merged through every lineitem row, the sorted rows of the entries are an allowed output.
pub proof fn lemma_final(db: Database, m: M, ps: Seq<Literal>, nrep: Seq<u64>, es: Seq<Ent>, rows: Seq<Row>, out: Seq<Row>)
    requires
        bound_ok(db, m, ps), no_like_err(m, qp_of(ps)),
        nrep_ok(m, nrep), ents_wf(m, nrep, es),
        keys_on(m, qp_of(ps), es, m.l_n),
        rows_ok(m, es, es.len() as int, rows),
        out == sort_rows(q9_keys(), rows),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    let p = qp_of(ps);
    assert(m.l_n >= 0) by { assert(frame_ok(m.l_n, m.l_bs, m.l_nb)); }
    lemma_caps(m, p, es);
    let fams = seq![3int, 1int];
    assert(all_keys_ok(q9_keys(), fams, rows));
    lemma_sort_rows(q9_keys(), fams, rows);
    // the sorted rows: the same elements, no duplicates
    rows.lemma_multiset_has_no_duplicates();
    assert forall|x: Row| out.to_multiset().contains(x) implies out.to_multiset().count(x) == 1 by {}
    out.lemma_multiset_has_no_duplicates_conv();
    assert forall|r: Row| #[trigger] out.contains(r) <==> exists|k: Row| kcnt(m, p, k) > 0 && r == krow(m, p, k) by {
        assert(out.contains(r) <==> rows.contains(r)) by {
            assert(out.to_multiset().count(r) == rows.to_multiset().count(r));
        }
        if rows.contains(r) {
            let i = choose|i: int| 0 <= i < es.len() && es[i].cell.cnt > 0 && r == erow(m, es[i]);
            let e = es[i];
            let k = gkey(ename(m, e), e.y as int);
            lemma_val_at(m, nrep, es, ename(m, e), e.y as int, i);
            lemma_group_val(m, p, es, ename(m, e), e.y as int);
            assert(krow(m, p, k) =~= erow(m, e));
            assert(kcnt(m, p, k) > 0 && r == krow(m, p, k));
        }
        if exists|k: Row| kcnt(m, p, k) > 0 && r == krow(m, p, k) {
            let k = choose|k: Row| kcnt(m, p, k) > 0 && r == krow(m, p, k);
            if !exists|j: int| 0 <= j < m.l_n && jok(m, p, j) && jkey(m, j) == k {
                lemma_no_rows(m, p, k);
            }
            lemma_key_form(m, p, k);
            let (name, y) = (k[0]->Text_0, k[1]->Num_coeff);
            lemma_group_val(m, p, es, name, y);
            assert(has_key(m, es, name, y)) by {
                if !has_key(m, es, name, y) {
                    assert(val(m, es, name, y) == super::cells::zero_cell());
                }
            }
            let i = choose|i: int| #[trigger] is_at(m, es, name, y, i);
            lemma_val_at(m, nrep, es, name, y, i);
            assert(krow(m, p, k) =~= erow(m, es[i]));
            assert(rows.contains(r));
        }
    }
    lemma_q9_ordered(db, m, ps, out);
}

} // verus!
