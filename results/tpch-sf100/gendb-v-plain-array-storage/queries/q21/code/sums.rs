//! The group counts of the normal form over the joined rows are the stored-column counts `nf::gc`
//! (`lemma_gcount_gc`).
//!
//! `gcount` over the projected product is the sum of the per-row count term over the product rows; the product is
//! left-deep `((S x L) x O) x N`, so the sum is the nested sum over supplier rows `a`, lineitem rows `i`, orders rows
//! `b` and nation rows `n` of `jt(a, i, b, n)` (`link::join::lemma_sum_of_product`, `common::rowsum`). The condition
//! of a joined row splits into a supplier-lineitem part (`ca`), a lineitem-orders part (`cb`) and a supplier-nation
//! part (`nhit`), so the inner sums close level by level: over nations to the nation weight `nw` (`lemma_n_closed`),
//! over orders to the order weight `ofs` (`lemma_o_closed`), over lineitem rows to the key count `ksum`
//! (`lemma_l_closed`) and over suppliers to `gsum_s` (`lemma_s_closed`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::relation::product_rows;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::link::query::*;
use crate::link::join::{sum_of, count_term, lemma_acc_sum_of, lemma_sum_of_product, lemma_sum_of_map, lemma_sum_of_ext};
use crate::agent::cols::*;
use crate::agent::nf::*;
use crate::agent::denot::*;
use crate::agent::common::rowsum::*;

verus! {

// ------------------------------------------------------------------------------------------------ the parts

/// The supplier-lineitem part of the condition, with the group name: supplier `a` supplies the waiting row `i`.
pub open spec fn ca(sv: StoresView, nm: Seq<u8>, a: int, i: int) -> bool {
    skey(sv)[a] == ls(sv)[i] && lq(sv, i) && sname(sv, a) == nm
}

/// The lineitem-orders part: orders row `b` is row `i`'s order and has status `F`.
pub open spec fn cb(sv: StoresView, i: int, b: int) -> bool { ok(sv)[b] == lk(sv)[i] && fstat(sv, b) }

/// The count term of joined row `(a, i, b, n)` for group `nm`.
pub open spec fn jt(sv: StoresView, p: Seq<u8>, nm: Seq<u8>, a: int, i: int, b: int, n: int) -> int {
    if jqual(sv, p, JRow { a, i, b, n }) && sname(sv, a) == nm { 1 } else { 0 }
}

/// The closed sum over nations, over orders and over lineitem rows.
pub open spec fn ntot(sv: StoresView, p: Seq<u8>, nm: Seq<u8>, a: int, i: int, b: int) -> int {
    if ca(sv, nm, a, i) && cb(sv, i, b) { nw(sv, p, a) as int } else { 0 }
}

pub open spec fn otot(sv: StoresView, p: Seq<u8>, nm: Seq<u8>, a: int, i: int) -> int {
    if ca(sv, nm, a, i) { (nw(sv, p, a) * ofs(sv, lk(sv)[i] as int)) as int } else { 0 }
}

pub open spec fn ltot(sv: StoresView, p: Seq<u8>, nm: Seq<u8>, a: int) -> int {
    if sname(sv, a) == nm { (nw(sv, p, a) * ksum(sv, skey(sv)[a] as int, 0, n_l(sv))) as int } else { 0 }
}

// ------------------------------------------------------------------------------------------------ closing the sums

/// Over nations: the count of nations named `p` with supplier `a`'s nation key, when the other parts hold.
pub proof fn lemma_n_closed(sv: StoresView, p: Seq<u8>, nm: Seq<u8>, a: int, i: int, b: int, m: int)
    requires 0 <= m,
    ensures isum(|n: int| jt(sv, p, nm, a, i, b, n), m)
        == if ca(sv, nm, a, i) && cb(sv, i, b) { ncnt(sv, p, snk(sv)[a] as int, m) as int } else { 0 },
    decreases m,
{
    hide(lq);
    hide(q_qual);
    if m > 0 {
        lemma_n_closed(sv, p, nm, a, i, b, m - 1);
    }
}

/// Over orders: the nation weight times the order weight of row `i`'s key, when the supplier part holds.
pub proof fn lemma_o_closed(sv: StoresView, p: Seq<u8>, nm: Seq<u8>, a: int, i: int, m: int)
    requires 0 <= m,
    ensures isum(|b: int| ntot(sv, p, nm, a, i, b), m)
        == if ca(sv, nm, a, i) { (nw(sv, p, a) * ocnt(sv, lk(sv)[i] as int, m)) as int } else { 0 },
    decreases m,
{
    hide(lq);
    if m > 0 {
        lemma_o_closed(sv, p, nm, a, i, m - 1);
        let h = |b: int| ntot(sv, p, nm, a, i, b);
        assert(isum(h, m) == isum(h, m - 1) + h(m - 1));
        let w = nw(sv, p, a) as int;
        let x = ocnt(sv, lk(sv)[i] as int, m - 1) as int;
        let y: int = if ohit(sv, lk(sv)[i] as int, m - 1) { 1 } else { 0 };
        assert(ocnt(sv, lk(sv)[i] as int, m) as int == x + y);
        assert(cb(sv, i, m - 1) == ohit(sv, lk(sv)[i] as int, m - 1));
        if ca(sv, nm, a, i) {
            assert(h(m - 1) == w * y);
            assert(w * x + w * y == w * (x + y)) by (nonlinear_arith);
            assert((nw(sv, p, a) * ocnt(sv, lk(sv)[i] as int, m)) as int == w * (x + y));
        } else {
            assert(h(m - 1) == 0);
        }
    } else {
        assert(ocnt(sv, lk(sv)[i] as int, m) == 0);
        assert(nw(sv, p, a) * 0 == 0);
    }
}

/// Over lineitem rows: the nation weight times the count of supplier `a`'s key, when `a` is named `nm`.
pub proof fn lemma_l_closed(sv: StoresView, p: Seq<u8>, nm: Seq<u8>, a: int, m: int)
    requires 0 <= m,
    ensures isum(|i: int| otot(sv, p, nm, a, i), m)
        == if sname(sv, a) == nm { (nw(sv, p, a) * ksum(sv, skey(sv)[a] as int, 0, m)) as int } else { 0 },
    decreases m,
{
    hide(lq);
    if m > 0 {
        lemma_l_closed(sv, p, nm, a, m - 1);
        let h = |i: int| otot(sv, p, nm, a, i);
        assert(isum(h, m) == isum(h, m - 1) + h(m - 1));
        let v = skey(sv)[a] as int;
        let w = nw(sv, p, a) as int;
        let x = ksum(sv, v, 0, m - 1) as int;
        let y = lterm(sv, v, m - 1) as int;
        assert(ksum(sv, v, 0, m) as int == x + y);
        if sname(sv, a) == nm {
            assert(ca(sv, nm, a, m - 1) == (ls(sv)[m - 1] as int == v && lq(sv, m - 1)));
            assert(h(m - 1) == w * y);
            assert(w * x + w * y == w * (x + y)) by (nonlinear_arith);
            assert((nw(sv, p, a) * ksum(sv, v, 0, m)) as int == w * (x + y));
        } else {
            assert(h(m - 1) == 0);
        }
    } else {
        assert(ksum(sv, skey(sv)[a] as int, 0, m) == 0);
        assert(nw(sv, p, a) * 0 == 0);
    }
}

/// Over suppliers: the group count.
pub proof fn lemma_s_closed(sv: StoresView, p: Seq<u8>, nm: Seq<u8>, m: int)
    requires 0 <= m,
    ensures isum(|a: int| ltot(sv, p, nm, a), m) == gsum_s(sv, p, nm, m),
    decreases m,
{
    hide(lq);
    hide(q_qual);
    if m > 0 {
        lemma_s_closed(sv, p, nm, m - 1);
    }
}

// ------------------------------------------------------------------------------------------------ the product

/// The count term over full joined rows.
pub open spec fn fr(sv: StoresView, p: Seq<u8>, k: Row) -> spec_fn(Row) -> int {
    |r: Row| count_term(q_spec(sv, p), k)(proj(r, q_cols()))
}

pub open spec fn f1(sv: StoresView, p: Seq<u8>, k: Row, db: Database) -> spec_fn(Row) -> int {
    |x: Row| sum_of(db.tables[6], |y: Row| fr(sv, p, k)(x + y))
}

pub open spec fn f2(sv: StoresView, p: Seq<u8>, k: Row, db: Database) -> spec_fn(Row) -> int {
    |x: Row| sum_of(db.tables[1], |y: Row| f1(sv, p, k, db)(x + y))
}

pub open spec fn f3(sv: StoresView, p: Seq<u8>, k: Row, db: Database) -> spec_fn(Row) -> int {
    |x: Row| sum_of(db.tables[0], |y: Row| f2(sv, p, k, db)(x + y))
}

/// The count term of a joined row is `jt`.
proof fn lemma_fr_joined(sv: StoresView, db: Database, p: Seq<u8>, nm: Seq<u8>, w: JRow)
    requires bound_db(sv, db), jrow_ok(sv, w),
    ensures fr(sv, p, seq![Val::Text(nm)])(joined(db, w.a, w.i, w.b, w.n)) == jt(sv, p, nm, w.a, w.i, w.b, w.n),
{
    lemma_joined_normal_form(sv, db, p, w);
    let k = seq![Val::Text(nm)];
    let ks = seq![Val::Text(sname(sv, w.a))];
    if ks == k {
        assert(ks[0] == k[0]);
    }
    if sname(sv, w.a) == nm {
        assert(ks =~= k);
    }
}

/// Level 1 (nations): `f1` of `S[a] ++ L[i] ++ O[b]` is `ntot`.
#[verifier::spinoff_prover]
proof fn lemma_f1(sv: StoresView, db: Database, p: Seq<u8>, nm: Seq<u8>, a: int, i: int, b: int)
    requires bound_db(sv, db), 0 <= a < n_s(sv), 0 <= i < n_l(sv), 0 <= b < n_o(sv),
    ensures f1(sv, p, seq![Val::Text(nm)], db)(db.tables[5][a] + db.tables[0][i] + db.tables[1][b]) == ntot(sv, p, nm, a, i, b),
{
    hide(lq);
    hide(q_qual);
    lemma_parts_shape(sv, db);
    let k = seq![Val::Text(nm)];
    let x = db.tables[5][a] + db.tables[0][i] + db.tables[1][b];
    let t6 = db.tables[6];
    let f = |y: Row| fr(sv, p, k)(x + y);
    let h = |n: int| jt(sv, p, nm, a, i, b, n);
    assert forall|n: int| 0 <= n < t6.len() implies #[trigger] h(n) == f(t6[n]) by {
        reveal(joined);
        assert(x + t6[n] == joined(db, a, i, b, n));
        lemma_fr_joined(sv, db, p, nm, JRow { a, i, b, n });
    }
    lemma_sum_rows(t6, f, h);
    lemma_n_closed(sv, p, nm, a, i, b, n_n(sv));
}

/// Level 2 (orders): `f2` of `S[a] ++ L[i]` is `otot`.
#[verifier::spinoff_prover]
proof fn lemma_f2(sv: StoresView, db: Database, p: Seq<u8>, nm: Seq<u8>, a: int, i: int)
    requires bound_db(sv, db), 0 <= a < n_s(sv), 0 <= i < n_l(sv),
    ensures f2(sv, p, seq![Val::Text(nm)], db)(db.tables[5][a] + db.tables[0][i]) == otot(sv, p, nm, a, i),
{
    hide(lq);
    hide(q_qual);
    lemma_parts_shape(sv, db);
    let k = seq![Val::Text(nm)];
    let x = db.tables[5][a] + db.tables[0][i];
    let t1 = db.tables[1];
    let f = |y: Row| f1(sv, p, k, db)(x + y);
    let h = |b: int| ntot(sv, p, nm, a, i, b);
    assert forall|b: int| 0 <= b < t1.len() implies #[trigger] h(b) == f(t1[b]) by {
        lemma_f1(sv, db, p, nm, a, i, b);
    }
    lemma_sum_rows(t1, f, h);
    lemma_o_closed(sv, p, nm, a, i, n_o(sv));
}

/// Level 3 (lineitem): `f3` of `S[a]` is `ltot`.
#[verifier::spinoff_prover]
proof fn lemma_f3(sv: StoresView, db: Database, p: Seq<u8>, nm: Seq<u8>, a: int)
    requires bound_db(sv, db), 0 <= a < n_s(sv),
    ensures f3(sv, p, seq![Val::Text(nm)], db)(db.tables[5][a]) == ltot(sv, p, nm, a),
{
    hide(lq);
    hide(q_qual);
    lemma_parts_shape(sv, db);
    let k = seq![Val::Text(nm)];
    let x = db.tables[5][a];
    let t0 = db.tables[0];
    let f = |y: Row| f2(sv, p, k, db)(x + y);
    let h = |i: int| otot(sv, p, nm, a, i);
    assert forall|i: int| 0 <= i < t0.len() implies #[trigger] h(i) == f(t0[i]) by {
        lemma_f2(sv, db, p, nm, a, i);
    }
    lemma_sum_rows(t0, f, h);
    lemma_l_closed(sv, p, nm, a, n_l(sv));
}

/// The group count of key `[nm]` over the projected joined rows is `gc(nm)`.
#[verifier::spinoff_prover]
pub proof fn lemma_gcount_gc(sv: StoresView, db: Database, p: Seq<u8>, nm: Seq<u8>)
    requires bound_db(sv, db),
    ensures gcount(q_spec(sv, p), q_xs(db), seq![Val::Text(nm)]) == gc(sv, p, nm),
{
    hide(lq);
    hide(q_qual);
    lemma_parts_shape(sv, db);
    let g = q_spec(sv, p);
    let k = seq![Val::Text(nm)];
    let rows = q_rows(db);
    let (t5, t0, t1, t6) = (db.tables[5], db.tables[0], db.tables[1], db.tables[6]);
    let sl = product_rows(t5, t0);
    let slo = product_rows(sl, t1);
    // gcount over the projection = sum over the full rows
    lemma_acc_sum_of(g, q_xs(db), k, 0);
    let m = |r: Row| proj(r, q_cols());
    assert(q_xs(db) == rows.map_values(m));
    lemma_sum_of_map(rows, m, count_term(g, k));
    lemma_sum_of_ext(rows, |r: Row| count_term(g, k)(m(r)), fr(sv, p, k));
    // the three product levels
    lemma_sum_of_product(slo, t6, fr(sv, p, k));
    lemma_sum_of_ext(slo, |x: Row| sum_of(t6, |y: Row| fr(sv, p, k)(x + y)), f1(sv, p, k, db));
    lemma_sum_of_product(sl, t1, f1(sv, p, k, db));
    lemma_sum_of_ext(sl, |x: Row| sum_of(t1, |y: Row| f1(sv, p, k, db)(x + y)), f2(sv, p, k, db));
    lemma_sum_of_product(t5, t0, f2(sv, p, k, db));
    lemma_sum_of_ext(t5, |x: Row| sum_of(t0, |y: Row| f2(sv, p, k, db)(x + y)), f3(sv, p, k, db));
    // the outer sum over suppliers
    let h = |a: int| ltot(sv, p, nm, a);
    assert forall|a: int| 0 <= a < t5.len() implies #[trigger] h(a) == f3(sv, p, k, db)(t5[a]) by {
        lemma_f3(sv, db, p, nm, a);
    }
    lemma_sum_rows(t5, f3(sv, p, k, db), h);
    lemma_s_closed(sv, p, nm, n_s(sv));
}

/// A group with a qualifying row has a one-text key.
pub proof fn lemma_gcount_key(sv: StoresView, db: Database, p: Seq<u8>, k: Row)
    requires bound_db(sv, db), gcount(q_spec(sv, p), q_xs(db), k) > 0,
    ensures k == seq![Val::Text(k[0]->Text_0)],
{
    let g = q_spec(sv, p);
    let xs = q_xs(db);
    lemma_count_witness(g, xs, k);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
    lemma_key_types(sv, db, p, m);
    assert(k =~= seq![Val::Text(k[0]->Text_0)]);
}

} // verus!
