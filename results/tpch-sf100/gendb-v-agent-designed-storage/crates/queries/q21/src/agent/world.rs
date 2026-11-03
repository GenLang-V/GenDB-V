//! The normal form's group count over the models (`model::Cols` of storage `facts`, `side::SCols` of storage
//! `suppliers`) of a database bound to the parts. Sums over the projected tables become index sums over the models'
//! rows (`lemma_sum_rows`: through the row maps, which are permutations); then
//! - `ocnt` (a line's orders rows with status `F`) is the model's `ofound` (orders primary key, `lemma_ocnt`),
//! - the subqueries over the lineitem table are the model's `ex2` / `ex3` (`lemma_ex_bridge`),
//! - `lsum` of supplier row `r` is its counted lines `cnt` when the group key is its name (`lemma_lsum`),
//! - `ncnt` of supplier row `r` is 1 exactly when its nation is listed (nation primary key, `lemma_ncnt`),
//! so a group's count is the sum of `cnt` over the listed nations' suppliers with that name (`lemma_gcount_model`),
//! and, over the slots (`lemma_reindex`), the sum of the slot counts `tot` with that name (`lemma_gcount_slots`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::*;
use crate::link::query::*;
use crate::link::join::{sum_of, lemma_sum_of_ext, lemma_sum_of_map, lemma_sum_of_perm};
use crate::link::expr::{ival, tval};
use crate::stores::facts::interface::common::colfmt::{text_of, is_perm, stored_rows, covered, lemma_stored_rows_multiset,
    lemma_dict_distinct, text_parts_wf, dict_sorted};
use crate::stores::facts::interface::{orders_map, lineitem_map};
use super::common::isum::*;
use super::model::*;
use super::side::*;
use super::bind::*;
use super::decode::*;
use super::kernel::counts_ok;
use super::cand::slot_name;
use super::groups::{gtot, same_f};
use super::sqlrow::*;
use super::sqllink::*;
use super::typed::*;

verus! {

// ------------------------------------------------------------------------------------------------ sums by table

/// A sum over a projected relation is an index sum over its stored rows: `rel`'s rows in the order of the
/// permutation `rmap`, each projected on `cols`, are `rowf(0) .. rowf(n - 1)`.
pub proof fn lemma_sum_rows(rel: Seq<Row>, cols: Seq<nat>, rmap: Seq<int>, n: int, rowf: spec_fn(int) -> Row, f: spec_fn(Row) -> int)
    requires
        rel.len() == n,
        is_perm(rmap, n),
        forall|j: int| 0 <= j < n ==> #[trigger] proj(rel[rmap[j]], cols) == rowf(j),
    ensures
        sum_of(proj_all(rel, cols), f) == isum(n, |j: int| f(rowf(j))),
{
    let st = stored_rows(rel, rmap);
    let pf = |r: Row| f(proj(r, cols));
    let m = |r: Row| proj(r, cols);
    lemma_sum_of_map(rel, m, f);
    assert(proj_all(rel, cols) == rel.map_values(m));
    lemma_sum_of_ext(rel, |r: Row| f(m(r)), pf);
    lemma_stored_rows_multiset(rel, rmap);
    lemma_sum_of_perm(st, rel, pf);
    assert(st =~= Seq::new(n as nat, |j: int| rel[rmap[j]]));
    let rf = |j: int| rel[rmap[j]];
    let g1 = |i: int| pf(rf(i));
    let g2 = |j: int| f(rowf(j));
    lemma_sum_of_seq(n, rf, pf);
    assert forall|i: int| 0 <= i < n implies #[trigger] g1(i) == g2(i) by {
        assert(proj(rel[rmap[i]], cols) == rowf(i));
    }
    lemma_isum_ext(n, g1, g2);
}

/// The identity is a permutation.
pub proof fn lemma_id_perm(n: int)
    requires n >= 0,
    ensures is_perm(Seq::new(n as nat, |j: int| j), n),
{
    let m = Seq::new(n as nat, |j: int| j);
    assert forall|i: int| 0 <= i < n implies #[trigger] covered(m, i) by {
        assert(m[i] == i);
    }
}

// ------------------------------------------------------------------------------------------------ the bound models

/// The status dictionary index `f` is the entry `'F'`: equal exactly for that entry's index.
pub open spec fn fcode_ok(doffs: Seq<u64>, dbytes: Seq<u8>, f: int) -> bool {
    forall|d: int| 0 <= d < doffs.len() - 1 ==> (#[trigger] text_of(doffs, dbytes, d) == f_text()) == (d == f)
}

/// Everything about one bound database that the link uses.
pub open spec fn world_ok(db: Database, fparts: Seq<PartView>, sparts: Seq<PartView>, c: Cols, sc: SCols,
    doffs: Seq<u64>, dbytes: Seq<u8>, f: int) -> bool {
    &&& fbound(db, fparts)
    &&& sbound(db, sparts)
    &&& cols_from_parts(c, fparts)
    &&& scols_from_parts(sc, sparts)
    &&& fparts[p_oso()] == PartView::U64(doffs)
    &&& fparts[p_osy()] == PartView::U8(dbytes)
    &&& doffs.len() - 1 <= u64::MAX
    &&& fcode_ok(doffs, dbytes, f)
}

/// A projected lineitem row of the model: `[l_orderkey, l_suppkey, l_commitdate, l_receiptdate]` of stored row `j`.
pub open spec fn lj(c: Cols, j: int) -> Row {
    seq![Val::Int(lkey(c, j)), Val::Int(lsupp(c, j)), Val::Date(lcmt(c, j)), Val::Date(lrcp(c, j))]
}

/// A projected orders row of the model: `[o_orderkey, o_orderstatus]` of stored row `q`.
pub open spec fn oj(c: Cols, doffs: Seq<u64>, dbytes: Seq<u8>, q: int) -> Row {
    seq![Val::Int(okey(c, q)), Val::Text(text_of(doffs, dbytes, ostat(c, q)))]
}

/// A projected supplier row: `[s_suppkey, s_name, s_nationkey]` of row `r`.
pub open spec fn sj(sc: SCols, r: int) -> Row {
    seq![Val::Int(skey(sc, r)), Val::Text(sname(sc, r)), Val::Int(snat(sc, r))]
}

/// A projected nation row: `[n_nationkey, n_name]` of row `n`.
pub open spec fn nj(sc: SCols, n: int) -> Row {
    seq![Val::Int(nkey(sc, n)), Val::Text(nname(sc, n))]
}

/// Sums over the four projected tables as index sums over the models.
pub proof fn lemma_sums(db: Database, fparts: Seq<PartView>, sparts: Seq<PartView>, c: Cols, sc: SCols,
    doffs: Seq<u64>, dbytes: Seq<u8>, f: int, h: spec_fn(Row) -> int)
    requires world_ok(db, fparts, sparts, c, sc, doffs, dbytes, f),
    ensures
        sum_of(lrel(db), h) == isum(c.n_l as int, |j: int| h(lj(c, j))),
        sum_of(orel(db), h) == isum(c.n_o as int, |q: int| h(oj(c, doffs, dbytes, q))),
        sum_of(srel(db), h) == isum(sc.n_s as int, |r: int| h(sj(sc, r))),
        sum_of(nrel(db), h) == isum(sc.n_n as int, |n: int| h(nj(sc, n))),
{
    lemma_row_maps(db, fparts);
    lemma_rel_values(db);
    lemma_lineitem_cols(db, fparts, c);
    lemma_orders_cols(db, fparts, c, doffs, dbytes);
    lemma_srels(db);
    lemma_supplier_cols(db, sparts, sc);
    lemma_parts_shape(db, fparts);
    // lineitem
    let (t0, lmap) = (db.tables[0], lineitem_map(ltp(fparts), lrel_of(db).len() as int));
    let lr = lrows(fparts, db);
    assert forall|j: int| 0 <= j < c.n_l implies #[trigger] proj(t0[lmap[j]], lcols()) == lj(c, j) by {
        let i = lmap[j];
        assert(lr[j] == lrel_of(db)[i]);
        assert(proj(t0[i], lcols()) =~= lj(c, j));
    }
    lemma_sum_rows(t0, lcols(), lmap, c.n_l as int, |j: int| lj(c, j), h);
    lemma_isum_ext(c.n_l as int, |j: int| h((|j: int| lj(c, j))(j)), |j: int| h(lj(c, j)));
    // orders
    let (t1, omap) = (db.tables[1], orders_map(otp(fparts), orel_of(db).len() as int));
    let orr = orows(fparts, db);
    assert forall|q: int| 0 <= q < c.n_o implies #[trigger] proj(t1[omap[q]], ocols()) == oj(c, doffs, dbytes, q) by {
        let i = omap[q];
        assert(orr[q] == orel_of(db)[i]);
        assert(proj(t1[i], ocols()) =~= oj(c, doffs, dbytes, q));
    }
    lemma_sum_rows(t1, ocols(), omap, c.n_o as int, |q: int| oj(c, doffs, dbytes, q), h);
    lemma_isum_ext(c.n_o as int, |q: int| h((|q: int| oj(c, doffs, dbytes, q))(q)), |q: int| h(oj(c, doffs, dbytes, q)));
    // supplier and nation (canonical order)
    let id_s = Seq::new(sc.n_s as nat, |j: int| j);
    let id_n = Seq::new(sc.n_n as nat, |j: int| j);
    lemma_id_perm(sc.n_s as int);
    lemma_id_perm(sc.n_n as int);
    let t5 = db.tables[5];
    let t6 = db.tables[6];
    assert forall|r: int| 0 <= r < sc.n_s implies #[trigger] proj(t5[id_s[r]], scols()) == sj(sc, r) by {
        assert(id_s[r] == r);
        assert(srel_of(db)[r][0] == t5[r][0] && srel_of(db)[r][1] == t5[r][1] && srel_of(db)[r][3] == t5[r][3]);
        assert(proj(t5[r], scols()) =~= sj(sc, r));
    }
    assert forall|n: int| 0 <= n < sc.n_n implies #[trigger] proj(t6[id_n[n]], ncols()) == nj(sc, n) by {
        assert(id_n[n] == n);
        assert(nrel_of(db)[n][0] == t6[n][0] && nrel_of(db)[n][1] == t6[n][1]);
        assert(proj(t6[n], ncols()) =~= nj(sc, n));
    }
    lemma_sum_rows(t5, scols(), id_s, sc.n_s as int, |r: int| sj(sc, r), h);
    lemma_isum_ext(sc.n_s as int, |r: int| h((|r: int| sj(sc, r))(r)), |r: int| h(sj(sc, r)));
    lemma_sum_rows(t6, ncols(), id_n, sc.n_n as int, |n: int| nj(sc, n), h);
    lemma_isum_ext(sc.n_n as int, |n: int| h((|n: int| nj(sc, n))(n)), |n: int| h(nj(sc, n)));
}

// ------------------------------------------------------------------------------------------------ the factors

/// A line's orders rows with status `F` are its stored order's (`ofound`): 1 or 0.
pub proof fn lemma_ocnt(db: Database, fparts: Seq<PartView>, sparts: Seq<PartView>, c: Cols, sc: SCols,
    doffs: Seq<u64>, dbytes: Seq<u8>, f: int, l: Row, k: int)
    requires
        world_ok(db, fparts, sparts, c, sc, doffs, dbytes, f),
        ival(l[0]) == k,
    ensures
        ocnt(db, l) == if rpos(c, k) < c.n_o && ostat(c, rpos(c, k)) == f { 1int } else { 0int },
{
    lemma_sums(db, fparts, sparts, c, sc, doffs, dbytes, f, |o: Row| co(l, o));
    lemma_orders_cols(db, fparts, c, doffs, dbytes);
    lemma_keys_distinct(db, fparts, c, doffs, dbytes);
    let tf = |q: int| (|o: Row| co(l, o))(oj(c, doffs, dbytes, q));
    let p = rpos(c, k);
    lemma_rpos_bound(c, k);
    assert forall|q: int| 0 <= q < c.n_o implies #[trigger] tf(q) == if okey(c, q) == k && ostat(c, q) == f { 1int } else { 0int } by {
        assert(orows(fparts, db)[q][0] == Val::Int(okey(c, q)));
        assert(0 <= ostat(c, q) < doffs.len() - 1);
        assert(oj(c, doffs, dbytes, q)[0] == Val::Int(okey(c, q)));
        assert(oj(c, doffs, dbytes, q)[1] == Val::Text(text_of(doffs, dbytes, ostat(c, q))));
        assert((text_of(doffs, dbytes, ostat(c, q)) == f_text()) == (ostat(c, q) == f));
    }
    assert forall|q: int| 0 <= q < c.n_o && q != p implies #[trigger] tf(q) == 0 by {
        if okey(c, q) == k {
            lemma_rpos_of(c, q);
        }
    }
    lemma_isum_single(c.n_o as int, tf, p);
}

/// The subqueries over the lineitem table are the model's `ex2` and `ex3` of stored line `j`.
pub proof fn lemma_ex_bridge(db: Database, fparts: Seq<PartView>, c: Cols, j: int)
    requires
        fbound(db, fparts),
        cols_from_parts(c, fparts),
        0 <= j < c.n_l,
    ensures
        ex2_db(db, lkey(c, j), lsupp(c, j)) == ex2(c, j),
        ex3_db(db, lkey(c, j), lsupp(c, j)) == ex3(c, j),
{
    lemma_row_maps(db, fparts);
    lemma_rel_values(db);
    lemma_lineitem_cols(db, fparts, c);
    let t0 = db.tables[0];
    let lr = lrows(fparts, db);
    let n = lrel_of(db).len() as int;
    let lmap = lineitem_map(ltp(fparts), n);
    let (k, s) = (lkey(c, j), lsupp(c, j));
    // Row i of the table is stored row j2 with lmap[j2] == i, and conversely.
    if ex2_db(db, k, s) {
        let i = choose|i: int| 0 <= i < t0.len() && #[trigger] sub2_hit(t0[i], k, s);
        assert(covered(lmap, i));
        let j2 = choose|j2: int| 0 <= j2 < lmap.len() && lmap[j2] == i;
        assert(lr[j2] == lrel_of(db)[i]);
        assert(other(c, j2, j));
    }
    if ex2(c, j) {
        let j2 = choose|j2: int| 0 <= j2 < c.n_l && #[trigger] other(c, j2, j);
        let i = lmap[j2];
        assert(lr[j2] == lrel_of(db)[i]);
        assert(sub2_hit(t0[i], k, s));
    }
    if ex3_db(db, k, s) {
        let i = choose|i: int| 0 <= i < t0.len() && #[trigger] sub3_hit(t0[i], k, s);
        assert(covered(lmap, i));
        let j2 = choose|j2: int| 0 <= j2 < lmap.len() && lmap[j2] == i;
        assert(lr[j2] == lrel_of(db)[i]);
        assert(other(c, j2, j) && late(c, j2));
    }
    if ex3(c, j) {
        let j2 = choose|j2: int| 0 <= j2 < c.n_l && #[trigger] other(c, j2, j) && late(c, j2);
        let i = lmap[j2];
        assert(lr[j2] == lrel_of(db)[i]);
        assert(sub3_hit(t0[i], k, s));
    }
}

/// `cnt` is the index sum of its hits.
pub proof fn lemma_cnt_isum(c: Cols, f: int, s: int, n: int)
    requires n >= 0,
    ensures cnt(c, f, s, 0, n) == isum(n, |j: int| if lhit(c, f, s, j) { 1int } else { 0int }),
    decreases n,
{
    if n > 0 {
        lemma_cnt_isum(c, f, s, n - 1);
        lemma_isum_step(n - 1, |j: int| if lhit(c, f, s, j) { 1int } else { 0int });
    }
}

/// The group key of supplier row `r`: its name.
pub open spec fn skey_row(sc: SCols, r: int) -> Row {
    seq![Val::Text(sname(sc, r))]
}

/// Supplier row `r`'s counted lines for group `k`: its `cnt` when `k` is its name, else 0.
pub proof fn lemma_lsum(db: Database, fparts: Seq<PartView>, sparts: Seq<PartView>, c: Cols, sc: SCols,
    doffs: Seq<u64>, dbytes: Seq<u8>, f: int, k: Row, r: int)
    requires
        world_ok(db, fparts, sparts, c, sc, doffs, dbytes, f),
        0 <= r < sc.n_s,
    ensures
        lsum(db, k, sj(sc, r)) == if k == skey_row(sc, r) { cnt(c, f, skey(sc, r), 0, c.n_l as int) } else { 0int },
{
    let s = sj(sc, r);
    let h = |l: Row| csl(db, k, s, l) * ocnt(db, l);
    lemma_sums(db, fparts, sparts, c, sc, doffs, dbytes, f, h);
    let hit = |j: int| if lhit(c, f, skey(sc, r), j) { 1int } else { 0int };
    let kk: int = if k == skey_row(sc, r) { 1 } else { 0 };
    assert(seq![s[1]] == skey_row(sc, r)) by {
        assert(seq![s[1]] =~= skey_row(sc, r));
    }
    assert forall|j: int| 0 <= j < c.n_l implies #[trigger] h(lj(c, j)) == kk * hit(j) by {
        let l = lj(c, j);
        assert(l[0] == Val::Int(lkey(c, j)) && l[1] == Val::Int(lsupp(c, j)) && l[2] == Val::Date(lcmt(c, j)) && l[3] == Val::Date(lrcp(c, j)));
        lemma_ocnt(db, fparts, sparts, c, sc, doffs, dbytes, f, l, lkey(c, j));
        lemma_ex_bridge(db, fparts, c, j);
        let a = csl(db, k, s, l);
        let b = ocnt(db, l);
        assert(a * b == kk * hit(j)) by {
            if a == 1 && b == 1 {
                assert(lhit(c, f, skey(sc, r), j));
            } else {
                assert(a * b == 0) by (nonlinear_arith) requires a == 0 || b == 0;
                if kk == 1 && hit(j) == 1 {
                    assert(lineq(c, f, j));
                }
            }
        }
    }
    lemma_isum_ext(c.n_l as int, |j: int| h(lj(c, j)), |j: int| kk * hit(j));
    lemma_isum_scale(c.n_l as int, hit, kk);
    lemma_cnt_isum(c, f, skey(sc, r), c.n_l as int);
}

/// Supplier row `r` joins one nation row named `nm` exactly when its nation key is listed (`nks_ok`), else none.
pub proof fn lemma_ncnt(db: Database, fparts: Seq<PartView>, sparts: Seq<PartView>, c: Cols, sc: SCols,
    doffs: Seq<u64>, dbytes: Seq<u8>, f: int, nm: Seq<u8>, nks: Seq<i64>, nwit: Seq<int>, r: int)
    requires
        world_ok(db, fparts, sparts, c, sc, doffs, dbytes, f),
        nks_ok(sc, nm, nks, nwit),
        0 <= r < sc.n_s,
    ensures
        ncnt(db, nm, sj(sc, r)) == if in_nation(sc, nks, r) { 1int } else { 0int },
{
    let s = sj(sc, r);
    let h = |n: Row| cn(nm, s, n);
    lemma_sums(db, fparts, sparts, c, sc, doffs, dbytes, f, h);
    lemma_srels(db);
    lemma_supplier_cols(db, sparts, sc);
    lemma_scols_bounds(db, sparts, sc);
    let tf = |n: int| h(nj(sc, n));
    assert forall|n: int| 0 <= n < sc.n_n implies #[trigger] tf(n) == if snat(sc, r) == nkey(sc, n) && nname(sc, n) == nm { 1int } else { 0int } by {}
    if in_nation(sc, nks, r) {
        let i = choose|i: int| 0 <= i < nks.len() && nks[i] == snat(sc, r) as i64;
        let n0 = nwit[i];
        assert(0 <= n0 < sc.n_n && nname(sc, n0) == nm && nks[i] == nkey(sc, n0));
        assert forall|n: int| 0 <= n < sc.n_n && n != n0 implies #[trigger] tf(n) == 0 by {
            if snat(sc, r) == nkey(sc, n) {
                lemma_nkey_distinct(db, sparts, sc, n, n0);
            }
        }
        lemma_isum_single(sc.n_n as int, tf, n0);
    } else {
        assert forall|n: int| 0 <= n < sc.n_n implies #[trigger] tf(n) == 0 by {
            if snat(sc, r) == nkey(sc, n) && nname(sc, n) == nm {
                assert(nks.contains(nkey(sc, n) as i64));
            }
        }
        lemma_isum_zero(sc.n_n as int, tf);
    }
}

/// Supplier and nation model values fit `i64` (they are the stored relations' integers).
pub proof fn lemma_scols_bounds(db: Database, sparts: Seq<PartView>, sc: SCols)
    requires sbound(db, sparts), scols_from_parts(sc, sparts),
    ensures
        forall|r: int| 0 <= r < sc.n_s ==> in_i64(#[trigger] skey(sc, r)) && in_i64(snat(sc, r)),
        forall|r: int| 0 <= r < sc.n_s ==> in_i64(#[trigger] snat(sc, r)),
        forall|n: int| 0 <= n < sc.n_n ==> in_i64(#[trigger] nkey(sc, n)),
{
    lemma_srels(db);
    lemma_supplier_cols(db, sparts, sc);
    lemma_tables_typed(db);
    crate::stores::suppliers::declaration::lemma_declared_schema();
    let s = crate::schema::schema_spec();
    assert forall|r: int| 0 <= r < sc.n_s implies in_i64(#[trigger] skey(sc, r)) && in_i64(snat(sc, r)) by {
        let row = db.tables[5][r];
        assert(srel_of(db)[r][0] == row[0] && srel_of(db)[r][3] == row[3]);
        assert(srel_of(db)[r][0] == Val::Int(skey(sc, r)) && srel_of(db)[r][3] == Val::Int(snat(sc, r)));
        assert(crate::spec::typing::row_in_table(row, db.schema[5]));
        assert(crate::spec::typing::value_in_column(row[0], s[5].columns[0]));
        assert(crate::spec::typing::value_in_column(row[3], s[5].columns[3]));
        assert(s[5].columns[0] == crate::stores::suppliers::declaration::stored_columns_t1()[0]);
        assert(s[5].columns[3] == crate::stores::suppliers::declaration::stored_columns_t1()[3]);
    }
    assert forall|r: int| 0 <= r < sc.n_s implies in_i64(#[trigger] snat(sc, r)) by {
        assert(in_i64(skey(sc, r)));
    }
    assert forall|n: int| 0 <= n < sc.n_n implies in_i64(#[trigger] nkey(sc, n)) by {
        let row = db.tables[6][n];
        assert(nrel_of(db)[n][0] == row[0]);
        assert(nrel_of(db)[n][0] == Val::Int(nkey(sc, n)));
        assert(crate::spec::typing::row_in_table(row, db.schema[6]));
        assert(crate::spec::typing::value_in_column(row[0], s[6].columns[0]));
        assert(s[6].columns[0] == crate::stores::suppliers::declaration::stored_columns_t2()[0]);
    }
}

/// Under the nation primary key, two nation rows with one key are one row.
pub proof fn lemma_nkey_distinct(db: Database, sparts: Seq<PartView>, sc: SCols, a: int, b: int)
    requires
        sbound(db, sparts), scols_from_parts(sc, sparts),
        0 <= a < sc.n_n, 0 <= b < sc.n_n,
        nkey(sc, a) == nkey(sc, b),
    ensures a == b,
{
    lemma_srels(db);
    lemma_supplier_cols(db, sparts, sc);
    assert(nrel_of(db)[a][0] == db.tables[6][a][0] && nrel_of(db)[b][0] == db.tables[6][b][0]);
    assert(nrel_of(db)[a][0] == Val::Int(nkey(sc, a)) && nrel_of(db)[b][0] == Val::Int(nkey(sc, b)));
    if a != b {
        lemma_pk0(db, 6, a, b);
    }
}

/// Under the supplier primary key, two supplier rows with one key are one row.
pub proof fn lemma_skey_distinct(db: Database, sparts: Seq<PartView>, sc: SCols, a: int, b: int)
    requires
        sbound(db, sparts), scols_from_parts(sc, sparts),
        0 <= a < sc.n_s, 0 <= b < sc.n_s,
        skey(sc, a) == skey(sc, b),
    ensures a == b,
{
    lemma_srels(db);
    lemma_supplier_cols(db, sparts, sc);
    assert(srel_of(db)[a][0] == db.tables[5][a][0] && srel_of(db)[b][0] == db.tables[5][b][0]);
    assert(srel_of(db)[a][0] == Val::Int(skey(sc, a)) && srel_of(db)[b][0] == Val::Int(skey(sc, b)));
    if a != b {
        lemma_pk0(db, 5, a, b);
    }
}

// ------------------------------------------------------------------------------------------------ the group count

/// Supplier row `r`'s contribution to group `k`.
pub open spec fn rterm(c: Cols, sc: SCols, nks: Seq<i64>, f: int, k: Row) -> spec_fn(int) -> int {
    |r: int| if in_nation(sc, nks, r) && k == skey_row(sc, r) { cnt(c, f, skey(sc, r), 0, c.n_l as int) } else { 0int }
}

/// A group's count is the sum over the listed nations' supplier rows with that name of their counted lines.
pub proof fn lemma_gcount_model(db: Database, fparts: Seq<PartView>, sparts: Seq<PartView>, c: Cols, sc: SCols,
    doffs: Seq<u64>, dbytes: Seq<u8>, f: int, nm: Seq<u8>, nks: Seq<i64>, nwit: Seq<int>, k: Row)
    requires
        world_ok(db, fparts, sparts, c, sc, doffs, dbytes, f),
        nks_ok(sc, nm, nks, nwit),
    ensures
        gcount(q21_g(db, nm), q21_xs(db), k) == isum(sc.n_s as int, rterm(c, sc, nks, f, k)),
{
    lemma_tables_typed(db);
    lemma_gcount_factor(db, nm, k);
    let h = |s: Row| ncnt(db, nm, s) * lsum(db, k, s);
    lemma_sums(db, fparts, sparts, c, sc, doffs, dbytes, f, h);
    assert forall|r: int| 0 <= r < sc.n_s implies #[trigger] h(sj(sc, r)) == rterm(c, sc, nks, f, k)(r) by {
        lemma_ncnt(db, fparts, sparts, c, sc, doffs, dbytes, f, nm, nks, nwit, r);
        lemma_lsum(db, fparts, sparts, c, sc, doffs, dbytes, f, k, r);
    }
    lemma_isum_ext(sc.n_s as int, |r: int| h(sj(sc, r)), rterm(c, sc, nks, f, k));
}

/// Reindexing: the sum over the rows the slots enumerate (increasing, each listed once) is the sum over the slots.
pub proof fn lemma_reindex(n: int, p: spec_fn(int) -> bool, h: spec_fn(int) -> int, rows: Seq<usize>, b: int, m: int)
    requires
        0 <= b <= n <= usize::MAX,
        0 <= m <= rows.len(),
        forall|t: int| 0 <= t < rows.len() ==> #[trigger] rows[t] < n && p(rows[t] as int),
        forall|a: int, t: int| 0 <= a < t < rows.len() ==> #[trigger] rows[a] < #[trigger] rows[t],
        forall|r: int| 0 <= r < n && #[trigger] p(r) ==> rows.contains(r as usize),
        forall|t: int| 0 <= t < m ==> #[trigger] rows[t] < b,
        forall|t: int| m <= t < rows.len() ==> #[trigger] rows[t] >= b,
    ensures
        isum(b, |r: int| if p(r) { h(r) } else { 0int }) == isum(m, |t: int| h(rows[t] as int)),
    decreases b,
{
    let fr = |r: int| if p(r) { h(r) } else { 0int };
    let ft = |t: int| h(rows[t] as int);
    if b > 0 {
        let r = b - 1;
        if p(r) {
            assert(rows.contains(r as usize));
            let t0 = choose|t: int| 0 <= t < rows.len() && rows[t] == r as usize;
            assert(rows[t0] as int == r);
            // t0 is the last slot below b.
            assert(t0 < m) by {
                if t0 >= m {
                    assert(rows[t0] >= b);
                }
            }
            assert(t0 == m - 1) by {
                if t0 < m - 1 {
                    assert(0 <= t0 < m - 1 < rows.len());
                    assert(rows[t0] < rows[m - 1]);
                    assert(rows[m - 1] < b);
                    assert(false);
                }
            }
            lemma_reindex(n, p, h, rows, b - 1, m - 1);
            lemma_isum_step(b - 1, fr);
            lemma_isum_step(m - 1, ft);
        } else {
            assert forall|t: int| 0 <= t < m implies #[trigger] rows[t] < b - 1 by {
                assert(p(rows[t] as int));
                assert(rows[t] as int != r);
                assert(rows[t] < b);
            }
            lemma_reindex(n, p, h, rows, b - 1, m);
            lemma_isum_step(b - 1, fr);
        }
    } else {
        assert(m == 0) by {
            if m > 0 {
                assert(rows[0] < b);
            }
        }
    }
}

/// Slot `t`'s contribution to group `k`.
pub open spec fn tterm(sc: SCols, srows: Seq<usize>, tot: Seq<usize>, k: Row) -> spec_fn(int) -> int {
    |t: int| if k == seq![Val::Text(slot_name(sc, srows, t))] { tot[t] as int } else { 0int }
}

/// A group's count is the sum of the slot counts with that name.
pub proof fn lemma_gcount_slots(db: Database, fparts: Seq<PartView>, sparts: Seq<PartView>, c: Cols, sc: SCols,
    doffs: Seq<u64>, dbytes: Seq<u8>, f: int, nm: Seq<u8>, nks: Seq<i64>, nwit: Seq<int>, srows: Seq<usize>,
    skeys: Seq<i64>, tot: Seq<usize>, k: Row)
    requires
        world_ok(db, fparts, sparts, c, sc, doffs, dbytes, f),
        nks_ok(sc, nm, nks, nwit),
        slots_ok(sc, nks, srows, skeys),
        counts_ok(c, f, skeys, tot, 0, c.n_l as int),
    ensures
        gcount(q21_g(db, nm), q21_xs(db), k) == isum(srows.len() as int, tterm(sc, srows, tot, k)),
{
    lemma_gcount_model(db, fparts, sparts, c, sc, doffs, dbytes, f, nm, nks, nwit, k);
    let p = |r: int| in_nation(sc, nks, r);
    let h = |r: int| if k == skey_row(sc, r) { cnt(c, f, skey(sc, r), 0, c.n_l as int) } else { 0int };
    lemma_isum_ext(sc.n_s as int, rterm(c, sc, nks, f, k), |r: int| if p(r) { h(r) } else { 0int });
    lemma_reindex(sc.n_s as int, p, h, srows, sc.n_s as int, srows.len() as int);
    assert forall|t: int| 0 <= t < srows.len() implies #[trigger] h(srows[t] as int) == tterm(sc, srows, tot, k)(t) by {
        assert(skeys[t] == skey(sc, srows[t] as int));
        assert(tot[t] as int == cnt(c, f, skeys[t] as int, 0, c.n_l as int));
    }
    lemma_isum_ext(srows.len() as int, |t: int| h(srows[t] as int), tterm(sc, srows, tot, k));
}

/// The count of slot `t`'s name group is `gtot(t)`.
pub proof fn lemma_tterm_gtot(sc: SCols, srows: Seq<usize>, tot: Seq<usize>, t: int)
    requires tot.len() == srows.len(), 0 <= t < srows.len(),
    ensures isum(srows.len() as int, tterm(sc, srows, tot, seq![Val::Text(slot_name(sc, srows, t))])) == gtot(sc, srows, tot, t),
{
    let k = seq![Val::Text(slot_name(sc, srows, t))];
    assert forall|u: int| 0 <= u < srows.len() implies #[trigger] tterm(sc, srows, tot, k)(u) == same_f(sc, srows, tot, t)(u) by {
        if slot_name(sc, srows, u) == slot_name(sc, srows, t) {
            assert(k == seq![Val::Text(slot_name(sc, srows, u))]);
        } else {
            assert(k[0] != seq![Val::Text(slot_name(sc, srows, u))][0]);
        }
    }
    lemma_isum_ext(srows.len() as int, tterm(sc, srows, tot, k), same_f(sc, srows, tot, t));
}


/// What the storage contract gives about the supplier and nation group parts and name texts.
proof fn lemma_s_facts(db: Database, sparts: Seq<PartView>)
    requires sbound(db, sparts),
    ensures
        crate::stores::suppliers::interface::common::colfmt::groups_part_ok(sparts[p_sg()], srel_of(db).len() as int,
            crate::stores::suppliers::interface::common::colfmt::u64s(sparts[p_sl()])[1] as int),
        crate::stores::suppliers::interface::common::colfmt::groups_part_ok(sparts[p_ng()], nrel_of(db).len() as int,
            crate::stores::suppliers::interface::common::colfmt::u64s(sparts[p_nl()])[1] as int),
        crate::stores::suppliers::interface::common::colfmt::text_parts_wf(
            crate::stores::suppliers::interface::common::colfmt::u64s(sparts[p_smo()]),
            crate::stores::suppliers::interface::common::colfmt::u8s(sparts[p_smy()]), srel_of(db).len() as int),
        crate::stores::suppliers::interface::common::colfmt::text_parts_wf(
            crate::stores::suppliers::interface::common::colfmt::u64s(sparts[p_nmo()]),
            crate::stores::suppliers::interface::common::colfmt::u8s(sparts[p_nmy()]), nrel_of(db).len() as int),
{
    use crate::stores::suppliers::interface as si;
    let st = stp(sparts);
    let nt = ntp(sparts);
    assert(si::supplier_ok(st, srel_of(db)));
    assert(si::nation_ok(nt, nrel_of(db)));
    assert(st[si::SU_LAYOUT as int] == sparts[p_sl()]);
    assert(st[si::SU_GROUPS as int] == sparts[p_sg()]);
    assert(st[si::SU_NAME_OFFS as int] == sparts[p_smo()]);
    assert(st[si::SU_NAME_BYTES as int] == sparts[p_smy()]);
    assert(nt[si::NA_LAYOUT as int] == sparts[p_nl()]);
    assert(nt[si::NA_GROUPS as int] == sparts[p_ng()]);
    assert(nt[si::NA_NAME_OFFS as int] == sparts[p_nmo()]);
    assert(nt[si::NA_NAME_BYTES as int] == sparts[p_nmy()]);
}

/// Uniform groups of `sbs` rows over `n` rows, seen with a model group size `b` (`bind::bs_ok`): the bases cover
/// the rows.
proof fn lemma_blocks_cover(gp: PartView, n: int, sbs: int, b: int, nbases: int)
    requires
        crate::stores::suppliers::interface::common::colfmt::groups_part_ok(gp, n, sbs),
        crate::stores::suppliers::interface::common::colfmt::u64s(gp).len() - 1 == nbases,
        bs_ok(b, sbs, n),
    ensures nbases * b >= n,
{
    use crate::stores::suppliers::interface::common::colfmt as sf;
    sf::lemma_uniform_groups(gp, n, sbs);
    sf::lemma_nblocks(n, sbs);
    if b != sbs && n > 0 {
        assert(sf::nblocks_of(n, sbs) >= 1);
        assert(nbases * b >= b) by (nonlinear_arith) requires nbases >= 1, b >= 1;
    }
}

/// The supplier-side model's facts (`side::scols_ok`) for a database bound to the parts.
pub proof fn lemma_scols_ok(db: Database, sparts: Seq<PartView>, sc: SCols)
    requires sbound(db, sparts), scols_from_parts(sc, sparts),
    ensures scols_ok(sc),
{
    lemma_sparts_shape(db, sparts);
    lemma_s_facts(db, sparts);
    lemma_blocks_cover(sparts[p_sg()], sc.n_s as int, crate::stores::suppliers::interface::common::colfmt::u64s(sparts[p_sl()])[1] as int,
        sc.bs_s as int, sc.sk_bases@.len() as int);
    lemma_blocks_cover(sparts[p_ng()], sc.n_n as int, crate::stores::suppliers::interface::common::colfmt::u64s(sparts[p_nl()])[1] as int,
        sc.bs_n as int, sc.nk_bases@.len() as int);
    lemma_scols_bounds(db, sparts, sc);
    assert(sc.bs_s >= 1);
    assert(sc.bs_n >= 1);
    assert(sc.sk_codes@.len() == sc.n_s);
    assert(sc.sn_codes@.len() == sc.n_s);
    assert(sc.sn_bases@.len() == sc.sk_bases@.len());
    assert(sc.sk_bases@.len() * sc.bs_s >= sc.n_s);
    {
        use crate::stores::suppliers::interface::common::colfmt as sf;
        assert(sf::u64s(sparts[p_smo()]) == sc.sm_offs@ && sf::u8s(sparts[p_smy()]) == sc.sm_bytes@);
        assert(sf::u64s(sparts[p_nmo()]) == sc.nm_offs@ && sf::u8s(sparts[p_nmy()]) == sc.nm_bytes@);
        assert(srel_of(db).len() == sc.n_s && nrel_of(db).len() == sc.n_n);
        assert(sf::text_parts_wf(sc.sm_offs@, sc.sm_bytes@, sc.n_s as int));
        assert(sf::text_parts_wf(sc.nm_offs@, sc.nm_bytes@, sc.n_n as int));
    }
    assert(sc.nk_codes@.len() == sc.n_n);
    assert(sc.nk_bases@.len() * sc.bs_n >= sc.n_n);
}

} // verus!
