//! The statement's answers: the collected groups in count order are an allowed output (`lemma_final`); a failing
//! LIKE (`lemma_like_err`) or a count beyond int8 (`lemma_overflow`) is the statement's error. `answer_columns`
//! builds the columnar answer of the ordered groups.
//!
//! The GROUP BY's rows are, without duplicates, `key + [COUNT(DISTINCT)]` for the keys of the kept rows
//! (`common::distinct::lemma_group_count_distinct`). A key of a kept row is the part key of a qualifying pair
//! (`answer::lemma_keys_has`), so it is `key_bt` of the pair's (brand entry, type entry, size slot), a group with a
//! positive count (`lemma_key_group`); the collected groups hold every such group with its count
//! (`groups_ok`), so the answer rows and the GROUP BY's rows are the same set; the answer rows are distinct
//! (dictionary entries and sizes are distinct) and in ORDER BY order (`output::lemma_row_cmp`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::limits::int8_max;
use crate::query::query_spec_at;
use crate::link::outcome::lemma_outcome_sorted;
use crate::link::query::lemma_nodup_same_multiset;
use crate::gendb_entry::results::*;
use crate::stores::custpart::interface::common::read::text_slice;
use super::tables::*;
use super::model::*;
use super::sqlq::*;
use super::sqlrel::*;
use super::answer::*;
use super::output::*;
use super::round::*;
use super::bind::{keys_unique, fk_supp};
use super::common::distinct::*;

verus! {

/// The distinct sizes of the IN list, increasing.
pub open spec fn sizes_ok(sizes: Seq<i64>, m: Prm) -> bool {
    &&& forall|a: int, b: int| 0 <= a < b < sizes.len() ==> #[trigger] sizes[a] < #[trigger] sizes[b]
    &&& forall|v: int| #[trigger] listed(sizes, v) <==> m.sizes.contains(v)
}

/// The collected groups: in (brand, type, slot) order, each with its count, and every group of positive count.
pub open spec fn groups_ok(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, gs: Seq<Grp>) -> bool {
    &&& lex_sorted(gs)
    &&& forall|k: int| 0 <= k < gs.len() ==> grp_ok(c, t, m, sizes, #[trigger] gs[k])
    &&& forall|b: int, tt: int, z: int| 0 <= b < c.p.brand_o@.len() - 1 && 0 <= tt < c.p.type_o@.len() - 1
        && 0 <= z < sizes.len() && #[trigger] kc(c, t, m, sizes, b, tt, z) > 0
        ==> exists|k: int| 0 <= k < gs.len() && at(#[trigger] gs[k], b, tt, z)
}

/// The answer rows: group `perm[i]` at row `i`.
pub open spec fn out_rows(c: Cols, sizes: Seq<i64>, gs: Seq<Grp>, perm: Seq<usize>) -> Seq<Row> {
    Seq::new(perm.len(), |i: int| orow(c, sizes, gs[perm[i] as int]))
}

// ------------------------------------------------------------------------------------------------ keys and groups

/// The part key of a qualifying pair is the key of a group with a positive count.
proof fn lemma_key_group(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, i: int, j: int)
    requires
        cols_ok(c, t), keys_unique(t), fk_supp(t),
        sizes_ok(sizes, m),
        qual(t, m, i, j),
    ensures
        exists|b: int, tt: int, z: int| 0 <= b < c.p.brand_o@.len() - 1 && 0 <= tt < c.p.type_o@.len() - 1
            && 0 <= z < sizes.len() && key_bt(c, sizes, b, tt, z) == prow_key(t, j)
            && #[trigger] kc(c, t, m, sizes, b, tt, z) > 0,
{
    lemma_tabs_typed(c, t);
    lemma_srow_exists(c, t, i);
    let r = choose|r: int| #[trigger] srow_of(c, i, r);
    lemma_qual_cols(c, t, m, i, j, r);
    assert(part_row_ok(c.p, t.p[j], j));
    let (b, tt, v) = (bidx(c.p, j), tidx(c.p, j), sval(c.p, j));
    assert(m.sizes.contains(v));
    assert(listed(sizes, v));
    let z = choose|z: int| 0 <= z < sizes.len() && sizes[z] == v;
    lemma_prow_key(c, t, j);
    assert(key_bt(c, sizes, b, tt, z) =~= prow_key(t, j));
    lemma_kv_has(t, m, prow_key(t, j), t.ps[i][1]);
    let s = kv(t, m, prow_key(t, j));
    if s.len() == 0 {
        s.lemma_len0_is_empty();
    }
    assert(kc(c, t, m, sizes, b, tt, z) > 0);
}

/// Every key of the kept rows is the key of a collected group, with its count.
proof fn lemma_key_has_group(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, gs: Seq<Grp>, k: Row)
    requires
        cols_ok(c, t), keys_unique(t), fk_supp(t),
        sizes_ok(sizes, m),
        groups_ok(c, t, m, sizes, gs),
        keys_of(kept(t, m)).contains(k),
    ensures
        exists|x: int| 0 <= x < gs.len() && key_bt(c, sizes, gs[x].b as int, gs[x].t as int, gs[x].z as int) == k
            && #[trigger] gs[x].cnt as int == kv(t, m, k).len(),
{
    lemma_tabs_typed(c, t);
    lemma_keys_has(t, m, k);
    let (i, j) = choose|i: int, j: int| #[trigger] qual(t, m, i, j) && prow_key(t, j) == k;
    lemma_key_group(c, t, m, sizes, i, j);
    let (b, tt, z) = choose|b: int, tt: int, z: int| 0 <= b < c.p.brand_o@.len() - 1 && 0 <= tt < c.p.type_o@.len() - 1
        && 0 <= z < sizes.len() && key_bt(c, sizes, b, tt, z) == prow_key(t, j)
        && #[trigger] kc(c, t, m, sizes, b, tt, z) > 0;
    let x = choose|x: int| 0 <= x < gs.len() && at(#[trigger] gs[x], b, tt, z);
    assert(grp_ok(c, t, m, sizes, gs[x]));
}

/// A collected group's key is a key of the kept rows.
proof fn lemma_group_is_key(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, e: Grp)
    requires cols_ok(c, t), grp_ok(c, t, m, sizes, e),
    ensures keys_of(kept(t, m)).contains(key_bt(c, sizes, e.b as int, e.t as int, e.z as int)),
{
    lemma_tabs_typed(c, t);
    let k = key_bt(c, sizes, e.b as int, e.t as int, e.z as int);
    let s = kv(t, m, k);
    assert(s.len() > 0);
    if !(exists|v: Val| s.contains(v)) {
        assert(s =~= Set::empty());
    }
    let v = choose|v: Val| s.contains(v);
    lemma_kv_has(t, m, k, v);
    let (i, j) = choose|i: int, j: int| #[trigger] qual(t, m, i, j) && prow_key(t, j) == k && t.ps[i][1] == v;
    lemma_keys_has(t, m, k);
}

/// The GROUP BY's inputs are plain values.
proof fn lemma_group_inputs(t: Tabs, m: Prm)
    requires tabs_typed(t),
    ensures
        keys_of(kept(t, m)).len() == args_of(kept(t, m)).len(),
        forall|i: int| 0 <= i < keys_of(kept(t, m)).len() ==> plain_row(#[trigger] keys_of(kept(t, m))[i]),
        forall|i: int| 0 <= i < args_of(kept(t, m)).len() ==> (#[trigger] args_of(kept(t, m))[i]).len() == 1
            && plain(args_of(kept(t, m))[i][0]),
{
    lemma_kept_rows(t, m);
    let ks = kept(t, m);
    assert forall|i: int| 0 <= i < keys_of(ks).len() implies plain_row(#[trigger] keys_of(ks)[i]) by {
        assert(xrow_ok(ks[i]));
        assert(keys_of(ks)[i] == key_of(ks[i]));
    }
    assert forall|i: int| 0 <= i < args_of(ks).len() implies (#[trigger] args_of(ks)[i]).len() == 1
        && plain(args_of(ks)[i][0]) by {
        assert(xrow_ok(ks[i]));
        assert(args_of(ks)[i] == arg_of(ks[i]));
    }
}

/// The statement's body is the GROUP BY of the kept rows (with plain inputs).
proof fn lemma_body(db: Database, ps: Seq<Literal>)
    requires
        db.tables.len() == 8,
        tabs_typed(tabs_of(db)),
        params_ok(ps),
        like_all_ok(tabs_of(db), prm_of(ps)) || prod(tabs_of(db)).len() == 0,
    ensures
        query_spec_at(ps).keys == q_keys(),
        query_spec_at(ps).offset == 0,
        query_spec_at(ps).limit is None,
        denote_body(db, query_spec_at(ps)) == group_rows(count_distinct_aggs(Expr::Col(1)),
            keys_of(kept(tabs_of(db), prm_of(ps))), args_of(kept(tabs_of(db), prm_of(ps)))),
        keys_of(kept(tabs_of(db), prm_of(ps))).len() == args_of(kept(tabs_of(db), prm_of(ps))).len(),
        forall|i: int| 0 <= i < keys_of(kept(tabs_of(db), prm_of(ps))).len()
            ==> plain_row(#[trigger] keys_of(kept(tabs_of(db), prm_of(ps)))[i]),
        forall|i: int| 0 <= i < args_of(kept(tabs_of(db), prm_of(ps))).len()
            ==> (#[trigger] args_of(kept(tabs_of(db), prm_of(ps)))[i]).len() == 1
            && plain(args_of(kept(tabs_of(db), prm_of(ps)))[i][0]),
{
    let t = tabs_of(db);
    let m = prm_of(ps);
    lemma_query_shape(ps);
    lemma_eval_filter_ok(db, ps);
    lemma_eval_body(db, ps);
    lemma_group_inputs(t, m);
    assert(q_aggs() == count_distinct_aggs(Expr::Col(1)));
}

// ------------------------------------------------------------------------------------------------ the answers

/// The answer rows have no duplicates.
proof fn lemma_out_nodup(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, gs: Seq<Grp>, perm: Seq<usize>)
    requires
        cols_ok(c, t),
        sizes_ok(sizes, m),
        groups_ok(c, t, m, sizes, gs),
        perm_ok(gs, perm),
    ensures out_rows(c, sizes, gs, perm).no_duplicates(),
{
    let out = out_rows(c, sizes, gs, perm);
    assert forall|p: int, q: int| 0 <= p < out.len() && 0 <= q < out.len() && p != q implies out[p] != out[q] by {
        let (x, y) = (perm[p] as int, perm[q] as int);
        let (e1, e2) = (gs[x], gs[y]);
        assert(grp_ok(c, t, m, sizes, gs[x]) && grp_ok(c, t, m, sizes, gs[y]));
        if out[p] == out[q] {
            assert(out[p][0] == out[q][0] && out[p][1] == out[q][1] && out[p][2] == out[q][2]);
            lemma_dict_inj(c.p.brand_o@, c.p.brand_y@, e1.b as int, e2.b as int);
            lemma_dict_inj(c.p.type_o@, c.p.type_y@, e1.t as int, e2.t as int);
            if e1.z < e2.z {
                assert(sizes[e1.z as int] < sizes[e2.z as int]);
            } else if e1.z > e2.z {
                assert(sizes[e2.z as int] < sizes[e1.z as int]);
            }
            if x < y {
                assert(grp_lt(gs[x], gs[y]));
            } else if y < x {
                assert(grp_lt(gs[y], gs[x]));
            }
            if p < q {
                assert(gs[perm[p] as int].cnt > gs[perm[q] as int].cnt
                    || (gs[perm[p] as int].cnt == gs[perm[q] as int].cnt && perm[p] < perm[q]));
            } else {
                assert(gs[perm[q] as int].cnt > gs[perm[p] as int].cnt
                    || (gs[perm[q] as int].cnt == gs[perm[p] as int].cnt && perm[q] < perm[p]));
            }
        }
    }
}

/// The answer rows are in ORDER BY order.
proof fn lemma_out_sorted(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, gs: Seq<Grp>, perm: Seq<usize>)
    requires
        cols_ok(c, t),
        sizes_ok(sizes, m),
        groups_ok(c, t, m, sizes, gs),
        perm_ok(gs, perm),
    ensures sorted_by(q_keys(), out_rows(c, sizes, gs, perm)),
{
    let out = out_rows(c, sizes, gs, perm);
    assert forall|p: int, q: int| 0 <= p < q < out.len() implies keys_cmp(q_keys(), #[trigger] out[p], #[trigger] out[q]) <= 0 by {
        let (x, y) = (perm[p] as int, perm[q] as int);
        assert(grp_ok(c, t, m, sizes, gs[x]) && grp_ok(c, t, m, sizes, gs[y]));
        assert(gs[perm[p] as int].cnt > gs[perm[q] as int].cnt
            || (gs[perm[p] as int].cnt == gs[perm[q] as int].cnt && perm[p] < perm[q]));
        if gs[x].cnt == gs[y].cnt {
            assert(grp_lt(gs[x], gs[y]));
        }
        lemma_row_cmp(c, sizes, gs[x], gs[y]);
    }
}

/// The groups' preconditions of the final lemmas.
pub open spec fn fin_ok(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, gs: Seq<Grp>) -> bool {
    &&& cols_ok(c, t)
    &&& keys_unique(t)
    &&& fk_supp(t)
    &&& sizes_ok(sizes, m)
    &&& groups_ok(c, t, m, sizes, gs)
    &&& gs.len() <= usize::MAX
}

/// Every key's count is an int8.
proof fn lemma_counts_int8(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, gs: Seq<Grp>)
    requires fin_ok(c, t, m, sizes, gs),
    ensures
        forall|i: int| 0 <= i < keys_of(kept(t, m)).len() ==> #[trigger] key_vals(keys_of(kept(t, m)),
            args_of(kept(t, m)), keys_of(kept(t, m))[i]).len() <= int8_max(),
{
    let ks = kept(t, m);
    let (keys, args) = (keys_of(ks), args_of(ks));
    assert forall|i: int| 0 <= i < keys.len() implies #[trigger] key_vals(keys, args, keys[i]).len() <= int8_max() by {
        assert(keys.contains(keys[i]));
        lemma_key_has_group(c, t, m, sizes, gs, keys[i]);
        let x = choose|x: int| 0 <= x < gs.len() && key_bt(c, sizes, gs[x].b as int, gs[x].t as int, gs[x].z as int) == keys[i]
            && #[trigger] gs[x].cnt as int == kv(t, m, keys[i]).len();
        assert(grp_ok(c, t, m, sizes, gs[x]));
    }
}

/// An answer row is a GROUP BY row.
proof fn lemma_out_to_rows(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, gs: Seq<Grp>, perm: Seq<usize>, p: int)
    requires fin_ok(c, t, m, sizes, gs), perm_ok(gs, perm), 0 <= p < perm.len(),
    ensures
        exists|i: int| 0 <= i < keys_of(kept(t, m)).len() && out_rows(c, sizes, gs, perm)[p]
            == group_out(keys_of(kept(t, m)), args_of(kept(t, m)), #[trigger] keys_of(kept(t, m))[i]),
{
    let ks = kept(t, m);
    let (keys, args) = (keys_of(ks), args_of(ks));
    let e = gs[perm[p] as int];
    assert(grp_ok(c, t, m, sizes, e));
    let k = key_bt(c, sizes, e.b as int, e.t as int, e.z as int);
    lemma_group_is_key(c, t, m, sizes, e);
    let i = choose|i: int| 0 <= i < keys.len() && keys[i] == k;
    assert(out_rows(c, sizes, gs, perm)[p] == group_out(keys, args, keys[i]));
}

/// A GROUP BY row is an answer row.
proof fn lemma_rows_to_out(c: Cols, t: Tabs, m: Prm, sizes: Seq<i64>, gs: Seq<Grp>, perm: Seq<usize>, i: int)
    requires fin_ok(c, t, m, sizes, gs), perm_ok(gs, perm), 0 <= i < keys_of(kept(t, m)).len(),
    ensures
        exists|p: int| 0 <= p < perm.len() && #[trigger] out_rows(c, sizes, gs, perm)[p]
            == group_out(keys_of(kept(t, m)), args_of(kept(t, m)), keys_of(kept(t, m))[i]),
{
    let ks = kept(t, m);
    let (keys, args) = (keys_of(ks), args_of(ks));
    assert(keys.contains(keys[i]));
    lemma_key_has_group(c, t, m, sizes, gs, keys[i]);
    let y = choose|y: int| 0 <= y < gs.len() && key_bt(c, sizes, gs[y].b as int, gs[y].t as int, gs[y].z as int) == keys[i]
        && #[trigger] gs[y].cnt as int == kv(t, m, keys[i]).len();
    assert(perm.contains(y as usize));
    let p = choose|p: int| 0 <= p < perm.len() && perm[p] == y as usize;
    assert(perm[p] as int == y);
    assert(out_rows(c, sizes, gs, perm)[p] == group_out(keys, args, keys[i]));
}

/// The ordered collected groups are an allowed output.
pub proof fn lemma_final(db: Database, ps: Seq<Literal>, c: Cols, sizes: Seq<i64>, gs: Seq<Grp>, perm: Seq<usize>)
    requires
        db.tables.len() == 8,
        params_ok(ps),
        like_all_ok(tabs_of(db), prm_of(ps)) || prod(tabs_of(db)).len() == 0,
        fin_ok(c, tabs_of(db), prm_of(ps), sizes, gs),
        perm_ok(gs, perm),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out_rows(c, sizes, gs, perm))),
{
    let t = tabs_of(db);
    let m = prm_of(ps);
    lemma_tabs_typed(c, t);
    let ks = kept(t, m);
    let (keys, args) = (keys_of(ks), args_of(ks));
    lemma_body(db, ps);
    lemma_counts_int8(c, t, m, sizes, gs);
    lemma_group_count_distinct(Expr::Col(1), keys, args);
    let rows = denote_body(db, query_spec_at(ps))->Ok_0;
    let out = out_rows(c, sizes, gs, perm);
    assert forall|x: Row| out.contains(x) <==> rows.contains(x) by {
        if out.contains(x) {
            let p = choose|p: int| 0 <= p < out.len() && out[p] == x;
            lemma_out_to_rows(c, t, m, sizes, gs, perm, p);
        }
        if rows.contains(x) {
            let i = choose|i: int| 0 <= i < keys.len() && x == group_out(keys, args, #[trigger] keys[i]);
            lemma_rows_to_out(c, t, m, sizes, gs, perm, i);
        }
    }
    lemma_out_nodup(c, t, m, sizes, gs, perm);
    lemma_out_sorted(c, t, m, sizes, gs, perm);
    lemma_nodup_same_multiset(out, rows);
    lemma_outcome_sorted(db, query_spec_at(ps), rows, out);
    assert(slice_rows(out, 0, None) =~= out);
}

/// A count beyond int8 is the statement's error.
pub proof fn lemma_overflow(db: Database, ps: Seq<Literal>, c: Cols, sizes: Seq<i64>, b: int, tt: int, z: int)
    requires
        db.tables.len() == 8,
        cols_ok(c, tabs_of(db)),
        params_ok(ps),
        like_all_ok(tabs_of(db), prm_of(ps)) || prod(tabs_of(db)).len() == 0,
        kc(c, tabs_of(db), prm_of(ps), sizes, b, tt, z) > i64::MAX,
    ensures ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)),
{
    let t = tabs_of(db);
    let m = prm_of(ps);
    lemma_tabs_typed(c, t);
    let k = key_bt(c, sizes, b, tt, z);
    let s = kv(t, m, k);
    if !(exists|v: Val| s.contains(v)) {
        assert(s =~= Set::empty());
    }
    let v = choose|v: Val| s.contains(v);
    lemma_kv_has(t, m, k, v);
    lemma_keys_has(t, m, k);
    let ks = kept(t, m);
    let i = choose|i: int| 0 <= i < keys_of(ks).len() && keys_of(ks)[i] == k;
    lemma_body(db, ps);
    assert(key_vals(keys_of(ks), args_of(ks), keys_of(ks)[i]).len() > int8_max());
    lemma_group_count_distinct(Expr::Col(1), keys_of(ks), args_of(ks));
}

/// The first failing LIKE is the statement's error.
pub proof fn lemma_like_err(db: Database, ps: Seq<Literal>, i: int, err: SqlError)
    requires
        db.tables.len() == 8,
        tabs_typed(tabs_of(db)),
        params_ok(ps),
        0 <= i < tabs_of(db).p.len(),
        like_res(tabs_of(db).p[i][4], prm_of(ps).pat) == Err::<Val, SqlError>(err),
        forall|i2: int| 0 <= i2 < i ==> #[trigger] like_res(tabs_of(db).p[i2][4], prm_of(ps).pat) is Ok,
        tabs_of(db).ps.len() > 0,
    ensures ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(err)),
{
    lemma_eval_filter_err(db, ps, i, err);
    lemma_query_shape(ps);
}

// ------------------------------------------------------------------------------------------------ columns

/// A text column of dictionary entries `ids` (copied bytes).
pub fn text_col(o: &[u64], y: &[u8], ids: &Vec<usize>) -> (r: ResultColumn)
    requires
        dict_ok(o@, y@),
        forall|i: int| 0 <= i < ids@.len() ==> #[trigger] ids@[i] < o@.len() - 1,
    ensures
        column_wf(r, ids@.len() as nat),
        forall|i: int| 0 <= i < ids@.len() ==> #[trigger] column_value(r, i) == Val::Text(txt(o@, y@, ids@[i] as int)),
{
    let n = ids.len();
    let mut offs: Vec<usize> = Vec::new();
    let mut bytes: Vec<u8> = Vec::new();
    offs.push(0);
    let mut i: usize = 0;
    while i < n
        invariant
            dict_ok(o@, y@), n == ids@.len(), i <= n,
            forall|k: int| 0 <= k < ids@.len() ==> #[trigger] ids@[k] < o@.len() - 1,
            offs@.len() == i + 1,
            offs@[i as int] == bytes@.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] offs@[k] <= offs@[k + 1] && offs@[k + 1] <= bytes@.len()
                && bytes@.subrange(offs@[k] as int, offs@[k + 1] as int) == txt(o@, y@, ids@[k] as int),
        decreases n - i,
    {
        let id = ids[i];
        assert(o@[id as int] <= o@[id + 1] && o@[id + 1] <= y@.len());
        let s = text_slice(o, y, id);
        let ghost b0 = bytes@;
        let ghost o0 = offs@;
        bytes.extend_from_slice(s);
        proof {
            assert(bytes@ =~= b0 + s@);
        }
        let len = bytes.len();
        offs.push(len);
        proof {
            assert forall|k: int| 0 <= k < i + 1 implies #[trigger] offs@[k] <= offs@[k + 1] && offs@[k + 1] <= bytes@.len()
                && bytes@.subrange(offs@[k] as int, offs@[k + 1] as int) == txt(o@, y@, ids@[k] as int) by {
                if k < i {
                    assert(offs@[k] == o0[k] && offs@[k + 1] == o0[k + 1]);
                    assert(bytes@.subrange(offs@[k] as int, offs@[k + 1] as int) =~= b0.subrange(o0[k] as int, o0[k + 1] as int));
                } else {
                    assert(offs@[k] == b0.len());
                    assert(bytes@.subrange(offs@[k] as int, offs@[k + 1] as int) =~= s@);
                }
            }
        }
        i = i + 1;
    }
    ResultColumn::Text { offsets: offs, bytes }
}

/// The columns of the ordered groups: p_brand, p_type, p_size, supplier_cnt.
pub fn answer_columns(c: &Cols, sizes: &Vec<i64>, gs: &Vec<Grp>, perm: &Vec<usize>) -> (r: ResultColumns)
    requires
        dict_ok(c.p.brand_o@, c.p.brand_y@), dict_ok(c.p.type_o@, c.p.type_y@),
        forall|p: int| 0 <= p < perm@.len() ==> #[trigger] perm@[p] < gs@.len(),
        forall|k: int| 0 <= k < gs@.len() ==> (#[trigger] gs@[k]).b < c.p.brand_o@.len() - 1
            && gs@[k].t < c.p.type_o@.len() - 1 && gs@[k].z < sizes@.len() && gs@[k].cnt <= i64::MAX,
    ensures
        columns_wf(r),
        columns_view(r) == out_rows(*c, sizes@, gs@, perm@),
{
    let n = perm.len();
    let mut bids: Vec<usize> = Vec::new();
    let mut tids: Vec<usize> = Vec::new();
    let mut szs: Vec<i64> = Vec::new();
    let mut cns: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == perm@.len(), i <= n,
            forall|p: int| 0 <= p < perm@.len() ==> #[trigger] perm@[p] < gs@.len(),
            forall|k: int| 0 <= k < gs@.len() ==> (#[trigger] gs@[k]).b < c.p.brand_o@.len() - 1
                && gs@[k].t < c.p.type_o@.len() - 1 && gs@[k].z < sizes@.len() && gs@[k].cnt <= i64::MAX,
            bids@.len() == i, tids@.len() == i, szs@.len() == i, cns@.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] bids@[k] == gs@[perm@[k] as int].b,
            forall|k: int| 0 <= k < i ==> #[trigger] tids@[k] == gs@[perm@[k] as int].t,
            forall|k: int| 0 <= k < i ==> #[trigger] szs@[k] == sizes@[gs@[perm@[k] as int].z as int],
            forall|k: int| 0 <= k < i ==> #[trigger] cns@[k] as int == gs@[perm@[k] as int].cnt as int,
        decreases n - i,
    {
        let e = gs[perm[i]];
        bids.push(e.b);
        tids.push(e.t);
        szs.push(sizes[e.z]);
        cns.push(e.cnt as i64);
        i = i + 1;
    }
    let bcol = text_col(c.p.brand_o, c.p.brand_y, &bids);
    let tcol = text_col(c.p.type_o, c.p.type_y, &tids);
    let mut cols: Vec<ResultColumn> = Vec::new();
    cols.push(bcol);
    cols.push(tcol);
    cols.push(ResultColumn::Int(szs));
    cols.push(ResultColumn::Int(cns));
    let r = ResultColumns { rows: n, columns: cols };
    proof {
        let out = out_rows(*c, sizes@, gs@, perm@);
        assert forall|k: int| 0 <= k < r.columns@.len() implies column_wf(#[trigger] r.columns@[k], r.rows as nat) by {}
        assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i].len() == r.columns@.len() by {}
        assert forall|i: int, k: int| 0 <= i < out.len() && 0 <= k < r.columns@.len()
            implies #[trigger] out[i][k] == column_value(r.columns@[k], i) by {
            let e = gs@[perm@[i] as int];
            assert(out[i] == orow(*c, sizes@, e));
            assert(bids@[i] == e.b);
            assert(tids@[i] == e.t);
            assert(szs@[i] == sizes@[e.z as int]);
            assert(cns@[i] as int == e.cnt as int);
        }
        lemma_columns_view_eq(r, out);
    }
    r
}

} // verus!
