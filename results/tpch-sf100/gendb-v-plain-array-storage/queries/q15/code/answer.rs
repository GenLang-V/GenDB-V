//! From the picked supplier rows to the fixed claim.
//!
//! Supplier row `i` contributes an output row exactly when its key is a group key whose SUM is the largest one `m`
//! (`pick_of`); the group keys are distinct, so it contributes at most one row, `out_row_of(S[i], m)`
//! (`lemma_row_part`). Hence the body's rows are the output rows of the picked supplier rows in row order
//! (`lemma_body_picks`). `emit_rows` builds them from the stored text columns, `finish` sorts them by `s_suppkey`
//! (`sort_rows_exec`), which is the canonical sorted output `denote_top` of every bound database
//! (`lemma_rows_all`, through `bridge::order::lemma_denote_top_ok`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::relation::product_rows;
use crate::spec::order::*;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::query::{param_domain, query_spec_at, lemma_query_wf_at};
use crate::exec::value::{EVal, ERow, view_row};
use crate::exec::ast::{EOrderKey, view_order_keys};
use crate::exec::relational::order::sort_rows_exec;
use crate::bridge::order::lemma_denote_top_ok;
use crate::link::query::*;
use crate::link::join::{keep, lemma_keep_push, lemma_keep_none, lemma_keep_append};
use crate::link::outcome::{lemma_view_rows, lemma_view_rows_push};
use crate::stores::flat_supplier::interface as si;
use crate::agent::common::selection::range_filter;
use crate::agent::normal::*;
use crate::agent::cols::*;
use crate::agent::groups::*;
use crate::agent::body::*;

verus! {

/// Supplier row `i` is picked: its key is a group key whose SUM is `m`.
pub open spec fn pick_of(g: QuerySpec, xs: Seq<Row>, srows: Seq<Row>, m: int) -> spec_fn(int) -> bool {
    |i: int| gkeys(g, xs).contains(seq![srows[i][0]]) && gsum(g, xs, seq![srows[i][0]], 0) == m
}

/// The output row of supplier row `s` with the SUM `m`: `s_suppkey, s_name, s_address, s_phone, total_revenue`.
pub open spec fn out_row_of(s: Row, m: int) -> Row {
    seq![s[0], s[1], s[2], s[4], Val::Num { coeff: m, scale: 4 }]
}

/// The output rows of the supplier rows listed in `idxs`.
pub open spec fn picked_rows(srows: Seq<Row>, idxs: Seq<int>, m: int) -> Seq<Row> {
    idxs.map_values(|i: int| out_row_of(srows[i], m))
}

/// One more left row of a product: its pairs with every right row come last.
pub proof fn lemma_product_push(a: Seq<Row>, x: Row, b: Seq<Row>)
    ensures product_rows(a.push(x), b) == product_rows(a, b) + b.map_values(|r: Row| x + r),
{
    assert(a.push(x).drop_last() =~= a);
}

/// A condition that holds on exactly one row `t[j]` keeps that row.
pub proof fn lemma_keep_single(t: Seq<Row>, f: spec_fn(Row) -> bool, j: int)
    requires
        0 <= j < t.len(),
        f(t[j]),
        forall|i: int| 0 <= i < t.len() && i != j ==> !f(#[trigger] t[i]),
    ensures keep(t, f) == seq![t[j]],
    decreases t.len(),
{
    let d = t.drop_last();
    assert(t == d.push(t.last()));
    lemma_keep_push(d, t.last(), f);
    if j == t.len() - 1 {
        assert forall|i: int| 0 <= i < d.len() implies !f(#[trigger] d[i]) by {
            assert(d[i] == t[i]);
        }
        lemma_keep_none(d, f);
        assert(Seq::<Row>::empty().push(t[j]) =~= seq![t[j]]);
    } else {
        assert forall|i: int| 0 <= i < d.len() && i != j implies !f(#[trigger] d[i]) by {
            assert(d[i] == t[i]);
        }
        assert(d[j] == t[j]);
        lemma_keep_single(d, f, j);
        assert(!f(t[t.len() - 1]));
    }
}

/// The body's rows of one supplier row `S[i]`: its output row when picked, none otherwise.
pub proof fn lemma_row_part(lrows: Seq<Row>, b: QBounds, srows: Seq<Row>, m: int, i: int)
    requires li_rows_ok(lrows), supp_rows_ok(srows), 0 <= i < srows.len(),
    ensures ({
        let g = q_spec(b);
        let xs = xs_of(lrows);
        keep(grp_rows(g, xs).map_values(|r: Row| srows[i] + r), cond_of(m)).map_values(|pr: Row| select(pr, out_cols()))
            == if pick_of(g, xs, srows, m)(i) { seq![out_row_of(srows[i], m)] } else { Seq::<Row>::empty() }
    }),
{
    let g = q_spec(b);
    let xs = xs_of(lrows);
    let s = srows[i];
    let gk = gkeys(g, xs);
    let rr = grp_rows(g, xs);
    let t = rr.map_values(|r: Row| s + r);
    let f = cond_of(m);
    let key = seq![s[0]];
    lemma_gkeys(g, xs);
    // `t[j]` passes exactly when group `j` is the key `[s_suppkey]` with SUM `m`
    assert forall|j: int| 0 <= j < t.len() implies #[trigger] f(t[j]) == (gk[j] == key && gsum(g, xs, gk[j], 0) == m) by {
        lemma_grp_row(lrows, b, j);
        assert(gk.contains(gk[j]));
        lemma_gkey_shape(lrows, b, gk[j]);
        assert(t[j] == s + rr[j]);
        assert(t[j][0] == s[0] && t[j][7] == rr[j][0] && t[j][8] == rr[j][1]);
        if gk[j][0] == s[0] {
            assert(gk[j] =~= key);
        }
    }
    if pick_of(g, xs, srows, m)(i) {
        let j = choose|j: int| 0 <= j < gk.len() && gk[j] == key;
        assert forall|i2: int| 0 <= i2 < t.len() && i2 != j implies !f(#[trigger] t[i2]) by {
            assert(gk[i2] != gk[j]);
        }
        lemma_keep_single(t, f, j);
        lemma_grp_row(lrows, b, j);
        assert(select(t[j], out_cols()) =~= out_row_of(s, m));
        assert(seq![t[j]].map_values(|pr: Row| select(pr, out_cols())) =~= seq![out_row_of(s, m)]);
    } else {
        assert forall|j: int| 0 <= j < t.len() implies !f(#[trigger] t[j]) by {
            if f(t[j]) {
                assert(gk.contains(gk[j]));
            }
        }
        lemma_keep_none(t, f);
        assert(Seq::<Row>::empty().map_values(|pr: Row| select(pr, out_cols())) =~= Seq::<Row>::empty());
    }
}

/// The body's rows over the first `hi` supplier rows are the output rows of the picked ones among them.
pub proof fn lemma_body_picks(lrows: Seq<Row>, b: QBounds, srows: Seq<Row>, m: int, hi: int)
    requires li_rows_ok(lrows), supp_rows_ok(srows), 0 <= hi <= srows.len(),
    ensures ({
        let g = q_spec(b);
        let xs = xs_of(lrows);
        body_rows(srows.take(hi), grp_rows(g, xs), m) == picked_rows(srows, range_filter(0, hi, pick_of(g, xs, srows, m)), m)
    }),
    decreases hi,
{
    let g = q_spec(b);
    let xs = xs_of(lrows);
    let rr = grp_rows(g, xs);
    let f = cond_of(m);
    let p = pick_of(g, xs, srows, m);
    if hi == 0 {
        assert(srows.take(0) =~= Seq::<Row>::empty());
        assert(product_rows(Seq::<Row>::empty(), rr) == Seq::<Row>::empty());
        assert(keep(Seq::<Row>::empty(), f) == Seq::<Row>::empty());
        assert(body_rows(srows.take(0), rr, m) =~= Seq::<Row>::empty());
        assert(picked_rows(srows, range_filter(0, 0, p), m) =~= Seq::<Row>::empty());
    } else {
        lemma_body_picks(lrows, b, srows, m, hi - 1);
        let a = srows.take(hi - 1);
        let s = srows[hi - 1];
        assert(srows.take(hi) =~= a.push(s));
        lemma_product_push(a, s, rr);
        let part = rr.map_values(|r: Row| s + r);
        lemma_keep_append(product_rows(a, rr), part, f);
        let sel = |pr: Row| select(pr, out_cols());
        assert((keep(product_rows(a, rr), f) + keep(part, f)).map_values(sel)
            =~= keep(product_rows(a, rr), f).map_values(sel) + keep(part, f).map_values(sel));
        lemma_row_part(lrows, b, srows, m, hi - 1);
        let r0 = range_filter(0, hi - 1, p);
        if p(hi - 1) {
            assert(range_filter(0, hi, p) == r0.push(hi - 1));
            assert(picked_rows(srows, r0.push(hi - 1), m) =~= picked_rows(srows, r0, m) + seq![out_row_of(s, m)]);
        } else {
            assert(range_filter(0, hi, p) == r0);
            assert(picked_rows(srows, r0, m) + Seq::<Row>::empty() =~= picked_rows(srows, r0, m));
        }
    }
}

/// A copy of the bytes of a text value.
pub fn to_vec(s: &[u8]) -> (v: Vec<u8>)
    ensures v@ == s@,
{
    let n = s.len();
    let mut v: Vec<u8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant n == s@.len(), i <= n, v@ == s@.subrange(0, i as int),
        decreases n - i,
    {
        v.push(s[i]);
        i = i + 1;
        assert(v@ =~= s@.subrange(0, i as int));
    }
    assert(s@.subrange(0, n as int) =~= s@);
    v
}

/// The output row of supplier row `i` with the SUM `m`, from the stored columns.
pub fn out_row(stores: &mut Stores, k: &SuppKeys, i: usize, m: i128, Ghost(srels): Ghost<Seq<Seq<Row>>>) -> (row: Vec<EVal>)
    requires si::represents(old(stores)@.flat_supplier, srels), keys_match(*k, srels[0]), i < k.ns,
    ensures final(stores)@ == old(stores)@, view_row(row@) == out_row_of(srels[0][i as int], m as int),
{
    let name = si::read_s_name_at(&mut stores.flat_supplier, i, Ghost(srels));
    let addr = si::read_s_address_at(&mut stores.flat_supplier, i, Ghost(srels));
    let phone = si::read_s_phone_at(&mut stores.flat_supplier, i, Ghost(srels));
    let mut row: Vec<EVal> = Vec::new();
    row.push(EVal::Int(k.keys[i]));
    row.push(EVal::Text(to_vec(name)));
    row.push(EVal::Text(to_vec(addr)));
    row.push(EVal::Text(to_vec(phone)));
    row.push(EVal::Num { coeff: m, scale: 4 });
    proof {
        assert(view_row(row@) =~= out_row_of(srels[0][i as int], m as int));
    }
    row
}

/// `idxs` lists the row positions `sel`, each below `ns`.
pub open spec fn idxs_ok(idxs: Seq<usize>, sel: Seq<int>, ns: usize) -> bool {
    &&& idxs.len() == sel.len()
    &&& forall|t: int| 0 <= t < sel.len() ==> (#[trigger] idxs[t]) as int == sel[t] && sel[t] < ns
}

/// The output rows of the supplier rows listed in `idxs` (row positions `sel`).
pub fn emit_rows(stores: &mut Stores, k: &SuppKeys, idxs: &Vec<usize>, m: i128, Ghost(srels): Ghost<Seq<Seq<Row>>>,
    Ghost(sel): Ghost<Seq<int>>) -> (rows: Vec<ERow>)
    requires
        si::represents(old(stores)@.flat_supplier, srels),
        keys_match(*k, srels[0]),
        idxs_ok(idxs@, sel, k.ns),
    ensures
        final(stores)@ == old(stores)@,
        view_rows(rows@) == picked_rows(srels[0], sel, m as int),
{
    let mut rows: Vec<ERow> = Vec::new();
    let mut t: usize = 0;
    let ghost s0 = stores@;
    proof {
        lemma_view_rows(rows@);
        assert(sel.take(0) =~= Seq::<int>::empty());
        assert(picked_rows(srels[0], sel.take(0), m as int) =~= Seq::<Row>::empty());
    }
    while t < idxs.len()
        invariant
            t <= idxs@.len(),
            idxs@.len() == sel.len(),
            idxs_ok(idxs@, sel, k.ns),
            si::represents(stores@.flat_supplier, srels),
            stores@ == s0,
            s0 == old(stores)@,
            keys_match(*k, srels[0]),
            view_rows(rows@) == picked_rows(srels[0], sel.take(t as int), m as int),
        decreases idxs@.len() - t,
    {
        let i = idxs[t];
        let row = out_row(stores, k, i, m, Ghost(srels));
        proof {
            lemma_view_rows_push(rows@, row);
            assert(sel.take(t + 1) =~= sel.take(t as int).push(sel[t as int]));
            assert(picked_rows(srels[0], sel.take(t + 1), m as int)
                =~= picked_rows(srels[0], sel.take(t as int), m as int).push(out_row_of(srels[0][i as int], m as int)));
        }
        rows.push(row);
        t = t + 1;
    }
    proof {
        assert(sel.take(sel.len() as int) =~= sel);
    }
    rows
}

/// `ORDER BY s_suppkey` as executable keys.
pub fn order_keys() -> (keys: Vec<EOrderKey>)
    ensures view_order_keys(keys@) == ast_order_keys(),
{
    let mut keys: Vec<EOrderKey> = Vec::new();
    keys.push(EOrderKey { col: 0, desc: false, nulls_first: false });
    proof {
        assert(view_order_keys(keys@) =~= ast_order_keys());
    }
    keys
}

/// The rows of the picked supplier rows, sorted by `s_suppkey`, are an allowed output of every bound database.
pub proof fn lemma_rows_all(sv: StoresView, c: Cols, k: SuppKeys, lrels: Seq<Seq<Row>>, srels: Seq<Seq<Row>>, ps: Seq<Literal>,
    b: QBounds, t1: int, sel: Seq<int>)
    requires
        read_facts(sv, c, k, lrels, srels, ps),
        bounds_ok(ps, b, t1),
        group_caps(q_spec(b), crows(c)),
        sel == range_filter(0, k.ns as int, pick_of(q_spec(b), crows(c), srels[0], max_sum(q_spec(b), crows(c)))),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(
            sort_rows(ast_order_keys(), picked_rows(srels[0], sel, max_sum(q_spec(b), crows(c)))))),
{
    let g = q_spec(b);
    let m = max_sum(g, crows(c));
    let srows = srels[0];
    let out = picked_rows(srows, sel, m);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(
        sort_rows(ast_order_keys(), out))) by {
        lemma_bound(sv, db, c, k, lrels, srels, ps);
        let lrows = db.tables[0];
        assert(supp_rows_ok(srows)) by {
            assert forall|j: int| 0 <= j < srows.len() implies (#[trigger] srows[j]).len() == 7 && srows[j][0] is Int by {
                assert(keys_match(k, srows));
            }
        }
        assert(db_hyps(db, lrows, srows));
        assert(xs_of(lrows) == crows(c));
        lemma_body_ok(db, lrows, srows, ps, b, t1);
        lemma_body_picks(lrows, b, srows, m, srows.len() as int);
        assert(srows.take(srows.len() as int) =~= srows);
        lemma_query_shape(ps);
        lemma_query_wf_at(ps);
        lemma_denote_top_ok(db, query_spec_at(ps));
        let s = sort_rows(ast_order_keys(), out);
        assert(slice_rows(s, 0, None) =~= s);
    }
}

} // verus!
