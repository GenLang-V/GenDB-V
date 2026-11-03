//! The final claim for the produced rows: every database bound to the parts is `db_ok` for the call's context
//! (`lemma_bound`), and the first 100 sorted answer rows at a threshold `t2` (with at least 100 rows, or `t2` the
//! smallest coefficient) are an allowed output of the statement (`lemma_answer`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::int::*;
use crate::spec::order::*;
use crate::spec::equality::*;
use crate::spec::constraints::*;
use crate::spec::types::Constraint;
use crate::bridge::order::*;
use crate::bridge::equality::lemma_row_not_distinct_refl;
use crate::link::query::{proj, proj_all};
use crate::link::source::lemma_proj_all_index;
use crate::link::outcome::lemma_outcome_sorted;
use crate::gendb_entry::stores::StoresView;
use crate::stores::flat_num::interface as ni;
use crate::stores::flat_sub::interface as si;
use crate::agent::spec::*;
use crate::agent::sem::*;
use crate::agent::order::*;

verus! {

/// Every database bound to the parts of `c` is `db_ok` for `c`.
pub proof fn lemma_bound(sv: StoresView, db: Database, c: Ctx)
    requires
        crate::gendb_entry::bound_db(sv, db),
        ctx_ok(c),
        c.np == sv.flat_num,
        c.sp == sv.flat_sub,
    ensures db_ok(db, c),
{
    reveal(ctx_ok);
    reveal(nrow);
    reveal(srow);
    let nrels = crate::stores::flat_num::declaration::stored_relations(db);
    let srels = crate::stores::flat_sub::declaration::stored_relations(db);
    crate::stores::flat_num::declaration::lemma_declared_schema();
    crate::stores::flat_sub::declaration::lemma_declared_schema();
    let nn = db.tables[1];
    let ss = db.tables[0];
    let ncols = crate::stores::flat_num::declaration::stored_cols_t0();
    let scols = crate::stores::flat_sub::declaration::stored_cols_t0();
    lemma_proj_all_index(nn, ncols);
    lemma_proj_all_index(ss, scols);
    // Row counts: the parts determine them.
    assert(ni::text_view(c.np, ni::ADSH_OFFSETS as int, ni::ADSH_BYTES as int).offsets.len() == nrels[0].len() + 1);
    assert(ni::text_view(c.np, ni::ADSH_OFFSETS as int, ni::ADSH_BYTES as int).offsets.len() == c.n + 1);
    assert(si::text_view(c.sp, si::ADSH_OFFSETS as int, si::ADSH_BYTES as int).offsets.len() == srels[0].len() + 1);
    assert(si::text_view(c.sp, si::ADSH_OFFSETS as int, si::ADSH_BYTES as int).offsets.len() == c.m + 1);
    assert forall|i: int| 0 <= i < c.n implies #[trigger] db.tables[1][i] == nrow(c, i) by {
        assert(crate::spec::typing::row_in_table(nn[i], db.schema[1]));
        assert(nn[i].len() == 9);
        assert(nrels[0][i] == ni::row_at(c.np, i));
        assert(proj(nn[i], ncols) =~= nn[i]);
    }
    assert forall|s: int| 0 <= s < c.m implies #[trigger] db.tables[0][s] == srow(c, s) by {
        assert(crate::spec::typing::row_in_table(ss[s], db.schema[0]));
        assert(ss[s].len() == 20);
        assert(srels[0][s] == si::row_at(c.sp, s));
        assert(proj(ss[s], scols) =~= ss[s]);
    }
    // The primary key of sub.
    let ddb = crate::gendb_constraints::declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    assert(ddb.schema[0].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert forall|s1: int, s2: int| 0 <= s1 < c.m && 0 <= s2 < c.m && #[trigger] sadsh_text(c, s1) == #[trigger] sadsh_text(c, s2)
        implies s1 == s2 by {
        assert(ss[s1] == srow(c, s1));
        assert(ss[s2] == srow(c, s2));
        crate::agent::sem::lemma_row_cells(c, 0, s1);
        crate::agent::sem::lemma_row_cells(c, 0, s2);
        assert(ddb.tables[0][s1][0] == ddb.tables[0][s2][0]);
        let k1 = key_of(ddb.tables[0][s1], seq![0nat]);
        let k2 = key_of(ddb.tables[0][s2], seq![0nat]);
        assert(k1 =~= k2);
        lemma_row_not_distinct_refl(k1);
        crate::bridge::constraints::lemma_primary_key_identifies(ddb, 0, 0, seq![0nat], true, s1, s2);
    }
}

/// The literals of a binding in the domain.
pub proof fn lemma_lits(ps: Seq<Literal>, pv: Seq<u8>, fy: int)
    requires
        crate::query::param_domain(ps),
        ps == seq![Literal::Text(pv), (Literal::Int { v: fy, kind: IntKind::Int4 })],
    ensures
        int_in_range(IntKind::Int4, fy),
{
    assert(ps[1] == Literal::Int { v: fy, kind: IntKind::Int4 });
}

/// The answer rows of rows `0..k` are the mapped `body_ok` candidates at the smallest threshold.
pub proof fn lemma_norm_cands(c: Ctx, k: int)
    requires 0 <= k <= c.n, ctx_ok(c),
    ensures norm(c, k) == cands(c, 0, k, i128::MIN as int).filter(body_p(c)).map_values(out_p(c)),
    decreases k,
{
    let fb = body_p(c);
    let o = out_p(c);
    if k == 0 {
        reveal(Seq::filter);
        assert(cands(c, 0, 0, i128::MIN as int).filter(fb).map_values(o) =~= Seq::<Row>::empty());
    } else {
        lemma_norm_cands(c, k - 1);
        lemma_cands_step(c, 0, k - 1, i128::MIN as int);
        lemma_num_text_wf(c);
        let p = cands(c, 0, k - 1, i128::MIN as int);
        assert(coeff(c, k - 1) >= i128::MIN as int);
        if uom_text(c, k - 1) == c.pv {
            lemma_filter_push(p, k - 1, fb);
            if body_ok(c, k - 1) {
                assert(p.filter(fb).push(k - 1).map_values(o) =~= p.filter(fb).map_values(o) + seq![out_row(c, k - 1)]);
            } else {
                assert(p.filter(fb).map_values(o) =~= p.filter(fb).map_values(o) + Seq::<Row>::empty());
            }
        } else {
            assert(!body_ok(c, k - 1));
            assert(p.filter(fb).map_values(o) =~= p.filter(fb).map_values(o) + Seq::<Row>::empty());
        }
    }
}

/// A filter that rejects every element is empty.
pub proof fn lemma_filter_none(s: Seq<int>, f: spec_fn(int) -> bool)
    requires forall|k: int| 0 <= k < s.len() ==> !f(#[trigger] s[k]),
    ensures s.filter(f) == Seq::<int>::empty(),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert(d.push(s.last()) =~= s);
        assert forall|k: int| 0 <= k < d.len() implies !f(#[trigger] d[k]) by {
            assert(d[k] == s[k]);
        }
        lemma_filter_none(d, f);
        lemma_filter_push(d, s.last(), f);
        assert(!f(s[s.len() - 1]));
    } else {
        reveal(Seq::filter);
    }
}

/// The produced answer rows are the answer rows (`out_row`) of the `body_ok` candidates at `t2`.
pub proof fn lemma_ans_rows_eq(c: Ctx, rows: Seq<usize>, subs: Seq<usize>, coeffs: Seq<i128>, b: Seq<int>)
    requires entries(c, rows, subs, coeffs, b), sub_key(c),
    ensures ans_rows(c, rows, subs, coeffs) == b.map_values(out_p(c)),
{
    assert forall|k: int| 0 <= k < b.len() implies #[trigger] ans_rows(c, rows, subs, coeffs)[k] == out_row(c, b[k]) by {
        let i = b[k];
        assert(sub_match(c, i, subs[k] as int));
        assert(has_sub(c, i));
        assert(sub_match(c, i, sub_of(c, i)));
        assert(sadsh_text(c, subs[k] as int) == sadsh_text(c, sub_of(c, i)));
        assert(subs[k] as int == sub_of(c, i));
        lemma_ans_row(c, rows[k] as int, subs[k] as int, coeffs[k] as int);
    }
    assert(ans_rows(c, rows, subs, coeffs) =~= b.map_values(out_p(c)));
}

/// Every row of a mapped candidate list satisfies the key families, and comes from an element of the list.
pub proof fn lemma_mapped_keys_ok(c: Ctx, s: Seq<int>)
    ensures
        all_keys_ok(order_keys(), ans_fams(), s.map_values(out_p(c))),
{
    let v = s.map_values(out_p(c));
    assert forall|k: int| 0 <= k < v.len() implies keys_ok(order_keys(), ans_fams(), #[trigger] v[k]) by {
        lemma_ans_keys_ok(c, s[k], sub_of(c, s[k]), coeff(c, s[k]));
        lemma_ans_row(c, s[k], sub_of(c, s[k]), coeff(c, s[k]));
        assert(v[k] == ans_row(c, s[k], sub_of(c, s[k]), coeff(c, s[k])));
    }
}

/// A row of a sorted permutation of mapped rows is the answer row of some element.
pub proof fn lemma_sorted_member(c: Ctx, s: Seq<int>, p: Seq<Row>, q: int)
    requires p.to_multiset() == s.map_values(out_p(c)).to_multiset(), 0 <= q < p.len(),
    ensures exists|k: int| 0 <= k < s.len() && p[q] == out_row(c, s[k]),
{
    broadcast use vstd::seq_lib::group_seq_properties;
    let v = s.map_values(out_p(c));
    assert(p.contains(p[q]));
    assert(p.to_multiset().count(p[q]) > 0);
    assert(v.to_multiset().count(p[q]) > 0);
    assert(v.contains(p[q]));
    let k = choose|k: int| 0 <= k < v.len() && v[k] == p[q];
    assert(v[k] == out_row(c, s[k]));
}

/// The final claim for the rows produced at threshold `t2`.
pub proof fn lemma_answer(db: Database, c: Ctx, ps: Seq<Literal>, rows: Seq<usize>, subs: Seq<usize>, coeffs: Seq<i128>,
    t2: int, out: Seq<Row>)
    requires
        db_ok(db, c),
        lits_ok(c, ps[0], ps[1]),
        ps.len() == 2,
        entries(c, rows, subs, coeffs, cands(c, 0, c.n, t2).filter(body_p(c))),
        rows.len() >= 100 || t2 == i128::MIN as int,
        i128::MIN as int <= t2,
        out == sort_rows(order_keys(), ans_rows(c, rows, subs, coeffs)).take(
            if rows.len() < 100 { rows.len() as int } else { 100 }),
    ensures ordered_ok(db, crate::query::query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    broadcast use vstd::seq_lib::group_seq_properties;
    let oq = crate::query::query_spec_at(ps);
    let keys = order_keys();
    let fb = body_p(c);
    let ge = ge_thr(c, t2);
    let lt = lt_thr(c, t2);
    let o = out_p(c);
    let a = cands(c, 0, c.n, i128::MIN as int);
    // The body.
    lemma_query_shape(ps);
    assert(ps =~= seq![ps[0], ps[1]]);
    lemma_body(db, c, ps[0], ps[1]);
    lemma_norm_cands(c, c.n);
    let body = a.filter(fb).map_values(o);
    assert(denote_body(db, oq) == Ok::<Relation, SqlError>(body));
    // The rows at t2 and the rest.
    lemma_cands_raise(c, 0, c.n, i128::MIN as int, t2);
    let top = a.filter(ge).filter(fb);
    let rest = a.filter(lt).filter(fb);
    lemma_ans_rows_eq(c, rows, subs, coeffs, top);
    let v = top.map_values(o);
    let w = rest.map_values(o);
    lemma_filter_split_multiset(a, fb, ge, lt, o);
    lemma_mapped_keys_ok(c, top);
    lemma_mapped_keys_ok(c, rest);
    lemma_sort_rows(keys, ans_fams(), v);
    lemma_sort_rows(keys, ans_fams(), w);
    let sv = sort_rows(keys, v);
    let sw = sort_rows(keys, w);
    sv.to_multiset_ensures();
    v.to_multiset_ensures();
    sw.to_multiset_ensures();
    w.to_multiset_ensures();
    assert(sv.len() == v.len());
    assert(sw.len() == w.len());
    let p = sv + sw;
    vstd::seq_lib::lemma_multiset_commutative(sv, sw);
    assert(p.to_multiset() == body.to_multiset());
    // Sorted: every row at t2 has a larger value than every row below it.
    assert forall|i: int, j: int| 0 <= i < sv.len() && 0 <= j < sw.len() implies keys_cmp(keys, #[trigger] sv[i], #[trigger] sw[j]) <= 0 by {
        lemma_sorted_member(c, top, sv, i);
        lemma_sorted_member(c, rest, sw, j);
        let x = choose|k: int| 0 <= k < top.len() && sv[i] == out_row(c, top[k]);
        let y = choose|k: int| 0 <= k < rest.len() && sw[j] == out_row(c, rest[k]);
        lemma_filter_source(a.filter(ge), fb, x);
        let x0 = choose|q: int| 0 <= q < a.filter(ge).len() && a.filter(ge)[q] == top[x];
        a.lemma_filter_pred(ge, x0);
        lemma_filter_source(a.filter(lt), fb, y);
        let y0 = choose|q: int| 0 <= q < a.filter(lt).len() && a.filter(lt)[q] == rest[y];
        a.lemma_filter_pred(lt, y0);
        let (ri, rj) = (top[x], rest[y]);
        lemma_keys_cmp_ans(c, ri, sub_of(c, ri), coeff(c, ri), rj, sub_of(c, rj), coeff(c, rj));
        lemma_ans_row(c, ri, sub_of(c, ri), coeff(c, ri));
        lemma_ans_row(c, rj, sub_of(c, rj), coeff(c, rj));
        assert(sv[i] == ans_row(c, ri, sub_of(c, ri), coeff(c, ri)));
        assert(sw[j] == ans_row(c, rj, sub_of(c, rj), coeff(c, rj)));
    }
    lemma_sorted_concat(keys, sv, sw);
    lemma_outcome_sorted(db, oq, body, p);
    // LIMIT 100.
    assert(v.len() == rows.len());
    if rows.len() >= 100 {
        assert(slice_rows(p, 0, Some(100nat)) =~= sv.take(100));
    } else {
        assert(t2 == i128::MIN as int);
        assert forall|k: int| 0 <= k < a.len() implies !lt(#[trigger] a[k]) by {
            lemma_cands_range(c, 0, c.n, i128::MIN as int, k);
        }
        lemma_filter_none(a, lt);
        reveal(Seq::filter);
        assert(rest =~= Seq::<int>::empty());
        assert(sw.len() == 0);
        assert(slice_rows(p, 0, Some(100nat)) =~= sv.take(rows.len() as int));
    }
}

} // verus!
