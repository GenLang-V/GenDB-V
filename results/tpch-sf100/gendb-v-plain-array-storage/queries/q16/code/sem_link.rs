//! From the fast path's group counts to the statement's groups (`sem_result`).
//!
//! Under the partsupp layout (`layout`: rows `l * a .. l * a + l` belong to part row `a`), unique part keys, complete
//! dictionaries (`no_miss`) and an exact bit set of excluded supplier keys (`excl_ok`), the distinct non-excluded
//! offsets of the partsupp rows of the part rows of group id `g` (`counts::tset`) correspond one to one
//! (`d ↦ smin + d`) to the distinct supplier keys of group `grow(g)` (`lemma_group_count`); every group of the
//! statement is some `grow(g)` (`lemma_every_group`); and the output rows of the present group ids are the
//! statement's output rows (`lemma_fast_rows`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::limits::int8_max;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem_sub::excluded;
use crate::agent::sem_row::*;
use crate::agent::sem_result::*;
use crate::agent::parts::*;
use crate::agent::counts::{row_vals, seg_vals, tset};
use crate::agent::output::*;
use crate::agent::common::bitset::*;
use crate::agent::common::ranks::{distinct_texts, distinct_ints};

verus! {

/// The partsupp rows of part row `a` are `l * a .. l * a + l`.
pub open spec fn layout(sv: StoresView, l: int) -> bool {
    &&& l >= 1 && ps_n(sv) == l * part_n(sv)
    &&& forall|a: int, i: int| 0 <= a < part_n(sv) && 0 <= i < l ==> #[trigger] ps_pkeys(sv)[l * a + i] == p_keys(sv)[a]
}

/// No part row of a listed size misses a dictionary.
pub open spec fn no_miss(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, sv: StoresView, ps: Seq<Literal>) -> bool {
    forall|a: int| 0 <= a < part_n(sv) ==> !#[trigger] missed(kb, kt, sv, ps, a)
}

/// The bit set `eb` holds exactly the excluded supplier keys of partsupp, as offsets from `smin`.
pub open spec fn excl_ok(sv: StoresView, smin: int, eb: Seq<u64>) -> bool {
    forall|c: int| 0 <= c < ps_n(sv) ==> 0 <= #[trigger] ps_skeys(sv)[c] - smin && in_bits(eb, ps_skeys(sv)[c] - smin)
        && (bit_at(eb, ps_skeys(sv)[c] - smin) == excluded(sv, ps_skeys(sv)[c] as int))
}

/// `rows` lists exactly the qualifying part rows of group id `g`.
pub open spec fn group_rows_are(rows: Seq<u32>, kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, sv: StoresView,
    ps: Seq<Literal>, g: int) -> bool {
    &&& forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]) < part_n(sv)
    &&& forall|a: int| 0 <= a < part_n(sv) ==> (#[trigger] rows.contains(a as u32)
        <==> part_ok(sv, ps, a) && gid_of(kb, kt, szl, sv, a) == g)
}

/// The facts shared by the lemmas below.
pub open spec fn fast_ok(sv: StoresView, ps: Seq<Literal>, kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>) -> bool {
    &&& stores_wf(sv) && keys_ok(sv) && param_domain_ok(ps)
    &&& distinct_texts(kb) && distinct_texts(kt) && sizes_ok(szl, ps)
    &&& kb.len() >= 1 && kt.len() >= 1
    &&& no_miss(kb, kt, sv, ps)
    &&& part_n(sv) < 0x1_0000_0000
}

/// The literal forms of the binding (`sem_row::lemma_params`).
pub open spec fn param_domain_ok(ps: Seq<Literal>) -> bool {
    ps.len() == 10
}

/// A qualifying part row's group id is in range and stands for its key.
pub proof fn lemma_gid_row(sv: StoresView, ps: Seq<Literal>, kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, a: int)
    requires fast_ok(sv, ps, kb, kt, szl), 0 <= a < part_n(sv), part_ok(sv, ps, a),
    ensures
        0 <= gid_of(kb, kt, szl, sv, a) < kb.len() * kt.len() * szl.len(),
        grow(kb, kt, szl, gid_of(kb, kt, szl, sv, a)) == krow(sv, a),
{
    assert(!missed(kb, kt, sv, ps, a));
    let (br, ty, sz) = (p_brand(sv, a), p_type(sv, a), p_sizes(sv)[a]);
    assert(kb.contains(br) && kt.contains(ty));
    assert(exists|j: int| 0 <= j < szl.len() && szl[j] == sz as int);
    let bi = key_index(kb, br);
    let ti = key_index(kt, ty);
    let si = size_index(szl, sz);
    assert(0 <= bi < kb.len() && kb[bi] == br);
    assert(0 <= ti < kt.len() && kt[ti] == ty);
    assert(0 <= si < szl.len() && szl[si] == sz);
    lemma_compose(bi, ti, si, kb.len() as int, kt.len() as int, szl.len() as int);
    let g = gid_of(kb, kt, szl, sv, a);
    assert(grow(kb, kt, szl, g) =~= krow(sv, a));
}

/// `grow` is injective on the group ids.
pub proof fn lemma_grow_injective(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, g1: int, g2: int)
    requires distinct_texts(kb), distinct_texts(kt), distinct_ints(szl), kb.len() >= 1, kt.len() >= 1, szl.len() >= 1,
        0 <= g1 < kb.len() * kt.len() * szl.len(), 0 <= g2 < kb.len() * kt.len() * szl.len(),
        grow(kb, kt, szl, g1) == grow(kb, kt, szl, g2),
    ensures g1 == g2,
{
    let (nb, nt, ns) = (kb.len() as int, kt.len() as int, szl.len() as int);
    lemma_decode(g1, nb, nt, ns);
    lemma_decode(g2, nb, nt, ns);
    let (r1, r2) = (grow(kb, kt, szl, g1), grow(kb, kt, szl, g2));
    assert(r1[0] == r2[0] && r1[1] == r2[1] && r1[2] == r2[2]);
    let (b1, t1, s1) = (bi_of(g1, nt, ns), ti_of(g1, nt, ns), si_of(g1, ns));
    let (b2, t2, s2) = (bi_of(g2, nt, ns), ti_of(g2, nt, ns), si_of(g2, ns));
    assert(kb[b1] == kb[b2] && kt[t1] == kt[t2] && szl[s1] == szl[s2]);
    assert(b1 == b2 && t1 == t2 && s1 == s2);
}

/// Every group of the statement is `grow(g)` for a group id `g`.
pub proof fn lemma_every_group(sv: StoresView, ps: Seq<Literal>, kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, k: Row)
    requires fast_ok(sv, ps, kb, kt, szl), is_group(sv, ps, k),
    ensures exists|g: int| 0 <= g < kb.len() * kt.len() * szl.len() && #[trigger] grow(kb, kt, szl, g) == k,
{
    let (c, a) = choose|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a) && krow(sv, a) == k;
    lemma_gid_row(sv, ps, kb, kt, szl, a);
    let g = gid_of(kb, kt, szl, sv, a);
    assert(grow(kb, kt, szl, g) == k);
}

/// An offset of `seg_vals` comes from a listed row; a listed row's offsets are in `seg_vals`.
proof fn lemma_seg_member(sk: Seq<i64>, l: int, smin: int, rows: Seq<u32>, d: int)
    requires l >= 1,
    ensures seg_vals(sk, l, smin, rows).contains(d) <==> exists|x: int, i: int| 0 <= x < rows.len() && 0 <= i < l
        && #[trigger] sk[l * rows[x] + i] as int - smin == d,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let p = rows.drop_last();
        let a = rows.last();
        lemma_seg_member(sk, l, smin, p, d);
        let sp = seg_vals(sk, l, smin, p);
        let rv = row_vals(sk, l, smin, a as int);
        assert(seg_vals(sk, l, smin, rows) == sp + rv);
        if seg_vals(sk, l, smin, rows).contains(d) {
            let y = choose|y: int| 0 <= y < (sp + rv).len() && (sp + rv)[y] == d;
            if y < sp.len() {
                assert(sp.contains(d));
                let (x, i) = choose|x: int, i: int| 0 <= x < p.len() && 0 <= i < l && #[trigger] sk[l * p[x] + i] as int - smin == d;
                assert(rows[x] == p[x]);
                assert(sk[l * rows[x] + i] as int - smin == d);
            } else {
                let i = y - sp.len();
                assert(rv[i] == d);
                assert(rows[rows.len() - 1] == a);
                assert(sk[l * rows[rows.len() - 1] + i] as int - smin == d);
            }
        }
        if exists|x: int, i: int| 0 <= x < rows.len() && 0 <= i < l && #[trigger] sk[l * rows[x] + i] as int - smin == d {
            let (x, i) = choose|x: int, i: int| 0 <= x < rows.len() && 0 <= i < l && #[trigger] sk[l * rows[x] + i] as int - smin == d;
            if x < p.len() {
                assert(p[x] == rows[x]);
                assert(sk[l * p[x] + i] as int - smin == d);
                assert(sp.contains(d));
                let y = choose|y: int| 0 <= y < sp.len() && sp[y] == d;
                assert((sp + rv)[y] == d);
            } else {
                assert(rows[x] == a);
                assert(rv[i] == d);
                assert((sp + rv)[sp.len() + i] == d);
            }
        }
    } else {
        assert(seg_vals(sk, l, smin, rows) =~= Seq::<int>::empty());
    }
}

/// The partsupp row `c` belongs to part row `c / l`, and to no other.
proof fn lemma_owner(sv: StoresView, l: int, c: int, a: int)
    requires stores_wf(sv), keys_ok(sv), layout(sv, l), 0 <= c < ps_n(sv), 0 <= a < part_n(sv),
        ps_pkeys(sv)[c] == p_keys(sv)[a],
    ensures c == l * a + c % l, 0 <= c % l < l,
{
    let a0 = c / l;
    let i = c % l;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(c, l);
    vstd::arithmetic::div_mod::lemma_mod_bound(c, l);
    assert(c == l * a0 + i);
    assert(0 <= a0 < part_n(sv)) by (nonlinear_arith)
        requires c == l * a0 + i, 0 <= i < l, 0 <= c < l * part_n(sv), l >= 1;
    assert(ps_pkeys(sv)[l * a0 + i] == p_keys(sv)[a0]);
    if a0 != a {
        assert(p_keys(sv)[a0] != p_keys(sv)[a]);
    }
}

/// The distinct supplier keys of group `grow(g)` are the offsets of `tset`, shifted by `smin`; so their numbers
/// agree, and the group exists exactly when the count is positive.
pub proof fn lemma_group_count(sv: StoresView, ps: Seq<Literal>, kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>,
    l: int, smin: int, eb: Seq<u64>, g: int, rows: Seq<u32>)
    requires
        fast_ok(sv, ps, kb, kt, szl), layout(sv, l), excl_ok(sv, smin, eb),
        0 <= g < kb.len() * kt.len() * szl.len(),
        group_rows_are(rows, kb, kt, szl, sv, ps, g),
    ensures
        tset(ps_skeys(sv), l, smin, rows, eb).len() == gcount(sv, ps, grow(kb, kt, szl, g)),
        is_group(sv, ps, grow(kb, kt, szl, g)) <==> tset(ps_skeys(sv), l, smin, rows, eb).len() > 0,
{
    let sk = ps_skeys(sv);
    let k = grow(kb, kt, szl, g);
    let t = tset(sk, l, smin, rows, eb);
    let f = |d: int| Val::Int(smin + d);
    let gv = gvals(sv, ps, k);
    let np = part_n(sv);
    assert(np * l == ps_n(sv)) by (nonlinear_arith) requires ps_n(sv) == l * np;
    assert forall|v: Val| #[trigger] gv.contains(v) <==> t.map(f).contains(v) by {
        lemma_vals_contains(sv, ps, k, v);
        if gv.contains(v) {
            let (c, a) = choose|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a)
                && krow(sv, a) == k && v == Val::Int(sk[c] as int);
            lemma_owner(sv, l, c, a);
            let i = c % l;
            lemma_gid_row(sv, ps, kb, kt, szl, a);
            lemma_grow_injective(kb, kt, szl, gid_of(kb, kt, szl, sv, a), g);
            assert(a < 0x1_0000_0000);
            assert(rows.contains(a as u32));
            let x = choose|x: int| 0 <= x < rows.len() && rows[x] == a as u32;
            assert(rows[x] as int == a);
            let d = sk[c] as int - smin;
            assert(sk[l * rows[x] + i] as int - smin == d);
            lemma_seg_member(sk, l, smin, rows, d);
            assert(!bit_at(eb, d));
            assert(t.contains(d));
            assert(f(d) == v);
        }
        if t.map(f).contains(v) {
            let d = choose|d: int| t.contains(d) && f(d) == v;
            lemma_seg_member(sk, l, smin, rows, d);
            let (x, i) = choose|x: int, i: int| 0 <= x < rows.len() && 0 <= i < l && #[trigger] sk[l * rows[x] + i] as int - smin == d;
            let a = rows[x] as int;
            assert(rows.contains(a as u32));
            assert(part_ok(sv, ps, a) && gid_of(kb, kt, szl, sv, a) == g);
            let c = l * a + i;
            assert(0 <= c < ps_n(sv)) by (nonlinear_arith) requires 0 <= a < np, 0 <= i < l, c == l * a + i, ps_n(sv) == l * np;
            assert(ps_pkeys(sv)[l * a + i] == p_keys(sv)[a]);
            assert(!excluded(sv, sk[c] as int));
            assert(qual(sv, ps, c, a));
            lemma_gid_row(sv, ps, kb, kt, szl, a);
            assert(in_vals(sv, ps, k, v));
        }
    }
    assert(gv =~= t.map(f));
    assert forall|d1: int, d2: int| t.contains(d1) && t.contains(d2) && f(d1) == f(d2) implies d1 == d2 by {}
    vstd::set_lib::lemma_map_size(t, t.map(f), f);
    if is_group(sv, ps, k) {
        let (c, a) = choose|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a) && krow(sv, a) == k;
        lemma_vals_contains(sv, ps, k, Val::Int(sk[c] as int));
        assert(gv.contains(Val::Int(sk[c] as int)));
        if gv.len() == 0 { assert(gv =~= Set::empty()); }
    }
    if t.len() > 0 {
        if !exists|v: Val| gv.contains(v) { assert(gv =~= Set::empty()); }
        let v = choose|v: Val| gv.contains(v);
        lemma_vals_contains(sv, ps, k, v);
    }
}

/// The counts of all group ids: present ids are the statement's groups, the output rows are its output rows, and
/// every count fits.
pub proof fn lemma_fast_rows(sv: StoresView, ps: Seq<Literal>, kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>,
    cnt: Seq<u64>, out: Seq<Row>)
    requires
        fast_ok(sv, ps, kb, kt, szl), tables_ok(kb, kt, szl, cnt),
        forall|g: int| 0 <= g < cnt.len() ==> #[trigger] cnt[g] == gcount(sv, ps, grow(kb, kt, szl, g))
            && (is_group(sv, ps, grow(kb, kt, szl, g)) <==> cnt[g] > 0),
        forall|row: Row| #[trigger] out.contains(row) <==> exists|g: int| #[trigger] present(cnt, g)
            && row == orow(kb, kt, szl, cnt, g),
    ensures
        counts_fit(sv, ps),
        forall|r: Row| #[trigger] out.contains(r) <==> exists|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k),
{
    assert forall|k: Row| #[trigger] is_group(sv, ps, k) implies gcount(sv, ps, k) <= int8_max() by {
        lemma_every_group(sv, ps, kb, kt, szl, k);
        let g = choose|g: int| 0 <= g < kb.len() * kt.len() * szl.len() && #[trigger] grow(kb, kt, szl, g) == k;
        assert(cnt[g] == gcount(sv, ps, k));
    }
    assert forall|r: Row| #[trigger] out.contains(r) <==> exists|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k) by {
        if out.contains(r) {
            let g = choose|g: int| #[trigger] present(cnt, g) && r == orow(kb, kt, szl, cnt, g);
            let k = grow(kb, kt, szl, g);
            assert(cnt[g] == gcount(sv, ps, k));
            assert(is_group(sv, ps, k));
            assert(r == out_row(sv, ps, k));
        }
        if exists|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k) {
            let k = choose|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k);
            lemma_every_group(sv, ps, kb, kt, szl, k);
            let g = choose|g: int| 0 <= g < kb.len() * kt.len() * szl.len() && #[trigger] grow(kb, kt, szl, g) == k;
            assert(cnt[g] == gcount(sv, ps, k));
            assert(present(cnt, g));
            assert(r == orow(kb, kt, szl, cnt, g));
        }
    }
}

} // verus!
