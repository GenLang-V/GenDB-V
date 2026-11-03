//! ORDER BY value DESC, name, tag LIMIT 100 over the answer rows at threshold `t2`.
//!
//! The answer rows at `t2` are sorted with the statement's own stable insertion sort (`spec::order::sort_rows`,
//! mirrored by `rank::sort_positions`). The witness permutation of all answer rows is that sorted list followed by
//! the sorted answer rows below `t2`: every row of the first part has a larger value than every row of the second,
//! so the concatenation is sorted, and its first 100 rows are the first 100 sorted rows at `t2` (when there are at
//! least 100 of them, or when `t2 = i128::MIN` and no row is below it).
use vstd::prelude::*;
use vstd::multiset::Multiset;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::order::*;
use crate::bridge::order::*;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::link::expr::{lemma_compare_num, lemma_align_same};
use crate::agent::spec::*;
use crate::agent::sem::*;

verus! {

/// An answer row given by its parts: `[sub.name of s, tag of r, Num(co, 4)]`.
#[verifier::opaque]
pub open spec fn ans_row(c: Ctx, r: int, s: int, co: int) -> Row {
    seq![Val::Text(sname_text(c, s)), Val::Text(tag_text(c, r)), (Val::Num { coeff: co, scale: 4 })]
}

/// The answer rows of parallel vectors (num row, sub row, coefficient).
pub open spec fn ans_rows(c: Ctx, rows: Seq<usize>, subs: Seq<usize>, coeffs: Seq<i128>) -> Seq<Row> {
    Seq::new(rows.len(), |k: int| ans_row(c, rows[k] as int, subs[k] as int, coeffs[k] as int))
}

/// ORDER BY on two answer rows: value DESC, then name, then tag.
pub proof fn lemma_keys_cmp_ans(c: Ctx, ra: int, sa: int, ca: int, rb: int, sb: int, cb: int)
    ensures keys_cmp(order_keys(), ans_row(c, ra, sa, ca), ans_row(c, rb, sb, cb)) == if ca > cb {
            -1
        } else if ca < cb {
            1
        } else if lex_cmp_of(sname_text(c, sa), sname_text(c, sb)) != 0 {
            lex_cmp_of(sname_text(c, sa), sname_text(c, sb))
        } else {
            lex_cmp_of(tag_text(c, ra), tag_text(c, rb))
        },
{
    reveal(ans_row);
    let (x, y) = (ans_row(c, ra, sa, ca), ans_row(c, rb, sb, cb));
    let ks = order_keys();
    reveal_with_fuel(keys_cmp, 4);
    lemma_compare_num(ca, 4, cb, 4);
    lemma_align_same(ca, 4);
    lemma_align_same(cb, 4);
    assert(max_nat(4, 4) == 4);
    assert(ks.drop_first() =~= seq![OrderKey { col: 0, desc: false, nulls_first: false }, OrderKey { col: 1, desc: false, nulls_first: false }]);
    assert(ks.drop_first().drop_first() =~= seq![OrderKey { col: 1, desc: false, nulls_first: false }]);
    assert(ks.drop_first().drop_first().drop_first() =~= Seq::<OrderKey>::empty());
    crate::bridge::order::lemma_lex_cmp_antisym(sname_text(c, sa), sname_text(c, sb));
    crate::bridge::order::lemma_lex_cmp_antisym(tag_text(c, ra), tag_text(c, rb));
}

/// `lex_cmp` (named for the ensures of `rank::row_cmp`).
pub open spec fn lex_cmp_of(a: Seq<u8>, b: Seq<u8>) -> int {
    crate::spec::text::lex_cmp(a, b)
}

/// The value of an answer row.
pub proof fn lemma_ans_row(c: Ctx, r: int, s: int, co: int)
    ensures ans_row(c, r, s, co) == seq![Val::Text(sname_text(c, s)), Val::Text(tag_text(c, r)), (Val::Num { coeff: co, scale: 4 })],
{
    reveal(ans_row);
}

/// The sort of no rows.
pub proof fn lemma_sort_empty(keys: Seq<OrderKey>, v: Seq<Row>)
    ensures sort_rows(keys, v.take(0)) == Seq::<Row>::empty(),
{
    assert(v.take(0) =~= Seq::<Row>::empty());
}

/// One step of the stable insertion sort.
pub proof fn lemma_sort_step(keys: Seq<OrderKey>, v: Seq<Row>, k: int)
    requires 0 <= k < v.len(),
    ensures sort_rows(keys, v.take(k + 1)) == insert_sorted(keys, sort_rows(keys, v.take(k)), v[k]),
{
    assert(v.take(k + 1).drop_last() =~= v.take(k));
    assert(v.take(k + 1).last() == v[k]);
}

/// Stable insertion: inserting `r` after the last row that is not greater (position `j`).
pub proof fn lemma_insert_at(keys: Seq<OrderKey>, s: Seq<Row>, r: Row, j: int)
    requires
        0 <= j <= s.len(),
        j == 0 || keys_cmp(keys, s[j - 1], r) <= 0,
        forall|q: int| j <= q < s.len() ==> keys_cmp(keys, #[trigger] s[q], r) > 0,
    ensures insert_sorted(keys, s, r) == s.take(j) + seq![r] + s.skip(j),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.take(0) + seq![r] + s.skip(0) =~= seq![r]);
    } else if j == s.len() {
        assert(keys_cmp(keys, s.last(), r) <= 0);
        assert(s.take(j) + seq![r] + s.skip(j) =~= s.push(r));
    } else {
        assert(keys_cmp(keys, s[s.len() - 1], r) > 0);
        let d = s.drop_last();
        assert forall|q: int| j <= q < d.len() implies keys_cmp(keys, #[trigger] d[q], r) > 0 by {
            assert(d[q] == s[q]);
        }
        if j > 0 {
            assert(d[j - 1] == s[j - 1]);
        }
        lemma_insert_at(keys, d, r, j);
        assert((d.take(j) + seq![r] + d.skip(j)).push(s.last()) =~= s.take(j) + seq![r] + s.skip(j));
    }
}

/// The family of every key of an answer row (numeric value, text name, text tag).
pub open spec fn ans_fams() -> Seq<int> {
    seq![1int, 3, 3]
}

pub proof fn lemma_ans_keys_ok(c: Ctx, r: int, s: int, co: int)
    ensures keys_ok(order_keys(), ans_fams(), ans_row(c, r, s, co)),
{
    reveal(ans_row);
    let x = ans_row(c, r, s, co);
    assert forall|i: int| 0 <= i < order_keys().len() implies #[trigger] key_ok(order_keys()[i], ans_fams()[i], x) by {
        if i == 0 {} else if i == 1 {} else {}
    }
}

/// Two sorted sequences, every row of the first not above any of the second, concatenate sorted.
pub proof fn lemma_sorted_concat(keys: Seq<OrderKey>, a: Seq<Row>, b: Seq<Row>)
    requires
        sorted_by(keys, a),
        sorted_by(keys, b),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> keys_cmp(keys, #[trigger] a[i], #[trigger] b[j]) <= 0,
    ensures sorted_by(keys, a + b),
{
    let s = a + b;
    assert forall|i: int, j: int| 0 <= i < j < s.len() implies keys_cmp(keys, #[trigger] s[i], #[trigger] s[j]) <= 0 by {
        if j < a.len() {
            assert(s[i] == a[i] && s[j] == a[j]);
        } else if i >= a.len() {
            assert(s[i] == b[i - a.len()] && s[j] == b[j - a.len()]);
        } else {
            assert(s[i] == a[i] && s[j] == b[j - a.len()]);
        }
    }
}

/// Splitting a filter by a second condition splits its mapped multiset.
pub proof fn lemma_filter_split_multiset(s: Seq<int>, f: spec_fn(int) -> bool, g: spec_fn(int) -> bool, ng: spec_fn(int) -> bool,
    o: spec_fn(int) -> Row)
    requires forall|x: int| #[trigger] ng(x) == !g(x),
    ensures
        s.filter(f).map_values(o).to_multiset()
            == s.filter(g).filter(f).map_values(o).to_multiset().add(s.filter(ng).filter(f).map_values(o).to_multiset()),
    decreases s.len(),
{
    broadcast use vstd::seq_lib::group_seq_properties;
    broadcast use vstd::multiset::group_multiset_axioms;
    if s.len() == 0 {
        reveal(Seq::filter);
        assert(s.filter(f).map_values(o) =~= Seq::<Row>::empty());
        assert(s.filter(g).filter(f).map_values(o) =~= Seq::<Row>::empty());
        assert(s.filter(ng).filter(f).map_values(o) =~= Seq::<Row>::empty());
        assert(Multiset::<Row>::empty().add(Multiset::<Row>::empty()) =~= Multiset::<Row>::empty());
    } else {
        let d = s.drop_last();
        let x = s.last();
        assert(d.push(x) =~= s);
        lemma_filter_split_multiset(d, f, g, ng, o);
        lemma_filter_push(d, x, f);
        lemma_filter_push(d, x, g);
        lemma_filter_push(d, x, ng);
        lemma_filter_push(d.filter(g), x, f);
        lemma_filter_push(d.filter(ng), x, f);
        if f(x) {
            assert(d.filter(f).push(x).map_values(o) =~= d.filter(f).map_values(o).push(o(x)));
            if g(x) {
                assert(d.filter(g).filter(f).push(x).map_values(o) =~= d.filter(g).filter(f).map_values(o).push(o(x)));
            } else {
                assert(d.filter(ng).filter(f).push(x).map_values(o) =~= d.filter(ng).filter(f).map_values(o).push(o(x)));
            }
            let m1 = d.filter(g).filter(f).map_values(o).to_multiset();
            let m2 = d.filter(ng).filter(f).map_values(o).to_multiset();
            assert(m1.add(m2).insert(o(x)) =~= m1.insert(o(x)).add(m2));
            assert(m1.add(m2).insert(o(x)) =~= m1.add(m2.insert(o(x))));
        } else {
            if g(x) {
                lemma_filter_push(d.filter(g), x, f);
            } else {
                lemma_filter_push(d.filter(ng), x, f);
            }
        }
    }
}

} // verus!
