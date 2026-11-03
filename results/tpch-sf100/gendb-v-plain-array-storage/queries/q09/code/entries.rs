//! The output groups as a list of entries (`elist_ok`: exactly the non-empty (group, year) pairs, each with its
//! amount sum, every group's absolute amount within `i128`), from the fast path's table (`table_entries`), and the
//! output rows (`output_rows`): the entries sorted by name, then year descending (`answer::entry_lt`, a strict
//! total order on the entries: groups have distinct names), as the statement's rows (`answer::answer_ok`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::text::lex_cmp;
use crate::gendb_entry::stores::StoresView;
use crate::exec::value::EVal;
use crate::exec::text::lex_cmp_exec;
use crate::link::query::view_rows;
use crate::link::expr::i128_max;
use crate::bridge::order::{lemma_lex_cmp_antisym, lemma_lex_cmp_trans};
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::agent::tables::*;
use crate::agent::lines::*;
use crate::agent::answer::*;
use crate::agent::columns::*;
use crate::agent::nations::*;
use crate::agent::scan::*;
use crate::agent::partmatch::copy_range;

verus! {

/// One output group: nation group `a`, year `y`, amount sum `sum`.
#[derive(Clone, Copy)]
pub struct Entry {
    pub a: usize,
    pub y: i64,
    pub sum: i128,
}

pub open spec fn ekey(e: Entry) -> (int, int) { (e.a as int, e.y as int) }

/// The entries are exactly the non-empty (group, year) pairs of the rows `0..n`, with their sums; every group's
/// absolute amount fits `i128`.
pub open spec fn elist_ok(es: Seq<Entry>, sv: StoresView, ps: Seq<Literal>, n: int) -> bool {
    &&& forall|i: int| 0 <= i < es.len() ==> 0 <= (#[trigger] es[i]).a < n_n(sv) && nrep(sv, es[i].a as int) == es[i].a
        && tsum(sv, ps, es[i].a as int, es[i].y as int, 0, 0, n) > 0
        && es[i].sum as int == tsum(sv, ps, es[i].a as int, es[i].y as int, 1, 0, n)
    &&& forall|i: int, j: int| 0 <= i < es.len() && 0 <= j < es.len() && i != j ==> ekey(#[trigger] es[i]) != ekey(#[trigger] es[j])
    &&& forall|a: int, y: int| 0 <= a < n_n(sv) && nrep(sv, a) == a && #[trigger] tsum(sv, ps, a, y, 0, 0, n) > 0
        ==> exists|i: int| 0 <= i < es.len() && ekey(es[i]) == (a, y)
    &&& forall|a: int, y: int| #[trigger] tsum(sv, ps, a, y, 2, 0, n) <= i128_max()
}

/// A non-empty (group, year) pair has a qualifying row; its group is a group's first row.
pub proof fn lemma_tsum_witness(sv: StoresView, ps: Seq<Literal>, a: int, y: int, lo: int, hi: int) -> (l: int)
    requires tsum(sv, ps, a, y, 0, lo, hi) > 0,
    ensures lo <= l < hi, line_qual(sv, ps, l), grp(sv, l) == a, yr(sv, l) == y,
        0 <= a < n_n(sv), nrep(sv, a) == a,
    decreases hi - lo,
{
    if tsum(sv, ps, a, y, 0, lo, hi - 1) > 0 {
        lemma_tsum_witness(sv, ps, a, y, lo, hi - 1)
    } else {
        let l = hi - 1;
        assert(tterm(sv, ps, a, y, 0, l) > 0);
        lemma_line_key_grp(sv, ps, l);
        l
    }
}

// ------------------------------------------------------------------------------------------------ from the table

/// The entries of the table of all rows: its slots with a non-zero count.
pub fn table_entries(acc: &Vec<i128>, cnt: &Vec<u64>, mass: u128, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (es: Vec<Entry>)
    requires table_ok(acc@, cnt@, mass, sv, ps, 0, n_l(sv)),
    ensures elist_ok(es@, sv, ps, n_l(sv)),
{
    let ghost n = n_l(sv);
    let mut es: Vec<Entry> = Vec::new();
    let ghost mut ixs: Seq<int> = Seq::empty();
    let mut ix: usize = 0;
    while ix < NT
        invariant
            ix <= NT, table_ok(acc@, cnt@, mass, sv, ps, 0, n), es@.len() == ixs.len(),
            forall|i: int| 0 <= i < es@.len() ==> 0 <= #[trigger] ixs[i] < ix && cnt@[ixs[i]] > 0
                && es@[i].a as int == tgrp(ixs[i]) && es@[i].y as int == tyr(ixs[i]) && es@[i].sum == acc@[ixs[i]],
            forall|i: int, j: int| 0 <= i < j < es@.len() ==> #[trigger] ixs[i] < #[trigger] ixs[j],
            forall|x: int| 0 <= x < ix && cnt@[x] > 0 ==> exists|i: int| 0 <= i < es@.len() && #[trigger] ixs[i] == x,
        decreases NT - ix,
    {
        if cnt[ix] > 0 {
            proof {
                assert(acc@[ix as int] as int == tsum(sv, ps, tgrp(ix as int), tyr(ix as int), 1, 0, n));
                assert(cnt@[ix as int] as int == tsum(sv, ps, tgrp(ix as int), tyr(ix as int), 0, 0, n));
                lemma_tsum_witness(sv, ps, tgrp(ix as int), tyr(ix as int), 0, n);
            }
            let e = Entry { a: ix / 255, y: Y0 + (ix % 255) as i64, sum: acc[ix] };
            let ghost es0 = es@;
            let ghost ixs0 = ixs;
            es.push(e);
            proof {
                ixs = ixs0.push(ix as int);
                assert forall|i: int| 0 <= i < es0.len() implies #[trigger] ixs[i] == ixs0[i] && es@[i] == es0[i] by {}
                assert forall|x: int| 0 <= x < ix + 1 && cnt@[x] > 0 implies exists|i: int| 0 <= i < es@.len() && #[trigger] ixs[i] == x by {
                    if x == ix { assert(ixs[ixs.len() - 1] == x); }
                    else {
                        let i = choose|i: int| 0 <= i < es0.len() && #[trigger] ixs0[i] == x;
                        assert(ixs[i] == x);
                    }
                }
            }
        }
        ix = ix + 1;
    }
    proof {
        // entries
        assert forall|i: int| 0 <= i < es@.len() implies 0 <= (#[trigger] es@[i]).a < n_n(sv) && nrep(sv, es@[i].a as int) == es@[i].a
            && tsum(sv, ps, es@[i].a as int, es@[i].y as int, 0, 0, n) > 0
            && es@[i].sum as int == tsum(sv, ps, es@[i].a as int, es@[i].y as int, 1, 0, n) by {
            let x = ixs[i];
            assert(acc@[x] as int == tsum(sv, ps, tgrp(x), tyr(x), 1, 0, n));
            assert(cnt@[x] as int == tsum(sv, ps, tgrp(x), tyr(x), 0, 0, n));
            lemma_tsum_witness(sv, ps, tgrp(x), tyr(x), 0, n);
        }
        // distinct keys
        assert forall|i: int, j: int| 0 <= i < es@.len() && 0 <= j < es@.len() && i != j implies ekey(#[trigger] es@[i]) != ekey(#[trigger] es@[j]) by {
            let (x1, x2) = (ixs[i], ixs[j]);
            if i < j { assert(x1 < x2); } else { assert(x2 < x1); }
            if tgrp(x1) == tgrp(x2) && tyr(x1) == tyr(x2) {
                assert(x1 == tgrp(x1) * 255 + x1 % 255) by (nonlinear_arith) requires 0 <= x1, tgrp(x1) == x1 / 255;
                assert(x2 == tgrp(x2) * 255 + x2 % 255) by (nonlinear_arith) requires 0 <= x2, tgrp(x2) == x2 / 255;
            }
        }
        // complete
        assert forall|a: int, y: int| 0 <= a < n_n(sv) && nrep(sv, a) == a && #[trigger] tsum(sv, ps, a, y, 0, 0, n) > 0
            implies exists|i: int| 0 <= i < es@.len() && ekey(es@[i]) == (a, y) by {
            let yi = y - Y0;
            lemma_slot(a, yi);
            let x = a * 255 + yi;
            assert(acc@[x] as int == tsum(sv, ps, a, y, 1, 0, n));
            assert(cnt@[x] as int == tsum(sv, ps, a, y, 0, 0, n));
            let i = choose|i: int| 0 <= i < es@.len() && #[trigger] ixs[i] == x;
            assert(ekey(es@[i]) == (a, y));
        }
        // masses
        assert forall|a: int, y: int| #[trigger] tsum(sv, ps, a, y, 2, 0, n) <= i128_max() by {
            lemma_tsum_bounds(sv, ps, a, y, 0, n);
        }
    }
    es
}

// ------------------------------------------------------------------------------------------------ the order

/// `entry_lt` is irreflexive, transitive and total on distinct group/year pairs whose groups are first rows.
proof fn lemma_entry_order(sv: StoresView, e: (int, int), f: (int, int), g: (int, int))
    requires 0 <= e.0 && nrep(sv, e.0) == e.0, 0 <= f.0 && nrep(sv, f.0) == f.0, 0 <= g.0 && nrep(sv, g.0) == g.0,
    ensures
        !entry_lt(sv, e, e),
        e != f ==> entry_lt(sv, e, f) || entry_lt(sv, f, e),
        entry_lt(sv, e, f) && entry_lt(sv, f, g) ==> entry_lt(sv, e, g),
        entry_lt(sv, e, f) ==> !entry_lt(sv, f, e),
{
    let (ne, nf, ng) = (nname(sv, e.0), nname(sv, f.0), nname(sv, g.0));
    lemma_lex_cmp_zero(ne, ne);
    lemma_lex_cmp_zero(ne, nf);
    lemma_lex_cmp_zero(nf, ng);
    lemma_lex_cmp_zero(ne, ng);
    lemma_lex_cmp_antisym(ne, nf);
    lemma_lex_cmp_antisym(nf, ng);
    lemma_lex_cmp_antisym(ne, ng);
    lemma_nrep_eq(sv, e.0, f.0);
    lemma_nrep_eq(sv, f.0, g.0);
    lemma_nrep_eq(sv, e.0, g.0);
    if entry_lt(sv, e, f) && entry_lt(sv, f, g) {
        if lex_cmp(ne, nf) < 0 && lex_cmp(nf, ng) < 0 {
            lemma_lex_cmp_trans(ne, nf, ng);
        }
    }
}

/// `entry_lt` of two entries, executably.
fn entry_lt_exec(names: &Vec<Vec<u8>>, e: Entry, f: Entry, Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires e.a < names@.len(), f.a < names@.len(),
        forall|a: int| 0 <= a < names@.len() ==> (#[trigger] names@[a])@ == nname(sv, a),
    ensures r == entry_lt(sv, ekey(e), ekey(f)),
{
    let cmp = lex_cmp_exec(&names[e.a], &names[f.a]);
    cmp < 0 || (e.a == f.a && e.y > f.y)
}

/// The names of the nation rows.
fn nation_names(c: &Cols, Ghost(sv): Ghost<StoresView>) -> (names: Vec<Vec<u8>>)
    requires cols_ok(*c, sv),
    ensures names@.len() == c.nn, forall|a: int| 0 <= a < c.nn ==> (#[trigger] names@[a])@ == nname(sv, a),
{
    let mut names: Vec<Vec<u8>> = Vec::new();
    let mut a: usize = 0;
    while a < c.nn
        invariant a <= c.nn, cols_ok(*c, sv), names@.len() == a, forall|x: int| 0 <= x < a ==> (#[trigger] names@[x])@ == nname(sv, x),
        decreases c.nn - a,
    {
        let s = c.noffs[a];
        let e = c.noffs[a + 1];
        assert(0 <= s <= e <= c.nbytes@.len());
        names.push(copy_range(c.nbytes, s as usize, e as usize));
        a = a + 1;
    }
    names
}

/// The indices of the entries sorted by `entry_lt` (insertion sort).
fn sort_entries(es: &Vec<Entry>, names: &Vec<Vec<u8>>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(n): Ghost<int>)
    -> (order: Vec<usize>)
    requires
        elist_ok(es@, sv, ps, n), names@.len() == n_n(sv),
        forall|a: int| 0 <= a < names@.len() ==> (#[trigger] names@[a])@ == nname(sv, a),
    ensures
        order@.len() == es@.len(),
        forall|p: int| 0 <= p < order@.len() ==> (#[trigger] order@[p]) < es@.len(),
        forall|x: int| 0 <= x < es@.len() ==> #[trigger] order@.contains(x as usize),
        forall|p: int, q: int| 0 <= p < q < order@.len() ==> entry_lt(sv, ekey(es@[#[trigger] order@[p] as int]), ekey(es@[#[trigger] order@[q] as int])),
{
    let mut order: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < es.len()
        invariant
            i <= es@.len(), elist_ok(es@, sv, ps, n), names@.len() == n_n(sv),
            forall|a: int| 0 <= a < names@.len() ==> (#[trigger] names@[a])@ == nname(sv, a),
            order@.len() == i,
            forall|p: int| 0 <= p < order@.len() ==> (#[trigger] order@[p]) < i,
            forall|x: int| 0 <= x < i ==> #[trigger] order@.contains(x as usize),
            forall|p: int, q: int| 0 <= p < q < order@.len() ==> entry_lt(sv, ekey(es@[#[trigger] order@[p] as int]), ekey(es@[#[trigger] order@[q] as int])),
        decreases es@.len() - i,
    {
        let ei = es[i];
        let mut p: usize = 0;
        while p < order.len() && entry_lt_exec(names, es[order[p]], ei, Ghost(sv))
            invariant
                p <= order@.len(), i < es@.len(), ei == es@[i as int], elist_ok(es@, sv, ps, n), names@.len() == n_n(sv),
                forall|a: int| 0 <= a < names@.len() ==> (#[trigger] names@[a])@ == nname(sv, a),
                forall|q: int| 0 <= q < order@.len() ==> (#[trigger] order@[q]) < i,
                forall|q: int| 0 <= q < p ==> entry_lt(sv, ekey(es@[#[trigger] order@[q] as int]), ekey(ei)),
            decreases order@.len() - p,
        {
            p = p + 1;
        }
        let ghost before = order@;
        proof {
            let ki = ekey(ei);
            assert(0 <= ei.a && nrep(sv, ei.a as int) == ei.a);
            if p < before.len() {
                let kp = ekey(es@[before[p as int] as int]);
                assert(!entry_lt(sv, kp, ki));
                assert(before[p as int] != i);
                assert(kp != ki);
                lemma_entry_order(sv, ki, kp, kp);
                assert(entry_lt(sv, ki, kp));
                assert forall|q: int| p <= q < before.len() implies entry_lt(sv, ki, ekey(es@[#[trigger] before[q] as int])) by {
                    if q > p {
                        let kq = ekey(es@[before[q] as int]);
                        lemma_entry_order(sv, ki, kp, kq);
                    }
                }
            }
        }
        order.insert(p, i);
        proof {
            let ki = ekey(ei);
            assert(order@ == before.insert(p as int, i));
            assert forall|q: int| 0 <= q < order@.len() implies (#[trigger] order@[q]) < i + 1 by {
                if q < p { assert(order@[q] == before[q]); } else if q > p { assert(order@[q] == before[q - 1]); }
            }
            assert forall|x: int| 0 <= x < i + 1 implies #[trigger] order@.contains(x as usize) by {
                if x == i {
                    assert(order@[p as int] == i);
                } else {
                    assert(before.contains(x as usize));
                    let q = choose|q: int| 0 <= q < before.len() && before[q] == x as usize;
                    if q < p { assert(order@[q] == before[q]); } else { assert(order@[q + 1] == before[q]); }
                }
            }
            assert forall|q1: int, q2: int| 0 <= q1 < q2 < order@.len() implies
                entry_lt(sv, ekey(es@[#[trigger] order@[q1] as int]), ekey(es@[#[trigger] order@[q2] as int])) by {
                if q2 < p {
                    assert(order@[q1] == before[q1] && order@[q2] == before[q2]);
                } else if q2 == p {
                    assert(order@[q1] == before[q1] && order@[q2] == i);
                } else if q1 == p {
                    assert(order@[q1] == i && order@[q2] == before[q2 - 1]);
                } else if q1 < p {
                    assert(order@[q1] == before[q1] && order@[q2] == before[q2 - 1]);
                } else {
                    assert(order@[q1] == before[q1 - 1] && order@[q2] == before[q2 - 1]);
                }
            }
        }
        i = i + 1;
    }
    order
}

// ------------------------------------------------------------------------------------------------ the rows

/// The output rows of the entries, sorted by name then year descending, and their (group, year) list.
pub fn output_rows(c: &Cols, es: &Vec<Entry>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: (Vec<Vec<EVal>>, Ghost<Seq<(int, int)>>))
    requires cols_ok(*c, sv), elist_ok(es@, sv, ps, n_l(sv)),
    ensures answer_ok(sv, ps, r.1@, n_l(sv)), view_rows(r.0@) == answer_rows(sv, ps, r.1@),
{
    let ghost n = n_l(sv);
    let names = nation_names(c, Ghost(sv));
    let order = sort_entries(es, &names, Ghost(sv), Ghost(ps), Ghost(n));
    let ghost ent = order@.map_values(|x: usize| ekey(es@[x as int]));
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut p: usize = 0;
    while p < order.len()
        invariant
            p <= order@.len(), order@.len() == es@.len(), elist_ok(es@, sv, ps, n), names@.len() == n_n(sv),
            forall|a: int| 0 <= a < names@.len() ==> (#[trigger] names@[a])@ == nname(sv, a),
            forall|q: int| 0 <= q < order@.len() ==> (#[trigger] order@[q]) < es@.len(),
            ent == order@.map_values(|x: usize| ekey(es@[x as int])), n == n_l(sv),
            view_rows(rows@) == answer_rows(sv, ps, ent.subrange(0, p as int)),
        decreases order@.len() - p,
    {
        let e = es[order[p]];
        let name = copy_range(&names[e.a], 0, names[e.a].len());
        let mut row: Vec<EVal> = Vec::new();
        row.push(EVal::Text(name));
        row.push(EVal::Num { coeff: e.y as i128, scale: 0 });
        row.push(EVal::Num { coeff: e.sum, scale: 4 });
        let ghost rows0 = rows@;
        rows.push(row);
        proof {
            assert(names@[e.a as int]@.subrange(0, names@[e.a as int]@.len() as int) =~= names@[e.a as int]@);
            let k = ent[p as int];
            assert(k == ekey(e));
            assert(crate::exec::value::view_row(row@) =~= entry_row(sv, ps, k));
            assert(ent.subrange(0, p + 1) =~= ent.subrange(0, p as int).push(k));
            assert(view_rows(rows@) =~= view_rows(rows0).push(crate::exec::value::view_row(row@)));
            assert(answer_rows(sv, ps, ent.subrange(0, p + 1)) =~= answer_rows(sv, ps, ent.subrange(0, p as int)).push(entry_row(sv, ps, k)));
        }
        p = p + 1;
    }
    proof {
        assert(ent.subrange(0, order@.len() as int) =~= ent);
        // the answer's conditions
        assert forall|i: int| 0 <= i < ent.len() implies 0 <= (#[trigger] ent[i]).0 < n_n(sv) && nrep(sv, ent[i].0) == ent[i].0
            && tsum(sv, ps, ent[i].0, ent[i].1, 0, 0, n) > 0 by {
            assert(ent[i] == ekey(es@[order@[i] as int]));
        }
        assert forall|a: int, y: int| 0 <= a < n_n(sv) && nrep(sv, a) == a && #[trigger] tsum(sv, ps, a, y, 0, 0, n) > 0
            implies ent.contains((a, y)) by {
            let i = choose|i: int| 0 <= i < es@.len() && ekey(es@[i]) == (a, y);
            assert(order@.contains(i as usize));
            let q = choose|q: int| 0 <= q < order@.len() && order@[q] == i as usize;
            assert(ent[q] == (a, y));
        }
        assert forall|i: int, j: int| 0 <= i < j < ent.len() implies entry_lt(sv, #[trigger] ent[i], #[trigger] ent[j]) by {
            assert(ent[i] == ekey(es@[order@[i] as int]) && ent[j] == ekey(es@[order@[j] as int]));
        }
    }
    (rows, Ghost(ent))
}

} // verus!
