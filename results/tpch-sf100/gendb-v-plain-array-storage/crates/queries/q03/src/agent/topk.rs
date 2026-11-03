//! Top 10 groups by `revenue DESC, o_orderdate`: insertion into a sorted list of at most 10 groups.
//!
//! On the group rows the ORDER BY comparison is `row_cmp(sum, date, sum', date')` (`lemma_order_row_cmp`): the
//! larger sum first, then the earlier date. A group enters the list when the list has room or it sorts strictly
//! before the last entry; it goes after the entries that do not sort after it, and the 11th entry drops out.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::order::*;
use crate::spec::ast::{Literal, OrderKey};
use crate::spec::scalar::compare;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::source_check::date32_val;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::denotation::q3_order_keys;
use crate::agent::answer::*;

verus! {

/// ORDER BY revenue DESC, o_orderdate on (sum, date) pairs: negative when the first sorts strictly first.
pub open spec fn row_cmp(s1: int, d1: int, s2: int, d2: int) -> int {
    if s1 > s2 { -1 } else if s1 < s2 { 1 } else { sign(d1 - d2) }
}

/// The ORDER BY keys on two group rows.
pub proof fn lemma_order_row_cmp(sv: StoresView, j1: int, s1: int, j2: int, s2: int)
    ensures keys_cmp(q3_order_keys(), order_row(sv, j1, s1), order_row(sv, j2, s2)) == row_cmp(s1, od(sv)[j1] as int, s2, od(sv)[j2] as int),
{
    let keys = q3_order_keys();
    let (r1, r2) = (order_row(sv, j1, s1), order_row(sv, j2, s2));
    let (d1, d2) = (od(sv)[j1] as int, od(sv)[j2] as int);
    assert(pow10(0) == 1) by (compute);
    let k0 = keys[0];
    let k1 = keys[1];
    assert(k0 == OrderKey { col: 1, desc: true, nulls_first: true });
    assert(k1 == OrderKey { col: 2, desc: false, nulls_first: false });
    assert(r1[1] == Val::Num { coeff: s1, scale: 4 } && r2[1] == Val::Num { coeff: s2, scale: 4 });
    assert(num_sub_coeff(s1, 4, s2, 4) == s1 - s2) by {
        assert(align(s1, 4, 4) == s1 * pow10(0));
        assert(align(s2, 4, 4) == s2 * pow10(0));
    }
    assert(compare(r1[1], r2[1]) == Some(sign(s1 - s2)));
    let c0 = key_cmp(k0, r1, r2);
    assert(c0 == -sign(s1 - s2));
    assert(r1[2] == date32_val(od(sv)[j1]) && r2[2] == date32_val(od(sv)[j2]));
    assert(compare(r1[2], r2[2]) == Some(sign((d1 - 10957) - (d2 - 10957))));
    let c1 = key_cmp(k1, r1, r2);
    assert(c1 == sign(d1 - d2));
    let rest = keys.drop_first();
    assert(rest.len() == 1 && rest[0] == k1);
    assert(rest.drop_first().len() == 0);
    assert(keys_cmp(rest.drop_first(), r1, r2) == 0);
    assert(keys_cmp(rest, r1, r2) == c1);
    assert(keys_cmp(keys, r1, r2) == if c0 != 0 { c0 } else { c1 });
}

/// The selection over group entries `(order, sum, date)`: `sel`, `ss`, `sd` in sorted order.
pub open spec fn sorted_sel(ss: Seq<i128>, sd: Seq<i32>) -> bool {
    &&& ss.len() == sd.len()
    &&& forall|a: int, b: int| 0 <= a < b < ss.len() ==> row_cmp(ss[a] as int, sd[a] as int, ss[b] as int, sd[b] as int) <= 0
}

pub proof fn lemma_row_cmp_facts(s1: int, d1: int, s2: int, d2: int, s3: int, d3: int)
    ensures
        row_cmp(s1, d1, s2, d2) == -row_cmp(s2, d2, s1, d1),
        row_cmp(s1, d1, s2, d2) <= 0 && row_cmp(s2, d2, s3, d3) <= 0 ==> row_cmp(s1, d1, s3, d3) <= 0,
{
}

/// `x` sorts strictly before `y`.
pub fn better(sx: i128, dx: i32, sy: i128, dy: i32) -> (b: bool)
    ensures b == (row_cmp(sx as int, dx as int, sy as int, dy as int) < 0),
    no_unwind
{
    sx > sy || (sx == sy && dx < dy)
}

/// Insert `(x, s, d)` into the sorted selection after every entry that does not sort after it; drop an 11th entry.
fn insert_entry(sel: &mut Vec<usize>, ss: &mut Vec<i128>, sd: &mut Vec<i32>, x: usize, s: i128, d: i32) -> (p: usize)
    requires
        old(sel)@.len() == old(ss)@.len(), old(sel)@.len() == old(sd)@.len(), old(sel)@.len() <= 10,
        sorted_sel(old(ss)@, old(sd)@),
        old(sel)@.len() == 10 ==> row_cmp(s as int, d as int, old(ss)@[9] as int, old(sd)@[9] as int) < 0,
    ensures
        p <= old(sel)@.len(),
        old(sel)@.len() == 10 ==> p <= 9,
        sorted_sel(old(ss)@.insert(p as int, s), old(sd)@.insert(p as int, d)),
        old(sel)@.len() < 10 ==> final(sel)@ == old(sel)@.insert(p as int, x) && final(ss)@ == old(ss)@.insert(p as int, s)
            && final(sd)@ == old(sd)@.insert(p as int, d),
        old(sel)@.len() == 10 ==> final(sel)@ == old(sel)@.insert(p as int, x).drop_last()
            && final(ss)@ == old(ss)@.insert(p as int, s).drop_last() && final(sd)@ == old(sd)@.insert(p as int, d).drop_last(),
{
    let len = sel.len();
    let mut p = len;
    while p > 0 && better(s, d, ss[p - 1], sd[p - 1])
        invariant
            p <= len, len == ss@.len(), len == sd@.len(), ss@ == old(ss)@, sd@ == old(sd)@,
            forall|k: int| p <= k < len ==> #[trigger] row_cmp(s as int, d as int, ss@[k] as int, sd@[k] as int) < 0,
        decreases p,
    {
        p = p - 1;
    }
    let ghost (ss0, sd0) = (ss@, sd@);
    proof {
        assert forall|k: int| 0 <= k < p implies row_cmp(ss0[k] as int, sd0[k] as int, s as int, d as int) <= 0 by {
            lemma_row_cmp_facts(ss0[p - 1] as int, sd0[p - 1] as int, s as int, d as int, 0, 0);
            if k < p - 1 {
                lemma_row_cmp_facts(ss0[k] as int, sd0[k] as int, ss0[p - 1] as int, sd0[p - 1] as int, s as int, d as int);
            }
        }
        let (fs, fd) = (ss0.insert(p as int, s), sd0.insert(p as int, d));
        assert forall|a: int, b: int| 0 <= a < b < fs.len() implies row_cmp(fs[a] as int, fd[a] as int, fs[b] as int, fd[b] as int) <= 0 by {
            if b < p {
                assert(fs[a] == ss0[a] && fd[a] == sd0[a] && fs[b] == ss0[b] && fd[b] == sd0[b]);
            } else if b == p {
                assert(fs[a] == ss0[a] && fd[a] == sd0[a]);
            } else if a == p {
                assert(fs[b] == ss0[b - 1] && fd[b] == sd0[b - 1]);
            } else if a < p {
                assert(fs[a] == ss0[a] && fd[a] == sd0[a] && fs[b] == ss0[b - 1] && fd[b] == sd0[b - 1]);
            } else {
                assert(fs[a] == ss0[a - 1] && fd[a] == sd0[a - 1] && fs[b] == ss0[b - 1] && fd[b] == sd0[b - 1]);
            }
        }
    }
    sel.insert(p, x);
    ss.insert(p, s);
    sd.insert(p, d);
    if sel.len() > 10 {
        sel.pop();
        ss.pop();
        sd.pop();
    }
    p
}


// ------------------------------------------------------------------------------------------------ the selection, generically

/// Items with values: `gs[h]` is `vf(gj[h])`, no item twice.
pub open spec fn items_ok(gj: Seq<usize>, gs: Seq<i128>, vf: spec_fn(int) -> int) -> bool {
    &&& gj.len() == gs.len()
    &&& gj.no_duplicates()
    &&& forall|h: int| 0 <= h < gj.len() ==> #[trigger] gs[h] as int == vf(gj[h] as int)
}

/// The selected entries' sums and dates are `vf` and `df` of the entries.
pub open spec fn sel_okg(vf: spec_fn(int) -> int, df: spec_fn(int) -> int, sel: Seq<usize>, ss: Seq<i128>, sd: Seq<i32>) -> bool {
    forall|k: int| 0 <= k < sel.len() ==> #[trigger] ss[k] as int == vf(sel[k] as int) && sd[k] as int == df(sel[k] as int)
}

/// One instance of `sel_okg`.
pub proof fn lemma_sel_okg_at(vf: spec_fn(int) -> int, df: spec_fn(int) -> int, sel: Seq<usize>, ss: Seq<i128>, sd: Seq<i32>, k: int)
    requires sel_okg(vf, df, sel, ss, sd), 0 <= k < sel.len(),
    ensures ss[k] as int == vf(sel[k] as int), sd[k] as int == df(sel[k] as int),
{
    assert(ss[k] as int == vf(sel[k] as int) && sd[k] as int == df(sel[k] as int));
}

/// `x` is one of the first `g` items of `gj`.
pub open spec fn among(gj: Seq<usize>, g: int, x: usize) -> bool {
    exists|h: int| 0 <= h < g && gj[h] == x
}

/// `sel` (sums `ss`, dates `sd`) is the top 10 (at most) of the processed items `gj` (values `gs`, dates `df`): sorted,
/// processed items only, every other item sorting no earlier than the last, and all items while fewer than 10.
pub open spec fn top_invg(sel: Seq<usize>, ss: Seq<i128>, sd: Seq<i32>, gj: Seq<usize>, gs: Seq<i128>, vf: spec_fn(int) -> int,
    df: spec_fn(int) -> int) -> bool
{
    &&& sel.len() == ss.len() && sel.len() == sd.len()
    &&& sel.len() == if gj.len() <= 10 { gj.len() as int } else { 10 }
    &&& sorted_sel(ss, sd)
    &&& sel.no_duplicates()
    &&& forall|k: int| 0 <= k < sel.len() ==> among(gj, gj.len() as int, #[trigger] sel[k])
    &&& sel_okg(vf, df, sel, ss, sd)
    &&& sel.len() > 0 ==> forall|h: int| 0 <= h < gj.len() && !sel.contains(#[trigger] gj[h]) ==>
            row_cmp(ss.last() as int, sd.last() as int, gs[h] as int, df(gj[h] as int)) <= 0
    &&& sel.len() < 10 ==> forall|h: int| 0 <= h < gj.len() ==> sel.contains(#[trigger] gj[h])
}

pub proof fn lemma_top_empty(vf: spec_fn(int) -> int, df: spec_fn(int) -> int)
    ensures top_invg(Seq::empty(), Seq::empty(), Seq::empty(), Seq::empty(), Seq::empty(), vf, df),
{
}

/// The selection's facts about the items before the new item `x` carry over to `gj.push(x)`; `x` is not selected.
proof fn lemma_step_bridge(sel0: Seq<usize>, ss0: Seq<i128>, sd0: Seq<i32>, gj: Seq<usize>, gs: Seq<i128>, x: usize, s: i128,
    vf: spec_fn(int) -> int, df: spec_fn(int) -> int)
    requires top_invg(sel0, ss0, sd0, gj, gs, vf, df), items_ok(gj.push(x), gs.push(s), vf),
    ensures
        gj.push(x)[gj.len() as int] == x, gs.push(s)[gj.len() as int] == s,
        forall|k: int| 0 <= k < sel0.len() ==> among(gj.push(x), gj.len() as int, #[trigger] sel0[k]),
        sel0.len() > 0 ==> forall|h: int| 0 <= h < gj.len() && !sel0.contains(#[trigger] gj.push(x)[h]) ==>
            row_cmp(ss0.last() as int, sd0.last() as int, gs.push(s)[h] as int, df(gj.push(x)[h] as int)) <= 0,
        sel0.len() < 10 ==> forall|h: int| 0 <= h < gj.len() ==> sel0.contains(#[trigger] gj.push(x)[h]),
        forall|h: int| 0 <= h < gj.len() + 1 ==> #[trigger] gs.push(s)[h] as int == vf(gj.push(x)[h] as int),
        !sel0.contains(x),
{
    let (gj2, gs2, g) = (gj.push(x), gs.push(s), gj.len() as int);
    assert(gj2[g] == x && gs2[g] == s);
    assert forall|h: int| 0 <= h < g implies gj2[h] == gj[h] && gs2[h] == gs[h] by {}
    assert forall|k: int| 0 <= k < sel0.len() implies among(gj2, g, #[trigger] sel0[k]) by {
        let h = choose|h: int| 0 <= h < gj.len() && gj[h] == #[trigger] sel0[k];
        assert(gj2[h] == sel0[k]);
    }
    if sel0.len() > 0 {
        assert forall|h: int| 0 <= h < g && !sel0.contains(#[trigger] gj2[h]) implies
            row_cmp(ss0.last() as int, sd0.last() as int, gs2[h] as int, df(gj2[h] as int)) <= 0 by {
            assert(gj2[h] == gj[h] && gs2[h] == gs[h]);
        }
    }
    if sel0.len() < 10 {
        assert forall|h: int| 0 <= h < g implies sel0.contains(#[trigger] gj2[h]) by {
            assert(gj2[h] == gj[h]);
        }
    }
    assert(!sel0.contains(x)) by {
        if sel0.contains(x) {
            let k = choose|k: int| 0 <= k < sel0.len() && sel0[k] == x;
            let h = choose|h: int| 0 <= h < g && gj2[h] == #[trigger] sel0[k];
            assert(gj2[h] == gj2[g]);
        }
    }
}

/// The new item `(x, s, d)` was inserted at `p` (the 11th entry dropped): the selection is that of `gj.push(x)`.
pub proof fn lemma_step_enter(vf: spec_fn(int) -> int, df: spec_fn(int) -> int, gj: Seq<usize>, gs: Seq<i128>, x: usize, s: i128,
    d: i32, sel0: Seq<usize>, ss0: Seq<i128>, sd0: Seq<i32>, p: int, sel: Seq<usize>, ss: Seq<i128>, sd: Seq<i32>)
    requires
        top_invg(sel0, ss0, sd0, gj, gs, vf, df), items_ok(gj.push(x), gs.push(s), vf), d as int == df(x as int),
        0 <= p <= sel0.len(),
        sel0.len() == 10 ==> p <= 9,
        sorted_sel(ss0.insert(p, s), sd0.insert(p, d)),
        sel0.len() < 10 ==> sel == sel0.insert(p, x) && ss == ss0.insert(p, s) && sd == sd0.insert(p, d),
        sel0.len() == 10 ==> sel == sel0.insert(p, x).drop_last() && ss == ss0.insert(p, s).drop_last()
            && sd == sd0.insert(p, d).drop_last(),
    ensures top_invg(sel, ss, sd, gj.push(x), gs.push(s), vf, df),
{
    let (gj2, gs2, g) = (gj.push(x), gs.push(s), gj.len() as int);
    lemma_step_bridge(sel0, ss0, sd0, gj, gs, x, s, vf, df);
    assert(s as int == vf(x as int)) by {
        assert(gs2[g] as int == vf(gj2[g] as int));
    }
    assert forall|k: int| 0 <= k < sel0.len() implies among(gj2, g, #[trigger] sel0[k]) by {
        let h = choose|h: int| 0 <= h < gj.len() && gj.push(x)[h] == #[trigger] sel0[k];
        assert(gj2[h] == sel0[k]);
    }
    lemma_insert_excluded(vf, df, gj2, gs2, g, x, s, d, sel0, ss0, sd0, p, sel, ss, sd);
    lemma_insert_rest(vf, df, x, s, d, sel0, ss0, sd0, p, sel, ss, sd);
}

/// The new item `(x, s)` does not sort before the last of a full selection: the selection is that of `gj.push(x)`.
pub proof fn lemma_step_skip(vf: spec_fn(int) -> int, df: spec_fn(int) -> int, gj: Seq<usize>, gs: Seq<i128>, x: usize, s: i128,
    sel: Seq<usize>, ss: Seq<i128>, sd: Seq<i32>)
    requires
        top_invg(sel, ss, sd, gj, gs, vf, df), items_ok(gj.push(x), gs.push(s), vf),
        sel.len() == 10, !(row_cmp(s as int, df(x as int), ss[9] as int, sd[9] as int) < 0),
    ensures top_invg(sel, ss, sd, gj.push(x), gs.push(s), vf, df),
{
    let (gj2, gs2, g) = (gj.push(x), gs.push(s), gj.len() as int);
    lemma_step_bridge(sel, ss, sd, gj, gs, x, s, vf, df);
    assert(row_cmp(ss.last() as int, sd.last() as int, s as int, df(x as int)) <= 0) by {
        lemma_row_cmp_facts(s as int, df(x as int), ss[9] as int, sd[9] as int, 0, 0);
    }
    assert forall|h: int| 0 <= h < g + 1 && !sel.contains(#[trigger] gj2[h]) implies
        row_cmp(ss.last() as int, sd.last() as int, gs2[h] as int, df(gj2[h] as int)) <= 0 by {}
    assert forall|k: int| 0 <= k < sel.len() implies among(gj2, g + 1, #[trigger] sel[k]) by {
        let h = choose|h: int| 0 <= h < g && gj2[h] == #[trigger] sel[k];
    }
}

/// Ten distinct items, each sorting no later than `(wv, wd)`, are processed: the selection is full and its last entry
/// sorts no later than `(wv, wd)`.
pub proof fn lemma_top_pigeon(sel: Seq<usize>, ss: Seq<i128>, sd: Seq<i32>, gj: Seq<usize>, gs: Seq<i128>, vf: spec_fn(int) -> int,
    df: spec_fn(int) -> int, lw: Seq<usize>, wv: int, wd: int)
    requires
        top_invg(sel, ss, sd, gj, gs, vf, df), items_ok(gj, gs, vf),
        lw.len() == 10, lw.no_duplicates(),
        forall|k: int| 0 <= k < 10 ==> gj.contains(#[trigger] lw[k]) && row_cmp(vf(lw[k] as int), df(lw[k] as int), wv, wd) <= 0,
    ensures
        sel.len() == 10,
        row_cmp(ss.last() as int, sd.last() as int, wv, wd) <= 0,
{
    lw.unique_seq_to_set();
    gj.unique_seq_to_set();
    assert(lw.to_set().subset_of(gj.to_set())) by {
        assert forall|e: usize| lw.to_set().contains(e) implies gj.to_set().contains(e) by {
            let k = choose|k: int| 0 <= k < lw.len() && lw[k] == e;
            assert(gj.contains(lw[k]));
        }
    }
    vstd::set_lib::lemma_len_subset(lw.to_set(), gj.to_set());
    assert(gj.len() >= 10);
    if exists|k: int| 0 <= k < 10 && !sel.contains(#[trigger] lw[k]) {
        let k = choose|k: int| 0 <= k < 10 && !sel.contains(#[trigger] lw[k]);
        assert(gj.contains(lw[k]));
        let h = choose|h: int| 0 <= h < gj.len() && gj[h] == lw[k];
        assert(!sel.contains(gj[h]));
        assert(row_cmp(ss.last() as int, sd.last() as int, gs[h] as int, df(gj[h] as int)) <= 0);
        assert(gs[h] as int == vf(gj[h] as int));
        lemma_row_cmp_facts(ss.last() as int, sd.last() as int, vf(lw[k] as int), df(lw[k] as int), wv, wd);
    } else {
        sel.unique_seq_to_set();
        assert(lw.to_set().subset_of(sel.to_set())) by {
            assert forall|e: usize| lw.to_set().contains(e) implies sel.to_set().contains(e) by {
                let k = choose|k: int| 0 <= k < lw.len() && lw[k] == e;
                assert(sel.contains(lw[k]));
            }
        }
        vstd::set_lib::lemma_subset_equality(lw.to_set(), sel.to_set());
        let last = sel.len() - 1;
        assert(sel.to_set().contains(sel[last]));
        assert(lw.to_set().contains(sel[last]));
        let k = choose|k: int| 0 <= k < lw.len() && lw[k] == sel[last];
        assert(ss[last] as int == vf(sel[last] as int) && sd[last] as int == df(sel[last] as int));
    }
}

/// The other facts of the selection after an insertion: sorted, no duplicates, sums and dates of the entries.
proof fn lemma_insert_rest(vf: spec_fn(int) -> int, df: spec_fn(int) -> int, x: usize, s: i128, d: i32, sel0: Seq<usize>, ss0: Seq<i128>,
    sd0: Seq<i32>, p: int, sel: Seq<usize>, ss: Seq<i128>, sd: Seq<i32>)
    requires
        sel0.len() == ss0.len(), sel0.len() == sd0.len(), sel0.len() <= 10, 0 <= p <= sel0.len(),
        sel0.no_duplicates(), !sel0.contains(x),
        s as int == vf(x as int), d as int == df(x as int),
        sel_okg(vf, df, sel0, ss0, sd0),
        sorted_sel(ss0.insert(p, s), sd0.insert(p, d)),
        sel0.len() < 10 ==> sel == sel0.insert(p, x) && ss == ss0.insert(p, s) && sd == sd0.insert(p, d),
        sel0.len() == 10 ==> sel == sel0.insert(p, x).drop_last() && ss == ss0.insert(p, s).drop_last()
            && sd == sd0.insert(p, d).drop_last(),
    ensures
        sel.len() == ss.len(), sel.len() == sd.len(),
        sel.len() == if sel0.len() < 10 { sel0.len() + 1 } else { 10 },
        sorted_sel(ss, sd),
        sel.no_duplicates(),
        sel_okg(vf, df, sel, ss, sd),
{
    let (fj, fs, fd) = (sel0.insert(p, x), ss0.insert(p, s), sd0.insert(p, d));
    assert forall|k: int| 0 <= k < fj.len() implies #[trigger] fs[k] as int == vf(fj[k] as int) && fd[k] as int == df(fj[k] as int) by {
        if k < p {
            assert(fj[k] == sel0[k] && fs[k] == ss0[k] && fd[k] == sd0[k]);
        } else if k > p {
            assert(fj[k] == sel0[k - 1] && fs[k] == ss0[k - 1] && fd[k] == sd0[k - 1]);
        }
    }
    assert(fj.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < fj.len() && 0 <= b < fj.len() && a != b implies fj[a] != fj[b] by {
            if a == p {
                let b0 = if b < p { b } else { b - 1 };
                assert(fj[b] == sel0[b0]);
                assert(sel0.contains(sel0[b0]));
            } else if b == p {
                let a0 = if a < p { a } else { a - 1 };
                assert(fj[a] == sel0[a0]);
                assert(sel0.contains(sel0[a0]));
            } else {
                let a0 = if a < p { a } else { a - 1 };
                let b0 = if b < p { b } else { b - 1 };
                assert(fj[a] == sel0[a0] && fj[b] == sel0[b0]);
            }
        }
    }
    if sel0.len() == 10 {
        assert forall|a: int, b: int| 0 <= a < b < ss.len() implies row_cmp(ss[a] as int, sd[a] as int, ss[b] as int, sd[b] as int) <= 0 by {
            assert(ss[a] == fs[a] && sd[a] == fd[a] && ss[b] == fs[b] && sd[b] == fd[b]);
        }
        assert forall|a: int, b: int| 0 <= a < sel.len() && 0 <= b < sel.len() && a != b implies sel[a] != sel[b] by {
            assert(sel[a] == fj[a] && sel[b] == fj[b]);
        }
        assert forall|k: int| 0 <= k < sel.len() implies #[trigger] ss[k] as int == vf(sel[k] as int) && sd[k] as int == df(sel[k] as int) by {
            assert(sel[k] == fj[k] && ss[k] == fs[k] && sd[k] == fd[k]);
        }
        assert(sel_okg(vf, df, sel, ss, sd));
    } else {
        assert(sel == fj && ss == fs && sd == fd);
        assert(sel_okg(vf, df, fj, fs, fd));
        assert(sel_okg(vf, df, sel, ss, sd));
    }
}

/// After inserting entry `x` (item `g`) at `p` into a full or non-full selection, and dropping the 11th entry:
/// every item not selected sorts no earlier than the new last entry, every selected entry is a processed item, and
/// while fewer than 10 are selected all processed items are.
proof fn lemma_insert_excluded(vf: spec_fn(int) -> int, df: spec_fn(int) -> int, gj: Seq<usize>, gs: Seq<i128>, g: int, x: usize, s: i128,
    d: i32, sel0: Seq<usize>, ss0: Seq<i128>, sd0: Seq<i32>, p: int, sel: Seq<usize>, ss: Seq<i128>, sd: Seq<i32>)
    requires
        forall|h: int| 0 <= h < gj.len() ==> #[trigger] gs[h] as int == vf(gj[h] as int),
        sel_okg(vf, df, sel0, ss0, sd0),
        0 <= g < gj.len(), gj.len() == gs.len(), gj[g] == x, gs[g] == s, d as int == df(x as int),
        gj.no_duplicates(),
        sel0.len() == ss0.len(), sel0.len() == sd0.len(), sel0.len() <= 10, sel0.len() == if g <= 10 { g } else { 10 },
        0 <= p <= sel0.len(),
        sel0.len() == 10 ==> p <= 9,
        sorted_sel(ss0.insert(p, s), sd0.insert(p, d)),
        forall|k: int| 0 <= k < sel0.len() ==> among(gj, g, #[trigger] sel0[k]),
        sel0.len() > 0 ==> forall|h: int| 0 <= h < g && !sel0.contains(#[trigger] gj[h]) ==>
            row_cmp(ss0.last() as int, sd0.last() as int, gs[h] as int, df(gj[h] as int)) <= 0,
        sel0.len() < 10 ==> forall|h: int| 0 <= h < g ==> sel0.contains(#[trigger] gj[h]),
        sel0.len() < 10 ==> sel == sel0.insert(p, x) && ss == ss0.insert(p, s) && sd == sd0.insert(p, d),
        sel0.len() == 10 ==> sel == sel0.insert(p, x).drop_last() && ss == ss0.insert(p, s).drop_last()
            && sd == sd0.insert(p, d).drop_last(),
    ensures
        sel.len() > 0 ==> forall|h: int| 0 <= h < g + 1 && !sel.contains(#[trigger] gj[h]) ==>
            row_cmp(ss.last() as int, sd.last() as int, gs[h] as int, df(gj[h] as int)) <= 0,
        forall|k: int| 0 <= k < sel.len() ==> among(gj, g + 1, #[trigger] sel[k]),
        sel.len() < 10 ==> forall|h: int| 0 <= h < g + 1 ==> sel.contains(#[trigger] gj[h]),
{
    let fj = sel0.insert(p, x);
    let fs = ss0.insert(p, s);
    let fd = sd0.insert(p, d);
    // every entry of the full list is a processed item
    assert forall|t: int| 0 <= t < fj.len() implies among(gj, g + 1, #[trigger] fj[t]) by {
        if t == p {
            assert(gj[g] == fj[t]);
        } else {
            let t0 = if t < p { t } else { t - 1 };
            assert(fj[t] == sel0[t0]);
            let h = choose|h: int| 0 <= h < g && gj[h] == #[trigger] sel0[t0];
        }
    }
    assert forall|k: int| 0 <= k < sel.len() implies among(gj, g + 1, #[trigger] sel[k]) by {
        assert(sel[k] == fj[k]);
    }
    // the new entry is selected
    assert(sel0.len() < 10 ==> sel[p] == x);
    assert(sel0.len() == 10 ==> sel[p] == x);
    if sel0.len() < 10 {
        assert forall|h: int| 0 <= h < g + 1 implies sel.contains(#[trigger] gj[h]) by {
            if h == g {
                assert(sel[p] == gj[h]);
            } else {
                assert(sel0.contains(gj[h]));
                let k = choose|k: int| 0 <= k < sel0.len() && sel0[k] == gj[h];
                let k2 = if k < p { k } else { k + 1 };
                assert(sel[k2] == gj[h]);
            }
        }
    } else {
        // full: the old last entry is the dropped 11th
        assert(fj[10] == sel0[9] && fs[10] == ss0[9] && fd[10] == sd0[9]);
        assert(ss.last() == fs[9] && sd.last() == fd[9]);
        assert(row_cmp(fs[9] as int, fd[9] as int, fs[10] as int, fd[10] as int) <= 0);
        assert forall|h: int| 0 <= h < g + 1 && !sel.contains(#[trigger] gj[h]) implies
            row_cmp(ss.last() as int, sd.last() as int, gs[h] as int, df(gj[h] as int)) <= 0 by {
            if h == g {
                assert(sel[p] == gj[h]);
                assert(false);
            } else if gj[h] == sel0[9] {
                let h9 = choose|h9: int| 0 <= h9 < g && gj[h9] == #[trigger] sel0[9];
                if h9 != h {
                    assert(gj[h9] != gj[h]);
                }
                assert(ss0[9] as int == vf(sel0[9] as int) && sd0[9] as int == df(sel0[9] as int));
                assert(gs[h] as int == ss0[9] as int);
            } else {
                assert(!sel0.contains(gj[h])) by {
                    if sel0.contains(gj[h]) {
                        let k = choose|k: int| 0 <= k < sel0.len() && sel0[k] == gj[h];
                        assert(k != 9);
                        let k2 = if k < p { k } else { k + 1 };
                        assert(k2 < 10);
                        assert(sel[k2] == gj[h]);
                    }
                }
                lemma_row_cmp_facts(fs[9] as int, fd[9] as int, ss0[9] as int, sd0[9] as int, gs[h] as int, df(gj[h] as int));
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ fixed capacity (workers)

/// A selection of at most 10 entries in preallocated buffers (no allocation): the first `k` slots. Each entry is an
/// item `ti`, its sum `ts`, its date `td` and a tag `to` the caller attaches to the item (its order, for the scan).
pub struct FixTop {
    pub ti: Vec<usize>,
    pub ts: Vec<i128>,
    pub td: Vec<i32>,
    pub to: Vec<usize>,
    pub k: usize,
}

pub open spec fn fix_wf(t: FixTop) -> bool {
    &&& t.ti@.len() == 10 && t.ts@.len() == 10 && t.td@.len() == 10 && t.to@.len() == 10
    &&& t.k <= 10
}

/// Every selected entry's tag is `of` of its item.
pub open spec fn fix_tags(t: FixTop, of: spec_fn(int) -> int) -> bool {
    forall|q: int| 0 <= q < t.k ==> #[trigger] t.to@[q] as int == of(t.ti@[q] as int)
}

/// Tags stay valid under another tag function that agrees on the selected items.
pub proof fn lemma_tags_congr(t: FixTop, of: spec_fn(int) -> int, of2: spec_fn(int) -> int)
    requires
        fix_wf(t), fix_tags(t, of),
        forall|q: int| 0 <= q < t.k ==> of(#[trigger] t.ti@[q] as int) == of2(t.ti@[q] as int),
    ensures fix_tags(t, of2),
{
    assert forall|q: int| 0 <= q < t.k implies #[trigger] t.to@[q] as int == of2(t.ti@[q] as int) by {
        assert(t.to@[q] as int == of(t.ti@[q] as int));
    }
}

/// A selection over items `gj` stays one under value and date functions that agree on those items.
pub proof fn lemma_fix_congr(t: FixTop, gj: Seq<usize>, gs: Seq<i128>, vf: spec_fn(int) -> int, df: spec_fn(int) -> int,
    vf2: spec_fn(int) -> int, df2: spec_fn(int) -> int)
    requires
        fix_inv(t, gj, gs, vf, df),
        forall|h: int| 0 <= h < gj.len() ==> vf(#[trigger] gj[h] as int) == vf2(gj[h] as int) && df(gj[h] as int) == df2(gj[h] as int),
    ensures fix_inv(t, gj, gs, vf2, df2),
{
    let (sel, ss, sd) = (fsel(t), fss(t), fsd(t));
    assert(sel_okg(vf, df, sel, ss, sd));
    assert forall|k: int| 0 <= k < sel.len() implies #[trigger] ss[k] as int == vf2(sel[k] as int) && sd[k] as int == df2(sel[k] as int) by {
        assert(among(gj, gj.len() as int, sel[k]));
        let h = choose|h: int| 0 <= h < gj.len() && gj[h] == sel[k];
        assert(vf(gj[h] as int) == vf2(gj[h] as int) && df(gj[h] as int) == df2(gj[h] as int));
        lemma_sel_okg_at(vf, df, sel, ss, sd, k);
    }
    assert(sel_okg(vf2, df2, sel, ss, sd));
    if sel.len() > 0 {
        assert forall|h: int| 0 <= h < gj.len() && !sel.contains(#[trigger] gj[h]) implies
            row_cmp(ss.last() as int, sd.last() as int, gs[h] as int, df2(gj[h] as int)) <= 0 by {
            assert(df(gj[h] as int) == df2(gj[h] as int));
        }
    }
}

pub open spec fn fsel(t: FixTop) -> Seq<usize> { t.ti@.subrange(0, t.k as int) }
pub open spec fn fss(t: FixTop) -> Seq<i128> { t.ts@.subrange(0, t.k as int) }
pub open spec fn fsd(t: FixTop) -> Seq<i32> { t.td@.subrange(0, t.k as int) }
pub open spec fn fso(t: FixTop) -> Seq<usize> { t.to@.subrange(0, t.k as int) }

/// Insert `(x, s, d)` after every entry that does not sort after it; a full selection drops its 10th entry.
fn fix_insert(t: &mut FixTop, x: usize, s: i128, d: i32, o: usize) -> (p: usize)
    requires
        fix_wf(*old(t)),
        sorted_sel(fss(*old(t)), fsd(*old(t))),
        old(t).k == 10 ==> row_cmp(s as int, d as int, old(t).ts@[9] as int, old(t).td@[9] as int) < 0,
    ensures
        fix_wf(*final(t)),
        p <= old(t).k,
        old(t).k == 10 ==> p <= 9,
        sorted_sel(fss(*old(t)).insert(p as int, s), fsd(*old(t)).insert(p as int, d)),
        old(t).k < 10 ==> fsel(*final(t)) == fsel(*old(t)).insert(p as int, x) && fss(*final(t)) == fss(*old(t)).insert(p as int, s)
            && fsd(*final(t)) == fsd(*old(t)).insert(p as int, d) && fso(*final(t)) == fso(*old(t)).insert(p as int, o),
        old(t).k == 10 ==> fsel(*final(t)) == fsel(*old(t)).insert(p as int, x).drop_last()
            && fss(*final(t)) == fss(*old(t)).insert(p as int, s).drop_last()
            && fsd(*final(t)) == fsd(*old(t)).insert(p as int, d).drop_last()
            && fso(*final(t)) == fso(*old(t)).insert(p as int, o).drop_last(),
    no_unwind
{
    let k = t.k;
    let ghost (sel0, ss0, sd0, so0) = (fsel(*t), fss(*t), fsd(*t), fso(*t));
    let ghost (ti0, ts0, td0, to0) = (t.ti@, t.ts@, t.td@, t.to@);
    let mut p = k;
    while p > 0 && better(s, d, t.ts[p - 1], t.td[p - 1])
        invariant
            p <= k, k <= 10, fix_wf(*t), t.ti@ == ti0, t.ts@ == ts0, t.td@ == td0, t.to@ == to0, t.k == k,
            forall|q: int| p <= q < k ==> #[trigger] row_cmp(s as int, d as int, ts0[q] as int, td0[q] as int) < 0,
        decreases p,
    {
        p = p - 1;
    }
    proof {
        assert forall|q: int| 0 <= q < p implies row_cmp(ss0[q] as int, sd0[q] as int, s as int, d as int) <= 0 by {
            assert(ss0[p - 1] == ts0[p - 1] && sd0[p - 1] == td0[p - 1]);
            lemma_row_cmp_facts(ss0[p - 1] as int, sd0[p - 1] as int, s as int, d as int, 0, 0);
            if q < p - 1 {
                lemma_row_cmp_facts(ss0[q] as int, sd0[q] as int, ss0[p - 1] as int, sd0[p - 1] as int, s as int, d as int);
            }
        }
        assert forall|q: int| p <= q < k implies row_cmp(s as int, d as int, ss0[q] as int, sd0[q] as int) < 0 by {
            assert(ss0[q] == ts0[q] && sd0[q] == td0[q]);
        }
        let (fs, fd) = (ss0.insert(p as int, s), sd0.insert(p as int, d));
        assert forall|a: int, b: int| 0 <= a < b < fs.len() implies row_cmp(fs[a] as int, fd[a] as int, fs[b] as int, fd[b] as int) <= 0 by {
            if b < p {
                assert(fs[a] == ss0[a] && fd[a] == sd0[a] && fs[b] == ss0[b] && fd[b] == sd0[b]);
            } else if b == p {
                assert(fs[a] == ss0[a] && fd[a] == sd0[a]);
            } else if a == p {
                assert(fs[b] == ss0[b - 1] && fd[b] == sd0[b - 1]);
            } else if a < p {
                assert(fs[a] == ss0[a] && fd[a] == sd0[a] && fs[b] == ss0[b - 1] && fd[b] == sd0[b - 1]);
            } else {
                assert(fs[a] == ss0[a - 1] && fd[a] == sd0[a - 1] && fs[b] == ss0[b - 1] && fd[b] == sd0[b - 1]);
            }
        }
    }
    // shift the entries p..top up by one (the 10th of a full selection drops out)
    let top = if k < 10 { k } else { 9 };
    let mut q = top;
    while q > p
        invariant
            p <= q <= top, top < 10, top == if k < 10 { k } else { 9 }, p <= k, k <= 10, k == 10 ==> p <= 9,
            fix_wf(*t), t.k == k,
            forall|i: int| q < i <= top ==> #[trigger] t.ti@[i] == ti0[i - 1],
            forall|i: int| q < i <= top ==> #[trigger] t.ts@[i] == ts0[i - 1],
            forall|i: int| q < i <= top ==> #[trigger] t.td@[i] == td0[i - 1],
            forall|i: int| q < i <= top ==> #[trigger] t.to@[i] == to0[i - 1],
            forall|i: int| 0 <= i <= q ==> #[trigger] t.ti@[i] == ti0[i],
            forall|i: int| 0 <= i <= q ==> #[trigger] t.ts@[i] == ts0[i],
            forall|i: int| 0 <= i <= q ==> #[trigger] t.td@[i] == td0[i],
            forall|i: int| 0 <= i <= q ==> #[trigger] t.to@[i] == to0[i],
        decreases q,
    {
        let a = t.ti[q - 1];
        let b = t.ts[q - 1];
        let c = t.td[q - 1];
        let e = t.to[q - 1];
        assert(a == ti0[q - 1] && b == ts0[q - 1] && c == td0[q - 1] && e == to0[q - 1]);
        t.ti[q] = a;
        t.ts[q] = b;
        t.td[q] = c;
        t.to[q] = e;
        q = q - 1;
    }
    t.ti[p] = x;
    t.ts[p] = s;
    t.td[p] = d;
    t.to[p] = o;
    t.k = if k < 10 { k + 1 } else { 10 };
    proof {
        let k2 = t.k as int;
        let (fj, fs, fd) = (sel0.insert(p as int, x), ss0.insert(p as int, s), sd0.insert(p as int, d));
        assert forall|i: int| 0 <= i < k2 implies #[trigger] fsel(*t)[i] == fj[i] by {
            if i < p {
                assert(t.ti@[i] == ti0[i]);
            } else if i > p {
                assert(i <= top);
                assert(t.ti@[i] == ti0[i - 1]);
            }
        }
        assert forall|i: int| 0 <= i < k2 implies #[trigger] fss(*t)[i] == fs[i] by {
            if i < p {
                assert(t.ts@[i] == ts0[i]);
            } else if i > p {
                assert(i <= top);
                assert(t.ts@[i] == ts0[i - 1]);
            }
        }
        assert forall|i: int| 0 <= i < k2 implies #[trigger] fsd(*t)[i] == fd[i] by {
            if i < p {
                assert(t.td@[i] == td0[i]);
            } else if i > p {
                assert(i <= top);
                assert(t.td@[i] == td0[i - 1]);
            }
        }
        let fo = so0.insert(p as int, o);
        assert forall|i: int| 0 <= i < k2 implies #[trigger] fso(*t)[i] == fo[i] by {
            if i < p {
                assert(t.to@[i] == to0[i]);
            } else if i > p {
                assert(i <= top);
                assert(t.to@[i] == to0[i - 1]);
            }
        }
        if k < 10 {
            assert(fsel(*t) =~= fj);
            assert(fss(*t) =~= fs);
            assert(fsd(*t) =~= fd);
            assert(fso(*t) =~= fo);
        } else {
            assert(fsel(*t) =~= fj.drop_last());
            assert(fss(*t) =~= fs.drop_last());
            assert(fsd(*t) =~= fd.drop_last());
            assert(fso(*t) =~= fo.drop_last());
        }
    }
    p
}

/// The fixed selection as a top over items: `top_invg` of its first `k` slots.
pub open spec fn fix_inv(t: FixTop, gj: Seq<usize>, gs: Seq<i128>, vf: spec_fn(int) -> int, df: spec_fn(int) -> int) -> bool {
    &&& fix_wf(t)
    &&& top_invg(fsel(t), fss(t), fsd(t), gj, gs, vf, df)
}

/// An insertion keeps every entry with its tag.
proof fn lemma_insert_tags(t0: FixTop, t1: FixTop, x: usize, o: usize, p: int, of: spec_fn(int) -> int)
    requires
        fix_wf(t0), fix_wf(t1), fix_tags(t0, of), of(x as int) == o as int, 0 <= p <= t0.k,
        t0.k < 10 ==> fsel(t1) == fsel(t0).insert(p, x) && fso(t1) == fso(t0).insert(p, o),
        t0.k == 10 ==> p <= 9 && fsel(t1) == fsel(t0).insert(p, x).drop_last() && fso(t1) == fso(t0).insert(p, o).drop_last(),
    ensures fix_tags(t1, of),
{
    let (fj, fo) = (fsel(t0).insert(p, x), fso(t0).insert(p, o));
    assert forall|q: int| 0 <= q < t1.k implies #[trigger] t1.to@[q] as int == of(t1.ti@[q] as int) by {
        assert(fsel(t1)[q] == t1.ti@[q] && fso(t1)[q] == t1.to@[q]);
        assert(fsel(t1)[q] == fj[q] && fso(t1)[q] == fo[q]);
        if q < p {
            assert(fj[q] == t0.ti@[q] && fo[q] == t0.to@[q]);
        } else if q > p {
            assert(fj[q] == t0.ti@[q - 1] && fo[q] == t0.to@[q - 1]);
        }
    }
}

/// Process one more item `x` with value `s`; its date is `odate[m]`, read only when the value does not decide.
pub fn fix_step(t: &mut FixTop, x: usize, s: i128, odate: &[i32], m: usize, o: usize, Ghost(gj): Ghost<Seq<usize>>,
    Ghost(gs): Ghost<Seq<i128>>, Ghost(vf): Ghost<spec_fn(int) -> int>, Ghost(df): Ghost<spec_fn(int) -> int>,
    Ghost(of): Ghost<spec_fn(int) -> int>, Ghost(nod): Ghost<int>)
    requires
        fix_inv(*old(t), gj, gs, vf, df),
        fix_tags(*old(t), of), of(x as int) == o as int,
        items_ok(gj.push(x), gs.push(s), vf),
        nod == odate@.len(), m < nod, df(x as int) == odate@[m as int] as int,
    ensures fix_inv(*final(t), gj.push(x), gs.push(s), vf, df), fix_tags(*final(t), of),
    no_unwind
{
    let k = t.k;
    let enters = if k < 10 {
        true
    } else if s < t.ts[9] {
        false
    } else {
        better(s, odate[m], t.ts[9], t.td[9])
    };
    let ghost (sel0, ss0, sd0) = (fsel(*t), fss(*t), fsd(*t));
    proof {
        assert(k < 10 ==> sel0.len() < 10);
        if k == 10 {
            assert(ss0[9] == t.ts@[9] && sd0[9] == t.td@[9]);
            assert(enters == (row_cmp(s as int, df(x as int), ss0[9] as int, sd0[9] as int) < 0));
        }
    }
    let ghost t0 = *t;
    if enters {
        let d = odate[m];
        let p = fix_insert(t, x, s, d, o);
        proof {
            lemma_step_enter(vf, df, gj, gs, x, s, d, sel0, ss0, sd0, p as int, fsel(*t), fss(*t), fsd(*t));
            lemma_insert_tags(t0, *t, x, o, p as int, of);
        }
    } else {
        proof {
            lemma_step_skip(vf, df, gj, gs, x, s, sel0, ss0, sd0);
        }
    }
}

// ------------------------------------------------------------------------------------------------ the groups' top 10

/// The final sum of order `j` (over all lineitem rows) and its date.
pub open spec fn fin(sv: StoresView, ps: Seq<Literal>) -> spec_fn(int) -> int {
    |j: int| order_sum(sv, seg_of(ps), dl_of(ps), j, 0, n_l(sv))
}

pub open spec fn odf(sv: StoresView) -> spec_fn(int) -> int {
    |j: int| od(sv)[j] as int
}

/// Groups ready for the selection: distinct orders with their sums over all lineitem rows.
pub open spec fn groups_final(gj: Seq<usize>, gs: Seq<i128>, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& items_ok(gj, gs, fin(sv, ps))
    &&& n_o(sv) == od(sv).len()
    &&& forall|g: int| 0 <= g < gj.len() ==> (#[trigger] gj[g] as int) < n_o(sv)
}

/// The selection so far: orders `sel` with sums `ss` and dates `sd`, sorted.
pub struct Top {
    pub sel: Vec<usize>,
    pub ss: Vec<i128>,
    pub sd: Vec<i32>,
}

/// `t` is the top 10 (at most) of the processed groups `gj`/`gs`.
pub open spec fn top_inv(t: Top, gj: Seq<usize>, gs: Seq<i128>, sv: StoresView, ps: Seq<Literal>) -> bool {
    top_invg(t.sel@, t.ss@, t.sd@, gj, gs, fin(sv, ps), odf(sv))
}

/// The result of the selection: the selected orders and their sums, the top rows of the groups `gj`.
pub open spec fn top_out_ok(sel: Seq<usize>, ss: Seq<i128>, gj: Seq<usize>, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& sel.len() == ss.len()
    &&& forall|k: int| 0 <= k < sel.len() ==> #[trigger] ss[k] as int == order_sum(sv, seg_of(ps), dl_of(ps), sel[k] as int, 0, n_l(sv))
    &&& forall|k: int| 0 <= k < sel.len() ==> (#[trigger] sel[k] as int) < n_o(sv)
    &&& top_rows_ok(sv, ps, gj.map_values(|x: usize| x as int), sel.map_values(|x: usize| x as int))
}

pub fn top_new(Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (t: Top)
    ensures top_inv(t, Seq::empty(), Seq::empty(), sv, ps),
{
    proof {
        lemma_top_empty(fin(sv, ps), odf(sv));
    }
    Top { sel: Vec::new(), ss: Vec::new(), sd: Vec::new() }
}

/// Process one more group `(x, s)` after the groups `gj`/`gs`.
pub fn top_step(t: &mut Top, x: usize, s: i128, odate: &[i32], Ghost(gj): Ghost<Seq<usize>>, Ghost(gs): Ghost<Seq<i128>>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    requires
        top_inv(*old(t), gj, gs, sv, ps),
        groups_final(gj.push(x), gs.push(s), sv, ps),
        odate@ == od(sv),
    ensures top_inv(*final(t), gj.push(x), gs.push(s), sv, ps),
{
    let ghost (vf, df) = (fin(sv, ps), odf(sv));
    proof {
        assert(gj.push(x)[gj.len() as int] == x);
        assert((x as int) < n_o(sv));
    }
    let len = t.sel.len();
    // the date is read only when the sum does not already decide (most groups fall below the 10th sum)
    let enters = if len < 10 {
        true
    } else if s < t.ss[len - 1] {
        false
    } else {
        better(s, odate[x], t.ss[len - 1], t.sd[len - 1])
    };
    let ghost (sel0, ss0, sd0) = (t.sel@, t.ss@, t.sd@);
    proof {
        if len == 10 {
            assert(enters == (row_cmp(s as int, df(x as int), ss0[9] as int, sd0[9] as int) < 0));
        }
    }
    if enters {
        let d = odate[x];
        let p = insert_entry(&mut t.sel, &mut t.ss, &mut t.sd, x, s, d);
        proof {
            lemma_step_enter(vf, df, gj, gs, x, s, d, sel0, ss0, sd0, p as int, t.sel@, t.ss@, t.sd@);
        }
    } else {
        proof {
            lemma_step_skip(vf, df, gj, gs, x, s, sel0, ss0, sd0);
        }
    }
}

/// The selection over all groups is the result.
pub fn top_done(t: Top, Ghost(gj): Ghost<Seq<usize>>, Ghost(gs): Ghost<Seq<i128>>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: (Vec<usize>, Vec<i128>))
    requires top_inv(t, gj, gs, sv, ps), groups_final(gj, gs, sv, ps),
    ensures top_out_ok(r.0@, r.1@, gj, sv, ps),
{
    proof {
        lemma_top_final(sv, ps, gj, gs, t.sel@, t.ss@, t.sd@);
    }
    (t.sel, t.ss)
}

/// The top 10 entries (at most) of the groups `gj`/`gs`: the selected orders `sel` and their sums.
pub fn top10(gj: &Vec<usize>, gs: &Vec<i128>, odate: &'static [i32], Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: (Vec<usize>, Vec<i128>))
    requires groups_final(gj@, gs@, sv, ps), odate@ == od(sv),
    ensures top_out_ok(r.0@, r.1@, gj@, sv, ps),
{
    let mut t = top_new(Ghost(sv), Ghost(ps));
    let n = gj.len();
    let mut g: usize = 0;
    while g < n
        invariant
            n == gj@.len(), g <= n, odate@ == od(sv),
            groups_final(gj@, gs@, sv, ps),
            top_inv(t, gj@.subrange(0, g as int), gs@.subrange(0, g as int), sv, ps),
        decreases n - g,
    {
        let ghost (pj, ps_) = (gj@.subrange(0, g as int), gs@.subrange(0, g as int));
        proof {
            assert(gj@.subrange(0, g + 1) =~= pj.push(gj@[g as int]));
            assert(gs@.subrange(0, g + 1) =~= ps_.push(gs@[g as int]));
            lemma_groups_prefix(gj@, gs@, sv, ps, g + 1);
        }
        top_step(&mut t, gj[g], gs[g], odate, Ghost(pj), Ghost(ps_), Ghost(sv), Ghost(ps));
        g = g + 1;
    }
    assert(gj@.subrange(0, n as int) =~= gj@);
    assert(gs@.subrange(0, n as int) =~= gs@);
    top_done(t, Ghost(gj@), Ghost(gs@), Ghost(sv), Ghost(ps))
}

/// A prefix of final groups is final.
proof fn lemma_groups_prefix(gj: Seq<usize>, gs: Seq<i128>, sv: StoresView, ps: Seq<Literal>, g: int)
    requires groups_final(gj, gs, sv, ps), 0 <= g <= gj.len(),
    ensures groups_final(gj.subrange(0, g), gs.subrange(0, g), sv, ps),
{
    let (qj, qs) = (gj.subrange(0, g), gs.subrange(0, g));
    assert forall|a: int, b: int| 0 <= a < qj.len() && 0 <= b < qj.len() && a != b implies qj[a] != qj[b] by {
        assert(qj[a] == gj[a] && qj[b] == gj[b]);
    }
    assert forall|a: int| 0 <= a < qj.len() implies (#[trigger] qj[a] as int) < n_o(sv) by {
        assert(qj[a] == gj[a]);
    }
    assert forall|a: int| 0 <= a < qj.len() implies #[trigger] qs[a] as int == fin(sv, ps)(qj[a] as int) by {
        assert(qj[a] == gj[a] && qs[a] == gs[a]);
    }
}

/// The selection's invariant over all groups gives `top_out_ok`.
proof fn lemma_top_final(sv: StoresView, ps: Seq<Literal>, gj: Seq<usize>, gs: Seq<i128>, sel: Seq<usize>, ss: Seq<i128>, sd: Seq<i32>)
    requires top_invg(sel, ss, sd, gj, gs, fin(sv, ps), odf(sv)), groups_final(gj, gs, sv, ps),
    ensures top_out_ok(sel, ss, gj, sv, ps),
{
    assert forall|k: int| 0 <= k < sel.len() implies gj.contains(#[trigger] sel[k]) && (sel[k] as int) < n_o(sv) by {
        let h = choose|h: int| 0 <= h < gj.len() && gj[h] == #[trigger] sel[k];
        assert(gj[h] == sel[k]);
    }
    assert forall|k: int| 0 <= k < sel.len() implies #[trigger] ss[k] as int == order_sum(sv, seg_of(ps), dl_of(ps), sel[k] as int, 0, n_l(sv))
        && sd[k] == od(sv)[sel[k] as int] by {
        assert(ss[k] as int == fin(sv, ps)(sel[k] as int) && sd[k] as int == odf(sv)(sel[k] as int));
    }
    assert forall|h: int| 0 <= h < gj.len() implies #[trigger] gs[h] as int == order_sum(sv, seg_of(ps), dl_of(ps), gj[h] as int, 0, n_l(sv)) by {
        assert(gs[h] as int == fin(sv, ps)(gj[h] as int));
    }
    if sel.len() > 0 {
        assert forall|h: int| 0 <= h < gj.len() && !sel.contains(#[trigger] gj[h]) implies
            row_cmp(ss.last() as int, sd.last() as int, gs[h] as int, od(sv)[gj[h] as int] as int) <= 0 by {
            assert(odf(sv)(gj[h] as int) == od(sv)[gj[h] as int] as int);
        }
    }
    lemma_top_rows(sv, ps, gj, gs, sel, ss, sd);
}

/// The selection's invariant at the end is `top_rows_ok`.
proof fn lemma_top_rows(sv: StoresView, ps: Seq<Literal>, gj: Seq<usize>, gs: Seq<i128>, sel: Seq<usize>, ss: Seq<i128>, sd: Seq<i32>)
    requires
        gj.len() == gs.len(),
        forall|g: int| 0 <= g < gj.len() ==> #[trigger] gs[g] as int == order_sum(sv, seg_of(ps), dl_of(ps), gj[g] as int, 0, n_l(sv)),
        sel.len() == ss.len(), sel.len() == sd.len(),
        sel.len() == if gj.len() <= 10 { gj.len() as int } else { 10 },
        sorted_sel(ss, sd),
        sel.no_duplicates(),
        forall|k: int| 0 <= k < sel.len() ==> gj.contains(#[trigger] sel[k]),
        forall|k: int| 0 <= k < sel.len() ==> #[trigger] ss[k] as int == order_sum(sv, seg_of(ps), dl_of(ps), sel[k] as int, 0, n_l(sv))
            && sd[k] == od(sv)[sel[k] as int],
        sel.len() > 0 ==> forall|h: int| 0 <= h < gj.len() && !sel.contains(#[trigger] gj[h]) ==>
            row_cmp(ss.last() as int, sd.last() as int, gs[h] as int, od(sv)[gj[h] as int] as int) <= 0,
    ensures top_rows_ok(sv, ps, gj.map_values(|x: usize| x as int), sel.map_values(|x: usize| x as int)),
{
    let groups = gj.map_values(|x: usize| x as int);
    let si = sel.map_values(|x: usize| x as int);
    let rows = si.map_values(|j: int| group_row(sv, ps, j));
    assert(si.no_duplicates()) by {
        assert forall|a: int, b: int| 0 <= a < si.len() && 0 <= b < si.len() && a != b implies si[a] != si[b] by {
            assert(sel[a] != sel[b]);
        }
    }
    assert forall|t: int| 0 <= t < si.len() implies groups.contains(#[trigger] si[t]) by {
        assert(gj.contains(sel[t]));
        let h = choose|h: int| 0 <= h < gj.len() && gj[h] == sel[t];
        assert(groups[h] == si[t]);
    }
    assert forall|a: int, b: int| 0 <= a < b < rows.len() implies keys_cmp(q3_order_keys(), #[trigger] rows[a], #[trigger] rows[b]) <= 0 by {
        lemma_order_row_cmp(sv, si[a], ss[a] as int, si[b], ss[b] as int);
        assert(rows[a] == order_row(sv, si[a], ss[a] as int));
        assert(rows[b] == order_row(sv, si[b], ss[b] as int));
    }
    if si.len() > 0 {
        let last = si.len() - 1;
        assert(rows.last() == order_row(sv, si[last], ss[last] as int));
        assert forall|j: int| #[trigger] groups.contains(j) && !si.contains(j) implies
            keys_cmp(q3_order_keys(), rows.last(), group_row(sv, ps, j)) <= 0 by {
            let h = choose|h: int| 0 <= h < groups.len() && groups[h] == j;
            assert(gj[h] as int == j);
            if sel.contains(gj[h]) {
                let k = choose|k: int| 0 <= k < sel.len() && sel[k] == gj[h];
                assert(si[k] == j);
            }
            lemma_order_row_cmp(sv, si[last], ss[last] as int, j, gs[h] as int);
        }
    }
}

} // verus!
