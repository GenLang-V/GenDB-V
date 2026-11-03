//! The answer from the tasks' results: merge (ghost) and flags, the threshold `theta` (the largest of the full
//! tasks' least listed sums: no group outside the listed ones exceeds it), the candidates (listed groups with sum at
//! least `theta`), their sort by sum and the first `TOP` rows.
use vstd::prelude::*;
use vstd::multiset::Multiset;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::stores::num::interface::common::text::text_entry_of;
use crate::agent::meaning::{p_stmt, ps_ok};
use crate::agent::views::*;
use crate::agent::fspec::*;
use crate::agent::load::{Inputs, loaded};
use crate::agent::filings::{Filing, FilingOut, lemma_stext, lemma_ptext};
use crate::agent::join::*;
use crate::agent::assemble::*;
use crate::agent::phases::{a_done, d_done, cuts_ok};
use crate::agent::common::sort::{sort_range, SumOrder, SortOrder, all_ok, sorted_by};
use crate::gendb_entry::work::filled;
use crate::gendb_entry::{Answer, answer_meets};
use crate::exec::value::{EVal, view_row};
use crate::link::query::view_rows;
use crate::stores::num::interface as ni;
use crate::stores::pre::interface as pi;
use crate::stores::sub::interface as si;
use crate::stores::pre::interface::common::text as ptext;
use crate::stores::sub::interface::common::text as stext;
use crate::stores::pre::interface::common::cols::list_entry;
use crate::agent::pairs::pd_ok;

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

/// The groups of the first `n` tasks, in task order.
pub open spec fn concat_groups(gs: Seq<JoinOut>, n: int) -> Seq<Partial>
    decreases n,
{
    if n <= 0 { Seq::empty() } else { concat_groups(gs, n - 1) + gs[n - 1].groups@ }
}

pub open spec fn any_cnt(gg: Seq<Partial>) -> bool {
    exists|x: int| 0 <= x < gg.len() && (#[trigger] gg[x]).cnt == CNT_OVER
}

pub open spec fn any_mass(gg: Seq<Partial>) -> bool {
    exists|x: int| 0 <= x < gg.len() && (#[trigger] gg[x]).mass == MASS_OVER
}

proof fn lemma_any_append(a: Seq<Partial>, b: Seq<Partial>)
    ensures any_cnt(a + b) == (any_cnt(a) || any_cnt(b)), any_mass(a + b) == (any_mass(a) || any_mass(b)),
{
    let c = a + b;
    if any_cnt(c) {
        let x = choose|x: int| 0 <= x < c.len() && (#[trigger] c[x]).cnt == CNT_OVER;
        if x >= a.len() { assert(b[x - a.len()] == c[x]); }
    }
    if any_cnt(b) {
        let x = choose|x: int| 0 <= x < b.len() && (#[trigger] b[x]).cnt == CNT_OVER;
        assert(c[a.len() + x] == b[x]);
    }
    if any_cnt(a) {
        let x = choose|x: int| 0 <= x < a.len() && (#[trigger] a[x]).cnt == CNT_OVER;
        assert(c[x] == a[x]);
    }
    if any_mass(c) {
        let x = choose|x: int| 0 <= x < c.len() && (#[trigger] c[x]).mass == MASS_OVER;
        if x >= a.len() { assert(b[x - a.len()] == c[x]); }
    }
    if any_mass(b) {
        let x = choose|x: int| 0 <= x < b.len() && (#[trigger] b[x]).mass == MASS_OVER;
        assert(c[a.len() + x] == b[x]);
    }
    if any_mass(a) {
        let x = choose|x: int| 0 <= x < a.len() && (#[trigger] a[x]).mass == MASS_OVER;
        assert(c[x] == a[x]);
    }
}

/// The finished tasks' results, task `k` for the names `[ncuts[k], ncuts[k + 1])`.
pub open spec fn tasks_done(sv: StoresView, ps: Seq<Literal>, ncuts: Seq<u64>, aouts: Seq<FilingOut>, gouts: Seq<JoinOut>,
    w: int) -> bool {
    &&& aouts.len() == w && gouts.len() == w && ncuts.len() == w + 1
    &&& forall|k: int| 0 <= k < w ==> #[trigger] a_done(sv, ps, ncuts[k] as int, ncuts[k + 1] as int, aouts[k])
        && d_done(sv, ps, aouts[k].filings@, aouts[k].len as int, gouts[k])
}

/// Merge every task (ghost) and read the flags.
pub fn merge(Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, ncuts: &Vec<u64>, Ghost(aouts): Ghost<Seq<FilingOut>>,
    gouts: &Vec<JoinOut>, w: usize) -> (r: (bool, bool, Ghost<Seq<Filing>>))
    requires
        layouts(sv), cuts_ok(ncuts@, w as int, name_count(sv)), tasks_done(sv, ps, ncuts@, aouts, gouts@, w as int),
    ensures
        merged_ok(sv, ps, name_count(sv), r.2@, concat_groups(gouts@, w as int)),
        r.0 == any_cnt(concat_groups(gouts@, w as int)), r.1 == any_mass(concat_groups(gouts@, w as int)),
{
    let ghost mut pall: Seq<Filing> = Seq::empty();
    let mut cnt_any = false;
    let mut mass_any = false;
    proof { lemma_merged_init(sv, ps); }
    let mut k: usize = 0;
    while k < w
        invariant
            layouts(sv), k <= w, cuts_ok(ncuts@, w as int, name_count(sv)), tasks_done(sv, ps, ncuts@, aouts, gouts@, w as int),
            merged_ok(sv, ps, ncuts@[k as int] as int, pall, concat_groups(gouts@, k as int)),
            cnt_any == any_cnt(concat_groups(gouts@, k as int)), mass_any == any_mass(concat_groups(gouts@, k as int)),
        decreases w - k,
    {
        proof {
            assert(a_done(sv, ps, ncuts@[k as int] as int, ncuts@[k + 1] as int, aouts[k as int]));
            assert(ncuts@[k as int] <= ncuts@[k + 1]);
            lemma_merge_step(sv, ps, ncuts@[k as int] as int, ncuts@[k + 1] as int, pall, concat_groups(gouts@, k as int),
                aouts[k as int], gouts@[k as int]);
            lemma_any_append(concat_groups(gouts@, k as int), gouts@[k as int].groups@);
            pall = pall + aouts[k as int].pushed@;
        }
        cnt_any = cnt_any || gouts[k].cnt_over;
        mass_any = mass_any || gouts[k].mass_over;
        k = k + 1;
    }
    (cnt_any, mass_any, Ghost(pall))
}

/// The threshold: the largest least sum of the full lists (`found` when some list is full).
pub fn theta(gouts: &Vec<JoinOut>, w: usize) -> (r: (bool, i128, Ghost<int>))
    requires
        gouts@.len() == w,
        forall|k: int| 0 <= k < w ==> (#[trigger] gouts@[k]).top@.len() == TOP && gouts@[k].len <= TOP,
    ensures
        !r.0 ==> forall|k: int| 0 <= k < w ==> (#[trigger] gouts@[k]).len < TOP,
        r.0 ==> 0 <= r.2@ < w && gouts@[r.2@].len == TOP
            && forall|i: int| 0 <= i < TOP ==> #[trigger] gouts@[r.2@].top@[i].sum >= r.1,
        r.0 ==> forall|k: int| 0 <= k < w && (#[trigger] gouts@[k]).len == TOP
            ==> exists|i: int| 0 <= i < TOP && gouts@[k].top@[i].sum <= r.1,
{
    let mut found = false;
    let mut th: i128 = 0;
    let ghost mut ts: int = 0;
    let mut k: usize = 0;
    while k < w
        invariant
            k <= w, gouts@.len() == w,
            forall|a: int| 0 <= a < w ==> (#[trigger] gouts@[a]).top@.len() == TOP && gouts@[a].len <= TOP,
            !found ==> forall|a: int| 0 <= a < k ==> (#[trigger] gouts@[a]).len < TOP,
            found ==> 0 <= ts < k && gouts@[ts].len == TOP && forall|i: int| 0 <= i < TOP ==> #[trigger] gouts@[ts].top@[i].sum >= th,
            found ==> forall|a: int| 0 <= a < k && (#[trigger] gouts@[a]).len == TOP
                ==> exists|i: int| 0 <= i < TOP && gouts@[a].top@[i].sum <= th,
        decreases w - k,
    {
        if gouts[k].len == TOP {
            let mut m = gouts[k].top[0].sum;
            let ghost mut mi: int = 0;
            let mut i: usize = 1;
            while i < TOP
                invariant
                    1 <= i <= TOP, k < w, gouts@.len() == w, gouts@[k as int].top@.len() == TOP,
                    0 <= mi < i, gouts@[k as int].top@[mi].sum == m,
                    forall|a: int| 0 <= a < i ==> #[trigger] gouts@[k as int].top@[a].sum >= m,
                decreases TOP - i,
            {
                if gouts[k].top[i].sum < m {
                    m = gouts[k].top[i].sum;
                    proof { mi = i as int; }
                }
                i = i + 1;
            }
            let ghost th0 = th;
            if !found || m > th {
                th = m;
                proof { ts = k as int; }
                found = true;
            }
            proof {
                assert forall|a: int| 0 <= a < k + 1 && (#[trigger] gouts@[a]).len == TOP
                    implies exists|i: int| 0 <= i < TOP && gouts@[a].top@[i].sum <= th by {
                    if a == k {
                        assert(gouts@[a].top@[mi].sum <= th);
                    } else {
                        let i = choose|i: int| 0 <= i < TOP && gouts@[a].top@[i].sum <= th0;
                        assert(gouts@[a].top@[i].sum <= th);
                    }
                }
            }
        }
        k = k + 1;
    }
    (found, th, Ghost(ts))
}

proof fn lemma_mset_push3(a: Seq<Partial>, b: Seq<Partial>, m0: Multiset<Partial>, t: Seq<Partial>, x: Partial)
    requires a.to_multiset().add(b.to_multiset()) == m0.add(t.to_multiset()),
    ensures
        a.push(x).to_multiset().add(b.to_multiset()) == m0.add(t.push(x).to_multiset()),
        a.to_multiset().add(b.push(x).to_multiset()) == m0.add(t.push(x).to_multiset()),
{
    let sx = seq![x];
    assert(a.push(x) =~= a + sx);
    assert(b.push(x) =~= b + sx);
    assert(t.push(x) =~= t + sx);
    vstd::seq_lib::lemma_multiset_commutative(a, sx);
    vstd::seq_lib::lemma_multiset_commutative(b, sx);
    vstd::seq_lib::lemma_multiset_commutative(t, sx);
    let (am, bm, tm, xm) = (a.to_multiset(), b.to_multiset(), t.to_multiset(), sx.to_multiset());
    assert forall|v: Partial| am.add(xm).add(bm).count(v) == m0.add(tm.add(xm)).count(v)
        && am.add(bm.add(xm)).count(v) == m0.add(tm.add(xm)).count(v) by {
        vstd::multiset::axiom_multiset_add(am, bm, v);
        vstd::multiset::axiom_multiset_add(m0, tm, v);
        vstd::multiset::axiom_multiset_add(am, xm, v);
        vstd::multiset::axiom_multiset_add(am.add(xm), bm, v);
        vstd::multiset::axiom_multiset_add(tm, xm, v);
        vstd::multiset::axiom_multiset_add(m0, tm.add(xm), v);
        vstd::multiset::axiom_multiset_add(bm, xm, v);
        vstd::multiset::axiom_multiset_add(am, bm.add(xm), v);
        assert(am.add(bm).count(v) == m0.add(tm).count(v));
    }
    assert(am.add(xm).add(bm) =~= m0.add(tm.add(xm)));
    assert(am.add(bm.add(xm)) =~= m0.add(tm.add(xm)));
}

proof fn lemma_mset_rest(cm: Multiset<Partial>, nm: Multiset<Partial>, m0: Multiset<Partial>, tm: Multiset<Partial>,
    rm: Multiset<Partial>, gm: Multiset<Partial>)
    requires cm.add(nm) == m0.add(tm), gm == tm.add(rm),
    ensures cm.add(nm.add(rm)) == m0.add(gm),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    assert forall|v: Partial| cm.add(nm.add(rm)).count(v) == m0.add(gm).count(v) by {
        vstd::multiset::axiom_multiset_add(cm, nm, v);
        vstd::multiset::axiom_multiset_add(m0, tm, v);
        vstd::multiset::axiom_multiset_add(nm, rm, v);
        vstd::multiset::axiom_multiset_add(cm, nm.add(rm), v);
        vstd::multiset::axiom_multiset_add(tm, rm, v);
        vstd::multiset::axiom_multiset_add(m0, gm, v);
        assert(cm.add(nm).count(v) == m0.add(tm).count(v));
    }
    assert(cm.add(nm.add(rm)) =~= m0.add(gm));
}

/// The listed groups with sum at least `th` (all listed groups without a threshold), and the other groups (ghost).
pub fn candidates(gouts: &Vec<JoinOut>, w: usize, found: bool, th: i128, Ghost(ts): Ghost<int>) -> (r: (Vec<Partial>, Ghost<Seq<Partial>>))
    requires
        gouts@.len() == w,
        forall|k: int| 0 <= k < w ==> top_ok((#[trigger] gouts@[k]).top@, gouts@[k].len as int, gouts@[k].rest@, gouts@[k].groups@),
        !found ==> forall|k: int| 0 <= k < w ==> (#[trigger] gouts@[k]).len < TOP,
        found ==> 0 <= ts < w && gouts@[ts].len == TOP
            && forall|i: int| 0 <= i < TOP ==> #[trigger] gouts@[ts].top@[i].sum >= th,
        found ==> forall|k: int| 0 <= k < w && (#[trigger] gouts@[k]).len == TOP
            ==> exists|i: int| 0 <= i < TOP && gouts@[k].top@[i].sum <= th,
    ensures
        r.0@.to_multiset().add(r.1@.to_multiset()) == concat_groups(gouts@, w as int).to_multiset(),
        forall|a: int| 0 <= a < r.0@.len() ==> found ==> (#[trigger] r.0@[a]).sum >= th,
        forall|b: int| 0 <= b < r.1@.len() ==> (#[trigger] r.1@[b]).sum <= th,
        r.1@.len() > 0 ==> found && r.0@.len() >= TOP,
{
    let mut cand: Vec<Partial> = Vec::new();
    let ghost mut nonc: Seq<Partial> = Seq::empty();
    let mut k: usize = 0;
    while k < w
        invariant
            k <= w, gouts@.len() == w,
            forall|a: int| 0 <= a < w ==> top_ok((#[trigger] gouts@[a]).top@, gouts@[a].len as int, gouts@[a].rest@, gouts@[a].groups@),
            !found ==> forall|a: int| 0 <= a < w ==> (#[trigger] gouts@[a]).len < TOP,
            found ==> 0 <= ts < w && gouts@[ts].len == TOP
                && forall|i: int| 0 <= i < TOP ==> #[trigger] gouts@[ts].top@[i].sum >= th,
            found ==> forall|a: int| 0 <= a < w && (#[trigger] gouts@[a]).len == TOP
                ==> exists|i: int| 0 <= i < TOP && gouts@[a].top@[i].sum <= th,
            cand@.to_multiset().add(nonc.to_multiset()) == concat_groups(gouts@, k as int).to_multiset(),
            forall|a: int| 0 <= a < cand@.len() ==> found ==> (#[trigger] cand@[a]).sum >= th,
            forall|b: int| 0 <= b < nonc.len() ==> found && (#[trigger] nonc[b]).sum <= th,
            found && k > ts ==> cand@.len() >= TOP,
            !found ==> nonc.len() == 0,
        decreases w - k,
    {
        let g = gouts[k].len;
        let ghost top = gouts@[k as int].top@;
        let ghost m0 = concat_groups(gouts@, k as int).to_multiset();
        proof { assert(top_ok(top, g as int, gouts@[k as int].rest@, gouts@[k as int].groups@)); }
        let ghost c0 = cand@.len();
        let mut i: usize = 0;
        while i < g
            invariant
                k < w, gouts@.len() == w, i <= g, g == gouts@[k as int].len, g <= TOP, top == gouts@[k as int].top@,
                top.len() == TOP,
                found ==> 0 <= ts < w && gouts@[ts].len == TOP
                    && forall|a: int| 0 <= a < TOP ==> #[trigger] gouts@[ts].top@[a].sum >= th,
                cand@.to_multiset().add(nonc.to_multiset()) == m0.add(top.subrange(0, i as int).to_multiset()),
                forall|a: int| 0 <= a < cand@.len() ==> found ==> (#[trigger] cand@[a]).sum >= th,
                forall|b: int| 0 <= b < nonc.len() ==> found && (#[trigger] nonc[b]).sum <= th,
                found && k > ts ==> cand@.len() >= TOP,
                found && k == ts ==> cand@.len() >= c0 + i,
                c0 <= cand@.len(),
                !found ==> nonc.len() == 0,
            decreases g - i,
        {
            let x = gouts[k].top[i];
            proof {
                assert(top.subrange(0, i + 1) =~= top.subrange(0, i as int).push(x));
                lemma_mset_push3(cand@, nonc, m0, top.subrange(0, i as int), x);
            }
            if !found || x.sum >= th {
                cand.push(x);
            } else {
                proof { nonc = nonc.push(x); }
            }
            i = i + 1;
        }
        proof {
            let rest = gouts@[k as int].rest@;
            let grp = gouts@[k as int].groups@;
            vstd::seq_lib::lemma_multiset_commutative(nonc, rest);
            vstd::seq_lib::lemma_multiset_commutative(concat_groups(gouts@, k as int), grp);
            assert(concat_groups(gouts@, k + 1) == concat_groups(gouts@, k as int) + grp);
            if rest.len() > 0 {
                assert(g == TOP);
                let it = choose|it: int| 0 <= it < TOP && gouts@[k as int].top@[it].sum <= th;
                assert forall|b: int| 0 <= b < rest.len() implies found && (#[trigger] rest[b]).sum <= th by {
                    assert(rest[b].sum <= top[it].sum);
                }
            }
            let n2 = nonc + rest;
            assert forall|b: int| 0 <= b < n2.len() implies found && (#[trigger] n2[b]).sum <= th by {
                if b >= nonc.len() {
                    assert(n2[b] == rest[b - nonc.len()]);
                }
            }
            assert(top.subrange(0, g as int) == top.subrange(0, i as int));
            lemma_mset_rest(cand@.to_multiset(), nonc.to_multiset(), m0, top.subrange(0, g as int).to_multiset(),
                rest.to_multiset(), grp.to_multiset());
            nonc = n2;
        }
        k = k + 1;
    }
    (cand, Ghost(nonc))
}

fn copy_bytes(s: &[u8], n: usize) -> (v: Vec<u8>)
    requires n == s@.len(),
    ensures v@ == s@,
{
    let mut v: Vec<u8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant i <= n, n == s@.len(), v@ == s@.subrange(0, i as int),
        decreases n - i,
    {
        v.push(s[i]);
        i = i + 1;
        proof { assert(v@ =~= s@.subrange(0, i as int)); }
    }
    proof { assert(s@.subrange(0, n as int) =~= s@); }
    v
}

/// The output row of group `x`.
pub fn row_of(inp: &Inputs, p1: &[u8], x: Partial, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Vec<EVal>)
    requires loaded(*inp, sv), codes_ok(sv, x), x.cnt <= INT8_MAX, p1@ == p_stmt(ps),
    ensures view_row(r@) == rrow(sv, ps, x),
{
    let ghost sp = sv.sub;
    let ghost pp = sv.pre;
    proof {
        assert(si::sub_layout_ok(sp));
        assert(pi::pre_layout_ok(pp));
        assert(pd_ok(inp.dicts, sv));
        lemma_stext(inp.name_off@, inp.name_bytes@, inp.name_count as int);
        lemma_ptext(inp.dicts.ptag_off@, inp.dicts.ptag_bytes@, inp.dicts.ptag_count as int);
        assert(pi::P_PLABEL_OFF + 1 == pi::P_PLABEL_BYTES);
        lemma_ptext(inp.plabel_off@, inp.plabel_bytes@, inp.nplabel as int);
    }
    let mut row: Vec<EVal> = Vec::new();
    let (nmb, nml) = text_entry_of(inp.name_off, inp.name_bytes, inp.name_count, x.nm as usize);
    row.push(EVal::Text(copy_bytes(nmb, nml)));
    row.push(EVal::Text(copy_bytes(p1, p1.len())));
    let (tb, tl) = text_entry_of(inp.dicts.ptag_off, inp.dicts.ptag_bytes, inp.dicts.ptag_count, x.tag as usize);
    row.push(EVal::Text(copy_bytes(tb, tl)));
    if x.pk == 0 {
        row.push(EVal::Null);
    } else {
        let (lb, ll) = text_entry_of(inp.plabel_off, inp.plabel_bytes, inp.nplabel, (x.pk - 1) as usize);
        row.push(EVal::Text(copy_bytes(lb, ll)));
    }
    row.push(EVal::Num { coeff: x.sum, scale: 4 });
    row.push(EVal::Int(x.cnt as i64));
    proof {
        assert(view_row(row@) =~= rrow(sv, ps, x));
    }
    row
}

/// The answer from the finished tasks.
pub fn finish(inp: &Inputs, p1: &[u8], ncuts: &Vec<u64>, gouts: &Vec<JoinOut>, w: usize, Ghost(sv): Ghost<StoresView>,
    Ghost(ps): Ghost<Seq<Literal>>, Ghost(aouts): Ghost<Seq<FilingOut>>) -> (r: Answer)
    requires
        loaded(*inp, sv), ps_ok(ps), p1@ == p_stmt(ps), cuts_ok(ncuts@, w as int, inp.name_count as int),
        tasks_done(sv, ps, ncuts@, aouts, gouts@, w as int),
    ensures answer_meets(sv, ps, Ok(r)),
{
    let (cnt_any, mass_any, Ghost(pall)) = merge(Ghost(sv), Ghost(ps), ncuts, Ghost(aouts), gouts, w);
    let ghost gg = concat_groups(gouts@, w as int);
    if cnt_any {
        proof {
            let x = choose|x: int| 0 <= x < gg.len() && (#[trigger] gg[x]).cnt == CNT_OVER;
            lemma_answer_count_err(sv, ps, pall, gg, x);
        }
        return Answer::SqlError(SqlError::NumericValueOutOfRange);
    }
    if mass_any {
        proof {
            let x = choose|x: int| 0 <= x < gg.len() && (#[trigger] gg[x]).mass == MASS_OVER;
            lemma_answer_capacity(sv, ps, pall, gg, x);
        }
        return Answer::Capacity;
    }
    proof {
        assert forall|k: int| 0 <= k < w implies top_ok((#[trigger] gouts@[k]).top@, gouts@[k].len as int, gouts@[k].rest@, gouts@[k].groups@)
            && gouts@[k].top@.len() == TOP && gouts@[k].len <= TOP by {
            assert(a_done(sv, ps, ncuts@[k] as int, ncuts@[k + 1] as int, aouts[k]));
            assert(d_done(sv, ps, aouts[k].filings@, aouts[k].len as int, gouts@[k]));
        }
        assert(no_flags(gg));
    }
    let (found, th, Ghost(ts)) = theta(gouts, w);
    let cr = candidates(gouts, w, found, th, Ghost(ts));
    let ghost nonc = cr.1@;
    proof {
        assert(forall|b: int| 0 <= b < nonc.len() ==> (#[trigger] nonc[b]).sum <= th);
    }
    let mut cand = cr.0;
    let ghost c0 = cand@;
    let nc = cand.len();
    let mut tmp: Vec<Partial> = filled(nc, empty_partial());
    let so = SumOrder {};
    proof {
        assert forall|q: int| 0 <= q < nc implies so.ok(#[trigger] cand@.subrange(0, nc as int)[q]) by {}
    }
    sort_range(&so, &mut cand, &mut tmp, 0, nc);
    let ghost cs = cand@;
    proof {
        assert(cs.subrange(0, nc as int) =~= cs);
        assert(c0.subrange(0, nc as int) =~= c0);
        vstd::seq_lib::lemma_multiset_commutative(cs, nonc);
        assert((cs + nonc).to_multiset() == gg.to_multiset());
        assert forall|a: int| 0 <= a < cs.len() && found implies (#[trigger] cs[a]).sum >= th by {
            assert(cs.contains(cs[a]));
            assert(c0.to_multiset().count(cs[a]) > 0);
            assert(c0.contains(cs[a]));
        }
    }
    proof {
        assert forall|a: int, b: int| 0 <= a < cs.len() && 0 <= b < nonc.len() implies (#[trigger] cs[a]).sum >= (#[trigger] nonc[b]).sum by {
            assert(nonc[b].sum <= th);
            assert(found);
            assert(cs[a].sum >= th);
        }
        assert forall|a: int, b: int| 0 <= a < b < cs.len() implies (#[trigger] cs[a]).sum >= (#[trigger] cs[b]).sum by {
            assert(cs.subrange(0, nc as int)[a] == cs[a] && cs.subrange(0, nc as int)[b] == cs[b]);
            assert(so.le(cs.subrange(0, nc as int)[a], cs.subrange(0, nc as int)[b]));
        }
        assert(nonc.len() > 0 ==> cs.len() >= TOP);
    }
    let nout = if nc < TOP { nc } else { TOP };
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut i: usize = 0;
    while i < nout
        invariant
            loaded(*inp, sv), p1@ == p_stmt(ps), i <= nout, nout <= nc, cand@ == cs, cs.len() == nc,
            merged_ok(sv, ps, name_count(sv), pall, gg), no_flags(gg), (cs + nonc).to_multiset() == gg.to_multiset(),
            rows@.len() == i,
            forall|a: int| 0 <= a < i ==> #[trigger] view_row(rows@[a]@) == rrow(sv, ps, cs[a]),
            forall|a: int, b: int| 0 <= a < cs.len() && 0 <= b < nonc.len() ==> (#[trigger] cs[a]).sum >= (#[trigger] nonc[b]).sum,
            forall|a: int, b: int| 0 <= a < b < cs.len() ==> (#[trigger] cs[a]).sum >= (#[trigger] cs[b]).sum,
            nonc.len() > 0 ==> cs.len() >= TOP,
            nout == if nc < TOP { nc } else { TOP },
            ps_ok(ps),
        decreases nout - i,
    {
        let x = cand[i];
        proof {
            lemma_in_groups(gg, cs, nonc, x);
            let y = choose|y: int| 0 <= y < gg.len() && gg[y] == x;
            assert(exact_ok(gg[y]) && codes_ok(sv, gg[y]));
        }
        let row = row_of(inp, p1, x, Ghost(sv), Ghost(ps));
        rows.push(row);
        i = i + 1;
    }
    proof {
        let out = view_rows(rows@);
        assert forall|a: int| 0 <= a < out.len() implies #[trigger] out[a] == rrow(sv, ps, cs[a]) by {
            assert(out[a] == view_row(rows@[a]@));
        }
        assert(lists_ok(sv, ps, gg, cs, nonc, out));
        lemma_answer_rows(sv, ps, pall, gg, cs, nonc, rows@);
    }
    Answer::Rows(rows)
}

} // verus!
