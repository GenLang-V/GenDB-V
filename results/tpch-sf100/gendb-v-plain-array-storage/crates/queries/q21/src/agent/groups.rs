//! The groups of the statement (one per `s_name` with a waiting row) from the counts of the selected suppliers.
//!
//! The COUNT of name `nm` is the sum of the counts of the selected suppliers named `nm` (`lemma_gc_sel`: the other
//! suppliers have no nation named `$1`, a selected one exactly one by the primary key). The groups are built in one
//! pass over the selected suppliers with a positive count (`build_groups`): a supplier joins the group of its name,
//! found by a scan of the groups, or starts one. When every such supplier's name is `<9 bytes><decimal digits of its
//! key>` (dbgen's `Supplier#000000001`; `name_keys`), two of them never share a name (their keys differ), so the scan
//! is skipped. A group's count is kept capped at `CAP = 2^63` (one more than int8's maximum), which is exact below it.
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::{text_at, text_wf};
use crate::agent::cols::*;
use crate::agent::nf::*;
use crate::agent::scan::*;
use crate::agent::plan::sel_exact;

verus! {

/// One more than int8's maximum.
pub const CAP: u64 = 0x8000_0000_0000_0000;

/// `x` capped at `CAP`.
pub open spec fn capped(x: int) -> int { if x < CAP as int { x } else { CAP as int } }

/// The name of the selected supplier `ci`.
pub open spec fn gname(sv: StoresView, m: SupMap, ci: int) -> Seq<u8> { sname(sv, m.sel@[ci] as int) }

/// The counts of the selected suppliers over all lineitem rows.
pub open spec fn tot_ok(sv: StoresView, m: SupMap, tot: Seq<u64>) -> bool {
    &&& tot.len() == m.nsel
    &&& forall|ci: int| 0 <= ci < m.nsel ==> #[trigger] tot[ci] as int == ksum(sv, ckey(m, ci), 0, n_l(sv))
}

/// The sum of the counts of the first `k` selected suppliers named `nm`.
pub open spec fn csel(sv: StoresView, m: SupMap, tot: Seq<u64>, nm: Seq<u8>, k: int) -> int
    decreases k,
{
    if k <= 0 { 0 } else { csel(sv, m, tot, nm, k - 1) + if gname(sv, m, k - 1) == nm { tot[k - 1] as int } else { 0 } }
}

/// The group count over supplier rows `0..s` is the sum over the selected suppliers below `s` (the first `k`).
proof fn lemma_gsum_sel(sv: StoresView, p: Seq<u8>, m: SupMap, tot: Seq<u64>, nm: Seq<u8>, s: int, k: int)
    requires
        sv_facts(sv), sup_ok(m, sv), sel_exact(m, sv, p), tot_ok(sv, m, tot),
        0 <= s <= n_s(sv), 0 <= k <= m.nsel,
        k == m.nsel || m.sel@[k] >= s,
        k == 0 || m.sel@[k - 1] < s,
    ensures gsum_s(sv, p, nm, s) == csel(sv, m, tot, nm, k),
    decreases s,
{
    if s > 0 {
        let s1 = s - 1;
        if k > 0 && m.sel@[k - 1] == s1 {
            if k > 1 { assert(m.sel@[k - 2] < m.sel@[k - 1]); }
            lemma_gsum_sel(sv, p, m, tot, nm, s1, k - 1);
            assert(nw(sv, p, m.sel@[k - 1] as int) > 0);
            lemma_ncnt_le1(sv, p, snk(sv)[s1] as int, n_n(sv));
            assert(nw(sv, p, s1) == 1);
            assert(tot[k - 1] as int == ksum(sv, ckey(m, k - 1), 0, n_l(sv)));
        } else {
            lemma_gsum_sel(sv, p, m, tot, nm, s1, k);
            if nw(sv, p, s1) > 0 {
                let ci = choose|ci: int| 0 <= ci < m.nsel && #[trigger] m.sel@[ci] == s1;
                if ci < k - 1 { assert(m.sel@[ci] < m.sel@[k - 1]); }
                if ci > k { assert(m.sel@[k] < m.sel@[ci]); }
            }
            assert(nw(sv, p, s1) == 0);
        }
    } else {
        if k > 0 { assert(m.sel@[k - 1] >= 0); }
    }
}

/// The COUNT of name `nm` is the sum of the counts of the selected suppliers named `nm`.
pub proof fn lemma_gc_sel(sv: StoresView, p: Seq<u8>, m: SupMap, tot: Seq<u64>, nm: Seq<u8>)
    requires sv_facts(sv), sup_ok(m, sv), sel_exact(m, sv, p), tot_ok(sv, m, tot),
    ensures gc(sv, p, nm) == csel(sv, m, tot, nm, m.nsel as int),
{
    let k = m.nsel as int;
    if k > 0 { assert(m.sel@[k - 1] < m.ns); }
    lemma_gsum_sel(sv, p, m, tot, nm, n_s(sv), k);
}

/// A positive sum has a selected supplier of that name with a positive count.
pub proof fn lemma_csel_pos(sv: StoresView, m: SupMap, tot: Seq<u64>, nm: Seq<u8>, k: int)
    requires 0 <= k <= tot.len(), csel(sv, m, tot, nm, k) > 0,
    ensures exists|cj: int| 0 <= cj < k && #[trigger] gname(sv, m, cj) == nm && tot[cj] > 0,
    decreases k,
{
    if k > 0 {
        if gname(sv, m, k - 1) == nm && tot[k - 1] > 0 {
            assert(gname(sv, m, k - 1) == nm);
        } else {
            lemma_csel_pos(sv, m, tot, nm, k - 1);
            let cj = choose|cj: int| 0 <= cj < k - 1 && #[trigger] gname(sv, m, cj) == nm && tot[cj] > 0;
            assert(gname(sv, m, cj) == nm);
        }
    }
}

pub proof fn lemma_csel_nonneg(sv: StoresView, m: SupMap, tot: Seq<u64>, nm: Seq<u8>, k: int)
    ensures csel(sv, m, tot, nm, k) >= 0,
    decreases k,
{
    if k > 0 { lemma_csel_nonneg(sv, m, tot, nm, k - 1); }
}

// ------------------------------------------------------------------------------------------------ names

/// Whether supplier rows `s1` and `s2` have the same name.
fn names_eq(c: &Cols, s1: usize, s2: usize, Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires cols_ok(*c, sv), s1 < c.ns, s2 < c.ns,
    ensures r == (sname(sv, s1 as int) == sname(sv, s2 as int)),
{
    let ghost t = sname_col(sv);
    let a1 = c.snoff[s1];
    let b1 = c.snoff[s1 + 1];
    let a2 = c.snoff[s2];
    let b2 = c.snoff[s2 + 1];
    let blen = c.snb.len();
    proof {
        assert(0 <= t.offsets[s1 as int] <= t.offsets[s1 + 1] <= t.bytes.len());
        assert(0 <= t.offsets[s2 as int] <= t.offsets[s2 + 1] <= t.bytes.len());
    }
    if b1 - a1 != b2 - a2 {
        proof { assert(sname(sv, s1 as int).len() != sname(sv, s2 as int).len()); }
        return false;
    }
    let len = (b1 - a1) as usize;
    let (u1, u2) = (a1 as usize, a2 as usize);
    let ghost n1 = sname(sv, s1 as int);
    let ghost n2 = sname(sv, s2 as int);
    let mut i: usize = 0;
    while i < len
        invariant
            cols_ok(*c, sv), t == sname_col(sv), s1 < c.ns, s2 < c.ns, blen == c.snb@.len(),
            u1 == a1, u2 == a2, a1 == t.offsets[s1 as int], b1 == t.offsets[s1 + 1], a2 == t.offsets[s2 as int],
            b2 == t.offsets[s2 + 1], 0 <= a1 <= b1 <= blen, 0 <= a2 <= b2 <= blen, len == b1 - a1, len == b2 - a2,
            i <= len,
            n1 == sname(sv, s1 as int), n2 == sname(sv, s2 as int),
            forall|k: int| 0 <= k < i ==> #[trigger] n1[k] == n2[k],
        decreases len - i,
    {
        proof { assert(n1[i as int] == c.snb@[u1 + i] && n2[i as int] == c.snb@[u2 + i]); }
        if c.snb[u1 + i] != c.snb[u2 + i] {
            return false;
        }
        i = i + 1;
    }
    proof { assert(n1 =~= n2); }
    true
}

/// Decimal value of bytes (any byte counts as its value minus `'0'`).
pub open spec fn dec_val(b: Seq<u8>) -> int
    decreases b.len(),
{
    if b.len() == 0 { 0 } else { dec_val(b.drop_last()) * 10 + (b.last() as int - 48) }
}

/// Supplier row `s`'s name is 9 bytes followed by bytes whose decimal value is its key.
pub open spec fn keyed(sv: StoresView, s: int) -> bool {
    let nm = sname(sv, s);
    nm.len() >= 9 && dec_val(nm.subrange(9, nm.len() as int)) == skey(sv)[s] as int
}

pub open spec fn p10(k: nat) -> nat
    decreases k,
{
    if k == 0 { 1 } else { 10 * p10((k - 1) as nat) }
}

/// The decimal value of supplier row `s`'s name after its first 9 bytes, when they are at most 18 decimal digits.
fn name_dec(c: &Cols, s: usize, Ghost(sv): Ghost<StoresView>) -> (r: Option<u64>)
    requires cols_ok(*c, sv), s < c.ns,
    ensures r matches Some(v) ==> sname(sv, s as int).len() >= 9
        && dec_val(sname(sv, s as int).subrange(9, sname(sv, s as int).len() as int)) == v as int,
{
    let ghost t = sname_col(sv);
    let a = c.snoff[s];
    let b = c.snoff[s + 1];
    let blen = c.snb.len();
    proof { assert(0 <= t.offsets[s as int] <= t.offsets[s + 1] <= t.bytes.len()); }
    if b - a < 9 || b - a > 27 {
        return None;
    }
    let ghost nm = sname(sv, s as int);
    let start = (a + 9) as usize;
    let end = b as usize;
    let mut v: u64 = 0;
    let mut i: usize = start;
    proof {
        assert(nm.subrange(9, (i - a) as int) =~= Seq::<u8>::empty());
        assert(p10(0) == 1);
    }
    while i < end
        invariant
            cols_ok(*c, sv), t == sname_col(sv), s < c.ns, nm == sname(sv, s as int), blen == c.snb@.len(),
            a == t.offsets[s as int], b == t.offsets[s + 1], 0 <= a, a + 9 <= b <= blen, b - a <= 27,
            start == a + 9, end == b, start <= i <= end,
            v as int == dec_val(nm.subrange(9, i - a)),
            (v as int) < p10((i - start) as nat),
        decreases end - i,
    {
        let d = c.snb[i];
        if d < 48u8 || d > 57u8 {
            return None;
        }
        proof {
            let k = (i - start) as nat;
            assert(p10(k + 1) == 10 * p10(k));
            assert(nm[i - a] == d);
            assert(nm.subrange(9, i + 1 - a).drop_last() =~= nm.subrange(9, i - a));
            assert(k <= 17);
            assert(p10(k) <= p10(17)) by {
                lemma_p10_mono(k, 17);
            }
            assert(p10(17) == 100_000_000_000_000_000) by (compute);
            assert((v as int) * 10 + 9 < 10 * p10(k)) by (nonlinear_arith) requires (v as int) < p10(k);
        }
        v = v * 10 + (d - 48u8) as u64;
        i = i + 1;
    }
    proof { assert(nm.subrange(9, end - a) =~= nm.subrange(9, nm.len() as int)); }
    Some(v)
}

pub proof fn lemma_p10_mono(a: nat, b: nat)
    requires a <= b,
    ensures p10(a) <= p10(b),
    decreases b,
{
    if b > a { lemma_p10_mono(a, (b - 1) as nat); }
}

/// The selected suppliers with a positive count have pairwise different names.
pub open spec fn cand_distinct(sv: StoresView, m: SupMap, tot: Seq<u64>) -> bool {
    forall|ci: int, cj: int| 0 <= ci < m.nsel && 0 <= cj < m.nsel && tot[ci] > 0 && tot[cj] > 0
        && #[trigger] gname(sv, m, ci) == #[trigger] gname(sv, m, cj) ==> ci == cj
}

/// Whether every selected supplier with a positive count is `keyed` (then their names are pairwise different).
pub fn name_keys(c: &Cols, m: &SupMap, tot: &Vec<u64>, Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires cols_ok(*c, sv), sup_ok(*m, sv), tot@.len() == m.nsel,
    ensures r ==> cand_distinct(sv, *m, tot@),
{
    let mut ci: usize = 0;
    while ci < m.nsel
        invariant
            cols_ok(*c, sv), sup_ok(*m, sv), tot@.len() == m.nsel, ci <= m.nsel,
            forall|d: int| 0 <= d < ci && tot@[d] > 0 ==> #[trigger] keyed(sv, m.sel@[d] as int),
        decreases m.nsel - ci,
    {
        if tot[ci] > 0 {
            let s = m.sel[ci];
            match name_dec(c, s, Ghost(sv)) {
                Some(v) => {
                    let k = c.skey[s];
                    if k < 0 || v != k as u64 {
                        return false;
                    }
                },
                None => {
                    return false;
                },
            }
        }
        ci = ci + 1;
    }
    proof {
        assert forall|a: int, b: int| 0 <= a < m.nsel && 0 <= b < m.nsel && tot@[a] > 0 && tot@[b] > 0
            && #[trigger] gname(sv, *m, a) == #[trigger] gname(sv, *m, b) implies a == b by {
            let (sa, sb) = (m.sel@[a] as int, m.sel@[b] as int);
            assert(keyed(sv, sa) && keyed(sv, sb));
            assert(skey(sv)[sa] == skey(sv)[sb]);
            assert(sa == sb);
            if a < b { assert(m.sel@[a] < m.sel@[b]); }
            if b < a { assert(m.sel@[b] < m.sel@[a]); }
        }
    }
    true
}

// ------------------------------------------------------------------------------------------------ the groups

/// The groups after the first `k` selected suppliers: representatives `grep` (selected suppliers with a positive count,
/// pairwise different names) with their capped sums `gt`, and every supplier with a positive count among the first
/// `k` represented by its name.
pub open spec fn grp_ok(sv: StoresView, m: SupMap, tot: Seq<u64>, grep: Seq<usize>, gt: Seq<u64>, k: int) -> bool {
    &&& grep.len() == gt.len()
    &&& forall|g: int| 0 <= g < grep.len() ==> (#[trigger] grep[g] as int) < k && grep[g] < m.nsel && tot[grep[g] as int] > 0
    &&& forall|g: int, h: int| 0 <= g < grep.len() && 0 <= h < grep.len() && g != h
            ==> gname(sv, m, #[trigger] grep[g] as int) != gname(sv, m, #[trigger] grep[h] as int)
    &&& forall|g: int| 0 <= g < grep.len() ==> #[trigger] gt[g] as int == capped(csel(sv, m, tot, gname(sv, m, grep[g] as int), k))
    &&& forall|g: int| 0 <= g < grep.len() ==> csel(sv, m, tot, gname(sv, m, #[trigger] grep[g] as int), k) > 0
    &&& forall|cj: int| 0 <= cj < k && tot[cj] > 0 ==> exists|g: int| 0 <= g < grep.len() && #[trigger] gname(sv, m, grep[g] as int) == gname(sv, m, cj)
}

/// One more supplier `k` without a positive count: the groups stay.
proof fn lemma_grp_zero(sv: StoresView, m: SupMap, tot: Seq<u64>, grep: Seq<usize>, gt: Seq<u64>, k: int)
    requires grp_ok(sv, m, tot, grep, gt, k), 0 <= k < m.nsel, tot.len() == m.nsel, tot[k] == 0,
    ensures grp_ok(sv, m, tot, grep, gt, k + 1),
{
    assert forall|g: int| 0 <= g < grep.len() implies #[trigger] csel(sv, m, tot, gname(sv, m, grep[g] as int), k + 1)
        == csel(sv, m, tot, gname(sv, m, grep[g] as int), k) by {}
}

/// Supplier `k` with a positive count joins the group `g0` of its name.
#[verifier::spinoff_prover]
proof fn lemma_grp_join(sv: StoresView, m: SupMap, tot: Seq<u64>, grep: Seq<usize>, gt: Seq<u64>, k: int, g0: int,
    gt2: Seq<u64>)
    requires
        grp_ok(sv, m, tot, grep, gt, k), 0 <= k < m.nsel, tot.len() == m.nsel, tot[k] > 0,
        0 <= g0 < grep.len(), gname(sv, m, grep[g0] as int) == gname(sv, m, k),
        gt2 == gt.update(g0, capped(gt[g0] as int + tot[k] as int) as u64),
    ensures grp_ok(sv, m, tot, grep, gt2, k + 1),
{
    let nm = gname(sv, m, k);
    let t = tot[k] as int;
    lemma_csel_nonneg(sv, m, tot, nm, k);
    assert forall|g: int| 0 <= g < grep.len() implies #[trigger] csel(sv, m, tot, gname(sv, m, grep[g] as int), k + 1)
        == csel(sv, m, tot, gname(sv, m, grep[g] as int), k) + if gname(sv, m, grep[g] as int) == nm { t } else { 0 } by {}
    assert forall|g: int| 0 <= g < grep.len() implies #[trigger] gt2[g] as int
        == capped(csel(sv, m, tot, gname(sv, m, grep[g] as int), k + 1)) by {
        if g != g0 {
            assert(gname(sv, m, grep[g] as int) != gname(sv, m, grep[g0] as int));
        }
    }
    assert forall|cj: int| 0 <= cj < k + 1 && tot[cj] > 0 implies exists|g: int| 0 <= g < grep.len()
        && #[trigger] gname(sv, m, grep[g] as int) == gname(sv, m, cj) by {
        if cj == k {
            assert(gname(sv, m, grep[g0] as int) == gname(sv, m, cj));
        }
    }
}

/// Supplier `k` with a positive count and a name no group has starts a group.
#[verifier::spinoff_prover]
proof fn lemma_grp_new(sv: StoresView, m: SupMap, tot: Seq<u64>, grep: Seq<usize>, gt: Seq<u64>, k: int,
    grep2: Seq<usize>, gt2: Seq<u64>)
    requires
        grp_ok(sv, m, tot, grep, gt, k), 0 <= k < m.nsel, tot.len() == m.nsel, tot[k] > 0,
        forall|g: int| 0 <= g < grep.len() ==> gname(sv, m, #[trigger] grep[g] as int) != gname(sv, m, k),
        grep2 == grep.push(k as usize), gt2 == gt.push(capped(tot[k] as int) as u64),
    ensures grp_ok(sv, m, tot, grep2, gt2, k + 1),
{
    let nm = gname(sv, m, k);
    let t = tot[k] as int;
    // no group has the name, so no earlier supplier with a positive count has it
    if csel(sv, m, tot, nm, k) > 0 {
        lemma_csel_pos(sv, m, tot, nm, k);
        let cj = choose|cj: int| 0 <= cj < k && #[trigger] gname(sv, m, cj) == nm && tot[cj] > 0;
        let g = choose|g: int| 0 <= g < grep.len() && #[trigger] gname(sv, m, grep[g] as int) == gname(sv, m, cj);
        assert(false);
    }
    lemma_csel_nonneg(sv, m, tot, nm, k);
    let n = grep.len() as int;
    assert(grep2[n] == k as usize);
    assert forall|g: int| 0 <= g < grep.len() implies #[trigger] csel(sv, m, tot, gname(sv, m, grep[g] as int), k + 1)
        == csel(sv, m, tot, gname(sv, m, grep[g] as int), k) by {}
    assert forall|g: int| 0 <= g < grep2.len() implies (#[trigger] grep2[g] as int) < k + 1 && grep2[g] < m.nsel
        && tot[grep2[g] as int] > 0 by {
        if g < n { assert(grep2[g] == grep[g]); }
    }
    assert forall|g: int, h: int| 0 <= g < grep2.len() && 0 <= h < grep2.len() && g != h
        implies gname(sv, m, #[trigger] grep2[g] as int) != gname(sv, m, #[trigger] grep2[h] as int) by {
        if g < n && h < n { assert(grep2[g] == grep[g] && grep2[h] == grep[h]); }
        else if g < n { assert(grep2[g] == grep[g]); }
        else if h < n { assert(grep2[h] == grep[h]); }
    }
    assert forall|g: int| 0 <= g < grep2.len() implies #[trigger] gt2[g] as int
        == capped(csel(sv, m, tot, gname(sv, m, grep2[g] as int), k + 1)) by {
        if g < n {
            assert(grep2[g] == grep[g] && gt2[g] == gt[g]);
        }
    }
    assert forall|g: int| 0 <= g < grep2.len() implies csel(sv, m, tot, gname(sv, m, #[trigger] grep2[g] as int), k + 1) > 0 by {
        if g < n {
            assert(grep2[g] == grep[g]);
        }
    }
    assert forall|cj: int| 0 <= cj < k + 1 && tot[cj] > 0 implies exists|g: int| 0 <= g < grep2.len()
        && #[trigger] gname(sv, m, grep2[g] as int) == gname(sv, m, cj) by {
        if cj == k {
            assert(gname(sv, m, grep2[n] as int) == gname(sv, m, cj));
        } else {
            let g = choose|g: int| 0 <= g < grep.len() && #[trigger] gname(sv, m, grep[g] as int) == gname(sv, m, cj);
            assert(grep2[g] == grep[g]);
            assert(gname(sv, m, grep2[g] as int) == gname(sv, m, cj));
        }
    }
}

/// The groups of all selected suppliers with a positive count.
pub fn build_groups(c: &Cols, m: &SupMap, tot: &Vec<u64>, distinct: bool, Ghost(sv): Ghost<StoresView>)
    -> (r: (Vec<usize>, Vec<u64>))
    requires cols_ok(*c, sv), sup_ok(*m, sv), tot@.len() == m.nsel, distinct ==> cand_distinct(sv, *m, tot@),
    ensures grp_ok(sv, *m, tot@, r.0@, r.1@, m.nsel as int),
{
    let mut grep: Vec<usize> = Vec::new();
    let mut gt: Vec<u64> = Vec::new();
    let mut ci: usize = 0;
    while ci < m.nsel
        invariant
            cols_ok(*c, sv), sup_ok(*m, sv), tot@.len() == m.nsel, distinct ==> cand_distinct(sv, *m, tot@),
            ci <= m.nsel, grp_ok(sv, *m, tot@, grep@, gt@, ci as int),
        decreases m.nsel - ci,
    {
        let t = tot[ci];
        if t > 0 {
            let s = m.sel[ci];
            let ng = grep.len();
            let mut fg: usize = ng;
            if !distinct {
                let mut g: usize = 0;
                while g < ng && fg == ng
                    invariant
                        cols_ok(*c, sv), sup_ok(*m, sv), ci < m.nsel, s == m.sel@[ci as int], g <= ng, ng == grep@.len(),
                        grp_ok(sv, *m, tot@, grep@, gt@, ci as int),
                        fg == ng || (fg < ng && gname(sv, *m, grep@[fg as int] as int) == gname(sv, *m, ci as int)),
                        fg == ng ==> forall|h: int| 0 <= h < g ==> gname(sv, *m, #[trigger] grep@[h] as int) != gname(sv, *m, ci as int),
                    decreases ng - g,
                {
                    if names_eq(c, m.sel[grep[g]], s, Ghost(sv)) {
                        fg = g;
                    }
                    g = g + 1;
                }
            } else {
                proof {
                    assert forall|h: int| 0 <= h < grep@.len() implies gname(sv, *m, #[trigger] grep@[h] as int) != gname(sv, *m, ci as int) by {
                        let x = grep@[h] as int;
                        if gname(sv, *m, x) == gname(sv, *m, ci as int) {
                            assert(x < ci);
                        }
                    }
                }
            }
            let ghost (grep0, gt0) = (grep@, gt@);
            if fg < ng {
                let x = gt[fg] as u128 + t as u128;
                let y: u64 = if x < CAP as u128 { x as u64 } else { CAP };
                gt.set(fg, y);
                proof {
                    lemma_grp_join(sv, *m, tot@, grep0, gt0, ci as int, fg as int, gt@);
                }
            } else {
                grep.push(ci);
                gt.push(if t < CAP { t } else { CAP });
                proof {
                    lemma_grp_new(sv, *m, tot@, grep0, gt0, ci as int, grep@, gt@);
                }
            }
        } else {
            proof {
                lemma_grp_zero(sv, *m, tot@, grep@, gt@, ci as int);
            }
        }
        ci = ci + 1;
    }
    (grep, gt)
}

} // verus!
