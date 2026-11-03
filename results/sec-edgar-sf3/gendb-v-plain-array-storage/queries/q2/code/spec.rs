//! The query's normal form over the flat parts of `num` (`c.np`, `c.n` rows) and `sub` (`c.sp`, `c.m` rows)
//! at the binding `$1 = c.pv` (bytes), `$2 = c.fy`: which `num` rows are candidates (`uom = $1` and a `sub`
//! row of the same `adsh` with `fy = $2`), which candidates are the maximum of their `(adsh, tag)` group among
//! the `uom = $1` rows, and the candidate lists at a coefficient threshold that the scan computes.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::link::query::{text_at, text_wf, TextView};
use crate::stores::flat_num::interface as ni;
use crate::stores::flat_sub::interface as si;

verus! {

/// The ghost context of one call: the parts of both storages, their row counts and the binding.
pub ghost struct Ctx {
    pub np: Seq<PartView>,
    pub n: int,
    pub sp: Seq<PartView>,
    pub m: int,
    pub pv: Seq<u8>,
    pub fy: int,
}

#[verifier::opaque]
pub open spec fn ctx_ok(c: Ctx) -> bool {
    &&& ni::parts_wf(c.np, c.n)
    &&& si::parts_wf(c.sp, c.m)
}

// ------------------------------------------------------------------------------------------------ num columns

pub open spec fn uom_view(np: Seq<PartView>) -> TextView {
    ni::text_view(np, ni::UOM_OFFSETS as int, ni::UOM_BYTES as int)
}

pub open spec fn adsh_view(np: Seq<PartView>) -> TextView {
    ni::text_view(np, ni::ADSH_OFFSETS as int, ni::ADSH_BYTES as int)
}

pub open spec fn tag_view(np: Seq<PartView>) -> TextView {
    ni::text_view(np, ni::TAG_OFFSETS as int, ni::TAG_BYTES as int)
}

pub open spec fn coeff_seq(np: Seq<PartView>) -> Seq<i128> {
    ni::i128s(np[ni::VALUE as int])
}

/// `uom` of `num` row `i` (bytes).
pub open spec fn uom_text(c: Ctx, i: int) -> Seq<u8> {
    text_at(uom_view(c.np), i)
}

/// `adsh` of `num` row `i` (bytes).
pub open spec fn adsh_text(c: Ctx, i: int) -> Seq<u8> {
    text_at(adsh_view(c.np), i)
}

/// `tag` of `num` row `i` (bytes).
pub open spec fn tag_text(c: Ctx, i: int) -> Seq<u8> {
    text_at(tag_view(c.np), i)
}

/// The `value` coefficient of `num` row `i` (scale 4).
pub open spec fn coeff(c: Ctx, i: int) -> int {
    coeff_seq(c.np)[i] as int
}

// ------------------------------------------------------------------------------------------------ sub columns

pub open spec fn sadsh_view(sp: Seq<PartView>) -> TextView {
    si::text_view(sp, si::ADSH_OFFSETS as int, si::ADSH_BYTES as int)
}

pub open spec fn sname_view(sp: Seq<PartView>) -> TextView {
    si::text_view(sp, si::NAME_OFFSETS as int, si::NAME_BYTES as int)
}

pub open spec fn fy_seq(sp: Seq<PartView>) -> Seq<i32> {
    si::i32s(sp[si::FY as int])
}

pub open spec fn fy_valid_seq(sp: Seq<PartView>) -> Seq<u8> {
    si::u8s(sp[si::FY_VALIDITY as int])
}

/// `adsh` of `sub` row `s` (bytes).
pub open spec fn sadsh_text(c: Ctx, s: int) -> Seq<u8> {
    text_at(sadsh_view(c.sp), s)
}

/// `name` of `sub` row `s` (bytes).
pub open spec fn sname_text(c: Ctx, s: int) -> Seq<u8> {
    text_at(sname_view(c.sp), s)
}

/// `sub` row `s` exists and its `fy` is not NULL and equals `$2`.
pub open spec fn member(c: Ctx, s: int) -> bool {
    0 <= s < c.m && fy_valid_seq(c.sp)[s] != 0 && fy_seq(c.sp)[s] as int == c.fy
}

/// `sub` row `s` matches `num` row `i`: a member with the same `adsh`.
pub open spec fn sub_match(c: Ctx, i: int, s: int) -> bool {
    member(c, s) && sadsh_text(c, s) == adsh_text(c, i)
}

pub open spec fn has_sub(c: Ctx, i: int) -> bool {
    exists|s: int| #[trigger] sub_match(c, i, s)
}

// ------------------------------------------------------------------------------------------------ candidates

/// `num` row `i` has `uom = $1` and a coefficient of at least `thr`.
pub open spec fn cand(c: Ctx, i: int, thr: int) -> bool {
    uom_text(c, i) == c.pv && coeff(c, i) >= thr
}

/// The candidates among rows `lo..hi` at threshold `thr`, in row order.
pub open spec fn cands(c: Ctx, lo: int, hi: int, thr: int) -> Seq<int>
    decreases hi - lo,
{
    if hi <= lo {
        Seq::empty()
    } else {
        let p = cands(c, lo, hi - 1, thr);
        if cand(c, hi - 1, thr) { p.push(hi - 1) } else { p }
    }
}

/// Parallel vectors (num rows, coefficients) list the rows `cs` in order with their coefficients (the first
/// `len` entries).
pub open spec fn lists(c: Ctx, rows: Seq<usize>, coeffs: Seq<i128>, len: int, cs: Seq<int>) -> bool {
    &&& 0 <= len <= rows.len()
    &&& len <= coeffs.len()
    &&& cs.len() == len
    &&& forall|k: int| 0 <= k < len ==> #[trigger] rows[k] as int == cs[k]
    &&& forall|k: int| 0 <= k < len ==> #[trigger] coeffs[k] as int == coeff(c, cs[k])
}

/// Parallel vectors (num rows, sub rows, coefficients) list the rows `cs` in order, each with a matching `sub`
/// row and its coefficient.
pub open spec fn entries(c: Ctx, rows: Seq<usize>, subs: Seq<usize>, coeffs: Seq<i128>, cs: Seq<int>) -> bool {
    &&& rows.len() == cs.len()
    &&& subs.len() == cs.len()
    &&& coeffs.len() == cs.len()
    &&& forall|k: int| 0 <= k < cs.len() ==> #[trigger] rows[k] as int == cs[k]
    &&& forall|k: int| 0 <= k < cs.len() ==> #[trigger] sub_match(c, cs[k], subs[k] as int)
    &&& forall|k: int| 0 <= k < cs.len() ==> #[trigger] coeffs[k] as int == coeff(c, cs[k])
}

// ------------------------------------------------------------------------------------------------ answer rows

/// `num` row `j` is in the `(adsh, tag)` group of row `i` among the `uom = $1` rows.
pub open spec fn mate(c: Ctx, i: int, j: int) -> bool {
    uom_text(c, j) == c.pv && adsh_text(c, j) == adsh_text(c, i) && tag_text(c, j) == tag_text(c, i)
}

/// Row `i` has the largest coefficient of its group.
pub open spec fn gmax(c: Ctx, i: int) -> bool {
    forall|j: int| 0 <= j < c.n && #[trigger] mate(c, i, j) ==> coeff(c, j) <= coeff(c, i)
}

/// Row `i` gives an answer row: `uom = $1`, a matching `sub` row, the maximum of its group.
pub open spec fn body_ok(c: Ctx, i: int) -> bool {
    uom_text(c, i) == c.pv && has_sub(c, i) && gmax(c, i)
}

/// The `sub` rows' adsh identify them (the declared primary key of `sub`).
pub open spec fn sub_key(c: Ctx) -> bool {
    forall|s1: int, s2: int| 0 <= s1 < c.m && 0 <= s2 < c.m && #[trigger] sadsh_text(c, s1) == #[trigger] sadsh_text(c, s2) ==> s1 == s2
}

// ------------------------------------------------------------------------------------------------ predicates

/// Coefficient at least `t`.
pub open spec fn ge_thr(c: Ctx, t: int) -> spec_fn(int) -> bool {
    |x: int| coeff(c, x) >= t
}

/// Coefficient below `t`.
pub open spec fn lt_thr(c: Ctx, t: int) -> spec_fn(int) -> bool {
    |x: int| coeff(c, x) < t
}

/// Has a matching `sub` row.
pub open spec fn has_sub_p(c: Ctx) -> spec_fn(int) -> bool {
    |x: int| has_sub(c, x)
}

/// Gives an answer row.
pub open spec fn body_p(c: Ctx) -> spec_fn(int) -> bool {
    |x: int| body_ok(c, x)
}

// ------------------------------------------------------------------------------------------------ lemmas

pub proof fn lemma_num_text_wf(c: Ctx)
    requires ctx_ok(c),
    ensures
        text_wf(uom_view(c.np), c.n),
        text_wf(adsh_view(c.np), c.n),
        text_wf(tag_view(c.np), c.n),
        coeff_seq(c.np).len() == c.n,
        text_wf(sadsh_view(c.sp), c.m),
        text_wf(sname_view(c.sp), c.m),
        fy_seq(c.sp).len() == c.m,
        fy_valid_seq(c.sp).len() == c.m,
{
    reveal(ctx_ok);
}

pub proof fn lemma_filter_push(s: Seq<int>, x: int, f: spec_fn(int) -> bool)
    ensures s.push(x).filter(f) == if f(x) { s.filter(f).push(x) } else { s.filter(f) },
{
    reveal(Seq::filter);
    assert(s.push(x).drop_last() =~= s);
}

/// A filter that rejects some element is shorter.
pub proof fn lemma_filter_drops(s: Seq<int>, f: spec_fn(int) -> bool, k: int)
    requires 0 <= k < s.len(), !f(s[k]),
    ensures s.filter(f).len() < s.len(),
    decreases s.len(),
{
    let d = s.drop_last();
    assert(d.push(s.last()) =~= s);
    lemma_filter_push(d, s.last(), f);
    lemma_filter_len_le(d, f);
    if k < s.len() - 1 {
        assert(d[k] == s[k]);
        lemma_filter_drops(d, f, k);
    }
}

/// A filter is at most as long as its input.
pub proof fn lemma_filter_len_le(s: Seq<int>, f: spec_fn(int) -> bool)
    ensures s.filter(f).len() <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert(d.push(s.last()) =~= s);
        lemma_filter_push(d, s.last(), f);
        lemma_filter_len_le(d, f);
    } else {
        reveal(Seq::filter);
    }
}

/// One more row.
pub proof fn lemma_cands_step(c: Ctx, lo: int, i: int, thr: int)
    requires lo <= i,
    ensures cands(c, lo, i + 1, thr) == if cand(c, i, thr) { cands(c, lo, i, thr).push(i) } else { cands(c, lo, i, thr) },
{
}

/// Raising the threshold filters the candidates.
pub proof fn lemma_cands_raise(c: Ctx, lo: int, hi: int, t1: int, t2: int)
    requires t1 <= t2,
    ensures cands(c, lo, hi, t1).filter(ge_thr(c, t2)) == cands(c, lo, hi, t2),
    decreases hi - lo,
{
    if hi > lo {
        lemma_cands_raise(c, lo, hi - 1, t1, t2);
        lemma_filter_push(cands(c, lo, hi - 1, t1), hi - 1, ge_thr(c, t2));
    } else {
        reveal(Seq::filter);
    }
}

/// The candidates of `lo..hi` lie in `lo..hi`, in increasing order.
pub proof fn lemma_cands_range(c: Ctx, lo: int, hi: int, thr: int, k: int)
    requires 0 <= k < cands(c, lo, hi, thr).len(),
    ensures
        lo <= cands(c, lo, hi, thr)[k] < hi,
        cand(c, cands(c, lo, hi, thr)[k], thr),
    decreases hi - lo,
{
    if hi > lo {
        let p = cands(c, lo, hi - 1, thr);
        if k < p.len() {
            lemma_cands_range(c, lo, hi - 1, thr, k);
        }
    }
}

/// A row of `lo..hi` that is a candidate is in the candidate list.
pub proof fn lemma_cands_contains(c: Ctx, lo: int, hi: int, thr: int, j: int)
    requires lo <= j < hi, cand(c, j, thr),
    ensures cands(c, lo, hi, thr).contains(j),
    decreases hi - lo,
{
    let p = cands(c, lo, hi - 1, thr);
    if j == hi - 1 {
        assert(cands(c, lo, hi, thr) == p.push(j));
        assert(p.push(j)[p.len() as int] == j);
    } else {
        lemma_cands_contains(c, lo, hi - 1, thr, j);
        let k = choose|k: int| 0 <= k < p.len() && p[k] == j;
        if cand(c, hi - 1, thr) {
            assert(cands(c, lo, hi, thr)[k] == j);
        }
    }
}

/// Every element of a filter comes from the source.
pub proof fn lemma_filter_source(s: Seq<int>, f: spec_fn(int) -> bool, k: int)
    requires 0 <= k < s.filter(f).len(),
    ensures exists|j: int| 0 <= j < s.len() && s[j] == s.filter(f)[k],
    decreases s.len(),
{
    let d = s.drop_last();
    assert(d.push(s.last()) =~= s);
    lemma_filter_push(d, s.last(), f);
    if k < d.filter(f).len() {
        lemma_filter_source(d, f, k);
        let j = choose|j: int| 0 <= j < d.len() && d[j] == d.filter(f)[k];
        assert(s[j] == d[j]);
    } else {
        assert(s[s.len() - 1] == s.filter(f)[k]);
    }
}

/// Filtering by `f` and then by a stronger `g` is filtering by `g`.
pub proof fn lemma_filter_implied(s: Seq<int>, f: spec_fn(int) -> bool, g: spec_fn(int) -> bool)
    requires forall|x: int| #[trigger] g(x) ==> f(x),
    ensures s.filter(f).filter(g) == s.filter(g),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert(d.push(s.last()) =~= s);
        lemma_filter_push(d, s.last(), f);
        lemma_filter_push(d, s.last(), g);
        lemma_filter_push(d.filter(f), s.last(), g);
        lemma_filter_implied(d, f, g);
    } else {
        reveal(Seq::filter);
    }
}

/// Adjacent ranges concatenate.
pub proof fn lemma_cands_append(c: Ctx, lo: int, mid: int, hi: int, thr: int)
    requires lo <= mid <= hi,
    ensures cands(c, lo, mid, thr) + cands(c, mid, hi, thr) == cands(c, lo, hi, thr),
    decreases hi - mid,
{
    if hi > mid {
        lemma_cands_append(c, lo, mid, hi - 1, thr);
        assert((cands(c, lo, mid, thr) + cands(c, mid, hi - 1, thr)).push(hi - 1)
            =~= cands(c, lo, mid, thr) + cands(c, mid, hi - 1, thr).push(hi - 1));
    } else {
        assert(cands(c, lo, mid, thr) + Seq::<int>::empty() =~= cands(c, lo, mid, thr));
    }
}

} // verus!
