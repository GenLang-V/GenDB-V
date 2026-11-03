//! The statement's normal form over the flat parts (`cols::Ctx`): which rows of each table take part, the pre
//! entries (the pre rows that can match a num row), the contributions (one per pair of a num row and a matching
//! pre entry, in num row order, then pre row order) and the group key and aggregate arguments of a contribution.
//!
//! - a sub row is selected when its `sic` is not NULL and lies in `[$3, $4]`; by the sub key at most one sub row
//!   has a given adsh;
//! - a pre row is a candidate when `stmt = $2` and its adsh has a selected sub row, and selected when moreover
//!   its `(tag, version)` has a tag row with `abstract = 0` (unique by the tag key);
//! - a num row with `uom = $1` whose adsh has a selected sub row contributes once per selected pre row with its
//!   adsh, tag and version.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::agent::cols::*;

verus! {

// ------------------------------------------------------------------------------------------------ selections

/// Sub row `s` has `sic BETWEEN $3 AND $4` (so `sic` is not NULL).
pub open spec fn sub_sel(c: Ctx, s: int) -> bool {
    0 <= s < c.m && s_sic_valid(c, s) && c.lo <= s_sic(c, s) <= c.hi
}

/// Sub row `s` is selected and has adsh `a`.
pub open spec fn sub_of(c: Ctx, s: int, a: Seq<u8>) -> bool {
    sub_sel(c, s) && s_adsh(c, s) == a
}

/// Some selected sub row has adsh `a`.
pub open spec fn has_sub(c: Ctx, a: Seq<u8>) -> bool {
    exists|s: int| #[trigger] sub_of(c, s, a)
}

/// Tag row `k` has `abstract = 0`, tag `t` and version `v`.
pub open spec fn tag_of(c: Ctx, k: int, t: Seq<u8>, v: Seq<u8>) -> bool {
    0 <= k < c.nt && t_abs(c, k) == 0 && t_tag(c, k) == t && t_ver(c, k) == v
}

/// Some tag row with `abstract = 0` has tag `t` and version `v`.
pub open spec fn has_tag(c: Ctx, t: Seq<u8>, v: Seq<u8>) -> bool {
    exists|k: int| #[trigger] tag_of(c, k, t, v)
}

/// Pre row `l` has `stmt = $2` and an adsh with a selected sub row.
pub open spec fn pre_cand(c: Ctx, l: int) -> bool {
    0 <= l < c.npre && p_stmt_valid(c, l) && p_stmt(c, l) == c.stmt && has_sub(c, p_adsh(c, l))
}

/// Pre row `l` is a candidate whose `(tag, version)` has a tag row with `abstract = 0`.
pub open spec fn pre_sel(c: Ctx, l: int) -> bool {
    pre_cand(c, l) && has_tag(c, p_tag(c, l), p_ver(c, l))
}

/// The selected sub row of adsh `a` is unique.
pub proof fn lemma_sub_unique(c: Ctx, s1: int, s2: int, a: Seq<u8>)
    requires ctx_ok(c), sub_of(c, s1, a), sub_of(c, s2, a),
    ensures s1 == s2,
{
    lemma_keys(c);
}

/// The tag row of `(t, v)` is unique.
pub proof fn lemma_tag_unique(c: Ctx, k1: int, k2: int, t: Seq<u8>, v: Seq<u8>)
    requires ctx_ok(c), tag_of(c, k1, t, v), tag_of(c, k2, t, v),
    ensures k1 == k2,
{
    lemma_keys(c);
}

} // verus!
