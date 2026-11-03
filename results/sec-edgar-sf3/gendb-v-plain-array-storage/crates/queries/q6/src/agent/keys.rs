//! The hashes and partition of the qualifying `pre` rows (the entries) and of their keys.
//!
//! An entry is a `pre` row `k` with `pre_ok`; its member is `sub_for(adsh)`. Its join key is (member, tag,
//! version), hashed by `kh_spec` over (tag, adsh, version); its GROUP BY key is (member's name, tag, plabel), hashed by `gh_spec`. Entries,
//! join keys, group keys and the `num` rows probing them are partitioned by the top `pbits` bits of the tag's
//! signature (`tpart`): both keys contain the tag, so a key and everything that matches it lie in one partition.
//! `elist`/`plist` are the entries of a row range (of one partition), in row order.
use vstd::prelude::*;
use crate::agent::common::bytes::*;
use crate::agent::ctx::*;

verus! {

/// The hash of a `NULL` plabel.
pub const LH_NULL: u64 = 0x5555_5555_5555_5555u64;

/// Largest partition exponent (64 partitions).
pub const MAX_PBITS: u64 = 6;

/// The partition of a tag.
pub open spec fn tpart(t: Seq<u8>, pbits: u64) -> int {
    if pbits == 0 { 0 } else { (sig_spec(t) >> ((64 - pbits) as u64)) as int }
}

/// The hash of a join key (tag hash, member, version hash).
pub open spec fn kh_spec(th: u64, s: int, vh: u64) -> u64 {
    mix_spec(mix_spec(th, s as u64), vh)
}

/// The hash of the GROUP BY key of `pre` row `k` with member `s`.
pub open spec fn gh_spec(c: Ctx, s: int, k: int) -> u64 {
    mix_spec(mix_spec(sig_spec(p_tag(c, k)), sig_spec(s_name(c, s))),
        if p_plabelv_s(c)[k] != 0 { sig_spec(p_plabel(c, k)) } else { LH_NULL })
}

/// The member of entry `k`.
pub open spec fn esub(c: Ctx, k: int) -> int {
    sub_for(c, p_adsh(c, k))
}

/// The hash of entry `k`'s join key, over its adsh bytes (equal adsh and equal member are the same thing for
/// entries and the `num` rows that match them).
pub open spec fn ekh(c: Ctx, k: int) -> u64 {
    kh_spec(sig_spec(p_tag(c, k)), sig_spec(p_adsh(c, k)) as int, sig_spec(p_ver(c, k)))
}

pub open spec fn egh(c: Ctx, k: int) -> u64 {
    gh_spec(c, esub(c, k), k)
}

pub open spec fn epart(c: Ctx, pbits: u64, k: int) -> int {
    tpart(p_tag(c, k), pbits)
}

/// The entries among `pre` rows `lo..hi`, in row order.
pub open spec fn elist(c: Ctx, lo: int, hi: int) -> Seq<int>
    decreases hi - lo,
{
    if hi <= lo {
        Seq::empty()
    } else {
        let d = elist(c, lo, hi - 1);
        if pre_ok(c, hi - 1) { d.push(hi - 1) } else { d }
    }
}

/// The entries of partition `p` among `pre` rows `lo..hi`, in row order.
pub open spec fn plist(c: Ctx, pbits: u64, p: int, lo: int, hi: int) -> Seq<int>
    decreases hi - lo,
{
    if hi <= lo {
        Seq::empty()
    } else {
        let d = plist(c, pbits, p, lo, hi - 1);
        if pre_ok(c, hi - 1) && epart(c, pbits, hi - 1) == p { d.push(hi - 1) } else { d }
    }
}

/// The partition of a tag hash (top `pbits` bits), below `2^pbits`.
#[inline(always)]
pub fn part_of(th: u64, pbits: u64, Ghost(t): Ghost<Seq<u8>>) -> (r: usize)
    requires pbits <= MAX_PBITS, th == sig_spec(t),
    ensures r as int == tpart(t, pbits), r < 64, (r as int) < pow2u(pbits),
    no_unwind
{
    if pbits == 0 {
        proof {
            assert(pow2u(0) == 1);
        }
        0
    } else {
        let sh: u64 = 64 - pbits;
        proof {
            lemma_pow2u(pbits);
            assert(th >> sh < (1u64 << pbits)) by (bit_vector) requires 1 <= pbits <= 6, sh == 64 - pbits;
            assert((1u64 << pbits) <= 64) by (bit_vector) requires 1 <= pbits <= 6;
        }
        (th >> sh) as usize
    }
}

/// `2^b` (as an integer).
pub open spec fn pow2u(b: u64) -> int
    decreases b,
{
    if b == 0 { 1 } else { 2 * pow2u((b - 1) as u64) }
}

pub proof fn lemma_pow2u(b: u64)
    requires b <= 6,
    ensures pow2u(b) == (1u64 << b) as int, 1 <= pow2u(b) <= 64,
    decreases b,
{
    if b > 0 {
        lemma_pow2u((b - 1) as u64);
        let b1 = (b - 1) as u64;
        assert((1u64 << b) == 2 * (1u64 << b1)) by (bit_vector) requires 1 <= b <= 6, b1 == b - 1;
    } else {
        assert((1u64 << 0u64) == 1) by (bit_vector);
    }
    assert(1 <= (1u64 << b) <= 64) by (bit_vector) requires b <= 6;
}

/// `kh_spec`.
#[inline(always)]
pub fn kh(th: u64, s: usize, vh: u64) -> (r: u64)
    ensures r == kh_spec(th, s as int, vh),
    no_unwind
{
    mix(mix(th, s as u64), vh)
}

/// `kh_spec` over an adsh hash.
#[inline(always)]
pub fn kha(th: u64, ah: u64, vh: u64) -> (r: u64)
    ensures r == kh_spec(th, ah as int, vh),
    no_unwind
{
    mix(mix(th, ah), vh)
}

/// The entries of `lo..hi + 1`.
pub proof fn lemma_elist_step(c: Ctx, lo: int, hi: int)
    requires lo <= hi,
    ensures elist(c, lo, hi + 1) == if pre_ok(c, hi) { elist(c, lo, hi).push(hi) } else { elist(c, lo, hi) },
{
}

/// The entries of a range lie in it, increasing.
pub proof fn lemma_elist_range(c: Ctx, lo: int, hi: int, j: int)
    requires 0 <= j < elist(c, lo, hi).len(),
    ensures lo <= elist(c, lo, hi)[j] < hi, pre_ok(c, elist(c, lo, hi)[j]),
    decreases hi - lo,
{
    if hi > lo {
        let d = elist(c, lo, hi - 1);
        if j < d.len() {
            lemma_elist_range(c, lo, hi - 1, j);
        }
    }
}

/// At most one entry per row.
pub proof fn lemma_elist_len(c: Ctx, lo: int, hi: int)
    requires lo <= hi,
    ensures elist(c, lo, hi).len() <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_elist_len(c, lo, hi - 1);
    }
}

} // verus!
