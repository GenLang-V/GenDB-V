//! The call's context (the stored parts of `num`, `pre`, `sub`, `tag` and the binding) and the row-level normal
//! form the engine computes:
//!
//! - `qual(c, i)`: `num` row `i` passes `uom = $1 AND ddate BETWEEN $2 AND $3` (`value IS NOT NULL` always holds:
//!   the column is NOT NULL);
//! - `matched(c, i)`: some `pre` row has the same `(tag, version, adsh)` (the LEFT JOIN finds a partner);
//! - `keep(c, i)`: `qual && !matched`, the rows the WHERE keeps (`p.adsh IS NULL` holds exactly for unmatched rows);
//! - `keep_rows(c, k)`: the kept rows among `0..k`, in row order.
//!
//! Key hashes: `tv_hash` of `(tag, version)` (always odd, so 0 marks an empty table slot) and `ad_hash` of `adsh`.
//! `fk_ok` states the declared foreign keys on the parts (every `num` and `pre` row's `(tag, version)` is a `tag`
//! row's and its `adsh` a `sub` row's); `tv_injective` / `ad_injective` state that the hashes separate the `tag`
//! and `sub` values. Under these three, equal hash pairs mean equal keys (`lemma_pair_eq_key`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::link::query::{text_at, text_wf, TextView};
use crate::stores::flat_num::interface as ni;
use crate::stores::flat_pre::interface as pi;
use crate::stores::flat_sub::interface as si;
use crate::stores::flat_tag::interface as ti;
use crate::agent::hash::*;

verus! {

/// The parts of the four tables (row counts `n`, `m`, `ns`, `nt`) and the binding `$1 = pv`, `$2 = dlo`,
/// `$3 = dhi`.
pub struct Ctx {
    pub np: Seq<PartView>,
    pub n: int,
    pub pp: Seq<PartView>,
    pub m: int,
    pub sp: Seq<PartView>,
    pub ns: int,
    pub tp: Seq<PartView>,
    pub nt: int,
    pub pv: Seq<u8>,
    pub dlo: int,
    pub dhi: int,
}

pub open spec fn ctx_ok(c: Ctx) -> bool {
    &&& c.n >= 0 && c.m >= 0 && c.ns >= 0 && c.nt >= 0
    &&& ni::parts_wf(c.np, c.n)
    &&& pi::parts_wf(c.pp, c.m)
    &&& si::parts_wf(c.sp, c.ns)
    &&& ti::parts_wf(c.tp, c.nt)
}

// ------------------------------------------------------------------------------------------------ text columns

pub open spec fn ntag_v(c: Ctx) -> TextView { ni::text_view(c.np, ni::TAG_OFFSETS as int, ni::TAG_BYTES as int) }
pub open spec fn nver_v(c: Ctx) -> TextView { ni::text_view(c.np, ni::VERSION_OFFSETS as int, ni::VERSION_BYTES as int) }
pub open spec fn nadsh_v(c: Ctx) -> TextView { ni::text_view(c.np, ni::ADSH_OFFSETS as int, ni::ADSH_BYTES as int) }
pub open spec fn nuom_v(c: Ctx) -> TextView { ni::text_view(c.np, ni::UOM_OFFSETS as int, ni::UOM_BYTES as int) }
pub open spec fn ptag_v(c: Ctx) -> TextView { pi::text_view(c.pp, pi::TAG_OFFSETS as int, pi::TAG_BYTES as int) }
pub open spec fn pver_v(c: Ctx) -> TextView { pi::text_view(c.pp, pi::VERSION_OFFSETS as int, pi::VERSION_BYTES as int) }
pub open spec fn padsh_v(c: Ctx) -> TextView { pi::text_view(c.pp, pi::ADSH_OFFSETS as int, pi::ADSH_BYTES as int) }
pub open spec fn sadsh_v(c: Ctx) -> TextView { si::text_view(c.sp, si::ADSH_OFFSETS as int, si::ADSH_BYTES as int) }
pub open spec fn ttag_v(c: Ctx) -> TextView { ti::text_view(c.tp, ti::TAG_OFFSETS as int, ti::TAG_BYTES as int) }
pub open spec fn tver_v(c: Ctx) -> TextView { ti::text_view(c.tp, ti::VERSION_OFFSETS as int, ti::VERSION_BYTES as int) }

pub open spec fn ntag(c: Ctx, i: int) -> Seq<u8> { text_at(ntag_v(c), i) }
pub open spec fn nver(c: Ctx, i: int) -> Seq<u8> { text_at(nver_v(c), i) }
pub open spec fn nadsh(c: Ctx, i: int) -> Seq<u8> { text_at(nadsh_v(c), i) }
pub open spec fn nuom(c: Ctx, i: int) -> Seq<u8> { text_at(nuom_v(c), i) }
pub open spec fn ptag(c: Ctx, j: int) -> Seq<u8> { text_at(ptag_v(c), j) }
pub open spec fn pver(c: Ctx, j: int) -> Seq<u8> { text_at(pver_v(c), j) }
pub open spec fn padsh(c: Ctx, j: int) -> Seq<u8> { text_at(padsh_v(c), j) }
pub open spec fn sadsh(c: Ctx, s: int) -> Seq<u8> { text_at(sadsh_v(c), s) }
pub open spec fn ttag(c: Ctx, a: int) -> Seq<u8> { text_at(ttag_v(c), a) }
pub open spec fn tver(c: Ctx, a: int) -> Seq<u8> { text_at(tver_v(c), a) }

/// `num.ddate` of row `i` (days are not involved: `ddate` is a plain integer column).
pub open spec fn ddate(c: Ctx, i: int) -> int { ni::i32s(c.np[ni::DDATE as int])[i] as int }

/// `num.value` coefficient of row `i` (scale 4).
pub open spec fn coeff(c: Ctx, i: int) -> int { ni::i128s(c.np[ni::VALUE as int])[i] as int }

pub proof fn lemma_text_cols_wf(c: Ctx)
    requires ctx_ok(c),
    ensures
        text_wf(ntag_v(c), c.n), text_wf(nver_v(c), c.n), text_wf(nadsh_v(c), c.n), text_wf(nuom_v(c), c.n),
        text_wf(ptag_v(c), c.m), text_wf(pver_v(c), c.m), text_wf(padsh_v(c), c.m),
        text_wf(sadsh_v(c), c.ns), text_wf(ttag_v(c), c.nt), text_wf(tver_v(c), c.nt),
        ni::i32s(c.np[ni::DDATE as int]).len() == c.n,
        ni::i128s(c.np[ni::VALUE as int]).len() == c.n,
{
}

// ------------------------------------------------------------------------------------------------ row predicates

/// WHERE on `num` alone: `uom = $1 AND ddate BETWEEN $2 AND $3`.
pub open spec fn qual(c: Ctx, i: int) -> bool {
    nuom(c, i) == c.pv && c.dlo <= ddate(c, i) <= c.dhi
}

/// `pre` row `j` has `num` row `i`'s `(tag, version, adsh)`.
pub open spec fn same_key(c: Ctx, i: int, j: int) -> bool {
    ptag(c, j) == ntag(c, i) && pver(c, j) == nver(c, i) && padsh(c, j) == nadsh(c, i)
}

/// The LEFT JOIN finds a `pre` partner for `num` row `i`.
pub open spec fn matched(c: Ctx, i: int) -> bool {
    exists|j: int| 0 <= j < c.m && #[trigger] same_key(c, i, j)
}

/// The rows the WHERE keeps: qualifying and without partner (`p.adsh IS NULL`).
pub open spec fn keep(c: Ctx, i: int) -> bool {
    qual(c, i) && !matched(c, i)
}

/// The kept rows of `lo..hi`, in row order.
pub open spec fn keep_range(c: Ctx, lo: int, hi: int) -> Seq<int>
    decreases hi - lo,
{
    if hi <= lo {
        Seq::empty()
    } else if keep(c, hi - 1) {
        keep_range(c, lo, hi - 1).push(hi - 1)
    } else {
        keep_range(c, lo, hi - 1)
    }
}

/// The kept rows of `lo..mid` then `mid..hi` are the kept rows of `lo..hi`.
pub proof fn lemma_keep_range_split(c: Ctx, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures keep_range(c, lo, mid) + keep_range(c, mid, hi) == keep_range(c, lo, hi),
    decreases hi - mid,
{
    if hi == mid {
        assert(keep_range(c, mid, hi) =~= Seq::<int>::empty());
        assert(keep_range(c, lo, mid) + Seq::<int>::empty() =~= keep_range(c, lo, mid));
    } else {
        lemma_keep_range_split(c, lo, mid, hi - 1);
        if keep(c, hi - 1) {
            assert(keep_range(c, lo, mid) + keep_range(c, mid, hi - 1).push(hi - 1)
                =~= (keep_range(c, lo, mid) + keep_range(c, mid, hi - 1)).push(hi - 1));
        }
    }
}

/// Every element of `keep_range(c, lo, hi)` is a kept row of `lo..hi`, and the elements increase.
pub proof fn lemma_keep_range_elems(c: Ctx, lo: int, hi: int)
    ensures
        forall|q: int| 0 <= q < keep_range(c, lo, hi).len() ==>
            lo <= #[trigger] keep_range(c, lo, hi)[q] < hi && keep(c, keep_range(c, lo, hi)[q]),
    decreases hi - lo,
{
    if hi > lo {
        lemma_keep_range_elems(c, lo, hi - 1);
        let s = keep_range(c, lo, hi);
        let d = keep_range(c, lo, hi - 1);
        assert forall|q: int| 0 <= q < s.len() implies lo <= #[trigger] s[q] < hi && keep(c, s[q]) by {
            if q < d.len() {
                assert(s[q] == d[q]);
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ key hashes

/// Hash of a `(tag, version)` value; odd, so it is never the empty-slot marker 0.
pub open spec fn tv_hash(tag: Seq<u8>, ver: Seq<u8>) -> u64 {
    hash_text(ver, hash_text(tag, SEED_TAG)) | 1u64
}

/// Hash of an `adsh` value; odd, like `tv_hash`.
pub open spec fn ad_hash(adsh: Seq<u8>) -> u64 {
    hash_text(adsh, SEED_ADSH) | 1u64
}

pub open spec fn num_tv(c: Ctx, i: int) -> u64 { tv_hash(ntag(c, i), nver(c, i)) }
pub open spec fn num_ad(c: Ctx, i: int) -> u64 { ad_hash(nadsh(c, i)) }
pub open spec fn pre_tv(c: Ctx, j: int) -> u64 { tv_hash(ptag(c, j), pver(c, j)) }
pub open spec fn pre_ad(c: Ctx, j: int) -> u64 { ad_hash(padsh(c, j)) }
pub open spec fn tag_tv(c: Ctx, a: int) -> u64 { tv_hash(ttag(c, a), tver(c, a)) }
pub open spec fn sub_ad(c: Ctx, s: int) -> u64 { ad_hash(sadsh(c, s)) }

/// `(tag, version)` is the value of some `tag` row.
pub open spec fn in_tag(c: Ctx, tag: Seq<u8>, ver: Seq<u8>) -> bool {
    exists|a: int| 0 <= a < c.nt && #[trigger] ttag(c, a) == tag && tver(c, a) == ver
}

/// `adsh` is the value of some `sub` row.
pub open spec fn in_sub(c: Ctx, adsh: Seq<u8>) -> bool {
    exists|s: int| 0 <= s < c.ns && #[trigger] sadsh(c, s) == adsh
}

/// The declared foreign keys of `num` row `i`.
pub open spec fn num_fk(c: Ctx, i: int) -> bool {
    in_tag(c, ntag(c, i), nver(c, i)) && in_sub(c, nadsh(c, i))
}

/// The declared foreign keys of `pre` row `j`.
pub open spec fn pre_fk(c: Ctx, j: int) -> bool {
    in_tag(c, ptag(c, j), pver(c, j)) && in_sub(c, padsh(c, j))
}

/// The declared foreign keys, on the parts: `num.(tag, version)` and `pre.(tag, version)` are `tag` values,
/// `num.adsh` and `pre.adsh` are `sub` values.
pub open spec fn fk_ok(c: Ctx) -> bool {
    &&& forall|i: int| 0 <= i < c.n ==> #[trigger] num_fk(c, i)
    &&& forall|j: int| 0 <= j < c.m ==> #[trigger] pre_fk(c, j)
}

/// `tv_hash` separates the `(tag, version)` values of the `tag` table.
pub open spec fn tv_injective(c: Ctx) -> bool {
    forall|a: int, b: int| 0 <= a < c.nt && 0 <= b < c.nt && #[trigger] tag_tv(c, a) == #[trigger] tag_tv(c, b)
        ==> ttag(c, a) == ttag(c, b) && tver(c, a) == tver(c, b)
}

/// `ad_hash` separates the `adsh` values of the `sub` table.
pub open spec fn ad_injective(c: Ctx) -> bool {
    forall|s: int, t: int| 0 <= s < c.ns && 0 <= t < c.ns && #[trigger] sub_ad(c, s) == #[trigger] sub_ad(c, t)
        ==> sadsh(c, s) == sadsh(c, t)
}

/// Under the foreign keys and the two separations, a `num` row and a `pre` row with equal hash pairs have equal
/// keys; equal keys always give equal hash pairs.
pub proof fn lemma_pair_eq_key(c: Ctx, i: int, j: int)
    requires
        0 <= i < c.n, 0 <= j < c.m,
        fk_ok(c), tv_injective(c), ad_injective(c),
    ensures
        (num_tv(c, i) == pre_tv(c, j) && num_ad(c, i) == pre_ad(c, j)) <==> same_key(c, i, j),
{
    if num_tv(c, i) == pre_tv(c, j) && num_ad(c, i) == pre_ad(c, j) {
        assert(num_fk(c, i) && pre_fk(c, j));
        let a = choose|a: int| 0 <= a < c.nt && #[trigger] ttag(c, a) == ntag(c, i) && tver(c, a) == nver(c, i);
        let b = choose|b: int| 0 <= b < c.nt && #[trigger] ttag(c, b) == ptag(c, j) && tver(c, b) == pver(c, j);
        assert(tag_tv(c, a) == tag_tv(c, b));
        let s = choose|s: int| 0 <= s < c.ns && #[trigger] sadsh(c, s) == nadsh(c, i);
        let t = choose|t: int| 0 <= t < c.ns && #[trigger] sadsh(c, t) == padsh(c, j);
        assert(sub_ad(c, s) == sub_ad(c, t));
    }
}

} // verus!
