//! The ghost context of one call and the query's normal form over the flat parts.
//!
//! `Ctx` holds the parts of `num` (`np`, `n` rows), `sub` (`sp`, `m` rows) and `pre` (`pp`, `q` rows) and the
//! binding `$1 = uom`, `$2 = stmt`, `$3 = fy`. Row-level conditions:
//! - `member(s)`: `sub` row `s` has a non-NULL `fy` equal to `$3`;
//! - `pre_ok(k)`: `pre` row `k` has a non-NULL `stmt` equal to `$2` and its `adsh` is the `adsh` of a member;
//! - `num_ok(i)`: `num` row `i` has `uom = $1` (its value is never NULL);
//! - `nmatch(i, k)`: both hold and `num` row `i` has `pre` row `k`'s `adsh`, `tag` and `version`.
//!
//! Accumulators (`sel`: 0 counts, 1 sums the value coefficient, 2 sums its absolute value):
//! - `acc(sel, k, hi)`: over the `num` rows `0..hi` matching `pre` row `k`;
//! - `gacc(sel, key, hi)`: over the `pre` rows `0..hi` with `pre_ok` and group key `key`, of their `acc` over all
//!   of `num`. The statement's GROUP BY accumulators are these (`agent::sem`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::link::query::{text_at, text_wf, TextView};
use crate::spec::value::{Row, Val};
use crate::spec::numeric::abs;
use crate::stores::flat_num::interface as ni;
use crate::stores::flat_sub::interface as si;
use crate::stores::flat_pre::interface as pi;

verus! {

/// The ghost context of one call.
pub ghost struct Ctx {
    pub np: Seq<PartView>,
    pub n: int,
    pub sp: Seq<PartView>,
    pub m: int,
    pub pp: Seq<PartView>,
    pub q: int,
    pub uom: Seq<u8>,
    pub stmt: Seq<u8>,
    pub fy: int,
}

/// The parts of the three tables are well formed for their row counts.
#[verifier::opaque]
pub open spec fn ctx_ok(c: Ctx) -> bool {
    &&& ni::parts_wf(c.np, c.n)
    &&& si::parts_wf(c.sp, c.m)
    &&& pi::parts_wf(c.pp, c.q)
}

// ------------------------------------------------------------------------------------------------ column views

pub open spec fn n_adsh_v(c: Ctx) -> TextView { ni::text_view(c.np, ni::ADSH_OFFSETS as int, ni::ADSH_BYTES as int) }
pub open spec fn n_tag_v(c: Ctx) -> TextView { ni::text_view(c.np, ni::TAG_OFFSETS as int, ni::TAG_BYTES as int) }
pub open spec fn n_ver_v(c: Ctx) -> TextView { ni::text_view(c.np, ni::VERSION_OFFSETS as int, ni::VERSION_BYTES as int) }
pub open spec fn n_uom_v(c: Ctx) -> TextView { ni::text_view(c.np, ni::UOM_OFFSETS as int, ni::UOM_BYTES as int) }
pub open spec fn n_val_s(c: Ctx) -> Seq<i128> { ni::i128s(c.np[ni::VALUE as int]) }

pub open spec fn s_adsh_v(c: Ctx) -> TextView { si::text_view(c.sp, si::ADSH_OFFSETS as int, si::ADSH_BYTES as int) }
pub open spec fn s_name_v(c: Ctx) -> TextView { si::text_view(c.sp, si::NAME_OFFSETS as int, si::NAME_BYTES as int) }
pub open spec fn s_fy_s(c: Ctx) -> Seq<i32> { si::i32s(c.sp[si::FY as int]) }
pub open spec fn s_fyv_s(c: Ctx) -> Seq<u8> { si::u8s(c.sp[si::FY_VALIDITY as int]) }

pub open spec fn p_adsh_v(c: Ctx) -> TextView { pi::text_view(c.pp, pi::ADSH_OFFSETS as int, pi::ADSH_BYTES as int) }
pub open spec fn p_stmt_v(c: Ctx) -> TextView { pi::text_view(c.pp, pi::STMT_OFFSETS as int, pi::STMT_BYTES as int) }
pub open spec fn p_stmtv_s(c: Ctx) -> Seq<u8> { pi::u8s(c.pp[pi::STMT_VALIDITY as int]) }
pub open spec fn p_tag_v(c: Ctx) -> TextView { pi::text_view(c.pp, pi::TAG_OFFSETS as int, pi::TAG_BYTES as int) }
pub open spec fn p_ver_v(c: Ctx) -> TextView { pi::text_view(c.pp, pi::VERSION_OFFSETS as int, pi::VERSION_BYTES as int) }
pub open spec fn p_plabel_v(c: Ctx) -> TextView { pi::text_view(c.pp, pi::PLABEL_OFFSETS as int, pi::PLABEL_BYTES as int) }
pub open spec fn p_plabelv_s(c: Ctx) -> Seq<u8> { pi::u8s(c.pp[pi::PLABEL_VALIDITY as int]) }

pub open spec fn n_adsh(c: Ctx, i: int) -> Seq<u8> { text_at(n_adsh_v(c), i) }
pub open spec fn n_tag(c: Ctx, i: int) -> Seq<u8> { text_at(n_tag_v(c), i) }
pub open spec fn n_ver(c: Ctx, i: int) -> Seq<u8> { text_at(n_ver_v(c), i) }
pub open spec fn n_uom(c: Ctx, i: int) -> Seq<u8> { text_at(n_uom_v(c), i) }
/// The `value` coefficient of `num` row `i` (scale 4).
pub open spec fn n_val(c: Ctx, i: int) -> int { n_val_s(c)[i] as int }

pub open spec fn s_adsh(c: Ctx, s: int) -> Seq<u8> { text_at(s_adsh_v(c), s) }
pub open spec fn s_name(c: Ctx, s: int) -> Seq<u8> { text_at(s_name_v(c), s) }

pub open spec fn p_adsh(c: Ctx, k: int) -> Seq<u8> { text_at(p_adsh_v(c), k) }
pub open spec fn p_stmt(c: Ctx, k: int) -> Seq<u8> { text_at(p_stmt_v(c), k) }
pub open spec fn p_tag(c: Ctx, k: int) -> Seq<u8> { text_at(p_tag_v(c), k) }
pub open spec fn p_ver(c: Ctx, k: int) -> Seq<u8> { text_at(p_ver_v(c), k) }
pub open spec fn p_plabel(c: Ctx, k: int) -> Seq<u8> { text_at(p_plabel_v(c), k) }

/// `plabel` of `pre` row `k` as a value: NULL when its validity byte is 0.
pub open spec fn p_plabel_val(c: Ctx, k: int) -> Val {
    if p_plabelv_s(c)[k] == 0 { Val::Null } else { Val::Text(p_plabel(c, k)) }
}

// ------------------------------------------------------------------------------------------------ conditions

/// `sub` row `s` exists and its `fy` is not NULL and equals `$3`.
pub open spec fn member(c: Ctx, s: int) -> bool {
    0 <= s < c.m && s_fyv_s(c)[s] != 0 && s_fy_s(c)[s] as int == c.fy
}

/// Some member has `adsh` `a`.
pub open spec fn has_member(c: Ctx, a: Seq<u8>) -> bool {
    exists|s: int| #[trigger] member(c, s) && s_adsh(c, s) == a
}

/// A member with `adsh` `a` (the only one, by the key of `sub`).
pub open spec fn sub_for(c: Ctx, a: Seq<u8>) -> int {
    choose|s: int| #[trigger] member(c, s) && s_adsh(c, s) == a
}

/// `pre` row `k` qualifies: `stmt = $2` (not NULL) and its `adsh` is a member's.
pub open spec fn pre_ok(c: Ctx, k: int) -> bool {
    &&& 0 <= k < c.q
    &&& p_stmtv_s(c)[k] != 0
    &&& p_stmt(c, k) == c.stmt
    &&& has_member(c, p_adsh(c, k))
}

/// `num` row `i` qualifies: `uom = $1`.
pub open spec fn num_ok(c: Ctx, i: int) -> bool {
    0 <= i < c.n && n_uom(c, i) == c.uom
}

/// `num` row `i` joins `pre` row `k` and both qualify.
pub open spec fn nmatch(c: Ctx, i: int, k: int) -> bool {
    &&& num_ok(c, i)
    &&& pre_ok(c, k)
    &&& n_adsh(c, i) == p_adsh(c, k)
    &&& n_tag(c, i) == p_tag(c, k)
    &&& n_ver(c, i) == p_ver(c, k)
}

/// The weight of `num` row `i` in accumulator `sel`: 1, its coefficient, or the coefficient's absolute value.
pub open spec fn wt(c: Ctx, sel: int, i: int) -> int {
    if sel == 0 { 1 } else if sel == 1 { n_val(c, i) } else { abs(n_val(c, i)) }
}

/// Accumulator `sel` of `pre` row `k` over `num` rows `0..hi`.
pub open spec fn acc(c: Ctx, sel: int, k: int, hi: int) -> int
    decreases hi,
{
    if hi <= 0 { 0 } else { acc(c, sel, k, hi - 1) + if nmatch(c, hi - 1, k) { wt(c, sel, hi - 1) } else { 0 } }
}

/// The GROUP BY key of `pre` row `k` (with its member): `[sub.name, $2, tag, plabel]`.
pub open spec fn gkey(c: Ctx, k: int) -> Row {
    seq![Val::Text(s_name(c, sub_for(c, p_adsh(c, k)))), Val::Text(c.stmt), Val::Text(p_tag(c, k)), p_plabel_val(c, k)]
}

/// Accumulator `sel` of group `key` over `pre` rows `0..hi`.
pub open spec fn gacc(c: Ctx, sel: int, key: Row, hi: int) -> int
    decreases hi,
{
    if hi <= 0 {
        0
    } else {
        gacc(c, sel, key, hi - 1) + if pre_ok(c, hi - 1) && gkey(c, hi - 1) == key { acc(c, sel, hi - 1, c.n) } else { 0 }
    }
}

// ------------------------------------------------------------------------------------------------ basic facts

pub proof fn lemma_views_wf(c: Ctx)
    requires ctx_ok(c),
    ensures
        text_wf(n_adsh_v(c), c.n), text_wf(n_tag_v(c), c.n), text_wf(n_ver_v(c), c.n), text_wf(n_uom_v(c), c.n),
        n_val_s(c).len() == c.n,
        text_wf(s_adsh_v(c), c.m), text_wf(s_name_v(c), c.m), s_fy_s(c).len() == c.m, s_fyv_s(c).len() == c.m,
        text_wf(p_adsh_v(c), c.q), text_wf(p_stmt_v(c), c.q), p_stmtv_s(c).len() == c.q,
        text_wf(p_tag_v(c), c.q), text_wf(p_ver_v(c), c.q), text_wf(p_plabel_v(c), c.q),
        p_plabelv_s(c).len() == c.q,
{
    reveal(ctx_ok);
}

/// The member found for `adsh` `a` is a member with that `adsh`.
pub proof fn lemma_sub_for(c: Ctx, a: Seq<u8>)
    requires has_member(c, a),
    ensures member(c, sub_for(c, a)), s_adsh(c, sub_for(c, a)) == a,
{
}

/// The weights of counts and absolute values are non-negative; `|value| <= abs weight`.
pub proof fn lemma_acc_nonneg(c: Ctx, sel: int, k: int, hi: int)
    requires sel == 0 || sel == 2,
    ensures acc(c, sel, k, hi) >= 0,
    decreases hi,
{
    if hi > 0 {
        lemma_acc_nonneg(c, sel, k, hi - 1);
    }
}

pub proof fn lemma_gacc_nonneg(c: Ctx, sel: int, key: Row, hi: int)
    requires sel == 0 || sel == 2,
    ensures gacc(c, sel, key, hi) >= 0,
    decreases hi,
{
    if hi > 0 {
        lemma_gacc_nonneg(c, sel, key, hi - 1);
        lemma_acc_nonneg(c, sel, hi - 1, c.n);
    }
}

} // verus!
