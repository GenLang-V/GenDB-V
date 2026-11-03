//! The statement over the stored columns, one lineitem row at a time.
//!
//! A lineitem row `l` reaches its supplier, order and the order's customer through the key columns (`key_row`;
//! the primary keys make each one unique), and the supplier and customer reach their nations. A nation's *tag*
//! records which parameters its name equals: bit 0 (value 1) for `$1`, value 2 for `$2` (`name_tag`); a missing
//! nation has tag 0. Row `l` qualifies (`line_qual`) when its keys resolve, it ships in the window and the tags
//! match, i.e. the supplier's nation is `$1` and the customer's `$2` or the other way round (`tags_match`). Its
//! group (`line_grp`, 0..4) is `2 * [not (supplier $1 and customer $2)] + [ships in 1996]`, whose key is
//! `grp_key`. `lsum(g, w, lo, hi)` sums over the rows `lo..hi` of group `g` their count (`w == 0`), volume
//! (`w == 1`, `l_extendedprice * (100 - l_discount)` at scale 4) or absolute volume (`w == 2`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;
use crate::agent::normal_form::*;

verus! {

// ------------------------------------------------------------------------------------------------ key lookups

/// Some row of the key column holds `k`.
pub open spec fn has_key(keys: Seq<i64>, k: i64) -> bool {
    exists|j: int| 0 <= j < keys.len() && #[trigger] keys[j] == k
}

/// The row of the key column holding `k` (meaningful when `has_key`).
pub open spec fn key_row(keys: Seq<i64>, k: i64) -> int {
    choose|j: int| 0 <= j < keys.len() && #[trigger] keys[j] == k
}

/// The row holding `k` exists when some row holds it, and on a duplicate-free column it is the only one.
pub proof fn lemma_key_row(keys: Seq<i64>, k: i64)
    ensures
        has_key(keys, k) ==> 0 <= key_row(keys, k) < keys.len() && keys[key_row(keys, k)] == k,
        keys_unique(keys) ==> forall|j: int| 0 <= j < keys.len() && #[trigger] keys[j] == k ==> j == key_row(keys, k),
{
    if keys_unique(keys) {
        assert forall|j: int| 0 <= j < keys.len() && #[trigger] keys[j] == k implies j == key_row(keys, k) by {
            assert(has_key(keys, k));
            let r = key_row(keys, k);
            assert(keys[r] == keys[j]);
        }
    }
}

// ------------------------------------------------------------------------------------------------ nation tags

/// Which parameters nation row `a`'s name equals: 1 for `$1`, 2 for `$2` (3 for both).
pub open spec fn name_tag(sv: StoresView, ps: Seq<Literal>, a: int) -> int {
    (if nname(sv, a) == p1_of(ps) { 1int } else { 0int }) + (if nname(sv, a) == p2_of(ps) { 2int } else { 0int })
}

/// The tag of the nation with key `key` (0 when there is none).
pub open spec fn nat_tag(sv: StoresView, ps: Seq<Literal>, key: i64) -> int {
    if has_key(nk(sv), key) { name_tag(sv, ps, key_row(nk(sv), key)) } else { 0 }
}

/// The tag of supplier row `s`'s nation.
pub open spec fn supp_tag(sv: StoresView, ps: Seq<Literal>, s: int) -> int { nat_tag(sv, ps, sn(sv)[s]) }

/// The tag of customer row `c`'s nation.
pub open spec fn cust_tag(sv: StoresView, ps: Seq<Literal>, c: int) -> int { nat_tag(sv, ps, cn(sv)[c]) }

/// Supplier nation `$1` and customer nation `$2`, or the other way round.
pub open spec fn tags_match(st: int, ct: int) -> bool {
    (st % 2 == 1 && ct >= 2) || (st >= 2 && ct % 2 == 1)
}

/// The group of a qualifying row with supplier tag `st`, customer tag `ct` and stored ship day `d`.
pub open spec fn grp_of(st: int, ct: int, d: int) -> int {
    (if st % 2 == 1 && ct >= 2 { 0int } else { 2int }) + (if d >= 9496 { 1int } else { 0int })
}

/// The key `(supp_nation, cust_nation, l_year)` of group `g`: `($1, $2)` for groups 0 and 1, `($2, $1)` for 2 and
/// 3; year 1995 for even groups, 1996 for odd ones.
pub open spec fn grp_key(ps: Seq<Literal>, g: int) -> Row {
    seq![
        Val::Text(if g < 2 { p1_of(ps) } else { p2_of(ps) }),
        Val::Text(if g < 2 { p2_of(ps) } else { p1_of(ps) }),
        Val::Num { coeff: if g % 2 == 0 { 1995 } else { 1996 }, scale: 0 },
    ]
}

// ------------------------------------------------------------------------------------------------ lineitem rows

/// Supplier row of lineitem row `l`.
pub open spec fn l_supp(sv: StoresView, l: int) -> int { key_row(sk(sv), lsk(sv)[l]) }

/// Orders row of lineitem row `l`.
pub open spec fn l_ord(sv: StoresView, l: int) -> int { key_row(ok(sv), lok(sv)[l]) }

/// Customer row of lineitem row `l`'s order.
pub open spec fn l_cust(sv: StoresView, l: int) -> int { key_row(ck(sv), oc(sv)[l_ord(sv, l)]) }

/// The supplier, order and customer keys of lineitem row `l` resolve.
pub open spec fn line_keys(sv: StoresView, l: int) -> bool {
    &&& has_key(sk(sv), lsk(sv)[l])
    &&& has_key(ok(sv), lok(sv)[l])
    &&& has_key(ck(sv), oc(sv)[l_ord(sv, l)])
}

/// Lineitem row `l` qualifies.
pub open spec fn line_qual(sv: StoresView, ps: Seq<Literal>, l: int) -> bool {
    &&& line_keys(sv, l)
    &&& ship_in(lsd(sv)[l] as int)
    &&& tags_match(supp_tag(sv, ps, l_supp(sv, l)), cust_tag(sv, ps, l_cust(sv, l)))
}

/// The group of lineitem row `l`.
pub open spec fn line_grp(sv: StoresView, ps: Seq<Literal>, l: int) -> int {
    grp_of(supp_tag(sv, ps, l_supp(sv, l)), cust_tag(sv, ps, l_cust(sv, l)), lsd(sv)[l] as int)
}

/// `l_extendedprice * (1 - l_discount)` of lineitem row `l` (coefficient at scale 4).
pub open spec fn line_val(sv: StoresView, l: int) -> int { lpr(sv)[l] * (100 - ldc(sv)[l]) }

/// The quantity summed: count (`w == 0`), value (`w == 1`) or absolute value (`w == 2`).
pub open spec fn wval(w: int, v: int) -> int { if w == 0 { 1 } else if w == 1 { v } else { abs(v) } }

/// Contribution of lineitem row `l` to group `g`.
pub open spec fn lterm(sv: StoresView, ps: Seq<Literal>, g: int, w: int, l: int) -> int {
    if line_qual(sv, ps, l) && line_grp(sv, ps, l) == g { wval(w, line_val(sv, l)) } else { 0 }
}

/// Sum of the contributions of the lineitem rows `lo..hi` to group `g`.
pub open spec fn lsum(sv: StoresView, ps: Seq<Literal>, g: int, w: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { lsum(sv, ps, g, w, lo, hi - 1) + lterm(sv, ps, g, w, hi - 1) }
}

/// Adjacent ranges add.
pub proof fn lemma_lsum_split(sv: StoresView, ps: Seq<Literal>, g: int, w: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures lsum(sv, ps, g, w, lo, hi) == lsum(sv, ps, g, w, lo, mid) + lsum(sv, ps, g, w, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_lsum_split(sv, ps, g, w, lo, mid, hi - 1);
    }
}

/// Counts are non-negative, absolute sums are non-negative and bound the sums.
pub proof fn lemma_lsum_bounds(sv: StoresView, ps: Seq<Literal>, g: int, lo: int, hi: int)
    ensures
        lsum(sv, ps, g, 0, lo, hi) >= 0,
        lsum(sv, ps, g, 2, lo, hi) >= 0,
        -lsum(sv, ps, g, 2, lo, hi) <= lsum(sv, ps, g, 1, lo, hi) <= lsum(sv, ps, g, 2, lo, hi),
        lsum(sv, ps, g, 0, lo, hi) == 0 ==> lsum(sv, ps, g, 1, lo, hi) == 0 && lsum(sv, ps, g, 2, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_lsum_bounds(sv, ps, g, lo, hi - 1);
    }
}

/// Contribution of lineitem row `l` to the group with key `k`.
pub open spec fn kterm(sv: StoresView, ps: Seq<Literal>, k: Row, w: int, l: int) -> int {
    if line_qual(sv, ps, l) && grp_key(ps, line_grp(sv, ps, l)) == k { wval(w, line_val(sv, l)) } else { 0 }
}

/// Sum of the contributions of the lineitem rows `0..n` to the group with key `k`.
pub open spec fn ksum(sv: StoresView, ps: Seq<Literal>, k: Row, w: int, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { ksum(sv, ps, k, w, n - 1) + kterm(sv, ps, k, w, n - 1) }
}

} // verus!
