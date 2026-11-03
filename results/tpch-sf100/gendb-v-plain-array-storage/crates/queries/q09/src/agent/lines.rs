//! The statement over the stored columns, one lineitem row at a time.
//!
//! A lineitem row `l` reaches its part, supplier, partsupp row and order through the key columns (`key_row`,
//! `key_row2`; the primary keys make each one unique), and the supplier reaches its nation. Row `l` qualifies
//! (`line_qual`) when all of them exist (`chain_full`) and its part's name matches `$1` (`like_true`). Its group key
//! (`line_key`) is its nation's name and its order's year; its value (`line_val`) is the amount
//! `l_extendedprice * (100 - l_discount) - ps_supplycost * l_quantity` (coefficient at scale 4).
//! `ksum(k, w, n)` sums over the rows `0..n` with key `k` their count (`w == 0`), amount (`w == 1`) or absolute amount
//! (`w == 2`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::source_check::date32_val;
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

/// Row `j` of the key column pair holds `(x, y)`.
pub open spec fn at2(s: Seq<i64>, t: Seq<i64>, x: i64, y: i64, j: int) -> bool { s[j] == x && t[j] == y }

/// Some row of the key column pair (of one length) holds `(x, y)`.
pub open spec fn has_key2(s: Seq<i64>, t: Seq<i64>, x: i64, y: i64) -> bool {
    exists|j: int| 0 <= j < s.len() && #[trigger] at2(s, t, x, y, j)
}

/// The row of the key column pair holding `(x, y)` (meaningful when `has_key2`).
pub open spec fn key_row2(s: Seq<i64>, t: Seq<i64>, x: i64, y: i64) -> int {
    choose|j: int| 0 <= j < s.len() && #[trigger] at2(s, t, x, y, j)
}

/// The row holding `(x, y)` exists when some row holds it, and on a duplicate-free pair it is the only one.
pub proof fn lemma_key_row2(s: Seq<i64>, t: Seq<i64>, x: i64, y: i64)
    ensures
        has_key2(s, t, x, y) ==> 0 <= key_row2(s, t, x, y) < s.len() && at2(s, t, x, y, key_row2(s, t, x, y)),
        keys2_unique(s, t) ==> forall|j: int| 0 <= j < s.len() && #[trigger] at2(s, t, x, y, j) ==> j == key_row2(s, t, x, y),
{
    if keys2_unique(s, t) {
        assert forall|j: int| 0 <= j < s.len() && #[trigger] at2(s, t, x, y, j) implies j == key_row2(s, t, x, y) by {
            assert(has_key2(s, t, x, y));
            let r = key_row2(s, t, x, y);
            assert(at2(s, t, x, y, r));
            assert(s[r] == s[j] && t[r] == t[j]);
        }
    }
}

// ------------------------------------------------------------------------------------------------ lineitem rows

/// Part row of lineitem row `l`.
pub open spec fn l_part(sv: StoresView, l: int) -> int { key_row(pk(sv), lpk(sv)[l]) }

/// Supplier row of lineitem row `l`.
pub open spec fn l_supp(sv: StoresView, l: int) -> int { key_row(sk(sv), lsk(sv)[l]) }

/// Partsupp row of lineitem row `l` (its part and supplier keys).
pub open spec fn l_ps(sv: StoresView, l: int) -> int { key_row2(pspk(sv), pssk(sv), lpk(sv)[l], lsk(sv)[l]) }

/// Orders row of lineitem row `l`.
pub open spec fn l_ord(sv: StoresView, l: int) -> int { key_row(ok(sv), lok(sv)[l]) }

/// Nation row of the supplier of lineitem row `l`.
pub open spec fn l_nat(sv: StoresView, l: int) -> int { key_row(nk(sv), sn(sv)[l_supp(sv, l)]) }

/// The part, supplier, partsupp, order and supplier nation of lineitem row `l` exist.
pub open spec fn chain_full(sv: StoresView, l: int) -> bool {
    &&& has_key(pk(sv), lpk(sv)[l])
    &&& has_key(sk(sv), lsk(sv)[l])
    &&& has_key2(pspk(sv), pssk(sv), lpk(sv)[l], lsk(sv)[l])
    &&& has_key(ok(sv), lok(sv)[l])
    &&& has_key(nk(sv), sn(sv)[l_supp(sv, l)])
}

/// Lineitem row `l` qualifies.
pub open spec fn line_qual(sv: StoresView, ps: Seq<Literal>, l: int) -> bool {
    chain_full(sv, l) && like_true(pname(sv, l_part(sv, l)), pat_of(ps))
}

/// The year of a stored day (days since 1970-01-01): `EXTRACT(YEAR ..)` of the SQL date.
pub open spec fn day_year(d: i32) -> int { coeff_of(year_val(date32_val(d))) }

/// The group key of lineitem row `l`: its supplier nation's name and its order's year.
pub open spec fn line_key(sv: StoresView, l: int) -> Row {
    seq![Val::Text(nname(sv, l_nat(sv, l))), Val::Num { coeff: day_year(od(sv)[l_ord(sv, l)]), scale: 0 }]
}

/// The amount of lineitem row `l` (coefficient at scale 4).
pub open spec fn line_val(sv: StoresView, l: int) -> int {
    amount(lpr(sv)[l] as int, ldc(sv)[l] as int, psc(sv)[l_ps(sv, l)] as int, lqt(sv)[l] as int)
}

/// The quantity summed: count (`w == 0`), value (`w == 1`) or absolute value (`w == 2`).
pub open spec fn wval(w: int, v: int) -> int { if w == 0 { 1 } else if w == 1 { v } else { abs(v) } }

/// Contribution of lineitem row `l` to the group with key `k`.
pub open spec fn kterm(sv: StoresView, ps: Seq<Literal>, k: Row, w: int, l: int) -> int {
    if line_qual(sv, ps, l) && line_key(sv, l) == k { wval(w, line_val(sv, l)) } else { 0 }
}

/// Sum of the contributions of the lineitem rows `0..n` to the group with key `k`.
pub open spec fn ksum(sv: StoresView, ps: Seq<Literal>, k: Row, w: int, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { ksum(sv, ps, k, w, n - 1) + kterm(sv, ps, k, w, n - 1) }
}

/// Counts and absolute sums are non-negative and bound the sums; a zero count means zero sums.
pub proof fn lemma_ksum_bounds(sv: StoresView, ps: Seq<Literal>, k: Row, n: int)
    ensures
        ksum(sv, ps, k, 0, n) >= 0,
        ksum(sv, ps, k, 2, n) >= 0,
        -ksum(sv, ps, k, 2, n) <= ksum(sv, ps, k, 1, n) <= ksum(sv, ps, k, 2, n),
        ksum(sv, ps, k, 0, n) == 0 ==> ksum(sv, ps, k, 1, n) == 0 && ksum(sv, ps, k, 2, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_ksum_bounds(sv, ps, k, n - 1);
    }
}

} // verus!
