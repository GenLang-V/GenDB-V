//! The normal form of Q21 over the stored columns, one lineitem row at a time.
//!
//! Lineitem row `i` is *waiting* (`lq`) when it is late (`l_receiptdate > l_commitdate`), its order has a row of
//! another supplier (`ex2`, the EXISTS) and no late row of another supplier (`ex3`, the NOT EXISTS). Its weight is
//! the number of `F` orders with its order key (`ofs`; 0 or 1 by the primary key). The count of supplier key `v`
//! over lineitem rows `lo..hi` is `ksum(v, lo, hi)`, the sum of the weights of the waiting rows of `v`. The COUNT of
//! group `g` (an `s_name`) is `gc(g)`: over the suppliers named `g`, the number of nations named `$1` with the
//! supplier's nation key (`nw`; 0 or 1) times the supplier key's count over all lineitem rows.
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::agent::cols::*;

verus! {

// ------------------------------------------------------------------------------------------------ one lineitem row

/// Lineitem row `i` is late: `l_receiptdate > l_commitdate`.
pub open spec fn late(sv: StoresView, i: int) -> bool { lr(sv)[i] > lc(sv)[i] }

/// Lineitem row `j` belongs to row `i`'s order and has another supplier.
pub open spec fn other_at(sv: StoresView, i: int, j: int) -> bool { lk(sv)[j] == lk(sv)[i] && ls(sv)[j] != ls(sv)[i] }

/// The EXISTS of row `i`: its order has a row of another supplier.
pub open spec fn ex2(sv: StoresView, i: int) -> bool {
    exists|j: int| 0 <= j < n_l(sv) && #[trigger] other_at(sv, i, j)
}

/// The NOT EXISTS's subquery of row `i`: its order has a late row of another supplier.
pub open spec fn ex3(sv: StoresView, i: int) -> bool {
    exists|j: int| 0 <= j < n_l(sv) && #[trigger] other_at(sv, i, j) && late(sv, j)
}

/// Row `i` waits: late, with another supplier in its order and no late row of another supplier.
pub open spec fn lq(sv: StoresView, i: int) -> bool { late(sv, i) && ex2(sv, i) && !ex3(sv, i) }

// ------------------------------------------------------------------------------------------------ orders

/// `o_orderstatus = 'F'` of orders row `j`.
pub open spec fn fstat(sv: StoresView, j: int) -> bool { ostat(sv, j) == seq![70u8] }

/// Orders row `j` has key `k` and status `F`.
pub open spec fn ohit(sv: StoresView, k: int, j: int) -> bool { ok(sv)[j] as int == k && fstat(sv, j) }

/// Number of orders rows among the first `n` with key `k` and status `F`.
pub open spec fn ocnt(sv: StoresView, k: int, n: int) -> nat
    decreases n,
{
    if n <= 0 { 0 } else { ocnt(sv, k, n - 1) + if ohit(sv, k, n - 1) { 1nat } else { 0nat } }
}

/// Number of `F` orders with key `k`.
pub open spec fn ofs(sv: StoresView, k: int) -> nat { ocnt(sv, k, n_o(sv)) }

/// No orders row among the first `n` has key `k`: count 0.
pub proof fn lemma_ocnt_none(sv: StoresView, k: int, n: int)
    requires 0 <= n <= n_o(sv), forall|j: int| 0 <= j < n ==> ok(sv)[j] as int != k,
    ensures ocnt(sv, k, n) == 0,
    decreases n,
{
    if n > 0 { lemma_ocnt_none(sv, k, n - 1); }
}

/// With unique keys, the count over the first `n` rows is whether row `j` (holding `k`) is among them and `F`.
pub proof fn lemma_ocnt_one(sv: StoresView, k: int, j: int, n: int)
    requires keys_unique(ok(sv)), 0 <= j < n_o(sv), ok(sv)[j] as int == k, 0 <= n <= n_o(sv),
    ensures ocnt(sv, k, n) == if j < n && fstat(sv, j) { 1nat } else { 0nat },
    decreases n,
{
    if n > 0 {
        lemma_ocnt_one(sv, k, j, n - 1);
        if n - 1 != j && ok(sv)[n - 1] as int == k {
            assert(ok(sv)[n - 1] == ok(sv)[j]);
        }
    }
}

/// The weight of key `k`: 1 when the orders row `j` holding it has status `F`, else 0 (unique keys).
pub proof fn lemma_ofs_found(sv: StoresView, k: int, j: int)
    requires keys_unique(ok(sv)), 0 <= j < n_o(sv), ok(sv)[j] as int == k,
    ensures ofs(sv, k) == if fstat(sv, j) { 1nat } else { 0nat },
{
    lemma_ocnt_one(sv, k, j, n_o(sv));
}

/// The weight of a key no orders row holds is 0.
pub proof fn lemma_ofs_none(sv: StoresView, k: int)
    requires forall|j: int| 0 <= j < n_o(sv) ==> ok(sv)[j] as int != k,
    ensures ofs(sv, k) == 0,
{
    lemma_ocnt_none(sv, k, n_o(sv));
}

/// Every weight is at most 1 (unique keys).
pub proof fn lemma_ofs_le1(sv: StoresView, k: int)
    requires keys_unique(ok(sv)),
    ensures ofs(sv, k) <= 1,
{
    if exists|j: int| 0 <= j < n_o(sv) && ok(sv)[j] as int == k {
        let j = choose|j: int| 0 <= j < n_o(sv) && ok(sv)[j] as int == k;
        lemma_ofs_found(sv, k, j);
    } else {
        lemma_ofs_none(sv, k);
    }
}

// ------------------------------------------------------------------------------------------------ nations

/// Nation row `n` has key `v` and the name `p`.
pub open spec fn nhit(sv: StoresView, p: Seq<u8>, v: int, n: int) -> bool { nkey(sv)[n] as int == v && nname(sv, n) == p }

/// Number of nation rows among the first `m` with key `v` and name `p`.
pub open spec fn ncnt(sv: StoresView, p: Seq<u8>, v: int, m: int) -> nat
    decreases m,
{
    if m <= 0 { 0 } else { ncnt(sv, p, v, m - 1) + if nhit(sv, p, v, m - 1) { 1nat } else { 0nat } }
}

/// The number of nations named `p` with supplier row `s`'s nation key.
pub open spec fn nw(sv: StoresView, p: Seq<u8>, s: int) -> nat { ncnt(sv, p, snk(sv)[s] as int, n_n(sv)) }

/// With unique keys, at most one nation row has key `v`: the count is at most 1.
pub proof fn lemma_ncnt_le1(sv: StoresView, p: Seq<u8>, v: int, m: int)
    requires keys_unique(nkey(sv)), 0 <= m <= n_n(sv),
    ensures
        ncnt(sv, p, v, m) <= 1,
        ncnt(sv, p, v, m) == 1 ==> exists|n: int| 0 <= n < m && #[trigger] nhit(sv, p, v, n),
        (forall|n: int| 0 <= n < m ==> !#[trigger] nhit(sv, p, v, n)) ==> ncnt(sv, p, v, m) == 0,
    decreases m,
{
    if m > 0 {
        lemma_ncnt_le1(sv, p, v, m - 1);
        if nhit(sv, p, v, m - 1) && ncnt(sv, p, v, m - 1) == 1 {
            let n = choose|n: int| 0 <= n < m - 1 && #[trigger] nhit(sv, p, v, n);
            assert(nkey(sv)[n] == nkey(sv)[m - 1]);
        }
    }
}

// ------------------------------------------------------------------------------------------------ counts

/// Contribution of lineitem row `i` to the count of supplier key `v`: its weight when it waits and has supplier `v`.
pub open spec fn lterm(sv: StoresView, v: int, i: int) -> nat {
    if ls(sv)[i] as int == v && lq(sv, i) { ofs(sv, lk(sv)[i] as int) } else { 0 }
}

/// The count of supplier key `v` over lineitem rows `lo..hi`.
pub open spec fn ksum(sv: StoresView, v: int, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo { 0 } else { ksum(sv, v, lo, hi - 1) + lterm(sv, v, hi - 1) }
}

/// Adjacent ranges add.
pub proof fn lemma_ksum_split(sv: StoresView, v: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures ksum(sv, v, lo, hi) == ksum(sv, v, lo, mid) + ksum(sv, v, mid, hi),
    decreases hi - mid,
{
    if hi > mid { lemma_ksum_split(sv, v, lo, mid, hi - 1); }
}

/// A range whose rows contribute nothing to `v` has count 0.
pub proof fn lemma_ksum_zero(sv: StoresView, v: int, lo: int, hi: int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] lterm(sv, v, i) == 0,
    ensures ksum(sv, v, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo { lemma_ksum_zero(sv, v, lo, hi - 1); }
}

/// Every row contributes at most 1 (unique order keys): the count of a range is at most its length.
pub proof fn lemma_ksum_le(sv: StoresView, v: int, lo: int, hi: int)
    requires keys_unique(ok(sv)), lo <= hi,
    ensures ksum(sv, v, lo, hi) <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_ksum_le(sv, v, lo, hi - 1);
        lemma_ofs_le1(sv, lk(sv)[hi - 1] as int);
    }
}

/// The group count of name `g` over supplier rows `0..m`: per supplier named `g`, its nation weight times its key's
/// count over all lineitem rows.
pub open spec fn gsum_s(sv: StoresView, p: Seq<u8>, g: Seq<u8>, m: int) -> nat
    decreases m,
{
    if m <= 0 {
        0
    } else {
        gsum_s(sv, p, g, m - 1)
            + if sname(sv, m - 1) == g { nw(sv, p, m - 1) * ksum(sv, skey(sv)[m - 1] as int, 0, n_l(sv)) } else { 0 }
    }
}

/// The COUNT of group `g`.
pub open spec fn gc(sv: StoresView, p: Seq<u8>, g: Seq<u8>) -> nat { gsum_s(sv, p, g, n_s(sv)) }

} // verus!
