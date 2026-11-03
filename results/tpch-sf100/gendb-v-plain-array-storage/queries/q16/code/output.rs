//! The result rows from the group counts: group id `g` (below `nbr * nt * ns`) stands for the brand key
//! `kb[g / (nt * ns)]`, the type key `kt[(g / ns) % nt]` and the size `szl[g % ns]` (`grow`); its output row is that
//! key and the count `cnt[g]` (`orow`), for every group with a non-zero count (`present`).
//!
//! Order: each present group gets the sort key `(2^32 - 1 - count) << 32 | rc`, where `rc` combines the ranks of its
//! brand, type and size among the dictionary entries (`common::ranks`) in the same mixed radix as the group id.
//! Ascending sort keys are the ORDER BY order (`supplier_cnt DESC, p_brand, p_type, p_size`, `lemma_key_order`); a
//! table `ginv` maps `rc` back to the group. The rows are written as columns (`Answer::Columns`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::sign;
use crate::spec::text::lex_cmp;
use crate::spec::order::*;
use crate::gendb_entry::results::{ResultColumns, ResultColumn, columns_wf, columns_view, column_value, text_column, push_text};
use crate::agent::sem_ast::order_keys;
use crate::agent::common::text_dict::TextDict;
use crate::agent::common::ranks::*;
use crate::agent::common::sort_u64::{asc, sort_u64};
use crate::agent::order::{og_ok, order_by_count};
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::bridge::order::lemma_lex_cmp_antisym;

verus! {

/// The parts of a group id (mixed radix `nbr, nt, ns`).
pub open spec fn bi_of(g: int, nt: int, ns: int) -> int { g / (nt * ns) }
pub open spec fn ti_of(g: int, nt: int, ns: int) -> int { (g / ns) % nt }
pub open spec fn si_of(g: int, ns: int) -> int { g % ns }

/// The group key of group id `g`.
pub open spec fn grow(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, g: int) -> Row {
    let (nt, ns) = (kt.len() as int, szl.len() as int);
    seq![Val::Text(kb[bi_of(g, nt, ns)]), Val::Text(kt[ti_of(g, nt, ns)]), Val::Int(szl[si_of(g, ns)] as int)]
}

/// The output row of group id `g`.
pub open spec fn orow(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, cnt: Seq<u64>, g: int) -> Row {
    grow(kb, kt, szl, g) + seq![Val::Int(cnt[g] as int)]
}

/// Group `g` has a non-zero count.
pub open spec fn present(cnt: Seq<u64>, g: int) -> bool {
    0 <= g < cnt.len() && cnt[g] > 0
}

/// The tables are consistent: distinct keys and sizes, `cnt` over all group ids, counts below `2^32 - 1`.
pub open spec fn tables_ok(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, cnt: Seq<u64>) -> bool {
    &&& distinct_texts(kb) && distinct_texts(kt) && distinct_ints(szl)
    &&& kb.len() >= 1 && kt.len() >= 1 && szl.len() >= 1
    &&& cnt.len() == kb.len() * kt.len() * szl.len()
    &&& cnt.len() <= 0x400_0000
    &&& forall|g: int| 0 <= g < cnt.len() ==> #[trigger] cnt[g] < 0xFFFF_FFFF
}

// ------------------------------------------------------------------------------------------------ arithmetic

/// Decoding a group id: its parts are in range and recompose it.
pub proof fn lemma_decode(g: int, nb: int, nt: int, ns: int)
    requires nb >= 1, nt >= 1, ns >= 1, 0 <= g < nb * nt * ns,
    ensures
        0 <= bi_of(g, nt, ns) < nb, 0 <= ti_of(g, nt, ns) < nt, 0 <= si_of(g, ns) < ns,
        g == (bi_of(g, nt, ns) * nt + ti_of(g, nt, ns)) * ns + si_of(g, ns),
{
    let q = g / ns;
    let s = g % ns;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(g, ns);
    vstd::arithmetic::div_mod::lemma_mod_bound(g, ns);
    let t = q % nt;
    let b = q / nt;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q, nt);
    vstd::arithmetic::div_mod::lemma_mod_bound(q, nt);
    vstd::arithmetic::div_mod::lemma_div_denominator(g, ns, nt);
    assert(g / (ns * nt) == b);
    assert(nt * ns == ns * nt) by (nonlinear_arith);
    assert(bi_of(g, nt, ns) == b);
    assert(0 <= q) by (nonlinear_arith) requires 0 <= g, ns >= 1, q == g / ns {
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(g, ns);
    }
    assert(0 <= b) by { vstd::arithmetic::div_mod::lemma_div_pos_is_pos(q, nt); }
    assert(g == (b * nt + t) * ns + s) by (nonlinear_arith) requires g == ns * q + s, q == nt * b + t;
    assert(b < nb) by (nonlinear_arith) requires g == (b * nt + t) * ns + s, g < nb * nt * ns, 0 <= t, 0 <= s, nt >= 1, ns >= 1, b >= 0;
}

/// Composing parts in range gives a group id whose decoding returns them.
pub proof fn lemma_compose(b: int, t: int, s: int, nb: int, nt: int, ns: int)
    requires 0 <= b < nb, 0 <= t < nt, 0 <= s < ns,
    ensures ({
        let g = (b * nt + t) * ns + s;
        &&& 0 <= g < nb * nt * ns
        &&& bi_of(g, nt, ns) == b && ti_of(g, nt, ns) == t && si_of(g, ns) == s
    }),
{
    let g = (b * nt + t) * ns + s;
    let x = b * nt + t;
    assert(0 <= x < nb * nt) by (nonlinear_arith) requires 0 <= b < nb, 0 <= t < nt, x == b * nt + t;
    assert(0 <= g < (nb * nt) * ns) by (nonlinear_arith) requires 0 <= x < nb * nt, 0 <= s < ns, g == x * ns + s;
    assert((nb * nt) * ns == nb * nt * ns) by (nonlinear_arith);
    lemma_decode(g, nb, nt, ns);
    lemma_radix_unique(b, t, s, bi_of(g, nt, ns), ti_of(g, nt, ns), si_of(g, ns), nt, ns);
}

/// The mixed radix representation is unique.
pub proof fn lemma_radix_unique(b1: int, t1: int, s1: int, b2: int, t2: int, s2: int, nt: int, ns: int)
    requires 0 <= t1 < nt, 0 <= s1 < ns, 0 <= t2 < nt, 0 <= s2 < ns, 0 <= b1, 0 <= b2,
        (b1 * nt + t1) * ns + s1 == (b2 * nt + t2) * ns + s2,
    ensures b1 == b2 && t1 == t2 && s1 == s2,
{
    lemma_radix_order(b1, t1, s1, b2, t2, s2, nt, ns);
    lemma_radix_order(b2, t2, s2, b1, t1, s1, nt, ns);
}

/// The order of mixed radix numbers is the lexicographic order of their digits.
pub proof fn lemma_radix_order(b1: int, t1: int, s1: int, b2: int, t2: int, s2: int, nt: int, ns: int)
    requires 0 <= t1 < nt, 0 <= s1 < ns, 0 <= t2 < nt, 0 <= s2 < ns, 0 <= b1, 0 <= b2,
        (b1 * nt + t1) * ns + s1 <= (b2 * nt + t2) * ns + s2,
    ensures b1 < b2 || (b1 == b2 && (t1 < t2 || (t1 == t2 && s1 <= s2))),
{
    let x1 = b1 * nt + t1;
    let x2 = b2 * nt + t2;
    assert(x1 <= x2) by (nonlinear_arith) requires x1 * ns + s1 <= x2 * ns + s2, 0 <= s1 < ns, 0 <= s2 < ns;
    assert(b1 <= b2) by (nonlinear_arith) requires b1 * nt + t1 <= b2 * nt + t2, 0 <= t1 < nt, 0 <= t2 < nt;
    if b1 == b2 {
        assert(t1 <= t2);
        if t1 == t2 {
            assert(x1 == x2);
            assert(s1 <= s2) by (nonlinear_arith) requires x1 * ns + s1 <= x2 * ns + s2, x1 == x2;
        }
    }
}

/// Packing a high and a low 32-bit half into a `u64`.
pub proof fn lemma_pack(hi: u64, lo: u64)
    requires hi < 0x1_0000_0000, lo < 0x1_0000_0000,
    ensures
        ((hi << 32u64) | lo) as int == hi as int * 0x1_0000_0000 + lo as int,
        ((hi << 32u64) | lo) >> 32u64 == hi,
        ((hi << 32u64) | lo) & 0xFFFF_FFFFu64 == lo,
{
    assert(((hi << 32u64) | lo) == hi * 0x1_0000_0000u64 + lo) by (bit_vector)
        requires hi < 0x1_0000_0000u64, lo < 0x1_0000_0000u64;
    assert(((hi << 32u64) | lo) >> 32u64 == hi) by (bit_vector) requires hi < 0x1_0000_0000u64, lo < 0x1_0000_0000u64;
    assert(((hi << 32u64) | lo) & 0xFFFF_FFFFu64 == lo) by (bit_vector) requires hi < 0x1_0000_0000u64, lo < 0x1_0000_0000u64;
}

// ------------------------------------------------------------------------------------------------ order of rows

/// `keys_cmp` of the ORDER BY keys on two output rows: count descending, then brand, type and size ascending.
pub proof fn lemma_rows_cmp(r1: Row, r2: Row, b1: Seq<u8>, t1: Seq<u8>, s1: int, c1: int, b2: Seq<u8>, t2: Seq<u8>, s2: int, c2: int)
    requires
        r1 == seq![Val::Text(b1), Val::Text(t1), Val::Int(s1)] + seq![Val::Int(c1)],
        r2 == seq![Val::Text(b2), Val::Text(t2), Val::Int(s2)] + seq![Val::Int(c2)],
    ensures
        keys_cmp(order_keys(), r1, r2) == if c1 != c2 { -sign(c1 - c2) }
            else if lex_cmp(b1, b2) != 0 { lex_cmp(b1, b2) }
            else if lex_cmp(t1, t2) != 0 { lex_cmp(t1, t2) }
            else { sign(s1 - s2) },
{
    let ks = order_keys();
    assert(r1[0] == Val::Text(b1) && r1[1] == Val::Text(t1) && r1[2] == Val::Int(s1) && r1[3] == Val::Int(c1) && r1.len() == 4);
    assert(r2[0] == Val::Text(b2) && r2[1] == Val::Text(t2) && r2[2] == Val::Int(s2) && r2[3] == Val::Int(c2) && r2.len() == 4);
    assert(key_cmp(ks[0], r1, r2) == -sign(c1 - c2));
    assert(key_cmp(ks[1], r1, r2) == lex_cmp(b1, b2));
    assert(key_cmp(ks[2], r1, r2) == lex_cmp(t1, t2));
    assert(key_cmp(ks[3], r1, r2) == sign(s1 - s2));
    let k1 = ks.drop_first();
    let k2 = k1.drop_first();
    let k3 = k2.drop_first();
    assert(k3.drop_first() =~= Seq::<crate::spec::ast::OrderKey>::empty());
    assert(keys_cmp(k3.drop_first(), r1, r2) == 0);
    assert(k1[0] == ks[1] && k2[0] == ks[2] && k3[0] == ks[3]);
    assert(k3.len() == 1 && k2.len() == 2 && k1.len() == 3 && ks.len() == 4);
    assert(keys_cmp(k3, r1, r2) == sign(s1 - s2)) by {
        assert(key_cmp(k3[0], r1, r2) == sign(s1 - s2));
    }
    assert(keys_cmp(k2, r1, r2) == if lex_cmp(t1, t2) != 0 { lex_cmp(t1, t2) } else { sign(s1 - s2) }) by {
        assert(key_cmp(k2[0], r1, r2) == lex_cmp(t1, t2));
    }
    assert(keys_cmp(k1, r1, r2) == if lex_cmp(b1, b2) != 0 { lex_cmp(b1, b2) }
        else if lex_cmp(t1, t2) != 0 { lex_cmp(t1, t2) } else { sign(s1 - s2) }) by {
        assert(key_cmp(k1[0], r1, r2) == lex_cmp(b1, b2));
    }
    assert(-sign(c1 - c2) != 0 <==> c1 != c2);
}

// ------------------------------------------------------------------------------------------------ sort keys

/// The rank code of group `g`: the ranks of its parts in the group id's mixed radix.
pub open spec fn rc_of(rb: Seq<usize>, rt: Seq<usize>, rs: Seq<usize>, nt: int, ns: int, g: int) -> int {
    (rb[bi_of(g, nt, ns)] * nt + rt[ti_of(g, nt, ns)]) * ns + rs[si_of(g, ns)]
}

/// The sort key of group `g`.
pub open spec fn skey(cnt: Seq<u64>, rb: Seq<usize>, rt: Seq<usize>, rs: Seq<usize>, nt: int, ns: int, g: int) -> u64 {
    (((0xFFFF_FFFFu64 - cnt[g]) as u64) << 32u64) | (rc_of(rb, rt, rs, nt, ns, g) as u64)
}

/// The ranks are those of the keys and sizes.
pub open spec fn ranks_ok(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, rb: Seq<usize>, rt: Seq<usize>, rs: Seq<usize>) -> bool {
    &&& rb.len() == kb.len() && rt.len() == kt.len() && rs.len() == szl.len()
    &&& forall|i: int| 0 <= i < kb.len() ==> #[trigger] rb[i] == below_texts(kb, i).len()
    &&& forall|i: int| 0 <= i < kt.len() ==> #[trigger] rt[i] == below_texts(kt, i).len()
    &&& forall|i: int| 0 <= i < szl.len() ==> #[trigger] rs[i] == below_ints(szl, i).len()
}

/// The rank code of a group lies below the number of groups, and different groups have different codes.
pub proof fn lemma_rc(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, cnt: Seq<u64>, rb: Seq<usize>, rt: Seq<usize>,
    rs: Seq<usize>, g1: int, g2: int)
    requires tables_ok(kb, kt, szl, cnt), ranks_ok(kb, kt, szl, rb, rt, rs), 0 <= g1 < cnt.len(), 0 <= g2 < cnt.len(),
    ensures ({
        let (nt, ns) = (kt.len() as int, szl.len() as int);
        &&& 0 <= rc_of(rb, rt, rs, nt, ns, g1) < cnt.len()
        &&& rc_of(rb, rt, rs, nt, ns, g1) == rc_of(rb, rt, rs, nt, ns, g2) ==> g1 == g2
    }),
{
    let (nb, nt, ns) = (kb.len() as int, kt.len() as int, szl.len() as int);
    lemma_decode(g1, nb, nt, ns);
    lemma_decode(g2, nb, nt, ns);
    let (b1, t1, s1) = (bi_of(g1, nt, ns), ti_of(g1, nt, ns), si_of(g1, ns));
    let (b2, t2, s2) = (bi_of(g2, nt, ns), ti_of(g2, nt, ns), si_of(g2, ns));
    lemma_text_ranks(kb, b1, b2);
    lemma_text_ranks(kt, t1, t2);
    lemma_int_ranks(szl, s1, s2);
    lemma_text_ranks(kb, b2, b1);
    lemma_text_ranks(kt, t2, t1);
    lemma_int_ranks(szl, s2, s1);
    lemma_compose(rb[b1] as int, rt[t1] as int, rs[s1] as int, nb, nt, ns);
    if rc_of(rb, rt, rs, nt, ns, g1) == rc_of(rb, rt, rs, nt, ns, g2) {
        lemma_radix_unique(rb[b1] as int, rt[t1] as int, rs[s1] as int, rb[b2] as int, rt[t2] as int, rs[s2] as int, nt, ns);
    }
}

/// Ascending sort keys of two groups: their rows are in ORDER BY order.
pub proof fn lemma_key_order(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, cnt: Seq<u64>, rb: Seq<usize>, rt: Seq<usize>,
    rs: Seq<usize>, g1: int, g2: int)
    requires
        tables_ok(kb, kt, szl, cnt), ranks_ok(kb, kt, szl, rb, rt, rs), 0 <= g1 < cnt.len(), 0 <= g2 < cnt.len(),
        skey(cnt, rb, rt, rs, kt.len() as int, szl.len() as int, g1) <= skey(cnt, rb, rt, rs, kt.len() as int, szl.len() as int, g2),
    ensures keys_cmp(order_keys(), orow(kb, kt, szl, cnt, g1), orow(kb, kt, szl, cnt, g2)) <= 0,
{
    let (nb, nt, ns) = (kb.len() as int, kt.len() as int, szl.len() as int);
    lemma_rc(kb, kt, szl, cnt, rb, rt, rs, g1, g2);
    lemma_rc(kb, kt, szl, cnt, rb, rt, rs, g2, g1);
    let (c1, c2) = (cnt[g1], cnt[g2]);
    let (rc1, rc2) = (rc_of(rb, rt, rs, nt, ns, g1), rc_of(rb, rt, rs, nt, ns, g2));
    lemma_pack((0xFFFF_FFFFu64 - c1) as u64, rc1 as u64);
    lemma_pack((0xFFFF_FFFFu64 - c2) as u64, rc2 as u64);
    lemma_decode(g1, nb, nt, ns);
    lemma_decode(g2, nb, nt, ns);
    let (b1, t1, s1) = (bi_of(g1, nt, ns), ti_of(g1, nt, ns), si_of(g1, ns));
    let (b2, t2, s2) = (bi_of(g2, nt, ns), ti_of(g2, nt, ns), si_of(g2, ns));
    lemma_rows_cmp(orow(kb, kt, szl, cnt, g1), orow(kb, kt, szl, cnt, g2), kb[b1], kt[t1], szl[s1] as int, c1 as int,
        kb[b2], kt[t2], szl[s2] as int, c2 as int);
    if c1 == c2 {
        assert(rc1 <= rc2);
        lemma_text_ranks(kb, b1, b2);
        lemma_text_ranks(kt, t1, t2);
        lemma_int_ranks(szl, s1, s2);
        lemma_text_ranks(kb, b2, b1);
        lemma_text_ranks(kt, t2, t1);
        lemma_int_ranks(szl, s2, s1);
        lemma_radix_order(rb[b1] as int, rt[t1] as int, rs[s1] as int, rb[b2] as int, rt[t2] as int, rs[s2] as int, nt, ns);
        lemma_lex_cmp_antisym(kb[b1], kb[b2]);
        lemma_lex_cmp_zero(kb[b1], kb[b2]);
        lemma_lex_cmp_antisym(kt[t1], kt[t2]);
        lemma_lex_cmp_zero(kt[t1], kt[t2]);
        if rb[b1] == rb[b2] {
            assert(b1 == b2);
            if rt[t1] == rt[t2] {
                assert(t1 == t2);
                assert(rs[s1] <= rs[s2]);
                if s1 != s2 {
                    assert(rs[s1] != rs[s2]);
                    assert(szl[s1] < szl[s2]);
                }
            }
        }
    } else {
        assert(c1 > c2);
    }
}

/// Distinct groups have distinct rows.
pub proof fn lemma_orow_injective(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, cnt: Seq<u64>, g1: int, g2: int)
    requires tables_ok(kb, kt, szl, cnt), 0 <= g1 < cnt.len(), 0 <= g2 < cnt.len(),
        orow(kb, kt, szl, cnt, g1) == orow(kb, kt, szl, cnt, g2),
    ensures g1 == g2,
{
    let (nb, nt, ns) = (kb.len() as int, kt.len() as int, szl.len() as int);
    lemma_decode(g1, nb, nt, ns);
    lemma_decode(g2, nb, nt, ns);
    let (r1, r2) = (orow(kb, kt, szl, cnt, g1), orow(kb, kt, szl, cnt, g2));
    assert(r1[0] == r2[0] && r1[1] == r2[1] && r1[2] == r2[2]);
    let (b1, t1, s1) = (bi_of(g1, nt, ns), ti_of(g1, nt, ns), si_of(g1, ns));
    let (b2, t2, s2) = (bi_of(g2, nt, ns), ti_of(g2, nt, ns), si_of(g2, ns));
    assert(kb[b1] == kb[b2] && kt[t1] == kt[t2] && szl[s1] == szl[s2]);
    assert(b1 == b2 && t1 == t2 && s1 == s2);
}

/// The sort keys of the present groups (`gs`, increasing) and the table from rank codes back to groups.
fn make_keys(cnt: &Vec<u64>, rb: &Vec<usize>, rt: &Vec<usize>, rs: &Vec<usize>, nt: usize, ns: usize,
    Ghost(kb): Ghost<Seq<Seq<u8>>>, Ghost(kt): Ghost<Seq<Seq<u8>>>, Ghost(szl): Ghost<Seq<i64>>)
    -> (r: (Vec<u64>, Vec<u32>, Ghost<Seq<int>>))
    requires
        tables_ok(kb, kt, szl, cnt@), ranks_ok(kb, kt, szl, rb@, rt@, rs@), nt == kt.len(), ns == szl.len(),
    ensures ({
        let (keys, ginv, gs) = (r.0@, r.1@, r.2@);
        &&& keys.len() == gs.len() && ginv.len() == cnt@.len() && gs.len() <= cnt@.len()
        &&& forall|i: int| 0 <= i < gs.len() ==> #[trigger] present(cnt@, gs[i])
            && keys[i] == skey(cnt@, rb@, rt@, rs@, nt as int, ns as int, gs[i])
            && ginv[rc_of(rb@, rt@, rs@, nt as int, ns as int, gs[i])] == gs[i]
        &&& forall|i: int, j: int| 0 <= i < j < gs.len() ==> gs[i] < gs[j]
        &&& forall|g: int| #[trigger] present(cnt@, g) ==> gs.contains(g)
    }),
{
    let ghost (crb, crt, crs) = (rb@, rt@, rs@);
    let c = cnt.len();
    proof {
        let (nbi, nti, nsi) = (kb.len() as int, nt as int, ns as int);
        assert(nti * nsi <= c && nti * nsi >= 1) by (nonlinear_arith)
            requires c == nbi * nti * nsi, nbi >= 1, nti >= 1, nsi >= 1;
    }
    let ntns = nt * ns;
    let mut keys: Vec<u64> = Vec::new();
    let mut ginv: Vec<u32> = vec![0u32; c];
    let ghost mut gs: Seq<int> = Seq::empty();
    let mut g: usize = 0;
    proof {
        assert(nt >= 1 && ns >= 1);
        assert(ntns <= c) by (nonlinear_arith) requires c == kb.len() * nt * ns, kb.len() >= 1, ntns == nt * ns, nt >= 1, ns >= 1;
    }
    while g < c
        invariant
            tables_ok(kb, kt, szl, cnt@), ranks_ok(kb, kt, szl, crb, crt, crs), crb == rb@, crt == rt@, crs == rs@,
            nt == kt.len(), ns == szl.len(), ntns == nt * ns, c == cnt@.len(), g <= c,
            keys@.len() == gs.len(), ginv@.len() == c, gs.len() <= g, ntns >= 1,
            forall|i: int| 0 <= i < gs.len() ==> #[trigger] present(cnt@, gs[i]) && gs[i] < g
                && keys@[i] == skey(cnt@, crb, crt, crs, nt as int, ns as int, gs[i])
                && ginv@[rc_of(crb, crt, crs, nt as int, ns as int, gs[i])] == gs[i],
            forall|i: int, j: int| 0 <= i < j < gs.len() ==> gs[i] < gs[j],
            forall|x: int| 0 <= x < g && #[trigger] present(cnt@, x) ==> gs.contains(x),
        decreases c - g,
    {
        let cg = cnt[g];
        if cg > 0 {
            proof {
                lemma_decode(g as int, kb.len() as int, nt as int, ns as int);
                lemma_rc(kb, kt, szl, cnt@, crb, crt, crs, g as int, g as int);
            }
            let bi = g / ntns;
            let ti = (g / ns) % nt;
            let si = g % ns;
            proof {
                assert(bi as int == bi_of(g as int, nt as int, ns as int));
                lemma_text_ranks(kb, bi as int, bi as int);
                lemma_text_ranks(kt, ti as int, ti as int);
                lemma_int_ranks(szl, si as int, si as int);
                lemma_compose(crb[bi as int] as int, crt[ti as int] as int, crs[si as int] as int, kb.len() as int, nt as int, ns as int);
                let (x, y, z, nbi) = (crb[bi as int] as int, crt[ti as int] as int, crs[si as int] as int, kb.len() as int);
                assert(x * nt <= x * nt + y < nbi * nt && nbi * nt <= c && (x * nt + y) * ns <= (x * nt + y) * ns + z) by (nonlinear_arith)
                    requires 0 <= x < nbi, 0 <= y < nt, 0 <= z < ns, c == nbi * nt * ns, ns >= 1, nt >= 1;
            }
            let rcv = (rb[bi] * nt + rt[ti]) * ns + rs[si];
            proof {
                assert(rcv == rc_of(crb, crt, crs, nt as int, ns as int, g as int));
                assert(rcv < c);
                assert(cg < 0xFFFF_FFFF);
            }
            let k = ((0xFFFF_FFFFu64 - cg) << 32u64) | (rcv as u64);
            let ghost ginv0 = ginv@;
            let ghost gs0 = gs;
            keys.push(k);
            ginv[rcv] = g as u32;
            proof {
                gs = gs.push(g as int);
                assert forall|i: int| 0 <= i < gs.len() implies #[trigger] present(cnt@, gs[i]) && gs[i] < g + 1
                    && keys@[i] == skey(cnt@, crb, crt, crs, nt as int, ns as int, gs[i])
                    && ginv@[rc_of(crb, crt, crs, nt as int, ns as int, gs[i])] == gs[i] by {
                    if i < gs0.len() {
                        assert(gs[i] == gs0[i]);
                        assert(present(cnt@, gs0[i]));
                        lemma_rc(kb, kt, szl, cnt@, crb, crt, crs, gs0[i], g as int);
                        assert(rc_of(crb, crt, crs, nt as int, ns as int, gs0[i]) != rcv);
                    }
                }
                assert forall|i: int, j: int| 0 <= i < j < gs.len() implies gs[i] < gs[j] by {
                    if j == gs.len() - 1 {
                        assert(gs[i] == gs0[i]);
                        assert(present(cnt@, gs0[i]));
                    } else {
                        assert(gs[i] == gs0[i] && gs[j] == gs0[j]);
                    }
                }
                assert forall|x: int| 0 <= x < g + 1 && #[trigger] present(cnt@, x) implies gs.contains(x) by {
                    if x < g {
                        let i = choose|i: int| 0 <= i < gs0.len() && gs0[i] == x;
                        assert(gs[i] == x);
                    } else {
                        assert(gs[gs.len() - 1] == x);
                    }
                }
            }
        } else {
            proof {
                assert forall|x: int| 0 <= x < g + 1 && #[trigger] present(cnt@, x) implies gs.contains(x) by {}
            }
        }
        g = g + 1;
    }
    (keys, ginv, Ghost(gs))
}

/// Append one text value to a text column under construction (`push_text` with one copy of the bytes).
fn push_text_fast(offsets: &mut Vec<usize>, bytes: &mut Vec<u8>, value: &[u8])
    requires
        old(offsets)@.len() >= 1,
        old(offsets)@.last() == old(bytes)@.len(),
        old(bytes)@.len() + value@.len() <= usize::MAX,
    ensures
        final(bytes)@ == old(bytes)@ + value@,
        final(offsets)@ == old(offsets)@.push(final(bytes)@.len() as usize),
        final(offsets)@.last() == final(bytes)@.len(),
{
    let ghost b0 = bytes@;
    bytes.extend_from_slice(value);
    proof {
        assert forall|i: int| 0 <= i < bytes@.len() implies bytes@[i] == (b0 + value@)[i] by {
            if i >= b0.len() {
                assert(vstd::pervasive::cloned::<u8>(value@[i - b0.len()], bytes@[i]));
            }
        }
        assert(bytes@ =~= b0 + value@);
    }
    let len = bytes.len();
    offsets.push(len);
}

/// A slice of the dictionary bytes: key `i`.
fn key_slice(d: &TextDict, i: usize) -> (v: &[u8])
    requires d.wf(), i < d.n(),
    ensures v@ == d.key(i as int), v@.len() <= d.kbytes@.len(),
{
    let (x, y) = d.key_range(i);
    let all = d.kbytes.as_slice();
    let (_, rest) = all.split_at(x);
    let (v, _) = rest.split_at(y - x);
    proof { assert(v@ =~= d.kbytes@.subrange(x as int, y as int)); }
    v
}

/// Row `x` of the columns under construction is the output row of group `og[x]`.
pub open spec fn row_at(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, cnt: Seq<u64>, bo: Seq<usize>, bb: Seq<u8>,
    to: Seq<usize>, tb: Seq<u8>, sz: Seq<i64>, cn: Seq<i64>, og: Seq<int>, x: int) -> bool {
    let (nt, ns) = (kt.len() as int, szl.len() as int);
    &&& bo[x] <= bo[x + 1] <= bb.len() && to[x] <= to[x + 1] <= tb.len()
    &&& bb.subrange(bo[x] as int, bo[x + 1] as int) == kb[bi_of(og[x], nt, ns)]
    &&& tb.subrange(to[x] as int, to[x + 1] as int) == kt[ti_of(og[x], nt, ns)]
    &&& sz[x] == szl[si_of(og[x], ns)] && cn[x] as int == cnt[og[x]] as int
}

/// The columns under construction hold the output rows of the groups `og`.
pub open spec fn emitted(kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, cnt: Seq<u64>, bo: Seq<usize>, bb: Seq<u8>,
    to: Seq<usize>, tb: Seq<u8>, sz: Seq<i64>, cn: Seq<i64>, og: Seq<int>) -> bool {
    &&& bo.len() == og.len() + 1 && bo[0] == 0 && bo.last() == bb.len()
    &&& to.len() == og.len() + 1 && to[0] == 0 && to.last() == tb.len()
    &&& sz.len() == og.len() && cn.len() == og.len()
    &&& forall|x: int| 0 <= x < og.len() ==> #[trigger] row_at(kb, kt, szl, cnt, bo, bb, to, tb, sz, cn, og, x)
}

/// Append the output row of group `g`.
fn push_row(bo: &mut Vec<usize>, bb: &mut Vec<u8>, to: &mut Vec<usize>, tb: &mut Vec<u8>, sz: &mut Vec<i64>,
    cn: &mut Vec<i64>, bd: &TextDict, td: &TextDict, szl: &Vec<i64>, cnt: &Vec<u64>, g: usize, ntns: usize,
    Ghost(og): Ghost<Seq<int>>)
    requires
        bd.wf(), td.wf(), tables_ok(bd.keys(), td.keys(), szl@, cnt@), ntns == td.n() * szl@.len(), g < cnt@.len(),
        emitted(bd.keys(), td.keys(), szl@, cnt@, old(bo)@, old(bb)@, old(to)@, old(tb)@, old(sz)@, old(cn)@, og),
        old(bb)@.len() + bd.kbytes@.len() <= usize::MAX, old(tb)@.len() + td.kbytes@.len() <= usize::MAX,
    ensures
        emitted(bd.keys(), td.keys(), szl@, cnt@, final(bo)@, final(bb)@, final(to)@, final(tb)@, final(sz)@, final(cn)@,
            og.push(g as int)),
        final(bb)@.len() <= old(bb)@.len() + bd.kbytes@.len(), final(tb)@.len() <= old(tb)@.len() + td.kbytes@.len(),
{
    let ghost (kb, kt) = (bd.keys(), td.keys());
    let nt = td.count();
    let ns = szl.len();
    proof {
        lemma_decode(g as int, kb.len() as int, nt as int, ns as int);
        let (nbi, nti, nsi) = (kb.len() as int, nt as int, ns as int);
        assert(nti * nsi >= 1) by (nonlinear_arith) requires nti >= 1, nsi >= 1;
    }
    let bi = g / ntns;
    let ti = (g / ns) % nt;
    let si = g % ns;
    let bkey = key_slice(bd, bi);
    let tkey = key_slice(td, ti);
    let ghost (bo0, bb0, to0, tb0, sz0, cn0) = (bo@, bb@, to@, tb@, sz@, cn@);
    push_text_fast(bo, bb, bkey);
    push_text_fast(to, tb, tkey);
    sz.push(szl[si]);
    cn.push(cnt[g] as i64);
    proof {
        let og1 = og.push(g as int);
        assert(bo@[0] == 0 && to@[0] == 0);
        assert forall|x: int| 0 <= x < og1.len() implies #[trigger] row_at(kb, kt, szl@, cnt@, bo@, bb@, to@, tb@, sz@, cn@, og1, x) by {
            if x < og.len() {
                assert(row_at(kb, kt, szl@, cnt@, bo0, bb0, to0, tb0, sz0, cn0, og, x));
                assert(bo@[x] == bo0[x] && bo@[x + 1] == bo0[x + 1]);
                assert(bb@.subrange(bo@[x] as int, bo@[x + 1] as int) =~= bb0.subrange(bo0[x] as int, bo0[x + 1] as int));
                assert(to@[x] == to0[x] && to@[x + 1] == to0[x + 1]);
                assert(tb@.subrange(to@[x] as int, to@[x + 1] as int) =~= tb0.subrange(to0[x] as int, to0[x + 1] as int));
            } else {
                assert(bb@.subrange(bo@[x] as int, bo@[x + 1] as int) =~= bkey@);
                assert(tb@.subrange(to@[x] as int, to@[x + 1] as int) =~= tkey@);
            }
        }
    }
}

/// The group behind sort key `k` (the key of group `g0`).
fn key_group(k: u64, ginv: &Vec<u32>, Ghost(cnt): Ghost<Seq<u64>>, Ghost(g0): Ghost<int>, Ghost(kb): Ghost<Seq<Seq<u8>>>,
    Ghost(kt): Ghost<Seq<Seq<u8>>>, Ghost(szl): Ghost<Seq<i64>>, Ghost(rb): Ghost<Seq<usize>>, Ghost(rt): Ghost<Seq<usize>>,
    Ghost(rs): Ghost<Seq<usize>>) -> (g: usize)
    requires
        tables_ok(kb, kt, szl, cnt), ranks_ok(kb, kt, szl, rb, rt, rs), present(cnt, g0), ginv@.len() == cnt.len(),
        k == skey(cnt, rb, rt, rs, kt.len() as int, szl.len() as int, g0),
        ginv@[rc_of(rb, rt, rs, kt.len() as int, szl.len() as int, g0)] == g0,
    ensures g == g0,
{
    proof {
        lemma_rc(kb, kt, szl, cnt, rb, rt, rs, g0, g0);
        lemma_pack((0xFFFF_FFFFu64 - cnt[g0]) as u64, rc_of(rb, rt, rs, kt.len() as int, szl.len() as int, g0) as u64);
    }
    let rcv = (k & 0xFFFF_FFFFu64) as usize;
    ginv[rcv] as usize
}

/// The final facts about the columns built from the sorted keys.
proof fn lemma_columns(r: ResultColumns, kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, cnt: Seq<u64>, rb: Seq<usize>,
    rt: Seq<usize>, rs: Seq<usize>, sorted: Seq<u64>, keys0: Seq<u64>, gs: Seq<int>, og: Seq<int>, bo: Seq<usize>,
    bb: Seq<u8>, to: Seq<usize>, tb: Seq<u8>, sz: Seq<i64>, cn: Seq<i64>)
    requires
        tables_ok(kb, kt, szl, cnt), ranks_ok(kb, kt, szl, rb, rt, rs),
        r.rows == og.len(), og.len() == sorted.len(), r.columns@.len() == 4,
        r.columns@[0] matches ResultColumn::Text { offsets, bytes } && offsets@ == bo && bytes@ == bb,
        r.columns@[1] matches ResultColumn::Text { offsets, bytes } && offsets@ == to && bytes@ == tb,
        r.columns@[2] matches ResultColumn::Int(v) && v@ == sz,
        r.columns@[3] matches ResultColumn::Int(v) && v@ == cn,
        emitted(kb, kt, szl, cnt, bo, bb, to, tb, sz, cn, og),
        asc(sorted), sorted.to_multiset() == keys0.to_multiset(), keys0.len() == gs.len(),
        forall|x: int| 0 <= x < gs.len() ==> #[trigger] present(cnt, gs[x])
            && keys0[x] == skey(cnt, rb, rt, rs, kt.len() as int, szl.len() as int, gs[x]),
        forall|g: int| #[trigger] present(cnt, g) ==> gs.contains(g),
        forall|x: int| 0 <= x < og.len() ==> #[trigger] present(cnt, og[x])
            && sorted[x] == skey(cnt, rb, rt, rs, kt.len() as int, szl.len() as int, og[x]),
        sorted.no_duplicates(),
    ensures ({
        let out = columns_view(r);
        &&& columns_wf(r)
        &&& out.no_duplicates()
        &&& sorted_by(order_keys(), out)
        &&& forall|row: Row| #[trigger] out.contains(row) <==> exists|g: int| #[trigger] present(cnt, g)
            && row == orow(kb, kt, szl, cnt, g)
    }),
{
    let n = og.len() as int;
    let (nt, ns) = (kt.len() as int, szl.len() as int);
    let out = columns_view(r);
    assert(columns_wf(r)) by {
        assert forall|kk: int| 0 <= kk < r.columns@.len() implies crate::gendb_entry::results::column_wf(#[trigger] r.columns@[kk], r.rows as nat) by {
            if kk == 0 {
                assert forall|x: int| 0 <= x < n implies #[trigger] bo[x] <= bo[x + 1] && bo[x + 1] <= bb.len() by {
                    assert(row_at(kb, kt, szl, cnt, bo, bb, to, tb, sz, cn, og, x));
                }
            } else if kk == 1 {
                assert forall|x: int| 0 <= x < n implies #[trigger] to[x] <= to[x + 1] && to[x + 1] <= tb.len() by {
                    assert(row_at(kb, kt, szl, cnt, bo, bb, to, tb, sz, cn, og, x));
                }
            }
        }
    }
    assert forall|x: int| 0 <= x < n implies #[trigger] out[x] == orow(kb, kt, szl, cnt, og[x]) by {
        assert(row_at(kb, kt, szl, cnt, bo, bb, to, tb, sz, cn, og, x));
        crate::gendb_entry::results::lemma_columns_view(r, x, 0);
        crate::gendb_entry::results::lemma_columns_view(r, x, 1);
        crate::gendb_entry::results::lemma_columns_view(r, x, 2);
        crate::gendb_entry::results::lemma_columns_view(r, x, 3);
        assert(out[x] =~= orow(kb, kt, szl, cnt, og[x]));
    }
    assert(out.len() == n);
    assert forall|x: int, y: int| 0 <= x < y < out.len() implies keys_cmp(order_keys(), #[trigger] out[x], #[trigger] out[y]) <= 0 by {
        assert(present(cnt, og[x]) && present(cnt, og[y]));
        assert(sorted[x] <= sorted[y]);
        lemma_key_order(kb, kt, szl, cnt, rb, rt, rs, og[x], og[y]);
    }
    assert forall|x: int, y: int| 0 <= x < out.len() && 0 <= y < out.len() && x != y implies out[x] != out[y] by {
        assert(present(cnt, og[x]) && present(cnt, og[y]));
        if out[x] == out[y] {
            lemma_orow_injective(kb, kt, szl, cnt, og[x], og[y]);
            assert(sorted[x] == sorted[y]);
        }
    }
    assert forall|row: Row| #[trigger] out.contains(row) <==> exists|g: int| #[trigger] present(cnt, g)
        && row == orow(kb, kt, szl, cnt, g) by {
        if out.contains(row) {
            let x = choose|x: int| 0 <= x < out.len() && out[x] == row;
            assert(present(cnt, og[x]));
        }
        if exists|g: int| #[trigger] present(cnt, g) && row == orow(kb, kt, szl, cnt, g) {
            let g = choose|g: int| #[trigger] present(cnt, g) && row == orow(kb, kt, szl, cnt, g);
            assert(gs.contains(g));
            let jg = choose|jg: int| 0 <= jg < gs.len() && gs[jg] == g;
            assert(present(cnt, gs[jg]));
            let kg = keys0[jg];
            keys0.to_multiset_ensures();
            sorted.to_multiset_ensures();
            assert(keys0.to_multiset().count(kg) > 0);
            assert(sorted.contains(kg));
            let x = choose|x: int| 0 <= x < sorted.len() && sorted[x] == kg;
            assert(present(cnt, og[x]));
            lemma_rc(kb, kt, szl, cnt, rb, rt, rs, og[x], g);
            lemma_rc(kb, kt, szl, cnt, rb, rt, rs, g, og[x]);
            lemma_pack((0xFFFF_FFFFu64 - cnt[og[x]]) as u64, rc_of(rb, rt, rs, nt, ns, og[x]) as u64);
            lemma_pack((0xFFFF_FFFFu64 - cnt[g]) as u64, rc_of(rb, rt, rs, nt, ns, g) as u64);
            assert(og[x] == g);
            assert(out[x] == row);
        }
    }
}

/// The final facts about the columns built from the groups `og` (`og_ok`: the present groups in strictly ascending
/// sort key order).
proof fn lemma_columns_og(r: ResultColumns, kb: Seq<Seq<u8>>, kt: Seq<Seq<u8>>, szl: Seq<i64>, cnt: Seq<u64>, rb: Seq<usize>,
    rt: Seq<usize>, rs: Seq<usize>, og: Seq<u32>, ogs: Seq<int>, bo: Seq<usize>, bb: Seq<u8>, to: Seq<usize>, tb: Seq<u8>,
    sz: Seq<i64>, cn: Seq<i64>)
    requires
        tables_ok(kb, kt, szl, cnt), ranks_ok(kb, kt, szl, rb, rt, rs),
        r.rows == ogs.len(), ogs.len() == og.len(), r.columns@.len() == 4,
        r.columns@[0] matches ResultColumn::Text { offsets, bytes } && offsets@ == bo && bytes@ == bb,
        r.columns@[1] matches ResultColumn::Text { offsets, bytes } && offsets@ == to && bytes@ == tb,
        r.columns@[2] matches ResultColumn::Int(v) && v@ == sz,
        r.columns@[3] matches ResultColumn::Int(v) && v@ == cn,
        emitted(kb, kt, szl, cnt, bo, bb, to, tb, sz, cn, ogs),
        forall|x: int| 0 <= x < og.len() ==> #[trigger] ogs[x] == og[x] as int,
        og_ok(cnt, rb, rt, rs, kt.len() as int, szl.len() as int, og),
    ensures ({
        let out = columns_view(r);
        &&& columns_wf(r)
        &&& out.no_duplicates()
        &&& sorted_by(order_keys(), out)
        &&& forall|row: Row| #[trigger] out.contains(row) <==> exists|g: int| #[trigger] present(cnt, g)
            && row == orow(kb, kt, szl, cnt, g)
    }),
{
    let n = og.len() as int;
    let (nt, ns) = (kt.len() as int, szl.len() as int);
    let out = columns_view(r);
    assert(columns_wf(r)) by {
        assert forall|kk: int| 0 <= kk < r.columns@.len() implies crate::gendb_entry::results::column_wf(#[trigger] r.columns@[kk], r.rows as nat) by {
            if kk == 0 {
                assert forall|x: int| 0 <= x < n implies #[trigger] bo[x] <= bo[x + 1] && bo[x + 1] <= bb.len() by {
                    assert(row_at(kb, kt, szl, cnt, bo, bb, to, tb, sz, cn, ogs, x));
                }
            } else if kk == 1 {
                assert forall|x: int| 0 <= x < n implies #[trigger] to[x] <= to[x + 1] && to[x + 1] <= tb.len() by {
                    assert(row_at(kb, kt, szl, cnt, bo, bb, to, tb, sz, cn, ogs, x));
                }
            }
        }
    }
    assert forall|x: int| 0 <= x < n implies #[trigger] out[x] == orow(kb, kt, szl, cnt, ogs[x]) by {
        assert(row_at(kb, kt, szl, cnt, bo, bb, to, tb, sz, cn, ogs, x));
        crate::gendb_entry::results::lemma_columns_view(r, x, 0);
        crate::gendb_entry::results::lemma_columns_view(r, x, 1);
        crate::gendb_entry::results::lemma_columns_view(r, x, 2);
        crate::gendb_entry::results::lemma_columns_view(r, x, 3);
        assert(out[x] =~= orow(kb, kt, szl, cnt, ogs[x]));
    }
    assert(out.len() == n);
    assert forall|x: int, y: int| 0 <= x < y < out.len() implies keys_cmp(order_keys(), #[trigger] out[x], #[trigger] out[y]) <= 0 by {
        assert(ogs[x] == og[x] as int && ogs[y] == og[y] as int);
        assert(present(cnt, og[x] as int) && present(cnt, og[y] as int));
        assert(skey(cnt, rb, rt, rs, nt, ns, og[x] as int) < skey(cnt, rb, rt, rs, nt, ns, og[y] as int));
        lemma_key_order(kb, kt, szl, cnt, rb, rt, rs, ogs[x], ogs[y]);
    }
    assert forall|x: int, y: int| 0 <= x < out.len() && 0 <= y < out.len() && x != y implies out[x] != out[y] by {
        assert(ogs[x] == og[x] as int && ogs[y] == og[y] as int);
        assert(present(cnt, og[x] as int) && present(cnt, og[y] as int));
        if out[x] == out[y] {
            lemma_orow_injective(kb, kt, szl, cnt, ogs[x], ogs[y]);
            if x < y {
                assert(skey(cnt, rb, rt, rs, nt, ns, og[x] as int) < skey(cnt, rb, rt, rs, nt, ns, og[y] as int));
            } else {
                assert(skey(cnt, rb, rt, rs, nt, ns, og[y] as int) < skey(cnt, rb, rt, rs, nt, ns, og[x] as int));
            }
        }
    }
    assert forall|row: Row| #[trigger] out.contains(row) <==> exists|g: int| #[trigger] present(cnt, g)
        && row == orow(kb, kt, szl, cnt, g) by {
        if out.contains(row) {
            let x = choose|x: int| 0 <= x < out.len() && out[x] == row;
            assert(ogs[x] == og[x] as int);
            assert(present(cnt, og[x] as int));
        }
        if exists|g: int| #[trigger] present(cnt, g) && row == orow(kb, kt, szl, cnt, g) {
            let g = choose|g: int| #[trigger] present(cnt, g) && row == orow(kb, kt, szl, cnt, g);
            assert(og.contains(g as u32));
            let x = choose|x: int| 0 <= x < og.len() && og[x] == g as u32;
            assert(ogs[x] == og[x] as int);
            assert(g < 0x400_0000);
            assert(ogs[x] == g);
            assert(out[x] == row);
        }
    }
}

/// The result columns from the present groups `og` in ORDER BY order (`og_ok`).
fn emit_groups(bd: &TextDict, td: &TextDict, szl: &Vec<i64>, cnt: &Vec<u64>, rb: &Vec<usize>, rt: &Vec<usize>,
    rs: &Vec<usize>, og: &Vec<u32>) -> (r: ResultColumns)
    requires bd.wf(), td.wf(), tables_ok(bd.keys(), td.keys(), szl@, cnt@),
        ranks_ok(bd.keys(), td.keys(), szl@, rb@, rt@, rs@),
        og_ok(cnt@, rb@, rt@, rs@, td.keys().len() as int, szl@.len() as int, og@),
        cnt@.len() * bd.kbytes@.len() <= usize::MAX, cnt@.len() * td.kbytes@.len() <= usize::MAX,
    ensures ({
        let out = columns_view(r);
        &&& columns_wf(r)
        &&& out.no_duplicates()
        &&& sorted_by(order_keys(), out)
        &&& forall|row: Row| #[trigger] out.contains(row) <==> exists|g: int| #[trigger] present(cnt@, g)
            && row == orow(bd.keys(), td.keys(), szl@, cnt@, g)
    }),
{
    let ghost (kb, kt) = (bd.keys(), td.keys());
    let nt = td.count();
    let ns = szl.len();
    proof {
        let (nbi, nti, nsi) = (kb.len() as int, nt as int, ns as int);
        assert(nti * nsi <= cnt@.len()) by (nonlinear_arith) requires cnt@.len() == nbi * nti * nsi, nbi >= 1, nti >= 1, nsi >= 1;
    }
    let ntns = nt * ns;
    let n = og.len();
    let (mut bo, mut bb) = text_column();
    let (mut to, mut tb) = text_column();
    let mut sz: Vec<i64> = Vec::new();
    let mut cn: Vec<i64> = Vec::new();
    let ghost mut ogs: Seq<int> = Seq::empty();
    let mut i: usize = 0;
    while i < n
        invariant
            bd.wf(), td.wf(), tables_ok(kb, kt, szl@, cnt@), kb == bd.keys(), kt == td.keys(), nt == kt.len(),
            ns == szl@.len(), ntns == nt * ns, n == og@.len(), n <= cnt@.len(), i <= n, ogs.len() == i,
            og_ok(cnt@, rb@, rt@, rs@, nt as int, ns as int, og@),
            forall|x: int| 0 <= x < i ==> #[trigger] ogs[x] == og@[x] as int,
            emitted(kb, kt, szl@, cnt@, bo@, bb@, to@, tb@, sz@, cn@, ogs),
            cnt@.len() * bd.kbytes@.len() <= usize::MAX, cnt@.len() * td.kbytes@.len() <= usize::MAX,
            bb@.len() <= i * bd.kbytes@.len(), tb@.len() <= i * td.kbytes@.len(),
        decreases n - i,
    {
        let g = og[i] as usize;
        proof {
            assert(present(cnt@, og@[i as int] as int));
            let (kb_n, kt_n) = (bd.kbytes@.len() as int, td.kbytes@.len() as int);
            let (cn_, ii) = (cnt@.len() as int, i as int);
            assert(ii * kb_n + kb_n <= cn_ * kb_n) by (nonlinear_arith) requires ii + 1 <= cn_, kb_n >= 0;
            assert(ii * kt_n + kt_n <= cn_ * kt_n) by (nonlinear_arith) requires ii + 1 <= cn_, kt_n >= 0;
            assert((ii + 1) * kb_n == ii * kb_n + kb_n && (ii + 1) * kt_n == ii * kt_n + kt_n) by (nonlinear_arith);
        }
        push_row(&mut bo, &mut bb, &mut to, &mut tb, &mut sz, &mut cn, bd, td, szl, cnt, g, ntns, Ghost(ogs));
        proof {
            let ogs0 = ogs;
            ogs = ogs.push(g as int);
            assert forall|x: int| 0 <= x < i + 1 implies #[trigger] ogs[x] == og@[x] as int by {
                if x < i { assert(ogs[x] == ogs0[x]); }
            }
        }
        i = i + 1;
    }
    let ghost (gbo, gbb, gto, gtb, gsz, gcn) = (bo@, bb@, to@, tb@, sz@, cn@);
    let mut cols: Vec<ResultColumn> = Vec::new();
    cols.push(ResultColumn::Text { offsets: bo, bytes: bb });
    cols.push(ResultColumn::Text { offsets: to, bytes: tb });
    cols.push(ResultColumn::Int(sz));
    cols.push(ResultColumn::Int(cn));
    let r = ResultColumns { rows: n, columns: cols };
    proof {
        lemma_columns_og(r, kb, kt, szl@, cnt@, rb@, rt@, rs@, og@, ogs, gbo, gbb, gto, gtb, gsz, gcn);
    }
    r
}

/// The result columns: the rows of the present groups, sorted by the ORDER BY keys, without duplicates.
pub fn build_output(bd: &TextDict, td: &TextDict, szl: &Vec<i64>, cnt: &Vec<u64>) -> (r: ResultColumns)
    requires bd.wf(), td.wf(), tables_ok(bd.keys(), td.keys(), szl@, cnt@),
        cnt@.len() * bd.kbytes@.len() <= usize::MAX, cnt@.len() * td.kbytes@.len() <= usize::MAX,
    ensures ({
        let out = columns_view(r);
        &&& columns_wf(r)
        &&& out.no_duplicates()
        &&& sorted_by(order_keys(), out)
        &&& forall|row: Row| #[trigger] out.contains(row) <==> exists|g: int| #[trigger] present(cnt@, g)
            && row == orow(bd.keys(), td.keys(), szl@, cnt@, g)
    }),
{
    let ghost (kb, kt) = (bd.keys(), td.keys());
    proof {
        assert forall|i: int| 0 <= i < kb.len() implies bd.koff@[i] <= #[trigger] bd.koff@[i + 1] <= bd.kbytes@.len()
            && bd.kbytes@.subrange(bd.koff@[i] as int, bd.koff@[i + 1] as int) == kb[i] by {
            assert(bd.koff@[i + 1] <= bd.koff@[kb.len() as int]);
        }
        assert forall|i: int| 0 <= i < kt.len() implies td.koff@[i] <= #[trigger] td.koff@[i + 1] <= td.kbytes@.len()
            && td.kbytes@.subrange(td.koff@[i] as int, td.koff@[i + 1] as int) == kt[i] by {
            assert(td.koff@[i + 1] <= td.koff@[kt.len() as int]);
        }
    }
    let rb = text_ranks(&bd.kbytes, &bd.koff, Ghost(kb));
    let rt = text_ranks(&td.kbytes, &td.koff, Ghost(kt));
    let rs = int_ranks(szl);
    let nt = td.count();
    let ns = szl.len();
    proof {
        let (nbi, nti, nsi) = (kb.len() as int, nt as int, ns as int);
        assert(nti * nsi <= cnt@.len()) by (nonlinear_arith) requires cnt@.len() == nbi * nti * nsi, nbi >= 1, nti >= 1, nsi >= 1;
    }
    let ntns = nt * ns;
    // Counts below 2^20 (always on TPC-H data): the order by counting; otherwise sort the keys.
    match order_by_count(cnt, &rb, &rt, &rs, nt, ns, Ghost(kb), Ghost(kt), Ghost(szl@)) {
        Some(og) => {
            return emit_groups(bd, td, szl, cnt, &rb, &rt, &rs, &og);
        },
        None => {},
    }
    let (keys, ginv, Ghost(gs)) = make_keys(cnt, &rb, &rt, &rs, nt, ns, Ghost(kb), Ghost(kt), Ghost(szl@));
    let ghost keys0 = keys@;
    let sorted = sort_u64(keys);
    let n = sorted.len();
    // The keys are distinct, so the sorted keys are too.
    proof {
        assert forall|i: int, j: int| 0 <= i < j < keys0.len() implies keys0[i] != keys0[j] by {
            assert(present(cnt@, gs[i]) && present(cnt@, gs[j]));
            lemma_rc(kb, kt, szl@, cnt@, rb@, rt@, rs@, gs[j], gs[i]);
            lemma_rc(kb, kt, szl@, cnt@, rb@, rt@, rs@, gs[i], gs[j]);
            let (c1, c2) = (cnt@[gs[i]], cnt@[gs[j]]);
            lemma_pack((0xFFFF_FFFFu64 - c1) as u64, rc_of(rb@, rt@, rs@, nt as int, ns as int, gs[i]) as u64);
            lemma_pack((0xFFFF_FFFFu64 - c2) as u64, rc_of(rb@, rt@, rs@, nt as int, ns as int, gs[j]) as u64);
        }
        keys0.lemma_multiset_has_no_duplicates();
        sorted@.lemma_multiset_has_no_duplicates_conv();
    }
    let (mut bo, mut bb) = text_column();
    let (mut to, mut tb) = text_column();
    let mut sz: Vec<i64> = Vec::new();
    let mut cn: Vec<i64> = Vec::new();
    let ghost mut og: Seq<int> = Seq::empty();
    let mut i: usize = 0;
    while i < n
        invariant
            bd.wf(), td.wf(), tables_ok(kb, kt, szl@, cnt@), ranks_ok(kb, kt, szl@, rb@, rt@, rs@),
            kb == bd.keys(), kt == td.keys(), nt == kt.len(), ns == szl@.len(), ntns == nt * ns,
            n == sorted@.len(), i <= n, og.len() == i, ginv@.len() == cnt@.len(), n <= cnt@.len(),
            keys0.len() == gs.len(),
            forall|x: int| 0 <= x < gs.len() ==> #[trigger] present(cnt@, gs[x])
                && keys0[x] == skey(cnt@, rb@, rt@, rs@, nt as int, ns as int, gs[x])
                && ginv@[rc_of(rb@, rt@, rs@, nt as int, ns as int, gs[x])] == gs[x],
            sorted@.to_multiset() == keys0.to_multiset(),
            emitted(kb, kt, szl@, cnt@, bo@, bb@, to@, tb@, sz@, cn@, og),
            cnt@.len() * bd.kbytes@.len() <= usize::MAX, cnt@.len() * td.kbytes@.len() <= usize::MAX,
            bb@.len() <= i * bd.kbytes@.len(), tb@.len() <= i * td.kbytes@.len(),
            forall|x: int| 0 <= x < i ==> #[trigger] present(cnt@, og[x])
                && sorted@[x] == skey(cnt@, rb@, rt@, rs@, nt as int, ns as int, og[x]),
        decreases n - i,
    {
        let k = sorted[i];
        proof {
            sorted@.to_multiset_ensures();
            keys0.to_multiset_ensures();
            assert(sorted@.contains(k));
            assert(keys0.to_multiset().count(k) > 0);
            assert(keys0.contains(k));
        }
        let ghost j = choose|j: int| 0 <= j < keys0.len() && keys0[j] == k;
        let ghost g0 = gs[j];
        proof { assert(present(cnt@, g0)); }
        let g = key_group(k, &ginv, Ghost(cnt@), Ghost(g0), Ghost(kb), Ghost(kt), Ghost(szl@), Ghost(rb@), Ghost(rt@), Ghost(rs@));
        proof {
            let (kb_n, kt_n) = (bd.kbytes@.len() as int, td.kbytes@.len() as int);
            let (cn_, ii) = (cnt@.len() as int, i as int);
            assert(ii * kb_n + kb_n <= cn_ * kb_n) by (nonlinear_arith) requires ii + 1 <= cn_, kb_n >= 0;
            assert(ii * kt_n + kt_n <= cn_ * kt_n) by (nonlinear_arith) requires ii + 1 <= cn_, kt_n >= 0;
            assert((ii + 1) * kb_n == ii * kb_n + kb_n && (ii + 1) * kt_n == ii * kt_n + kt_n) by (nonlinear_arith);
        }
        push_row(&mut bo, &mut bb, &mut to, &mut tb, &mut sz, &mut cn, bd, td, szl, cnt, g, ntns, Ghost(og));
        proof { og = og.push(g as int); }
        i = i + 1;
    }
    let ghost (gbo, gbb, gto, gtb, gsz, gcn) = (bo@, bb@, to@, tb@, sz@, cn@);
    let mut cols: Vec<ResultColumn> = Vec::new();
    cols.push(ResultColumn::Text { offsets: bo, bytes: bb });
    cols.push(ResultColumn::Text { offsets: to, bytes: tb });
    cols.push(ResultColumn::Int(sz));
    cols.push(ResultColumn::Int(cn));
    let r = ResultColumns { rows: n, columns: cols };
    proof {
        lemma_columns(r, kb, kt, szl@, cnt@, rb@, rt@, rs@, sorted@, keys0, gs, og, gbo, gbb, gto, gtb, gsz, gcn);
    }
    r
}

} // verus!
