//! Grouping of the qualifying filings sorted by `(cik, name, pos)`: one pass that cuts the sorted list into maximal
//! runs of equal group key (`(cik, name)`, or `cik` alone) and sums each run's `sum` and `mass`.
//!
//! Every group's sum (mass) is the sum of `sum` (`mass`) over all filings of the list with its key (`ssum` with
//! `sum_f` / `mass_f`), group keys strictly increase, and every filing's key is a group key. A group whose mass
//! exceeds `i128::MAX` stops the pass (`Err`), with a filing whose key's total mass exceeds it.
use vstd::prelude::*;
use crate::agent::common::sort::{Filing, FilingOrder, filing_le, sorted_by};
use crate::agent::common::sums::*;

verus! {

/// The group key of a filing: `(cik, name)`, or `(cik, 0)` when grouping by cik alone.
pub open spec fn gkey(e: Filing, by_name: bool) -> (u64, u64) {
    (e.cik, if by_name { e.name } else { 0 })
}

pub open spec fn key_lt(a: (u64, u64), b: (u64, u64)) -> bool {
    a.0 < b.0 || (a.0 == b.0 && a.1 < b.1)
}

/// `sum` and `mass` of the filings of key `k` (0 for the others).
pub open spec fn sum_f(k: (u64, u64), by_name: bool) -> spec_fn(Filing) -> int {
    |e: Filing| if gkey(e, by_name) == k { e.sum as int } else { 0int }
}

pub open spec fn mass_f(k: (u64, u64), by_name: bool) -> spec_fn(Filing) -> int {
    |e: Filing| if gkey(e, by_name) == k { e.mass as int } else { 0int }
}

/// Each filing's sum is bounded by its mass, which fits `i128`.
pub open spec fn filings_ok(l: Seq<Filing>) -> bool {
    forall|t: int| 0 <= t < l.len() ==> {
        &&& (#[trigger] l[t]).mass <= i128::MAX as u128
        &&& l[t].sum as int <= l[t].mass as int
        &&& -(l[t].sum as int) <= l[t].mass as int
    }
}

/// The key of group `h` of the key word sequences.
pub open spec fn gk(cs: Seq<u64>, ns: Seq<u64>, h: int, by_name: bool) -> (u64, u64) {
    (cs[h], if by_name { ns[h] } else { 0 })
}

/// Group sums and masses are the list totals of their keys; masses fit `i128` and bound the sums.
#[verifier::opaque]
pub open spec fn gf_vals(cs: Seq<u64>, ns: Seq<u64>, ss: Seq<i128>, ms: Seq<u128>, l: Seq<Filing>, by_name: bool) -> bool {
    &&& forall|h: int| 0 <= h < ss.len() ==> #[trigger] ss[h] as int == ssum(l, sum_f(gk(cs, ns, h, by_name), by_name))
    &&& forall|h: int| 0 <= h < ss.len() ==> #[trigger] ms[h] as int == ssum(l, mass_f(gk(cs, ns, h, by_name), by_name))
    &&& forall|h: int| 0 <= h < ss.len() ==> #[trigger] ms[h] <= i128::MAX as u128
    &&& forall|h: int| 0 <= h < ss.len() ==> (#[trigger] ss[h]) as int <= ms[h] as int && -(ss[h] as int) <= ms[h] as int
}

/// Group keys strictly increase.
#[verifier::opaque]
pub open spec fn gf_sorted(cs: Seq<u64>, ns: Seq<u64>, ng: int, by_name: bool) -> bool {
    forall|a: int, b: int| 0 <= a < b < ng ==> key_lt(#[trigger] gk(cs, ns, a, by_name), #[trigger] gk(cs, ns, b, by_name))
}

/// Every filing before `t` has its key among the groups.
#[verifier::opaque]
pub open spec fn gf_cover(cs: Seq<u64>, ns: Seq<u64>, ng: int, l: Seq<Filing>, by_name: bool, t: int) -> bool {
    forall|i: int| #![trigger l[i]] 0 <= i < t ==> exists|h: int| 0 <= h < ng && #[trigger] gk(cs, ns, h, by_name) == gkey(l[i], by_name)
}

/// Every group has a filing before `t` with its key and its key words.
#[verifier::opaque]
pub open spec fn gf_wit(cs: Seq<u64>, ns: Seq<u64>, ng: int, l: Seq<Filing>, by_name: bool, t: int) -> bool {
    &&& forall|h: int| #![trigger gk(cs, ns, h, by_name)] 0 <= h < ng ==> exists|i: int| 0 <= i < t
        && gkey(#[trigger] l[i], by_name) == gk(cs, ns, h, by_name)
    &&& forall|h: int| #![trigger cs[h]] 0 <= h < ng ==> exists|i: int| 0 <= i < t && #[trigger] l[i].cik == cs[h]
        && l[i].name == ns[h]
}

/// The facts a pass establishes about its groups `(cs, ns, ss, ms)` over the filings before position `t`.
pub open spec fn groups_facts(cs: Seq<u64>, ns: Seq<u64>, ss: Seq<i128>, ms: Seq<u128>, l: Seq<Filing>,
    by_name: bool, t: int) -> bool {
    &&& cs.len() == ss.len() && ns.len() == ss.len() && ms.len() == ss.len()
    &&& gf_vals(cs, ns, ss, ms, l, by_name)
    &&& gf_sorted(cs, ns, ss.len() as int, by_name)
    &&& gf_cover(cs, ns, ss.len() as int, l, by_name, t)
    &&& gf_wit(cs, ns, ss.len() as int, l, by_name, t)
}

/// Every filing from position `t` on has a key above group `h`'s.
pub open spec fn tail_above(cs: Seq<u64>, ns: Seq<u64>, h: int, l: Seq<Filing>, by_name: bool, t: int) -> bool {
    forall|i: int| t <= i < l.len() ==> key_lt(gk(cs, ns, h, by_name), #[trigger] gkey(l[i], by_name))
}

/// The loop state of a pass at position `t`: the facts, and every later filing's key above the last group's.
pub open spec fn pass_inv(cs: Seq<u64>, ns: Seq<u64>, ss: Seq<i128>, ms: Seq<u128>, l: Seq<Filing>, by_name: bool,
    t: int) -> bool {
    &&& 0 <= t <= l.len()
    &&& groups_facts(cs, ns, ss, ms, l, by_name, t)
    &&& ss.len() > 0 ==> tail_above(cs, ns, ss.len() - 1, l, by_name, t)
    &&& ss.len() == 0 ==> t == 0
}

/// The groups of one pass: key words, sums and masses.
pub struct Groups {
    pub cik: Vec<u64>,
    pub name: Vec<u64>,
    pub sum: Vec<i128>,
    pub mass: Vec<u128>,
}

/// What a pass over `l` returns.
pub open spec fn groups_ok(g: Groups, l: Seq<Filing>, by_name: bool) -> bool {
    groups_facts(g.cik@, g.name@, g.sum@, g.mass@, l, by_name, l.len() as int)
}

/// In a list sorted by `(cik, name, pos)` the group keys never decrease.
pub proof fn lemma_sorted_keys(l: Seq<Filing>, by_name: bool, a: int, b: int)
    requires sorted_by(FilingOrder {}, l), 0 <= a < b < l.len(),
    ensures gkey(l[a], by_name) == gkey(l[b], by_name) || key_lt(gkey(l[a], by_name), gkey(l[b], by_name)),
{
    assert(filing_le(l[a], l[b]));
}

/// A maximal run `[a, b)` of key `k` carries the whole list's sum and mass of `k`.
proof fn lemma_group_total(l: Seq<Filing>, by_name: bool, k: (u64, u64), a: int, b: int, f: spec_fn(Filing) -> int,
    v: spec_fn(int) -> int)
    requires
        0 <= a <= b <= l.len(),
        forall|t: int| 0 <= t < l.len() && !(a <= t < b) ==> gkey(#[trigger] l[t], by_name) != k,
        forall|t: int| a <= t < b ==> gkey(#[trigger] l[t], by_name) == k,
        forall|t: int| 0 <= t < l.len() ==> #[trigger] f(l[t]) == if gkey(l[t], by_name) == k { v(t) } else { 0int },
    ensures ssum(l, f) == rsum(a, b, v),
{
    lemma_ssum_index(l, f);
    let g = |t: int| f(l[t]);
    lemma_rsum_split(0, a, l.len() as int, g);
    lemma_rsum_split(a, b, l.len() as int, g);
    assert forall|t: int| 0 <= t < a implies #[trigger] g(t) == 0 by {}
    assert forall|t: int| b <= t < l.len() implies #[trigger] g(t) == 0 by {}
    lemma_rsum_zero(0, a, g);
    lemma_rsum_zero(b, l.len() as int, g);
    assert forall|t: int| a <= t < b implies #[trigger] g(t) == v(t) by {}
    lemma_rsum_ext(a, b, g, v);
}

/// The empty pass.
proof fn lemma_pass_start(l: Seq<Filing>, by_name: bool)
    ensures pass_inv(Seq::empty(), Seq::empty(), Seq::empty(), Seq::empty(), l, by_name, 0),
{
    reveal(gf_vals);
    reveal(gf_sorted);
    reveal(gf_cover);
    reveal(gf_wit);
}

/// A run `[a, t)` whose mass exceeds the bound: the total mass of its key exceeds it.
proof fn lemma_run_overflow(l: Seq<Filing>, by_name: bool, k: (u64, u64), a: int, t: int)
    requires
        0 <= a < t <= l.len(),
        forall|i: int| a <= i < t ==> gkey(#[trigger] l[i], by_name) == k,
        rsum(a, t, |i: int| l[i].mass as int) > i128::MAX as int,
    ensures ssum(l, mass_f(k, by_name)) > i128::MAX as int,
{
    let mf = mass_f(k, by_name);
    let n = l.len() as int;
    lemma_ssum_index(l, mf);
    assert forall|i: int| 0 <= i < n implies mf(#[trigger] l[i]) >= 0 by {}
    lemma_rsum_sub_range(0, a, t, n, |i: int| mf(l[i]));
    assert forall|i: int| a <= i < t implies mf(#[trigger] l[i]) == l[i].mass as int by {}
    lemma_rsum_ext(a, t, |i: int| mf(l[i]), |i: int| l[i].mass as int);
}

/// The run `[a, t)` of key `k` is maximal: no filing outside it has key `k`.
proof fn lemma_run_maximal(cs: Seq<u64>, ns: Seq<u64>, ss: Seq<i128>, ms: Seq<u128>, l: Seq<Filing>, by_name: bool,
    a: int, t: int)
    requires
        pass_inv(cs, ns, ss, ms, l, by_name, a),
        sorted_by(FilingOrder {}, l),
        0 <= a < t <= l.len(),
        forall|i: int| a <= i < t ==> gkey(#[trigger] l[i], by_name) == gkey(l[a], by_name),
        t < l.len() ==> gkey(l[t], by_name) != gkey(l[a], by_name),
    ensures
        forall|i: int| 0 <= i < l.len() && !(a <= i < t) ==> gkey(#[trigger] l[i], by_name) != gkey(l[a], by_name),
        tail_above(cs.push(l[a].cik), ns.push(l[a].name), ss.len() as int, l, by_name, t),
        ss.len() > 0 ==> key_lt(gk(cs, ns, ss.len() - 1, by_name), gkey(l[a], by_name)),
{
    let k = gkey(l[a], by_name);
    let ng = ss.len() as int;
    let (cs2, ns2) = (cs.push(l[a].cik), ns.push(l[a].name));
    assert(gk(cs2, ns2, ng, by_name) == k);
    assert forall|i: int| 0 <= i < l.len() && !(a <= i < t) implies gkey(#[trigger] l[i], by_name) != k by {
        if i < a {
            reveal(gf_cover);
            reveal(gf_sorted);
            let hh = choose|h: int| 0 <= h < ng && #[trigger] gk(cs, ns, h, by_name) == gkey(l[i], by_name);
            let last = ng - 1;
            if hh < last {
                assert(key_lt(gk(cs, ns, hh, by_name), gk(cs, ns, last, by_name)));
            }
            assert(key_lt(gk(cs, ns, last, by_name), gkey(l[a], by_name)));
        } else {
            lemma_sorted_keys(l, by_name, a, t);
            if i > t {
                lemma_sorted_keys(l, by_name, t, i);
            }
        }
    }
    assert forall|i: int| t <= i < l.len() implies key_lt(gk(cs2, ns2, ng, by_name), #[trigger] gkey(l[i], by_name)) by {
        lemma_sorted_keys(l, by_name, a, i);
    }
}

/// Pushing the closed run's group keeps the values facts.
proof fn lemma_push_vals(cs: Seq<u64>, ns: Seq<u64>, ss: Seq<i128>, ms: Seq<u128>, l: Seq<Filing>, by_name: bool,
    a: int, s: i128, m: u128)
    requires
        cs.len() == ss.len() && ns.len() == ss.len() && ms.len() == ss.len(),
        gf_vals(cs, ns, ss, ms, l, by_name),
        0 <= a < l.len(),
        s as int == ssum(l, sum_f(gkey(l[a], by_name), by_name)),
        m as int == ssum(l, mass_f(gkey(l[a], by_name), by_name)),
        m <= i128::MAX as u128,
        s as int <= m as int, -(s as int) <= m as int,
    ensures gf_vals(cs.push(l[a].cik), ns.push(l[a].name), ss.push(s), ms.push(m), l, by_name),
{
    reveal(gf_vals);
    let ng = ss.len() as int;
    let (cs2, ns2, ss2, ms2) = (cs.push(l[a].cik), ns.push(l[a].name), ss.push(s), ms.push(m));
    assert(gk(cs2, ns2, ng, by_name) == gkey(l[a], by_name));
    assert forall|h: int| 0 <= h < ng implies #[trigger] gk(cs2, ns2, h, by_name) == gk(cs, ns, h, by_name) by {}
    assert forall|h: int| 0 <= h < ng + 1 implies #[trigger] ss2[h] as int == ssum(l, sum_f(gk(cs2, ns2, h, by_name), by_name)) by {
        if h < ng {
            assert(ss2[h] == ss[h]);
        }
    }
    assert forall|h: int| 0 <= h < ng + 1 implies #[trigger] ms2[h] as int == ssum(l, mass_f(gk(cs2, ns2, h, by_name), by_name)) by {
        if h < ng {
            assert(ms2[h] == ms[h]);
        }
    }
    assert forall|h: int| 0 <= h < ng + 1 implies #[trigger] ms2[h] <= i128::MAX as u128 by {
        if h < ng {
            assert(ms2[h] == ms[h]);
        }
    }
    assert forall|h: int| 0 <= h < ng + 1 implies (#[trigger] ss2[h]) as int <= ms2[h] as int
        && -(ss2[h] as int) <= ms2[h] as int by {
        if h < ng {
            assert(ss2[h] == ss[h] && ms2[h] == ms[h]);
        }
    }
}

/// Pushing a key above every group key keeps the keys sorted.
proof fn lemma_push_sorted(cs: Seq<u64>, ns: Seq<u64>, ng: int, by_name: bool, c: u64, nm: u64)
    requires
        cs.len() == ng && ns.len() == ng,
        gf_sorted(cs, ns, ng, by_name),
        ng > 0 ==> key_lt(gk(cs, ns, ng - 1, by_name), gk(cs.push(c), ns.push(nm), ng, by_name)),
    ensures gf_sorted(cs.push(c), ns.push(nm), ng + 1, by_name),
{
    reveal(gf_sorted);
    let (cs2, ns2) = (cs.push(c), ns.push(nm));
    assert forall|h: int| 0 <= h < ng implies #[trigger] gk(cs2, ns2, h, by_name) == gk(cs, ns, h, by_name) by {}
    assert forall|x: int, y: int| 0 <= x < y < ng + 1 implies
        key_lt(#[trigger] gk(cs2, ns2, x, by_name), #[trigger] gk(cs2, ns2, y, by_name)) by {
        if y == ng {
            let last = ng - 1;
            if x < last {
                assert(key_lt(gk(cs, ns, x, by_name), gk(cs, ns, last, by_name)));
            }
        } else {
            assert(key_lt(gk(cs, ns, x, by_name), gk(cs, ns, y, by_name)));
        }
    }
}

/// Pushing the run's group: every filing before `t` is covered.
proof fn lemma_push_cover(cs: Seq<u64>, ns: Seq<u64>, ng: int, l: Seq<Filing>, by_name: bool, a: int, t: int)
    requires
        cs.len() == ng && ns.len() == ng,
        gf_cover(cs, ns, ng, l, by_name, a),
        0 <= a < t <= l.len(),
        forall|i: int| a <= i < t ==> gkey(#[trigger] l[i], by_name) == gkey(l[a], by_name),
    ensures gf_cover(cs.push(l[a].cik), ns.push(l[a].name), ng + 1, l, by_name, t),
{
    reveal(gf_cover);
    let (cs2, ns2) = (cs.push(l[a].cik), ns.push(l[a].name));
    assert forall|i: int| #![trigger l[i]] 0 <= i < t implies exists|h: int| 0 <= h < ng + 1
        && #[trigger] gk(cs2, ns2, h, by_name) == gkey(l[i], by_name) by {
        if i < a {
            let hh = choose|h: int| 0 <= h < ng && #[trigger] gk(cs, ns, h, by_name) == gkey(l[i], by_name);
            assert(gk(cs2, ns2, hh, by_name) == gkey(l[i], by_name));
        } else {
            assert(gk(cs2, ns2, ng, by_name) == gkey(l[i], by_name));
        }
    }
}

/// Pushing the run's group: every group has a witness before `t`.
proof fn lemma_push_wit(cs: Seq<u64>, ns: Seq<u64>, ng: int, l: Seq<Filing>, by_name: bool, a: int, t: int)
    requires
        cs.len() == ng && ns.len() == ng,
        gf_wit(cs, ns, ng, l, by_name, a),
        0 <= a < t <= l.len(),
    ensures gf_wit(cs.push(l[a].cik), ns.push(l[a].name), ng + 1, l, by_name, t),
{
    reveal(gf_wit);
    let (cs2, ns2) = (cs.push(l[a].cik), ns.push(l[a].name));
    assert forall|h: int| #![trigger gk(cs2, ns2, h, by_name)] 0 <= h < ng + 1 implies exists|i: int| 0 <= i < t
        && gkey(#[trigger] l[i], by_name) == gk(cs2, ns2, h, by_name) by {
        if h < ng {
            let ii = choose|i: int| 0 <= i < a && gkey(#[trigger] l[i], by_name) == gk(cs, ns, h, by_name);
            assert(gkey(l[ii], by_name) == gk(cs2, ns2, h, by_name));
        } else {
            assert(gkey(l[a], by_name) == gk(cs2, ns2, h, by_name));
        }
    }
    assert forall|h: int| #![trigger cs2[h]] 0 <= h < ng + 1 implies exists|i: int| 0 <= i < t
        && #[trigger] l[i].cik == cs2[h] && l[i].name == ns2[h] by {
        if h < ng {
            let ii = choose|i: int| 0 <= i < a && #[trigger] l[i].cik == cs[h] && l[i].name == ns[h];
            assert(l[ii].cik == cs2[h] && l[ii].name == ns2[h]);
        } else {
            assert(l[a].cik == cs2[h] && l[a].name == ns2[h]);
        }
    }
}

/// Closing the maximal run `[a, t)` adds one group and keeps the loop state.
proof fn lemma_pass_step(cs: Seq<u64>, ns: Seq<u64>, ss: Seq<i128>, ms: Seq<u128>, l: Seq<Filing>, by_name: bool,
    a: int, t: int, s: i128, m: u128)
    requires
        pass_inv(cs, ns, ss, ms, l, by_name, a),
        sorted_by(FilingOrder {}, l),
        0 <= a < t <= l.len(),
        forall|i: int| a <= i < t ==> gkey(#[trigger] l[i], by_name) == gkey(l[a], by_name),
        t < l.len() ==> gkey(l[t], by_name) != gkey(l[a], by_name),
        s as int == rsum(a, t, |i: int| l[i].sum as int),
        m as int == rsum(a, t, |i: int| l[i].mass as int),
        m <= i128::MAX as u128,
        s as int <= m as int, -(s as int) <= m as int,
    ensures
        pass_inv(cs.push(l[a].cik), ns.push(l[a].name), ss.push(s), ms.push(m), l, by_name, t),
{
    let k = gkey(l[a], by_name);
    let ng = ss.len() as int;
    lemma_run_maximal(cs, ns, ss, ms, l, by_name, a, t);
    lemma_group_total(l, by_name, k, a, t, sum_f(k, by_name), |i: int| l[i].sum as int);
    lemma_group_total(l, by_name, k, a, t, mass_f(k, by_name), |i: int| l[i].mass as int);
    lemma_push_vals(cs, ns, ss, ms, l, by_name, a, s, m);
    assert(gk(cs.push(l[a].cik), ns.push(l[a].name), ng, by_name) == k);
    lemma_push_sorted(cs, ns, ng, by_name, l[a].cik, l[a].name);
    lemma_push_cover(cs, ns, ng, l, by_name, a, t);
    lemma_push_wit(cs, ns, ng, l, by_name, a, t);
}

/// One pass over the sorted list.
pub fn group_pass(l: &Vec<Filing>, by_name: bool) -> (r: Result<Groups, ()>)
    requires sorted_by(FilingOrder {}, l@), filings_ok(l@),
    ensures
        r matches Ok(g) ==> groups_ok(g, l@, by_name),
        r is Err ==> exists|t: int| 0 <= t < l@.len()
            && ssum(l@, mass_f(gkey(#[trigger] l@[t], by_name), by_name)) > i128::MAX as int,
{
    let n = l.len();
    // At most one group per filing: reserve once instead of growing.
    let mut g = Groups {
        cik: Vec::with_capacity(n), name: Vec::with_capacity(n), sum: Vec::with_capacity(n), mass: Vec::with_capacity(n),
    };
    proof { lemma_pass_start(l@, by_name); }
    let mut t: usize = 0;
    while t < n
        invariant
            n == l@.len(), t <= n,
            sorted_by(FilingOrder {}, l@), filings_ok(l@),
            pass_inv(g.cik@, g.name@, g.sum@, g.mass@, l@, by_name, t as int),
        decreases n - t,
    {
        let a = t;
        let k0 = l[t].cik;
        let k1 = if by_name { l[t].name } else { 0 };
        let ghost k = (k0, k1);
        assert(k == gkey(l@[a as int], by_name));
        let mut s: i128 = 0;
        let mut m: u128 = 0;
        while t < n && l[t].cik == k0 && (!by_name || l[t].name == k1)
            invariant
                n == l@.len(), a <= t <= n, a < n,
                filings_ok(l@),
                k == gkey(l@[a as int], by_name), k == (k0, k1),
                forall|i: int| a <= i < t ==> gkey(#[trigger] l@[i], by_name) == k,
                s as int == rsum(a as int, t as int, |i: int| l@[i].sum as int),
                m as int == rsum(a as int, t as int, |i: int| l@[i].mass as int),
                m <= i128::MAX as u128,
                s as int <= m as int, -(s as int) <= m as int,
            decreases n - t,
        {
            assert(gkey(l@[t as int], by_name) == k);
            assert(l@[t as int].mass <= i128::MAX as u128);
            proof {
                lemma_rsum_step(a as int, t as int, |i: int| l@[i].sum as int);
                lemma_rsum_step(a as int, t as int, |i: int| l@[i].mass as int);
            }
            let m2 = m + l[t].mass;
            if m2 > i128::MAX as u128 {
                proof {
                    lemma_run_overflow(l@, by_name, k, a as int, t + 1);
                }
                return Err(());
            }
            m = m2;
            s = s + l[t].sum;
            t = t + 1;
        }
        proof {
            lemma_pass_step(g.cik@, g.name@, g.sum@, g.mass@, l@, by_name, a as int, t as int, s, m);
        }
        g.cik.push(k0);
        g.name.push(l[a].name);
        g.sum.push(s);
        g.mass.push(m);
    }
    Ok(g)
}

} // verus!
