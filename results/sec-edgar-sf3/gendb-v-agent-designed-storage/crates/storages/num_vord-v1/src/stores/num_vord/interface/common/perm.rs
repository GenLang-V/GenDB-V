//! Permutations of row positions: `p` is a permutation of `0..n` when it has the multiset of `0..n`. Derived facts
//! (range, no duplicates, every position hit) and the transfer of a multiset through a permutation, which lets an
//! order-independent result (sum, count, group set) over a reordered table equal the one in canonical row order.
use vstd::prelude::*;

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

/// `0, 1, .., n - 1`.
pub open spec fn ident(n: nat) -> Seq<u64> {
    Seq::new(n, |k: int| k as u64)
}

/// `p` is a permutation of `0..n`.
pub open spec fn is_permutation(p: Seq<u64>, n: nat) -> bool {
    &&& n <= u64::MAX
    &&& p.to_multiset() == ident(n).to_multiset()
}

/// The positions `0..n` are distinct.
pub proof fn lemma_ident_no_duplicates(n: nat)
    requires n <= u64::MAX,
    ensures ident(n).no_duplicates(), ident(n).len() == n,
{
    let s = ident(n);
    assert forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j implies s[i] != s[j] by {}
}

/// A position of value `k` in `p` (meaningful when `p` holds `k`).
pub open spec fn position_of(p: Seq<u64>, k: int) -> int {
    choose|i: int| 0 <= i < p.len() && p[i] == k
}

/// A permutation of `0..n` has `n` entries, each `< n`, no two equal, and every position `< n` appears.
pub proof fn lemma_permutation_facts(p: Seq<u64>, n: nat)
    requires is_permutation(p, n),
    ensures
        p.len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] p[i] < n,
        p.no_duplicates(),
        forall|k: int| 0 <= k < n ==> 0 <= #[trigger] position_of(p, k) < n && p[position_of(p, k)] == k,
{
    let s = ident(n);
    lemma_ident_no_duplicates(n);
    assert(p.len() == p.to_multiset().len());
    assert(s.len() == s.to_multiset().len());
    assert forall|i: int| 0 <= i < n implies #[trigger] p[i] < n by {
        assert(p.contains(p[i]));
        assert(p.to_multiset().count(p[i]) > 0);
        assert(s.to_multiset().count(p[i]) > 0);
        assert(s.contains(p[i]));
        let k = choose|k: int| 0 <= k < s.len() && s[k] == p[i];
    }
    s.lemma_multiset_has_no_duplicates();
    assert forall|x: u64| p.to_multiset().contains(x) implies p.to_multiset().count(x) == 1 by {
        assert(s.to_multiset().contains(x));
    }
    p.lemma_multiset_has_no_duplicates_conv();
    assert forall|k: int| 0 <= k < n implies 0 <= #[trigger] position_of(p, k) < n && p[position_of(p, k)] == k by {
        assert(s[k] == k as u64);
        assert(s.contains(k as u64));
        assert(s.to_multiset().count(k as u64) > 0);
        assert(p.to_multiset().count(k as u64) > 0);
        assert(p.contains(k as u64));
    }
}

/// Equal multisets stay equal through any map.
pub proof fn lemma_multiset_map<A, B>(a: Seq<A>, b: Seq<A>, f: spec_fn(A) -> B)
    requires a.to_multiset() == b.to_multiset(),
    ensures a.map_values(f).to_multiset() == b.map_values(f).to_multiset(),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(b.len() == b.to_multiset().len());
        assert(a.map_values(f) =~= Seq::<B>::empty());
        assert(b.map_values(f) =~= Seq::<B>::empty());
    } else {
        let x = a.last();
        let ai = a.drop_last();
        assert(ai.push(x) =~= a);
        assert(a.to_multiset().count(x) > 0);
        assert(b.to_multiset().count(x) > 0);
        assert(b.contains(x));
        let i = choose|i: int| 0 <= i < b.len() && b[i] == x;
        let bi = b.remove(i);
        assert(bi.to_multiset() =~= b.to_multiset().remove(x));
        assert(ai.to_multiset() =~= a.to_multiset().remove(x));
        lemma_multiset_map(ai, bi, f);
        let bm = b.map_values(f);
        assert(bm.remove(i) =~= bi.map_values(f));
        assert(bm.remove(i).to_multiset() =~= bm.to_multiset().remove(bm[i]));
        assert(a.map_values(f) =~= ai.map_values(f).push(f(x)));
        assert(bm.to_multiset().count(f(x)) > 0) by {
            assert(bm.contains(f(x)));
        }
        assert(a.map_values(f).to_multiset() =~= bm.to_multiset());
    }
}

/// Rows read through a permutation of their positions have the rows' multiset.
pub proof fn lemma_permuted_multiset<T>(p: Seq<u64>, rows: Seq<T>)
    requires is_permutation(p, rows.len()),
    ensures Seq::new(rows.len(), |i: int| rows[p[i] as int]).to_multiset() == rows.to_multiset(),
{
    let n = rows.len();
    lemma_permutation_facts(p, n);
    let f = |k: u64| rows[k as int];
    lemma_multiset_map(p, ident(n), f);
    assert(Seq::new(n, |i: int| rows[p[i] as int]) =~= p.map_values(f));
    assert(rows =~= ident(n).map_values(f));
}

} // verus!
