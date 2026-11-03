//! Bags: permutation witnesses, bag equality of outcomes, and the multiset laws of the sequence operators the
//! relational operators are built from (engine toolkit; nothing here names a query, a table or a column).
//!
//! - `perm_of(p, a, b)`: an explicit witness that `b` is a reordering of `a` (`b[i] == a[p[i]]`, `p` injective).
//!   Operator proofs should carry such witnesses; `lemma_perm_bag` and `lemma_bag_perm` convert to and from
//!   multiset equality, the form `spec::order::ordered_ok` and `bag_eq` are stated in. `lemma_perm_id`,
//!   `lemma_perm_compose` and `lemma_perm_map` build witnesses.
//! - `bag_eq(x, y)`: two outcomes of a relational node agree up to row order: the same SQL error, or rows with
//!   equal multisets (obligation O1 of the design, section 4.1). It is an equivalence (`lemma_bag_eq_*`), and a
//!   bag-equal outcome of the statement body, sorted and sliced, is an allowed answer (`lemma_bag_eq_ordered`, O5).
//! - Multiset laws, all for `to_multiset` equality of the inputs: `map_values` (`lemma_map_bag`), the
//!   two-valued filter `link::join::keep` (`lemma_keep_bag`), sums of per-element terms (`sum_by`,
//!   `lemma_sum_by_bag`), concatenations of per-element blocks (`flat_by`, `lemma_flat_by_bag`,
//!   `lemma_flat_by_blocks`), and membership transfer (`lemma_bag_contains`).
//!
//! Every law is proved by the same induction: the last element of one side occurs in the other at some position
//! `m`; remove it there (`Seq::remove`) and recurse.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::OrderedQuery;
use crate::spec::order::*;
use crate::link::join::keep;
use crate::link::query::lemma_map_multiset;

verus! {

// ------------------------------------------------------------------------------------- permutation witnesses

/// `p` is a permutation witness from `a` to `b`: equal lengths, `b[i] == a[p[i]]`, and `p` injective.
pub open spec fn perm_of<A>(p: Seq<int>, a: Seq<A>, b: Seq<A>) -> bool {
    &&& a.len() == b.len()
    &&& p.len() == b.len()
    &&& forall|i: int| 0 <= i < b.len() ==> 0 <= #[trigger] p[i] < a.len() && b[i] == a[p[i]]
    &&& forall|i: int, j: int| 0 <= i < b.len() && 0 <= j < b.len() && i != j ==> #[trigger] p[i] != #[trigger] p[j]
}

/// The identity witness.
pub proof fn lemma_perm_id<A>(a: Seq<A>) -> (p: Seq<int>)
    ensures perm_of(p, a, a),
{
    Seq::new(a.len(), |i: int| i)
}

/// Witnesses compose: `a -> b` by `p` and `b -> c` by `q` give `a -> c` by `p[q[i]]`.
pub proof fn lemma_perm_compose<A>(p: Seq<int>, a: Seq<A>, b: Seq<A>, q: Seq<int>, c: Seq<A>) -> (r: Seq<int>)
    requires perm_of(p, a, b), perm_of(q, b, c),
    ensures perm_of(r, a, c),
{
    let r = Seq::new(c.len(), |i: int| p[q[i]]);
    assert forall|i: int| 0 <= i < c.len() implies 0 <= #[trigger] r[i] < a.len() && c[i] == a[r[i]] by {
        assert(0 <= q[i] < b.len());
    }
    assert forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c.len() && i != j implies #[trigger] r[i] != #[trigger] r[j] by {
        assert(q[i] != q[j]);
        assert(0 <= q[i] < b.len() && 0 <= q[j] < b.len());
    }
    r
}

/// A witness carries over to the images under any function.
pub proof fn lemma_perm_map<A, B>(p: Seq<int>, a: Seq<A>, b: Seq<A>, f: spec_fn(A) -> B)
    requires perm_of(p, a, b),
    ensures perm_of(p, a.map_values(f), b.map_values(f)),
{
    let (fa, fb) = (a.map_values(f), b.map_values(f));
    assert forall|i: int| 0 <= i < fb.len() implies 0 <= #[trigger] p[i] < fa.len() && fb[i] == fa[p[i]] by {
        assert(0 <= p[i] < a.len());
    }
}

/// Removing position `m = p[n - 1]` of `a` and the last element of `b` leaves a witness (positions above `m`
/// shift down by one).
pub proof fn lemma_perm_remove_last<A>(p: Seq<int>, a: Seq<A>, b: Seq<A>) -> (q: Seq<int>)
    requires perm_of(p, a, b), b.len() > 0,
    ensures
        0 <= p[b.len() - 1] < a.len(),
        perm_of(q, a.remove(p[b.len() - 1]), b.drop_last()),
{
    let n = b.len() - 1;
    let m = p[n];
    let a2 = a.remove(m);
    let b2 = b.drop_last();
    let q = Seq::new(n as nat, |i: int| if p[i] < m { p[i] } else { p[i] - 1 });
    assert forall|i: int| 0 <= i < b2.len() implies 0 <= #[trigger] q[i] < a2.len() && b2[i] == a2[q[i]] by {
        assert(p[i] != m);
        assert(0 <= p[i] < a.len());
    }
    assert forall|i: int, j: int| 0 <= i < b2.len() && 0 <= j < b2.len() && i != j implies #[trigger] q[i] != #[trigger] q[j] by {
        assert(p[i] != p[j]);
        assert(p[i] != m && p[j] != m);
    }
    q
}

// ------------------------------------------------------------------------------- witnesses and multisets

/// Removing an occurring element and putting it back gives the same multiset.
proof fn lemma_remove_insert<A>(s: Seq<A>, m: int)
    requires 0 <= m < s.len(),
    ensures s.to_multiset() == s.remove(m).to_multiset().insert(s[m]),
{
    s.to_multiset_ensures();
    assert(s.contains(s[m]));
    assert(s.to_multiset().count(s[m]) > 0);
    assert(s.remove(m).to_multiset() =~= s.to_multiset().remove(s[m]));
    assert(s.to_multiset() =~= s.to_multiset().remove(s[m]).insert(s[m]));
}

/// A permutation witness means equal multisets.
pub proof fn lemma_perm_bag<A>(p: Seq<int>, a: Seq<A>, b: Seq<A>)
    requires perm_of(p, a, b),
    ensures a.to_multiset() == b.to_multiset(),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a =~= b);
    } else {
        let n = b.len() - 1;
        let q = lemma_perm_remove_last(p, a, b);
        let m = p[n];
        lemma_perm_bag(q, a.remove(m), b.drop_last());
        lemma_remove_insert(a, m);
        b.drop_last().to_multiset_ensures();
        assert(b.drop_last().push(b[n]) =~= b);
    }
}

/// Equal multisets have a permutation witness.
pub proof fn lemma_bag_perm<A>(a: Seq<A>, b: Seq<A>) -> (p: Seq<int>)
    requires a.to_multiset() == b.to_multiset(),
    ensures perm_of(p, a, b),
    decreases b.len(),
{
    a.to_multiset_ensures();
    b.to_multiset_ensures();
    if b.len() == 0 {
        Seq::empty()
    } else {
        let n = b.len() - 1;
        let x = b[n];
        assert(b.contains(x));
        assert(b.to_multiset().count(x) > 0);
        assert(a.to_multiset().count(x) > 0);
        assert(a.contains(x));
        let m = choose|m: int| 0 <= m < a.len() && a[m] == x;
        let a2 = a.remove(m);
        let b2 = b.drop_last();
        b2.to_multiset_ensures();
        assert(b2.push(x) =~= b);
        assert(a2.to_multiset() =~= a.to_multiset().remove(x));
        assert(b2.to_multiset() =~= b.to_multiset().remove(x));
        let q = lemma_bag_perm(a2, b2);
        let p = Seq::new(b.len(), |i: int| if i < n { if q[i] < m { q[i] } else { q[i] + 1 } } else { m });
        assert forall|i: int| 0 <= i < b.len() implies 0 <= #[trigger] p[i] < a.len() && b[i] == a[p[i]] by {
            if i < n {
                assert(0 <= q[i] < a2.len());
                assert(b2[i] == a2[q[i]]);
            }
        }
        assert forall|i: int, j: int| 0 <= i < b.len() && 0 <= j < b.len() && i != j implies #[trigger] p[i] != #[trigger] p[j] by {
            if i < n && j < n {
                assert(q[i] != q[j]);
            }
        }
        p
    }
}

/// Every element of one side of a bag equality occurs on the other side.
pub proof fn lemma_bag_contains<A>(a: Seq<A>, b: Seq<A>, i: int) -> (j: int)
    requires a.to_multiset() == b.to_multiset(), 0 <= i < b.len(),
    ensures 0 <= j < a.len(), a[j] == b[i],
{
    a.to_multiset_ensures();
    b.to_multiset_ensures();
    assert(b.contains(b[i]));
    assert(b.to_multiset().count(b[i]) > 0);
    assert(a.to_multiset().count(b[i]) > 0);
    assert(a.contains(b[i]));
    choose|j: int| 0 <= j < a.len() && a[j] == b[i]
}

// ----------------------------------------------------------------------------------------- bag equality

/// Two outcomes of a relational node agree up to row order: the same SQL error, or rows with equal multisets.
pub open spec fn bag_eq(x: Result<Relation, SqlError>, y: Result<Relation, SqlError>) -> bool {
    match (x, y) {
        (Err(e), Err(f)) => e == f,
        (Ok(a), Ok(b)) => a.to_multiset() == b.to_multiset(),
        _ => false,
    }
}

/// Bag equality is reflexive.
pub proof fn lemma_bag_eq_refl(x: Result<Relation, SqlError>)
    ensures bag_eq(x, x),
{
}

/// Bag equality is symmetric.
pub proof fn lemma_bag_eq_symm(x: Result<Relation, SqlError>, y: Result<Relation, SqlError>)
    requires bag_eq(x, y),
    ensures bag_eq(y, x),
{
}

/// Bag equality is transitive (compose a plan's steps).
pub proof fn lemma_bag_eq_trans(x: Result<Relation, SqlError>, y: Result<Relation, SqlError>, z: Result<Relation, SqlError>)
    requires bag_eq(x, y), bag_eq(y, z),
    ensures bag_eq(x, z),
{
}

/// Rows with a witness are bag-equal outcomes.
pub proof fn lemma_perm_bag_eq(p: Seq<int>, a: Relation, b: Relation)
    requires perm_of(p, a, b),
    ensures bag_eq(Ok::<Relation, SqlError>(a), Ok::<Relation, SqlError>(b)),
{
    lemma_perm_bag(p, a, b);
}

/// Obligation O5: an outcome bag-equal to the statement body's is an allowed answer once its rows are put in a
/// sorted order (`p`, a reordering of them) and sliced by OFFSET/LIMIT; an error outcome is the body's error.
pub proof fn lemma_bag_eq_ordered(db: Database, oq: OrderedQuery, x: Result<Relation, SqlError>, p: Seq<Row>)
    requires
        bag_eq(x, denote_body(db, oq)),
        x matches Ok(rows) ==> p.to_multiset() == rows.to_multiset() && sorted_by(oq.keys, p),
    ensures
        match x {
            Err(e) => ordered_ok(db, oq, Err::<Relation, SqlError>(e)),
            Ok(_) => ordered_ok(db, oq, Ok::<Relation, SqlError>(slice_rows(p, oq.offset, oq.limit))),
        },
{
    if let Ok(rows) = x {
        let body = denote_body(db, oq)->Ok_0;
        assert(p.to_multiset() == body.to_multiset());
        assert(sorted_by(oq.keys, p));
    }
}

// ----------------------------------------------------------------------------------- multiset laws: map, keep

/// Equal multisets stay equal under `map_values` (`link::query::lemma_map_multiset`).
pub proof fn lemma_map_bag<A, B>(a: Seq<A>, b: Seq<A>, f: spec_fn(A) -> B)
    requires a.to_multiset() == b.to_multiset(),
    ensures a.map_values(f).to_multiset() == b.map_values(f).to_multiset(),
{
    lemma_map_multiset(a, b, f);
}

/// The multiplicity of a row in `keep(rows, f)`: its multiplicity in `rows` where `f` holds, else 0.
pub proof fn lemma_keep_count(rows: Seq<Row>, f: spec_fn(Row) -> bool, x: Row)
    ensures keep(rows, f).to_multiset().count(x) == if f(x) { rows.to_multiset().count(x) } else { 0 },
    decreases rows.len(),
{
    rows.to_multiset_ensures();
    if rows.len() == 0 {
        assert(keep(rows, f) =~= Seq::<Row>::empty());
        Seq::<Row>::empty().to_multiset_ensures();
    } else {
        let init = rows.drop_last();
        lemma_keep_count(init, f, x);
        init.to_multiset_ensures();
        keep(init, f).to_multiset_ensures();
        assert(init.push(rows.last()) =~= rows);
    }
}

/// Equal multisets stay equal under the two-valued filter `keep`.
pub proof fn lemma_keep_bag(a: Seq<Row>, b: Seq<Row>, f: spec_fn(Row) -> bool)
    requires a.to_multiset() == b.to_multiset(),
    ensures keep(a, f).to_multiset() == keep(b, f).to_multiset(),
{
    assert forall|x: Row| keep(a, f).to_multiset().count(x) == keep(b, f).to_multiset().count(x) by {
        lemma_keep_count(a, f, x);
        lemma_keep_count(b, f, x);
    }
    assert(keep(a, f).to_multiset() =~= keep(b, f).to_multiset());
}

// ------------------------------------------------------------------------------- multiset laws: sums

/// The sum of `f` over the elements, in order.
pub open spec fn sum_by<A>(s: Seq<A>, f: spec_fn(A) -> int) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { sum_by(s.drop_last(), f) + f(s.last()) }
}

/// Removing position `m` subtracts its term.
pub proof fn lemma_sum_by_remove<A>(s: Seq<A>, m: int, f: spec_fn(A) -> int)
    requires 0 <= m < s.len(),
    ensures sum_by(s, f) == sum_by(s.remove(m), f) + f(s[m]),
    decreases s.len(),
{
    let n = s.len() - 1;
    if m == n {
        assert(s.remove(m) =~= s.drop_last());
    } else {
        lemma_sum_by_remove(s.drop_last(), m, f);
        assert(s.remove(m).drop_last() =~= s.drop_last().remove(m));
        assert(s.remove(m).last() == s.last());
    }
}

/// Equal multisets have equal sums.
pub proof fn lemma_sum_by_bag<A>(a: Seq<A>, b: Seq<A>, f: spec_fn(A) -> int)
    requires a.to_multiset() == b.to_multiset(),
    ensures sum_by(a, f) == sum_by(b, f),
    decreases b.len(),
{
    a.to_multiset_ensures();
    b.to_multiset_ensures();
    if b.len() == 0 {
        assert(a.len() == 0);
    } else {
        let n = b.len() - 1;
        let m = lemma_bag_contains(a, b, n);
        let b2 = b.drop_last();
        b2.to_multiset_ensures();
        assert(b2.push(b[n]) =~= b);
        assert(a.remove(m).to_multiset() =~= a.to_multiset().remove(b[n]));
        assert(b2.to_multiset() =~= b.to_multiset().remove(b[n]));
        lemma_sum_by_bag(a.remove(m), b2, f);
        lemma_sum_by_remove(a, m, f);
    }
}

// ------------------------------------------------------------------------------- multiset laws: blocks

/// The concatenation of the blocks `f(s[0]) + f(s[1]) + ..` (the shape of a product or a join: one block of
/// output rows per input row).
pub open spec fn flat_by<A>(s: Seq<A>, f: spec_fn(A) -> Seq<Row>) -> Seq<Row>
    decreases s.len(),
{
    if s.len() == 0 { Seq::empty() } else { flat_by(s.drop_last(), f) + f(s.last()) }
}

/// The multiset of a concatenation is the sum of the multisets.
pub proof fn lemma_concat_bag<A>(x: Seq<A>, y: Seq<A>)
    ensures (x + y).to_multiset() == x.to_multiset().add(y.to_multiset()),
    decreases y.len(),
{
    x.to_multiset_ensures();
    y.to_multiset_ensures();
    if y.len() == 0 {
        assert(x + y =~= x);
        assert(x.to_multiset().add(y.to_multiset()) =~= x.to_multiset());
    } else {
        let yi = y.drop_last();
        lemma_concat_bag(x, yi);
        yi.to_multiset_ensures();
        (x + yi).to_multiset_ensures();
        assert(yi.push(y.last()) =~= y);
        assert((x + yi).push(y.last()) =~= x + y);
        assert((x + y).to_multiset() =~= x.to_multiset().add(y.to_multiset()));
    }
}

/// Removing position `m` removes its block from the multiset.
pub proof fn lemma_flat_by_remove<A>(s: Seq<A>, m: int, f: spec_fn(A) -> Seq<Row>)
    requires 0 <= m < s.len(),
    ensures flat_by(s, f).to_multiset() == flat_by(s.remove(m), f).to_multiset().add(f(s[m]).to_multiset()),
    decreases s.len(),
{
    let n = s.len() - 1;
    lemma_concat_bag(flat_by(s.drop_last(), f), f(s.last()));
    if m == n {
        assert(s.remove(m) =~= s.drop_last());
    } else {
        lemma_flat_by_remove(s.drop_last(), m, f);
        assert(s.remove(m).drop_last() =~= s.drop_last().remove(m));
        assert(s.remove(m).last() == s.last());
        lemma_concat_bag(flat_by(s.drop_last().remove(m), f), f(s.last()));
        assert(flat_by(s, f).to_multiset() =~= flat_by(s.remove(m), f).to_multiset().add(f(s[m]).to_multiset()));
    }
}

/// Block concatenations over equal multisets have equal multisets.
pub proof fn lemma_flat_by_bag<A>(a: Seq<A>, b: Seq<A>, f: spec_fn(A) -> Seq<Row>)
    requires a.to_multiset() == b.to_multiset(),
    ensures flat_by(a, f).to_multiset() == flat_by(b, f).to_multiset(),
    decreases b.len(),
{
    a.to_multiset_ensures();
    b.to_multiset_ensures();
    if b.len() == 0 {
        assert(a.len() == 0);
    } else {
        let n = b.len() - 1;
        let m = lemma_bag_contains(a, b, n);
        let b2 = b.drop_last();
        b2.to_multiset_ensures();
        assert(b2.push(b[n]) =~= b);
        assert(a.remove(m).to_multiset() =~= a.to_multiset().remove(b[n]));
        assert(b2.to_multiset() =~= b.to_multiset().remove(b[n]));
        lemma_flat_by_bag(a.remove(m), b2, f);
        lemma_flat_by_remove(a, m, f);
        lemma_concat_bag(flat_by(b2, f), f(b.last()));
    }
}

/// Blocks with equal multisets, element by element, give equal multisets.
pub proof fn lemma_flat_by_blocks<A>(s: Seq<A>, f: spec_fn(A) -> Seq<Row>, g: spec_fn(A) -> Seq<Row>)
    requires forall|i: int| 0 <= i < s.len() ==> (#[trigger] f(s[i])).to_multiset() == g(s[i]).to_multiset(),
    ensures flat_by(s, f).to_multiset() == flat_by(s, g).to_multiset(),
    decreases s.len(),
{
    if s.len() > 0 {
        let si = s.drop_last();
        assert forall|i: int| 0 <= i < si.len() implies (#[trigger] f(si[i])).to_multiset() == g(si[i]).to_multiset() by {
            assert(si[i] == s[i]);
        }
        lemma_flat_by_blocks(si, f, g);
        assert(f(s[s.len() - 1]).to_multiset() == g(s[s.len() - 1]).to_multiset());
        lemma_concat_bag(flat_by(si, f), f(s.last()));
        lemma_concat_bag(flat_by(si, g), g(s.last()));
    }
}

/// Block concatenations with equal blocks, element by element, are equal.
pub proof fn lemma_flat_by_ext<A>(s: Seq<A>, f: spec_fn(A) -> Seq<Row>, g: spec_fn(A) -> Seq<Row>)
    requires forall|i: int| 0 <= i < s.len() ==> #[trigger] f(s[i]) == g(s[i]),
    ensures flat_by(s, f) == flat_by(s, g),
    decreases s.len(),
{
    if s.len() > 0 {
        let si = s.drop_last();
        assert forall|i: int| 0 <= i < si.len() implies #[trigger] f(si[i]) == g(si[i]) by {
            assert(si[i] == s[i]);
        }
        lemma_flat_by_ext(si, f, g);
        assert(f(s[s.len() - 1]) == g(s[s.len() - 1]));
    }
}

/// The block of `x` filtered by `f`.
pub open spec fn kept_block<A>(g: spec_fn(A) -> Seq<Row>, f: spec_fn(Row) -> bool) -> spec_fn(A) -> Seq<Row> {
    |x: A| keep(g(x), f)
}

/// A two-valued filter of a block concatenation is the concatenation of the filtered blocks.
pub proof fn lemma_keep_flat_by<A>(s: Seq<A>, g: spec_fn(A) -> Seq<Row>, f: spec_fn(Row) -> bool)
    ensures keep(flat_by(s, g), f) == flat_by(s, kept_block(g, f)),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_keep_flat_by(s.drop_last(), g, f);
        crate::link::join::lemma_keep_append(flat_by(s.drop_last(), g), g(s.last()), f);
    }
}

} // verus!
