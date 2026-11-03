//! Group tables of Q4: one slot per priority, with a representative `orders` row (whose priority is the slot's key)
//! and the count of the rows of a row list `p` with that priority (`tbl_ok`). Keys are distinct and every row of `p`
//! has its key in the table. A task keeps its table in preallocated slots (`tbl_add_fixed`, no allocation); the calling
//! thread merges the task tables (`tbl_merge`) or builds one table by itself (`tbl_add_grow`).
//!
//! `tbl_ok` is opaque: the exec functions use it through the step lemmas below (one per kind of update).
use vstd::prelude::*;
use crate::agent::cols::*;
use crate::agent::lists::*;

verus! {

/// Key of slot `s`: the priority of its representative row.
pub open spec fn tkey(o: OCols, reps: Seq<usize>, s: int) -> Seq<u8> {
    prio(o, reps[s] as int)
}

/// Slot representatives are rows (`< no`).
pub open spec fn reps_ok(o: OCols, reps: Seq<usize>, ng: int) -> bool {
    forall|s: int| 0 <= s < ng ==> (#[trigger] reps[s]) < o.no
}

/// Some slot among the first `n` has key `kb`.
pub open spec fn in_tbl(o: OCols, reps: Seq<usize>, n: int, kb: Seq<u8>) -> bool {
    exists|g: int| 0 <= g < n && tkey(o, reps, g) == kb
}

/// The first `ng` slots are the groups of the row list `p`.
#[verifier::opaque]
pub open spec fn tbl_ok(o: OCols, reps: Seq<usize>, counts: Seq<u64>, ng: int, p: Seq<usize>) -> bool {
    &&& 0 <= ng <= reps.len()
    &&& ng <= counts.len()
    &&& forall|s: int| 0 <= s < ng ==> (#[trigger] reps[s]) < o.no && p.contains(reps[s])
    &&& forall|s: int| 0 <= s < ng ==> #[trigger] counts[s] as int == cnt_list(o, p, tkey(o, reps, s))
    &&& forall|s: int, t: int| 0 <= s < ng && 0 <= t < ng && s != t ==> tkey(o, reps, s) != tkey(o, reps, t)
    &&& forall|m: int| 0 <= m < p.len() ==> in_tbl(o, reps, ng, prio(o, (#[trigger] p[m]) as int))
}

/// The keys of the first `n` slots, as a predicate.
pub open spec fn tkeys(o: OCols, reps: Seq<usize>, n: int) -> spec_fn(Seq<u8>) -> bool {
    |kb: Seq<u8>| in_tbl(o, reps, n, kb)
}

/// What a table gives its users: bounds, representatives, counts, distinct keys, coverage of `p`.
pub proof fn lemma_tbl_facts(o: OCols, reps: Seq<usize>, counts: Seq<u64>, ng: int, p: Seq<usize>)
    requires tbl_ok(o, reps, counts, ng, p),
    ensures
        0 <= ng <= reps.len(),
        ng <= counts.len(),
        reps_ok(o, reps, ng),
        forall|s: int| 0 <= s < ng ==> p.contains(#[trigger] reps[s]),
        forall|s: int| 0 <= s < ng ==> #[trigger] counts[s] as int == cnt_list(o, p, tkey(o, reps, s)),
        forall|s: int, t: int| 0 <= s < ng && 0 <= t < ng && s != t ==> tkey(o, reps, s) != tkey(o, reps, t),
        forall|m: int| 0 <= m < p.len() ==> in_tbl(o, reps, ng, prio(o, (#[trigger] p[m]) as int)),
{
    reveal(tbl_ok);
}

/// The table of the empty list.
pub proof fn lemma_tbl_empty(o: OCols, reps: Seq<usize>, counts: Seq<u64>)
    ensures tbl_ok(o, reps, counts, 0, Seq::empty()),
{
    reveal(tbl_ok);
}

/// A key that no slot has counts no row of the list.
pub proof fn lemma_tbl_absent(o: OCols, reps: Seq<usize>, counts: Seq<u64>, ng: int, p: Seq<usize>, kb: Seq<u8>)
    requires
        tbl_ok(o, reps, counts, ng, p),
        !in_tbl(o, reps, ng, kb),
    ensures cnt_list(o, p, kb) == 0,
{
    reveal(tbl_ok);
    if cnt_list(o, p, kb) > 0 {
        lemma_cnt_witness(o, p, kb);
        let m = choose|m: int| 0 <= m < p.len() && prio(o, #[trigger] p[m] as int) == kb;
        assert(in_tbl(o, reps, ng, prio(o, p[m] as int)));
    }
}

/// Slots beyond `ng` do not matter to a table.
pub proof fn lemma_tbl_prefix(o: OCols, reps: Seq<usize>, counts: Seq<u64>, reps2: Seq<usize>, counts2: Seq<u64>, ng: int,
    p: Seq<usize>)
    requires
        tbl_ok(o, reps, counts, ng, p),
        ng <= reps2.len(),
        ng <= counts2.len(),
        forall|s: int| 0 <= s < ng ==> reps2[s] == reps[s] && counts2[s] == counts[s],
    ensures tbl_ok(o, reps2, counts2, ng, p),
{
    reveal(tbl_ok);
    assert forall|s: int| 0 <= s < ng implies #[trigger] tkey(o, reps2, s) == tkey(o, reps, s) by {
        assert(reps2[s] == reps[s]);
    }
    assert forall|s: int| 0 <= s < ng implies (#[trigger] reps2[s]) < o.no && p.contains(reps2[s]) by {
        assert(reps2[s] == reps[s]);
    }
    assert forall|s: int| 0 <= s < ng implies #[trigger] counts2[s] as int == cnt_list(o, p, tkey(o, reps2, s)) by {
        assert(counts2[s] == counts[s]);
        assert(tkey(o, reps2, s) == tkey(o, reps, s));
    }
    assert forall|s: int, t: int| 0 <= s < ng && 0 <= t < ng && s != t implies tkey(o, reps2, s) != tkey(o, reps2, t) by {
        assert(tkey(o, reps2, s) == tkey(o, reps, s));
        assert(tkey(o, reps2, t) == tkey(o, reps, t));
    }
    assert forall|m: int| 0 <= m < p.len() implies in_tbl(o, reps2, ng, prio(o, (#[trigger] p[m]) as int)) by {
        assert(in_tbl(o, reps, ng, prio(o, p[m] as int)));
        let s = choose|s: int| 0 <= s < ng && tkey(o, reps, s) == prio(o, p[m] as int);
        assert(tkey(o, reps2, s) == tkey(o, reps, s));
    }
}

/// Generic step: the list grows from `pa` to `pb`, whose counts differ from `pa`'s only at key `kb` (by `add`), and the
/// table's count of slot `g` (key `kb`) grows by `add`.
pub proof fn lemma_tbl_step_found(o: OCols, reps: Seq<usize>, c0: Seq<u64>, c1: Seq<u64>, n: int, g: int,
    pa: Seq<usize>, pb: Seq<usize>, kb: Seq<u8>, add: nat)
    requires
        tbl_ok(o, reps, c0, n, pa),
        0 <= g < n,
        tkey(o, reps, g) == kb,
        c1 == c0.update(g, (c0[g] + add) as u64),
        c0[g] + add <= u64::MAX,
        forall|x: Seq<u8>| #[trigger] cnt_list(o, pb, x) == cnt_list(o, pa, x) + if x == kb { add } else { 0 },
        forall|x: usize| pa.contains(x) ==> pb.contains(x),
        forall|m: int| 0 <= m < pb.len() ==> pa.contains(#[trigger] pb[m]) || prio(o, pb[m] as int) == kb,
    ensures tbl_ok(o, reps, c1, n, pb),
{
    reveal(tbl_ok);
    assert forall|s: int| 0 <= s < n implies (#[trigger] reps[s]) < o.no && pb.contains(reps[s]) by {}
    assert forall|s: int| 0 <= s < n implies #[trigger] c1[s] as int == cnt_list(o, pb, tkey(o, reps, s)) by {
        assert(cnt_list(o, pb, tkey(o, reps, s)) == cnt_list(o, pa, tkey(o, reps, s)) + if tkey(o, reps, s) == kb { add } else { 0 });
        if s != g {
            assert(tkey(o, reps, s) != kb);
        }
    }
    assert forall|m: int| 0 <= m < pb.len() implies in_tbl(o, reps, n, prio(o, (#[trigger] pb[m]) as int)) by {
        if pa.contains(pb[m]) {
            let x = choose|x: int| 0 <= x < pa.len() && pa[x] == pb[m];
            assert(in_tbl(o, reps, n, prio(o, pa[x] as int)));
        } else {
            assert(tkey(o, reps, g) == prio(o, pb[m] as int));
        }
    }
}

/// Generic step: as `lemma_tbl_step_found` for a key `kb` that no slot had; it gets slot `n` (representative in `pb`).
pub proof fn lemma_tbl_step_new(o: OCols, r0: Seq<usize>, c0: Seq<u64>, reps: Seq<usize>, counts: Seq<u64>, n: int,
    pa: Seq<usize>, pb: Seq<usize>, kb: Seq<u8>)
    requires
        tbl_ok(o, r0, c0, n, pa),
        n < reps.len(),
        n < counts.len(),
        forall|s: int| 0 <= s < n ==> reps[s] == r0[s] && counts[s] == c0[s],
        tkey(o, reps, n) == kb,
        reps[n] < o.no,
        pb.contains(reps[n]),
        !in_tbl(o, r0, n, kb),
        forall|x: Seq<u8>| #[trigger] cnt_list(o, pb, x) == cnt_list(o, pa, x) + if x == kb { counts[n] as int } else { 0 },
        forall|x: usize| pa.contains(x) ==> pb.contains(x),
        forall|m: int| 0 <= m < pb.len() ==> pa.contains(#[trigger] pb[m]) || prio(o, pb[m] as int) == kb,
    ensures tbl_ok(o, reps, counts, n + 1, pb),
{
    reveal(tbl_ok);
    lemma_tbl_absent(o, r0, c0, n, pa, kb);
    assert forall|s: int| 0 <= s < n implies #[trigger] tkey(o, reps, s) == tkey(o, r0, s) by {
        assert(reps[s] == r0[s]);
    }
    assert forall|s: int| 0 <= s < n + 1 implies (#[trigger] reps[s]) < o.no && pb.contains(reps[s]) by {
        if s < n {
            assert(reps[s] == r0[s]);
        }
    }
    assert forall|s: int| 0 <= s < n + 1 implies #[trigger] counts[s] as int == cnt_list(o, pb, tkey(o, reps, s)) by {
        if s < n {
            assert(tkey(o, reps, s) == tkey(o, r0, s));
            assert(counts[s] == c0[s]);
            assert(tkey(o, r0, s) != kb) by {
                if tkey(o, r0, s) == kb {
                    assert(in_tbl(o, r0, n, kb));
                }
            }
        }
    }
    assert forall|s: int, t: int| 0 <= s < n + 1 && 0 <= t < n + 1 && s != t implies tkey(o, reps, s) != tkey(o, reps, t) by {
        if s < n && t < n {
            assert(tkey(o, reps, s) == tkey(o, r0, s));
            assert(tkey(o, reps, t) == tkey(o, r0, t));
        } else {
            let u = if s < n { s } else { t };
            assert(tkey(o, reps, u) == tkey(o, r0, u));
            if tkey(o, r0, u) == kb {
                assert(in_tbl(o, r0, n, kb));
            }
        }
    }
    assert forall|m: int| 0 <= m < pb.len() implies in_tbl(o, reps, n + 1, prio(o, (#[trigger] pb[m]) as int)) by {
        if pa.contains(pb[m]) {
            let x = choose|x: int| 0 <= x < pa.len() && pa[x] == pb[m];
            assert(in_tbl(o, r0, n, prio(o, pa[x] as int)));
            let s = choose|s: int| 0 <= s < n && tkey(o, r0, s) == prio(o, pa[x] as int);
            assert(tkey(o, reps, s) == tkey(o, r0, s));
        } else {
            assert(tkey(o, reps, n) == prio(o, pb[m] as int));
        }
    }
}

/// The list with one more row `i` at the end, against the list: counts and members.
pub proof fn lemma_push_facts(o: OCols, p: Seq<usize>, i: usize)
    ensures
        forall|x: Seq<u8>| #[trigger] cnt_list(o, p.push(i), x) == cnt_list(o, p, x) + if x == prio(o, i as int) { 1nat } else { 0nat },
        forall|x: usize| p.contains(x) ==> p.push(i).contains(x),
        forall|m: int| 0 <= m < p.push(i).len() ==> p.contains(#[trigger] p.push(i)[m]) || prio(o, p.push(i)[m] as int) == prio(o, i as int),
        p.push(i).contains(i),
{
    let q = p.push(i);
    assert forall|x: Seq<u8>| #[trigger] cnt_list(o, q, x) == cnt_list(o, p, x) + if x == prio(o, i as int) { 1nat } else { 0nat } by {
        lemma_cnt_push(o, p, i, x);
    }
    assert forall|x: usize| p.contains(x) implies q.contains(x) by {
        let m = choose|m: int| 0 <= m < p.len() && p[m] == x;
        assert(q[m] == x);
    }
    assert forall|m: int| 0 <= m < q.len() implies p.contains(#[trigger] q[m]) || prio(o, q[m] as int) == prio(o, i as int) by {
        if m < p.len() {
            assert(q[m] == p[m]);
        }
    }
    assert(q[p.len() as int] == i);
}

/// Membership in a concatenation.
pub proof fn lemma_contains_concat(a: Seq<usize>, b: Seq<usize>, x: usize)
    ensures (a + b).contains(x) == (a.contains(x) || b.contains(x)),
{
    if (a + b).contains(x) {
        let m = choose|m: int| 0 <= m < (a + b).len() && (a + b)[m] == x;
        if m < a.len() {
            assert(a[m] == x);
        } else {
            assert(b[m - a.len()] == x);
        }
    }
    if a.contains(x) {
        let m = choose|m: int| 0 <= m < a.len() && a[m] == x;
        assert((a + b)[m] == x);
    }
    if b.contains(x) {
        let m = choose|m: int| 0 <= m < b.len() && b[m] == x;
        assert((a + b)[a.len() + m] == x);
    }
}

/// The byte extent `[a, b)` of the priority of order row `i` (its offsets as `usize`), `no_unwind`.
#[inline(always)]
pub fn prio_extent(o: &OCols, i: usize) -> (r: (usize, usize))
    requires ocols_wf(*o), i < o.no,
    ensures
        r.0 <= r.1 <= o.pbytes@.len(),
        r.0 == o.poff@[i as int],
        r.1 == o.poff@[i + 1],
        o.pbytes@.subrange(r.0 as int, r.1 as int) == prio(*o, i as int),
    no_unwind
{
    let a = o.poff[i];
    let b = o.poff[i + 1];
    assert(0 <= pview(*o).offsets[i as int] <= pview(*o).offsets[i + 1] <= pview(*o).bytes.len());
    // `pbytes.len()` (spec) carries the bound `<= usize::MAX` of the offsets.
    assert(0 <= a <= b <= o.pbytes.len());
    (a as usize, b as usize)
}

/// Bytes `[a, b)` of the priority bytes part equal the priority of row `r`, `no_unwind`.
#[inline(always)]
pub fn same_key(o: &OCols, a: usize, b: usize, r: usize) -> (eq: bool)
    requires
        ocols_wf(*o),
        a <= b <= o.pbytes@.len(),
        r < o.no,
    ensures eq == (o.pbytes@.subrange(a as int, b as int) == prio(*o, r as int)),
    no_unwind
{
    let (c, d) = prio_extent(o, r);
    let ghost x = o.pbytes@.subrange(a as int, b as int);
    let ghost y = o.pbytes@.subrange(c as int, d as int);
    if b - a != d - c {
        proof {
            assert(x.len() != y.len());
        }
        return false;
    }
    let n = b - a;
    let mut m: usize = 0;
    while m < n
        invariant
            ocols_wf(*o),
            a <= b <= o.pbytes@.len(),
            c <= d <= o.pbytes@.len(),
            n == b - a,
            n == d - c,
            m <= n,
            x == o.pbytes@.subrange(a as int, b as int),
            y == o.pbytes@.subrange(c as int, d as int),
            y == prio(*o, r as int),
            forall|t: int| 0 <= t < m ==> x[t] == y[t],
        decreases n - m,
    {
        if o.pbytes[a + m] != o.pbytes[c + m] {
            proof {
                assert(x[m as int] != y[m as int]);
            }
            return false;
        }
        m = m + 1;
    }
    proof {
        assert(x =~= y);
    }
    true
}

/// The slot whose key is the bytes `[a, b)`, or `ng` when no slot has it, `no_unwind`.
#[inline(always)]
pub fn find_slot(o: &OCols, reps: &Vec<usize>, ng: usize, a: usize, b: usize) -> (g: usize)
    requires
        ocols_wf(*o),
        a <= b <= o.pbytes@.len(),
        ng <= reps@.len(),
        reps_ok(*o, reps@, ng as int),
    ensures
        g <= ng,
        g < ng ==> tkey(*o, reps@, g as int) == o.pbytes@.subrange(a as int, b as int),
        g == ng ==> !in_tbl(*o, reps@, ng as int, o.pbytes@.subrange(a as int, b as int)),
    no_unwind
{
    let mut g: usize = 0;
    while g < ng
        invariant
            ocols_wf(*o),
            a <= b <= o.pbytes@.len(),
            ng <= reps@.len(),
            reps_ok(*o, reps@, ng as int),
            g <= ng,
            forall|s: int| 0 <= s < g ==> tkey(*o, reps@, s) != o.pbytes@.subrange(a as int, b as int),
        decreases ng - g,
    {
        if same_key(o, a, b, reps[g]) {
            return g;
        }
        g = g + 1;
    }
    g
}

/// Adds row `i` (priority bytes `[a, b)`) to a preallocated table, trying the slot `hint` first. `r.0` is `false`
/// when the key is new and every slot is used (the table is unchanged); `r.1` is the slot of the key.
#[inline(always)]
pub fn tbl_add_fixed(o: &OCols, reps: &mut Vec<usize>, counts: &mut Vec<u64>, ng: &mut usize, i: usize, a: usize,
    b: usize, hint: usize, Ghost(p): Ghost<Seq<usize>>) -> (r: (bool, usize))
    requires
        ocols_wf(*o),
        i < o.no,
        a <= b <= o.pbytes@.len(),
        o.pbytes@.subrange(a as int, b as int) == prio(*o, i as int),
        tbl_ok(*o, old(reps)@, old(counts)@, *old(ng) as int, p),
        p.len() < u64::MAX,
    ensures
        final(reps)@.len() == old(reps)@.len(),
        final(counts)@.len() == old(counts)@.len(),
        r.0 ==> tbl_ok(*o, final(reps)@, final(counts)@, *final(ng) as int, p.push(i)),
        r.0 ==> *final(ng) == *old(ng) || *final(ng) == *old(ng) + 1,
        r.0 ==> r.1 < *final(ng),
        !r.0 ==> final(reps)@ == old(reps)@ && final(counts)@ == old(counts)@ && *final(ng) == *old(ng)
            && (*old(ng) == old(reps)@.len() || *old(ng) == old(counts)@.len()),
    no_unwind
{
    let ghost kb = prio(*o, i as int);
    let ghost q = p.push(i);
    proof {
        lemma_tbl_facts(*o, reps@, counts@, *ng as int, p);
        lemma_push_facts(*o, p, i);
    }
    let n = *ng;
    let mut g = hint;
    if !(g < n && same_key(o, a, b, reps[g])) {
        g = find_slot(o, reps, n, a, b);
    }
    if g < n {
        proof {
            lemma_cnt_le(*o, q, kb);
            assert(counts@[g as int] as int == cnt_list(*o, p, kb));
        }
        let ghost c0 = counts@;
        let c = counts[g];
        counts[g] = c + 1;
        proof {
            lemma_tbl_step_found(*o, reps@, c0, counts@, n as int, g as int, p, q, kb, 1);
        }
        (true, g)
    } else if n < reps.len() && n < counts.len() {
        let ghost (r0, c0) = (reps@, counts@);
        reps[n] = i;
        counts[n] = 1;
        *ng = n + 1;
        proof {
            lemma_tbl_step_new(*o, r0, c0, reps@, counts@, n as int, p, q, kb);
        }
        (true, n)
    } else {
        (false, g)
    }
}

/// Adds row `i` to a table whose slots are exactly its groups (`ng == reps.len()`), growing it for a new key.
pub fn tbl_add_grow(o: &OCols, reps: &mut Vec<usize>, counts: &mut Vec<u64>, i: usize, Ghost(p): Ghost<Seq<usize>>)
    requires
        ocols_wf(*o),
        i < o.no,
        tbl_ok(*o, old(reps)@, old(counts)@, old(reps)@.len() as int, p),
        old(reps)@.len() == old(counts)@.len(),
        p.len() < u64::MAX,
    ensures
        final(reps)@.len() == final(counts)@.len(),
        tbl_ok(*o, final(reps)@, final(counts)@, final(reps)@.len() as int, p.push(i)),
{
    let (a, b) = prio_extent(o, i);
    let ghost (r0, c0) = (reps@, counts@);
    let n = reps.len();
    reps.push(0);
    counts.push(0);
    let mut ng = n;
    proof {
        lemma_tbl_prefix(*o, r0, c0, reps@, counts@, n as int, p);
    }
    let (added, _) = tbl_add_fixed(o, reps, counts, &mut ng, i, a, b, 0, Ghost(p));
    assert(added);
    if ng == n {
        let ghost (r1, c1) = (reps@, counts@);
        reps.pop();
        counts.pop();
        proof {
            lemma_tbl_prefix(*o, r1, c1, reps@, counts@, n as int, p.push(i));
        }
    }
}

/// The list of a merge in progress: `p1` and the rows of `p2` whose keys are among the first `s` keys of table 2.
pub open spec fn merged(o: OCols, p1: Seq<usize>, p2: Seq<usize>, reps2: Seq<usize>, s: int) -> Seq<usize> {
    p1 + key_filter(o, p2, tkeys(o, reps2, s))
}

/// One merge step on the lists: counts change only at the key of slot `s` of table 2 (by its full count), and rows
/// are kept.
pub proof fn lemma_merged_step(o: OCols, p1: Seq<usize>, p2: Seq<usize>, reps2: Seq<usize>, counts2: Seq<u64>, ng2: int, s: int)
    requires tbl_ok(o, reps2, counts2, ng2, p2), 0 <= s < ng2,
    ensures ({
        let pa = merged(o, p1, p2, reps2, s);
        let pb = merged(o, p1, p2, reps2, s + 1);
        let kb = tkey(o, reps2, s);
        &&& forall|x: Seq<u8>| #[trigger] cnt_list(o, pb, x) == cnt_list(o, pa, x) + if x == kb { counts2[s] as int } else { 0 }
        &&& forall|x: usize| pa.contains(x) ==> pb.contains(x)
        &&& forall|m: int| 0 <= m < pb.len() ==> pa.contains(#[trigger] pb[m]) || prio(o, pb[m] as int) == kb
        &&& pb.contains(reps2[s])
        &&& cnt_list(o, pa, kb) == cnt_list(o, p1, kb)
        &&& pb.len() <= p1.len() + p2.len()
    }),
{
    lemma_tbl_facts(o, reps2, counts2, ng2, p2);
    let ks = tkeys(o, reps2, s);
    let ks2 = tkeys(o, reps2, s + 1);
    let kb = tkey(o, reps2, s);
    let pa = merged(o, p1, p2, reps2, s);
    let pb = merged(o, p1, p2, reps2, s + 1);
    assert forall|x: Seq<u8>| #[trigger] ks2(x) == (ks(x) || x == kb) by {
        if ks2(x) {
            let t = choose|t: int| 0 <= t < s + 1 && tkey(o, reps2, t) == x;
            if t < s {
                assert(in_tbl(o, reps2, s, x));
            }
        }
        if ks(x) {
            let t = choose|t: int| 0 <= t < s && tkey(o, reps2, t) == x;
            assert(in_tbl(o, reps2, s + 1, x));
        }
        if x == kb {
            assert(in_tbl(o, reps2, s + 1, x));
        }
    }
    assert(!ks(kb)) by {
        if ks(kb) {
            let t = choose|t: int| 0 <= t < s && tkey(o, reps2, t) == kb;
        }
    }
    assert forall|x: Seq<u8>| #[trigger] cnt_list(o, pb, x) == cnt_list(o, pa, x) + if x == kb { counts2[s] as int } else { 0 } by {
        lemma_cnt_append(o, p1, key_filter(o, p2, ks), x);
        lemma_cnt_append(o, p1, key_filter(o, p2, ks2), x);
        lemma_cnt_key_filter(o, p2, ks, x);
        lemma_cnt_key_filter(o, p2, ks2, x);
    }
    assert forall|x: usize| pa.contains(x) implies pb.contains(x) by {
        lemma_contains_concat(p1, key_filter(o, p2, ks), x);
        lemma_contains_concat(p1, key_filter(o, p2, ks2), x);
        lemma_key_filter_contains(o, p2, ks, x);
        lemma_key_filter_contains(o, p2, ks2, x);
    }
    assert forall|m: int| 0 <= m < pb.len() implies pa.contains(#[trigger] pb[m]) || prio(o, pb[m] as int) == kb by {
        let x = pb[m];
        lemma_contains_concat(p1, key_filter(o, p2, ks), x);
        lemma_contains_concat(p1, key_filter(o, p2, ks2), x);
        lemma_key_filter_contains(o, p2, ks, x);
        lemma_key_filter_contains(o, p2, ks2, x);
        assert(pb.contains(x));
    }
    let a = reps2[s];
    lemma_key_filter_contains(o, p2, ks2, a);
    lemma_contains_concat(p1, key_filter(o, p2, ks2), a);
    lemma_cnt_append(o, p1, key_filter(o, p2, ks), kb);
    lemma_cnt_key_filter(o, p2, ks, kb);
    lemma_key_filter_len(o, p2, ks2);
}

/// The end of a merge: every row of `p2` has its key in table 2, so the filter keeps all of `p2`.
pub proof fn lemma_merged_end(o: OCols, p1: Seq<usize>, p2: Seq<usize>, reps2: Seq<usize>, counts2: Seq<u64>, ng2: int)
    requires tbl_ok(o, reps2, counts2, ng2, p2),
    ensures merged(o, p1, p2, reps2, ng2) == p1 + p2,
{
    lemma_tbl_facts(o, reps2, counts2, ng2, p2);
    let ks = tkeys(o, reps2, ng2);
    assert forall|m: int| 0 <= m < p2.len() implies ks(prio(o, #[trigger] p2[m] as int)) by {
        assert(in_tbl(o, reps2, ng2, prio(o, p2[m] as int)));
    }
    lemma_key_filter_all(o, p2, ks);
}

/// The start of a merge: no key of table 2 yet.
pub proof fn lemma_merged_start(o: OCols, p1: Seq<usize>, p2: Seq<usize>, reps2: Seq<usize>)
    ensures merged(o, p1, p2, reps2, 0) == p1,
{
    let ks = tkeys(o, reps2, 0);
    assert(ks =~= (|kb: Seq<u8>| false));
    lemma_key_filter_none(o, p2);
    assert(p1 + Seq::<usize>::empty() =~= p1);
}

/// A key filter is no longer than its list.
pub proof fn lemma_key_filter_len(o: OCols, s: Seq<usize>, ks: spec_fn(Seq<u8>) -> bool)
    ensures key_filter(o, s, ks).len() <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_key_filter_len(o, s.drop_last(), ks);
    }
}

/// Merges table 2 (the groups of `p2`) into the growable table 1 (the groups of `p1`): the groups of `p1 + p2`.
pub fn tbl_merge(o: &OCols, reps: &mut Vec<usize>, counts: &mut Vec<u64>, reps2: &Vec<usize>, counts2: &Vec<u64>,
    ng2: usize, Ghost(p1): Ghost<Seq<usize>>, Ghost(p2): Ghost<Seq<usize>>)
    requires
        ocols_wf(*o),
        tbl_ok(*o, old(reps)@, old(counts)@, old(reps)@.len() as int, p1),
        old(reps)@.len() == old(counts)@.len(),
        tbl_ok(*o, reps2@, counts2@, ng2 as int, p2),
        p1.len() + p2.len() <= u64::MAX,
    ensures
        final(reps)@.len() == final(counts)@.len(),
        tbl_ok(*o, final(reps)@, final(counts)@, final(reps)@.len() as int, p1 + p2),
{
    proof {
        lemma_merged_start(*o, p1, p2, reps2@);
        lemma_tbl_facts(*o, reps2@, counts2@, ng2 as int, p2);
    }
    let mut s: usize = 0;
    while s < ng2
        invariant
            ocols_wf(*o),
            tbl_ok(*o, reps2@, counts2@, ng2 as int, p2),
            reps_ok(*o, reps2@, ng2 as int),
            ng2 <= reps2@.len(),
            ng2 <= counts2@.len(),
            p1.len() + p2.len() <= u64::MAX,
            s <= ng2,
            reps@.len() == counts@.len(),
            tbl_ok(*o, reps@, counts@, reps@.len() as int, merged(*o, p1, p2, reps2@, s as int)),
        decreases ng2 - s,
    {
        let ghost pa = merged(*o, p1, p2, reps2@, s as int);
        let ghost pb = merged(*o, p1, p2, reps2@, s + 1);
        let ghost kb = tkey(*o, reps2@, s as int);
        proof {
            lemma_merged_step(*o, p1, p2, reps2@, counts2@, ng2 as int, s as int);
            lemma_tbl_facts(*o, reps@, counts@, reps@.len() as int, pa);
            lemma_tbl_facts(*o, reps2@, counts2@, ng2 as int, p2);
        }
        let r2 = reps2[s];
        let (a, b) = prio_extent(o, r2);
        let n = reps.len();
        let g = find_slot(o, reps, n, a, b);
        let c2 = counts2[s];
        if g < n {
            let c = counts[g];
            proof {
                assert(c as int == cnt_list(*o, pa, kb));
                assert(c2 as int == cnt_list(*o, p2, kb));
                lemma_cnt_append(*o, p1, p2, kb);
                lemma_cnt_le(*o, p1 + p2, kb);
            }
            let ghost c0 = counts@;
            counts.set(g, c + c2);
            proof {
                lemma_tbl_step_found(*o, reps@, c0, counts@, n as int, g as int, pa, pb, kb, c2 as nat);
            }
        } else {
            let ghost (r0, c0) = (reps@, counts@);
            reps.push(r2);
            counts.push(c2);
            proof {
                lemma_tbl_step_new(*o, r0, c0, reps@, counts@, n as int, pa, pb, kb);
            }
        }
        s = s + 1;
    }
    proof {
        lemma_merged_end(*o, p1, p2, reps2@, counts2@, ng2 as int);
    }
}

} // verus!
