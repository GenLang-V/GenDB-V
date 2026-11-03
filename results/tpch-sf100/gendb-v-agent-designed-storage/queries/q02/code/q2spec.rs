//! The Q2 normal form over the five tables (`tables::Tabs`), by row index.
//!
//! A part row is selected (`part_sel`) when `p_size = $1` and `p_type LIKE $2` is true. A partsupp row `k`
//! qualifies for a partkey value (`qual`) when it has that key and its supplier lies in region `$3` (`inreg`: some
//! supplier with its suppkey, some nation with that supplier's nationkey, some region with that nation's regionkey
//! named `$3`). It is minimal (`is_min`) when no qualifying row of the key costs less. A candidate (`Cand`) is one
//! selected part, one minimal partsupp row of its key, and the matching supplier and nation rows (`cand_ok`); a chunk
//! of candidates over the part rows `[a, b)` is sorted by (part, partsupp), stays in its rows and is complete
//! (`chunk_ok`); adjacent chunks concatenate (`lemma_chunk_append`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::fns::like::like_value;
use super::tables::*;

verus! {

/// The bound statement parameters: `$1` (p_size), `$2` (the LIKE pattern) and `$3` (r_name).
pub struct Prm {
    pub size: int,
    pub pat: Seq<u8>,
    pub rname: Seq<u8>,
}

/// One qualifying combination of rows: part, partsupp, supplier and nation row indices, and the supplier's
/// account balance coefficient (the first ORDER BY key).
#[derive(Clone, Copy)]
pub struct Cand {
    pub part: usize,
    pub ps: usize,
    pub supp: usize,
    pub nation: usize,
    pub acct: i64,
}

/// `v LIKE pat` with the statement's escape `\`.
pub open spec fn like_res(v: Val, pat: Seq<u8>) -> Result<Val, SqlError> {
    like_value(v, Val::Text(pat), Val::Text(seq![92u8]))
}

pub open spec fn like_true(v: Val, pat: Seq<u8>) -> bool {
    like_res(v, pat) == Ok::<Val, SqlError>(Val::Bool(true))
}

/// Part row `i` passes `p_size = $1 AND p_type LIKE $2`.
pub open spec fn part_sel(t: Tabs, m: Prm, i: int) -> bool {
    &&& 0 <= i < t.p.len()
    &&& t.p[i][5] == Val::Int(m.size)
    &&& like_true(t.p[i][4], m.pat)
}

/// Supplier row `j` has partsupp row `k`'s suppkey.
pub open spec fn smatch(t: Tabs, k: int, j: int) -> bool {
    0 <= j < t.s.len() && t.s[j][0] == t.ps[k][1]
}

/// Nation row `n` has supplier row `j`'s nationkey.
pub open spec fn nmatch(t: Tabs, j: int, n: int) -> bool {
    0 <= n < t.n.len() && t.n[n][0] == t.s[j][3]
}

/// Region row `r` has nation row `n`'s regionkey and is named `$3`.
pub open spec fn rmatch(t: Tabs, m: Prm, n: int, r: int) -> bool {
    0 <= r < t.r.len() && t.r[r][0] == t.n[n][2] && t.r[r][1] == Val::Text(m.rname)
}

/// Partsupp row `k`'s supplier lies in region `$3`.
pub open spec fn inreg(t: Tabs, m: Prm, k: int) -> bool {
    exists|j: int, n: int, r: int| #![trigger smatch(t, k, j), nmatch(t, j, n), rmatch(t, m, n, r)]
        smatch(t, k, j) && nmatch(t, j, n) && rmatch(t, m, n, r)
}

/// Partsupp row `k` has partkey value `pk` and its supplier lies in region `$3`.
pub open spec fn qual(t: Tabs, m: Prm, pk: Val, k: int) -> bool {
    &&& 0 <= k < t.ps.len()
    &&& t.ps[k][0] == pk
    &&& inreg(t, m, k)
}

/// The supply cost coefficient of partsupp row `k`.
pub open spec fn cost(t: Tabs, k: int) -> int {
    match t.ps[k][3] {
        Val::Num { coeff, .. } => coeff,
        _ => 0,
    }
}

/// Partsupp row `k` qualifies for `pk` and no qualifying row of `pk` costs less.
pub open spec fn is_min(t: Tabs, m: Prm, pk: Val, k: int) -> bool {
    &&& qual(t, m, pk, k)
    &&& forall|k2: int| #[trigger] qual(t, m, pk, k2) ==> cost(t, k) <= cost(t, k2)
}

/// A candidate: a selected part, a minimal partsupp row of its key, its supplier and nation rows (in region `$3`),
/// and the supplier's account balance.
pub open spec fn cand_ok(t: Tabs, m: Prm, c: Cand) -> bool {
    &&& part_sel(t, m, c.part as int)
    &&& is_min(t, m, t.p[c.part as int][0], c.ps as int)
    &&& smatch(t, c.ps as int, c.supp as int)
    &&& nmatch(t, c.supp as int, c.nation as int)
    &&& exists|r: int| #[trigger] rmatch(t, m, c.nation as int, r)
    &&& t.s[c.supp as int][5] == (Val::Num { coeff: c.acct as int, scale: 2 })
}

/// Candidates in strictly increasing (part, partsupp) order.
pub open spec fn cand_lt(a: Cand, b: Cand) -> bool {
    a.part < b.part || (a.part == b.part && a.ps < b.ps)
}

pub open spec fn sorted_cands(cs: Seq<Cand>) -> bool {
    forall|x: int, y: int| 0 <= x < y < cs.len() ==> #[trigger] cand_lt(cs[x], cs[y])
}

/// Every candidate's part row lies in `[a, b)`.
pub open spec fn in_rows(cs: Seq<Cand>, a: int, b: int) -> bool {
    forall|x: int| 0 <= x < cs.len() ==> a <= #[trigger] cs[x].part < b
}

/// `cs` has (part `i`, partsupp `k`).
pub open spec fn has_pair(cs: Seq<Cand>, i: int, k: int) -> bool {
    exists|x: int| 0 <= x < cs.len() && #[trigger] cs[x].part == i && cs[x].ps == k
}

/// Every selected part row of `[a, b)` with every minimal partsupp row of its key is in `cs`.
pub open spec fn complete(t: Tabs, m: Prm, cs: Seq<Cand>, a: int, b: int) -> bool {
    forall|i: int, k: int| a <= i < b && #[trigger] part_sel(t, m, i) && #[trigger] is_min(t, m, t.p[i][0], k)
        ==> has_pair(cs, i, k)
}

/// The candidates of the part rows `[a, b)`, exactly and in order.
pub open spec fn chunk_ok(t: Tabs, m: Prm, cs: Seq<Cand>, a: int, b: int) -> bool {
    &&& a <= b
    &&& forall|x: int| 0 <= x < cs.len() ==> #[trigger] cand_ok(t, m, cs[x])
    &&& sorted_cands(cs)
    &&& in_rows(cs, a, b)
    &&& complete(t, m, cs, a, b)
}

/// An empty range has no candidates.
pub proof fn lemma_chunk_empty(t: Tabs, m: Prm, a: int)
    ensures chunk_ok(t, m, Seq::<Cand>::empty(), a, a),
{
}

/// Adjacent chunks concatenate.
pub proof fn lemma_chunk_append(t: Tabs, m: Prm, c1: Seq<Cand>, c2: Seq<Cand>, a: int, b: int, c: int)
    requires chunk_ok(t, m, c1, a, b), chunk_ok(t, m, c2, b, c),
    ensures chunk_ok(t, m, c1 + c2, a, c),
{
    let cs = c1 + c2;
    assert forall|x: int| 0 <= x < cs.len() implies #[trigger] cand_ok(t, m, cs[x]) by {
        if x < c1.len() { assert(cs[x] == c1[x]); } else { assert(cs[x] == c2[x - c1.len()]); }
    }
    assert forall|x: int, y: int| 0 <= x < y < cs.len() implies #[trigger] cand_lt(cs[x], cs[y]) by {
        if y < c1.len() {
            assert(cs[x] == c1[x] && cs[y] == c1[y]);
        } else if x >= c1.len() {
            assert(cs[x] == c2[x - c1.len()] && cs[y] == c2[y - c1.len()]);
        } else {
            assert(cs[x] == c1[x] && cs[y] == c2[y - c1.len()]);
        }
    }
    assert forall|x: int| 0 <= x < cs.len() implies a <= #[trigger] cs[x].part < c by {
        if x < c1.len() { assert(cs[x] == c1[x]); } else { assert(cs[x] == c2[x - c1.len()]); }
    }
    assert forall|i: int, k: int| a <= i < c && #[trigger] part_sel(t, m, i) && #[trigger] is_min(t, m, t.p[i][0], k)
        implies has_pair(cs, i, k) by {
        if i < b {
            let x = choose|x: int| 0 <= x < c1.len() && #[trigger] c1[x].part == i && c1[x].ps == k;
            assert(cs[x] == c1[x]);
        } else {
            let x = choose|x: int| 0 <= x < c2.len() && #[trigger] c2[x].part == i && c2[x].ps == k;
            assert(cs[x + c1.len()] == c2[x]);
        }
    }
}

/// Candidates `a` and `b` differ in their (part, partsupp) rows.
pub open spec fn pair_ne(a: Cand, b: Cand) -> bool {
    a.part != b.part || a.ps != b.ps
}

/// Every candidate of the statement exactly once, in any order: the bag the statement's body denotes.
pub open spec fn cands_ok(t: Tabs, m: Prm, cs: Seq<Cand>) -> bool {
    &&& forall|x: int| 0 <= x < cs.len() ==> #[trigger] cand_ok(t, m, cs[x])
    &&& forall|x: int, y: int| 0 <= x < cs.len() && 0 <= y < cs.len() && x != y ==> pair_ne(#[trigger] cs[x], #[trigger] cs[y])
    &&& complete(t, m, cs, 0, t.p.len() as int)
}

/// The candidates of all part rows in (part, partsupp) order are the statement's candidates.
pub proof fn lemma_chunk_cands(t: Tabs, m: Prm, cs: Seq<Cand>)
    requires chunk_ok(t, m, cs, 0, t.p.len() as int),
    ensures cands_ok(t, m, cs),
{
    assert forall|x: int, y: int| 0 <= x < cs.len() && 0 <= y < cs.len() && x != y implies pair_ne(#[trigger] cs[x], #[trigger] cs[y]) by {
        if x < y { assert(cand_lt(cs[x], cs[y])); } else { assert(cand_lt(cs[y], cs[x])); }
    }
}

/// Primary keys of the tables the plan looks up by key: two rows of supplier, nation or region (or part) with
/// equal keys are one row.
pub open spec fn keys_unique(t: Tabs) -> bool {
    &&& forall|i: int, j: int| 0 <= i < t.p.len() && 0 <= j < t.p.len() && #[trigger] t.p[i][0] == #[trigger] t.p[j][0] ==> i == j
    &&& forall|i: int, j: int| 0 <= i < t.s.len() && 0 <= j < t.s.len() && #[trigger] t.s[i][0] == #[trigger] t.s[j][0] ==> i == j
    &&& forall|i: int, j: int| 0 <= i < t.n.len() && 0 <= j < t.n.len() && #[trigger] t.n[i][0] == #[trigger] t.n[j][0] ==> i == j
    &&& forall|i: int, j: int| 0 <= i < t.r.len() && 0 <= j < t.r.len() && #[trigger] t.r[i][0] == #[trigger] t.r[j][0] ==> i == j
}

} // verus!
