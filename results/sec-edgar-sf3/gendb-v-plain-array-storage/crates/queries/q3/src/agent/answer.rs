//! The answer from the groups: the group sums and the total as `i128` (else outside the capacity domain), the AVG
//! of the per-cik sums (the total over the cik count, PostgreSQL's numeric division), the groups above it and the
//! 100 largest of those, largest first.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::fns::div::*;
use crate::exec::value::*;
use crate::exec::fns::div::num_div_exec;
use crate::exec::numeric::num_cmp_exec;
use crate::link::query::view_rows;
use crate::agent::common::bytes::*;
use crate::agent::common::wide::*;
use crate::agent::groups::*;

verus! {

pub open spec fn in128(x: int) -> bool {
    i128::MIN as int <= x <= i128::MAX as int
}

/// The output row of group `i`.
pub open spec fn grow(g: &Groups, kc: &KeyCols, i: int) -> Row {
    seq![Val::Text(kc.name(g.rep@[i] as int)), Val::Int(kc.cik(g.rep@[i] as int)), Val::Num { coeff: wval(g.sum@[i]), scale: 4 }]
}

/// The candidates (groups above the AVG, in order) and the picked groups (the largest, largest first).
pub open spec fn pick_facts(sums: spec_fn(int) -> int, ng: int, ac: int, asc: nat, cand: Seq<int>, pick: Seq<int>) -> bool {
    &&& forall|t: int| 0 <= t < cand.len() ==> 0 <= #[trigger] cand[t] < ng
    &&& forall|t1: int, t2: int| 0 <= t1 < t2 < cand.len() ==> #[trigger] cand[t1] < #[trigger] cand[t2]
    &&& forall|i: int| 0 <= i < ng ==> ((num_cmp(#[trigger] sums(i), 4, ac, asc) > 0) == cand.contains(i))
    &&& pick.no_duplicates()
    &&& forall|u: int| 0 <= u < pick.len() ==> cand.contains(#[trigger] pick[u])
    &&& pick.len() == if cand.len() < 100 { cand.len() } else { 100 }
    &&& forall|u: int, v: int| 0 <= u < v < pick.len() ==> sums(#[trigger] pick[u]) >= sums(#[trigger] pick[v])
    &&& forall|u: int, t: int| 0 <= u < pick.len() && 0 <= t < cand.len() && !pick.contains(cand[t]) ==>
        sums(#[trigger] pick[u]) >= sums(#[trigger] cand[t])
}

pub open spec fn gsums(g: &Groups) -> spec_fn(int) -> int {
    |i: int| wval(g.sum@[i])
}

pub enum Outcome3 {
    Rows(Vec<Vec<EVal>>),
    Err(SqlError),
    Capacity,
}

/// What the answer reports about the groups.
pub open spec fn answer_ok(g: &Groups, kc: &KeyCols, r: &Outcome3, cand: Seq<int>, pick: Seq<int>, ac: int, asc: nat) -> bool {
    let ng = g.rep@.len() as int;
    let n = g.ncik as int;
    let tt = wval(g.total);
    match r {
        Outcome3::Rows(out) => (ng == 0 && out@.len() == 0) || {
            &&& ng > 0 && in128(tt)
            &&& forall|i: int| 0 <= i < ng ==> #[trigger] in128(wval(g.sum@[i]))
            &&& num_div(tt, 4, n, 0) == Ok::<Val, SqlError>(Val::Num { coeff: ac, scale: asc })
            &&& pick_facts(gsums(g), ng, ac, asc, cand, pick)
            &&& view_rows(out@) == pick.map_values(|i: int| grow(g, kc, i))
        },
        Outcome3::Err(e) => ng > 0 && in128(tt) && num_div(tt, 4, n, 0) == Err::<Val, SqlError>(*e),
        Outcome3::Capacity => ng > 0 && ((exists|i: int| 0 <= i < ng && !#[trigger] in128(wval(g.sum@[i])))
            || !in128(tt) || !num_div_fits(tt, 4, n, 0)),
    }
}

/// The group sums as `i128`, `None` when one is outside.
pub fn group_sums(g: &Groups) -> (r: Option<Vec<i128>>)
    requires g.sum@.len() == g.rep@.len(),
    ensures
        r matches Some(s) ==> s@.len() == g.sum@.len()
            && forall|i: int| 0 <= i < s@.len() ==> #[trigger] s@[i] as int == wval(g.sum@[i]),
        r is None ==> exists|i: int| 0 <= i < g.sum@.len() && !#[trigger] in128(wval(g.sum@[i])),
{
    let n = g.sum.len();
    let mut s: Vec<i128> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            n == g.sum@.len(), i <= n, s@.len() == i,
            forall|t: int| 0 <= t < i ==> #[trigger] s@[t] as int == wval(g.sum@[t]),
        decreases n - i,
    {
        match wide_to_i128(g.sum[i]) {
            Some(x) => s.push(x),
            None => {
                proof {
                    assert(!in128(wval(g.sum@[i as int])));
                }
                return None;
            },
        }
        i = i + 1;
    }
    Some(s)
}

/// The groups whose sum compares above `(ac, asc)`, in order.
pub fn above(sums: &Vec<i128>, ac: i128, asc: u32) -> (r: Vec<usize>)
    ensures
        forall|t: int| 0 <= t < r@.len() ==> #[trigger] r@[t] < sums@.len(),
        forall|t1: int, t2: int| 0 <= t1 < t2 < r@.len() ==> #[trigger] r@[t1] < #[trigger] r@[t2],
        forall|i: int| 0 <= i < sums@.len() ==> (num_cmp(#[trigger] sums@[i] as int, 4, ac as int, asc as nat) > 0)
            == r@.contains(i as usize),
{
    let n = sums.len();
    let mut r: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == sums@.len(), i <= n,
            forall|t: int| 0 <= t < r@.len() ==> #[trigger] r@[t] < i,
            forall|t1: int, t2: int| 0 <= t1 < t2 < r@.len() ==> #[trigger] r@[t1] < #[trigger] r@[t2],
            forall|i2: int| 0 <= i2 < i ==> (num_cmp(#[trigger] sums@[i2] as int, 4, ac as int, asc as nat) > 0)
                == r@.contains(i2 as usize),
        decreases n - i,
    {
        let c = num_cmp_exec(sums[i], 4, ac, asc);
        let ghost r0 = r@;
        if c > 0 {
            r.push(i);
        }
        proof {
            assert forall|i2: int| 0 <= i2 < i + 1 implies (num_cmp(#[trigger] sums@[i2] as int, 4, ac as int, asc as nat) > 0)
                == r@.contains(i2 as usize) by {
                if i2 < i {
                    if r0.contains(i2 as usize) {
                        let t = choose|t: int| 0 <= t < r0.len() && r0[t] == i2 as usize;
                        assert(r@[t] == i2 as usize);
                    }
                    if r@.contains(i2 as usize) {
                        let t = choose|t: int| 0 <= t < r@.len() && r@[t] == i2 as usize;
                        if t < r0.len() {
                            assert(r0[t] == i2 as usize);
                        }
                    }
                } else {
                    if c > 0 {
                        assert(r@[r0.len() as int] == i2 as usize);
                    } else {
                        if r@.contains(i2 as usize) {
                            let t = choose|t: int| 0 <= t < r@.len() && r@[t] == i2 as usize;
                            assert(r0[t] < i);
                        }
                    }
                }
            }
        }
        i = i + 1;
    }
    r
}

/// Distinct positions below `n`: at most `n` of them; exactly `n` of them hold every position.
proof fn lemma_positions(pos: Seq<int>, n: int)
    requires
        pos.no_duplicates(), 0 <= n,
        forall|u: int| 0 <= u < pos.len() ==> 0 <= #[trigger] pos[u] < n,
    ensures
        pos.len() <= n,
        pos.len() < n ==> exists|t: int| 0 <= t < n && !#[trigger] pos.contains(t),
{
    pos.unique_seq_to_set();
    let r = vstd::set_lib::set_int_range(0, n);
    assert(pos.to_set().subset_of(r)) by {
        assert forall|x: int| #[trigger] pos.to_set().contains(x) implies r.contains(x) by {
            let a = choose|a: int| 0 <= a < pos.len() && pos[a] == x;
        }
    }
    vstd::set_lib::lemma_int_range(0, n);
    vstd::set_lib::lemma_len_subset(pos.to_set(), r);
    if pos.len() < n {
        if forall|t: int| 0 <= t < n ==> #[trigger] pos.contains(t) {
            assert(r.subset_of(pos.to_set())) by {
                assert forall|x: int| #[trigger] r.contains(x) implies pos.to_set().contains(x) by {
                    assert(pos.contains(x));
                }
            }
            vstd::set_lib::lemma_len_subset(r, pos.to_set());
        }
    }
}

/// The (at most) `lim` largest candidates by sum, largest first (positions into `cand`: `pos`).
pub fn top(sums: &Vec<i128>, cand: &Vec<usize>, lim: usize) -> (r: (Vec<usize>, Ghost<Seq<int>>))
    requires
        forall|t: int| 0 <= t < cand@.len() ==> #[trigger] cand@[t] < sums@.len(),
        forall|t1: int, t2: int| 0 <= t1 < t2 < cand@.len() ==> #[trigger] cand@[t1] < #[trigger] cand@[t2],
    ensures ({
        let (out, pos) = (r.0@, r.1@);
        let n = cand@.len() as int;
        &&& out.len() == (if n < lim { n } else { lim as int })
        &&& pos.len() == out.len()
        &&& pos.no_duplicates()
        &&& forall|u: int| 0 <= u < pos.len() ==> 0 <= #[trigger] pos[u] < n && out[u] == cand@[pos[u]]
        &&& forall|u: int, v: int| 0 <= u < v < out.len() ==> sums@[#[trigger] out[u] as int] >= sums@[#[trigger] out[v] as int]
        &&& forall|u: int, t: int| 0 <= u < out.len() && 0 <= t < n && !pos.contains(t) ==>
            sums@[#[trigger] out[u] as int] >= sums@[#[trigger] cand@[t] as int]
    }),
{
    let n = cand.len();
    let k = if n < lim { n } else { lim };
    let mut taken: Vec<bool> = vec![false; n];
    let mut r: Vec<usize> = Vec::with_capacity(k);
    let ghost mut pos: Seq<int> = Seq::empty();
    proof {
        assert forall|t: int| 0 <= t < n implies !#[trigger] taken@[t] by {
            assert(cloned(false, taken@[t]));
        }
    }
    let mut step: usize = 0;
    while step < k
        invariant
            n == cand@.len(), taken@.len() == n, k <= n, step <= k, r@.len() == step, pos.len() == step,
            forall|t: int| 0 <= t < cand@.len() ==> #[trigger] cand@[t] < sums@.len(),
            pos.no_duplicates(),
            forall|u: int| 0 <= u < pos.len() ==> 0 <= #[trigger] pos[u] < n && r@[u] == cand@[pos[u]],
            forall|t: int| 0 <= t < n ==> #[trigger] taken@[t] == pos.contains(t),
            forall|u: int, v: int| 0 <= u < v < r@.len() ==> sums@[#[trigger] r@[u] as int] >= sums@[#[trigger] r@[v] as int],
            forall|u: int, t: int| 0 <= u < r@.len() && 0 <= t < n && !pos.contains(t) ==>
                sums@[#[trigger] r@[u] as int] >= sums@[#[trigger] cand@[t] as int],
        decreases k - step,
    {
        let mut best: usize = n;
        let mut bv: i128 = 0;
        let mut t: usize = 0;
        while t < n
            invariant
                n == cand@.len(), taken@.len() == n, t <= n, best <= n,
                forall|t2: int| 0 <= t2 < cand@.len() ==> #[trigger] cand@[t2] < sums@.len(),
                best < n ==> best < t && !taken@[best as int] && bv == sums@[cand@[best as int] as int],
                best == n ==> forall|t2: int| 0 <= t2 < t ==> #[trigger] taken@[t2],
                best < n ==> forall|t2: int| 0 <= t2 < t && !taken@[t2] ==> bv >= sums@[#[trigger] cand@[t2] as int],
            decreases n - t,
        {
            if !taken[t] {
                let v = sums[cand[t]];
                if best == n || v > bv {
                    best = t;
                    bv = v;
                }
            }
            t = t + 1;
        }
        proof {
            lemma_positions(pos, n as int);
            if best == n {
                let t2 = choose|t2: int| 0 <= t2 < n && !#[trigger] pos.contains(t2);
                assert(taken@[t2]);
            }
        }
        let ghost r0 = r@;
        let ghost pos0 = pos;
        taken.set(best, true);
        r.push(cand[best]);
        proof {
            pos = pos.push(best as int);
            assert(!pos0.contains(best as int));
            assert(pos.no_duplicates()) by {
                assert forall|a: int, b: int| 0 <= a < pos.len() && 0 <= b < pos.len() && a != b implies pos[a] != pos[b] by {
                    if a < pos0.len() && b < pos0.len() {
                        assert(pos[a] == pos0[a] && pos[b] == pos0[b]);
                    } else if a < pos0.len() {
                        assert(pos[a] == pos0[a]);
                        assert(pos0.contains(pos0[a]));
                    } else {
                        assert(pos[b] == pos0[b]);
                        assert(pos0.contains(pos0[b]));
                    }
                }
            }
            assert forall|t2: int| 0 <= t2 < n implies #[trigger] taken@[t2] == pos.contains(t2) by {
                if pos.contains(t2) && t2 != best {
                    let a = choose|a: int| 0 <= a < pos.len() && pos[a] == t2;
                    assert(pos0[a] == t2);
                }
                if pos0.contains(t2) {
                    let a = choose|a: int| 0 <= a < pos0.len() && pos0[a] == t2;
                    assert(pos[a] == t2);
                }
                if t2 == best {
                    assert(pos[pos0.len() as int] == t2);
                }
            }
            assert forall|u: int, v: int| 0 <= u < v < r@.len() implies sums@[#[trigger] r@[u] as int] >= sums@[#[trigger] r@[v] as int] by {
                if v < r0.len() {
                    assert(r@[u] == r0[u] && r@[v] == r0[v]);
                } else {
                    assert(r@[u] == r0[u]);
                    assert(!pos0.contains(best as int));
                }
            }
            assert forall|u: int, t2: int| 0 <= u < r@.len() && 0 <= t2 < n && !pos.contains(t2) implies
                sums@[#[trigger] r@[u] as int] >= sums@[#[trigger] cand@[t2] as int] by {
                assert(!pos0.contains(t2)) by {
                    if pos0.contains(t2) {
                        let a = choose|a: int| 0 <= a < pos0.len() && pos0[a] == t2;
                        assert(pos[a] == t2);
                    }
                }
                if u < r0.len() {
                    assert(r@[u] == r0[u]);
                } else {
                    assert(t2 != best);
                    assert(!taken@[t2]) by {
                        assert(pos[pos0.len() as int] == best);
                    }
                }
            }
        }
        step = step + 1;
    }
    (r, Ghost(pos))
}

/// A copy of the bytes.
pub fn copy_bytes(x: &[u8]) -> (r: Vec<u8>)
    ensures r@ == x@,
{
    let n = x.len();
    let mut r: Vec<u8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant n == x@.len(), i <= n, r@ == x@.subrange(0, i as int),
        decreases n - i,
    {
        r.push(x[i]);
        i = i + 1;
        proof {
            assert(r@ =~= x@.subrange(0, i as int));
        }
    }
    r
}

/// The output rows of the picked groups.
pub fn out_rows(g: &Groups, kc: &KeyCols, sums: &Vec<i128>, picked: &Vec<usize>) -> (r: Vec<Vec<EVal>>)
    requires
        kc.wf(), groups_cols(g, kc), g.sum@.len() == g.rep@.len(),
        sums@.len() == g.rep@.len(),
        forall|i: int| 0 <= i < sums@.len() ==> #[trigger] sums@[i] as int == wval(g.sum@[i]),
        forall|u: int| 0 <= u < picked@.len() ==> #[trigger] picked@[u] < g.rep@.len(),
    ensures
        view_rows(r@) == picked@.map_values(|i: usize| grow(g, kc, i as int)),
{
    let n = picked.len();
    let mut out: Vec<Vec<EVal>> = Vec::with_capacity(n);
    let mut t: usize = 0;
    while t < n
        invariant
            n == picked@.len(), t <= n, out@.len() == t,
            kc.wf(), groups_cols(g, kc), g.sum@.len() == g.rep@.len(), sums@.len() == g.rep@.len(),
            forall|i: int| 0 <= i < sums@.len() ==> #[trigger] sums@[i] as int == wval(g.sum@[i]),
            forall|u: int| 0 <= u < picked@.len() ==> #[trigger] picked@[u] < g.rep@.len(),
            forall|u: int| 0 <= u < t ==> view_row((#[trigger] out@[u])@) == grow(g, kc, picked@[u] as int),
        decreases n - t,
    {
        let i = picked[t];
        let j = g.rep[i];
        proof {
            lemma_kc_row(kc, j as int);
        }
        let a = kc.name_off[j] as usize;
        let b = kc.name_off[j + 1] as usize;
        let name = copy_bytes(sub_bytes(kc.name_bytes, a, b));
        let mut row: Vec<EVal> = Vec::with_capacity(3);
        row.push(EVal::Text(name));
        row.push(EVal::Int(kc.cik[j] as i64));
        row.push(EVal::Num { coeff: sums[i], scale: 4 });
        proof {
            assert(view_row(row@) =~= grow(g, kc, i as int));
        }
        out.push(row);
        t = t + 1;
    }
    proof {
        assert(view_rows(out@) =~= picked@.map_values(|i: usize| grow(g, kc, i as int)));
    }
    out
}

/// The candidates as group indices.
proof fn lemma_pick_cand(g: &Groups, sums: Seq<i128>, cand: Seq<usize>, ac: int, asc: nat)
    requires
        sums.len() == g.rep@.len(), g.sum@.len() == g.rep@.len(), g.rep@.len() <= usize::MAX,
        forall|i: int| 0 <= i < sums.len() ==> #[trigger] sums[i] as int == wval(g.sum@[i]),
        forall|t: int| 0 <= t < cand.len() ==> #[trigger] cand[t] < sums.len(),
        forall|t1: int, t2: int| 0 <= t1 < t2 < cand.len() ==> #[trigger] cand[t1] < #[trigger] cand[t2],
        forall|i: int| 0 <= i < sums.len() ==> (num_cmp(#[trigger] sums[i] as int, 4, ac, asc) > 0) == cand.contains(i as usize),
    ensures ({
        let cv = cand.map_values(|v: usize| v as int);
        &&& forall|t: int| 0 <= t < cv.len() ==> 0 <= #[trigger] cv[t] < g.rep@.len()
        &&& forall|t1: int, t2: int| 0 <= t1 < t2 < cv.len() ==> #[trigger] cv[t1] < #[trigger] cv[t2]
        &&& forall|i: int| 0 <= i < g.rep@.len() ==> ((num_cmp(#[trigger] gsums(g)(i), 4, ac, asc) > 0) == cv.contains(i))
    }),
{
    let sf = gsums(g);
    let cv = cand.map_values(|v: usize| v as int);
    assert forall|t1: int, t2: int| 0 <= t1 < t2 < cv.len() implies #[trigger] cv[t1] < #[trigger] cv[t2] by {
        assert(cand[t1] < cand[t2]);
    }
    assert forall|i: int| 0 <= i < g.rep@.len() implies ((num_cmp(#[trigger] sf(i), 4, ac, asc) > 0) == cv.contains(i)) by {
        assert(sums[i] as int == sf(i));
        assert((i as usize) as int == i);
        if cand.contains(i as usize) {
            let t = choose|t: int| 0 <= t < cand.len() && cand[t] == i as usize;
            assert(cv[t] == i);
        }
        if cv.contains(i) {
            let t = choose|t: int| 0 <= t < cv.len() && cv[t] == i;
            assert(cand[t] == i as usize);
        }
    }
}

/// The picked groups: distinct candidates.
proof fn lemma_pick_set(cand: Seq<usize>, picked: Seq<usize>, pos: Seq<int>)
    requires
        forall|t1: int, t2: int| 0 <= t1 < t2 < cand.len() ==> #[trigger] cand[t1] < #[trigger] cand[t2],
        pos.len() == picked.len(), pos.no_duplicates(),
        forall|u: int| 0 <= u < pos.len() ==> 0 <= #[trigger] pos[u] < cand.len() && picked[u] == cand[pos[u]],
    ensures ({
        let cv = cand.map_values(|v: usize| v as int);
        let pv = picked.map_values(|v: usize| v as int);
        &&& pv.no_duplicates()
        &&& forall|u: int| 0 <= u < pv.len() ==> cv.contains(#[trigger] pv[u])
        &&& forall|t: int| 0 <= t < cv.len() && pv.contains(cv[t]) ==> #[trigger] pos.contains(t)
    }),
{
    let cv = cand.map_values(|v: usize| v as int);
    let pv = picked.map_values(|v: usize| v as int);
    assert forall|a: int, b: int| 0 <= a < pv.len() && 0 <= b < pv.len() && a != b implies pv[a] != pv[b] by {
        assert(pos[a] != pos[b]);
        if pos[a] < pos[b] {
            assert(cand[pos[a]] < cand[pos[b]]);
        } else {
            assert(cand[pos[b]] < cand[pos[a]]);
        }
    }
    assert forall|u: int| 0 <= u < pv.len() implies cv.contains(#[trigger] pv[u]) by {
        assert(cv[pos[u]] == pv[u]);
    }
    assert forall|t: int| 0 <= t < cv.len() && pv.contains(cv[t]) implies #[trigger] pos.contains(t) by {
        let a = choose|a: int| 0 <= a < pv.len() && pv[a] == cv[t];
        assert(cand[pos[a]] == cand[t]);
        if pos[a] < t {
            assert(cand[pos[a]] < cand[t]);
        } else if pos[a] > t {
            assert(cand[t] < cand[pos[a]]);
        }
        assert(pos[a] == t);
    }
}

/// The picked groups' order and their dominance over the other candidates.
proof fn lemma_pick_order(g: &Groups, sums: Seq<i128>, cand: Seq<usize>, picked: Seq<usize>, pos: Seq<int>)
    requires
        sums.len() == g.rep@.len(), g.sum@.len() == g.rep@.len(),
        forall|i: int| 0 <= i < sums.len() ==> #[trigger] sums[i] as int == wval(g.sum@[i]),
        forall|t: int| 0 <= t < cand.len() ==> #[trigger] cand[t] < sums.len(),
        pos.len() == picked.len(),
        forall|u: int| 0 <= u < pos.len() ==> 0 <= #[trigger] pos[u] < cand.len() && picked[u] == cand[pos[u]],
        forall|u: int, v: int| 0 <= u < v < picked.len() ==> sums[#[trigger] picked[u] as int] >= sums[#[trigger] picked[v] as int],
        forall|u: int, t: int| 0 <= u < picked.len() && 0 <= t < cand.len() && !pos.contains(t) ==>
            sums[#[trigger] picked[u] as int] >= sums[#[trigger] cand[t] as int],
        forall|t: int| 0 <= t < cand.len() && picked.map_values(|v: usize| v as int).contains(cand[t] as int) ==> #[trigger] pos.contains(t),
    ensures ({
        let cv = cand.map_values(|v: usize| v as int);
        let pv = picked.map_values(|v: usize| v as int);
        let sf = gsums(g);
        &&& forall|u: int, v: int| 0 <= u < v < pv.len() ==> sf(#[trigger] pv[u]) >= sf(#[trigger] pv[v])
        &&& forall|u: int, t: int| 0 <= u < pv.len() && 0 <= t < cv.len() && !pv.contains(cv[t]) ==>
            sf(#[trigger] pv[u]) >= sf(#[trigger] cv[t])
    }),
{
    let sf = gsums(g);
    let cv = cand.map_values(|v: usize| v as int);
    let pv = picked.map_values(|v: usize| v as int);
    assert forall|u: int, v: int| 0 <= u < v < pv.len() implies sf(#[trigger] pv[u]) >= sf(#[trigger] pv[v]) by {
        assert(sums[picked[u] as int] >= sums[picked[v] as int]);
        assert(picked[u] < sums.len()) by { assert(picked[u] == cand[pos[u]]); }
        assert(picked[v] < sums.len()) by { assert(picked[v] == cand[pos[v]]); }
    }
    assert forall|u: int, t: int| 0 <= u < pv.len() && 0 <= t < cv.len() && !pv.contains(cv[t]) implies
        sf(#[trigger] pv[u]) >= sf(#[trigger] cv[t]) by {
        assert(cv[t] == cand[t] as int);
        assert(!pos.contains(t)) by {
            if pos.contains(t) {
                let a = choose|a: int| 0 <= a < pos.len() && pos[a] == t;
                assert(pv[a] == cv[t]);
            }
        }
        assert(sums[picked[u] as int] >= sums[cand[t] as int]);
        assert(picked[u] < sums.len()) by { assert(picked[u] == cand[pos[u]]); }
    }
}

/// The candidates and the picked groups as group indices.
proof fn lemma_pick(g: &Groups, sums: Seq<i128>, cand: Seq<usize>, picked: Seq<usize>, pos: Seq<int>, ac: int, asc: nat)
    requires
        sums.len() == g.rep@.len(), g.sum@.len() == g.rep@.len(), g.rep@.len() <= usize::MAX,
        forall|i: int| 0 <= i < sums.len() ==> #[trigger] sums[i] as int == wval(g.sum@[i]),
        forall|t: int| 0 <= t < cand.len() ==> #[trigger] cand[t] < sums.len(),
        forall|t1: int, t2: int| 0 <= t1 < t2 < cand.len() ==> #[trigger] cand[t1] < #[trigger] cand[t2],
        forall|i: int| 0 <= i < sums.len() ==> (num_cmp(#[trigger] sums[i] as int, 4, ac, asc) > 0) == cand.contains(i as usize),
        picked.len() == (if cand.len() < 100 { cand.len() as int } else { 100 }),
        pos.len() == picked.len(), pos.no_duplicates(),
        forall|u: int| 0 <= u < pos.len() ==> 0 <= #[trigger] pos[u] < cand.len() && picked[u] == cand[pos[u]],
        forall|u: int, v: int| 0 <= u < v < picked.len() ==> sums[#[trigger] picked[u] as int] >= sums[#[trigger] picked[v] as int],
        forall|u: int, t: int| 0 <= u < picked.len() && 0 <= t < cand.len() && !pos.contains(t) ==>
            sums[#[trigger] picked[u] as int] >= sums[#[trigger] cand[t] as int],
    ensures
        pick_facts(gsums(g), g.rep@.len() as int, ac, asc, cand.map_values(|v: usize| v as int),
            picked.map_values(|v: usize| v as int)),
{
    lemma_pick_cand(g, sums, cand, ac, asc);
    lemma_pick_set(cand, picked, pos);
    let cv = cand.map_values(|v: usize| v as int);
    assert forall|t: int| 0 <= t < cand.len() && picked.map_values(|v: usize| v as int).contains(cand[t] as int)
        implies #[trigger] pos.contains(t) by {
        assert(cv[t] == cand[t] as int);
    }
    lemma_pick_order(g, sums, cand, picked, pos);
}

/// The answer from the groups; ghost: the candidates and picked groups, and the AVG.
pub fn answer(g: &Groups, kc: &KeyCols) -> (r: (Outcome3, Ghost<Seq<int>>, Ghost<Seq<int>>, Ghost<int>, Ghost<nat>))
    requires kc.wf(), groups_cols(g, kc), g.sum@.len() == g.rep@.len(),
    ensures answer_ok(g, kc, &r.0, r.1@, r.2@, r.3@, r.4@),
{
    let e = Ghost(Seq::<int>::empty());
    if g.rep.len() == 0 {
        return (Outcome3::Rows(Vec::new()), e, e, Ghost(0), Ghost(0));
    }
    let sums = match group_sums(g) {
        Some(s) => s,
        None => return (Outcome3::Capacity, e, e, Ghost(0), Ghost(0)),
    };
    let total = match wide_to_i128(g.total) {
        Some(x) => x,
        None => return (Outcome3::Capacity, e, e, Ghost(0), Ghost(0)),
    };
    let n = g.ncik as i128;
    let (ac, asc) = match num_div_exec(total, 4, n, 0) {
        Ok(Ok(EVal::Num { coeff, scale })) => (coeff, scale),
        Ok(Ok(v)) => {
            proof {
                // the division's value is numeric
                assert(num_div(total as int, 4, n as int, 0) == Ok::<Val, SqlError>(v@));
                assert(v@ is Num);
            }
            return (Outcome3::Capacity, e, e, Ghost(0), Ghost(0));
        },
        Ok(Err(err)) => return (Outcome3::Err(err), e, e, Ghost(0), Ghost(0)),
        Err(_) => return (Outcome3::Capacity, e, e, Ghost(0), Ghost(0)),
    };
    let cand = above(&sums, ac, asc);
    let (picked, Ghost(pos)) = top(&sums, &cand, 100);
    proof {
        assert forall|u: int| 0 <= u < picked@.len() implies #[trigger] picked@[u] < g.rep@.len() by {
            assert(picked@[u] == cand@[pos[u]]);
        }
    }
    let rows = out_rows(g, kc, &sums, &picked);
    let ghost cv = cand@.map_values(|v: usize| v as int);
    let ghost pv = picked@.map_values(|v: usize| v as int);
    proof {
        assert forall|i: int| 0 <= i < g.rep@.len() implies #[trigger] in128(wval(g.sum@[i])) by {
            assert(sums@[i] as int == wval(g.sum@[i]));
        }
        lemma_pick(g, sums@, cand@, picked@, pos, ac as int, asc as nat);
        assert(view_rows(rows@) == pv.map_values(|i: int| grow(g, kc, i))) by {
            assert(picked@.map_values(|i: usize| grow(g, kc, i as int)) =~= pv.map_values(|i: int| grow(g, kc, i)));
        }
    }
    (Outcome3::Rows(rows), Ghost(cv), Ghost(pv), Ghost(ac as int), Ghost(asc as nat))
}

} // verus!
