//! Small preparations on the calling thread: the distinct sizes of `$3..$10` (`size_list`) and the byte tests of
//! the parameters (`plain_pattern_exec`).
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::query::param_domain;
use crate::gendb_params::Params;
use crate::agent::sem_row::*;
use crate::agent::parts::sizes_ok;

verus! {

/// Allocations below this many 8-byte elements are rounded up to it, so that they come from fresh zero pages.
pub const BIG: usize = 0x44_0000;

/// `n`, rounded up to `BIG`.
pub fn big(n: usize) -> (r: usize)
    ensures r >= n,
{
    if n < BIG { BIG } else { n }
}

/// `n`, rounded up to `2 * BIG` (for 4-byte elements).
pub fn big4(n: usize) -> (r: usize)
    ensures r >= n,
{
    if n < 2 * BIG { 2 * BIG } else { n }
}


/// `size_match` over the first `n` sizes is membership among them.
pub proof fn lemma_size_match(ps: Seq<Literal>, n: int, s: int)
    requires 1 <= n,
    ensures size_match(ps, n, s) <==> exists|i: int| 0 <= i < n && s == #[trigger] size_lit(ps, i),
    decreases n,
{
    if n > 1 {
        lemma_size_match(ps, n - 1, s);
        if size_match(ps, n, s) {
            if size_match(ps, n - 1, s) {
                let i = choose|i: int| 0 <= i < n - 1 && s == #[trigger] size_lit(ps, i);
                assert(0 <= i < n && s == size_lit(ps, i));
            } else {
                assert(s == size_lit(ps, n - 1));
            }
        }
        if exists|i: int| 0 <= i < n && s == #[trigger] size_lit(ps, i) {
            let i = choose|i: int| 0 <= i < n && s == #[trigger] size_lit(ps, i);
            if i < n - 1 { assert(size_match(ps, n - 1, s)); }
        }
    } else {
        if exists|i: int| 0 <= i < n && s == #[trigger] size_lit(ps, i) {
            let i = choose|i: int| 0 <= i < n && s == #[trigger] size_lit(ps, i);
            assert(i == 0);
        }
    }
}

/// `v` is among the first `n` values of `s`.
pub open spec fn in_seq(s: Seq<i64>, n: int, v: i64) -> bool {
    exists|x: int| 0 <= x < n && s[x] == v
}

/// The sizes as a vector: value `i` is `$(3 + i)`.
fn size_params(params: &Params) -> (pv: Vec<i64>)
    requires param_domain(params@),
    ensures pv@.len() == 8, forall|i: int| 0 <= i < 8 ==> #[trigger] pv@[i] as int == size_lit(params@, i),
{
    let ghost ps = params@;
    proof { lemma_params(ps); }
    let pv: Vec<i64> = vec![params.p2, params.p3, params.p4, params.p5, params.p6, params.p7, params.p8, params.p9];
    proof {
        assert forall|i: int| 0 <= i < 8 implies #[trigger] pv@[i] as int == size_lit(ps, i) by {
            assert(ps[2 + i] == (Literal::Int { v: size_lit(ps, i), kind: crate::spec::int::IntKind::Int4 }));
            if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {} else if i == 5 {} else if i == 6 {} else {}
        }
    }
    pv
}

/// The distinct values of `pv`, in first-occurrence order.
fn distinct_values(pv: &Vec<i64>) -> (szl: Vec<i64>)
    requires pv@.len() >= 1,
    ensures
        1 <= szl@.len() <= pv@.len(),
        forall|x: int, y: int| 0 <= x < y < szl@.len() ==> szl@[x] != szl@[y],
        forall|v: i64| in_seq(szl@, szl@.len() as int, v) <==> in_seq(pv@, pv@.len() as int, v),
{
    let n = pv.len();
    let mut szl: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            n == pv@.len(), n >= 1, j <= n, szl@.len() <= j, j > 0 ==> szl@.len() >= 1,
            forall|x: int, y: int| 0 <= x < y < szl@.len() ==> szl@[x] != szl@[y],
            forall|v: i64| in_seq(szl@, szl@.len() as int, v) <==> in_seq(pv@, j as int, v),
        decreases n - j,
    {
        let v = pv[j];
        let mut dup = false;
        let mut k: usize = 0;
        while k < szl.len()
            invariant k <= szl@.len(), dup <==> in_seq(szl@, k as int, v),
            decreases szl@.len() - k,
        {
            if szl[k] == v {
                dup = true;
            }
            proof {
                if in_seq(szl@, k + 1, v) && !(szl@[k as int] == v) {
                    let x = choose|x: int| 0 <= x < k + 1 && szl@[x] == v;
                    assert(in_seq(szl@, k as int, v));
                }
                if in_seq(szl@, k as int, v) {
                    let x = choose|x: int| 0 <= x < k && szl@[x] == v;
                    assert(in_seq(szl@, k + 1, v));
                }
            }
            k = k + 1;
        }
        let ghost s0 = szl@;
        if !dup {
            szl.push(v);
        }
        proof {
            assert forall|w: i64| in_seq(szl@, szl@.len() as int, w) <==> in_seq(pv@, j + 1, w) by {
                if in_seq(szl@, szl@.len() as int, w) {
                    let x = choose|x: int| 0 <= x < szl@.len() && szl@[x] == w;
                    if x < s0.len() {
                        assert(szl@[x] == s0[x]);
                        assert(in_seq(s0, s0.len() as int, w));
                        assert(in_seq(pv@, j as int, w));
                        let i = choose|i: int| 0 <= i < j && pv@[i] == w;
                        assert(in_seq(pv@, j + 1, w));
                    } else {
                        assert(pv@[j as int] == w);
                        assert(in_seq(pv@, j + 1, w));
                    }
                }
                if in_seq(pv@, j + 1, w) {
                    let i = choose|i: int| 0 <= i < j + 1 && pv@[i] == w;
                    if i < j {
                        assert(in_seq(pv@, j as int, w));
                        let x = choose|x: int| 0 <= x < s0.len() && s0[x] == w;
                        assert(szl@[x] == w);
                    } else if dup {
                        let x = choose|x: int| 0 <= x < s0.len() && s0[x] == w;
                        assert(szl@[x] == w);
                    } else {
                        assert(szl@[s0.len() as int] == w);
                    }
                }
            }
        }
        j = j + 1;
    }
    szl
}

/// The distinct values of `$3..$10`, in first-occurrence order.
pub fn size_list(params: &Params) -> (szl: Vec<i64>)
    requires param_domain(params@),
    ensures sizes_ok(szl@, params@),
{
    let ghost ps = params@;
    let pv = size_params(params);
    let szl = distinct_values(&pv);
    proof {
        assert forall|s: int| size_match(ps, 8, s) <==> exists|j: int| 0 <= j < szl@.len() && szl@[j] == s by {
            lemma_size_match(ps, 8, s);
            if size_match(ps, 8, s) {
                let i = choose|i: int| 0 <= i < 8 && s == #[trigger] size_lit(ps, i);
                assert(pv@[i] as int == s);
                assert(in_seq(pv@, 8, pv@[i]));
                let x = choose|x: int| 0 <= x < szl@.len() && szl@[x] == pv@[i];
                assert(szl@[x] == s);
            }
            if exists|j: int| 0 <= j < szl@.len() && szl@[j] == s {
                let x = choose|x: int| 0 <= x < szl@.len() && szl@[x] == s;
                assert(in_seq(szl@, szl@.len() as int, szl@[x]));
                let i = choose|i: int| 0 <= i < 8 && pv@[i] == szl@[x];
                assert(s == size_lit(ps, i));
            }
        }
    }
    szl
}

} // verus!
