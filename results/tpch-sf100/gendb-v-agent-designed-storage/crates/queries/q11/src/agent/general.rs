//! The general plan, for any stored order and supplier keys (used when partsupp is not stored sorted by
//! ps_partkey or the supplier keys span too wide a range for a flag array). Serial and quadratic, correctness only:
//! decide per partsupp row whether it qualifies (a pass over the suppliers), add the total and mass, then for each
//! row that is the first qualifying row of its key, add up the key's SUM over all rows and keep it when it passes
//! HAVING (`gen_ok`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::{abs, pow10};
use crate::link::expr::{ival, fits_i128, i128_max};
use super::tables::*;
use super::nf::*;
use super::rows::*;
use super::supp::*;
use super::scan::MAXM;
use super::tasks::row_key;
use super::finish::*;
use super::plan::{PlanOut, plan_ok, cap_cond};

verus! {

/// Row `r` qualifies: some supplier with its supplier key is in a nation named `name` (a pass over the suppliers).
fn row_qualifies(c: &Cols, nk: &Vec<i64>, r: usize, Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>) -> (q: bool)
    requires cols_ok(*c, t), tabs_typed(t), nkeys_ok(t, name, nk@), r < c.ps.n,
    ensures q == rowq(t, name, r as int),
{
    assert(ps_row_ok(c.ps, t.ps[r as int], r as int));
    proof { lemma_grp_bound(c.ps.n as int, c.ps.bs as int, c.ps.ng as int, r as int); }
    let sv: i64 = c.ps.supp_b[r / c.ps.bs] + c.ps.supp_c[r] as i64;
    assert(t.ps[r as int][1] == Val::Int(sv as int));
    let ghost a = t.ps[r as int];
    assert(rowq(t, name, r as int) == sq(t, name, Val::Int(sv as int)));
    let mut j: usize = 0;
    while j < c.s.n
        invariant
            cols_ok(*c, t), tabs_typed(t), nkeys_ok(t, name, nk@), j <= c.s.n,
            rowq(t, name, r as int) == sq(t, name, Val::Int(sv as int)),
            forall|j2: int| 0 <= j2 < j ==> !(#[trigger] t.s[j2][0] == Val::Int(sv as int) && nq(t, name, t.s[j2][3])),
        decreases c.s.n - j,
    {
        assert(supp_row_ok(c.s, t.s[j as int], j as int));
        assert(s_typed(t.s[j as int]));
        proof { lemma_grp_bound(c.s.n as int, c.s.bs as int, c.s.ng as int, j as int); }
        let g = j / c.s.bs;
        let k: i64 = c.s.key_b[g] + c.s.key_c[j] as i64;
        if k == sv {
            let nkey: i64 = c.s.nat_b[g] + c.s.nat_c[j] as i64;
            if contains_key(nk, nkey) {
                assert(t.s[j as int][0] == Val::Int(sv as int));
                assert(t.s[j as int][3] == Val::Int(nkey as int));
                assert(nq(t, name, t.s[j as int][3]));
                assert(sq(t, name, Val::Int(sv as int)));
                assert(rq(t, name, t.ps[r as int]));
                return true;
            }
        }
        j = j + 1;
    }
    proof {
        if sq(t, name, Val::Int(sv as int)) {
            let j2 = choose|j2: int| 0 <= j2 < t.s.len() && #[trigger] t.s[j2][0] == Val::Int(sv as int) && nq(t, name, t.s[j2][3]);
        }
    }
    false
}

/// The argument `ps_supplycost * ps_availqty` of row `r`.
fn row_val(c: &PSCols, r: usize, Ghost(t): Ghost<Tabs>) -> (v: i128)
    requires pscols_ok(*c, t.ps), tabs_typed(t), r < c.n,
    ensures v as int == rval(t, r as int), abs(v as int) < 0x2_0000_0000_0000_0000_0000_0000_0000,
{
    assert(ps_row_ok(*c, t.ps[r as int], r as int));
    proof { lemma_grp_bound(c.n as int, c.bs as int, c.ng as int, r as int); }
    assert(pow10(15) == 1000000000000000) by (compute);
    let g = r / c.bs;
    let cost: i64 = c.cost_b[g] + c.cost_c[r] as i64;
    let qty: i64 = c.qty_b[g] + c.qty_c[r] as i64;
    proof {
        let (a, b) = (abs(cost as int), abs(qty as int));
        assert(a * b <= 1000000000000000 * 0x8000_0000_0000_0000) by (nonlinear_arith)
            requires 0 <= a < 1000000000000000, 0 <= b <= 0x8000_0000_0000_0000;
        assert(abs(cost as int * qty as int) == a * b) by (nonlinear_arith) requires a == abs(cost as int), b == abs(qty as int);
        assert((cost as int) * (qty as int) == (qty as int) * (cost as int)) by (nonlinear_arith);
    }
    cost as i128 * qty as i128
}

/// The qualification of every row.
fn qualify_all(c: &Cols, nk: &Vec<i64>, Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>) -> (qs: Vec<bool>)
    requires cols_ok(*c, t), tabs_typed(t), nkeys_ok(t, name, nk@),
    ensures qs@.len() == c.ps.n, forall|r: int| 0 <= r < c.ps.n ==> #[trigger] qs@[r] == rowq(t, name, r),
{
    let mut qs: Vec<bool> = Vec::new();
    let mut r: usize = 0;
    while r < c.ps.n
        invariant
            cols_ok(*c, t), tabs_typed(t), nkeys_ok(t, name, nk@), r <= c.ps.n,
            qs@.len() == r, forall|r2: int| 0 <= r2 < r ==> #[trigger] qs@[r2] == rowq(t, name, r2),
        decreases c.ps.n - r,
    {
        let q = row_qualifies(c, nk, r, Ghost(t), Ghost(name));
        qs.push(q);
        r = r + 1;
    }
    qs
}

/// The SUM of key `k` over all rows (inside the mass bound, so no overflow).
fn key_sum(c: &PSCols, qs: &Vec<bool>, k: i64, Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>) -> (s: i128)
    requires
        pscols_ok(*c, t.ps), tabs_typed(t), qs@.len() == c.n,
        forall|r: int| 0 <= r < c.n ==> #[trigger] qs@[r] == rowq(t, name, r),
        tabs(t, name, 0, c.n as int) <= i128_max(),
    ensures s as int == ksum(t, name, k as int, 0, c.n as int),
{
    let mut s: i128 = 0;
    let mut r: usize = 0;
    while r < c.n
        invariant
            pscols_ok(*c, t.ps), tabs_typed(t), qs@.len() == c.n, r <= c.n,
            forall|r2: int| 0 <= r2 < c.n ==> #[trigger] qs@[r2] == rowq(t, name, r2),
            tabs(t, name, 0, c.n as int) <= i128_max(),
            s as int == ksum(t, name, k as int, 0, r as int),
        decreases c.n - r,
    {
        if qs[r] && row_key(c, r, Ghost(t)) == k {
            let v = row_val(c, r, Ghost(t));
            proof {
                lemma_bounds(t, name, k as int, 0, r as int + 1);
                lemma_split(t, name, 0, 0, r as int + 1, c.n as int);
                lemma_bounds(t, name, 0, r as int + 1, c.n as int);
            }
            s = s + v;
        }
        r = r + 1;
    }
    s
}

/// Whether some row before `i` qualifies with key `k`.
fn seen_before(c: &PSCols, qs: &Vec<bool>, k: i64, i: usize, Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>) -> (b: bool)
    requires
        pscols_ok(*c, t.ps), tabs_typed(t), qs@.len() == c.n, i <= c.n,
        forall|r: int| 0 <= r < c.n ==> #[trigger] qs@[r] == rowq(t, name, r),
    ensures b == (kcnt(t, name, k as int, 0, i as int) > 0),
{
    let mut r: usize = 0;
    while r < i
        invariant
            pscols_ok(*c, t.ps), tabs_typed(t), qs@.len() == c.n, r <= i <= c.n,
            forall|r2: int| 0 <= r2 < c.n ==> #[trigger] qs@[r2] == rowq(t, name, r2),
            kcnt(t, name, k as int, 0, r as int) == 0,
        decreases i - r,
    {
        if qs[r] && row_key(c, r, Ghost(t)) == k {
            proof {
                lemma_split(t, name, k as int, 0, r as int + 1, i as int);
                lemma_bounds(t, name, k as int, r as int + 1, i as int);
            }
            return true;
        }
        r = r + 1;
    }
    false
}

/// The result pairs over the rows before `i`, in first-occurrence order.
pub open spec fn gen_ok(t: Tabs, name: Seq<u8>, i: int, res: Seq<(i64, i128)>, thr: i128) -> bool {
    let n = n_of(t);
    &&& forall|x: int| 0 <= x < res.len() ==> {
        &&& kcnt(t, name, #[trigger] res[x].0 as int, 0, n) > 0
        &&& res[x].1 as int == ksum(t, name, res[x].0 as int, 0, n)
        &&& res[x].1 > thr
        &&& kcnt(t, name, res[x].0 as int, 0, i) > 0
    }
    &&& forall|x: int, y: int| 0 <= x < res.len() && 0 <= y < res.len() && x != y ==> #[trigger] res[x].0 != #[trigger] res[y].0
    &&& forall|key: int| #[trigger] kcnt(t, name, key, 0, i) > 0 && ksum(t, name, key, 0, n) > thr ==>
            exists|x: int| 0 <= x < res.len() && res[x].0 as int == key
}

/// The general plan.
pub fn general_plan(c: &Cols, nk: &Vec<i64>, p1: i128, Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>) -> (o: PlanOut)
    requires cols_ok(*c, t), tabs_typed(t), keys_unique(t), nkeys_ok(t, name, nk@),
    ensures plan_ok(t, name, p1 as int, o),
{
    let n = c.ps.n;
    let qs = qualify_all(c, nk, Ghost(t), Ghost(name));
    assert(MAXM as int == i128_max());
    // Total and mass.
    let mut total: i128 = 0;
    let mut mass: u128 = 0;
    let mut r: usize = 0;
    while r < n
        invariant
            cols_ok(*c, t), tabs_typed(t), n == c.ps.n, n == n_of(t), qs@.len() == n, r <= n,
            forall|r2: int| 0 <= r2 < n ==> #[trigger] qs@[r2] == rowq(t, name, r2),
            total as int == tsum(t, name, 0, r as int), mass as int == tabs(t, name, 0, r as int), mass <= MAXM,
            MAXM as int == i128_max(),
        decreases n - r,
    {
        if qs[r] {
            let v = row_val(&c.ps, r, Ghost(t));
            let a: u128 = if v < 0 { (-v) as u128 } else { v as u128 };
            proof {
                lemma_split(t, name, 0, 0, r as int + 1, n as int);
                lemma_bounds(t, name, 0, r as int + 1, n as int);
                lemma_bounds(t, name, 0, 0, r as int + 1);
            }
            if a > MAXM - mass {
                return PlanOut { cap: true, res: Vec::new(), runs: Vec::new() };
            }
            mass = mass + a;
            total = total + v;
        }
        r = r + 1;
    }
    let prod = match total.checked_mul(p1) {
        Some(x) => x,
        None => {
            assert(total != 0);
            return PlanOut { cap: true, res: Vec::new(), runs: Vec::new() };
        },
    };
    let thr = thr_of(prod);
    // The groups, at their first qualifying row.
    let mut res: Vec<(i64, i128)> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            cols_ok(*c, t), tabs_typed(t), n == c.ps.n, n == n_of(t), qs@.len() == n, i <= n,
            forall|r2: int| 0 <= r2 < n ==> #[trigger] qs@[r2] == rowq(t, name, r2),
            tabs(t, name, 0, n as int) <= i128_max(),
            gen_ok(t, name, i as int, res@, thr),
        decreases n - i,
    {
        let ghost r0 = res@;
        assert forall|key: int| key != rkey(t, i as int) || !rowq(t, name, i as int) implies
            #[trigger] kcnt(t, name, key, 0, i as int + 1) == kcnt(t, name, key, 0, i as int) by {}
        if qs[i] {
            let k = row_key(&c.ps, i, Ghost(t));
            let seen = seen_before(&c.ps, &qs, k, i, Ghost(t), Ghost(name));
            proof {
                lemma_kpos(t, name, i as int, 0, i as int + 1);
                lemma_split(t, name, k as int, 0, i as int + 1, n as int);
                lemma_bounds(t, name, k as int, i as int + 1, n as int);
                lemma_bounds(t, name, k as int, 0, i as int);
            }
            if !seen {
                let s = key_sum(&c.ps, &qs, k, Ghost(t), Ghost(name));
                if s > thr {
                    res.push((k, s));
                    proof {
                        let r1 = res@;
                        assert forall|x: int, y: int| 0 <= x < r1.len() && 0 <= y < r1.len() && x != y implies
                            #[trigger] r1[x].0 != #[trigger] r1[y].0 by {
                            if x < r0.len() && y < r0.len() {
                                assert(r1[x] == r0[x] && r1[y] == r0[y]);
                            } else if x < r0.len() {
                                assert(r1[x] == r0[x]);
                                assert(kcnt(t, name, r0[x].0 as int, 0, i as int) > 0);
                            } else {
                                assert(r1[y] == r0[y]);
                                assert(kcnt(t, name, r0[y].0 as int, 0, i as int) > 0);
                            }
                        }
                        assert forall|x: int| 0 <= x < r1.len() implies kcnt(t, name, #[trigger] r1[x].0 as int, 0, i as int + 1) > 0 by {
                            if x < r0.len() {
                                assert(r1[x] == r0[x]);
                                lemma_split(t, name, r0[x].0 as int, 0, i as int, i as int + 1);
                                lemma_bounds(t, name, r0[x].0 as int, i as int, i as int + 1);
                            }
                        }
                        assert forall|key: int| #[trigger] kcnt(t, name, key, 0, i as int + 1) > 0 && ksum(t, name, key, 0, n as int) > thr implies
                            exists|x: int| 0 <= x < r1.len() && r1[x].0 as int == key by {
                            if key == k as int {
                                assert(r1[r0.len() as int].0 == k);
                            } else {
                                let x = choose|x: int| 0 <= x < r0.len() && r0[x].0 as int == key;
                                assert(r1[x] == r0[x]);
                            }
                        }
                    }
                } else {
                    proof {
                        assert forall|x: int| 0 <= x < r0.len() implies kcnt(t, name, #[trigger] r0[x].0 as int, 0, i as int + 1) > 0 by {
                            lemma_split(t, name, r0[x].0 as int, 0, i as int, i as int + 1);
                            lemma_bounds(t, name, r0[x].0 as int, i as int, i as int + 1);
                        }
                    }
                }
            } else {
                proof {
                    assert forall|x: int| 0 <= x < r0.len() implies kcnt(t, name, #[trigger] r0[x].0 as int, 0, i as int + 1) > 0 by {
                        lemma_split(t, name, r0[x].0 as int, 0, i as int, i as int + 1);
                        lemma_bounds(t, name, r0[x].0 as int, i as int, i as int + 1);
                    }
                }
            }
        } else {
            proof {
                assert forall|x: int| 0 <= x < r0.len() implies kcnt(t, name, #[trigger] r0[x].0 as int, 0, i as int + 1) > 0 by {
                    lemma_split(t, name, r0[x].0 as int, 0, i as int, i as int + 1);
                    lemma_bounds(t, name, r0[x].0 as int, i as int, i as int + 1);
                }
            }
        }
        i = i + 1;
    }
    proof {
        let tc = tsum(t, name, 0, n as int);
        let r1 = res@;
        assert forall|x: int| 0 <= x < r1.len() implies above(r1[x].1 as int, tc * p1) by {
            assert(kcnt(t, name, r1[x].0 as int, 0, n as int) > 0);
            assert(above(r1[x].1 as int, prod as int) <==> r1[x].1 > thr);
        }
        assert forall|key: int| #[trigger] kcnt(t, name, key, 0, n as int) > 0 && above(ksum(t, name, key, 0, n as int), tc * p1) implies
            exists|x: int| 0 <= x < r1.len() && r1[x].0 as int == key by {
            assert(above(ksum(t, name, key, 0, n as int), prod as int) <==> ksum(t, name, key, 0, n as int) > thr);
        }
    }
    let ghost res0 = res@;
    super::common::msort::sort_desc(&mut res);
    proof {
        lemma_res_ok_perm(t, name, res0, res@, p1 as int);
        assert(super::common::msort::seg(res@, 0, res@.len() as int) =~= res@);
    }
    let mut runs: Vec<usize> = Vec::new();
    runs.push(0);
    runs.push(res.len());
    PlanOut { cap: false, res, runs }
}

} // verus!
