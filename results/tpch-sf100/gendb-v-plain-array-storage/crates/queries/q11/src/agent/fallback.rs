//! The general serial path, for databases unlike dbgen's (supplier keys not dense, part keys not ordered among the
//! qualifying rows, or a run buffer too small): every partsupp row on the calling thread, its supplier found by a
//! linear search over the supplier keys (`key_ok_exec`), the groups kept in a list with distinct keys extended by a
//! linear search (`fallback_groups`). Quadratic, but it decides every database; dbgen data never takes it.
use vstd::prelude::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::normal::*;
use crate::agent::groups::*;
use crate::agent::scan::{bits_ok, GO, OVER, imax, vbound, lemma_val_bound_pub};
use crate::agent::sem::lemma_product_bound;
use crate::agent::common::bitmap::bit_at;
use crate::agent::common::msort::{pairs, lemma_pairs_push, lemma_pairs_frame};

verus! {

/// Some supplier row has key `s` and its bit set (its nation is named `p`): the general supplier lookup.
fn key_ok_exec(s: i64, skeys: &'static [i64], ns: usize, bits: &Vec<u64>, Ghost(sv): Ghost<StoresView>,
    Ghost(p): Ghost<Seq<u8>>) -> (q: bool)
    requires stores_wf(sv), skeys@ == s_keys(sv), ns == supp_n(sv), bits_ok(bits@, ns as int, sv, p),
    ensures q == key_ok(sv, p, s as int),
{
    let mut b: usize = 0;
    while b < ns
        invariant
            stores_wf(sv), skeys@ == s_keys(sv), ns == supp_n(sv), bits_ok(bits@, ns as int, sv, p), b <= ns,
            forall|x: int| 0 <= x < b && #[trigger] s_keys(sv)[x] == s ==> !supp_ok(sv, p, x),
        decreases ns - b,
    {
        if skeys[b] == s {
            proof {
                assert(b / 64 < bits@.len()) by (nonlinear_arith) requires b < ns, 64 * bits@.len() >= ns;
            }
            let w = bits[b / 64];
            let sh: u64 = (b % 64) as u64;
            if (w >> sh) & 1u64 == 1u64 {
                proof {
                    assert(bit_at(bits@, b as int));
                    assert(supp_ok(sv, p, b as int));
                }
                return true;
            }
            proof {
                assert(!bit_at(bits@, b as int));
            }
        }
        b = b + 1;
    }
    false
}

/// The groups of the qualifying rows `[0, c)`: distinct keys, each with its range sum and a positive count, and
/// every key with a row listed.
pub open spec fn groups_ok(sv: StoresView, p: Seq<u8>, c: int, ks: Seq<i64>, ss: Seq<i128>) -> bool {
    &&& ks.len() == ss.len()
    &&& forall|i: int| 0 <= i < ks.len() ==> #[trigger] ss[i] as int == rsum(sv, p, t_sum(sv, ks[i] as int), 0, c)
        && rsum(sv, p, t_cnt(sv, ks[i] as int), 0, c) > 0
    &&& forall|i: int, j: int| 0 <= i < ks.len() && 0 <= j < ks.len() && i != j ==> #[trigger] ks[i] != #[trigger] ks[j]
    &&& forall|k: int| #[trigger] rsum(sv, p, t_cnt(sv, k), 0, c) > 0 ==> exists|i: int| 0 <= i < ks.len() && ks[i] as int == k
}

/// The position of key `k`, if any.
fn find_key(keys: &Vec<i64>, k: i64) -> (r: Option<usize>)
    ensures
        r matches Some(i) ==> i < keys@.len() && keys@[i as int] == k,
        r is None ==> forall|i: int| 0 <= i < keys@.len() ==> keys@[i] != k,
{
    let n = keys.len();
    let mut i: usize = 0;
    while i < n
        invariant n == keys@.len(), i <= n, forall|j: int| 0 <= j < i ==> keys@[j] != k,
        decreases n - i,
    {
        if keys[i] == k {
            return Some(i);
        }
        i = i + 1;
    }
    None
}

/// The general path's result: the groups, the total and the absolute mass, or `OVER`.
pub struct Fallback {
    pub keys: Vec<i64>,
    pub sums: Vec<i128>,
    pub status: u8,
    pub total: i128,
    pub mass: i128,
}

/// The groups of all qualifying partsupp rows (serial, general).
pub fn fallback_groups(pk: &'static [i64], sk: &'static [i64], aq: &'static [i64], cost: &'static [i128], n: usize,
    skeys: &'static [i64], ns: usize, bits: &Vec<u64>, Ghost(sv): Ghost<StoresView>, Ghost(p): Ghost<Seq<u8>>) -> (r: Fallback)
    requires
        stores_wf(sv), bounds_ok(sv),
        pk@ == ps_pkeys(sv), sk@ == ps_skeys(sv), aq@ == ps_aqs(sv), cost@ == ps_costs(sv), n == ps_n(sv),
        skeys@ == s_keys(sv), ns == supp_n(sv), bits_ok(bits@, ns as int, sv, p),
    ensures
        r.status == GO || r.status == OVER,
        r.status == GO ==> groups_ok(sv, p, n as int, r.keys@, r.sums@)
            && r.total == rsum(sv, p, t_val(sv), 0, n as int)
            && r.mass == rsum(sv, p, t_absv(sv), 0, n as int),
        r.status == OVER ==> rsum(sv, p, t_absv(sv), 0, n as int) > imax(),
{
    let mut keys: Vec<i64> = Vec::new();
    let mut sums: Vec<i128> = Vec::new();
    let mut total: i128 = 0;
    let mut mass: i128 = 0;
    let mut c: usize = 0;
    while c < n
        invariant
            stores_wf(sv), bounds_ok(sv),
            pk@ == ps_pkeys(sv), sk@ == ps_skeys(sv), aq@ == ps_aqs(sv), cost@ == ps_costs(sv), n == ps_n(sv),
            skeys@ == s_keys(sv), ns == supp_n(sv), bits_ok(bits@, ns as int, sv, p),
            c <= n,
            groups_ok(sv, p, c as int, keys@, sums@),
            total == rsum(sv, p, t_val(sv), 0, c as int),
            mass == rsum(sv, p, t_absv(sv), 0, c as int),
        decreases n - c,
    {
        let q = key_ok_exec(sk[c], skeys, ns, bits, Ghost(sv), Ghost(p));
        let ghost (k0, s0) = (keys@, sums@);
        proof {
            assert(q == qrow(sv, p, c as int));
            lemma_rsum_step(sv, p, t_val(sv), 0, c as int);
            lemma_rsum_step(sv, p, t_absv(sv), 0, c as int);
            lemma_rsum_nonneg(sv, p, t_absv(sv), 0, c as int);
            lemma_rsum_bounds(sv, p, 0, 0, c as int);
        }
        if q {
            let k = pk[c];
            proof {
                lemma_product_bound(ps_costs(sv)[c as int] as int, ps_aqs(sv)[c as int] as int);
                lemma_val_bound_pub(sv, c as int);
            }
            let v = cost[c] * (aq[c] as i128);
            let av: i128 = if v < 0 { -v } else { v };
            if av > i128::MAX - mass {
                proof {
                    assert forall|x: int| c + 1 <= x < n implies #[trigger] (t_absv(sv))(x) >= 0 by {}
                    lemma_rsum_mono(sv, p, t_absv(sv), 0, c + 1, n as int);
                }
                return Fallback { keys, sums, status: OVER, total, mass };
            }
            mass = mass + av;
            total = total + v;
            match find_key(&keys, k) {
                Some(i) => {
                    proof {
                        lemma_rsum_bounds(sv, p, k as int, 0, c as int);
                        assert(sums@[i as int] as int == rsum(sv, p, t_sum(sv, k as int), 0, c as int));
                    }
                    let s = sums[i] + v;
                    sums.set(i, s);
                    proof {
                        assert(keys@ == k0);
                        assert forall|j: int| 0 <= j < keys@.len() implies #[trigger] sums@[j] as int == rsum(sv, p, t_sum(sv, keys@[j] as int), 0, c + 1)
                            && rsum(sv, p, t_cnt(sv, keys@[j] as int), 0, c + 1) > 0 by {
                            lemma_rsum_step(sv, p, t_sum(sv, keys@[j] as int), 0, c as int);
                            lemma_rsum_step(sv, p, t_cnt(sv, keys@[j] as int), 0, c as int);
                            lemma_rsum_bounds(sv, p, keys@[j] as int, 0, c as int);
                            if j != i {
                                assert(keys@[j] != k);
                                assert(sums@[j] == s0[j]);
                            }
                        }
                    }
                },
                None => {
                    proof {
                        lemma_rsum_bounds(sv, p, k as int, 0, c as int);
                        if rsum(sv, p, t_cnt(sv, k as int), 0, c as int) > 0 {
                            let j = choose|j: int| 0 <= j < k0.len() && k0[j] as int == k as int;
                        }
                        assert(rsum(sv, p, t_cnt(sv, k as int), 0, c as int) == 0);
                    }
                    keys.push(k);
                    sums.push(v);
                    proof {
                        assert forall|j: int| 0 <= j < keys@.len() implies #[trigger] sums@[j] as int == rsum(sv, p, t_sum(sv, keys@[j] as int), 0, c + 1)
                            && rsum(sv, p, t_cnt(sv, keys@[j] as int), 0, c + 1) > 0 by {
                            lemma_rsum_step(sv, p, t_sum(sv, keys@[j] as int), 0, c as int);
                            lemma_rsum_step(sv, p, t_cnt(sv, keys@[j] as int), 0, c as int);
                            lemma_rsum_bounds(sv, p, keys@[j] as int, 0, c as int);
                            if j < k0.len() {
                                assert(keys@[j] == k0[j] && sums@[j] == s0[j]);
                                assert(k0[j] != k);
                            }
                        }
                    }
                },
            }
            proof {
                assert forall|i: int, j: int| 0 <= i < keys@.len() && 0 <= j < keys@.len() && i != j implies #[trigger] keys@[i] != #[trigger] keys@[j] by {
                    if i < k0.len() && j < k0.len() {
                        assert(keys@[i] == k0[i] && keys@[j] == k0[j]);
                    }
                }
                assert forall|kk: int| #[trigger] rsum(sv, p, t_cnt(sv, kk), 0, c + 1) > 0 implies exists|i: int| 0 <= i < keys@.len() && keys@[i] as int == kk by {
                    lemma_rsum_step(sv, p, t_cnt(sv, kk), 0, c as int);
                    if kk != k as int {
                        assert(rsum(sv, p, t_cnt(sv, kk), 0, c as int) > 0);
                        let i = choose|i: int| 0 <= i < k0.len() && k0[i] as int == kk;
                        assert(keys@[i] == k0[i]);
                    } else if keys@.len() > k0.len() {
                        assert(keys@[k0.len() as int] == k);
                    } else {
                        let i = choose|i: int| 0 <= i < keys@.len() && keys@[i] == k;
                    }
                }
            }
        } else {
            proof {
                assert forall|i: int| 0 <= i < keys@.len() implies #[trigger] sums@[i] as int == rsum(sv, p, t_sum(sv, keys@[i] as int), 0, c + 1)
                    && rsum(sv, p, t_cnt(sv, keys@[i] as int), 0, c + 1) > 0 by {
                    lemma_rsum_step(sv, p, t_sum(sv, keys@[i] as int), 0, c as int);
                    lemma_rsum_step(sv, p, t_cnt(sv, keys@[i] as int), 0, c as int);
                }
                assert forall|kk: int| #[trigger] rsum(sv, p, t_cnt(sv, kk), 0, c + 1) > 0 implies exists|i: int| 0 <= i < keys@.len() && keys@[i] as int == kk by {
                    lemma_rsum_step(sv, p, t_cnt(sv, kk), 0, c as int);
                }
            }
        }
        c = c + 1;
    }
    Fallback { keys, sums, status: GO, total, mass }
}

} // verus!
