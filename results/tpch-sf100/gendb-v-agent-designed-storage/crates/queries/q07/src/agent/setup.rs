//! Per-call preparation and the parallel scan:
//! - dense keys (`check_dense_*`): rows sorted by a distinct key whose last key is `n - 1` above the first hold
//!   key `key0 + r` at row `r` (`lemma_dense`), so a lookup is one probe;
//! - block sizes that are powers of two are shifted instead of divided (`shift_of`);
//! - the zone maps bound the lineitem groups that can hold window lines (`zone_range`);
//! - the scan of those groups is split into tasks of contiguous groups, and their sums are merged (`run_scan`).
use vstd::prelude::*;
use vstd::arithmetic::power2::pow2;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::filled;
use crate::stores::facts::interface::common::keyidx::{fkey, keyidx_ok, sorted_at, irow};
use super::model::*;
use super::lookup::*;
use super::kernel::*;
use super::dates::*;

verus! {

// ------------------------------------------------------------------------------------------------ dense keys

/// Keys sorted (kind 1) and distinct grow by at least one per row.
proof fn lemma_grow(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bs: int, n: int, r: int)
    requires
        keyidx_ok(kc, kb, ic, ib, bs, 1, n),
        forall|a: int, b: int| 0 <= a < n && 0 <= b < n && #[trigger] fkey(kc, kb, bs, a) == #[trigger] fkey(kc, kb, bs, b) ==> a == b,
        0 <= r < n - 1,
    ensures fkey(kc, kb, bs, r) + 1 <= fkey(kc, kb, bs, r + 1),
{
    assert(sorted_at(kc, kb, ic, ib, bs, 1, r));
    assert(irow(1, ic, ib, bs, r) == r);
    assert(irow(1, ic, ib, bs, r + 1) == r + 1);
    assert(fkey(kc, kb, bs, r) != fkey(kc, kb, bs, r + 1));
}

proof fn lemma_grow_from0(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bs: int, n: int, r: int)
    requires
        keyidx_ok(kc, kb, ic, ib, bs, 1, n),
        forall|a: int, b: int| 0 <= a < n && 0 <= b < n && #[trigger] fkey(kc, kb, bs, a) == #[trigger] fkey(kc, kb, bs, b) ==> a == b,
        0 <= r < n,
    ensures fkey(kc, kb, bs, 0) + r <= fkey(kc, kb, bs, r),
    decreases r,
{
    if r > 0 {
        lemma_grow_from0(kc, kb, ic, ib, bs, n, r - 1);
        lemma_grow(kc, kb, ic, ib, bs, n, r - 1);
    }
}

proof fn lemma_grow_to_last(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bs: int, n: int, r: int)
    requires
        keyidx_ok(kc, kb, ic, ib, bs, 1, n),
        forall|a: int, b: int| 0 <= a < n && 0 <= b < n && #[trigger] fkey(kc, kb, bs, a) == #[trigger] fkey(kc, kb, bs, b) ==> a == b,
        0 <= r < n,
    ensures fkey(kc, kb, bs, r) + (n - 1 - r) <= fkey(kc, kb, bs, n - 1),
    decreases n - 1 - r,
{
    if r < n - 1 {
        lemma_grow_to_last(kc, kb, ic, ib, bs, n, r + 1);
        lemma_grow(kc, kb, ic, ib, bs, n, r);
    }
}

/// Sorted distinct keys spanning exactly `n - 1`: row `r` holds key `key0 + r`.
pub proof fn lemma_dense(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bs: int, n: int)
    requires
        keyidx_ok(kc, kb, ic, ib, bs, 1, n),
        forall|a: int, b: int| 0 <= a < n && 0 <= b < n && #[trigger] fkey(kc, kb, bs, a) == #[trigger] fkey(kc, kb, bs, b) ==> a == b,
        n > 0,
        fkey(kc, kb, bs, n - 1) - fkey(kc, kb, bs, 0) == n - 1,
    ensures forall|r: int| 0 <= r < n ==> #[trigger] fkey(kc, kb, bs, r) == fkey(kc, kb, bs, 0) + r,
{
    assert forall|r: int| 0 <= r < n implies #[trigger] fkey(kc, kb, bs, r) == fkey(kc, kb, bs, 0) + r by {
        lemma_grow_from0(kc, kb, ic, ib, bs, n, r);
        lemma_grow_to_last(kc, kb, ic, ib, bs, n, r);
    }
}

/// Whether the supplier keys are dense, and the first key.
pub fn check_dense_s(c: &Cols) -> (r: (bool, i64))
    requires sup_ok(*c), keys_ok(*c),
    ensures s_dense_ok(*c, r.0, r.1),
{
    if c.s_kind == 1 && c.n_s > 0 {
        proof {
            crate::stores::facts::interface::common::read::lemma_div_lt(0, c.bs_s as int, c.sk_bases@.len() as int);
            crate::stores::facts::interface::common::read::lemma_div_lt(c.n_s - 1, c.bs_s as int, c.sk_bases@.len() as int);
            assert(in_i64(skey(*c, 0)) && in_i64(skey(*c, c.n_s - 1)));
        }
        let k0 = c.sk_bases[0 / c.bs_s] + c.sk_codes[0] as i64;
        let last = c.n_s - 1;
        let kl = c.sk_bases[last / c.bs_s] + c.sk_codes[last] as i64;
        if kl as i128 - k0 as i128 == last as i128 {
            proof {
                assert forall|a: int, b: int| 0 <= a < c.n_s && 0 <= b < c.n_s
                    && #[trigger] fkey(c.sk_codes@, c.sk_bases@, c.bs_s as int, a) == #[trigger] fkey(c.sk_codes@, c.sk_bases@, c.bs_s as int, b)
                    implies a == b by {
                    assert(skey(*c, a) == skey(*c, b));
                }
                lemma_dense(c.sk_codes@, c.sk_bases@, c.no_codes@, c.no_bases@, c.bs_s as int, c.n_s as int);
                assert forall|r: int| 0 <= r < c.n_s implies #[trigger] skey(*c, r) == k0 + r by {
                    assert(fkey(c.sk_codes@, c.sk_bases@, c.bs_s as int, r) == fkey(c.sk_codes@, c.sk_bases@, c.bs_s as int, 0) + r);
                }
            }
            return (true, k0);
        }
    }
    (false, 0)
}

/// Whether the customer keys are dense, and the first key.
pub fn check_dense_c(c: &Cols) -> (r: (bool, i64))
    requires cus_ok(*c), keys_ok(*c),
    ensures c_dense_ok(*c, r.0, r.1),
{
    if c.c_kind == 1 && c.n_c > 0 {
        proof {
            crate::stores::facts::interface::common::read::lemma_div_lt(0, c.bs_c as int, c.ck_bases@.len() as int);
            crate::stores::facts::interface::common::read::lemma_div_lt(c.n_c - 1, c.bs_c as int, c.ck_bases@.len() as int);
            assert(in_i64(ckey(*c, 0)) && in_i64(ckey(*c, c.n_c - 1)));
        }
        let k0 = c.ck_bases[0 / c.bs_c] + c.ck_codes[0] as i64;
        let last = c.n_c - 1;
        let kl = c.ck_bases[last / c.bs_c] + c.ck_codes[last] as i64;
        if kl as i128 - k0 as i128 == last as i128 {
            proof {
                assert forall|a: int, b: int| 0 <= a < c.n_c && 0 <= b < c.n_c
                    && #[trigger] fkey(c.ck_codes@, c.ck_bases@, c.bs_c as int, a) == #[trigger] fkey(c.ck_codes@, c.ck_bases@, c.bs_c as int, b)
                    implies a == b by {
                    assert(ckey(*c, a) == ckey(*c, b));
                }
                lemma_dense(c.ck_codes@, c.ck_bases@, c.no_codes@, c.no_bases@, c.bs_c as int, c.n_c as int);
                assert forall|r: int| 0 <= r < c.n_c implies #[trigger] ckey(*c, r) == k0 + r by {
                    assert(fkey(c.ck_codes@, c.ck_bases@, c.bs_c as int, r) == fkey(c.ck_codes@, c.ck_bases@, c.bs_c as int, 0) + r);
                }
            }
            return (true, k0);
        }
    }
    (false, 0)
}

// ------------------------------------------------------------------------------------------------ shifts

/// `(sh, true)` when `bs == 2^sh`, else `(0, false)`.
pub fn shift_of(bs: usize) -> (r: (usize, bool))
    requires bs >= 1,
    ensures shift_ok(bs, r.0, r.1),
{
    let mut sh: u64 = 0;
    while sh < 63
        invariant sh <= 63,
        decreases 63 - sh,
    {
        proof {
            vstd::bits::lemma_u64_pow2_no_overflow(sh as nat);
            vstd::bits::lemma_u64_shl_is_mul(1, sh);
        }
        if (1u64 << sh) == bs as u64 {
            return (sh as usize, true);
        }
        sh = sh + 1;
    }
    (0, false)
}

// ------------------------------------------------------------------------------------------------ zone range

/// A group the zone map excludes holds no window line.
pub open spec fn excluded(c: Cols, g: int) -> bool {
    c.ls_bases@[g] > win_hi() || c.ls_zmax@[g] < win_lo()
}

proof fn lemma_excluded_line(c: Cols, x: Ctx, j: int)
    requires li_ok(c), 0 <= j < c.n_l, excluded(c, j / c.bs_l as int),
    ensures l_grp(c, x, j) == -1,
{
    assert(lship(c, j) <= c.ls_zmax@[j / c.bs_l as int]);
}

/// The groups `[ga, gb)` outside of which the zone maps exclude every group.
pub fn zone_range(c: &Cols) -> (r: (usize, usize))
    requires li_ok(*c), groups_ok(*c),
    ensures
        r.0 <= r.1 <= c.ls_bases@.len(),
        forall|g: int| 0 <= g < r.0 ==> #[trigger] excluded(*c, g),
        forall|g: int| r.1 <= g < c.ls_bases@.len() ==> #[trigger] excluded(*c, g),
{
    let lo: i64 = -1826;
    let hi: i64 = -1096;
    let ng = c.ls_bases.len();
    let mut ga: usize = 0;
    while ga < ng && (c.ls_bases[ga] > hi || c.ls_zmax[ga] < lo)
        invariant
            li_ok(*c), ng == c.ls_bases@.len(), ga <= ng, lo == win_lo(), hi == win_hi(),
            forall|g: int| 0 <= g < ga ==> #[trigger] excluded(*c, g),
        decreases ng - ga,
    {
        ga = ga + 1;
    }
    let mut gb: usize = ng;
    while gb > ga && (c.ls_bases[gb - 1] > hi || c.ls_zmax[gb - 1] < lo)
        invariant
            li_ok(*c), ng == c.ls_bases@.len(), ga <= gb <= ng, lo == win_lo(), hi == win_hi(),
            forall|g: int| gb <= g < ng ==> #[trigger] excluded(*c, g),
        decreases gb,
    {
        gb = gb - 1;
    }
    (ga, gb)
}

/// Lines of excluded groups below `jlo(ga)` and from `jlo(gb)` on are in no group.
pub proof fn lemma_zone_lines(c: Cols, x: Ctx, ga: int, gb: int)
    requires
        li_ok(c), groups_ok(c),
        0 <= ga <= gb <= c.ls_bases@.len(),
        forall|g: int| 0 <= g < ga ==> #[trigger] excluded(c, g),
        forall|g: int| gb <= g < c.ls_bases@.len() ==> #[trigger] excluded(c, g),
    ensures
        forall|j: int| 0 <= j < jlo(c, ga) ==> #[trigger] l_grp(c, x, j) == -1,
        forall|j: int| jlo(c, gb) <= j < c.n_l ==> #[trigger] l_grp(c, x, j) == -1,
        0 <= jlo(c, ga) <= jlo(c, gb) <= c.n_l,
{
    let bs = c.bs_l as int;
    let ng = c.ls_bases@.len() as int;
    assert(ga * bs <= gb * bs) by (nonlinear_arith) requires ga <= gb, bs >= 1;
    assert(ga * bs >= 0) by (nonlinear_arith) requires ga >= 0, bs >= 1;
    assert forall|j: int| 0 <= j < jlo(c, ga) implies #[trigger] l_grp(c, x, j) == -1 by {
        assert(j < ga * bs);
        assert(j / bs < ga) by {
            vstd::arithmetic::div_mod::lemma_div_is_ordered(j, ga * bs - 1, bs);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ga * bs - 1, bs);
            if ga * bs - 1 >= 0 {
                vstd::arithmetic::div_mod::lemma_div_multiples_vanish_fancy(ga - 1, bs - 1, bs);
                assert(ga * bs - 1 == (ga - 1) * bs + (bs - 1)) by (nonlinear_arith);
            }
        }
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, bs);
        lemma_excluded_line(c, x, j);
    }
    assert forall|j: int| jlo(c, gb) <= j < c.n_l implies #[trigger] l_grp(c, x, j) == -1 by {
        assert(j >= gb * bs);
        assert(j / bs >= gb) by {
            vstd::arithmetic::div_mod::lemma_div_is_ordered(gb * bs, j, bs);
            vstd::arithmetic::div_mod::lemma_div_by_multiple(gb, bs);
        }
        assert(j / bs < ng) by {
            crate::stores::facts::interface::common::read::lemma_div_lt(j, bs, ng);
        }
        lemma_excluded_line(c, x, j);
    }
}

} // verus!
