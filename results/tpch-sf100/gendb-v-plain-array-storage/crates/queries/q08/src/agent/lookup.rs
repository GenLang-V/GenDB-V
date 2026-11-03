//! Key lookups into orders, customer, supplier and nation, and the nation flags.
//!
//! Each lookup returns the row holding a key, or none: it first tries the row the dbgen layout predicts (orders:
//! the sparse key `((i >> 3) << 5) | (i & 7)` of 1-based row `i`; customer and supplier: key `i` at row `i - 1`)
//! and checks it, and otherwise searches the column. The check makes the answer correct for every stored
//! column; the search only runs when the layout differs. The nation directory `NatDir` maps the keys `0..256`
//! to their row and holds, per nation row, whether its region is `$2` and whether its name is `$1`.
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::text_at;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::cols::*;
use crate::agent::common::text::{text_eq_at, tview};

verus! {

/// The orders row of key `k`, if any.
pub fn order_row(c: &Cols, k: i64, Ghost(sv): Ghost<StoresView>) -> (r: Option<usize>)
    requires cols_ok(*c, sv),
    ensures
        match r {
            Some(j) => j < n_o(sv) && o_key(sv)[j as int] == k,
            None => forall|j: int| 0 <= j < n_o(sv) ==> o_key(sv)[j] != k,
        },
    no_unwind
{
    if k >= 1 {
        let low = (k as u64) % 32;
        if low < 8 {
            let i = ((k as u64) / 32) * 8 + low;
            if i >= 1 && i - 1 < c.no as u64 {
                let j = (i - 1) as usize;
                if c.o_key[j] == k {
                    return Some(j);
                }
            }
        }
    }
    let mut j: usize = 0;
    while j < c.no
        invariant cols_ok(*c, sv), j <= c.no, forall|x: int| 0 <= x < j ==> o_key(sv)[x] != k,
        decreases c.no - j,
    {
        if c.o_key[j] == k {
            return Some(j);
        }
        j = j + 1;
    }
    None
}

/// The customer row of key `k`, if any.
pub fn cust_row(c: &Cols, k: i64, Ghost(sv): Ghost<StoresView>) -> (r: Option<usize>)
    requires cols_ok(*c, sv),
    ensures
        match r {
            Some(j) => j < n_c(sv) && c_key(sv)[j as int] == k,
            None => forall|j: int| 0 <= j < n_c(sv) ==> c_key(sv)[j] != k,
        },
    no_unwind
{
    if k >= 1 && ((k - 1) as u64) < c.nc as u64 {
        let g = (k - 1) as usize;
        if c.c_key[g] == k {
            return Some(g);
        }
    }
    let mut j: usize = 0;
    while j < c.nc
        invariant cols_ok(*c, sv), j <= c.nc, forall|x: int| 0 <= x < j ==> c_key(sv)[x] != k,
        decreases c.nc - j,
    {
        if c.c_key[j] == k {
            return Some(j);
        }
        j = j + 1;
    }
    None
}

/// The supplier row of key `k`, if any.
pub fn supp_row(c: &Cols, k: i64, Ghost(sv): Ghost<StoresView>) -> (r: Option<usize>)
    requires cols_ok(*c, sv),
    ensures
        match r {
            Some(j) => j < n_s(sv) && s_key(sv)[j as int] == k,
            None => forall|j: int| 0 <= j < n_s(sv) ==> s_key(sv)[j] != k,
        },
    no_unwind
{
    if k >= 1 && ((k - 1) as u64) < c.ns as u64 {
        let g = (k - 1) as usize;
        if c.s_key[g] == k {
            return Some(g);
        }
    }
    let mut j: usize = 0;
    while j < c.ns
        invariant cols_ok(*c, sv), j <= c.ns, forall|x: int| 0 <= x < j ==> s_key(sv)[x] != k,
        decreases c.ns - j,
    {
        if c.s_key[j] == k {
            return Some(j);
        }
        j = j + 1;
    }
    None
}

// ------------------------------------------------------------------------------------------------ nations

/// Nation row `n` lies in a region named `$2`.
pub open spec fn in_region(sv: StoresView, ps: Seq<Literal>, n: int) -> bool {
    exists|r: int| 0 <= r < n_r(sv) && #[trigger] reg_hit(sv, ps, r, n)
}

/// The key directory of the nations (keys `0..256`) and the flags of every nation row.
pub struct NatDir {
    pub ktab: Vec<usize>,
    pub rin: Vec<bool>,
    pub rthen: Vec<bool>,
}

/// `ktab[k]` is `0` when no nation has key `k`, otherwise one plus a row with key `k`; `rin` and `rthen` are the
/// region and name flags of every nation row.
pub open spec fn natdir_ok(d: NatDir, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& d.ktab@.len() == 256
    &&& forall|k: int| 0 <= k < 256 ==> (#[trigger] d.ktab@[k] == 0 ==> forall|n: int| 0 <= n < n_n(sv) ==> n_key(sv)[n] != k)
    &&& forall|k: int| 0 <= k < 256 ==> (#[trigger] d.ktab@[k] > 0 ==> d.ktab@[k] <= n_n(sv) && n_key(sv)[d.ktab@[k] - 1] == k)
    &&& d.rin@.len() == n_n(sv)
    &&& forall|n: int| 0 <= n < n_n(sv) ==> #[trigger] d.rin@[n] == in_region(sv, ps, n)
    &&& d.rthen@.len() == n_n(sv)
    &&& forall|n: int| 0 <= n < n_n(sv) ==> #[trigger] d.rthen@[n] == (n_name(sv, n) == nat_of(ps))
}

/// Region and name flags of one nation row.
fn nat_flags(c: &Cols, n: usize, pnat: &[u8], preg: &[u8], Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: (bool, bool))
    requires cols_ok(*c, sv), n < c.nn, pnat@ == nat_of(ps), preg@ == reg_of(ps),
    ensures r.0 == in_region(sv, ps, n as int), r.1 == (n_name(sv, n as int) == nat_of(ps)),
{
    let nat_len = pnat.len();
    let reg_len = preg.len();
    let then = text_eq_at(c.n_noffs, c.n_nbytes, c.n_nnb, n, pnat, nat_len, Ghost(n_n(sv) as int));
    let mut inr = false;
    let mut r: usize = 0;
    while r < c.nr
        invariant
            cols_ok(*c, sv), n < c.nn, r <= c.nr, preg@ == reg_of(ps), reg_len == preg@.len(),
            inr == exists|x: int| 0 <= x < r && #[trigger] reg_hit(sv, ps, x, n as int),
        decreases c.nr - r,
    {
        if !inr && c.r_key[r] == c.n_reg[n] {
            let eq = text_eq_at(c.r_noffs, c.r_nbytes, c.r_nnb, r, preg, reg_len, Ghost(n_r(sv) as int));
            if eq {
                assert(reg_hit(sv, ps, r as int, n as int));
                inr = true;
            }
        }
        proof {
            if !inr {
                assert forall|x: int| 0 <= x < r + 1 implies !#[trigger] reg_hit(sv, ps, x, n as int) by {
                    if x == r as int {
                        assert(r_name(sv, x) == text_at(tview(c.r_noffs@, c.r_nbytes@), x));
                    }
                }
            }
        }
        r = r + 1;
    }
    (inr, then)
}

/// Build the nation directory.
pub fn build_natdir(c: &Cols, pnat: &[u8], preg: &[u8], Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (d: NatDir)
    requires cols_ok(*c, sv), pnat@ == nat_of(ps), preg@ == reg_of(ps),
    ensures natdir_ok(d, sv, ps),
{
    let mut ktab: Vec<usize> = vec![0usize; 256];
    let mut rin: Vec<bool> = Vec::new();
    let mut rthen: Vec<bool> = Vec::new();
    let mut n: usize = 0;
    while n < c.nn
        invariant
            cols_ok(*c, sv), n <= c.nn, pnat@ == nat_of(ps), preg@ == reg_of(ps),
            ktab@.len() == 256,
            forall|k: int| 0 <= k < 256 ==> (#[trigger] ktab@[k] == 0 ==> forall|m: int| 0 <= m < n ==> n_key(sv)[m] != k),
            forall|k: int| 0 <= k < 256 ==> (#[trigger] ktab@[k] > 0 ==> ktab@[k] <= n && n_key(sv)[ktab@[k] - 1] == k),
            rin@.len() == n, rthen@.len() == n,
            forall|m: int| 0 <= m < n ==> #[trigger] rin@[m] == in_region(sv, ps, m),
            forall|m: int| 0 <= m < n ==> #[trigger] rthen@[m] == (n_name(sv, m) == nat_of(ps)),
        decreases c.nn - n,
    {
        let (inr, then) = nat_flags(c, n, pnat, preg, Ghost(sv), Ghost(ps));
        rin.push(inr);
        rthen.push(then);
        let k = c.n_key[n];
        if 0 <= k && k < 256 {
            ktab[k as usize] = n + 1;
        }
        n = n + 1;
    }
    NatDir { ktab, rin, rthen }
}

/// The nation row of key `k`, if any.
pub fn nat_row(c: &Cols, d: &NatDir, k: i64, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Option<usize>)
    requires cols_ok(*c, sv), natdir_ok(*d, sv, ps),
    ensures
        match r {
            Some(j) => j < n_n(sv) && n_key(sv)[j as int] == k,
            None => forall|j: int| 0 <= j < n_n(sv) ==> n_key(sv)[j] != k,
        },
    no_unwind
{
    if 0 <= k && k < 256 {
        let v = d.ktab[k as usize];
        if v == 0 {
            return None;
        } else {
            return Some(v - 1);
        }
    }
    let mut j: usize = 0;
    while j < c.nn
        invariant cols_ok(*c, sv), j <= c.nn, forall|x: int| 0 <= x < j ==> n_key(sv)[x] != k,
        decreases c.nn - j,
    {
        if c.n_key[j] == k {
            return Some(j);
        }
        j = j + 1;
    }
    None
}

} // verus!
