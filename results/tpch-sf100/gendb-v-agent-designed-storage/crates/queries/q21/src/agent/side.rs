//! The supplier side of Q21 over storage `suppliers` (supplier and nation in canonical row order): the column
//! slices (`SCols`), the nation keys whose n_name is `$1` (`nation_keys`), the suppliers of those nations as count
//! slots (`nation_suppliers`: slot `t` is supplier row `srows[t]`, in increasing row order), and whether the slots'
//! names are strictly increasing bytewise (`names_increasing`, so distinct: then every name group is one slot).
use vstd::prelude::*;
use crate::spec::text::lex_cmp;
use crate::stores::suppliers::interface::common::colfmt::{text_of, text_range_ok, text_parts_wf};
use crate::stores::suppliers::interface::common::read::{text_slice, bytes_cmp};
use super::model::{in_i64, lemma_div_below, lemma_div_group};
use super::wscan::{bt, low_index, sub_slice, lemma_zero_bit, lemma_or_bits, lemma_clear_bits, lemma_wsub};

verus! {

/// Column slices of supplier (`n_s` rows, groups of `bs_s`) and nation (`n_n` rows, groups of `bs_n`).
pub struct SCols {
    pub sk_codes: &'static [u32],
    pub sk_bases: &'static [i64],
    pub sn_codes: &'static [u8],
    pub sn_bases: &'static [i64],
    pub sm_offs: &'static [u64],
    pub sm_bytes: &'static [u8],
    pub n_s: usize,
    pub bs_s: usize,
    pub nk_codes: &'static [u8],
    pub nk_bases: &'static [i64],
    pub nm_offs: &'static [u64],
    pub nm_bytes: &'static [u8],
    pub n_n: usize,
    pub bs_n: usize,
}

impl Copy for SCols {}

impl Clone for SCols {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

/// s_suppkey of supplier row `r`.
pub open spec fn skey(c: SCols, r: int) -> int {
    c.sk_bases@[r / c.bs_s as int] + c.sk_codes@[r]
}

/// s_nationkey of supplier row `r`.
pub open spec fn snat(c: SCols, r: int) -> int {
    c.sn_bases@[r / c.bs_s as int] + c.sn_codes@[r]
}

/// s_name of supplier row `r`.
pub open spec fn sname(c: SCols, r: int) -> Seq<u8> {
    text_of(c.sm_offs@, c.sm_bytes@, r)
}

/// n_nationkey of nation row `n`.
pub open spec fn nkey(c: SCols, n: int) -> int {
    c.nk_bases@[n / c.bs_n as int] + c.nk_codes@[n]
}

/// n_name of nation row `n`.
pub open spec fn nname(c: SCols, n: int) -> Seq<u8> {
    text_of(c.nm_offs@, c.nm_bytes@, n)
}

/// Shapes of the slices and decoded values in `i64`.
pub open spec fn scols_ok(c: SCols) -> bool {
    &&& c.bs_s >= 1
    &&& c.bs_n >= 1
    &&& c.sk_codes@.len() == c.n_s
    &&& c.sn_codes@.len() == c.n_s
    &&& c.sn_bases@.len() == c.sk_bases@.len()
    &&& c.sk_bases@.len() * c.bs_s >= c.n_s
    &&& text_parts_wf(c.sm_offs@, c.sm_bytes@, c.n_s as int)
    &&& c.nk_codes@.len() == c.n_n
    &&& c.nk_bases@.len() * c.bs_n >= c.n_n
    &&& text_parts_wf(c.nm_offs@, c.nm_bytes@, c.n_n as int)
    &&& forall|r: int| 0 <= r < c.n_s ==> in_i64(#[trigger] skey(c, r))
    &&& forall|r: int| 0 <= r < c.n_s ==> in_i64(#[trigger] snat(c, r))
    &&& forall|n: int| 0 <= n < c.n_n ==> in_i64(#[trigger] nkey(c, n))
}

/// Bytewise equality of two byte strings.
pub fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures r == (a@ == b@),
{
    let n = a.len();
    if n != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            n == a@.len(),
            n == b@.len(),
            i <= n,
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases n - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    assert(a@ =~= b@);
    true
}

/// The nation keys of the nation rows named `name`: `nks[i]` is `nkey(wit[i])` of a nation row `wit[i]` with that
/// name, and every such row's key is listed.
pub open spec fn nks_ok(c: SCols, name: Seq<u8>, nks: Seq<i64>, wit: Seq<int>) -> bool {
    &&& wit.len() == nks.len()
    &&& forall|i: int| 0 <= i < nks.len() ==> 0 <= #[trigger] wit[i] < c.n_n && nname(c, wit[i]) == name && nks[i] == nkey(c, wit[i])
    &&& forall|n: int| 0 <= n < c.n_n && nname(c, n) == name ==> #[trigger] nks.contains(nkey(c, n) as i64)
}

/// The keys of the nations named `name`.
pub fn nation_keys(c: &SCols, name: &[u8]) -> (r: (Vec<i64>, Ghost<Seq<int>>))
    requires scols_ok(*c),
    ensures nks_ok(*c, name@, r.0@, r.1@),
{
    let n_n = c.n_n;
    let mut nks: Vec<i64> = Vec::new();
    let ghost mut wit: Seq<int> = Seq::empty();
    let mut n: usize = 0;
    while n < n_n
        invariant
            scols_ok(*c),
            n_n == c.n_n,
            n <= n_n,
            wit.len() == nks@.len(),
            forall|i: int| 0 <= i < nks@.len() ==> 0 <= #[trigger] wit[i] < c.n_n && nname(*c, wit[i]) == name@ && nks@[i] == nkey(*c, wit[i]),
            forall|m: int| 0 <= m < n && nname(*c, m) == name@ ==> #[trigger] nks@.contains(nkey(*c, m) as i64),
        decreases n_n - n,
    {
        assert(text_range_ok(c.nm_offs@, c.nm_bytes@, n as int));
        let nm = text_slice(c.nm_offs, c.nm_bytes, n);
        if bytes_eq(nm, name) {
            proof {
                lemma_div_below(n as int, c.bs_n as int, c.nk_bases@.len() as int);
                assert(in_i64(nkey(*c, n as int)));
            }
            let k = c.nk_bases[n / c.bs_n] + c.nk_codes[n] as i64;
            let ghost old_nks = nks@;
            let ghost old_wit = wit;
            nks.push(k);
            proof {
                wit = wit.push(n as int);
                assert(nks@[nks@.len() - 1] == k);
                assert(nm@ == nname(*c, n as int));
                assert forall|m: int| 0 <= m < n + 1 && nname(*c, m) == name@ implies #[trigger] nks@.contains(nkey(*c, m) as i64) by {
                    if m < n {
                        assert(old_nks.contains(nkey(*c, m) as i64));
                        let i = choose|i: int| 0 <= i < old_nks.len() && old_nks[i] == nkey(*c, m) as i64;
                        assert(nks@[i] == old_nks[i]);
                    } else {
                        assert(nks@[nks@.len() - 1] == nkey(*c, m) as i64);
                    }
                }
                assert forall|i: int| 0 <= i < nks@.len() implies 0 <= #[trigger] wit[i] < c.n_n && nname(*c, wit[i]) == name@ && nks@[i] == nkey(*c, wit[i]) by {
                    if i < old_nks.len() {
                        assert(nks@[i] == old_nks[i] && wit[i] == old_wit[i]);
                    }
                }
            }
        }
        n = n + 1;
    }
    (nks, Ghost(wit))
}

/// Supplier row `r` is in a nation listed in `nks`.
pub open spec fn in_nation(c: SCols, nks: Seq<i64>, r: int) -> bool {
    nks.contains(snat(c, r) as i64)
}

/// The slots: `srows` are exactly the supplier rows in a listed nation, increasing; `skeys` their keys.
pub open spec fn slots_ok(c: SCols, nks: Seq<i64>, srows: Seq<usize>, skeys: Seq<i64>) -> bool {
    &&& srows.len() == skeys.len()
    &&& forall|t: int| 0 <= t < srows.len() ==> #[trigger] srows[t] < c.n_s && in_nation(c, nks, srows[t] as int)
    &&& forall|t: int| 0 <= t < srows.len() ==> #[trigger] skeys[t] == skey(c, srows[t] as int)
    &&& forall|a: int, b: int| 0 <= a < b < srows.len() ==> #[trigger] srows[a] < #[trigger] srows[b]
    &&& forall|r: int| 0 <= r < c.n_s && #[trigger] in_nation(c, nks, r) ==> srows.contains(r as usize)
}

/// Whether nation key `k` is listed.
fn listed(nks: &Vec<i64>, k: i64) -> (r: bool)
    ensures r == nks@.contains(k),
{
    let n = nks.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == nks@.len(),
            i <= n,
            forall|j: int| 0 <= j < i ==> nks@[j] != k,
        decreases n - i,
    {
        if nks[i] == k {
            assert(nks@[i as int] == k);
            return true;
        }
        i = i + 1;
    }
    false
}

/// The supplier rows in a listed nation, with their keys: group by group when one nation key is listed
/// (`suppliers_of_key`), else row by row.
pub fn nation_suppliers(c: &SCols, nks: &Vec<i64>) -> (r: (Vec<usize>, Vec<i64>))
    requires scols_ok(*c),
    ensures slots_ok(*c, nks@, r.0@, r.1@),
{
    if nks.len() == 1 {
        suppliers_of_key(c, nks)
    } else {
        nation_suppliers_rows(c, nks)
    }
}

/// Match bits of `len` codes: bit `u` is `cs[u] == t`; bits from `len` on are clear.
#[inline(always)]
fn eq_bits(cs: &[u8], t: u8, len: usize) -> (m: u64)
    requires
        1 <= len <= 64,
        cs@.len() == len,
    ensures
        forall|u: u64| u < len ==> #[trigger] bt(m, u) == (cs@[u as int] == t),
        forall|u: u64| len <= u < 64 ==> !#[trigger] bt(m, u),
    no_unwind
{
    let mut m: u64 = 0;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bt(m, u) by { lemma_zero_bit(u); }
    }
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len <= 64,
            cs@.len() == len,
            forall|u: u64| u < i ==> #[trigger] bt(m, u) == (cs@[u as int] == t),
            forall|u: u64| i <= u < 64 ==> !#[trigger] bt(m, u),
        decreases len - i,
    {
        let d = (cs[i] == t) as u64;
        proof { lemma_or_bits(m, d, i as u64); }
        m = m | (d << (i as u64));
        i = i + 1;
    }
    m
}

/// `eq_bits` of 64 codes (a constant trip count, so the compiler vectorizes the loop without a remainder).
#[inline(always)]
fn eq_bits64(cs: &[u8], t: u8) -> (m: u64)
    requires
        cs@.len() == 64,
    ensures
        forall|u: u64| u < 64 ==> #[trigger] bt(m, u) == (cs@[u as int] == t),
    no_unwind
{
    let mut m: u64 = 0;
    proof {
        assert forall|u: u64| u < 64 implies !#[trigger] bt(m, u) by { lemma_zero_bit(u); }
    }
    let mut i: usize = 0;
    while i < 64
        invariant
            i <= 64,
            cs@.len() == 64,
            forall|u: u64| u < i ==> #[trigger] bt(m, u) == (cs@[u as int] == t),
            forall|u: u64| i <= u < 64 ==> !#[trigger] bt(m, u),
        decreases 64 - i,
    {
        let d = (cs[i] == t) as u64;
        proof { lemma_or_bits(m, d, i as u64); }
        m = m | (d << (i as u64));
        i = i + 1;
    }
    m
}

/// The supplier rows whose nation key is the one listed key, with their keys. Group by group: a group whose base
/// puts the key outside its 8-bit codes holds none; otherwise its rows' codes are compared with the key's code.
fn suppliers_of_key(c: &SCols, nks: &Vec<i64>) -> (r: (Vec<usize>, Vec<i64>))
    requires scols_ok(*c), nks@.len() == 1,
    ensures slots_ok(*c, nks@, r.0@, r.1@),
{
    let nk0 = nks[0];
    let n_s = c.n_s;
    let bs = c.bs_s;
    let mut srows: Vec<usize> = Vec::new();
    let mut skeys: Vec<i64> = Vec::new();
    let mut gs: usize = 0;
    let mut g: usize = 0;
    proof {
        assert forall|x: int| 0 <= x < c.n_s implies #[trigger] in_nation(*c, nks@, x) == (snat(*c, x) == nk0) by {
            if in_nation(*c, nks@, x) {
                let i = choose|i: int| 0 <= i < nks@.len() && nks@[i] == snat(*c, x) as i64;
                assert(i == 0);
            }
            if snat(*c, x) == nk0 {
                assert(nks@[0] == snat(*c, x) as i64);
            }
        }
    }
    while gs < n_s
        invariant
            scols_ok(*c),
            n_s == c.n_s,
            bs == c.bs_s,
            nks@.len() == 1,
            nk0 == nks@[0],
            forall|x: int| 0 <= x < c.n_s ==> #[trigger] in_nation(*c, nks@, x) == (snat(*c, x) == nk0),
            gs <= n_s,
            gs < n_s ==> gs == g * bs,
            srows@.len() == skeys@.len(),
            forall|t: int| 0 <= t < srows@.len() ==> #[trigger] srows@[t] < gs && in_nation(*c, nks@, srows@[t] as int),
            forall|t: int| 0 <= t < srows@.len() ==> #[trigger] skeys@[t] == skey(*c, srows@[t] as int),
            forall|a: int, b: int| 0 <= a < b < srows@.len() ==> #[trigger] srows@[a] < #[trigger] srows@[b],
            forall|x: int| 0 <= x < gs && #[trigger] in_nation(*c, nks@, x) ==> srows@.contains(x as usize),
        decreases n_s - gs,
    {
        proof {
            lemma_div_below(gs as int, bs as int, c.sk_bases@.len() as int);
            lemma_div_group(gs as int, bs as int, g as int);
        }
        let ge = if bs <= n_s - gs { gs + bs } else { n_s };
        let d = nk0 as i128 - c.sn_bases[g] as i128;
        if d >= 0 && d <= 255 {
            let t = d as u8;
            let kb = c.sk_bases[g];
            let mut r = gs;
            // 64 rows at a time: one vectorized byte compare gives the rows' match bits, then only the set bits
            // (about one row in 25) are visited.
            while r < ge
                invariant
                    scols_ok(*c),
                    n_s == c.n_s,
                    bs == c.bs_s,
                    nks@.len() == 1,
                    nk0 == nks@[0],
                    forall|x: int| 0 <= x < c.n_s ==> #[trigger] in_nation(*c, nks@, x) == (snat(*c, x) == nk0),
                    gs == g * bs,
                    g < c.sk_bases@.len(),
                    gs <= r <= ge <= n_s,
                    ge <= gs + bs,
                    t as int == nk0 - c.sn_bases@[g as int],
                    kb == c.sk_bases@[g as int],
                    srows@.len() == skeys@.len(),
                    forall|u: int| 0 <= u < srows@.len() ==> #[trigger] srows@[u] < r && in_nation(*c, nks@, srows@[u] as int),
                    forall|u: int| 0 <= u < srows@.len() ==> #[trigger] skeys@[u] == skey(*c, srows@[u] as int),
                    forall|a: int, b: int| 0 <= a < b < srows@.len() ==> #[trigger] srows@[a] < #[trigger] srows@[b],
                    forall|x: int| 0 <= x < r && #[trigger] in_nation(*c, nks@, x) ==> srows@.contains(x as usize),
                decreases ge - r,
            {
                let len = if ge - r < 64 { ge - r } else { 64 };
                let w = sub_slice(c.sn_codes, r, len);
                let m = if len == 64 { eq_bits64(w, t) } else { eq_bits(w, t, len) };
                proof {
                    assert forall|u: u64| u < len implies #[trigger] bt(m, u) == in_nation(*c, nks@, r + u) by {
                        assert(w@[u as int] == c.sn_codes@[r + u]);
                        lemma_div_group(r + u, bs as int, g as int);
                    }
                }
                let mut tm = m;
                let mut p: usize = 0;
                while tm != 0
                    invariant
                        scols_ok(*c),
                        n_s == c.n_s,
                        bs == c.bs_s,
                        nks@.len() == 1,
                        gs == g * bs,
                        g < c.sk_bases@.len(),
                        gs <= r,
                        r + len <= ge <= n_s,
                        ge <= gs + bs,
                        1 <= len <= 64,
                        kb == c.sk_bases@[g as int],
                        p <= len,
                        forall|u: u64| u < len ==> #[trigger] bt(m, u) == in_nation(*c, nks@, r + u),
                        forall|u: u64| len <= u < 64 ==> !#[trigger] bt(m, u),
                        forall|u: u64| p <= u < 64 ==> #[trigger] bt(tm, u) == bt(m, u),
                        forall|u: u64| u < p ==> !#[trigger] bt(tm, u),
                        srows@.len() == skeys@.len(),
                        forall|u: int| 0 <= u < srows@.len() ==> #[trigger] srows@[u] < r + p && in_nation(*c, nks@, srows@[u] as int),
                        forall|u: int| 0 <= u < srows@.len() ==> #[trigger] skeys@[u] == skey(*c, srows@[u] as int),
                        forall|a: int, b: int| 0 <= a < b < srows@.len() ==> #[trigger] srows@[a] < #[trigger] srows@[b],
                        forall|x: int| 0 <= x < r + p && #[trigger] in_nation(*c, nks@, x) ==> srows@.contains(x as usize),
                    decreases tm,
                {
                    let i = low_index(tm);
                    proof {
                        if i < p as u64 {
                            assert(!bt(tm, i));
                        }
                        if i >= len as u64 {
                            assert(bt(m, i));
                        }
                    }
                    let x = r + i as usize;
                    proof {
                        assert(bt(m, i));
                        assert(in_nation(*c, nks@, x as int));
                        lemma_div_group(x as int, bs as int, g as int);
                        assert(in_i64(skey(*c, x as int)));
                    }
                    let k = kb + c.sk_codes[x] as i64;
                    let ghost old_rows = srows@;
                    srows.push(x);
                    skeys.push(k);
                    proof {
                        assert(srows@[srows@.len() - 1] == x);
                        // The rows between the last visited one and x are not in the nation (their bits are clear).
                        assert forall|y: int| 0 <= y < x + 1 && #[trigger] in_nation(*c, nks@, y) implies srows@.contains(y as usize) by {
                            if y < r + p {
                                let j = choose|j: int| 0 <= j < old_rows.len() && old_rows[j] == y as usize;
                                assert(srows@[j] == old_rows[j]);
                            } else if y < x {
                                let u = (y - r) as u64;
                                assert(p as u64 <= u && u < i);
                                assert(!bt(tm, u));
                                assert(bt(m, u) == in_nation(*c, nks@, r + u));
                            } else {
                                assert(srows@[srows@.len() - 1] == y as usize);
                            }
                        }
                        assert forall|a: int, b: int| 0 <= a < b < srows@.len() implies #[trigger] srows@[a] < #[trigger] srows@[b] by {
                            if b < old_rows.len() {
                                assert(srows@[a] == old_rows[a] && srows@[b] == old_rows[b]);
                            } else {
                                assert(srows@[a] == old_rows[a]);
                            }
                        }
                        assert forall|u: int| 0 <= u < srows@.len() implies #[trigger] srows@[u] < r + i + 1 && in_nation(*c, nks@, srows@[u] as int) by {
                            if u < old_rows.len() {
                                assert(srows@[u] == old_rows[u]);
                            }
                        }
                        assert forall|u: int| 0 <= u < srows@.len() implies #[trigger] skeys@[u] == skey(*c, srows@[u] as int) by {
                            if u < old_rows.len() {
                                assert(srows@[u] == old_rows[u]);
                            }
                        }
                        lemma_clear_bits(tm, i);
                        lemma_wsub(tm, 1u64);
                    }
                    let ghost old_tm = tm;
                    tm = tm & tm.wrapping_sub(1u64);
                    proof {
                        assert forall|u: u64| (i + 1) <= u < 64 implies #[trigger] bt(tm, u) == bt(m, u) by {
                            assert(bt(tm, u) == (bt(old_tm, u) && u != i));
                        }
                        assert forall|u: u64| u < i + 1 implies !#[trigger] bt(tm, u) by {
                            assert(bt(tm, u) == (bt(old_tm, u) && u != i));
                        }
                    }
                    p = (i + 1) as usize;
                }
                proof {
                    // No set bit is left: the rows from r + p to r + len are not in the nation.
                    assert forall|y: int| 0 <= y < r + len && #[trigger] in_nation(*c, nks@, y) implies srows@.contains(y as usize) by {
                        if y >= r + p {
                            let u = (y - r) as u64;
                            lemma_zero_bit(u);
                            assert(bt(tm, u) == bt(m, u));
                        }
                    }
                }
                r = r + len;
            }
        } else {
            proof {
                assert forall|x: int| gs <= x < ge implies !#[trigger] in_nation(*c, nks@, x) by {
                    super::model::lemma_div_group(x, bs as int, g as int);
                }
            }
        }
        proof {
            assert((g + 1) * bs == g * bs + bs) by (nonlinear_arith);
        }
        gs = ge;
        g = g + 1;
    }
    (srows, skeys)
}

/// The supplier rows in a listed nation, with their keys, row by row. With one listed nation key, a group's rows
/// are tested by comparing their nation key codes with that key's code in the group.
fn nation_suppliers_rows(c: &SCols, nks: &Vec<i64>) -> (r: (Vec<usize>, Vec<i64>))
    requires scols_ok(*c),
    ensures slots_ok(*c, nks@, r.0@, r.1@),
{
    let n_s = c.n_s;
    let bs_s = c.bs_s;
    let one = nks.len() == 1;
    let nk0: i64 = if one { nks[0] } else { 0 };
    let mut srows: Vec<usize> = Vec::new();
    let mut skeys: Vec<i64> = Vec::new();
    let mut r: usize = 0;
    // The group of r and its nation key code of nk0 (or none).
    let mut g: usize = 0;
    let mut gend: usize = 0;
    let mut tcode: Option<u8> = None;
    while r < n_s
        invariant
            scols_ok(*c),
            n_s == c.n_s,
            bs_s == c.bs_s,
            r <= n_s,
            one == (nks@.len() == 1),
            one ==> nk0 == nks@[0],
            r < gend ==> (g * bs_s <= r && gend <= g * bs_s + bs_s),
            r < gend ==> match tcode { Some(t) => t as int == nk0 - c.sn_bases@[g as int], None => (nk0 - c.sn_bases@[g as int] < 0 || nk0 - c.sn_bases@[g as int] > 255) },
            srows@.len() == skeys@.len(),
            forall|t: int| 0 <= t < srows@.len() ==> #[trigger] srows@[t] < r && in_nation(*c, nks@, srows@[t] as int),
            forall|t: int| 0 <= t < srows@.len() ==> #[trigger] skeys@[t] == skey(*c, srows@[t] as int),
            forall|a: int, b: int| 0 <= a < b < srows@.len() ==> #[trigger] srows@[a] < #[trigger] srows@[b],
            forall|x: int| 0 <= x < r && #[trigger] in_nation(*c, nks@, x) ==> srows@.contains(x as usize),
        decreases n_s - r,
    {
        proof {
            lemma_div_below(r as int, bs_s as int, c.sk_bases@.len() as int);
            assert(in_i64(snat(*c, r as int)));
            assert(in_i64(skey(*c, r as int)));
        }
        if r >= gend {
            g = r / bs_s;
            proof { super::model::lemma_group_of_row(r as int, bs_s as int); }
            let gs = g * bs_s;
            gend = if bs_s <= n_s - gs { gs + bs_s } else { n_s };
            let d = nk0 as i128 - c.sn_bases[g] as i128;
            tcode = if d >= 0 && d <= 255 { Some(d as u8) } else { None };
        }
        proof {
            super::model::lemma_div_group(r as int, bs_s as int, g as int);
        }
        let hit = if one {
            match tcode {
                Some(t) => c.sn_codes[r] == t,
                None => false,
            }
        } else {
            listed(nks, c.sn_bases[g] + c.sn_codes[r] as i64)
        };
        proof {
            if one {
                assert(nks@.len() == 1);
                if in_nation(*c, nks@, r as int) {
                    let i = choose|i: int| 0 <= i < nks@.len() && nks@[i] == snat(*c, r as int) as i64;
                    assert(i == 0);
                }
                if hit {
                    assert(nks@[0] == snat(*c, r as int) as i64);
                }
            }
            assert(hit == in_nation(*c, nks@, r as int));
        }
        if hit {
            let k = c.sk_bases[g] + c.sk_codes[r] as i64;
            let ghost old_rows = srows@;
            srows.push(r);
            skeys.push(k);
            proof {
                assert(srows@[srows@.len() - 1] == r);
                assert forall|x: int| 0 <= x < r + 1 && #[trigger] in_nation(*c, nks@, x) implies srows@.contains(x as usize) by {
                    if x < r {
                        let i = choose|i: int| 0 <= i < old_rows.len() && old_rows[i] == x as usize;
                        assert(srows@[i] == old_rows[i]);
                    }
                }
                assert forall|a: int, b: int| 0 <= a < b < srows@.len() implies #[trigger] srows@[a] < #[trigger] srows@[b] by {
                    if b < old_rows.len() {
                        assert(srows@[a] == old_rows[a] && srows@[b] == old_rows[b]);
                    } else {
                        assert(srows@[a] == old_rows[a]);
                    }
                }
            }
        }
        r = r + 1;
    }
    (srows, skeys)
}

/// Slot `t`'s name is bytewise below slot `t + 1`'s.
pub open spec fn inc_at(c: SCols, srows: Seq<usize>, t: int) -> bool {
    lex_cmp(sname(c, srows[t] as int), sname(c, srows[t + 1] as int)) < 0
}

/// The slots' names are strictly increasing bytewise.
pub open spec fn names_inc(c: SCols, srows: Seq<usize>) -> bool {
    forall|t: int| 0 <= t < srows.len() - 1 ==> #[trigger] inc_at(c, srows, t)
}

/// Whether the slots' names are strictly increasing (`no_unwind`, for a worker body; the slot count `ns` given).
pub fn names_increasing(c: &SCols, srows: &Vec<usize>, ns: usize) -> (b: bool)
    requires
        scols_ok(*c),
        ns == srows@.len(),
        forall|t: int| 0 <= t < srows@.len() ==> #[trigger] srows@[t] < c.n_s,
    ensures b == names_inc(*c, srows@),
    no_unwind
{
    if ns <= 1 {
        return true;
    }
    let mut t: usize = 0;
    while t + 1 < ns
        invariant
            scols_ok(*c),
            ns == srows@.len(),
            forall|u: int| 0 <= u < srows@.len() ==> #[trigger] srows@[u] < c.n_s,
            ns >= 2,
            t + 1 <= ns,
            forall|u: int| 0 <= u < t ==> #[trigger] inc_at(*c, srows@, u),
        decreases ns - t,
    {
        let a = srows[t];
        let b = srows[t + 1];
        assert(text_range_ok(c.sm_offs@, c.sm_bytes@, a as int));
        assert(text_range_ok(c.sm_offs@, c.sm_bytes@, b as int));
        let x = text_slice(c.sm_offs, c.sm_bytes, a);
        let y = text_slice(c.sm_offs, c.sm_bytes, b);
        let xl = (c.sm_offs[a + 1] - c.sm_offs[a]) as usize;
        let yl = (c.sm_offs[b + 1] - c.sm_offs[b]) as usize;
        proof {
            vstd::slice::axiom_spec_len(c.sm_bytes);
            assert(c.sm_offs@[a + 1] <= c.sm_bytes@.len() <= usize::MAX);
            assert(c.sm_offs@[b + 1] <= c.sm_bytes@.len() <= usize::MAX);
            assert(x@ == text_of(c.sm_offs@, c.sm_bytes@, a as int));
            assert(y@ == text_of(c.sm_offs@, c.sm_bytes@, b as int));
            assert(x@.len() == xl);
            assert(y@.len() == yl);
        }
        if bytes_cmp(x, xl, y, yl) >= 0 {
            proof {
                assert(!inc_at(*c, srows@, t as int));
                assert(0 <= t < srows@.len() - 1);
            }
            return false;
        }
        proof {
            assert(inc_at(*c, srows@, t as int));
        }
        t = t + 1;
    }
    true
}

} // verus!
