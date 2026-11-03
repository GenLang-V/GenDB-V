//! Small structures built on the calling thread: the group of every nation row (`nation_reps`: the first row with
//! its name, `answer::nrep`), the slot of every nation key (`nation_table`: its nation's group, 255 for a key no nation
//! has), the slot of every supplier (`supplier_slots`), and the year of every stored day of a window (`year_table`).
//!
//! Slots fit a byte and a day's year slot is `year - Y0` (255 outside `Y0 .. Y0 + 255`), so the lineitem scan
//! accumulates into a table of `NG x YW` slots (`NG` nation groups, `YW` years).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::datetime::civil_from_date;
use crate::spec::fns::extract::extract_field;
use crate::spec::ast::ScalarFn;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::source_check::date32_val;
use crate::exec::datetime::{civil_from_date_exec, day_bound};
use crate::link::query::{text_wf, text_at};
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::lines::*;
use crate::agent::answer::*;
use crate::agent::columns::*;
use crate::agent::partmatch::positional;

verus! {

/// Nation groups the scan's table holds.
pub const NG: usize = 32;

/// Years the scan's table holds, from `Y0`.
pub const YW: usize = 255;

/// The first year of the table.
pub const Y0: i64 = 1900;

/// The first stored day of the year table: 1970-01-01 (days since 1970-01-01).
pub const D0: i32 = 0;

/// Days of the year table (to 2024-10-04; a day outside the window sends the query to the general path).
pub const ND: usize = 20000;

// ------------------------------------------------------------------------------------------------ nations

/// The slot of nation key `k`: its nation's group, or 255 when no nation has the key.
pub open spec fn slot_of(sv: StoresView, k: i64) -> int {
    if has_key(nk(sv), k) { nrep(sv, key_row(nk(sv), k)) } else { 255 }
}

/// At most `NG` nations, every nation key in `0..256`.
pub open spec fn nations_small(sv: StoresView) -> bool {
    &&& n_n(sv) <= NG
    &&& forall|a: int| 0 <= a < n_n(sv) ==> 0 <= #[trigger] nk(sv)[a] < 256
}

/// The byte range of nation row `a`'s name.
fn nation_name(c: &Cols, a: usize, Ghost(sv): Ghost<StoresView>) -> (se: (usize, usize))
    requires cols_ok(*c, sv), a < c.nn,
    ensures se.0 <= se.1 <= c.nbytes@.len(), c.nbytes@.subrange(se.0 as int, se.1 as int) == nname(sv, a as int),
{
    let s = c.noffs[a];
    let e = c.noffs[a + 1];
    assert(0 <= s <= e <= c.nbytes@.len());
    (s as usize, e as usize)
}

/// Whether two byte ranges hold the same bytes.
pub fn bytes_eq(b: &[u8], s1: usize, e1: usize, s2: usize, e2: usize) -> (r: bool)
    requires s1 <= e1 <= b@.len(), s2 <= e2 <= b@.len(),
    ensures r == (b@.subrange(s1 as int, e1 as int) == b@.subrange(s2 as int, e2 as int)),
{
    if e1 - s1 != e2 - s2 {
        proof {
            assert(b@.subrange(s1 as int, e1 as int).len() != b@.subrange(s2 as int, e2 as int).len());
        }
        return false;
    }
    let n = e1 - s1;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n, n == e1 - s1, n == e2 - s2, e1 <= b@.len(), e2 <= b@.len(),
            forall|j: int| 0 <= j < i ==> b@[s1 + j] == #[trigger] b@[s2 + j],
        decreases n - i,
    {
        if b[s1 + i] != b[s2 + i] {
            proof {
                assert(b@.subrange(s1 as int, e1 as int)[i as int] != b@.subrange(s2 as int, e2 as int)[i as int]);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(b@.subrange(s1 as int, e1 as int) =~= b@.subrange(s2 as int, e2 as int)) by {
            assert forall|j: int| 0 <= j < n implies b@.subrange(s1 as int, e1 as int)[j] == b@.subrange(s2 as int, e2 as int)[j] by {
                assert(b@[s1 + j] == b@[s2 + j]);
            }
        }
    }
    true
}

/// The first nation row with the name of row `a` (whose name is the bytes `sa..ea`).
fn first_same(c: &Cols, a: usize, sa: usize, ea: usize, Ghost(sv): Ghost<StoresView>) -> (r: usize)
    requires cols_ok(*c, sv), a < c.nn, sa <= ea <= c.nbytes@.len(), c.nbytes@.subrange(sa as int, ea as int) == nname(sv, a as int),
    ensures r as int == nrep(sv, a as int),
{
    let mut b: usize = 0;
    while b < a
        invariant
            b <= a, a < c.nn, cols_ok(*c, sv),
            sa <= ea <= c.nbytes@.len(), c.nbytes@.subrange(sa as int, ea as int) == nname(sv, a as int),
            rep_from(sv, a as int, b as int) == nrep(sv, a as int),
        decreases a - b,
    {
        let (sb, eb) = nation_name(c, b, Ghost(sv));
        if bytes_eq(c.nbytes, sb, eb, sa, ea) {
            return b;
        }
        b = b + 1;
    }
    a
}

/// The group of every nation row: the first row with its name.
pub fn nation_reps(c: &Cols, Ghost(sv): Ghost<StoresView>) -> (reps: Vec<usize>)
    requires cols_ok(*c, sv),
    ensures reps@.len() == c.nn, forall|a: int| 0 <= a < c.nn ==> #[trigger] reps@[a] as int == nrep(sv, a),
{
    let nn = c.nn;
    let mut reps: Vec<usize> = Vec::new();
    let mut a: usize = 0;
    while a < nn
        invariant
            a <= nn, nn == c.nn, cols_ok(*c, sv), reps@.len() == a,
            forall|x: int| 0 <= x < a ==> #[trigger] reps@[x] as int == nrep(sv, x),
        decreases nn - a,
    {
        let (sa, ea) = nation_name(c, a, Ghost(sv));
        let rep = first_same(c, a, sa, ea, Ghost(sv));
        reps.push(rep);
        a = a + 1;
    }
    reps
}

/// The nation row with key `k`, if any.
fn find_nation(c: &Cols, k: i64, Ghost(sv): Ghost<StoresView>) -> (r: Option<usize>)
    requires cols_ok(*c, sv),
    ensures
        r matches Some(a) ==> a < c.nn && nk(sv)[a as int] == k && key_row(nk(sv), k) == a && has_key(nk(sv), k),
        r is None ==> !has_key(nk(sv), k),
{
    let mut a: usize = 0;
    while a < c.nn
        invariant a <= c.nn, cols_ok(*c, sv), forall|x: int| 0 <= x < a ==> #[trigger] nk(sv)[x] != k,
        decreases c.nn - a,
    {
        if c.nkey[a] == k {
            proof {
                assert(has_key(nk(sv), k));
                lemma_key_row(nk(sv), k);
            }
            return Some(a);
        }
        a = a + 1;
    }
    proof {
        assert(!has_key(nk(sv), k)) by {
            if has_key(nk(sv), k) {
                let j = choose|j: int| 0 <= j < nk(sv).len() && #[trigger] nk(sv)[j] == k;
                assert(nk(sv)[j] != k);
            }
        }
    }
    None
}

/// The slot of every nation key `0..256`, when there are at most `NG` nations and every nation key is in `0..256`.
pub fn nation_table(c: &Cols, reps: &Vec<usize>, Ghost(sv): Ghost<StoresView>) -> (r: Option<Vec<u8>>)
    requires
        cols_ok(*c, sv), reps@.len() == c.nn,
        forall|a: int| 0 <= a < c.nn ==> #[trigger] reps@[a] as int == nrep(sv, a),
    ensures
        r matches Some(t) ==> nations_small(sv) && t@.len() == 256
            && forall|k: int| 0 <= k < 256 ==> #[trigger] t@[k] as int == slot_of(sv, k as i64),
{
    let nn = c.nn;
    if nn > NG {
        return None;
    }
    let mut a: usize = 0;
    while a < nn
        invariant a <= nn, nn == c.nn, cols_ok(*c, sv), forall|x: int| 0 <= x < a ==> 0 <= #[trigger] nk(sv)[x] < 256,
        decreases nn - a,
    {
        if c.nkey[a] < 0 || c.nkey[a] >= 256 {
            return None;
        }
        a = a + 1;
    }
    let mut t: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    while k < 256
        invariant
            k <= 256, nn == c.nn, nn <= NG, cols_ok(*c, sv), nations_small(sv), t@.len() == k,
            reps@.len() == nn, forall|a: int| 0 <= a < nn ==> #[trigger] reps@[a] as int == nrep(sv, a),
            forall|x: int| 0 <= x < k ==> #[trigger] t@[x] as int == slot_of(sv, x as i64),
        decreases 256 - k,
    {
        let slot: u8 = match find_nation(c, k as i64, Ghost(sv)) {
            Some(a) => {
                proof { lemma_nrep(sv, a as int); }
                reps[a] as u8
            },
            None => 255,
        };
        t.push(slot);
        k = k + 1;
    }
    Some(t)
}

/// The slot of every supplier's nation key, and whether `s_suppkey` is positional from `sbase`.
pub fn supplier_slots(c: &Cols, ntab: &Vec<u8>, sbase: i64, Ghost(sv): Ghost<StoresView>) -> (r: (Vec<u8>, bool))
    requires
        cols_ok(*c, sv), nations_small(sv), ntab@.len() == 256,
        forall|k: int| 0 <= k < 256 ==> #[trigger] ntab@[k] as int == slot_of(sv, k as i64),
        0 <= sbase, sbase + c.ns < i64::MAX,
    ensures
        r.0@.len() == c.ns,
        forall|s: int| 0 <= s < c.ns ==> #[trigger] r.0@[s] as int == slot_of(sv, sn(sv)[s]),
        r.1 ==> positional(sk(sv), sbase as int),
{
    let ns = c.ns;
    // one zeroed allocation, filled by index (no growth on the calling thread)
    let mut slots: Vec<u8> = crate::agent::common::zeroed::zeros_u8(ns);
    let mut pos = true;
    let mut s: usize = 0;
    while s < ns
        invariant
            s <= ns, ns == c.ns, cols_ok(*c, sv), nations_small(sv), ntab@.len() == 256,
            forall|k: int| 0 <= k < 256 ==> #[trigger] ntab@[k] as int == slot_of(sv, k as i64),
            0 <= sbase, sbase + ns < i64::MAX, slots@.len() == ns,
            forall|x: int| 0 <= x < s ==> #[trigger] slots@[x] as int == slot_of(sv, sn(sv)[x]),
            pos ==> forall|x: int| 0 <= x < s ==> #[trigger] sk(sv)[x] as int == sbase + x,
        decreases ns - s,
    {
        let k = c.snat[s];
        let slot = if 0 <= k && k < 256 {
            ntab[k as usize]
        } else {
            proof {
                assert(!has_key(nk(sv), k)) by {
                    if has_key(nk(sv), k) {
                        let j = choose|j: int| 0 <= j < nk(sv).len() && #[trigger] nk(sv)[j] == k;
                    }
                }
            }
            255u8
        };
        if c.skey[s] != sbase + s as i64 {
            pos = false;
        }
        let ghost before = slots@;
        slots[s] = slot;
        proof {
            assert forall|x: int| 0 <= x < s + 1 implies #[trigger] slots@[x] as int == slot_of(sv, sn(sv)[x]) by {
                if x < s { assert(slots@[x] == before[x]); }
            }
        }
        s = s + 1;
    }
    (slots, pos)
}

// ------------------------------------------------------------------------------------------------ years

/// The year slot of stored day `x`: `year - Y0` inside the table's years, else 255.
pub open spec fn yslot(x: i32) -> int {
    if Y0 <= day_year(x) < Y0 + 255 { day_year(x) - Y0 } else { 255 }
}

/// The year table: the year slot of every day `D0 + d` of the window.
pub open spec fn ytab_ok(t: Seq<u8>) -> bool {
    &&& t.len() == ND
    &&& forall|d: int| 0 <= d < ND ==> #[trigger] t[d] as int == yslot((D0 + d) as i32)
}

/// `EXTRACT(YEAR ..)` of stored day `x` (days since 1970-01-01).
pub fn day_year_exec(x: i32) -> (y: i64)
    ensures y as int == day_year(x),
{
    proof { assert(day_bound() == 0x1_0000_0000); }
    let (cy, _, _) = civil_from_date_exec(x as i64 - 10957);
    proof {
        assert(date32_val(x) == Val::Date(x as int - 10957));
        assert(civil_from_date(x as int - 10957).0 == cy as int);
    }
    if cy > 0 { cy } else { cy - 1 }
}

/// The year slot of every day of the window.
pub fn year_table() -> (t: Vec<u8>)
    ensures ytab_ok(t@),
{
    let mut t: Vec<u8> = Vec::new();
    let mut d: usize = 0;
    while d < ND
        invariant d <= ND, t@.len() == d, forall|x: int| 0 <= x < d ==> #[trigger] t@[x] as int == yslot((D0 + x) as i32),
        decreases ND - d,
    {
        let x: i32 = D0 + d as i32;
        let y = day_year_exec(x);
        let slot: u8 = if Y0 <= y && y < Y0 + 255 { (y - Y0) as u8 } else { 255 };
        t.push(slot);
        d = d + 1;
    }
    t
}

} // verus!
