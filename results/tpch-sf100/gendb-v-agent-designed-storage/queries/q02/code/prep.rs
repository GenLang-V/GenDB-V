//! Per-call preparation on the calling thread: `p_type LIKE $2` per p_type dictionary entry (`like_table`), the
//! first part row whose LIKE fails (`first_like_error`), nation and region lookups (`nation_lookups`), the dense
//! key checks of supplier and part (`supp_dense`, `part_dense`: sorted unique keys whose last key is `first +
//! n - 1` are exactly `first + j`), and copies of the lookups for worker tasks.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::fns::like::*;
use crate::spec::chars::chars;
use crate::exec::chars::{chars_exec, view_chars};
use crate::exec::fns::like::{like_tokens_exec, like_mt_exec, view_toks};
use crate::stores::suppliers::interface::common::read::text_slice;
use crate::stores::suppliers::interface::common::keyidx::{sorted_at, fkey, irow};
use vstd::slice::slice_to_vec;
use super::tables::*;
use super::q2spec::*;
use super::scan::*;
use super::sqlq::lemma_like_shape;
use super::sqlrel::like_all_ok;

verus! {

/// Byte equality of two slices.
pub fn slices_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures r == (a@ == b@),
{
    let n = a.len();
    if n != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant n == a@.len(), n == b@.len(), i <= n, a@.subrange(0, i as int) == b@.subrange(0, i as int),
        decreases n - i,
    {
        if a[i] != b[i] {
            assert(a@[i as int] != b@[i as int]);
            return false;
        }
        assert(a@.subrange(0, i + 1) =~= a@.subrange(0, i as int).push(a@[i as int]));
        assert(b@.subrange(0, i + 1) =~= b@.subrange(0, i as int).push(b@[i as int]));
        i = i + 1;
    }
    assert(a@ =~= a@.subrange(0, n as int));
    assert(b@ =~= b@.subrange(0, n as int));
    true
}

// ------------------------------------------------------------------------------------------------ LIKE

/// `LIKE $2` on p_type dictionary entry `e`.
pub open spec fn like_entry(c: Cols, m: Prm, e: int) -> Result<Val, SqlError> {
    like_res(Val::Text(txt(c.p.type_o@, c.p.type_y@, e)), m.pat)
}

pub open spec fn err_ok(x: Option<SqlError>, c: Cols, m: Prm, e: int) -> bool {
    match x {
        Some(err) => like_entry(c, m, e) == Err::<Val, SqlError>(err),
        None => like_entry(c, m, e) is Ok,
    }
}

/// The LIKE outcome of every p_type dictionary entry: true/false, its error, and whether any entry fails.
pub fn like_table(c: &Cols, pat: &[u8], Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (r: (Vec<bool>, Vec<Option<SqlError>>, bool))
    requires cols_ok(*c, t), pat@ == m.pat,
    ensures
        r.0@.len() == c.p.type_o@.len() - 1,
        r.1@.len() == c.p.type_o@.len() - 1,
        forall|e: int| 0 <= e < r.0@.len() ==> #[trigger] r.0@[e] == like_true(Val::Text(txt(c.p.type_o@, c.p.type_y@, e)), m.pat),
        forall|e: int| 0 <= e < r.1@.len() ==> #[trigger] err_ok(r.1@[e], *c, m, e),
        !r.2 ==> forall|e: int| 0 <= e < r.1@.len() ==> #[trigger] r.1@[e] is None,
{
    let nd = c.p.type_o.len() - 1;
    let pv = slice_to_vec(pat);
    let pc = chars_exec(&pv);
    let mut ev: Vec<u8> = Vec::new();
    ev.push(92u8);
    proof { assert(ev@ =~= seq![92u8]); }
    let esc: Option<Vec<u8>> = Some(ev);
    let toks = like_tokens_exec(&pc, &esc);
    let ghost tk = like_tokens(chars(m.pat), Some(seq![92u8]), 0);
    assert(view_toks(toks@) == tk);
    let mut ok: Vec<bool> = Vec::new();
    let mut errs: Vec<Option<SqlError>> = Vec::new();
    let mut any = false;
    let mut e: usize = 0;
    while e < nd
        invariant
            cols_ok(*c, t), nd == c.p.type_o@.len() - 1, e <= nd,
            view_toks(toks@) == tk, tk == like_tokens(chars(m.pat), Some(seq![92u8]), 0),
            ok@.len() == e, errs@.len() == e,
            forall|x: int| 0 <= x < e ==> #[trigger] ok@[x] == like_true(Val::Text(txt(c.p.type_o@, c.p.type_y@, x)), m.pat),
            forall|x: int| 0 <= x < e ==> #[trigger] err_ok(errs@[x], *c, m, x),
            !any ==> forall|x: int| 0 <= x < e ==> #[trigger] errs@[x] is None,
        decreases nd - e,
    {
        assert(c.p.type_o@[e as int] <= c.p.type_o@[e + 1] && c.p.type_o@[e + 1] <= c.p.type_y@.len());
        let s = text_slice(c.p.type_o, c.p.type_y, e);
        let sv = slice_to_vec(s);
        let tc = chars_exec(&sv);
        let ghost sb = txt(c.p.type_o@, c.p.type_y@, e as int);
        assert(sv@ == sb);
        proof { lemma_like_shape(sb, m.pat); }
        match like_mt_exec(&tc, &toks, 0, 0) {
            Ok(res) => {
                let b = match res { LikeRes::Match => true, _ => false };
                ok.push(b);
                errs.push(None);
            },
            Err(err) => {
                ok.push(false);
                errs.push(Some(err));
                any = true;
            },
        }
        e = e + 1;
    }
    (ok, errs, any)
}

/// The first part row whose LIKE fails, with its error; `None` when no part row's LIKE fails.
pub fn first_like_error(c: &Cols, errs: &Vec<Option<SqlError>>, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>)
    -> (r: Option<(usize, SqlError)>)
    requires
        cols_ok(*c, t),
        errs@.len() == c.p.type_o@.len() - 1,
        forall|e: int| 0 <= e < errs@.len() ==> #[trigger] err_ok(errs@[e], *c, m, e),
    ensures
        r matches Some((i, err)) ==> i < t.p.len() && like_res(t.p[i as int][4], m.pat) == Err::<Val, SqlError>(err)
            && forall|i2: int| 0 <= i2 < i ==> #[trigger] like_res(t.p[i2][4], m.pat) is Ok,
        r is None ==> like_all_ok(t, m),
{
    let mut i: usize = 0;
    while i < c.p.n
        invariant
            cols_ok(*c, t),
            errs@.len() == c.p.type_o@.len() - 1,
            forall|e: int| 0 <= e < errs@.len() ==> #[trigger] err_ok(errs@[e], *c, m, e),
            i <= c.p.n,
            forall|i2: int| 0 <= i2 < i ==> #[trigger] like_res(t.p[i2][4], m.pat) is Ok,
        decreases c.p.n - i,
    {
        assert(part_row_ok(c.p, t.p[i as int], i as int));
        proof { lemma_grp_bound(c.p.n as int, c.p.bs as int, c.p.ng as int, i as int); }
        let g = grp(i, c.p.bs);
        let e = (c.p.type_b[g] + c.p.type_c[i] as u64) as usize;
        assert(err_ok(errs@[e as int], *c, m, e as int));
        match errs[e] {
            Some(err) => {
                return Some((i, err));
            },
            None => {},
        }
        i = i + 1;
    }
    None
}

/// Without a failing dictionary entry no part row's LIKE fails.
pub proof fn lemma_like_all_from_entries(c: Cols, t: Tabs, m: Prm, errs: Seq<Option<SqlError>>)
    requires
        cols_ok(c, t),
        errs.len() == c.p.type_o@.len() - 1,
        forall|e: int| 0 <= e < errs.len() ==> #[trigger] err_ok(errs[e], c, m, e),
        forall|e: int| 0 <= e < errs.len() ==> #[trigger] errs[e] is None,
    ensures like_all_ok(t, m),
{
    assert forall|i: int| 0 <= i < t.p.len() implies #[trigger] like_res(t.p[i][4], m.pat) is Ok by {
        assert(part_row_ok(c.p, t.p[i], i));
        let e = fu8(c.p.type_c@, c.p.type_b@, c.p.bs as int, i);
        assert(err_ok(errs[e], c, m, e));
        assert(errs[e] is None);
    }
}

// ------------------------------------------------------------------------------------------------ nation and region

/// Nation lookups: nation row by nationkey value (below 256), every nation's key, and its region row named `$3`.
pub fn nation_lookups(c: &Cols, rname: &[u8], Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (r: (Vec<usize>, Vec<i64>, Vec<usize>))
    requires cols_ok(*c, t), rname@ == m.rname,
    ensures
        r.0@.len() == 256,
        forall|v: int| 0 <= v < 256 ==> #[trigger] nat_tab_ok(r.0@[v], t, v),
        r.1@.len() == t.n.len(),
        forall|q: int| 0 <= q < t.n.len() ==> t.n[q][0] == Val::Int(#[trigger] r.1@[q] as int),
        r.2@.len() == t.n.len(),
        forall|q: int| 0 <= q < t.n.len() ==> #[trigger] nreg_ok(r.2@[q], t, m, q),
{
    let mut nat_tab: Vec<usize> = Vec::new();
    let mut v: usize = 0;
    while v < 256
        invariant v <= 256, nat_tab@.len() == v, forall|x: int| 0 <= x < v ==> #[trigger] nat_tab@[x] == 0,
        decreases 256 - v,
    {
        nat_tab.push(0);
        v = v + 1;
    }
    let mut nkeys: Vec<i64> = Vec::new();
    let mut nreg: Vec<usize> = Vec::new();
    let nn = c.n.n;
    let mut q: usize = 0;
    while q < nn
        invariant
            cols_ok(*c, t), rname@ == m.rname, nn == c.n.n, nn == t.n.len(), q <= nn,
            nat_tab@.len() == 256,
            forall|x: int| 0 <= x < 256 ==> (#[trigger] nat_tab@[x] == 0 ==> forall|q2: int| 0 <= q2 < q ==> t.n[q2][0] != Val::Int(x)),
            forall|x: int| 0 <= x < 256 ==> (#[trigger] nat_tab@[x] > 0 ==> nat_tab@[x] - 1 < q && t.n[nat_tab@[x] - 1][0] == Val::Int(x)),
            nkeys@.len() == q,
            forall|q2: int| 0 <= q2 < q ==> t.n[q2][0] == Val::Int(#[trigger] nkeys@[q2] as int),
            nreg@.len() == q,
            forall|q2: int| 0 <= q2 < q ==> #[trigger] nreg_ok(nreg@[q2], t, m, q2),
        decreases nn - q,
    {
        assert(nat_row_ok(c.n, t.n[q as int], q as int));
        proof { lemma_grp_bound(c.n.n as int, c.n.bs as int, c.n.ng as int, q as int); }
        let g = grp(q, c.n.bs);
        let key: i64 = c.n.key_b[g] + c.n.key_c[q] as i64;
        nkeys.push(key);
        if 0 <= key && key < 256 && nat_tab[key as usize] == 0 {
            nat_tab.set(key as usize, q + 1);
        }
        let rk: i64 = c.n.reg_b[g] + c.n.reg_c[q] as i64;
        let mut found: usize = 0;
        let mut rr: usize = 0;
        while rr < c.r.n
            invariant
                cols_ok(*c, t), rname@ == m.rname, q < t.n.len(),
                t.n[q as int][2] == Val::Int(rk as int),
                rr <= c.r.n,
                found == 0 ==> forall|r2: int| 0 <= r2 < rr ==> !rmatch(t, m, q as int, r2),
                found > 0 ==> rmatch(t, m, q as int, found - 1),
            decreases c.r.n - rr,
        {
            if found == 0 {
                assert(reg_row_ok(c.r, t.r[rr as int], rr as int));
                proof { lemma_grp_bound(c.r.n as int, c.r.bs as int, c.r.ng as int, rr as int); }
                let key2: i64 = c.r.key_b[grp(rr, c.r.bs)] + c.r.key_c[rr] as i64;
                if key2 == rk {
                    assert(c.r.name_o@[rr as int] <= c.r.name_o@[rr + 1] && c.r.name_o@[rr + 1] <= c.r.name_y@.len());
                    let nm = text_slice(c.r.name_o, c.r.name_y, rr);
                    if slices_eq(nm, rname) {
                        found = rr + 1;
                    }
                }
            }
            rr = rr + 1;
        }
        nreg.push(found);
        proof {
            assert(nreg_ok(nreg@[q as int], t, m, q as int));
        }
        q = q + 1;
    }
    (nat_tab, nkeys, nreg)
}

pub fn copy_bools(v: &Vec<bool>) -> (r: Vec<bool>)
    ensures r@ == v@,
{
    let mut r: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
    }
    assert(r@ =~= v@);
    r
}

pub fn copy_usizes(v: &Vec<usize>) -> (r: Vec<usize>)
    ensures r@ == v@,
{
    let mut r: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
    }
    assert(r@ =~= v@);
    r
}

pub fn copy_i64s(v: &Vec<i64>) -> (r: Vec<i64>)
    ensures r@ == v@,
{
    let mut r: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
    }
    assert(r@ =~= v@);
    r
}

/// A copy of the lookups (one per worker task).
pub fn copy_lookups(lk: &Lookups) -> (r: Lookups)
    ensures r.like_ok@ == lk.like_ok@, r.nat_tab@ == lk.nat_tab@, r.nkeys@ == lk.nkeys@, r.nreg@ == lk.nreg@,
{
    Lookups { like_ok: copy_bools(&lk.like_ok), nat_tab: copy_usizes(&lk.nat_tab), nkeys: copy_i64s(&lk.nkeys), nreg: copy_usizes(&lk.nreg) }
}

// ------------------------------------------------------------------------------------------------ dense keys

proof fn lemma_dense_lower(f: spec_fn(int) -> int, n: int, j: int)
    requires 0 <= j < n, forall|r: int| 0 <= r < n - 1 ==> #[trigger] f(r) < f(r + 1),
    ensures f(j) >= f(0) + j,
    decreases j,
{
    if j > 0 {
        lemma_dense_lower(f, n, j - 1);
        assert(f(j - 1) < f((j - 1) + 1));
    }
}

proof fn lemma_dense_upper(f: spec_fn(int) -> int, n: int, j: int)
    requires 0 <= j < n, forall|r: int| 0 <= r < n - 1 ==> #[trigger] f(r) < f(r + 1),
    ensures f(j) <= f(n - 1) - (n - 1 - j),
    decreases n - j,
{
    if j < n - 1 {
        lemma_dense_upper(f, n, j + 1);
        assert(f(j) < f(j + 1));
    }
}

/// Strictly increasing integers from `f(0)` to `f(0) + n - 1` over `n` positions are `f(0) + j`.
pub proof fn lemma_dense(f: spec_fn(int) -> int, n: int)
    requires n >= 1, forall|r: int| 0 <= r < n - 1 ==> #[trigger] f(r) < f(r + 1), f(n - 1) == f(0) + n - 1,
    ensures forall|j: int| 0 <= j < n ==> #[trigger] f(j) == f(0) + j,
{
    assert forall|j: int| 0 <= j < n implies #[trigger] f(j) == f(0) + j by {
        lemma_dense_lower(f, n, j);
        lemma_dense_upper(f, n, j);
    }
}

/// The first supplier key, and whether every supplier row `j` has key `first + j`.
pub fn supp_dense(c: &Cols, Ghost(t): Ghost<Tabs>) -> (r: (i64, bool))
    requires cols_ok(*c, t), keys_unique(t),
    ensures r.1 ==> forall|j: int| 0 <= j < t.s.len() ==> #[trigger] t.s[j][0] == Val::Int(r.0 + j),
{
    let n = c.s.n;
    if n == 0 {
        return (0, false);
    }
    assert(supp_row_ok(c.s, t.s[0], 0));
    proof { lemma_grp_bound(n as int, c.s.bs as int, c.s.ng as int, 0); }
    let first: i64 = c.s.key_b[0] + c.s.key_c[0] as i64;
    if c.s.kind != 1 {
        return (first, false);
    }
    assert(supp_row_ok(c.s, t.s[n - 1], n - 1));
    proof { lemma_grp_bound(n as int, c.s.bs as int, c.s.ng as int, n - 1); }
    let last: i64 = c.s.key_b[grp(n - 1, c.s.bs)] + c.s.key_c[n - 1] as i64;
    if last as i128 == first as i128 + (n - 1) as i128 {
        proof {
            let b = c.s.bs as int;
            let f = |j: int| fv32(c.s.key_c@, c.s.key_b@, b, j);
            assert forall|r: int| 0 <= r < n - 1 implies #[trigger] f(r) < f(r + 1) by {
                assert(sorted_at(c.s.key_c@, c.s.key_b@, c.e32@, c.e64@, b, c.s.kind, r));
                assert(irow(c.s.kind, c.e32@, c.e64@, b, r) == r);
                assert(irow(c.s.kind, c.e32@, c.e64@, b, r + 1) == r + 1);
                assert(supp_row_ok(c.s, t.s[r], r) && supp_row_ok(c.s, t.s[r + 1], r + 1));
                if f(r) == f(r + 1) {
                    assert(t.s[r][0] == t.s[r + 1][0]);
                }
            }
            lemma_dense(f, n as int);
            assert forall|j: int| 0 <= j < t.s.len() implies #[trigger] t.s[j][0] == Val::Int(first + j) by {
                assert(supp_row_ok(c.s, t.s[j], j));
                assert(f(j) == f(0) + j);
            }
        }
        (first, true)
    } else {
        (first, false)
    }
}

/// The first part key, and whether every part row `i` has key `first + i`.
pub fn part_dense(c: &Cols, Ghost(t): Ghost<Tabs>) -> (r: (i64, bool))
    requires cols_ok(*c, t), keys_unique(t),
    ensures r.1 ==> forall|i: int| 0 <= i < t.p.len() ==> #[trigger] t.p[i][0] == Val::Int(r.0 + i),
{
    let n = c.p.n;
    if n == 0 {
        return (0, false);
    }
    assert(part_row_ok(c.p, t.p[0], 0));
    proof { lemma_grp_bound(n as int, c.p.bs as int, c.p.ng as int, 0); }
    let first: i64 = c.p.key_b[0] + c.p.key_c[0] as i64;
    if c.p.kind != 1 {
        return (first, false);
    }
    assert(part_row_ok(c.p, t.p[n - 1], n - 1));
    proof { lemma_grp_bound(n as int, c.p.bs as int, c.p.ng as int, n - 1); }
    let last: i64 = c.p.key_b[grp(n - 1, c.p.bs)] + c.p.key_c[n - 1] as i64;
    if last as i128 == first as i128 + (n - 1) as i128 {
        proof {
            let b = c.p.bs as int;
            let f = |j: int| fv32(c.p.key_c@, c.p.key_b@, b, j);
            assert forall|r: int| 0 <= r < n - 1 implies #[trigger] f(r) < f(r + 1) by {
                assert(fv32(c.p.key_c@, c.p.key_b@, b, r) <= fv32(c.p.key_c@, c.p.key_b@, b, r + 1));
                assert(part_row_ok(c.p, t.p[r], r) && part_row_ok(c.p, t.p[r + 1], r + 1));
                if f(r) == f(r + 1) {
                    assert(t.p[r][0] == t.p[r + 1][0]);
                }
            }
            lemma_dense(f, n as int);
            assert forall|i: int| 0 <= i < t.p.len() implies #[trigger] t.p[i][0] == Val::Int(first + i) by {
                assert(part_row_ok(c.p, t.p[i], i));
                assert(f(i) == f(0) + i);
            }
        }
        (first, true)
    } else {
        (first, false)
    }
}

} // verus!
