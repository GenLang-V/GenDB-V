//! Per-call preparation on the calling thread: `p_type LIKE $2` per p_type dictionary entry (`like_table`), the
//! first part row whose LIKE fails (`first_like_error`), `p_brand <> $1` per brand entry (`brand_table`), the
//! distinct sizes of the IN list in ascending order (`size_list`) and the dense key check of supplier
//! (`supp_dense`: sorted unique keys whose last key is `first + n - 1` are exactly `first + r`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::chars::chars;
use crate::spec::fns::like::*;
use crate::exec::chars::{chars_exec, view_chars};
use crate::exec::fns::like::{like_tokens_exec, like_mt_exec, view_toks};
use crate::stores::suppliers::interface::common::keyidx as sk;
use crate::stores::custpart::interface::common::keyidx as pk;
use vstd::slice::slice_to_vec;
use super::tables::*;
use super::model::{skey, pkey};
use super::sqlq::{like_res, like_true, lemma_like_shape, esc};

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

/// Text value `e` of a dictionary as a slice.
fn dict_text<'a>(o: &[u64], y: &'a [u8], e: usize) -> (r: &'a [u8])
    requires e + 1 < o@.len(), o@[e as int] <= o@[e + 1] <= y@.len(),
    ensures r@ == txt(o@, y@, e as int),
{
    let yl = y.len();
    let a = o[e] as usize;
    let b = o[e + 1] as usize;
    let r = vstd::slice::slice_subrange(y, a, b);
    r
}

// ------------------------------------------------------------------------------------------------ LIKE

/// `LIKE $2` on p_type dictionary entry `e`.
pub open spec fn like_entry(p: PCols, pat: Seq<u8>, e: int) -> Result<Val, SqlError> {
    like_res(Val::Text(txt(p.type_o@, p.type_y@, e)), pat)
}

pub open spec fn err_ok(x: Option<SqlError>, p: PCols, pat: Seq<u8>, e: int) -> bool {
    match x {
        Some(err) => like_entry(p, pat, e) == Err::<Val, SqlError>(err),
        None => like_entry(p, pat, e) is Ok,
    }
}

/// The LIKE outcome of every p_type dictionary entry: true/false, its error, and whether any entry fails.
pub fn like_table(p: &PCols, pat: &[u8]) -> (r: (Vec<bool>, Vec<Option<SqlError>>, bool))
    requires dict_ok(p.type_o@, p.type_y@),
    ensures
        r.0@.len() == p.type_o@.len() - 1,
        r.1@.len() == p.type_o@.len() - 1,
        forall|e: int| 0 <= e < r.0@.len() ==> #[trigger] r.0@[e] == like_true(Val::Text(txt(p.type_o@, p.type_y@, e)), pat@),
        forall|e: int| 0 <= e < r.1@.len() ==> #[trigger] err_ok(r.1@[e], *p, pat@, e),
        !r.2 ==> forall|e: int| 0 <= e < r.1@.len() ==> #[trigger] r.1@[e] is None,
{
    let nd = p.type_o.len() - 1;
    let pv = slice_to_vec(pat);
    let pc = chars_exec(&pv);
    let mut ev: Vec<u8> = Vec::new();
    ev.push(92u8);
    proof { assert(ev@ =~= esc()); }
    let e: Option<Vec<u8>> = Some(ev);
    let toks = like_tokens_exec(&pc, &e);
    let ghost tk = like_tokens(chars(pat@), Some(esc()), 0);
    assert(view_toks(toks@) == tk);
    let mut ok: Vec<bool> = Vec::new();
    let mut errs: Vec<Option<SqlError>> = Vec::new();
    let mut any = false;
    let mut k: usize = 0;
    while k < nd
        invariant
            dict_ok(p.type_o@, p.type_y@), nd == p.type_o@.len() - 1, k <= nd,
            view_toks(toks@) == tk, tk == like_tokens(chars(pat@), Some(esc()), 0),
            ok@.len() == k, errs@.len() == k,
            forall|x: int| 0 <= x < k ==> #[trigger] ok@[x] == like_true(Val::Text(txt(p.type_o@, p.type_y@, x)), pat@),
            forall|x: int| 0 <= x < k ==> #[trigger] err_ok(errs@[x], *p, pat@, x),
            !any ==> forall|x: int| 0 <= x < k ==> #[trigger] errs@[x] is None,
        decreases nd - k,
    {
        assert(p.type_o@[k as int] <= p.type_o@[k + 1] && p.type_o@[k + 1] <= p.type_y@.len());
        let s = dict_text(p.type_o, p.type_y, k);
        let sv = slice_to_vec(s);
        let tc = chars_exec(&sv);
        let ghost sb = txt(p.type_o@, p.type_y@, k as int);
        assert(sv@ == sb);
        proof { lemma_like_shape(sb, pat@); }
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
        k = k + 1;
    }
    (ok, errs, any)
}

/// No part row's `p_type LIKE $2` fails.
pub open spec fn like_rows_ok(p: PCols, rows: Seq<Row>, pat: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> #[trigger] like_res(rows[i][4], pat) is Ok
}

/// The first part row whose LIKE fails, with its error; `None` when no part row's LIKE fails.
pub fn first_like_error(p: &PCols, errs: &Vec<Option<SqlError>>, Ghost(rows): Ghost<Seq<Row>>, Ghost(pat): Ghost<Seq<u8>>)
    -> (r: Option<(usize, SqlError)>)
    requires
        pcols_ok(*p, rows, Seq::<u32>::empty(), Seq::<u64>::empty()),
        errs@.len() == p.type_o@.len() - 1,
        forall|e: int| 0 <= e < errs@.len() ==> #[trigger] err_ok(errs@[e], *p, pat, e),
    ensures
        r matches Some((i, err)) ==> i < rows.len() && like_res(rows[i as int][4], pat) == Err::<Val, SqlError>(err)
            && forall|i2: int| 0 <= i2 < i ==> #[trigger] like_res(rows[i2][4], pat) is Ok,
        r is None ==> like_rows_ok(*p, rows, pat),
{
    let mut i: usize = 0;
    while i < p.n
        invariant
            pcols_ok(*p, rows, Seq::<u32>::empty(), Seq::<u64>::empty()),
            errs@.len() == p.type_o@.len() - 1,
            forall|e: int| 0 <= e < errs@.len() ==> #[trigger] err_ok(errs@[e], *p, pat, e),
            i <= p.n,
            forall|i2: int| 0 <= i2 < i ==> #[trigger] like_res(rows[i2][4], pat) is Ok,
        decreases p.n - i,
    {
        assert(part_row_ok(*p, rows[i as int], i as int));
        proof { lemma_grp_bound(p.n as int, p.bs as int, p.ng as int, i as int); }
        let g = i / p.bs;
        let e = (p.type_b[g] + p.type_c[i] as u64) as usize;
        assert(err_ok(errs@[e as int], *p, pat, e as int));
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
pub proof fn lemma_like_all_from_entries(p: PCols, rows: Seq<Row>, pat: Seq<u8>, errs: Seq<Option<SqlError>>)
    requires
        pcols_ok(p, rows, Seq::<u32>::empty(), Seq::<u64>::empty()),
        errs.len() == p.type_o@.len() - 1,
        forall|e: int| 0 <= e < errs.len() ==> #[trigger] err_ok(errs[e], p, pat, e),
        forall|e: int| 0 <= e < errs.len() ==> #[trigger] errs[e] is None,
    ensures like_rows_ok(p, rows, pat),
{
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] like_res(rows[i][4], pat) is Ok by {
        assert(part_row_ok(p, rows[i], i));
        let e = fu8(p.type_c@, p.type_b@, p.bs as int, i);
        assert(err_ok(errs[e], p, pat, e));
        assert(errs[e] is None);
    }
}

// ------------------------------------------------------------------------------------------------ brand

/// `p_brand <> $1` per brand dictionary entry.
pub fn brand_table(p: &PCols, b1: &[u8]) -> (r: Vec<bool>)
    requires dict_ok(p.brand_o@, p.brand_y@),
    ensures
        r@.len() == p.brand_o@.len() - 1,
        forall|e: int| 0 <= e < r@.len() ==> #[trigger] r@[e] == (txt(p.brand_o@, p.brand_y@, e) != b1@),
{
    let nd = p.brand_o.len() - 1;
    let mut ok: Vec<bool> = Vec::new();
    let mut e: usize = 0;
    while e < nd
        invariant
            dict_ok(p.brand_o@, p.brand_y@), nd == p.brand_o@.len() - 1, e <= nd,
            ok@.len() == e,
            forall|x: int| 0 <= x < e ==> #[trigger] ok@[x] == (txt(p.brand_o@, p.brand_y@, x) != b1@),
        decreases nd - e,
    {
        assert(p.brand_o@[e as int] <= p.brand_o@[e + 1] && p.brand_o@[e + 1] <= p.brand_y@.len());
        let s = dict_text(p.brand_o, p.brand_y, e);
        ok.push(!slices_eq(s, b1));
        e = e + 1;
    }
    ok
}

// ------------------------------------------------------------------------------------------------ sizes

/// The number of the eight values above `last`.
pub open spec fn cnt_gt(v: Seq<i64>, k: int, last: int) -> nat
    decreases k,
{
    if k <= 0 { 0 } else { cnt_gt(v, k - 1, last) + if v[k - 1] > last { 1nat } else { 0nat } }
}

proof fn lemma_cnt_gt_less(v: Seq<i64>, k: int, a: int, b: int, w: int)
    requires 0 <= w < k, a < v[w] <= b, a <= b,
    ensures cnt_gt(v, k, b) < cnt_gt(v, k, a),
    decreases k,
{
    if k - 1 == w {
        lemma_cnt_gt_le(v, k - 1, a, b);
    } else {
        lemma_cnt_gt_less(v, k - 1, a, b, w);
    }
}

proof fn lemma_cnt_gt_bound(v: Seq<i64>, k: int, a: int)
    requires k >= 0,
    ensures cnt_gt(v, k, a) <= k,
    decreases k,
{
    if k > 0 {
        lemma_cnt_gt_bound(v, k - 1, a);
    }
}

proof fn lemma_cnt_gt_le(v: Seq<i64>, k: int, a: int, b: int)
    requires a <= b,
    ensures cnt_gt(v, k, b) <= cnt_gt(v, k, a),
    decreases k,
{
    if k > 0 {
        lemma_cnt_gt_le(v, k - 1, a, b);
    }
}

/// The distinct values of `v` (8 values), strictly ascending.
pub fn size_list(v: [i64; 8]) -> (r: Vec<i64>)
    ensures
        r@.len() <= 8,
        forall|a: int, b: int| 0 <= a < b < r@.len() ==> #[trigger] r@[a] < #[trigger] r@[b],
        forall|x: i64| #[trigger] r@.contains(x) <==> v@.contains(x),
{
    let mut out: Vec<i64> = Vec::new();
    let mut last: i128 = i64::MIN as i128 - 1;
    let mut more = true;
    proof {
        lemma_cnt_gt_bound(v@, 8, last as int);
    }
    while more
        invariant
            v@.len() == 8,
            i64::MIN as i128 - 1 <= last <= i64::MAX,
            out@.len() <= 8 - cnt_gt(v@, 8, last as int),
            forall|a: int, b: int| 0 <= a < b < out@.len() ==> #[trigger] out@[a] < #[trigger] out@[b],
            forall|a: int| 0 <= a < out@.len() ==> #[trigger] out@[a] <= last,
            forall|a: int| 0 <= a < out@.len() ==> v@.contains(#[trigger] out@[a]),
            forall|k: int| 0 <= k < 8 && #[trigger] v@[k] <= last ==> out@.contains(v@[k]),
            !more ==> forall|k: int| 0 <= k < 8 ==> #[trigger] v@[k] <= last,
        decreases cnt_gt(v@, 8, last as int), if more { 1int } else { 0int },
    {
        let mut best: i128 = i64::MAX as i128 + 1;
        let mut w: usize = 8;
        let mut k: usize = 0;
        while k < 8
            invariant
                v@.len() == 8,
                k <= 8,
                last < best <= i64::MAX as i128 + 1,
                w < 8 ==> v@[w as int] == best,
                w >= 8 ==> best == i64::MAX as i128 + 1,
                forall|k2: int| 0 <= k2 < k && #[trigger] v@[k2] > last ==> best <= v@[k2],
            decreases 8 - k,
        {
            let x = v[k] as i128;
            if x > last && x < best {
                best = x;
                w = k;
            }
            k = k + 1;
        }
        if w >= 8 {
            more = false;
            proof {
                assert forall|k2: int| 0 <= k2 < 8 implies #[trigger] v@[k2] <= last by {
                    if v@[k2] > last {
                        assert(best <= v@[k2]);
                    }
                }
            }
        } else {
            let bv = best as i64;
            proof {
                lemma_cnt_gt_less(v@, 8, last as int, best as int, w as int);
                lemma_cnt_gt_le(v@, 8, last as int, best as int);
                assert(v@[w as int] == bv);
            }
            let ghost old_out = out@;
            out.push(bv);
            proof {
                assert forall|k2: int| 0 <= k2 < 8 && #[trigger] v@[k2] <= best implies out@.contains(v@[k2]) by {
                    if v@[k2] <= last {
                        let a = choose|a: int| 0 <= a < old_out.len() && old_out[a] == v@[k2];
                        assert(out@[a] == v@[k2]);
                    } else {
                        assert(best <= v@[k2]);
                        assert(out@[old_out.len() as int] == v@[k2]);
                    }
                }
                assert(v@.contains(v@[w as int]));
            }
            last = best;
        }
    }
    proof {
        assert forall|x: i64| #[trigger] out@.contains(x) <==> v@.contains(x) by {
            if v@.contains(x) {
                let k = choose|k: int| 0 <= k < 8 && v@[k] == x;
                assert(v@[k] <= last);
            }
        }
    }
    out
}

// ------------------------------------------------------------------------------------------------ dense keys

proof fn lemma_dense_lower(f: spec_fn(int) -> int, n: int, j: int)
    requires 0 <= j < n, forall|r: int| 0 <= r < n - 1 ==> #[trigger] f(r) < f(r + 1),
    ensures f(j) >= f(0) + j,
    decreases j,
{
    if j > 0 {
        lemma_dense_lower(f, n, j - 1);
        assert(f(j - 1) < f(j - 1 + 1));
    }
}

proof fn lemma_dense_upper(f: spec_fn(int) -> int, n: int, j: int)
    requires 0 <= j < n, forall|r: int| 0 <= r < n - 1 ==> #[trigger] f(r) < f(r + 1),
    ensures f(j) <= f(n - 1) - (n - 1 - j),
    decreases n - 1 - j,
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

/// Sorted unique keys strictly increase.
proof fn lemma_strict(s: SCols, e32: Seq<u32>, e64: Seq<u64>)
    requires
        s.kind == 1,
        sk::keyidx_ok(s.key_c@, s.key_b@, e32, e64, s.bs as int, s.kind, s.n as int),
        forall|r1: int, r2: int| 0 <= r1 < s.n && 0 <= r2 < s.n && #[trigger] skey(s, r1) == #[trigger] skey(s, r2) ==> r1 == r2,
    ensures forall|r: int| 0 <= r < s.n - 1 ==> #[trigger] skey(s, r) < skey(s, r + 1),
{
    assert forall|r: int| 0 <= r < s.n - 1 implies #[trigger] skey(s, r) < skey(s, r + 1) by {
        assert(sk::sorted_at(s.key_c@, s.key_b@, e32, e64, s.bs as int, s.kind, r));
        assert(sk::irow(s.kind, e32, e64, s.bs as int, r) == r);
        assert(sk::irow(s.kind, e32, e64, s.bs as int, r + 1) == r + 1);
        assert(skey(s, r) <= skey(s, r + 1));
        if skey(s, r) == skey(s, r + 1) {
            assert(r == r + 1);
        }
    }
}

/// Dense keys from the strict order and the last key.
proof fn lemma_supp_dense(s: SCols, first: int)
    requires
        s.n >= 1,
        forall|r: int| 0 <= r < s.n - 1 ==> #[trigger] skey(s, r) < skey(s, r + 1),
        skey(s, 0) == first,
        skey(s, s.n - 1) == first + s.n - 1,
    ensures forall|j: int| 0 <= j < s.n ==> #[trigger] skey(s, j) == first + j,
{
    let f = |j: int| skey(s, j);
    assert forall|r: int| 0 <= r < s.n - 1 implies #[trigger] f(r) < f(r + 1) by {
        assert(skey(s, r) < skey(s, r + 1));
    }
    lemma_dense(f, s.n as int);
    assert forall|j: int| 0 <= j < s.n implies #[trigger] skey(s, j) == first + j by {
        assert(f(j) == f(0) + j);
    }
}

/// The first supplier key, and whether every supplier row `r` has key `first + r` (sorted unique keys, checked
/// first and last keys).
pub fn supp_dense(s: &SCols, Ghost(e32): Ghost<Seq<u32>>, Ghost(e64): Ghost<Seq<u64>>) -> (r: (i64, bool))
    requires
        frame_ok(s.n as int, s.bs as int, s.ng as int),
        s.key_c@.len() == s.n, s.key_b@.len() == s.ng,
        sk::keyidx_ok(s.key_c@, s.key_b@, e32, e64, s.bs as int, s.kind, s.n as int),
        forall|r: int| 0 <= r < s.n ==> #[trigger] i64r(skey(*s, r)),
        forall|r1: int, r2: int| 0 <= r1 < s.n && 0 <= r2 < s.n && #[trigger] skey(*s, r1) == #[trigger] skey(*s, r2) ==> r1 == r2,
    ensures
        r.1 ==> forall|j: int| 0 <= j < s.n ==> #[trigger] skey(*s, j) == r.0 + j,
{
    let n = s.n;
    if n == 0 {
        return (0, false);
    }
    proof {
        lemma_grp_bound(n as int, s.bs as int, s.ng as int, 0);
        assert(i64r(skey(*s, 0)));
        vstd::arithmetic::div_mod::lemma_basic_div(0, s.bs as int);
    }
    let first: i64 = s.key_b[0] + s.key_c[0] as i64;
    if s.kind != 1 {
        return (first, false);
    }
    proof {
        lemma_grp_bound(n as int, s.bs as int, s.ng as int, n - 1);
        assert(i64r(skey(*s, n - 1)));
    }
    let last: i64 = s.key_b[(n - 1) / s.bs] + s.key_c[n - 1] as i64;
    if last as i128 == first as i128 + (n - 1) as i128 {
        proof {
            lemma_strict(*s, e32, e64);
            lemma_supp_dense(*s, first as int);
        }
        (first, true)
    } else {
        (first, false)
    }
}


/// Sorted unique part keys strictly increase.
proof fn lemma_pstrict(p: PCols, e32: Seq<u32>, e64: Seq<u64>)
    requires
        p.kind == 1,
        pk::keyidx_ok(p.key_c@, p.key_b@, e32, e64, p.bs as int, p.kind, p.n as int),
        forall|j1: int, j2: int| 0 <= j1 < p.n && 0 <= j2 < p.n && #[trigger] pkey(p, j1) == #[trigger] pkey(p, j2) ==> j1 == j2,
    ensures forall|j: int| 0 <= j < p.n - 1 ==> #[trigger] pkey(p, j) < pkey(p, j + 1),
{
    assert forall|j: int| 0 <= j < p.n - 1 implies #[trigger] pkey(p, j) < pkey(p, j + 1) by {
        assert(pk::sorted_at(p.key_c@, p.key_b@, e32, e64, p.bs as int, p.kind, j));
        assert(pk::irow(p.kind, e32, e64, p.bs as int, j) == j);
        assert(pk::irow(p.kind, e32, e64, p.bs as int, j + 1) == j + 1);
        assert(pkey(p, j) <= pkey(p, j + 1));
        if pkey(p, j) == pkey(p, j + 1) {
            assert(j == j + 1);
        }
    }
}

/// The first part key, and whether every part row `j` has key `first + j` (sorted unique keys, checked first and
/// last keys).
pub fn part_dense(p: &PCols, Ghost(e32): Ghost<Seq<u32>>, Ghost(e64): Ghost<Seq<u64>>) -> (r: (i64, bool))
    requires
        frame_ok(p.n as int, p.bs as int, p.ng as int),
        p.key_c@.len() == p.n, p.key_b@.len() == p.ng,
        pk::keyidx_ok(p.key_c@, p.key_b@, e32, e64, p.bs as int, p.kind, p.n as int),
        forall|j: int| 0 <= j < p.n ==> #[trigger] i64r(pkey(*p, j)),
        forall|j1: int, j2: int| 0 <= j1 < p.n && 0 <= j2 < p.n && #[trigger] pkey(*p, j1) == #[trigger] pkey(*p, j2) ==> j1 == j2,
    ensures
        r.1 ==> forall|j: int| 0 <= j < p.n ==> #[trigger] pkey(*p, j) == r.0 + j,
{
    let n = p.n;
    if n == 0 {
        return (0, false);
    }
    proof {
        lemma_grp_bound(n as int, p.bs as int, p.ng as int, 0);
        assert(i64r(pkey(*p, 0)));
        vstd::arithmetic::div_mod::lemma_basic_div(0, p.bs as int);
    }
    let first: i64 = p.key_b[0] + p.key_c[0] as i64;
    if p.kind != 1 {
        return (first, false);
    }
    proof {
        lemma_grp_bound(n as int, p.bs as int, p.ng as int, n - 1);
        assert(i64r(pkey(*p, n - 1)));
    }
    let last: i64 = p.key_b[(n - 1) / p.bs] + p.key_c[n - 1] as i64;
    if last as i128 == first as i128 + (n - 1) as i128 {
        proof {
            lemma_pstrict(*p, e32, e64);
            let f = |j: int| pkey(*p, j);
            assert forall|j: int| 0 <= j < n - 1 implies #[trigger] f(j) < f(j + 1) by {
                assert(pkey(*p, j) < pkey(*p, j + 1));
            }
            lemma_dense(f, n as int);
            assert forall|j: int| 0 <= j < n implies #[trigger] pkey(*p, j) == first + j by {
                assert(f(j) == f(0) + j);
            }
        }
        (first, true)
    } else {
        (first, false)
    }
}
} // verus!
