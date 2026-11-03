//! The general path, for data the fast path does not handle (another partsupp layout, dictionary misses, other
//! patterns): serial and quadratic, with no assumption beyond the declared keys.
//!
//! 1. per part row, the part conditions (`part_flags`; the first `LIKE` error is the answer);
//! 2. per partsupp row `c`, its part row `pa[c]` (by key) and whether `(c, pa[c])` qualifies (`ok[c]`, `join_ok`);
//! 3. per qualifying row, its leader `ld[c]`: the first qualifying row with the same group key (`lead_ok`);
//! 4. per leader, the number of distinct supplier keys of the rows it leads (`cnt`, `sset`);
//! 5. one output row per leader, sorted by the framework's verified insertion sort (`sort_rows_exec`).
use vstd::prelude::*;
use vstd::set_lib::set_int_range;
use crate::spec::value::*;
use crate::spec::limits::int8_max;
use crate::spec::ast::{Literal, OrderKey};
use crate::spec::order::*;
use crate::query::param_domain;
use crate::exec::value::*;
use crate::exec::ast::EOrderKey;
use crate::exec::fns::like::like_value_exec;
use crate::exec::relational::schema::view_rows;
use crate::exec::relational::order::{sort_rows_exec, view_keys};
use crate::bridge::order::{all_keys_ok, keys_ok as order_keys_ok, key_ok, lemma_sort_rows};
use crate::gendb_params::Params;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::{Answer, bound_db, outcome_ok};
use crate::query::query_spec_at;
use crate::agent::model::*;
use crate::agent::cols::*;
use crate::agent::sem_ast::*;
use crate::agent::sem_sub::*;
use crate::agent::sem_row::*;
use crate::agent::sem_result::*;
use crate::agent::parts::{sizes_ok, size_pos};
use crate::agent::supp::{copy_bytes, has_key};
use crate::agent::common::text_dict::bytes_eq_range;

verus! {

// ------------------------------------------------------------------------------------------------ part rows

/// `p_type LIKE $2` of part row `a` (calling thread).
fn type_like(c: &Cols, a: usize, pat: &EVal, esc: &EVal, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Result<EVal, SqlError>)
    requires cols_ok(*c, sv), a < c.np, pat@ == Val::Text(pat_lit(ps)), esc@ == Val::Text(backslash()),
    ensures view_result(r) == type_res(sv, ps, a as int),
{
    let (x, y) = trange(&c.ptype, a, Ghost(c.np as int));
    let v = copy_bytes(c.ptype.bytes, x, y);
    let s = EVal::Text(v);
    proof { assert(s@ == Val::Text(p_type(sv, a as int))); }
    like_value_exec(&s, pat, esc)
}

/// The part conditions of every part row, or the first part row whose `LIKE` fails and its error.
fn part_flags(c: &Cols, params: &Params, szl: &Vec<i64>, Ghost(sv): Ghost<StoresView>)
    -> (r: Result<Vec<bool>, (usize, SqlError)>)
    requires cols_ok(*c, sv), param_domain(params@), sizes_ok(szl@, params@),
    ensures
        r matches Ok(f) ==> f@.len() == c.np
            && (forall|a: int| 0 <= a < c.np ==> #[trigger] f@[a] == part_ok(sv, params@, a))
            && (forall|a: int| 0 <= a < c.np ==> #[trigger] type_res(sv, params@, a) is Ok),
        r matches Err((a0, e)) ==> a0 < c.np && type_res(sv, params@, a0 as int) == Err::<Val, SqlError>(e)
            && (forall|a: int| 0 <= a < a0 ==> #[trigger] type_res(sv, params@, a) is Ok),
{
    let ghost ps = params@;
    proof { lemma_params(ps); }
    let pat = EVal::Text(copy_bytes(params.p1, 0, params.p1.len()));
    let esc = EVal::Text(vec![92u8]);
    proof {
        assert(params.p1@.subrange(0, params.p1@.len() as int) =~= pat_lit(ps));
        assert(esc@ == Val::Text(backslash())) by {
            if let EVal::Text(v) = esc { assert(v@ =~= backslash()); }
        }
    }
    let blen = params.p0.len();
    let mut f: Vec<bool> = Vec::new();
    let mut a: usize = 0;
    while a < c.np
        invariant
            cols_ok(*c, sv), ps == params@, param_domain(ps), sizes_ok(szl@, ps), a <= c.np, f@.len() == a,
            blen == params.p0@.len(), params.p0@ == brand_lit(ps),
            pat@ == Val::Text(pat_lit(ps)), esc@ == Val::Text(backslash()),
            forall|x: int| 0 <= x < a ==> #[trigger] f@[x] == part_ok(sv, ps, x),
            forall|x: int| 0 <= x < a ==> #[trigger] type_res(sv, ps, x) is Ok,
        decreases c.np - a,
    {
        let t = type_like(c, a, &pat, &esc, Ghost(sv), Ghost(ps));
        let hit = match t {
            Ok(EVal::Bool(b)) => b,
            Ok(_) => false,
            Err(e) => {
                return Err((a, e));
            },
        };
        proof { assert(hit == type_hit(sv, ps, a as int)); }
        let (x, y) = trange(&c.brand, a, Ghost(c.np as int));
        let same = bytes_eq_range(c.brand.bytes, x, y, params.p0, 0, blen);
        proof {
            assert(params.p0@.subrange(0, blen as int) =~= params.p0@);
            assert(same == (p_brand(sv, a as int) == brand_lit(ps)));
        }
        let s = c.p_size[a];
        let j = size_pos(szl, s);
        proof {
            assert(size_match(ps, 8, s as int) == (j < szl@.len()));
        }
        f.push(!same && !hit && j < szl.len());
        a = a + 1;
    }
    Ok(f)
}

// ------------------------------------------------------------------------------------------------ the join

/// The part row with key `k`, or `np` when there is none.
fn find_part(c: &Cols, k: i64, Ghost(sv): Ghost<StoresView>) -> (a: usize)
    requires cols_ok(*c, sv),
    ensures
        a <= c.np,
        a < c.np ==> p_keys(sv)[a as int] == k,
        a == c.np ==> forall|x: int| 0 <= x < c.np ==> #[trigger] p_keys(sv)[x] != k,
{
    let mut a: usize = 0;
    while a < c.np
        invariant cols_ok(*c, sv), a <= c.np, forall|x: int| 0 <= x < a ==> #[trigger] p_keys(sv)[x] != k,
        decreases c.np - a,
    {
        if c.p_key[a] == k {
            return a;
        }
        a = a + 1;
    }
    a
}

/// Whether `v` holds `k`.
fn has_key_exec(v: &Vec<i64>, k: i64) -> (r: bool)
    ensures r == has_key(v@, k as int),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), forall|x: int| 0 <= x < i ==> v@[x] != k,
        decreases v@.len() - i,
    {
        if v[i] == k {
            return true;
        }
        i = i + 1;
    }
    false
}

/// `pa[c]` is the part row of partsupp row `c` (`np` when none), `ok[c]` whether the pair qualifies.
pub open spec fn join_ok(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>) -> bool {
    &&& pa.len() == ps_n(sv) && ok.len() == ps_n(sv)
    &&& forall|c: int| 0 <= c < ps_n(sv) ==> #[trigger] pa[c] <= part_n(sv)
        && (pa[c] < part_n(sv) ==> p_keys(sv)[pa[c] as int] == ps_pkeys(sv)[c])
        && (pa[c] == part_n(sv) ==> forall|a: int| 0 <= a < part_n(sv) ==> #[trigger] p_keys(sv)[a] != ps_pkeys(sv)[c])
    &&& forall|c: int| 0 <= c < ps_n(sv) ==> #[trigger] ok[c]
        == (pa[c] < part_n(sv) && part_ok(sv, ps, pa[c] as int) && !excluded(sv, ps_skeys(sv)[c] as int))
}

/// The join of partsupp and part with the conditions.
fn join_rows(c: &Cols, flags: &Vec<bool>, ekeys: &Vec<i64>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: (Vec<usize>, Vec<bool>))
    requires
        cols_ok(*c, sv), flags@.len() == c.np, forall|a: int| 0 <= a < c.np ==> #[trigger] flags@[a] == part_ok(sv, ps, a),
        forall|k: int| #[trigger] has_key(ekeys@, k) <==> excluded(sv, k),
    ensures join_ok(sv, ps, r.0@, r.1@),
{
    let mut pa: Vec<usize> = Vec::new();
    let mut ok: Vec<bool> = Vec::new();
    let mut q: usize = 0;
    while q < c.nq
        invariant
            cols_ok(*c, sv), flags@.len() == c.np, forall|a: int| 0 <= a < c.np ==> #[trigger] flags@[a] == part_ok(sv, ps, a),
            forall|k: int| #[trigger] has_key(ekeys@, k) <==> excluded(sv, k),
            q <= c.nq, pa@.len() == q, ok@.len() == q,
            forall|x: int| 0 <= x < q ==> #[trigger] pa@[x] <= part_n(sv)
                && (pa@[x] < part_n(sv) ==> p_keys(sv)[pa@[x] as int] == ps_pkeys(sv)[x])
                && (pa@[x] == part_n(sv) ==> forall|a: int| 0 <= a < part_n(sv) ==> #[trigger] p_keys(sv)[a] != ps_pkeys(sv)[x]),
            forall|x: int| 0 <= x < q ==> #[trigger] ok@[x]
                == (pa@[x] < part_n(sv) && part_ok(sv, ps, pa@[x] as int) && !excluded(sv, ps_skeys(sv)[x] as int)),
        decreases c.nq - q,
    {
        let a = find_part(c, c.ps_pk[q], Ghost(sv));
        let good = a < c.np && flags[a] && !has_key_exec(ekeys, c.ps_sk[q]);
        pa.push(a);
        ok.push(good);
        q = q + 1;
    }
    (pa, ok)
}

/// With unique part keys, `(c, a)` qualifies exactly when `ok[c]` and `a` is `pa[c]`.
pub proof fn lemma_qual_iff(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>, c: int, a: int)
    requires keys_ok(sv), join_ok(sv, ps, pa, ok), 0 <= c < ps_n(sv), 0 <= a < part_n(sv),
    ensures qual(sv, ps, c, a) <==> (ok[c] && a == pa[c] as int),
{
    if qual(sv, ps, c, a) {
        assert(p_keys(sv)[a] == ps_pkeys(sv)[c]);
        assert(pa[c] < part_n(sv));
        if pa[c] as int != a {
            assert(p_keys(sv)[pa[c] as int] != p_keys(sv)[a]);
        }
    }
}

// ------------------------------------------------------------------------------------------------ leaders

/// The group key of partsupp row `c` (of its part row).
pub open spec fn kr(sv: StoresView, pa: Seq<usize>, c: int) -> Row {
    krow(sv, pa[c] as int)
}

/// No qualifying row below `m` has key `k`.
pub open spec fn none_before(sv: StoresView, pa: Seq<usize>, ok: Seq<bool>, m: int, k: Row) -> bool {
    forall|x: int| 0 <= x < m && #[trigger] ok[x] ==> kr(sv, pa, x) != k
}

/// The leader of every qualifying row below `n` is the first qualifying row with its key.
pub open spec fn lead_ok(sv: StoresView, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, n: int) -> bool {
    &&& ld.len() >= n
    &&& forall|c: int| 0 <= c < n && #[trigger] ok[c] ==> ld[c] <= c && ok[ld[c] as int]
        && kr(sv, pa, ld[c] as int) == kr(sv, pa, c) && none_before(sv, pa, ok, ld[c] as int, kr(sv, pa, c))
}

/// Part rows `a1`, `a2` have the same group key.
fn same_key(c: &Cols, a1: usize, a2: usize, Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires cols_ok(*c, sv), a1 < c.np, a2 < c.np,
    ensures r == (krow(sv, a1 as int) == krow(sv, a2 as int)),
{
    let ghost (k1, k2) = (krow(sv, a1 as int), krow(sv, a2 as int));
    if c.p_size[a1] != c.p_size[a2] {
        proof { assert(k1[2] != k2[2]); }
        return false;
    }
    let (x1, y1) = trange(&c.brand, a1, Ghost(c.np as int));
    let (x2, y2) = trange(&c.brand, a2, Ghost(c.np as int));
    if !bytes_eq_range(c.brand.bytes, x1, y1, c.brand.bytes, x2, y2) {
        proof { assert(k1[0] != k2[0]); }
        return false;
    }
    let (x1, y1) = trange(&c.ptype, a1, Ghost(c.np as int));
    let (x2, y2) = trange(&c.ptype, a2, Ghost(c.np as int));
    if !bytes_eq_range(c.ptype.bytes, x1, y1, c.ptype.bytes, x2, y2) {
        proof { assert(k1[1] != k2[1]); }
        return false;
    }
    proof { assert(k1 =~= k2); }
    true
}

/// The first qualifying row below `q` with the key of row `q` (or `q`).
fn leader_of(c: &Cols, pa: &Vec<usize>, ok: &Vec<bool>, q: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: usize)
    requires cols_ok(*c, sv), join_ok(sv, ps, pa@, ok@), q < c.nq, ok@[q as int],
    ensures r <= q, ok@[r as int], kr(sv, pa@, r as int) == kr(sv, pa@, q as int),
        none_before(sv, pa@, ok@, r as int, kr(sv, pa@, q as int)),
{
    let ghost k = kr(sv, pa@, q as int);
    let mut x: usize = 0;
    while x < q
        invariant cols_ok(*c, sv), join_ok(sv, ps, pa@, ok@), q < c.nq, x <= q, ok@[q as int],
            k == kr(sv, pa@, q as int), none_before(sv, pa@, ok@, x as int, k),
        decreases q - x,
    {
        if ok[x] && same_key(c, pa[x], pa[q], Ghost(sv)) {
            return x;
        }
        proof {
            assert forall|y: int| 0 <= y < x + 1 && #[trigger] ok@[y] implies kr(sv, pa@, y) != k by {
                if y < x { assert(none_before(sv, pa@, ok@, x as int, k)); }
            }
        }
        x = x + 1;
    }
    q
}

/// The leader of every partsupp row (itself when it does not qualify).
fn leaders(c: &Cols, pa: &Vec<usize>, ok: &Vec<bool>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (ld: Vec<usize>)
    requires cols_ok(*c, sv), join_ok(sv, ps, pa@, ok@),
    ensures ld@.len() == c.nq, lead_ok(sv, pa@, ok@, ld@, c.nq as int), forall|x: int| 0 <= x < c.nq ==> #[trigger] ld@[x] <= x,
{
    let mut ld: Vec<usize> = Vec::new();
    let mut q: usize = 0;
    while q < c.nq
        invariant cols_ok(*c, sv), join_ok(sv, ps, pa@, ok@), q <= c.nq, ld@.len() == q, lead_ok(sv, pa@, ok@, ld@, q as int),
            forall|x: int| 0 <= x < q ==> #[trigger] ld@[x] <= x,
        decreases c.nq - q,
    {
        let l = if ok[q] { leader_of(c, pa, ok, q, Ghost(sv), Ghost(ps)) } else { q };
        let ghost ld0 = ld@;
        ld.push(l);
        proof {
            assert forall|x: int| 0 <= x < q + 1 && #[trigger] ok@[x] implies ld@[x] <= x && ok@[ld@[x] as int]
                && kr(sv, pa@, ld@[x] as int) == kr(sv, pa@, x) && none_before(sv, pa@, ok@, ld@[x] as int, kr(sv, pa@, x)) by {
                if x < q { assert(ld@[x] == ld0[x]); }
            }
            assert forall|x: int| 0 <= x < q + 1 implies #[trigger] ld@[x] <= x by {
                if x < q { assert(ld@[x] == ld0[x]); }
            }
        }
        q = q + 1;
    }
    ld
}

/// Two qualifying rows have the same leader exactly when they have the same key.
pub proof fn lemma_same_leader(sv: StoresView, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, n: int, c1: int, c2: int)
    requires lead_ok(sv, pa, ok, ld, n), 0 <= c1 < n, 0 <= c2 < n, ok[c1], ok[c2],
    ensures (ld[c1] == ld[c2]) <==> (kr(sv, pa, c1) == kr(sv, pa, c2)),
{
    let (l1, l2) = (ld[c1] as int, ld[c2] as int);
    if kr(sv, pa, c1) == kr(sv, pa, c2) {
        if l1 < l2 {
            assert(none_before(sv, pa, ok, l2, kr(sv, pa, c2)));
            assert(ok[l1]);
        } else if l2 < l1 {
            assert(none_before(sv, pa, ok, l1, kr(sv, pa, c1)));
            assert(ok[l2]);
        }
    }
}

// ------------------------------------------------------------------------------------------------ counts

/// The qualifying rows below `n` led by `l`.
pub open spec fn led(ok: Seq<bool>, ld: Seq<usize>, l: int, n: int) -> Set<int> {
    set_int_range(0, n).filter(|c: int| ok[c] && ld[c] as int == l)
}

/// The distinct supplier keys of the qualifying rows below `n` led by `l`.
pub open spec fn sset(sk: Seq<i64>, ok: Seq<bool>, ld: Seq<usize>, l: int, n: int) -> Set<Val> {
    led(ok, ld, l, n).map(|c: int| Val::Int(sk[c] as int))
}

/// Membership in `sset`.
proof fn lemma_sset_has(sk: Seq<i64>, ok: Seq<bool>, ld: Seq<usize>, l: int, n: int, x: Val)
    ensures sset(sk, ok, ld, l, n).contains(x) <==> exists|c: int| 0 <= c < n && ok[c] && ld[c] as int == l
        && Val::Int(#[trigger] sk[c] as int) == x,
{
    if exists|c: int| 0 <= c < n && ok[c] && ld[c] as int == l && Val::Int(#[trigger] sk[c] as int) == x {
        let c = choose|c: int| 0 <= c < n && ok[c] && ld[c] as int == l && Val::Int(#[trigger] sk[c] as int) == x;
        assert(led(ok, ld, l, n).contains(c));
    }
}

/// One more row: its key joins the set of its leader, the other sets stay.
proof fn lemma_sset_step(sk: Seq<i64>, ok: Seq<bool>, ld: Seq<usize>, l: int, n: int)
    requires 0 <= n,
    ensures sset(sk, ok, ld, l, n + 1) == if ok[n] && ld[n] as int == l {
        sset(sk, ok, ld, l, n).insert(Val::Int(sk[n] as int)) } else { sset(sk, ok, ld, l, n) },
{
    let s1 = sset(sk, ok, ld, l, n + 1);
    let s0 = sset(sk, ok, ld, l, n);
    let p = ok[n] && ld[n] as int == l;
    let t = if p { s0.insert(Val::Int(sk[n] as int)) } else { s0 };
    assert forall|x: Val| s1.contains(x) <==> t.contains(x) by {
        lemma_sset_has(sk, ok, ld, l, n + 1, x);
        lemma_sset_has(sk, ok, ld, l, n, x);
        if s1.contains(x) {
            let c = choose|c: int| 0 <= c < n + 1 && ok[c] && ld[c] as int == l && Val::Int(#[trigger] sk[c] as int) == x;
            if c < n { assert(s0.contains(x)); }
        }
    }
    assert(s1 =~= t);
}

/// Whether some qualifying row below `q` with leader `l` has supplier key `k`.
fn seen_before(c: &Cols, ok: &Vec<bool>, ld: &Vec<usize>, q: usize, l: usize, k: i64, Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires cols_ok(*c, sv), ok@.len() == c.nq, ld@.len() == c.nq, q <= c.nq,
    ensures r == sset(ps_skeys(sv), ok@, ld@, l as int, q as int).contains(Val::Int(k as int)),
{
    let ghost s = sset(ps_skeys(sv), ok@, ld@, l as int, q as int);
    let mut x: usize = 0;
    while x < q
        invariant cols_ok(*c, sv), ok@.len() == c.nq, ld@.len() == c.nq, q <= c.nq, x <= q,
            forall|y: int| 0 <= y < x && ok@[y] && ld@[y] == l ==> #[trigger] ps_skeys(sv)[y] != k,
        decreases q - x,
    {
        if ok[x] && ld[x] == l && c.ps_sk[x] == k {
            proof {
                lemma_sset_has(ps_skeys(sv), ok@, ld@, l as int, q as int, Val::Int(k as int));
                assert(Val::Int(ps_skeys(sv)[x as int] as int) == Val::Int(k as int));
            }
            return true;
        }
        x = x + 1;
    }
    proof {
        lemma_sset_has(ps_skeys(sv), ok@, ld@, l as int, q as int, Val::Int(k as int));
        if s.contains(Val::Int(k as int)) {
            let y = choose|y: int| 0 <= y < q && ok@[y] && ld@[y] as int == l as int
                && Val::Int(#[trigger] ps_skeys(sv)[y] as int) == Val::Int(k as int);
            assert(ps_skeys(sv)[y] != k);
        }
    }
    false
}

/// The number of distinct supplier keys of the rows of every leader.
fn count_sets(c: &Cols, ok: &Vec<bool>, ld: &Vec<usize>, Ghost(sv): Ghost<StoresView>) -> (cnt: Vec<u64>)
    requires cols_ok(*c, sv), ok@.len() == c.nq, ld@.len() == c.nq, forall|x: int| 0 <= x < c.nq ==> #[trigger] ld@[x] < c.nq,
    ensures cnt@.len() == c.nq,
        forall|l: int| 0 <= l < c.nq ==> #[trigger] cnt@[l] as int == sset(ps_skeys(sv), ok@, ld@, l, c.nq as int).len(),
{
    let ghost sk = ps_skeys(sv);
    let mut cnt: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < c.nq
        invariant cnt@.len() == i, i <= c.nq, forall|l: int| 0 <= l < i ==> #[trigger] cnt@[l] == 0,
        decreases c.nq - i,
    {
        cnt.push(0);
        i = i + 1;
    }
    proof {
        assert forall|l: int| 0 <= l < c.nq implies #[trigger] cnt@[l] as int == sset(sk, ok@, ld@, l, 0).len() by {
            assert forall|x: Val| !sset(sk, ok@, ld@, l, 0).contains(x) by { lemma_sset_has(sk, ok@, ld@, l, 0, x); }
            assert(sset(sk, ok@, ld@, l, 0) =~= Set::<Val>::empty());
        }
    }
    let mut q: usize = 0;
    while q < c.nq
        invariant
            cols_ok(*c, sv), sk == ps_skeys(sv), ok@.len() == c.nq, ld@.len() == c.nq, cnt@.len() == c.nq, q <= c.nq,
            forall|x: int| 0 <= x < c.nq ==> #[trigger] ld@[x] < c.nq,
            forall|l: int| 0 <= l < c.nq ==> #[trigger] cnt@[l] as int == sset(sk, ok@, ld@, l, q as int).len(),
            forall|l: int| 0 <= l < c.nq ==> #[trigger] cnt@[l] <= q,
        decreases c.nq - q,
    {
        let ghost cnt0 = cnt@;
        if ok[q] {
            let l = ld[q];
            let k = c.ps_sk[q];
            if !seen_before(c, ok, ld, q, l, k, Ghost(sv)) {
                let v = cnt[l];
                cnt.set(l, v + 1);
            }
        }
        proof {
            assert forall|l: int| 0 <= l < c.nq implies #[trigger] cnt@[l] as int == sset(sk, ok@, ld@, l, q + 1).len()
                && cnt@[l] <= q + 1 by {
                lemma_sset_step(sk, ok@, ld@, l, q as int);
                assert(cnt0[l] as int == sset(sk, ok@, ld@, l, q as int).len());
            }
        }
        q = q + 1;
    }
    cnt
}

/// The distinct supplier keys of the group of leader `l` are `sset(.., l, nq)`.
pub proof fn lemma_leader_vals(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, l: int)
    requires stores_wf(sv), keys_ok(sv), join_ok(sv, ps, pa, ok), lead_ok(sv, pa, ok, ld, ps_n(sv) as int),
        0 <= l < ps_n(sv), ok[l], ld[l] as int == l,
    ensures
        gvals(sv, ps, kr(sv, pa, l)) == sset(ps_skeys(sv), ok, ld, l, ps_n(sv) as int),
        is_group(sv, ps, kr(sv, pa, l)),
{
    let k = kr(sv, pa, l);
    let n = ps_n(sv) as int;
    let sk = ps_skeys(sv);
    let s = sset(sk, ok, ld, l, n);
    assert forall|v: Val| #[trigger] gvals(sv, ps, k).contains(v) <==> s.contains(v) by {
        lemma_vals_contains(sv, ps, k, v);
        lemma_sset_has(sk, ok, ld, l, n, v);
        if in_vals(sv, ps, k, v) {
            let (c, a) = choose|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a)
                && krow(sv, a) == k && v == Val::Int(sk[c] as int);
            lemma_qual_iff(sv, ps, pa, ok, c, a);
            lemma_same_leader(sv, pa, ok, ld, n, c, l);
            assert(Val::Int(sk[c] as int) == v);
        }
        if s.contains(v) {
            let c = choose|c: int| 0 <= c < n && ok[c] && ld[c] as int == l && Val::Int(#[trigger] sk[c] as int) == v;
            lemma_same_leader(sv, pa, ok, ld, n, c, l);
            let a = pa[c] as int;
            lemma_qual_iff(sv, ps, pa, ok, c, a);
            assert(qual(sv, ps, c, a) && krow(sv, a) == k);
        }
    }
    assert(gvals(sv, ps, k) =~= s);
    lemma_qual_iff(sv, ps, pa, ok, l, pa[l] as int);
    assert(qual(sv, ps, l, pa[l] as int));
}

/// Every group of the statement is the key of a leader.
pub proof fn lemma_group_leader(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, k: Row)
    requires stores_wf(sv), keys_ok(sv), join_ok(sv, ps, pa, ok), lead_ok(sv, pa, ok, ld, ps_n(sv) as int), is_group(sv, ps, k),
    ensures exists|l: int| 0 <= l < ps_n(sv) && ok[l] && ld[l] as int == l && #[trigger] kr(sv, pa, l) == k,
{
    let n = ps_n(sv) as int;
    let (c, a) = choose|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a) && krow(sv, a) == k;
    lemma_qual_iff(sv, ps, pa, ok, c, a);
    let l = ld[c] as int;
    assert(ok[l] && kr(sv, pa, l) == k);
    lemma_same_leader(sv, pa, ok, ld, n, c, l);
    assert(ld[l] <= l);
    lemma_same_leader(sv, pa, ok, ld, n, l, ld[l] as int);
    assert(ok[ld[l] as int]);
    assert(kr(sv, pa, ld[l] as int) == kr(sv, pa, l));
    lemma_same_leader(sv, pa, ok, ld, n, ld[l] as int, c);
}

// ------------------------------------------------------------------------------------------------ output

/// Row `l` leads its group.
pub open spec fn is_leader(ok: Seq<bool>, ld: Seq<usize>, l: int) -> bool {
    0 <= l < ok.len() && ok[l] && ld[l] as int == l
}

/// The output row of leader `l` with count `cnt`.
fn leader_row(c: &Cols, pa: &Vec<usize>, cnt: u64, l: usize, Ghost(sv): Ghost<StoresView>) -> (r: ERow)
    requires cols_ok(*c, sv), pa@.len() == c.nq, l < c.nq, pa@[l as int] < c.np, cnt <= 0x7fff_ffff_ffff_ffff,
    ensures view_row(r@) == kr(sv, pa@, l as int) + seq![Val::Int(cnt as int)],
{
    let a = pa[l];
    let (x, y) = trange(&c.brand, a, Ghost(c.np as int));
    let b = copy_bytes(c.brand.bytes, x, y);
    let (x, y) = trange(&c.ptype, a, Ghost(c.np as int));
    let t = copy_bytes(c.ptype.bytes, x, y);
    let r: ERow = vec![EVal::Text(b), EVal::Text(t), EVal::Int(c.p_size[a]), EVal::Int(cnt as i64)];
    proof {
        assert(view_row(r@) =~= kr(sv, pa@, l as int) + seq![Val::Int(cnt as int)]);
    }
    r
}

/// The facts the output needs about the join, leaders and counts.
pub open spec fn tables_fb(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, cnt: Seq<u64>) -> bool {
    &&& stores_wf(sv) && keys_ok(sv)
    &&& join_ok(sv, ps, pa, ok) && lead_ok(sv, pa, ok, ld, ps_n(sv) as int) && ld.len() == ps_n(sv)
    &&& cnt.len() == ps_n(sv)
    &&& forall|l: int| 0 <= l < ps_n(sv) ==> #[trigger] cnt[l] as int == sset(ps_skeys(sv), ok, ld, l, ps_n(sv) as int).len()
}

/// The count of a leader is its group's count.
proof fn lemma_leader_count(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, cnt: Seq<u64>, l: int)
    requires tables_fb(sv, ps, pa, ok, ld, cnt), is_leader(ok, ld, l),
    ensures cnt[l] as int == gcount(sv, ps, kr(sv, pa, l)), is_group(sv, ps, kr(sv, pa, l)), pa[l] < part_n(sv),
{
    lemma_leader_vals(sv, ps, pa, ok, ld, l);
}

/// The rows `rs` are the output rows of the leaders `lds` (increasing), which are all leaders below `q`.
pub open spec fn emitted_ok(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, rs: Seq<Row>,
    lds: Seq<int>, q: int) -> bool {
    &&& rs.len() == lds.len()
    &&& e1(sv, ps, pa, ok, ld, rs, lds, q)
    &&& e2(lds)
    &&& e3(ok, ld, lds, q)
    &&& e4(sv, ps, pa, ok, ld, q)
}

/// Parts of `emitted_ok`: the rows and leaders agree; the leaders increase; every leader below `q` is listed; its
/// count fits.
pub open spec fn e1(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, rs: Seq<Row>,
    lds: Seq<int>, q: int) -> bool {
    forall|i: int| 0 <= i < lds.len() ==> #[trigger] is_leader(ok, ld, lds[i]) && lds[i] < q
        && rs[i] == out_row(sv, ps, kr(sv, pa, lds[i]))
}
pub open spec fn e2(lds: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < lds.len() ==> lds[i] < lds[j]
}
pub open spec fn e3(ok: Seq<bool>, ld: Seq<usize>, lds: Seq<int>, q: int) -> bool {
    forall|l: int| 0 <= l < q && #[trigger] is_leader(ok, ld, l) ==> lds.contains(l)
}
pub open spec fn e4(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, q: int) -> bool {
    forall|l: int| 0 <= l < q && #[trigger] is_leader(ok, ld, l) ==> gcount(sv, ps, kr(sv, pa, l)) <= int8_max()
}

proof fn lemma_e1_mono(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, rs: Seq<Row>,
    lds: Seq<int>, q: int)
    requires e1(sv, ps, pa, ok, ld, rs, lds, q),
    ensures e1(sv, ps, pa, ok, ld, rs, lds, q + 1),
{
}

proof fn lemma_e34_skip(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, lds: Seq<int>, q: int)
    requires e3(ok, ld, lds, q), e4(sv, ps, pa, ok, ld, q), !is_leader(ok, ld, q),
    ensures e3(ok, ld, lds, q + 1), e4(sv, ps, pa, ok, ld, q + 1),
{
}

/// A row that is not a leader adds nothing.
proof fn lemma_emit_skip(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, rs: Seq<Row>,
    lds: Seq<int>, q: int)
    requires emitted_ok(sv, ps, pa, ok, ld, rs, lds, q), !is_leader(ok, ld, q),
    ensures emitted_ok(sv, ps, pa, ok, ld, rs, lds, q + 1),
{
    lemma_e1_mono(sv, ps, pa, ok, ld, rs, lds, q);
    lemma_e34_skip(sv, ps, pa, ok, ld, lds, q);
}

/// A leader adds its row.
proof fn lemma_emit_push(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, rs: Seq<Row>,
    lds: Seq<int>, q: int, row: Row)
    requires emitted_ok(sv, ps, pa, ok, ld, rs, lds, q), is_leader(ok, ld, q), row == out_row(sv, ps, kr(sv, pa, q)),
        gcount(sv, ps, kr(sv, pa, q)) <= int8_max(),
    ensures emitted_ok(sv, ps, pa, ok, ld, rs.push(row), lds.push(q), q + 1),
{
    let (rs1, lds1) = (rs.push(row), lds.push(q));
    assert forall|i: int| 0 <= i < lds1.len() implies #[trigger] is_leader(ok, ld, lds1[i]) && lds1[i] < q + 1
        && rs1[i] == out_row(sv, ps, kr(sv, pa, lds1[i])) by {
        if i < lds.len() { assert(lds1[i] == lds[i] && rs1[i] == rs[i]); }
    }
    assert forall|i: int, j: int| 0 <= i < j < lds1.len() implies lds1[i] < lds1[j] by {
        if j < lds.len() {
            assert(lds1[i] == lds[i] && lds1[j] == lds[j]);
        } else {
            assert(lds1[i] == lds[i]);
            assert(is_leader(ok, ld, lds[i]));
        }
    }
    assert forall|l: int| 0 <= l < q + 1 && #[trigger] is_leader(ok, ld, l) implies lds1.contains(l) by {
        if l < q {
            let i = choose|i: int| 0 <= i < lds.len() && lds[i] == l;
            assert(lds1[i] == l);
        } else {
            assert(lds1[lds.len() as int] == l);
        }
    }
}

/// The output rows of all leaders, in row order, or a leader whose count does not fit `int8`.
fn emit_rows(c: &Cols, pa: &Vec<usize>, ok: &Vec<bool>, ld: &Vec<usize>, cnt: &Vec<u64>, Ghost(sv): Ghost<StoresView>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<(Vec<ERow>, Ghost<Seq<int>>), usize>)
    requires cols_ok(*c, sv), tables_fb(sv, ps, pa@, ok@, ld@, cnt@),
    ensures
        r matches Ok((rows, lds)) ==> emitted_ok(sv, ps, pa@, ok@, ld@, view_rows(rows@), lds@, c.nq as int),
        r matches Err(l) ==> is_leader(ok@, ld@, l as int) && gcount(sv, ps, kr(sv, pa@, l as int)) > int8_max(),
{
    let mut rows: Vec<ERow> = Vec::new();
    let ghost mut lds: Seq<int> = Seq::empty();
    let mut q: usize = 0;
    proof { assert(view_rows(rows@) =~= Seq::<Row>::empty()); }
    while q < c.nq
        invariant
            cols_ok(*c, sv), tables_fb(sv, ps, pa@, ok@, ld@, cnt@), q <= c.nq,
            emitted_ok(sv, ps, pa@, ok@, ld@, view_rows(rows@), lds, q as int),
        decreases c.nq - q,
    {
        if ok[q] && ld[q] == q {
            proof { lemma_leader_count(sv, ps, pa@, ok@, ld@, cnt@, q as int); }
            let n = cnt[q];
            if n > 0x7fff_ffff_ffff_ffff {
                return Err(q);
            }
            let row = leader_row(c, pa, n, q, Ghost(sv));
            let ghost rows0 = rows@;
            rows.push(row);
            proof {
                assert(view_rows(rows@) =~= view_rows(rows0).push(view_row(row@)));
                lemma_emit_push(sv, ps, pa@, ok@, ld@, view_rows(rows0), lds, q as int, view_row(row@));
                lds = lds.push(q as int);
            }
        } else {
            proof { lemma_emit_skip(sv, ps, pa@, ok@, ld@, view_rows(rows@), lds, q as int); }
        }
        q = q + 1;
    }
    Ok((rows, Ghost(lds)))
}

/// The emitted rows are distinct.
proof fn lemma_emitted_nodup(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, cnt: Seq<u64>,
    rs: Seq<Row>, lds: Seq<int>)
    requires tables_fb(sv, ps, pa, ok, ld, cnt), emitted_ok(sv, ps, pa, ok, ld, rs, lds, ps_n(sv) as int),
    ensures rs.no_duplicates(),
{
    let n = ps_n(sv) as int;
    assert forall|i: int, j: int| 0 <= i < rs.len() && 0 <= j < rs.len() && i != j implies rs[i] != rs[j] by {
        assert(is_leader(ok, ld, lds[i]) && is_leader(ok, ld, lds[j]));
        let (k1, k2) = (kr(sv, pa, lds[i]), kr(sv, pa, lds[j]));
        if rs[i] == rs[j] {
            assert(k1 =~= rs[i].subrange(0, 3));
            assert(k2 =~= rs[j].subrange(0, 3));
            lemma_same_leader(sv, pa, ok, ld, n, lds[i], lds[j]);
            if i < j { assert(lds[i] < lds[j]); } else { assert(lds[j] < lds[i]); }
        }
    }
}

/// Every group's count fits.
proof fn lemma_emitted_fit(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, cnt: Seq<u64>,
    rs: Seq<Row>, lds: Seq<int>)
    requires tables_fb(sv, ps, pa, ok, ld, cnt), emitted_ok(sv, ps, pa, ok, ld, rs, lds, ps_n(sv) as int),
    ensures counts_fit(sv, ps),
{
    assert forall|k: Row| #[trigger] is_group(sv, ps, k) implies gcount(sv, ps, k) <= int8_max() by {
        lemma_group_leader(sv, ps, pa, ok, ld, k);
        let l = choose|l: int| 0 <= l < ps_n(sv) && ok[l] && ld[l] as int == l && #[trigger] kr(sv, pa, l) == k;
        assert(is_leader(ok, ld, l));
    }
}

/// The emitted rows are the statement's output rows.
proof fn lemma_emitted_rows(sv: StoresView, ps: Seq<Literal>, pa: Seq<usize>, ok: Seq<bool>, ld: Seq<usize>, cnt: Seq<u64>,
    rs: Seq<Row>, lds: Seq<int>)
    requires tables_fb(sv, ps, pa, ok, ld, cnt), emitted_ok(sv, ps, pa, ok, ld, rs, lds, ps_n(sv) as int),
    ensures
        forall|r: Row| #[trigger] rs.contains(r) <==> exists|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k),
        forall|r: Row| #[trigger] rs.contains(r) ==> r.len() == 4 && r[0] is Text && r[1] is Text && r[2] is Int && r[3] is Int,
{
    assert forall|r: Row| #[trigger] rs.contains(r) <==> exists|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k) by {
        if rs.contains(r) {
            let i = choose|i: int| 0 <= i < rs.len() && rs[i] == r;
            assert(is_leader(ok, ld, lds[i]));
            lemma_leader_count(sv, ps, pa, ok, ld, cnt, lds[i]);
            assert(is_group(sv, ps, kr(sv, pa, lds[i])));
        }
        if exists|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k) {
            let k = choose|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k);
            lemma_group_leader(sv, ps, pa, ok, ld, k);
            let l = choose|l: int| 0 <= l < ps_n(sv) && ok[l] && ld[l] as int == l && #[trigger] kr(sv, pa, l) == k;
            assert(is_leader(ok, ld, l));
            let i = choose|i: int| 0 <= i < lds.len() && lds[i] == l;
            assert(is_leader(ok, ld, lds[i]));
            assert(rs[i] == r);
        }
    }
    assert forall|r: Row| #[trigger] rs.contains(r) implies r.len() == 4 && r[0] is Text && r[1] is Text && r[2] is Int && r[3] is Int by {
        let i = choose|i: int| 0 <= i < rs.len() && rs[i] == r;
        assert(is_leader(ok, ld, lds[i]));
        lemma_leader_count(sv, ps, pa, ok, ld, cnt, lds[i]);
    }
}

/// The ORDER BY keys as executable keys.
fn exec_order_keys() -> (ks: Vec<EOrderKey>)
    ensures view_keys(ks@) == order_keys(),
{
    let ks = vec![
        EOrderKey { col: 3, desc: true, nulls_first: true },
        EOrderKey { col: 0, desc: false, nulls_first: false },
        EOrderKey { col: 1, desc: false, nulls_first: false },
        EOrderKey { col: 2, desc: false, nulls_first: false },
    ];
    proof { assert(view_keys(ks@) =~= order_keys()); }
    ks
}

/// Sorting the rows keeps them, once each, and orders them.
proof fn lemma_sorted_rows(sv: StoresView, ps: Seq<Literal>, rs: Seq<Row>, out: Seq<Row>)
    requires
        rs.no_duplicates(),
        forall|r: Row| #[trigger] rs.contains(r) <==> exists|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k),
        forall|r: Row| #[trigger] rs.contains(r) ==> r.len() == 4 && r[0] is Text && r[1] is Text && r[2] is Int && r[3] is Int,
        out == sort_rows(order_keys(), rs),
    ensures
        out.no_duplicates(), sorted_by(order_keys(), out),
        forall|r: Row| #[trigger] out.contains(r) <==> exists|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k),
{
    let fams = seq![1int, 3int, 3int, 1int];
    let ks = order_keys();
    assert forall|i: int| 0 <= i < rs.len() implies order_keys_ok(ks, fams, #[trigger] rs[i]) by {
        assert(rs.contains(rs[i]));
        assert forall|j: int| 0 <= j < ks.len() implies #[trigger] key_ok(ks[j], fams[j], rs[i]) by {}
    }
    lemma_sort_rows(ks, fams, rs);
    rs.to_multiset_ensures();
    out.to_multiset_ensures();
    rs.lemma_multiset_has_no_duplicates();
    out.lemma_multiset_has_no_duplicates_conv();
    assert forall|r: Row| #[trigger] out.contains(r) <==> rs.contains(r) by {
        assert(out.to_multiset().count(r) == rs.to_multiset().count(r));
    }
}

/// The answer of the general path.
pub fn fallback(c: &Cols, params: &Params, szl: &Vec<i64>, ekeys: &Vec<i64>, Ghost(sv): Ghost<StoresView>) -> (r: Answer)
    requires
        cols_ok(*c, sv), stores_wf(sv), keys_ok(sv), param_domain(params@), sizes_ok(szl@, params@),
        c.np >= 1, c.nq >= 1,
        forall|k: int| #[trigger] has_key(ekeys@, k) <==> excluded(sv, k),
    ensures forall|db: Database| #[trigger] bound_db(sv, db) ==> outcome_ok(db, query_spec_at(params@), Ok::<Answer, crate::gendb_entry::runtime::QueryError>(r)),
{
    let ghost ps = params@;
    let flags = match part_flags(c, params, szl, Ghost(sv)) {
        Ok(f) => f,
        Err((a0, e)) => {
            proof { lemma_answer_like_err(sv, ps, a0 as int); }
            return Answer::SqlError(e);
        },
    };
    let (pa, ok) = join_rows(c, &flags, ekeys, Ghost(sv), Ghost(ps));
    let ld = leaders(c, &pa, &ok, Ghost(sv), Ghost(ps));
    proof {
        assert forall|x: int| 0 <= x < c.nq implies #[trigger] ld@[x] < c.nq by {
            assert(ld@[x] <= x);
        }
    }
    let cnt = count_sets(c, &ok, &ld, Ghost(sv));
    let (rows, Ghost(lds)) = match emit_rows(c, &pa, &ok, &ld, &cnt, Ghost(sv), Ghost(ps)) {
        Ok(x) => x,
        Err(l) => {
            proof {
                lemma_leader_count(sv, ps, pa@, ok@, ld@, cnt@, l as int);
                lemma_answer_count_err(sv, ps, kr(sv, pa@, l as int));
            }
            return Answer::SqlError(SqlError::NumericValueOutOfRange);
        },
    };
    let ghost rs = view_rows(rows@);
    proof {
        lemma_emitted_nodup(sv, ps, pa@, ok@, ld@, cnt@, rs, lds);
        lemma_emitted_fit(sv, ps, pa@, ok@, ld@, cnt@, rs, lds);
        lemma_emitted_rows(sv, ps, pa@, ok@, ld@, cnt@, rs, lds);
    }
    let ks = exec_order_keys();
    let sorted = sort_rows_exec(&ks, rows);
    proof {
        lemma_sorted_rows(sv, ps, rs, view_rows(sorted@));
        lemma_answer_rows(sv, ps, view_rows(sorted@));
    }
    Answer::Rows(sorted)
}

} // verus!
