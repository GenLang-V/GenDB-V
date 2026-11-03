//! The matching part rows, decided on the calling thread.
//! - Fast mode (pattern `P%` with a plain ASCII `P`, name order present): four binary searches over the name order
//!   give two ranges of name-order positions holding exactly the matching rows (`fast_ranges`): the names in
//!   `[P, P'')` (`P''`: `P` with its last byte incremented) start with `P`; those in `[P ++ 0x80, P ++ 0xC0)`
//!   continue with a UTF-8 continuation byte and do not match `P%` (its `%` starts at a character boundary).
//! - General mode: the LIKE of every part name (`like_all`), which also finds an erring name.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::text::lex_cmp;
use crate::spec::chars::is_cont;
use crate::gendb_entry::layout::PartView;
use crate::exec::value::EVal;
use crate::exec::fns::like::like_value_exec;
use crate::stores::part_nameidx::interface as pi;
use crate::stores::suppliers::interface::common::read::{text_slice, bytes_cmp};
use crate::stores::suppliers::interface::common::colfmt as cf;
use super::nf::*;
use super::bind_pl::pp_ok;
use super::sl::*;
use super::common::likeprefix::*;

verus! {

/// The name at position `p` of the name order.
pub open spec fn name_pos(pp: Seq<PartView>, p: int) -> Seq<u8> {
    pi::name_at(pp, pi::perm(pp)[p] as int)
}

/// The views of the part slices.
pub open spec fn pslices(pp: Seq<PartView>, offs: Seq<u64>, bytes: Seq<u8>, n: int) -> bool {
    &&& pp_ok(pp)
    &&& offs == pi::name_offs(pp)
    &&& bytes == pi::name_bytes(pp)
    &&& n == pi::n_rows(pp)
}

/// `a <= b < c` gives `a < c`.
pub proof fn lemma_lt_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires lex_cmp(a, b) <= 0, lex_cmp(b, c) < 0,
    ensures lex_cmp(a, c) < 0,
{
    crate::bridge::order::lemma_lex_cmp_trans(a, b, c);
    if lex_cmp(a, c) == 0 {
        crate::bridge::equality::lemma_lex_cmp_zero(a, c);
        crate::bridge::order::lemma_lex_cmp_antisym(b, c);
    }
}

/// The name of part row `r`.
pub fn name_of<'a>(offs: &[u64], bytes: &'a [u8], r: usize, Ghost(pp): Ghost<Seq<PartView>>, Ghost(n): Ghost<int>) -> (s: &'a [u8])
    requires pslices(pp, offs@, bytes@, n), r < n,
    ensures s@ == pi::name_at(pp, r as int),
    no_unwind
{
    assert(pi::name_range_ok(pp, r as int));
    assert(cf::text_range_ok(offs@, bytes@, r as int));
    text_slice(offs, bytes, r)
}

/// The first position of the name order whose name is not below `key`.
pub fn name_lb(perm: &[u32], offs: &[u64], bytes: &[u8], n: usize, key: &[u8], Ghost(pp): Ghost<Seq<PartView>>) -> (r: usize)
    requires
        pslices(pp, offs@, bytes@, n as int),
        pi::has_perm(pp),
        perm@ == pi::perm(pp),
    ensures
        r <= n,
        forall|p: int| 0 <= p < r ==> lex_cmp(#[trigger] name_pos(pp, p), key@) < 0,
        forall|p: int| r <= p < n ==> lex_cmp(#[trigger] name_pos(pp, p), key@) >= 0,
{
    let mut lo: usize = 0;
    let mut hi: usize = n;
    while lo < hi
        invariant
            pslices(pp, offs@, bytes@, n as int),
            pi::has_perm(pp),
            perm@ == pi::perm(pp),
            lo <= hi <= n,
            forall|p: int| 0 <= p < lo ==> lex_cmp(#[trigger] name_pos(pp, p), key@) < 0,
            forall|p: int| hi <= p < n ==> lex_cmp(#[trigger] name_pos(pp, p), key@) >= 0,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        assert(perm@[mid as int] < n);
        let r = perm[mid] as usize;
        let s = name_of(offs, bytes, r, Ghost(pp), Ghost(n as int));
        let c = bytes_cmp(s, s.len(), key, key.len());
        proof {
            assert(s@ == name_pos(pp, mid as int));
        }
        if c < 0 {
            proof {
                assert forall|p: int| 0 <= p < mid + 1 implies lex_cmp(#[trigger] name_pos(pp, p), key@) < 0 by {
                    pi::lemma_name_order(pp, n as int, p, mid as int);
                    lemma_lt_trans(name_pos(pp, p), name_pos(pp, mid as int), key@);
                }
            }
            lo = mid + 1;
        } else {
            proof {
                assert forall|p: int| mid <= p < n implies lex_cmp(#[trigger] name_pos(pp, p), key@) >= 0 by {
                    pi::lemma_name_order(pp, n as int, mid as int, p);
                    crate::bridge::order::lemma_lex_cmp_antisym(name_pos(pp, mid as int), key@);
                    crate::bridge::order::lemma_lex_cmp_trans(key@, name_pos(pp, mid as int), name_pos(pp, p));
                    crate::bridge::order::lemma_lex_cmp_antisym(name_pos(pp, p), key@);
                }
            }
            hi = mid;
        }
    }
    lo
}

/// Position `p` lies in the two ranges.
pub open spec fn in_ranges(a1: int, b1: int, a2: int, b2: int, p: int) -> bool {
    (a1 <= p < b1) || (a2 <= p < b2)
}

/// Part row `r`'s name matches `$1`.
pub open spec fn hit_row(pp: Seq<PartView>, pat: Seq<u8>, r: int) -> bool {
    like_hit(pi::name_at(pp, r), pat)
}

/// A copy of the bytes `p`.
pub fn copy_bytes(p: &[u8]) -> (v: Vec<u8>)
    ensures v@ == p@,
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < p.len()
        invariant i <= p@.len(), v@ == p@.subrange(0, i as int),
        decreases p@.len() - i,
    {
        v.push(p[i]);
        proof {
            assert(v@ =~= p@.subrange(0, i + 1));
        }
        i = i + 1;
    }
    proof {
        assert(p@.subrange(0, p@.len() as int) =~= p@);
    }
    v
}

/// The bytes `p` with byte `b` appended.
fn push_copy(p: &[u8], b: u8) -> (v: Vec<u8>)
    ensures v@ == p@.push(b),
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < p.len()
        invariant i <= p@.len(), v@ == p@.subrange(0, i as int),
        decreases p@.len() - i,
    {
        v.push(p[i]);
        proof {
            assert(v@ =~= p@.subrange(0, i + 1));
        }
        i = i + 1;
    }
    v.push(b);
    proof {
        assert(p@.subrange(0, p@.len() as int) =~= p@);
    }
    v
}

/// `P` is a plain ASCII prefix: no `%`, `_` or `\`.
pub fn is_plain(p: &[u8]) -> (b: bool)
    ensures b == plain_prefix(p@),
{
    let mut i: usize = 0;
    while i < p.len()
        invariant i <= p@.len(), forall|j: int| 0 <= j < i ==> #[trigger] p@[j] < 0x80u8 && p@[j] != 0x25u8 && p@[j] != 0x5Fu8 && p@[j] != 0x5Cu8,
        decreases p@.len() - i,
    {
        let c = p[i];
        if c >= 0x80u8 || c == 0x25u8 || c == 0x5Fu8 || c == 0x5Cu8 {
            proof {
                assert(!(p@[i as int] < 0x80u8 && p@[i as int] != 0x25u8 && p@[i as int] != 0x5Fu8 && p@[i as int] != 0x5Cu8));
            }
            return false;
        }
        i = i + 1;
    }
    true
}

/// Position `p` is in the ranges exactly when its name matches, from the four bounds.
proof fn lemma_ranges(pp: Seq<PartView>, pre: Seq<u8>, pat: Seq<u8>, k4: Seq<u8>, n: int, pa: int, qa: int, qb: int, pb: int, p: int)
    requires
        plain_prefix(pre), pre.len() >= 1, pat == pre.push(0x25u8),
        k4 == pre.subrange(0, pre.len() - 1).push((pre[pre.len() - 1] + 1) as u8),
        0 <= p < n,
        (p >= pa) == (lex_cmp(name_pos(pp, p), pre) >= 0),
        (p >= qa) == (lex_cmp(name_pos(pp, p), pre.push(0x80u8)) >= 0),
        (p >= qb) == (lex_cmp(name_pos(pp, p), pre.push(0xC0u8)) >= 0),
        (p >= pb) == (lex_cmp(name_pos(pp, p), k4) >= 0),
    ensures
        ((pa <= p < pb) && !(qa <= p < qb)) == like_hit(name_pos(pp, p), pat),
{
    let t = name_pos(pp, p);
    let m = pre.len() - 1;
    let q = pre.subrange(0, m);
    let a = pre[m];
    assert(a < 0x80u8);
    assert(q.push(a) =~= pre);
    crate::bridge::order::lemma_lex_cmp_antisym(t, pre);
    crate::bridge::order::lemma_lex_cmp_antisym(t, pre.push(0x80u8));
    crate::bridge::order::lemma_lex_cmp_antisym(t, pre.push(0xC0u8));
    crate::bridge::order::lemma_lex_cmp_antisym(t, k4);
    lemma_lex_interval(q, a, (a + 1) as u8, t);
    lemma_lex_interval(pre, 0x80u8, 0xC0u8, t);
    lemma_prefix_like(t, pre);
    // starts with pre
    let st = t.len() > q.len() && t.subrange(0, q.len() as int) == q && a <= t[q.len() as int] < (a + 1) as u8;
    let st2 = t.len() >= pre.len() && t.subrange(0, pre.len() as int) == pre;
    if st {
        assert(t[m] == a);
        assert(t.subrange(0, pre.len() as int) =~= t.subrange(0, m).push(t[m]));
        assert(st2);
    }
    if st2 {
        assert(t.subrange(0, m) =~= t.subrange(0, pre.len() as int).subrange(0, m));
        assert(t[m] == t.subrange(0, pre.len() as int)[m]);
        assert(st);
    }
    assert(prefix_cond(t, pre) == (st2 && !(t.len() > pre.len() && is_cont(t[pre.len() as int]))));
}

/// Fast mode: the two ranges of name-order positions holding exactly the rows whose name matches `pre ++ %`.
pub fn fast_ranges(perm: &[u32], offs: &[u64], bytes: &[u8], n: usize, pre: &[u8], Ghost(pp): Ghost<Seq<PartView>>,
    Ghost(pat): Ghost<Seq<u8>>) -> (r: (usize, usize, usize, usize))
    requires
        pslices(pp, offs@, bytes@, n as int),
        pi::has_perm(pp),
        perm@ == pi::perm(pp),
        plain_prefix(pre@), pre@.len() >= 1, pat == pre@.push(0x25u8),
    ensures
        r.0 <= r.1 <= n, r.2 <= r.3 <= n,
        forall|p: int| 0 <= p < n ==> in_ranges(r.0 as int, r.1 as int, r.2 as int, r.3 as int, p)
            == #[trigger] like_hit(name_pos(pp, p), pat),
{
    let m = pre.len() - 1;
    let k2 = push_copy(pre, 0x80u8);
    let k3 = push_copy(pre, 0xC0u8);
    let (q, _) = pre.split_at(m);
    let last = pre[m];
    assert(last < 0x80u8);
    let k4 = push_copy(q, last + 1);
    let pa = name_lb(perm, offs, bytes, n, pre, Ghost(pp));
    let qa = name_lb(perm, offs, bytes, n, k2.as_slice(), Ghost(pp));
    let qb = name_lb(perm, offs, bytes, n, k3.as_slice(), Ghost(pp));
    let pb = name_lb(perm, offs, bytes, n, k4.as_slice(), Ghost(pp));
    let mn = if qa < pb { qa } else { pb };
    let b1 = if mn < pa { pa } else { mn };
    let mq = if qb < pb { qb } else { pb };
    let a2 = if mq < b1 { b1 } else { mq };
    let b2 = if pb < a2 { a2 } else { pb };
    proof {
        assert forall|p: int| 0 <= p < n implies in_ranges(pa as int, b1 as int, a2 as int, b2 as int, p)
            == #[trigger] like_hit(name_pos(pp, p), pat) by {
            lemma_ranges(pp, pre@, pat, k4@, n as int, pa as int, qa as int, qb as int, pb as int, p);
        }
    }
    (pa, b1, a2, b2)
}

/// General mode: the LIKE of every part name; `err` when some name makes it fail.
pub fn like_all(offs: &[u64], bytes: &[u8], n: usize, pat: &[u8], Ghost(pp): Ghost<Seq<PartView>>) -> (r: (Vec<u8>, bool))
    requires pslices(pp, offs@, bytes@, n as int),
    ensures
        r.0@.len() == n,
        forall|q: int| 0 <= q < n ==> (#[trigger] r.0@[q] != 0) == hit_row(pp, pat@, q),
        r.1 == sl_part_err(pp, pat@),
{
    let mut flags: Vec<u8> = Vec::new();
    let mut err = false;
    let pv = EVal::Text(copy_bytes(pat));
    let mut eb: Vec<u8> = Vec::new();
    eb.push(92u8);
    proof {
        assert(eb@ =~= seq![92u8]);
    }
    let ev = EVal::Text(eb);
    let mut q: usize = 0;
    while q < n
        invariant
            pslices(pp, offs@, bytes@, n as int),
            q <= n,
            pv@ == Val::Text(pat@),
            ev@ == Val::Text(seq![92u8]),
            flags@.len() == q,
            forall|j: int| 0 <= j < q ==> (#[trigger] flags@[j] != 0) == hit_row(pp, pat@, j),
            err == exists|j: int| 0 <= j < q && #[trigger] like_of(pi::name_at(pp, j), pat@) is Err,
        decreases n - q,
    {
        let s = name_of(offs, bytes, q, Ghost(pp), Ghost(n as int));
        let sv = EVal::Text(copy_bytes(s));
        let res = like_value_exec(&sv, &pv, &ev);
        proof {
            assert(like_of(pi::name_at(pp, q as int), pat@) == crate::exec::value::view_result(res));
        }
        let hit = match res {
            Ok(EVal::Bool(b)) => b,
            Ok(_) => false,
            Err(_) => {
                err = true;
                false
            },
        };
        flags.push(if hit { 1u8 } else { 0u8 });
        proof {
            assert(hit == hit_row(pp, pat@, q as int));
            if err {
                if !(res is Err) {
                    let j = choose|j: int| 0 <= j < q && #[trigger] like_of(pi::name_at(pp, j), pat@) is Err;
                    assert(0 <= j < q + 1);
                }
            }
            if exists|j: int| 0 <= j < q + 1 && #[trigger] like_of(pi::name_at(pp, j), pat@) is Err {
                let j = choose|j: int| 0 <= j < q + 1 && #[trigger] like_of(pi::name_at(pp, j), pat@) is Err;
                if j < q {
                } else {
                    assert(res is Err);
                }
            }
        }
        q = q + 1;
    }
    (flags, err)
}

} // verus!
