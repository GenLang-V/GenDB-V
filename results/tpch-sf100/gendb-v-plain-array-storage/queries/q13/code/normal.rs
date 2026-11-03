//! The statement's normal form over the stored columns (`sv`) and the pattern bytes `pat` of `$1`:
//! - `like_j(sv, pat, j)`: the value of `o_comment LIKE $1` on orders row `j` (a Boolean, or the matcher's error,
//!   always 22025, `lemma_like_kinds`);
//! - `counted(sv, pat, j)`: row `j` passes `NOT LIKE` (the LIKE is false);
//! - `ccnt(sv, pat, i)`: `c_count` of customer row `i`, the number of counted orders whose `o_custkey` is its key;
//! - `r1(sv, pat)`: the inner GROUP BY's rows `(c_custkey, c_count)`, one per customer row in row order;
//! - `hcount(sv, pat, v, n)`: the number of customer rows below `n` with `c_count == v` (the outer COUNT(*)).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::gendb_entry::stores::StoresView;
use crate::agent::common::segments::like_of;
use crate::agent::tables::*;

verus! {

/// The pattern bytes of `$1`.
pub open spec fn pat_of(ps: Seq<Literal>) -> Seq<u8> {
    match ps[0] {
        Literal::Text(b) => b,
        _ => Seq::empty(),
    }
}

/// `o_comment LIKE $1` on orders row `j`.
pub open spec fn like_j(sv: StoresView, pat: Seq<u8>, j: int) -> Result<Val, SqlError> {
    like_of(cmt(sv, j), pat)
}

/// No orders row's `LIKE` raises.
pub open spec fn likes_ok(sv: StoresView, pat: Seq<u8>) -> bool {
    forall|j: int| 0 <= j < n_o(sv) ==> #[trigger] like_j(sv, pat, j) is Ok
}

/// Orders row `j` passes `o_comment NOT LIKE $1`.
pub open spec fn counted(sv: StoresView, pat: Seq<u8>, j: int) -> bool {
    like_j(sv, pat, j) == Ok::<Val, SqlError>(Val::Bool(false))
}

/// Number of counted orders rows below `n` whose `o_custkey` is `key`.
pub open spec fn ocnt(sv: StoresView, pat: Seq<u8>, key: int, n: int) -> nat
    decreases n,
{
    if n <= 0 { 0 } else { ocnt(sv, pat, key, n - 1) + if ock(sv)[n - 1] as int == key && counted(sv, pat, n - 1) { 1nat } else { 0nat } }
}

/// `c_count` of customer row `i`.
pub open spec fn ccnt(sv: StoresView, pat: Seq<u8>, i: int) -> nat {
    ocnt(sv, pat, cck(sv)[i] as int, n_o(sv))
}

/// The inner GROUP BY's rows: `(c_custkey, c_count)` per customer row.
pub open spec fn r1(sv: StoresView, pat: Seq<u8>) -> Seq<Row> {
    Seq::new(n_c(sv) as nat, |i: int| seq![Val::Int(cck(sv)[i] as int), Val::Int(ccnt(sv, pat, i) as int)])
}

/// Number of customer rows below `n` with `c_count == v`.
pub open spec fn hcount(sv: StoresView, pat: Seq<u8>, v: int, n: int) -> nat
    decreases n,
{
    if n <= 0 { 0 } else { hcount(sv, pat, v, n - 1) + if ccnt(sv, pat, n - 1) == v { 1nat } else { 0nat } }
}

// ------------------------------------------------------------------------------------------------ the LIKE values

/// `like_end` never raises.
proof fn lemma_end_ok(p: Seq<LikeTok>, j: int)
    ensures like_end(p, j) is Ok,
    decreases p.len() - j,
{
    if 0 <= j < p.len() {
        if p[j] is Any {
            lemma_end_ok(p, j + 1);
        }
    }
}

/// `like_mt` raises only 22025.
proof fn lemma_mt_err(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    ensures like_mt(t, p, i, j) is Err ==> like_mt(t, p, i, j) == Err::<LikeRes, SqlError>(SqlError::InvalidEscapeSequence),
    decreases p.len() - j, 0int, t.len() - i,
{
    if 0 <= i < t.len() && 0 <= j < p.len() {
        match p[j] {
            LikeTok::Dangling => {},
            LikeTok::Lit(c) => { if t[i] == c { lemma_mt_err(t, p, i + 1, j + 1); } },
            LikeTok::One => { lemma_mt_err(t, p, i + 1, j + 1); },
            LikeTok::Any => { lemma_any_err(t, p, i, j + 1); },
        }
    } else if 0 <= i < t.len() {
    } else {
        lemma_end_ok(p, j);
    }
}

/// `like_any` raises only 22025.
proof fn lemma_any_err(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    ensures like_any(t, p, i, j) is Err ==> like_any(t, p, i, j) == Err::<LikeRes, SqlError>(SqlError::InvalidEscapeSequence),
    decreases p.len() - j, 2int, t.len() - i,
{
    if 0 <= j < p.len() {
        match p[j] {
            LikeTok::Any => { lemma_any_err(t, p, i, j + 1); },
            LikeTok::One => { if 0 <= i < t.len() { lemma_any_err(t, p, i + 1, j + 1); } },
            LikeTok::Dangling => {},
            LikeTok::Lit(_) => { lemma_scan_err(t, p, i, j); },
        }
    }
}

/// `like_scan` raises only 22025.
proof fn lemma_scan_err(t: Seq<Seq<u8>>, p: Seq<LikeTok>, k: int, j: int)
    ensures like_scan(t, p, k, j) is Err ==> like_scan(t, p, k, j) == Err::<LikeRes, SqlError>(SqlError::InvalidEscapeSequence),
    decreases p.len() - j, 1int, t.len() - k,
{
    if 0 <= k < t.len() {
        lemma_mt_err(t, p, k, j);
        if like_mt(t, p, k, j) == Ok::<LikeRes, SqlError>(LikeRes::NoMatch) {
            lemma_scan_err(t, p, k + 1, j);
        }
    }
}

/// `t LIKE pat` (escape backslash) is a Boolean or the error 22025.
pub proof fn lemma_like_kinds(t: Seq<u8>, pat: Seq<u8>)
    ensures
        like_of(t, pat) is Ok ==> exists|b: bool| like_of(t, pat) == Ok::<Val, SqlError>(Val::Bool(b)),
        like_of(t, pat) is Err ==> like_of(t, pat) == Err::<Val, SqlError>(SqlError::InvalidEscapeSequence),
{
    let e = seq![0x5Cu8];
    assert(e.drop_last() =~= Seq::<u8>::empty());
    assert(chars(e.drop_last()) == Seq::<Seq<u8>>::empty());
    assert(!is_cont(e.last()));
    assert(chars(e).len() == 1);
    let toks = like_tokens(chars(pat), escape_of(chars(e)), 0);
    lemma_mt_err(chars(t), toks, 0, 0);
    if like_of(t, pat) is Ok {
        let r = like_mt(chars(t), toks, 0, 0)->Ok_0;
        assert(like_of(t, pat) == Ok::<Val, SqlError>(Val::Bool(r is Match)));
    }
}

} // verus!
