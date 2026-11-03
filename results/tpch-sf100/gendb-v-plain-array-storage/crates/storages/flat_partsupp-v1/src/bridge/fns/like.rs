//! Proofs about `spec::fns::like`: type soundness (dispatched from `bridge::fns::lemma_fn_family`), and that
//! PostgreSQL's matcher `like_mt` means standard LIKE matching: whenever it returns, it returns `Match` exactly
//! when `like_std` holds, and on a pattern without a dangling escape it always returns (`lemma_like_mt_std`).
//! Its `Abort` early exit is sound: no later text position matches either.
//!
//! The matcher is three mutually recursive functions (`like_mt`, `like_any`, `like_scan`); the lemmas
//! `lemma_mt`, `lemma_any` and `lemma_scan` follow the same recursion and measures. Each states, for its
//! function at text position `i` and token `j`: a returned answer agrees with `like_std` (or, after a `%`, with
//! `std_from`: some position from `i` on matches), `Abort` means no position from `i` on matches, and without a
//! dangling escape the function returns. The recurring step `let k = choose|k| ... like_std(t, p, k, j)` names
//! the matching position so the solver can instantiate `like_std` / `std_from` at it.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::fns::like::*;
use crate::bridge::typing::*;

verus! {

/// Type soundness of `like`: a value is NULL or a boolean.
pub proof fn lemma_like_family(f: ScalarFn, tys: Seq<ColTy>, vs: Seq<Val>)
    requires
        row_typed(vs, tys),
        type_like(f, tys) is Some,
        apply_like(f, vs) is Ok,
    ensures
        val_has_family(apply_like(f, vs)->Ok_0, type_like(f, tys)->0.ty),
{
    let v = apply_like(f, vs)->Ok_0;
    assert(v is Null || v is Bool);
}

/// The tokens contain no dangling escape (then the matcher never raises 22025).
pub open spec fn no_dangling(p: Seq<LikeTok>) -> bool {
    forall|k: int| 0 <= k < p.len() ==> !(#[trigger] p[k] is Dangling)
}

/// Some position in `[i, n]` matches `p[j..]`.
pub open spec fn std_from(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int) -> bool {
    exists|k: int| i <= k <= t.len() && #[trigger] like_std(t, p, k, j)
}

/// `%` at `j`: `t[i..]` matches `p[j..]` iff some suffix `t[k..]`, `k >= i`, matches `p[j + 1..]`.
pub proof fn lemma_std_any(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    requires
        0 <= i <= t.len(),
        0 <= j < p.len(),
        p[j] is Any,
    ensures
        like_std(t, p, i, j) == std_from(t, p, i, j + 1),
    decreases t.len() - i,
{
    if i < t.len() {
        lemma_std_any(t, p, i + 1, j);
        if like_std(t, p, i, j) {
            if like_std(t, p, i, j + 1) {
                assert(like_std(t, p, i, j + 1));
            } else {
                let k = choose|k: int| i + 1 <= k <= t.len() && #[trigger] like_std(t, p, k, j + 1);
                assert(like_std(t, p, k, j + 1));
            }
        }
        if std_from(t, p, i, j + 1) {
            let k = choose|k: int| i <= k <= t.len() && #[trigger] like_std(t, p, k, j + 1);
            if k > i {
                assert(std_from(t, p, i + 1, j + 1));
            }
        }
    } else {
        if std_from(t, p, i, j + 1) {
            let k = choose|k: int| i <= k <= t.len() && #[trigger] like_std(t, p, k, j + 1);
            assert(k == i);
        }
        if like_std(t, p, i, j + 1) {
            assert(std_from(t, p, i, j + 1));
        }
    }
}

/// End of text: `like_end` returns `Match` or `Abort`, `Match` iff the empty rest matches.
pub proof fn lemma_std_end(t: Seq<Seq<u8>>, p: Seq<LikeTok>, j: int)
    requires 0 <= j <= p.len(),
    ensures
        like_end(p, j) == Ok::<LikeRes, SqlError>(LikeRes::Match) || like_end(p, j) == Ok::<LikeRes, SqlError>(LikeRes::Abort),
        (like_end(p, j) == Ok::<LikeRes, SqlError>(LikeRes::Match)) == like_std(t, p, t.len() as int, j),
    decreases p.len() - j,
{
    if j < p.len() {
        if p[j] is Any {
            lemma_std_end(t, p, j + 1);
        }
    }
}

/// The main loop of the matcher (`like_mt`): literal and `_` steps, `%` hands over to `like_any` (`lemma_any`).
pub proof fn lemma_mt(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    requires
        0 <= i <= t.len(),
        0 <= j <= p.len(),
    ensures
        like_mt(t, p, i, j) is Ok ==> ((like_mt(t, p, i, j) == Ok::<LikeRes, SqlError>(LikeRes::Match)) == like_std(t, p, i, j)),
        like_mt(t, p, i, j) == Ok::<LikeRes, SqlError>(LikeRes::Abort) ==> !std_from(t, p, i, j),
        no_dangling(p) ==> like_mt(t, p, i, j) is Ok,
    decreases p.len() - j, 0int, t.len() - i,
{
    let n = t.len() as int;
    if i < n && j < p.len() {
        match p[j] {
            LikeTok::Dangling => {
                assert(!no_dangling(p));
            },
            LikeTok::Lit(c) => {
                if t[i] == c {
                    lemma_mt(t, p, i + 1, j + 1);
                    if like_mt(t, p, i, j) == Ok::<LikeRes, SqlError>(LikeRes::Abort) {
                        if std_from(t, p, i, j) {
                            let k = choose|k: int| i <= k <= n && #[trigger] like_std(t, p, k, j);
                            assert(like_std(t, p, k + 1, j + 1));
                            assert(std_from(t, p, i + 1, j + 1));
                        }
                    }
                }
            },
            LikeTok::One => {
                lemma_mt(t, p, i + 1, j + 1);
                if like_mt(t, p, i, j) == Ok::<LikeRes, SqlError>(LikeRes::Abort) {
                    if std_from(t, p, i, j) {
                        let k = choose|k: int| i <= k <= n && #[trigger] like_std(t, p, k, j);
                        assert(like_std(t, p, k + 1, j + 1));
                        assert(std_from(t, p, i + 1, j + 1));
                    }
                }
            },
            LikeTok::Any => {
                lemma_any(t, p, i, j + 1);
                lemma_std_any(t, p, i, j);
                if like_mt(t, p, i, j) == Ok::<LikeRes, SqlError>(LikeRes::Abort) {
                    if std_from(t, p, i, j) {
                        let k = choose|k: int| i <= k <= n && #[trigger] like_std(t, p, k, j);
                        lemma_std_any(t, p, k, j);
                        let k2 = choose|k2: int| k <= k2 <= n && #[trigger] like_std(t, p, k2, j + 1);
                        assert(std_from(t, p, i, j + 1));
                    }
                }
            },
        }
    } else if i < n {
        if std_from(t, p, i, j) {
            let k = choose|k: int| i <= k <= n && #[trigger] like_std(t, p, k, j);
        }
    } else {
        lemma_std_end(t, p, j);
        if std_from(t, p, i, j) {
            let k = choose|k: int| i <= k <= n && #[trigger] like_std(t, p, k, j);
            assert(k == n);
        }
    }
}

/// After a `%`: `Match` iff some suffix from `i` on matches `p[j..]`; `Abort` iff none does.
pub proof fn lemma_any(t: Seq<Seq<u8>>, p: Seq<LikeTok>, i: int, j: int)
    requires
        0 <= i <= t.len(),
        0 <= j <= p.len(),
    ensures
        like_any(t, p, i, j) is Ok ==> ((like_any(t, p, i, j) == Ok::<LikeRes, SqlError>(LikeRes::Match)) == std_from(t, p, i, j)),
        like_any(t, p, i, j) == Ok::<LikeRes, SqlError>(LikeRes::Abort) ==> !std_from(t, p, i, j),
        no_dangling(p) ==> like_any(t, p, i, j) is Ok,
    decreases p.len() - j, 2int, t.len() - i,
{
    let n = t.len() as int;
    if j < p.len() {
        match p[j] {
            LikeTok::Any => {
                lemma_any(t, p, i, j + 1);
                if std_from(t, p, i, j) {
                    let k = choose|k: int| i <= k <= n && #[trigger] like_std(t, p, k, j);
                    lemma_std_any(t, p, k, j);
                    let k2 = choose|k2: int| k <= k2 <= n && #[trigger] like_std(t, p, k2, j + 1);
                    assert(std_from(t, p, i, j + 1));
                }
                if std_from(t, p, i, j + 1) {
                    let k = choose|k: int| i <= k <= n && #[trigger] like_std(t, p, k, j + 1);
                    lemma_std_any(t, p, k, j);
                    assert(std_from(t, p, k, j + 1));
                    assert(like_std(t, p, k, j));
                    assert(std_from(t, p, i, j));
                }
            },
            LikeTok::One => {
                if i < n {
                    lemma_any(t, p, i + 1, j + 1);
                    if std_from(t, p, i, j) {
                        let k = choose|k: int| i <= k <= n && #[trigger] like_std(t, p, k, j);
                        assert(like_std(t, p, k + 1, j + 1));
                        assert(std_from(t, p, i + 1, j + 1));
                    }
                    if std_from(t, p, i + 1, j + 1) {
                        let k = choose|k: int| i + 1 <= k <= n && #[trigger] like_std(t, p, k, j + 1);
                        assert(like_std(t, p, k - 1, j));
                        assert(std_from(t, p, i, j));
                    }
                } else {
                    if std_from(t, p, i, j) {
                        let k = choose|k: int| i <= k <= n && #[trigger] like_std(t, p, k, j);
                    }
                }
            },
            LikeTok::Dangling => {
                assert(!no_dangling(p));
            },
            LikeTok::Lit(_) => {
                lemma_scan(t, p, i, j);
            },
        }
    } else {
        assert(like_std(t, p, n, j));
        assert(std_from(t, p, i, j));
    }
}

/// The scan after a `%` over a literal at `j` (`like_scan`): the first position `k' >= k` where the rest does not
/// answer `NoMatch` decides.
pub proof fn lemma_scan(t: Seq<Seq<u8>>, p: Seq<LikeTok>, k: int, j: int)
    requires
        0 <= k <= t.len(),
        0 <= j < p.len(),
        p[j] is Lit,
    ensures
        like_scan(t, p, k, j) is Ok ==> ((like_scan(t, p, k, j) == Ok::<LikeRes, SqlError>(LikeRes::Match)) == std_from(t, p, k, j)),
        like_scan(t, p, k, j) == Ok::<LikeRes, SqlError>(LikeRes::Abort) ==> !std_from(t, p, k, j),
        no_dangling(p) ==> like_scan(t, p, k, j) is Ok,
    decreases p.len() - j, 1int, t.len() - k,
{
    let n = t.len() as int;
    if k < n {
        lemma_mt(t, p, k, j);
        if like_mt(t, p, k, j) == Ok::<LikeRes, SqlError>(LikeRes::NoMatch) {
            lemma_scan(t, p, k + 1, j);
            if std_from(t, p, k, j) {
                let k2 = choose|k2: int| k <= k2 <= n && #[trigger] like_std(t, p, k2, j);
                assert(k2 != k);
                assert(std_from(t, p, k + 1, j));
            }
            if std_from(t, p, k + 1, j) {
                let k2 = choose|k2: int| k + 1 <= k2 <= n && #[trigger] like_std(t, p, k2, j);
                assert(std_from(t, p, k, j));
            }
        } else if like_mt(t, p, k, j) == Ok::<LikeRes, SqlError>(LikeRes::Match) {
            assert(std_from(t, p, k, j));
        }
    } else {
        if std_from(t, p, k, j) {
            let k2 = choose|k2: int| k <= k2 <= n && #[trigger] like_std(t, p, k2, j);
            assert(k2 == n);
        }
    }
}

/// PostgreSQL's LIKE matcher is standard LIKE matching: whenever it returns, it returns `Match` exactly for
/// the standard meaning, and without a dangling escape it always returns (never raises 22025).
pub proof fn lemma_like_mt_std(t: Seq<Seq<u8>>, p: Seq<LikeTok>)
    ensures
        like_mt(t, p, 0, 0) is Ok ==> ((like_mt(t, p, 0, 0) == Ok::<LikeRes, SqlError>(LikeRes::Match)) == like_std(t, p, 0, 0)),
        no_dangling(p) ==> like_mt(t, p, 0, 0) is Ok,
{
    lemma_mt(t, p, 0, 0);
}

/// Without an escape character (`ESCAPE ''`) the tokens have no dangling escape, so LIKE never raises 22025
/// from the matcher.
pub proof fn lemma_tokens_no_escape(pc: Seq<Seq<u8>>, k: int)
    ensures no_dangling(like_tokens(pc, None, k)),
    decreases pc.len() - k,
{
    if 0 <= k < pc.len() {
        lemma_tokens_no_escape(pc, k + 1);
        let rest = like_tokens(pc, None, k + 1);
        let r = like_tokens(pc, None, k);
        assert forall|m: int| 0 <= m < r.len() implies !(#[trigger] r[m] is Dangling) by {
            if m > 0 { assert(r[m] == rest[m - 1]); }
        }
    }
}

} // verus!
