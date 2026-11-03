//! Glue between the phases' outputs and the statement's normal form.
//! - `cnt(f, a, b)`: the number of rows `r` of `a .. b` with `f(r)`, and its laws (split, extensionality,
//!   disjoint union, bounds, witnesses);
//! - per orders row: the matcher's outcome on its characters (`like_r`, `err_r`) and how the phase-1 flag relates to
//!   it (`lemma_rflag`): `FLAG_LIKE` matches, `FLAG_NO` neither matches nor raises, `FLAG_ERR` raises, and the
//!   undecided `FLAG_DEFER` rows are decided later;
//! - the counts of a key in the phase-1 outputs (`lemma_lkeys_cnt`, `lemma_lrows_cnt`, `lemma_drows_cnt`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::stores::factext_trislice::interface::trisig::sig_of;
use super::like::*;
use super::scan::*;
use super::count::*;

verus! {

// ------------------------------------------------------------------------------------------------ counting

/// Rows `r` of `a .. b` with `f(r)`.
pub open spec fn cnt(f: spec_fn(int) -> bool, a: int, b: int) -> nat
    decreases b - a,
{
    if b <= a { 0 } else { cnt(f, a, b - 1) + if f(b - 1) { 1nat } else { 0nat } }
}

/// The condition `f(i) == c` (a named closure, so every use is the same term).
pub open spec fn veq(f: spec_fn(int) -> int, c: int) -> spec_fn(int) -> bool {
    |i: int| f(i) == c
}

/// Rows `i` of `a .. b` whose value `f(i)` is `c`.
pub open spec fn vcount(f: spec_fn(int) -> int, c: int, a: int, b: int) -> nat {
    cnt(veq(f, c), a, b)
}

/// The conjunction of two conditions.
pub open spec fn and_p(f: spec_fn(int) -> bool, g: spec_fn(int) -> bool) -> spec_fn(int) -> bool {
    |i: int| f(i) && g(i)
}

/// A count of a conjunction is at most the count of one conjunct.
pub proof fn lemma_cnt_and_le(f: spec_fn(int) -> bool, g: spec_fn(int) -> bool, a: int, b: int)
    requires a <= b,
    ensures cnt(and_p(f, g), a, b) <= cnt(g, a, b),
    decreases b - a,
{
    if b > a {
        lemma_cnt_and_le(f, g, a, b - 1);
    }
}

/// A row with value `c` makes the value count positive.
pub proof fn lemma_vcount_at(f: spec_fn(int) -> int, c: int, a: int, b: int, i: int)
    requires a <= i < b, f(i) == c,
    ensures vcount(f, c, a, b) > 0,
{
    lemma_cnt_at(veq(f, c), a, b, i);
}

/// A positive value count has a witness row.
pub proof fn lemma_vcount_pos(f: spec_fn(int) -> int, c: int, a: int, b: int) -> (i: int)
    requires vcount(f, c, a, b) > 0,
    ensures a <= i < b, f(i) == c,
{
    lemma_cnt_pos(veq(f, c), a, b);
    let i = choose|i: int| a <= i < b && #[trigger] veq(f, c)(i);
    i
}

/// Counts over adjacent ranges add.
pub proof fn lemma_cnt_split(f: spec_fn(int) -> bool, a: int, m: int, b: int)
    requires a <= m <= b,
    ensures cnt(f, a, b) == cnt(f, a, m) + cnt(f, m, b),
    decreases b - m,
{
    if b > m {
        lemma_cnt_split(f, a, m, b - 1);
    }
}

/// Counts of pointwise equal conditions are equal.
pub proof fn lemma_cnt_ext(f: spec_fn(int) -> bool, g: spec_fn(int) -> bool, a: int, b: int)
    requires forall|r: int| a <= r < b ==> #[trigger] f(r) == g(r),
    ensures cnt(f, a, b) == cnt(g, a, b),
    decreases b - a,
{
    if b > a {
        lemma_cnt_ext(f, g, a, b - 1);
    }
}

/// The count of a disjoint union is the sum of the counts.
pub proof fn lemma_cnt_or(f: spec_fn(int) -> bool, g: spec_fn(int) -> bool, h: spec_fn(int) -> bool, a: int, b: int)
    requires forall|r: int| a <= r < b ==> #[trigger] h(r) == (f(r) || g(r)) && !(f(r) && g(r)),
    ensures cnt(h, a, b) == cnt(f, a, b) + cnt(g, a, b),
    decreases b - a,
{
    if b > a {
        lemma_cnt_or(f, g, h, a, b - 1);
    }
}

/// A count is at most the number of rows.
pub proof fn lemma_cnt_le(f: spec_fn(int) -> bool, a: int, b: int)
    requires a <= b,
    ensures cnt(f, a, b) <= b - a,
    decreases b - a,
{
    if b > a {
        lemma_cnt_le(f, a, b - 1);
    }
}

/// A positive count has a witness.
pub proof fn lemma_cnt_pos(f: spec_fn(int) -> bool, a: int, b: int)
    requires cnt(f, a, b) > 0,
    ensures exists|r: int| a <= r < b && #[trigger] f(r),
    decreases b - a,
{
    if b > a && !f(b - 1) {
        lemma_cnt_pos(f, a, b - 1);
    }
}

/// A row satisfying the condition makes the count positive.
pub proof fn lemma_cnt_at(f: spec_fn(int) -> bool, a: int, b: int, i: int)
    requires a <= i < b, f(i),
    ensures cnt(f, a, b) > 0,
{
    lemma_cnt_split(f, a, i + 1, b);
    lemma_cnt_split(f, a, i, i + 1);
}

/// No row satisfies the condition: the count is zero.
pub proof fn lemma_cnt_zero(f: spec_fn(int) -> bool, a: int, b: int)
    requires forall|r: int| a <= r < b ==> !#[trigger] f(r),
    ensures cnt(f, a, b) == 0,
    decreases b - a,
{
    if b > a {
        lemma_cnt_zero(f, a, b - 1);
    }
}

// ------------------------------------------------------------------------------------------------ named conditions

/// o_custkey of a row through the facts key index (as a function).
pub open spec fn okf(x: ScanCtx) -> spec_fn(int) -> int {
    |r: int| okey(x, r)
}

/// A key column as a function.
pub open spec fn kcf(keys: Seq<i64>) -> spec_fn(int) -> int {
    |r: int| keys[r] as int
}

/// Flag `FLAG_LIKE` and key `v`.
pub open spec fn pr_lk(x: ScanCtx, kf: spec_fn(int) -> int, v: int) -> spec_fn(int) -> bool {
    |q: int| rflag(x, q) == FLAG_LIKE && kf(q) == v
}

/// Flag `FLAG_DEFER`, the row matches, and key `v`.
pub open spec fn pr_dlk(x: ScanCtx, kf: spec_fn(int) -> int, v: int) -> spec_fn(int) -> bool {
    |q: int| rflag(x, q) == FLAG_DEFER && like_r(x, q) && kf(q) == v
}

/// Flag `FLAG_ERR`.
pub open spec fn pr_err(x: ScanCtx) -> spec_fn(int) -> bool {
    |q: int| rflag(x, q) == FLAG_ERR
}

/// Flag `FLAG_DEFER` and the matcher raises.
pub open spec fn pr_derr(x: ScanCtx) -> spec_fn(int) -> bool {
    |q: int| rflag(x, q) == FLAG_DEFER && err_r(x, q)
}

/// The row matches and has key `v`.
pub open spec fn pr_like(x: ScanCtx, kf: spec_fn(int) -> int, v: int) -> spec_fn(int) -> bool {
    |q: int| like_r(x, q) && kf(q) == v
}

/// The matcher raises on the row.
pub open spec fn pr_e(x: ScanCtx) -> spec_fn(int) -> bool {
    |q: int| err_r(x, q)
}

/// Flag `FLAG_DEFER` and condition `p`.
pub open spec fn pr_def(x: ScanCtx, p: spec_fn(int) -> bool) -> spec_fn(int) -> bool {
    |r: int| rflag(x, r) == FLAG_DEFER && p(r)
}

// ------------------------------------------------------------------------------------------------ key lists

/// Occurrences of `v` in a list depend only on its prefix.
pub proof fn lemma_cnt_seq_prefix(s: Seq<i64>, t: Seq<i64>, v: int, m: int)
    requires 0 <= m, m <= s.len(), m <= t.len(), forall|i: int| 0 <= i < m ==> s[i] == t[i],
    ensures cnt_seq(s, v, m) == cnt_seq(t, v, m),
    decreases m,
{
    if m > 0 {
        lemma_cnt_seq_prefix(s, t, v, m - 1);
    }
}

/// Occurrences of `v` in a list with one more element.
pub proof fn lemma_cnt_seq_push(s: Seq<i64>, x: i64, v: int)
    ensures cnt_seq(s.push(x), v, s.len() as int + 1) == cnt_seq(s, v, s.len() as int) + if x == v { 1nat } else { 0nat },
{
    lemma_cnt_seq_prefix(s.push(x), s, v, s.len() as int);
}

/// The occurrences of `v` among the keys of the `FLAG_LIKE` rows of `a .. b`.
pub proof fn lemma_lkeys_cnt(x: ScanCtx, a: int, b: int, v: int)
    requires
        a <= b,
        forall|r: int| a <= r < b ==> i64::MIN <= #[trigger] okey(x, r) <= i64::MAX,
    ensures
        cnt_seq(lkeys(x, a, b), v, lkeys(x, a, b).len() as int) == cnt(pr_lk(x, okf(x), v), a, b),
    decreases b - a,
{
    if b > a {
        lemma_lkeys_cnt(x, a, b - 1, v);
        if rflag(x, b - 1) == FLAG_LIKE {
            assert(i64::MIN <= okey(x, b - 1) <= i64::MAX);
            lemma_cnt_seq_push(lkeys(x, a, b - 1), okey(x, b - 1) as i64, v);
        }
    }
}

/// The keys `keyc[r]` of the `FLAG_LIKE` rows of `a .. b` (row mode).
pub open spec fn map_keys(rows: Seq<usize>, keyc: Seq<i64>) -> Seq<i64> {
    Seq::new(rows.len(), |q: int| keyc[rows[q] as int])
}

/// The occurrences of `v` among the row-mode keys of the `FLAG_LIKE` rows of `a .. b`.
pub proof fn lemma_lrows_cnt(x: ScanCtx, keyc: Seq<i64>, a: int, b: int, v: int)
    requires 0 <= a <= b <= usize::MAX,
    ensures
        cnt_seq(map_keys(lrows(x, a, b), keyc), v, lrows(x, a, b).len() as int)
            == cnt(pr_lk(x, kcf(keyc), v), a, b),
    decreases b - a,
{
    if b > a {
        lemma_lrows_cnt(x, keyc, a, b - 1, v);
        let s = map_keys(lrows(x, a, b - 1), keyc);
        if rflag(x, b - 1) == FLAG_LIKE {
            assert(map_keys(lrows(x, a, b), keyc) =~= s.push(keyc[b - 1]));
            lemma_cnt_seq_push(s, keyc[b - 1], v);
        } else {
            assert(map_keys(lrows(x, a, b), keyc) =~= s);
        }
    }
}

/// The deferred rows `drows(a, b)` satisfying `p` (over a list prefix `0 .. m`).
pub open spec fn cnt_list(s: Seq<usize>, p: spec_fn(int) -> bool, m: int) -> nat
    decreases m,
{
    if m <= 0 { 0 } else { cnt_list(s, p, m - 1) + if p(s[m - 1] as int) { 1nat } else { 0nat } }
}

/// List counts depend only on the prefix.
pub proof fn lemma_cnt_list_prefix(s: Seq<usize>, t: Seq<usize>, p: spec_fn(int) -> bool, m: int)
    requires 0 <= m, m <= s.len(), m <= t.len(), forall|i: int| 0 <= i < m ==> s[i] == t[i],
    ensures cnt_list(s, p, m) == cnt_list(t, p, m),
    decreases m,
{
    if m > 0 {
        lemma_cnt_list_prefix(s, t, p, m - 1);
    }
}

/// The deferred rows of `a .. b` satisfying `p` are counted by `cnt` over the rows.
pub proof fn lemma_drows_cnt(x: ScanCtx, p: spec_fn(int) -> bool, a: int, b: int)
    requires 0 <= a <= b <= usize::MAX,
    ensures
        cnt_list(drows(x, a, b), p, drows(x, a, b).len() as int) == cnt(pr_def(x, p), a, b),
        forall|q: int| 0 <= q < drows(x, a, b).len() ==> a <= #[trigger] drows(x, a, b)[q] < b,
    decreases b - a,
{
    if b > a {
        lemma_drows_cnt(x, p, a, b - 1);
        let s = drows(x, a, b - 1);
        if rflag(x, b - 1) == FLAG_DEFER {
            let t = s.push((b - 1) as usize);
            lemma_cnt_list_prefix(t, s, p, s.len() as int);
            assert forall|q: int| 0 <= q < t.len() implies a <= #[trigger] t[q] < b by {
                if q < s.len() { assert(t[q] == s[q]); }
            }
        }
    }
}

/// `nerr` is a count.
pub proof fn lemma_nerr_cnt(x: ScanCtx, a: int, b: int)
    requires a <= b,
    ensures nerr(x, a, b) == cnt(pr_err(x), a, b),
    decreases b - a,
{
    if b > a {
        lemma_nerr_cnt(x, a, b - 1);
    }
}

// ------------------------------------------------------------------------------------------------ flags

/// The matcher matches the characters of row `r`'s text.
pub open spec fn like_r(x: ScanCtx, r: int) -> bool {
    like_mt(chars(rtext(x, r)), x.p, 0, 0) == Ok::<LikeRes, SqlError>(LikeRes::Match)
}

/// The matcher raises on the characters of row `r`'s text.
pub open spec fn err_r(x: ScanCtx, r: int) -> bool {
    like_mt(chars(rtext(x, r)), x.p, 0, 0) is Err
}

/// Some code is a dangling escape.
pub open spec fn has_dang(codes: Seq<u16>) -> bool {
    exists|j: int| 0 <= j < codes.len() && #[trigger] codes[j] == TOK_DANGLING
}

/// The signatures are the texts' and the needed bits are the pattern's (none with a dangling escape).
pub open spec fn sigs_match(x: ScanCtx, n: int) -> bool {
    &&& codes_ok(x.codes, x.p)
    &&& x.need0 == (if has_dang(x.codes) { 0u64 } else { need_of(x.codes, 0) })
    &&& x.need1 == (if has_dang(x.codes) { 0u64 } else { need_of(x.codes, 1) })
    &&& x.sig.len() == 2 * n
    &&& forall|r: int| 0 <= r < n ==> x.sig[2 * r] == sig_of(#[trigger] rtext(x, r), 0) && x.sig[2 * r + 1] == sig_of(rtext(x, r), 1)
}

/// What a phase-1 flag says about the matcher on the row's characters.
pub proof fn lemma_rflag(x: ScanCtx, n: int, r: int)
    requires sigs_match(x, n), 0 <= r < n,
    ensures
        rflag(x, r) == FLAG_LIKE ==> like_r(x, r),
        rflag(x, r) == FLAG_NO ==> !like_r(x, r) && !err_r(x, r),
        rflag(x, r) == FLAG_ERR ==> err_r(x, r) && !like_r(x, r),
        rflag(x, r) == FLAG_LIKE || rflag(x, r) == FLAG_NO || rflag(x, r) == FLAG_ERR || rflag(x, r) == FLAG_DEFER,
{
    let t = rtext(x, r);
    let (s0, s1) = (x.sig[2 * r], x.sig[2 * r + 1]);
    assert(s0 == sig_of(t, 0) && s1 == sig_of(t, 1));
    if rejects(s0, s1, x.need0, x.need1) {
        if has_dang(x.codes) {
            assert(s0 & 0u64 == 0u64 && s1 & 0u64 == 0u64) by (bit_vector);
        } else {
            assert forall|j: int| 0 <= j < x.codes.len() implies #[trigger] x.codes[j] != TOK_DANGLING by {}
            lemma_no_dangling(x.codes, x.p);
            lemma_reject(t, x.codes, x.p);
        }
    } else if is_ascii(t) {
        lemma_ascii_chars(t);
    }
}

} // verus!
