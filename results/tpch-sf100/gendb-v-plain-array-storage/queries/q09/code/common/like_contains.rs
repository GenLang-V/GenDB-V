//! `s LIKE '%<lit>%'` (escape backslash) on an ASCII text `s` is the byte-substring test "`lit` occurs in `s`" when
//! `<lit>` is non-empty ASCII without `%`, `_` and backslash (`lemma_like_contains`), and executable searches for
//! it (`no_unwind`, usable in worker tasks): a direct scan (`has_sub_exec`) and a Horspool scan (`has_sub_skip`,
//! which after a mismatch at a window skips ahead by the distance from the window's last byte to its last
//! occurrence in `lit` before the end, `shift_ok`).
//!
//! The pattern's tokens are `%`, one literal character per byte of `lit`, `%`; the matcher (which never fails
//! without a dangling escape) is standard matching (`bridge::fns::like::lemma_like_mt_std`); a run of literal tokens
//! between two `%` matches exactly where those characters occur; and the characters of ASCII text are its bytes.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::chars::*;
use crate::spec::fns::like::*;
use crate::bridge::fns::like::{no_dangling, std_from, lemma_like_mt_std, lemma_std_any};

verus! {

// ------------------------------------------------------------------------------------------------ bytes

/// Every byte is ASCII (below 0x80): each is a character of its own.
pub open spec fn ascii(b: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < b.len() ==> #[trigger] b[i] < 0x80u8
}

/// `lit` occurs in `s` at byte `i`.
pub open spec fn sub_at(s: Seq<u8>, lit: Seq<u8>, i: int) -> bool {
    0 <= i && i + lit.len() <= s.len() && s.subrange(i, i + lit.len()) == lit
}

/// `lit` occurs in `s`.
pub open spec fn has_sub(s: Seq<u8>, lit: Seq<u8>) -> bool {
    exists|i: int| #[trigger] sub_at(s, lit, i)
}

/// `%`, then non-empty ASCII bytes that are neither `%`, `_` nor backslash, then `%`.
pub open spec fn contains_pattern(pat: Seq<u8>) -> bool {
    &&& pat.len() >= 3
    &&& pat[0] == 0x25u8
    &&& pat[pat.len() - 1] == 0x25u8
    &&& forall|i: int| 1 <= i < pat.len() - 1 ==> #[trigger] pat[i] < 0x80u8 && pat[i] != 0x25u8 && pat[i] != 0x5Fu8 && pat[i] != 0x5Cu8
}

/// The literal between the two `%` of a contains pattern.
pub open spec fn contains_lit(pat: Seq<u8>) -> Seq<u8> { pat.subrange(1, pat.len() - 1) }

// ------------------------------------------------------------------------------------------------ characters

/// The characters of ASCII bytes are the single bytes.
pub proof fn lemma_chars_ascii(b: Seq<u8>)
    requires ascii(b),
    ensures chars(b) == Seq::new(b.len(), |i: int| seq![b[i]]),
    decreases b.len(),
{
    if b.len() > 0 {
        let d = b.drop_last();
        assert(ascii(d)) by {
            assert forall|i: int| 0 <= i < d.len() implies #[trigger] d[i] < 0x80u8 by { assert(d[i] == b[i]); }
        }
        lemma_chars_ascii(d);
        assert(b[b.len() - 1] < 0x80u8);
        assert(!is_cont(b.last()));
        assert(chars(b) =~= Seq::new(b.len(), |i: int| seq![b[i]]));
    } else {
        assert(chars(b) =~= Seq::new(b.len(), |i: int| seq![b[i]]));
    }
}

/// The escape character: a backslash.
pub open spec fn backslash_char() -> Seq<u8> { seq![0x5Cu8] }

// ------------------------------------------------------------------------------------------------ tokens

/// Token `q` of a contains pattern of `m` literal characters: `%` at 0 and `m + 1`, else the literal character.
pub open spec fn ctok(pc: Seq<Seq<u8>>, m: int, q: int) -> LikeTok {
    if q == 0 || q == m + 1 { LikeTok::Any } else { LikeTok::Lit(pc[q]) }
}

/// The tokens of a contains pattern's characters from `k` (`1 <= k <= m + 2`).
proof fn lemma_tokens_from(pc: Seq<Seq<u8>>, m: int, k: int)
    requires
        pc.len() == m + 2, m >= 1, 1 <= k <= m + 2,
        pc[m + 1] == pct(),
        forall|i: int| 1 <= i <= m ==> #[trigger] pc[i] != backslash_char() && pc[i] != pct() && pc[i] != underscore(),
    ensures
        like_tokens(pc, Some(backslash_char()), k) == Seq::new((m + 2 - k) as nat, |j: int| ctok(pc, m, k + j)),
    decreases m + 2 - k,
{
    let esc = Some(backslash_char());
    if k < m + 2 {
        lemma_tokens_from(pc, m, k + 1);
        if k == m + 1 {
            assert(pc[k] != backslash_char()) by { assert(pc[k][0] == 0x25u8); }
        } else {
            assert(pc[k] != backslash_char() && pc[k] != pct() && pc[k] != underscore());
        }
        assert(like_tokens(pc, esc, k) =~= Seq::new((m + 2 - k) as nat, |j: int| ctok(pc, m, k + j)));
    } else {
        assert(like_tokens(pc, esc, k) =~= Seq::new((m + 2 - k) as nat, |j: int| ctok(pc, m, k + j)));
    }
}

// ------------------------------------------------------------------------------------------------ standard matching

/// The text from `i` matches the literal tokens `j..=m` then the final `%` exactly when the literal characters occur
/// at `i - j + 1`... i.e. the next `m + 1 - j` characters are those literals (and the rest is anything).
proof fn lemma_std_lits(t: Seq<Seq<u8>>, p: Seq<LikeTok>, m: int, i: int, j: int)
    requires
        p.len() == m + 2, m >= 1, 1 <= j <= m + 1, 0 <= i <= t.len(),
        p[m + 1] is Any,
        forall|q: int| 1 <= q <= m ==> (#[trigger] p[q]) is Lit,
    ensures
        like_std(t, p, i, j) == (i + (m + 1 - j) <= t.len()
            && forall|q: int| j <= q <= m ==> #[trigger] t[i - j + q] == p[q]->Lit_0),
    decreases m + 1 - j,
{
    if j == m + 1 {
        lemma_std_any(t, p, i, m + 1);
        if like_std(t, p, i, m + 1) {
        } else {
            assert(like_std(t, p, t.len() as int, m + 2));
            assert(std_from(t, p, i, m + 2));
        }
    } else {
        assert(p[j] is Lit);
        if i < t.len() {
            lemma_std_lits(t, p, m, i + 1, j + 1);
            if like_std(t, p, i, j) {
                assert forall|q: int| j <= q <= m implies #[trigger] t[i - j + q] == p[q]->Lit_0 by {
                    if q > j {
                        assert(t[(i + 1) - (j + 1) + q] == p[q]->Lit_0);
                    }
                }
            }
            if i + (m + 1 - j) <= t.len() && forall|q: int| j <= q <= m ==> #[trigger] t[i - j + q] == p[q]->Lit_0 {
                assert(t[i - j + j] == p[j]->Lit_0);
                assert forall|q: int| j + 1 <= q <= m implies #[trigger] t[(i + 1) - (j + 1) + q] == p[q]->Lit_0 by {
                    assert(t[i - j + q] == p[q]->Lit_0);
                }
            }
        }
    }
}

/// The literals of a contains pattern occur in `t` at character `k`.
pub open spec fn lits_at(t: Seq<Seq<u8>>, p: Seq<LikeTok>, m: int, k: int) -> bool {
    0 <= k && k + m <= t.len() && forall|q: int| 1 <= q <= m ==> #[trigger] t[k - 1 + q] == p[q]->Lit_0
}

/// `%`, literals, `%`: the text matches exactly when the literals occur at some character.
proof fn lemma_std_contains(t: Seq<Seq<u8>>, p: Seq<LikeTok>, m: int)
    requires
        p.len() == m + 2, m >= 1, p[0] is Any, p[m + 1] is Any,
        forall|q: int| 1 <= q <= m ==> (#[trigger] p[q]) is Lit,
    ensures like_std(t, p, 0, 0) == exists|k: int| #[trigger] lits_at(t, p, m, k),
{
    lemma_std_any(t, p, 0, 0);
    if like_std(t, p, 0, 0) {
        let k = choose|k: int| 0 <= k <= t.len() && #[trigger] like_std(t, p, k, 1);
        lemma_std_lits(t, p, m, k, 1);
        assert(lits_at(t, p, m, k));
    }
    if exists|k: int| #[trigger] lits_at(t, p, m, k) {
        let k = choose|k: int| #[trigger] lits_at(t, p, m, k);
        lemma_std_lits(t, p, m, k, 1);
        assert(like_std(t, p, k, 1));
        assert(std_from(t, p, 0, 1));
    }
}

// ------------------------------------------------------------------------------------------------ the theorem

/// `s LIKE pat` for a contains pattern and an ASCII text is the byte-substring test.
pub proof fn lemma_like_contains(s: Seq<u8>, pat: Seq<u8>)
    requires ascii(s), contains_pattern(pat),
    ensures
        like_value(Val::Text(s), Val::Text(pat), Val::Text(seq![92u8]))
            == Ok::<Val, SqlError>(Val::Bool(has_sub(s, contains_lit(pat)))),
{
    let lit = contains_lit(pat);
    let m = lit.len() as int;
    // the escape string is the one character backslash
    let bs = seq![92u8];
    assert(ascii(bs)) by { assert forall|i: int| 0 <= i < bs.len() implies #[trigger] bs[i] < 0x80u8 by {} }
    lemma_chars_ascii(bs);
    let ec = chars(bs);
    assert(ec =~= seq![backslash_char()]);
    assert(escape_of(ec) == Some(backslash_char()));
    // the pattern's characters and tokens
    assert(ascii(pat)) by {
        assert forall|i: int| 0 <= i < pat.len() implies #[trigger] pat[i] < 0x80u8 by {
            if 0 < i < pat.len() - 1 { assert(pat[i] < 0x80u8); }
        }
    }
    lemma_chars_ascii(pat);
    let pc = chars(pat);
    assert(pc.len() == m + 2);
    assert(pc[0] == pct()) by { assert(pc[0] =~= seq![0x25u8]); }
    assert(pc[m + 1] == pct()) by { assert(pc[m + 1] =~= seq![0x25u8]); }
    assert forall|i: int| 1 <= i <= m implies #[trigger] pc[i] != backslash_char() && pc[i] != pct() && pc[i] != underscore() by {
        assert(pc[i] == seq![pat[i]]);
        assert(pat[i] != 0x5Cu8 && pat[i] != 0x25u8 && pat[i] != 0x5Fu8);
        if pc[i] == backslash_char() { assert(pc[i][0] == 0x5Cu8); }
        if pc[i] == pct() { assert(pc[i][0] == 0x25u8); }
        if pc[i] == underscore() { assert(pc[i][0] == 0x5Fu8); }
    }
    lemma_tokens_from(pc, m, 1);
    let toks = like_tokens(pc, Some(backslash_char()), 0);
    assert(pc[0] != backslash_char()) by { assert(pc[0][0] == 0x25u8); }
    assert(toks =~= Seq::new((m + 2) as nat, |q: int| ctok(pc, m, q)));
    assert forall|q: int| 1 <= q <= m implies (#[trigger] toks[q]) is Lit && toks[q]->Lit_0 == seq![lit[q - 1]] by {
        assert(toks[q] == ctok(pc, m, q));
        assert(pc[q] == seq![pat[q]]);
        assert(lit[q - 1] == pat[q]);
    }
    assert(no_dangling(toks)) by {
        assert forall|k: int| 0 <= k < toks.len() implies !(#[trigger] toks[k] is Dangling) by {
            assert(toks[k] == ctok(pc, m, k));
        }
    }
    assert(toks[0] is Any && toks[m + 1] is Any) by {
        assert(toks[0] == ctok(pc, m, 0));
        assert(toks[m + 1] == ctok(pc, m, m + 1));
    }
    // the matcher is standard matching: `%`, the literals, `%`
    let t = chars(s);
    lemma_chars_ascii(s);
    lemma_like_mt_std(t, toks);
    lemma_std_contains(t, toks, m);
    // literal characters at character `k` are the literal bytes at byte `k`
    assert(like_std(t, toks, 0, 0) == has_sub(s, lit)) by {
        if like_std(t, toks, 0, 0) {
            let k = choose|k: int| #[trigger] lits_at(t, toks, m, k);
            assert(s.subrange(k, k + m) =~= lit) by {
                assert forall|j: int| 0 <= j < m implies s.subrange(k, k + m)[j] == lit[j] by {
                    let q = j + 1;
                    assert(t[k - 1 + q] == toks[q]->Lit_0);
                    assert(t[k + j] == seq![s[k + j]]);
                    assert(seq![s[k + j]][0] == seq![lit[j]][0]);
                }
            }
            assert(sub_at(s, lit, k));
        }
        if has_sub(s, lit) {
            let k = choose|k: int| #[trigger] sub_at(s, lit, k);
            assert forall|q: int| 1 <= q <= m implies #[trigger] t[k - 1 + q] == toks[q]->Lit_0 by {
                assert(t[k - 1 + q] == seq![s[k - 1 + q]]);
                assert(s.subrange(k, k + m)[q - 1] == lit[q - 1]);
            }
            assert(lits_at(t, toks, m, k));
        }
    }
}

// ------------------------------------------------------------------------------------------------ search

/// Whether `lit` (`m` bytes, `m >= 1`) occurs in `bytes[lo..hi]`: a scan for the first byte, then a comparison.
pub fn has_sub_exec(bytes: &[u8], lo: usize, hi: usize, lit: &Vec<u8>, m: usize) -> (r: bool)
    requires lo <= hi <= bytes@.len(), m == lit@.len(), m >= 1,
    ensures r == has_sub(bytes@.subrange(lo as int, hi as int), lit@),
    no_unwind
{
    let ghost s = bytes@.subrange(lo as int, hi as int);
    if hi - lo < m {
        proof {
            assert forall|i: int| !#[trigger] sub_at(s, lit@, i) by {}
        }
        return false;
    }
    let last = hi - m;
    let p0 = lit[0];
    let mut i = lo;
    while i <= last
        invariant
            lo <= i <= last + 1, last + m == hi, hi <= bytes@.len(), m == lit@.len(), m >= 1, p0 == lit@[0],
            s == bytes@.subrange(lo as int, hi as int),
            forall|k: int| 0 <= k < i - lo ==> !#[trigger] sub_at(s, lit@, k),
        decreases last + 1 - i,
    {
        if bytes[i] == p0 {
            let mut k: usize = 1;
            while k < m && bytes[i + k] == lit[k]
                invariant
                    1 <= k <= m, i + m <= hi, hi <= bytes@.len(), m == lit@.len(), p0 == lit@[0], bytes@[i as int] == p0,
                    forall|j: int| 0 <= j < k ==> bytes@[i + j] == #[trigger] lit@[j],
                decreases m - k,
            {
                k = k + 1;
            }
            if k == m {
                proof {
                    assert(s.subrange(i - lo, i - lo + m) =~= lit@) by {
                        assert forall|j: int| 0 <= j < m implies s.subrange(i - lo, i - lo + m)[j] == lit@[j] by {
                            assert(s[i - lo + j] == bytes@[i + j]);
                        }
                    }
                    assert(sub_at(s, lit@, i - lo));
                }
                return true;
            }
            proof {
                assert(!sub_at(s, lit@, i - lo)) by {
                    if sub_at(s, lit@, i - lo) {
                        assert(s.subrange(i - lo, i - lo + m)[k as int] == lit@[k as int]);
                        assert(s[i - lo + k] == bytes@[i + k]);
                    }
                }
            }
        } else {
            proof {
                assert(!sub_at(s, lit@, i - lo)) by {
                    if sub_at(s, lit@, i - lo) {
                        assert(s.subrange(i - lo, i - lo + m)[0] == lit@[0]);
                        assert(s[i - lo] == bytes@[i as int]);
                    }
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert forall|k: int| !#[trigger] sub_at(s, lit@, k) by {
            if sub_at(s, lit@, k) {
                assert(0 <= k < i - lo);
            }
        }
    }
    false
}

/// Whether every byte of `bytes[lo..hi]` is ASCII (the OR of the bytes is below 0x80).
pub fn ascii_exec(bytes: &[u8], lo: usize, hi: usize) -> (r: bool)
    requires lo <= hi <= bytes@.len(),
    ensures r == ascii(bytes@.subrange(lo as int, hi as int)),
    no_unwind
{
    let mut acc: u8 = 0;
    let mut i = lo;
    while i < hi
        invariant
            lo <= i <= hi, hi <= bytes@.len(),
            acc < 0x80u8 <==> forall|k: int| lo <= k < i ==> #[trigger] bytes@[k] < 0x80u8,
        decreases hi - i,
    {
        let b = bytes[i];
        proof {
            assert((acc | b) < 0x80u8 <==> (acc < 0x80u8 && b < 0x80u8)) by (bit_vector);
        }
        acc = acc | b;
        i = i + 1;
    }
    proof {
        let s = bytes@.subrange(lo as int, hi as int);
        assert(ascii(s) <==> forall|k: int| lo <= k < hi ==> #[trigger] bytes@[k] < 0x80u8) by {
            if ascii(s) {
                assert forall|k: int| lo <= k < hi implies #[trigger] bytes@[k] < 0x80u8 by { assert(s[k - lo] == bytes@[k]); }
            }
            if forall|k: int| lo <= k < hi ==> #[trigger] bytes@[k] < 0x80u8 {
                assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i] < 0x80u8 by { assert(bytes@[lo + i] < 0x80u8); }
            }
        }
    }
    acc < 0x80u8
}


// ------------------------------------------------------------------------------------------------ Horspool search

/// Skip distances of `lit` (`m = lit.len() >= 1` bytes): for every byte value `c`, `1 <= sh[c] <= m` and `c` does
/// not occur in `lit` at the positions `m - sh[c] .. m - 1` (before the last).
pub open spec fn shift_ok(lit: Seq<u8>, sh: Seq<usize>) -> bool {
    &&& sh.len() == 256
    &&& forall|c: int| 0 <= c < 256 ==> 1 <= #[trigger] sh[c] <= lit.len()
        && forall|k: int| lit.len() - 1 - sh[c] < k < lit.len() - 1 ==> lit[k] != c as u8
}

/// The skip distances of `lit`.
pub fn shift_table(lit: &Vec<u8>, m: usize) -> (sh: [usize; 256])
    requires m == lit@.len(), m >= 1,
    ensures shift_ok(lit@, sh@),
{
    let mut sh: [usize; 256] = [m; 256];
    let mut k: usize = 0;
    while k + 1 < m
        invariant
            m == lit@.len(), m >= 1, k + 1 <= m, sh@.len() == 256,
            forall|c: int| 0 <= c < 256 ==> 1 <= #[trigger] sh@[c] <= m
                && forall|kk: int| m - 1 - sh@[c] < kk < k ==> lit@[kk] != c as u8,
        decreases m - k,
    {
        let c = lit[k];
        sh[c as usize] = m - 1 - k;
        proof {
            assert forall|cc: int| 0 <= cc < 256 implies 1 <= #[trigger] sh@[cc] <= m
                && forall|kk: int| m - 1 - sh@[cc] < kk < k + 1 ==> lit@[kk] != cc as u8 by {
                if cc != c as int {
                    assert forall|kk: int| m - 1 - sh@[cc] < kk < k + 1 implies lit@[kk] != cc as u8 by {
                        if kk == k { assert(lit@[kk] == c); }
                    }
                }
            }
        }
        k = k + 1;
    }
    sh
}

/// Whether `lit` occurs in `bytes[lo..hi]`, by the Horspool scan.
pub fn has_sub_skip(bytes: &[u8], lo: usize, hi: usize, lit: &Vec<u8>, m: usize, sh: &[usize; 256]) -> (r: bool)
    requires lo <= hi <= bytes@.len(), m == lit@.len(), m >= 1, shift_ok(lit@, sh@),
    ensures r == has_sub(bytes@.subrange(lo as int, hi as int), lit@),
    no_unwind
{
    let ghost s = bytes@.subrange(lo as int, hi as int);
    if hi - lo < m {
        proof {
            assert forall|i: int| !#[trigger] sub_at(s, lit@, i) by {}
        }
        return false;
    }
    let last = hi - m;
    let lm = lit[m - 1];
    let mut i = lo;
    while i <= last
        invariant
            lo <= i, last + m == hi, hi <= bytes@.len(), m == lit@.len(), m >= 1, lm == lit@[m - 1],
            shift_ok(lit@, sh@), s == bytes@.subrange(lo as int, hi as int),
            forall|k: int| 0 <= k < i - lo ==> !#[trigger] sub_at(s, lit@, k),
        decreases last + m - i,
    {
        let c = bytes[i + m - 1];
        if c == lm {
            let mut k: usize = 0;
            while k + 1 < m && bytes[i + k] == lit[k]
                invariant
                    k + 1 <= m, i + m <= hi, hi <= bytes@.len(), m == lit@.len(),
                    forall|j: int| 0 <= j < k ==> bytes@[i + j] == #[trigger] lit@[j],
                decreases m - k,
            {
                k = k + 1;
            }
            if k + 1 == m {
                proof {
                    assert(s.subrange(i - lo, i - lo + m) =~= lit@) by {
                        assert forall|j: int| 0 <= j < m implies s.subrange(i - lo, i - lo + m)[j] == lit@[j] by {
                            assert(s[i - lo + j] == bytes@[i + j]);
                        }
                    }
                    assert(sub_at(s, lit@, i - lo));
                }
                return true;
            }
            proof {
                assert(!sub_at(s, lit@, i - lo)) by {
                    if sub_at(s, lit@, i - lo) {
                        assert(s.subrange(i - lo, i - lo + m)[k as int] == lit@[k as int]);
                        assert(s[i - lo + k] == bytes@[i + k]);
                    }
                }
            }
        } else {
            proof {
                assert(!sub_at(s, lit@, i - lo)) by {
                    if sub_at(s, lit@, i - lo) {
                        assert(s.subrange(i - lo, i - lo + m)[m - 1] == lit@[m - 1]);
                        assert(s[i - lo + m - 1] == bytes@[i + m - 1]);
                    }
                }
            }
        }
        let d = sh[c as usize];
        proof {
            // no occurrence starts strictly between i and i + d: its byte at i + m - 1 would be c before its end
            assert forall|j: int| i - lo < j < i - lo + d implies !#[trigger] sub_at(s, lit@, j) by {
                if sub_at(s, lit@, j) {
                    let kk = i - lo + m - 1 - j;
                    assert(0 <= kk < m - 1);
                    assert(s.subrange(j, j + m)[kk] == lit@[kk]);
                    assert(s[i - lo + m - 1] == bytes@[i + m - 1]);
                    assert(lit@[kk] == c);
                    assert(m - 1 - sh@[c as int] < kk);
                }
            }
        }
        if d > last - i {
            proof {
                assert forall|k: int| !#[trigger] sub_at(s, lit@, k) by {
                    if sub_at(s, lit@, k) {
                        assert(k <= last - lo);
                        if k >= i - lo { assert(k < i - lo + d); }
                    }
                }
            }
            return false;
        }
        i = i + d;
    }
    proof {
        assert forall|k: int| !#[trigger] sub_at(s, lit@, k) by {
            if sub_at(s, lit@, k) {
                assert(k <= last - lo);
            }
        }
    }
    false
}

} // verus!
