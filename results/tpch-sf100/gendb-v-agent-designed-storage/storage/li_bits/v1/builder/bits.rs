//! Bitmap words of one predicate over frame-of-reference coded rows.
//!
//! A bitmap of `nw` words over `n <= 64 nw` rows has bit `i` of word `w` for row `j = 64 w + i`; bits of rows
//! `j >= n` are 0. Row `j`'s value is `base[g] + code[j]` for its group `g` (`gs[g] <= j < gs[g + 1]`); a word
//! whose 64 rows lie in one group compares the codes against one code-space threshold (a branch-free loop the
//! compiler vectorizes), any other word decodes row by row.
use vstd::prelude::*;
use crate::stores::facts::interface::common::colfmt as FC;
use crate::stores::li_bits::interface::bit;

verus! {

/// Setting bit `i` of `x` sets exactly that bit.
pub proof fn lemma_bit_set(x: u64, i: u64, k: u64)
    requires i < 64, k < 64,
    ensures bit(x | (1u64 << i), k as int) == (bit(x, k as int) || k == i),
{
    assert(((x | (1u64 << i)) >> k) & 1u64 == 1u64 <==> (((x >> k) & 1u64 == 1u64) || k == i)) by (bit_vector)
        requires i < 64, k < 64;
}

/// No bit of 0 is set.
pub proof fn lemma_bit_zero(k: u64)
    requires k < 64,
    ensures !bit(0u64, k as int),
{
    assert((0u64 >> k) & 1u64 != 1u64) by (bit_vector);
}

/// No bit of 0 is set (all positions).
pub proof fn lemma_zero_word()
    ensures forall|k: int| 0 <= k < 64 ==> !#[trigger] bit(0u64, k),
{
    assert forall|k: int| 0 <= k < 64 implies !#[trigger] bit(0u64, k) by {
        lemma_bit_zero(k as u64);
    }
}

/// Setting bit `i` of `x` (all positions).
pub proof fn lemma_set_word(x: u64, i: u64)
    requires i < 64,
    ensures forall|k: int| 0 <= k < 64 ==> #[trigger] bit(x | (1u64 << i), k) == (bit(x, k) || k == i),
{
    assert forall|k: int| 0 <= k < 64 implies #[trigger] bit(x | (1u64 << i), k) == (bit(x, k) || k == i) by {
        lemma_bit_set(x, i, k as u64);
    }
}

/// Row `j` of word `w`: `j / 64 == w`, `j % 64 == j - 64 w`.
pub proof fn lemma_word_row(w: int, i: int)
    requires 0 <= w, 0 <= i < 64,
    ensures (64 * w + i) / 64 == w, (64 * w + i) % 64 == i,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(64 * w + i, 64, w, i);
}

/// The per-row predicates a bitmap marks.
pub enum Pred {
    /// value == key
    Eq,
    /// value < key
    Lt,
}

/// The predicate on a value.
pub open spec fn holds(p: Pred, v: int, key: int) -> bool {
    match p {
        Pred::Eq => v == key,
        Pred::Lt => v < key,
    }
}

/// The value of row `j` in group `g`: the group's base plus the row's code.
pub open spec fn val(base: Seq<i64>, codes: Seq<u16>, g: int, j: int) -> int {
    base[g] as int + codes[j] as int
}

/// The key index of group `g`.
pub open spec fn kidx(g: int, stride: int, off: int) -> int {
    g * stride + off
}

/// Row `j` is a row (`j < n`) whose value satisfies the predicate against its group's key.
pub open spec fn row_pred(p: Pred, gs: Seq<u64>, n: int, base: Seq<i64>, codes: Seq<u16>, keys: Seq<i64>,
    stride: int, off: int, j: int) -> bool
{
    j < n && holds(p, val(base, codes, FC::group_of(gs, j), j), keys[kidx(FC::group_of(gs, j), stride, off)] as int)
}

/// Word `w` marks `row_pred` of its 64 rows.
pub open spec fn word_ok(word: u64, w: int, p: Pred, gs: Seq<u64>, n: int, base: Seq<i64>, codes: Seq<u16>,
    keys: Seq<i64>, stride: int, off: int) -> bool
{
    forall|i: int| 0 <= i < 64 ==> #[trigger] bit(word, i) == row_pred(p, gs, n, base, codes, keys, stride, off, 64 * w + i)
}

/// The inputs of a bitmap pass: groups over `n` rows, one base per group, one code per row, keys per group.
pub open spec fn pass_ok(gs: Seq<u64>, n: int, base: Seq<i64>, codes: Seq<u16>, keys: Seq<i64>, stride: int, off: int) -> bool {
    &&& FC::groups_wf(gs, n)
    &&& base.len() == gs.len() - 1
    &&& codes.len() == n
    &&& 0 <= stride && 0 <= off
    &&& forall|g: int| 0 <= g < gs.len() - 1 ==> #[trigger] kidx(g, stride, off) < keys.len()
}

/// `x` clamped into `[lo, hi]`.
pub open spec fn clamp(x: int, lo: int, hi: int) -> int {
    if x < lo { lo } else if x > hi { hi } else { x }
}

/// Word `w` (rows `j0 = 64 w .. j0 + 64`, all inside group `g`, all `< n`): compare the codes against one
/// threshold in code space (`holds(p, base + c, key)` is `c == key - base` or `c < key - base`).
fn word_in_group(p: &Pred, codes: &[u16], j0: usize, b: i64, key: i64,
    Ghost(gs): Ghost<Seq<u64>>, Ghost(n): Ghost<int>, Ghost(base): Ghost<Seq<i64>>, Ghost(keys): Ghost<Seq<i64>>,
    Ghost(stride): Ghost<int>, Ghost(off): Ghost<int>, Ghost(g): Ghost<int>) -> (word: u64)
    requires
        pass_ok(gs, n, base, codes@, keys, stride, off),
        j0 % 64 == 0,
        0 <= g < gs.len() - 1,
        gs[g] <= j0, j0 + 64 <= gs[g + 1],
        b == base[g],
        key == keys[kidx(g, stride, off)],
    ensures
        word_ok(word, j0 as int / 64, *p, gs, n, base, codes@, keys, stride, off),
{
    let ghost w = j0 as int / 64;
    proof {
        FC::lemma_groups_bounds(gs, n, g + 1);
        assert(j0 == 64 * w);
        lemma_zero_word();
    }
    let d: i128 = key as i128 - b as i128;
    let (_, c1) = codes.split_at(j0);
    let (c, _) = c1.split_at(64);
    proof {
        assert(c@ =~= codes@.subrange(j0 as int, j0 + 64));
    }
    let mut word: u64 = 0;
    let mut i: usize = 0;
    match p {
        Pred::Eq => {
            // every code is below 2^16: a key outside base + [0, 2^16) matches no row
            let thr: u32 = if d < 0 || d >= 65536 { 65536 } else { d as u32 };
            while i < 64
                invariant
                    i <= 64,
                    c@.len() == 64,
                    thr == if d < 0 || d >= 65536 { 65536 } else { d },
                    forall|k: int| 0 <= k < i ==> #[trigger] bit(word, k) == (c@[k] == d),
                    forall|k: int| i <= k < 64 ==> !#[trigger] bit(word, k),
                decreases 64 - i,
            {
                let hit = (c[i] as u32) == thr;
                proof {
                    lemma_set_word(word, i as u64);
                }
                word = if hit { word | (1u64 << i as u64) } else { word };
                i = i + 1;
            }
        }
        Pred::Lt => {
            let thr: u32 = if d < 0 { 0 } else if d > 65536 { 65536 } else { d as u32 };
            while i < 64
                invariant
                    i <= 64,
                    c@.len() == 64,
                    thr == clamp(d as int, 0, 65536),
                    forall|k: int| 0 <= k < i ==> #[trigger] bit(word, k) == (c@[k] < d),
                    forall|k: int| i <= k < 64 ==> !#[trigger] bit(word, k),
                decreases 64 - i,
            {
                let hit = (c[i] as u32) < thr;
                proof {
                    lemma_set_word(word, i as u64);
                }
                word = if hit { word | (1u64 << i as u64) } else { word };
                i = i + 1;
            }
        }
    }
    proof {
        assert forall|k: int| 0 <= k < 64 implies #[trigger] bit(word, k)
            == row_pred(*p, gs, n, base, codes@, keys, stride, off, 64 * w + k) by {
            let j = 64 * w + k;
            assert(FC::in_group(gs, g, j));
            FC::lemma_group_of_unique(gs, n, g, j);
            assert(c@[k] == codes@[j]);
        }
    }
    word
}

/// The group of row `j < n`, searched forward from `g0` (a group starting at or before row `j`).
fn advance(gs_x: &[u64], n: usize, j: usize, g0: usize) -> (g: usize)
    requires
        FC::groups_wf(gs_x@, n as int),
        j < n,
        g0 < gs_x@.len() - 1,
        gs_x@[g0 as int] <= j,
    ensures
        g0 <= g < gs_x@.len() - 1,
        FC::in_group(gs_x@, g as int, j as int),
{
    let ghost gs = gs_x@;
    let ghost nn = n as int;
    let ng = gs_x.len() - 1;
    let mut g = g0;
    while gs_x[g + 1] <= j as u64
        invariant
            gs_x@ == gs,
            ng == gs.len() - 1,
            FC::groups_wf(gs, nn),
            nn == n,
            j < n,
            g0 <= g < ng,
            gs[g as int] <= j,
        decreases ng - g,
    {
        proof {
            FC::lemma_groups_bounds(gs, nn, g + 1);
        }
        g = g + 1;
    }
    g
}

/// The key index `g * stride + off` of group `g` (inside `keys`).
fn key_index(gs_x: &[u64], keys_x: &[i64], n: usize, stride: usize, off: usize, g: usize) -> (k: usize)
    requires
        forall|h: int| 0 <= h < gs_x@.len() - 1 ==> #[trigger] kidx(h, stride as int, off as int) < keys_x@.len(),
        g < gs_x@.len() - 1,
    ensures
        k == kidx(g as int, stride as int, off as int),
        k < keys_x@.len(),
{
    let kl = keys_x.len();
    proof {
        assert(kidx(g as int, stride as int, off as int) < kl);
        assert(g * stride + off < kl);
        assert(0 <= g * stride) by (nonlinear_arith) requires 0 <= g, 0 <= stride;
    }
    g * stride + off
}

/// `row_pred` of row `j < n`, advancing the group cursor `g0` (a group starting at or before row `j`) to row
/// `j`'s group.
fn row_bit_at(p: &Pred, gs_x: &[u64], base_x: &[i64], codes: &[u16], keys_x: &[i64], stride: usize, off: usize,
    n: usize, j: usize, g0: usize) -> (r: (bool, usize))
    requires
        pass_ok(gs_x@, n as int, base_x@, codes@, keys_x@, stride as int, off as int),
        j < n,
        g0 < gs_x@.len() - 1,
        gs_x@[g0 as int] <= j,
    ensures
        r.0 == row_pred(*p, gs_x@, n as int, base_x@, codes@, keys_x@, stride as int, off as int, j as int),
        g0 <= r.1 < gs_x@.len() - 1,
        gs_x@[r.1 as int] <= j,
{
    let ghost gs = gs_x@;
    let ghost nn = n as int;
    let g = advance(gs_x, n, j, g0);
    let ki = key_index(gs_x, keys_x, n, stride, off, g);
    proof {
        FC::lemma_group_of_unique(gs, nn, g as int, j as int);
    }
    let v = base_x[g] as i128 + codes[j] as i128;
    let key = keys_x[ki];
    let hit = match p {
        Pred::Eq => v == key as i128,
        Pred::Lt => v < key as i128,
    };
    (hit, g)
}

/// Word `w` row by row (rows of any groups; rows `>= n` get 0). `g0` is a group starting at or before row `64 w`.
fn word_rows(p: &Pred, gs_x: &[u64], base_x: &[i64], codes: &[u16], keys_x: &[i64], stride: usize, off: usize,
    n: usize, j0: usize, g0: usize) -> (r: (u64, usize))
    requires
        pass_ok(gs_x@, n as int, base_x@, codes@, keys_x@, stride as int, off as int),
        j0 % 64 == 0,
        j0 < n,
        j0 + 64 <= usize::MAX,
        g0 < gs_x@.len() - 1,
        gs_x@[g0 as int] <= j0,
    ensures
        word_ok(r.0, j0 as int / 64, *p, gs_x@, n as int, base_x@, codes@, keys_x@, stride as int, off as int),
        g0 <= r.1 < gs_x@.len() - 1,
        gs_x@[r.1 as int] <= j0 + 64,
{
    let ghost w = j0 as int / 64;
    let ghost gs = gs_x@;
    proof {
        assert(j0 == 64 * w);
        lemma_zero_word();
    }
    let mut word: u64 = 0;
    let mut g: usize = g0;
    let mut i: usize = 0;
    while i < 64
        invariant
            pass_ok(gs, n as int, base_x@, codes@, keys_x@, stride as int, off as int),
            gs_x@ == gs,
            j0 == 64 * w,
            j0 < n,
            j0 + 64 <= usize::MAX,
            i <= 64,
            g0 <= g < gs.len() - 1,
            gs[g as int] <= j0 + i,
            forall|k: int| 0 <= k < i ==> #[trigger] bit(word, k)
                == row_pred(*p, gs, n as int, base_x@, codes@, keys_x@, stride as int, off as int, 64 * w + k),
            forall|k: int| i <= k < 64 ==> !#[trigger] bit(word, k),
        decreases 64 - i,
    {
        let j = j0 + i;
        proof {
            lemma_set_word(word, i as u64);
        }
        if j < n {
            let (hit, g2) = row_bit_at(p, gs_x, base_x, codes, keys_x, stride, off, n, j, g);
            g = g2;
            word = if hit { word | (1u64 << i as u64) } else { word };
        } else {
            // rows past n are not rows
            assert(!row_pred(*p, gs, n as int, base_x@, codes@, keys_x@, stride as int, off as int, 64 * w + i));
        }
        i = i + 1;
    }
    (word, g)
}

/// Word `w` (`64 w < n`): the group cursor `g` (a group starting at or before row `64 w`) moves to the group
/// of row `64 w`; a word inside that group is compared in code space, any other word row by row.
fn one_word(p: &Pred, gs_x: &[u64], base_x: &[i64], codes: &[u16], keys_x: &[i64], stride: usize, off: usize,
    n: usize, w: usize, g0: usize) -> (r: (u64, usize))
    requires
        pass_ok(gs_x@, n as int, base_x@, codes@, keys_x@, stride as int, off as int),
        64 * w < n,
        64 * w + 64 <= usize::MAX,
        g0 < gs_x@.len() - 1,
        gs_x@[g0 as int] <= 64 * w,
    ensures
        word_ok(r.0, w as int, *p, gs_x@, n as int, base_x@, codes@, keys_x@, stride as int, off as int),
        r.1 < gs_x@.len() - 1,
        gs_x@[r.1 as int] <= 64 * w + 64,
{
    let ghost gs = gs_x@;
    let ghost nn = n as int;
    let j0 = 64 * w;
    proof {
        lemma_word_row(w as int, 0);
        assert(j0 as int / 64 == w);
    }
    let g = advance(gs_x, n, j0, g0);
    let gl = gs_x.len();
    proof {
        FC::lemma_groups_bounds(gs, nn, g + 1);
        assert(g + 1 < gl);
    }
    if j0 as u64 + 64 <= gs_x[g + 1] {
        // all 64 rows in group g: one code-space threshold
        let ki = key_index(gs_x, keys_x, n, stride, off, g);
        let word = word_in_group(p, codes, j0, base_x[g], keys_x[ki], Ghost(gs), Ghost(nn),
            Ghost(base_x@), Ghost(keys_x@), Ghost(stride as int), Ghost(off as int), Ghost(g as int));
        (word, g)
    } else {
        word_rows(p, gs_x, base_x, codes, keys_x, stride, off, n, j0, g)
    }
}

/// Appends the `nw` words of the bitmap of `holds(p, value, keys[g * stride + off])` over the `n` rows.
pub fn push_bitmap(out: &mut Vec<u64>, p: &Pred, gs_x: &[u64], base_x: &[i64], codes: &[u16], keys_x: &[i64],
    stride: usize, off: usize, n: usize, nw: usize)
    requires
        pass_ok(gs_x@, n as int, base_x@, codes@, keys_x@, stride as int, off as int),
        n <= nw * 64,
        nw * 64 <= usize::MAX,
    ensures
        final(out)@.len() == old(out)@.len() + nw,
        forall|w: int| 0 <= w < old(out)@.len() ==> final(out)@[w] == old(out)@[w],
        forall|w: int| 0 <= w < nw ==> #[trigger] word_ok(final(out)@[old(out)@.len() + w], w, *p, gs_x@, n as int,
            base_x@, codes@, keys_x@, stride as int, off as int),
{
    let ghost gs = gs_x@;
    let ghost pre = out@;
    let ghost nn = n as int;
    let mut g: usize = 0;
    let mut w: usize = 0;
    proof {
        lemma_zero_word();
    }
    while w < nw
        invariant
            gs_x@ == gs,
            pass_ok(gs, nn, base_x@, codes@, keys_x@, stride as int, off as int),
            nn == n,
            n <= nw * 64,
            nw * 64 <= usize::MAX,
            w <= nw,
            n > 0 ==> g < gs.len() - 1 && gs[g as int] <= 64 * w,
            out@.len() == pre.len() + w,
            forall|k: int| 0 <= k < pre.len() ==> out@[k] == pre[k],
            forall|k: int| 0 <= k < w ==> #[trigger] word_ok(out@[pre.len() + k], k, *p, gs, nn,
                base_x@, codes@, keys_x@, stride as int, off as int),
            forall|k: int| 0 <= k < 64 ==> !#[trigger] bit(0u64, k),
        decreases nw - w,
    {
        proof {
            if n > 0 && w == 0 {
                FC::lemma_groups_bounds(gs, nn, 0);
                assert(gs[0] == 0);
            }
        }
        let word = if 64 * w >= n {
            proof {
                assert forall|k: int| 0 <= k < 64 implies #[trigger] bit(0u64, k)
                    == row_pred(*p, gs, nn, base_x@, codes@, keys_x@, stride as int, off as int, 64 * w + k) by {
                }
            }
            0u64
        } else {
            let (wd, g2) = one_word(p, gs_x, base_x, codes, keys_x, stride, off, n, w, g);
            g = g2;
            wd
        };
        let ghost before = out@;
        out.push(word);
        proof {
            assert forall|k: int| 0 <= k < w + 1 implies #[trigger] word_ok(out@[pre.len() + k], k, *p, gs, nn,
                base_x@, codes@, keys_x@, stride as int, off as int) by {
                if k < w {
                    assert(out@[pre.len() + k] == before[pre.len() + k]);
                } else {
                    assert(out@[pre.len() + k] == word);
                }
            }
        }
        w = w + 1;
    }
}

} // verus!
