//! Index of the `sub` members (rows with `fy = $3`) by `adsh`.
//!
//! Layout: the nodes are the `sub` rows; only members are linked (`common::chain`, buckets by the top `bits` bits
//! of the adsh signature hash), and a 2^20-bit filter holds the bit of every member's hash (`common::bits`), so a
//! lookup of a non-member adsh usually ends at one cache-resident bitmap probe. A lookup compares the adsh bytes of
//! the chain's nodes, so it is exact: `Some(s)` is a member with the probed adsh, `None` proves there is none.
use vstd::prelude::*;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::gendb_entry::work::text_bytes;
use crate::agent::common::bytes::*;
use crate::agent::common::chain::*;
use crate::agent::common::bits::*;
use crate::agent::ctx::*;

verus! {

/// Bits of the member filter.
pub const SUB_FILTER_BITS: u64 = 20;

pub struct SubIdx {
    pub adsh: TextCol,
    pub m: usize,
    pub head: Vec<usize>,
    pub next: Vec<usize>,
    pub shift: u64,
    pub filter: Vec<u64>,
    pub fshift: u64,
}

pub open spec fn sub_in(c: Ctx) -> spec_fn(int) -> bool {
    |s: int| member(c, s)
}

pub open spec fn sub_bkt(c: Ctx, shift: u64) -> spec_fn(int) -> int {
    |s: int| (sig_spec(s_adsh(c, s)) >> shift) as int
}

/// The index is well formed for the call context `c`.
pub open spec fn sub_idx_wf(x: SubIdx, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& x.adsh@ == s_adsh_v(c)
    &&& x.m as int == c.m
    &&& x.next@.len() == c.m
    &&& 1 <= 64 - x.shift <= 30
    &&& x.head@.len() == pow2_64(64 - x.shift)
    &&& x.fshift == 64 - SUB_FILTER_BITS
    &&& x.filter@.len() * 64 == pow2_64(SUB_FILTER_BITS as int)
    &&& chain_wf(x.head@, x.next@, sub_in(c), sub_bkt(c, x.shift), c.m)
    &&& filter_wf(x.filter@, sub_in(c), sub_bkt(c, x.fshift), c.m)
}

/// `2^b` for `0 <= b < 64`.
pub open spec fn pow2_64(b: int) -> int
    decreases b,
{
    if b <= 0 { 1 } else { 2 * pow2_64(b - 1) }
}

/// The top `b` bits of a hash index a table of `2^b` slots.
pub proof fn lemma_top_bits(h: u64, sh: u64, b: u64)
    requires 1 <= b <= 30, sh == 64 - b,
    ensures
        ((h >> sh) as int) < pow2_64(b as int),
        pow2_64(b as int) == ((1u64 << b) as int),
        pow2_64(b as int) <= 0x4000_0000 < usize::MAX,
        (h >> sh) as usize as int == (h >> sh) as int,
{
    assert(usize::MAX >= 0xffff_ffff);
    lemma_pow2_le(b as int);
    lemma_pow2_shift(b);
    assert(h >> sh < (1u64 << b)) by (bit_vector) requires 1 <= b <= 40, sh == 64 - b;
}

pub proof fn lemma_pow2_le(b: int)
    requires 0 <= b <= 30,
    ensures 1 <= pow2_64(b) <= pow2_64(30), pow2_64(30) == 0x4000_0000,
    decreases 30 - b,
{
    assert(pow2_64(30) == 0x4000_0000) by (compute);
    if b < 30 {
        lemma_pow2_le(b + 1);
    }
}

pub proof fn lemma_pow2_shift(b: u64)
    requires b <= 40,
    ensures pow2_64(b as int) == (1u64 << b) as int,
    decreases b,
{
    if b > 0 {
        lemma_pow2_shift((b - 1) as u64);
        let b1 = (b - 1) as u64;
        assert((1u64 << b) == 2 * (1u64 << b1)) by (bit_vector) requires 1 <= b <= 40, b1 == b - 1;
    } else {
        assert((1u64 << 0u64) == 1) by (bit_vector);
    }
}

/// The bytes of text value `i` of a well-formed column.
#[inline(always)]
pub fn text_of(t: &TextCol, i: usize, Ghost(n): Ghost<int>) -> (r: &'static [u8])
    requires text_wf(t@, n), i < n,
    ensures r@ == text_at(t@, i as int),
    no_unwind
{
    proof {
        assert(0 <= t@.offsets[i as int] <= t@.offsets[i + 1] <= t@.bytes.len());
    }
    text_bytes(t, i)
}

/// The length of text value `i` of a well-formed column.
#[inline(always)]
pub fn text_len(t: &TextCol, i: usize, Ghost(n): Ghost<int>) -> (r: usize)
    requires text_wf(t@, n), i < n,
    ensures r as int == text_at(t@, i as int).len(),
    no_unwind
{
    proof {
        assert(0 <= t@.offsets[i as int] <= t@.offsets[i + 1] <= t@.bytes.len());
    }
    let a = t.offsets[i];
    let b = t.offsets[i + 1];
    proof {
        assert(t.bytes@.len() == t.bytes.len() as int);
    }
    (b - a) as usize
}

/// Bucket-count exponent: about twice `n` buckets, between 2^4 and 2^27.
pub fn bits_for(n: usize) -> (r: u64)
    ensures 4 <= r <= 27,
{
    let mut bits: u64 = 4;
    while bits < 27 && (1usize << bits) / 2 < n
        invariant 4 <= bits <= 27,
        decreases 27 - bits,
    {
        bits = bits + 1;
    }
    bits
}

/// Build the index of the members of `sub` (`m` rows).
pub fn build_sub(adsh: TextCol, fy: &'static [i32], fyv: &'static [u8], m: usize, p2: i64, Ghost(c): Ghost<Ctx>) -> (x: SubIdx)
    requires
        ctx_ok(c),
        adsh@ == s_adsh_v(c),
        fy@ == s_fy_s(c),
        fyv@ == s_fyv_s(c),
        m as int == c.m,
        p2 as int == c.fy,
        m < NONE,
    ensures sub_idx_wf(x, c),
{
    proof {
        lemma_views_wf(c);
    }
    let bits = bits_for(m / 4 + 16);
    let shift: u64 = 64 - bits;
    proof {
        lemma_pow2_shift(bits);
        lemma_pow2_shift(SUB_FILTER_BITS);
        lemma_pow2_shift(14u64);
        assert((1u64 << 20u64) == 64 * (1u64 << 14u64)) by (bit_vector);
    }
    let nb: usize = 1usize << bits;
    let fshift: u64 = 64 - SUB_FILTER_BITS;
    let nw: usize = 1usize << 14usize;
    proof {
        assert(nb as int == ((1u64 << bits) as int)) by (bit_vector) requires 4 <= bits <= 30, nb == 1usize << bits;
        assert(nw as int == ((1u64 << 14u64) as int)) by (bit_vector) requires nw == 1usize << 14usize;
    }
    let mut head: Vec<usize> = vec![NONE; nb];
    let mut next: Vec<usize> = vec![NONE; m];
    let mut filter: Vec<u64> = vec![0u64; nw];
    let ghost inset = sub_in(c);
    let ghost bkt = sub_bkt(c, shift);
    let ghost fb = sub_bkt(c, fshift);
    proof {
        lemma_empty(head@, next@, inset, bkt);
    }
    let mut s: usize = 0;
    while s < m
        invariant
            ctx_ok(c), adsh@ == s_adsh_v(c), fy@ == s_fy_s(c), fyv@ == s_fyv_s(c), m as int == c.m, p2 as int == c.fy,
            m < NONE, s <= m,
            text_wf(s_adsh_v(c), c.m), fy@.len() == m, fyv@.len() == m,
            inset == sub_in(c), bkt == sub_bkt(c, shift), fb == sub_bkt(c, fshift),
            shift == 64 - bits, 4 <= bits <= 30, fshift == 64 - SUB_FILTER_BITS,
            head@.len() == nb, nb as int == pow2_64(bits as int), next@.len() == m,
            filter@.len() == nw, 64 * nw == pow2_64(SUB_FILTER_BITS as int),
            chain_wf(head@, next@, inset, bkt, s as int),
            filter_wf(filter@, inset, fb, s as int),
        decreases m - s,
    {
        if fyv[s] != 0 && fy[s] as i64 == p2 {
            let a = text_of(&adsh, s, Ghost(c.m));
            let alen = text_len(&adsh, s, Ghost(c.m));
            let h = sig(a, alen);
            proof {
                lemma_top_bits(h, shift, bits);
                lemma_top_bits(h, fshift, SUB_FILTER_BITS);
                assert(member(c, s as int));
            }
            let b = (h >> shift) as usize;
            let f = (h >> fshift) as usize;
            let ghost f0 = filter@;
            set_bit(&mut filter, f, Ghost(nw as int));
            proof {
                assert(a@ == s_adsh(c, s as int));
                assert(fb(s as int) == f as int);
                assert(bkt(s as int) == b as int);
                assert forall|x: int| 0 <= x < s + 1 && #[trigger] inset(x) implies bit_set(filter@, fb(x)) by {
                    if x < s {
                        assert(bit_set(f0, fb(x)));
                    }
                }
                lemma_insert(head@, next@, inset, bkt, s as int, b as int);
            }
            let hb = head[b];
            next[s] = hb;
            head[b] = s;
        } else {
            proof {
                assert(!member(c, s as int));
                lemma_skip(head@, next@, inset, bkt, s as int);
            }
        }
        s = s + 1;
    }
    SubIdx { adsh, m, head, next, shift, filter, fshift }
}

/// The member with adsh `key` (`klen` bytes, signature hash `h`), if any.
pub fn sub_find_h(x: &SubIdx, key: &[u8], klen: usize, h: u64, Ghost(c): Ghost<Ctx>) -> (r: usize)
    requires sub_idx_wf(*x, c), klen == key@.len(), h == sig_spec(key@),
    ensures
        r != NONE ==> member(c, r as int) && s_adsh(c, r as int) == key@,
        r == NONE ==> !has_member(c, key@),
    no_unwind
{
    proof {
        lemma_views_wf(c);
    }
    let bits: u64 = 64 - x.shift;
    proof {
        lemma_top_bits(h, x.shift, bits);
        lemma_top_bits(h, x.fshift, SUB_FILTER_BITS);
    }
    let f = (h >> x.fshift) as usize;
    let ghost inset = sub_in(c);
    let ghost bkt = sub_bkt(c, x.shift);
    let ghost fb = sub_bkt(c, x.fshift);
    let nw = x.filter.len();
    if !test_bit(&x.filter, f, Ghost(nw as int)) {
        proof {
            assert forall|s: int| #[trigger] member(c, s) implies s_adsh(c, s) != key@ by {
                if s_adsh(c, s) == key@ {
                    assert(inset(s));
                    assert(bit_set(x.filter@, fb(s)));
                }
            }
        }
        return NONE;
    }
    let b = (h >> x.shift) as usize;
    let ghost p = |y: int| s_adsh(c, y) != key@;
    let mut cur = x.head[b];
    proof {
        lemma_walk_start(x.head@, x.next@, inset, bkt, c.m, b as int, p);
    }
    while cur != NONE
        invariant
            sub_idx_wf(*x, c), klen == key@.len(), text_wf(s_adsh_v(c), c.m),
            inset == sub_in(c), bkt == sub_bkt(c, x.shift), p == (|y: int| s_adsh(c, y) != key@),
            b as int == (sig_spec(key@) >> x.shift) as int,
            walk_ok(cur, inset, bkt, c.m, b as int, p),
        decreases if cur == NONE { 0 } else { cur + 1 },
    {
        let a = text_of(&x.adsh, cur, Ghost(c.m));
        let alen = text_len(&x.adsh, cur, Ghost(c.m));
        if text_same(a, alen, key, klen) {
            return cur;
        }
        proof {
            lemma_walk_step(x.head@, x.next@, inset, bkt, c.m, b as int, p, cur);
        }
        cur = x.next[cur];
    }
    proof {
        lemma_walk_done(inset, bkt, c.m, b as int, p);
        assert forall|s: int| #[trigger] member(c, s) implies s_adsh(c, s) != key@ by {
            if s_adsh(c, s) == key@ {
                assert(inset(s));
                assert(bkt(s) == b as int);
            }
        }
    }
    NONE
}

/// The member with adsh `key` (`klen` bytes), if any.
pub fn sub_find(x: &SubIdx, key: &[u8], klen: usize, Ghost(c): Ghost<Ctx>) -> (r: usize)
    requires sub_idx_wf(*x, c), klen == key@.len(),
    ensures
        r != NONE ==> member(c, r as int) && s_adsh(c, r as int) == key@,
        r == NONE ==> !has_member(c, key@),
    no_unwind
{
    let h = sig(key, klen);
    sub_find_h(x, key, klen, h, Ghost(c))
}

/// Whether a member may have an adsh of hash `h` (the filter bit): `false` proves that none has.
#[inline(always)]
pub fn sub_maybe(x: &SubIdx, h: u64, Ghost(c): Ghost<Ctx>) -> (r: bool)
    requires sub_idx_wf(*x, c),
    ensures !r ==> forall|s: int| #[trigger] member(c, s) ==> sig_spec(s_adsh(c, s)) != h,
    no_unwind
{
    proof {
        lemma_top_bits(h, x.fshift, SUB_FILTER_BITS);
    }
    let f = (h >> x.fshift) as usize;
    let nw = x.filter.len();
    let r = test_bit(&x.filter, f, Ghost(nw as int));
    proof {
        assert forall|s: int| #[trigger] member(c, s) implies sig_spec(s_adsh(c, s)) != h || r by {
            if sig_spec(s_adsh(c, s)) == h {
                assert(sub_in(c)(s));
                assert(bit_set(x.filter@, sub_bkt(c, x.fshift)(s)));
            }
        }
    }
    r
}

/// Text value `i` of a well-formed column equals `key` (`klen` bytes); the length is compared first.
#[inline(always)]
pub fn text_is(t: &TextCol, i: usize, Ghost(n): Ghost<int>, key: &[u8], klen: usize) -> (r: bool)
    requires text_wf(t@, n), i < n, klen == key@.len(),
    ensures r == (text_at(t@, i as int) == key@),
    no_unwind
{
    let l = text_len(t, i, Ghost(n));
    if l != klen {
        return false;
    }
    let b = text_of(t, i, Ghost(n));
    bytes_eq(b, key, klen)
}

} // verus!
