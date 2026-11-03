//! Index of the selected sub rows (`nf::sub_sel`) by adsh: the list `rows` of selected sub rows in row order and a
//! chained hash index over them keyed by `text_hash(0, adsh)` (`sub_index_ok`). `sub_find` returns the selected
//! sub row of an adsh, or `NONE` exactly when there is none.
use vstd::prelude::*;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::agent::common::hash::*;
use crate::agent::common::chains::*;
use crate::agent::common::text::*;
use crate::agent::cols::*;
use crate::agent::nf::*;

verus! {

pub struct SubIndex {
    pub rows: Vec<usize>,
    pub chains: Chains,
    pub s_adsh: TextCol,
}

pub open spec fn sub_index_ok(x: &SubIndex, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& x.s_adsh@ == s_adsh_v(c)
    &&& chains_wf(&x.chains)
    &&& x.rows@.len() == x.chains.hashes@.len()
    &&& sub_rows_ok(x.rows@, x.chains.hashes@, c)
}

/// `rows` lists exactly the selected sub rows, `hashes` their adsh hashes (hidden).
#[verifier::opaque]
pub open spec fn sub_rows_ok(rows: Seq<usize>, hashes: Seq<u64>, c: Ctx) -> bool {
    &&& forall|e: int| 0 <= e < rows.len() ==> sub_sel(c, #[trigger] rows[e] as int)
        && hashes[e] == text_hash_spec(0, s_adsh(c, rows[e] as int))
    &&& forall|s: int| #[trigger] sub_sel(c, s) ==> exists|e: int| 0 <= e < rows.len() && rows[e] == s
}

/// Build the index of the sub rows with `sic BETWEEN lo AND hi`.
pub fn build_sub(k: &Cols, lo: i64, hi: i64, Ghost(c): Ghost<Ctx>) -> (x: SubIndex)
    requires cols_ok(k, c), ctx_ok(c), c.lo == lo as int, c.hi == hi as int,
    ensures sub_index_ok(&x, c),
{
    proof {
        lemma_views(c);
    }
    let m = k.s_cik.len();
    let mut rows: Vec<usize> = Vec::new();
    let mut hashes: Vec<u64> = Vec::new();
    let mut s: usize = 0;
    while s < m
        invariant
            cols_ok(k, c), ctx_ok(c), c.lo == lo as int, c.hi == hi as int, m == c.m, s <= m,
            text_wf(k.s_adsh@, c.m), k.s_sicv@.len() == m, k.s_sic@.len() == m,
            rows@.len() == hashes@.len(), rows@.len() <= s,
            forall|e: int| 0 <= e < rows@.len() ==> sub_sel(c, #[trigger] rows@[e] as int)
                && hashes@[e] == text_hash_spec(0, s_adsh(c, rows@[e] as int)) && rows@[e] < s,
            forall|t: int| 0 <= t < s && #[trigger] sub_sel(c, t) ==> exists|e: int| 0 <= e < rows@.len() && rows@[e] == t,
        decreases m - s,
    {
        let sel = k.s_sicv[s] != 0 && lo <= k.s_sic[s] as i64 && k.s_sic[s] as i64 <= hi;
        proof {
            assert(sel == sub_sel(c, s as int));
        }
        let ghost old_rows = rows@;
        if sel {
            let (a, al) = text_val(&k.s_adsh, s, Ghost(c.m));
            let h = text_hash(0, a, al);
            rows.push(s);
            hashes.push(h);
        }
        proof {
            assert forall|t: int| 0 <= t < s + 1 && #[trigger] sub_sel(c, t) implies
                exists|e: int| 0 <= e < rows@.len() && rows@[e] == t by {
                if t == s {
                    assert(rows@[rows@.len() - 1] == s);
                } else {
                    let e = choose|e: int| 0 <= e < old_rows.len() && old_rows[e] == t;
                    assert(rows@[e] == old_rows[e]);
                }
            }
        }
        s = s + 1;
    }
    proof {
        assert(k.s_adsh.offsets@.len() == k.s_adsh.offsets.len() as int);
        assert(hashes@.len() < NONE);
        reveal(sub_rows_ok);
    }
    let chains = build_chains(hashes);
    SubIndex { rows, chains, s_adsh: tc(&k.s_adsh) }
}

/// The selected sub row with adsh `a` (`al` bytes, hash `h = text_hash(0, a)`), or `NONE` when there is none.
pub fn sub_find(x: &SubIndex, a: &[u8], al: usize, h: u64, Ghost(c): Ghost<Ctx>) -> (r: usize)
    requires sub_index_ok(x, c), al == a@.len(), h == text_hash_spec(0, a@),
    ensures
        r == NONE <==> !has_sub(c, a@),
        r != NONE ==> sub_of(c, r as int, a@),
    no_unwind
{
    let ghost hs = x.chains.hashes@;
    let ghost n = hs.len() as int;
    let ghost b = bucket_of(h, x.chains.shift);
    proof {
        lemma_views(c);
        reveal(sub_rows_ok);
    }
    if !may_contain(&x.chains, h) {
        proof {
            lemma_no_sub(x, c, a@, h, n);
        }
        return NONE;
    }
    let mut e = chain_start(&x.chains, h);
    let ghost mut pos: int = 0;
    while e != NONE
        invariant
            sub_index_ok(x, c), al == a@.len(), h == text_hash_spec(0, a@), hs == x.chains.hashes@, n == hs.len(),
            text_wf(x.s_adsh@, c.m), forall|q: int| 0 <= q < n ==> (#[trigger] x.rows@[q] as int) < c.m,
            b == bucket_of(h, x.chains.shift),
            0 <= pos <= n,
            e == enc(first_of(hs, x.chains.shift, b, pos)),
            forall|q: int| 0 <= q < pos && hs[q] == h ==> s_adsh(c, #[trigger] x.rows@[q] as int) != a@,
        decreases n - pos,
    {
        proof {
            lemma_first_of(hs, x.chains.shift, b, pos);
        }
        let s = x.rows[e];
        if x.chains.hashes[e] == h {
            let (sa, sal) = text_val(&x.s_adsh, s, Ghost(c.m));
            if bytes_eq(sa, sal, a, al) {
                proof {
                    reveal(sub_rows_ok);
                    assert(sub_sel(c, x.rows@[e as int] as int));
                    assert(sub_of(c, s as int, a@));
                    assert(x.s_adsh.offsets@.len() == x.s_adsh.offsets.len() as int);
                }
                return s;
            }
        }
        let ghost e0 = e as int;
        e = chain_next(&x.chains, e);
        proof {
            assert forall|q: int| 0 <= q < e0 + 1 && hs[q] == h implies s_adsh(c, #[trigger] x.rows@[q] as int) != a@ by {
                if pos <= q < e0 {
                    assert(bucket_of(hs[q], x.chains.shift) != b);
                }
            }
            pos = e0 + 1;
        }
    }
    proof {
        lemma_first_of(hs, x.chains.shift, b, pos);
        assert forall|q: int| 0 <= q < n && hs[q] == h implies s_adsh(c, #[trigger] x.rows@[q] as int) != a@ by {
            if q >= pos {
                assert(bucket_of(hs[q], x.chains.shift) != b);
            }
        }
        lemma_no_sub(x, c, a@, h, n);
    }
    NONE
}

/// No item with hash `h` has adsh `a`: no selected sub row has adsh `a`.
proof fn lemma_no_sub(x: &SubIndex, c: Ctx, a: Seq<u8>, h: u64, n: int)
    requires
        sub_index_ok(x, c), h == text_hash_spec(0, a), n == x.chains.hashes@.len(),
        forall|q: int| 0 <= q < n && x.chains.hashes@[q] == h ==> s_adsh(c, #[trigger] x.rows@[q] as int) != a,
    ensures !has_sub(c, a),
{
    reveal(sub_rows_ok);
    if has_sub(c, a) {
        let s = choose|s: int| #[trigger] sub_of(c, s, a);
        assert(sub_sel(c, s));
        let q = choose|q: int| 0 <= q < x.rows@.len() && x.rows@[q] == s;
        assert(x.chains.hashes@[q] == h);
        assert(s_adsh(c, x.rows@[q] as int) == a);
    }
}

} // verus!
