//! Builder of storage `li_okmode`: two passes over facts' stored lineitem rows (read from storage li_okruns'
//! inherited parts) build `nw = ceil(n / 64)` words per bitmap:
//! - the run-start bitmap: row `j` is set when `j == 0` or its l_orderkey differs from row `j - 1`'s;
//! - one l_shipmode bitmap per dictionary entry `k < nm`: row `j` is set when its dictionary index is `k`.
//! Each pass walks the rows in order with the row group tracked incrementally (`g * bs <= j < g * bs + bs`, so the
//! group base of row `j` is entry `g`, no division per row). Fallback (no rows, 2^30 rows or more, column parts shorter than the row
//! count, more than 64 l_shipmode entries): layout `[0, 0]` and empty bitmaps, which satisfy the same relation.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view, owned_part_view};
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::work::filled;
use crate::gendb_entry::{sources_ready, sources_bound, storage_parts};
use crate::spec::value::{Database, Row};
use crate::stores::facts::interface as F;
use crate::stores::li_okruns::interface as LR;
use crate::stores::li_okmode::interface as M;
use F::common::colfmt::{u8s, u32s, u64s, i64s};

verus! {

// ------------------------------------------------------------------------------------------------ sources

/// The kinds of the inherited parts the builder reads (from facts' `represents`).
pub open spec fn src_ok(p: Seq<PartView>) -> bool {
    &&& p.len() == LR::LI_OKRUNS_PARTS
    &&& p[F::LI_LAYOUT as int] is U64 && u64s(p[F::LI_LAYOUT as int]).len() == 2
    &&& p[F::LI_ORDERKEY_CODES as int] is U32
    &&& p[F::LI_ORDERKEY_BASE as int] is I64
    &&& p[F::LI_SHIPMODE_CODES as int] is U8
    &&& p[F::LI_SHIPMODE_BASE as int] is U64
    &&& p[F::LI_SHIPMODE_DICT_OFFS as int] is U64
}

/// The kinds, from facts' `represents` over the first 75 parts.
proof fn lemma_kinds(p: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires
        p.len() == LR::LI_OKRUNS_PARTS,
        F::represents(p.subrange(0, F::FACTS_PARTS as int), rels),
    ensures src_ok(p),
{
    let fp = p.subrange(0, F::FACTS_PARTS as int);
    let tp = fp.subrange(F::LINEITEM_FIRST as int, (F::LINEITEM_FIRST + F::LI_PARTS) as int);
    assert(F::lineitem_ok(tp, rels[0]));
    let rows = F::lineitem_rows(tp, rels[0]);
    assert(F::lineitem_cols_ok(tp, rows));
    assert(tp[F::LI_LAYOUT as int] == p[F::LI_LAYOUT as int]);
    assert(tp[F::LI_ORDERKEY_CODES as int] == p[F::LI_ORDERKEY_CODES as int]);
    assert(tp[F::LI_ORDERKEY_BASE as int] == p[F::LI_ORDERKEY_BASE as int]);
    assert(tp[F::LI_SHIPMODE_CODES as int] == p[F::LI_SHIPMODE_CODES as int]);
    assert(tp[F::LI_SHIPMODE_BASE as int] == p[F::LI_SHIPMODE_BASE as int]);
    assert(tp[F::LI_SHIPMODE_DICT_OFFS as int] == p[F::LI_SHIPMODE_DICT_OFFS as int]);
}

/// li_okmode's stored relations are li_okruns' (the same declaration).
proof fn lemma_same_relations(db: Database)
    ensures crate::stores::li_okmode::declaration::stored_relations(db)
        == crate::stores::li_okruns::declaration::stored_relations(db),
{
    assert(crate::stores::li_okmode::declaration::stored_cols_t0() =~= crate::stores::li_okruns::declaration::stored_cols_t0());
    assert(crate::stores::li_okmode::declaration::stored_cols_t1() =~= crate::stores::li_okruns::declaration::stored_cols_t1());
    assert(crate::stores::li_okmode::declaration::stored_relations(db)
        =~= crate::stores::li_okruns::declaration::stored_relations(db));
}

/// For a database bound to the sources: li_okruns represents this storage's relations, and the kinds hold.
proof fn lemma_src(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures
        LR::represents(sv.li_okruns, crate::stores::li_okmode::declaration::stored_relations(db)),
        src_ok(sv.li_okruns),
{
    lemma_same_relations(db);
    let rels = crate::stores::li_okruns::declaration::stored_relations(db);
    assert(LR::represents(sv.li_okruns, rels));
    lemma_kinds(sv.li_okruns, rels);
}

// ------------------------------------------------------------------------------------------------ bits

/// Setting bit `i` of `x` sets exactly that bit.
proof fn lemma_bit_set(x: u64, i: u64, k: u64)
    requires i < 64, k < 64,
    ensures M::bit(x | (1u64 << i), k as int) == (M::bit(x, k as int) || k == i),
{
    assert(((x | (1u64 << i)) >> k) & 1u64 == 1u64 <==> (((x >> k) & 1u64 == 1u64) || k == i)) by (bit_vector)
        requires i < 64, k < 64;
}

/// Setting bit `i` of `x` (all positions).
proof fn lemma_set_word(x: u64, i: u64)
    requires i < 64,
    ensures forall|k: int| 0 <= k < 64 ==> #[trigger] M::bit(x | (1u64 << i), k) == (M::bit(x, k) || k == i),
{
    assert forall|k: int| 0 <= k < 64 implies #[trigger] M::bit(x | (1u64 << i), k) == (M::bit(x, k) || k == i) by {
        lemma_bit_set(x, i, k as u64);
    }
}

/// No bit of 0 is set.
proof fn lemma_zero_word()
    ensures forall|k: int| 0 <= k < 64 ==> !#[trigger] M::bit(0u64, k),
{
    assert forall|k: int| 0 <= k < 64 implies !#[trigger] M::bit(0u64, k) by {
        let kk = k as u64;
        assert((0u64 >> kk) & 1u64 != 1u64) by (bit_vector);
    }
}

/// Row `64 w + i` of word `w`: `/ 64` is `w`, `% 64` is `i`.
proof fn lemma_word_row(w: int, i: int)
    requires 0 <= w, 0 <= i < 64,
    ensures (64 * w + i) / 64 == w, (64 * w + i) % 64 == i,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(64 * w + i, 64, w, i);
}

/// Row `j` of group `g` (rows `g * bs .. g * bs + bs`) has `j / bs == g`.
proof fn lemma_div_group(j: int, bs: int, g: int)
    requires bs >= 1, g * bs <= j < g * bs + bs,
    ensures j / bs == g,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j, bs, g, j - g * bs);
}

/// The next group starts one group size later.
proof fn lemma_next_group(g: int, bs: int)
    ensures (g + 1) * bs == g * bs + bs,
{
    assert((g + 1) * bs == g * bs + bs) by (nonlinear_arith);
}

/// What the passes read: the inherited parts `p`, their row count, group size and column slices.
pub struct Cols {
    pub n: usize,
    pub bs: usize,
    pub kc: &'static [u32],
    pub kb: &'static [i64],
    pub mc: &'static [u8],
    pub mb: &'static [u64],
}

/// The slices are the parts of `p`, long enough for its `n` rows.
pub open spec fn cols_ok(c: Cols, p: Seq<PartView>) -> bool {
    &&& src_ok(p)
    &&& c.n as int == LR::li_rows(p)
    &&& c.bs as int == LR::li_bsize(p)
    &&& c.bs >= 1
    &&& c.n + c.bs + 64 <= usize::MAX
    &&& c.kc@ == u32s(p[F::LI_ORDERKEY_CODES as int])
    &&& c.kb@ == i64s(p[F::LI_ORDERKEY_BASE as int])
    &&& c.mc@ == u8s(p[F::LI_SHIPMODE_CODES as int])
    &&& c.mb@ == u64s(p[F::LI_SHIPMODE_BASE as int])
    &&& c.kc@.len() == c.n
    &&& c.mc@.len() == c.n
    &&& c.kb@.len() * c.bs >= c.n
    &&& c.mb@.len() * c.bs >= c.n
}

/// The group cursor `(g, gend)` stands at row `j`: `g * bs <= j < gend == g * bs + bs`.
pub open spec fn at_group(c: Cols, g: usize, gend: usize, j: int) -> bool {
    &&& g * c.bs <= j < gend
    &&& gend == g * c.bs + c.bs
}

/// Moves the group cursor from row `j - 1`'s group to row `j`'s.
fn step_group(c: &Cols, g: usize, gend: usize, j: usize, Ghost(p): Ghost<Seq<PartView>>) -> (r: (usize, usize))
    requires
        cols_ok(*c, p),
        j < c.n,
        g * c.bs <= j <= gend,
        gend == g * c.bs + c.bs,
    ensures
        at_group(*c, r.0, r.1, j as int),
        r.0 < c.kb@.len(),
        r.0 < c.mb@.len(),
{
    let (g2, e2) = if j == gend {
        proof {
            lemma_next_group(g as int, c.bs as int);
            assert(g <= g * c.bs) by (nonlinear_arith) requires c.bs >= 1;
        }
        (g + 1, gend + c.bs)
    } else {
        (g, gend)
    };
    proof {
        if g2 >= c.kb@.len() {
            assert(g2 * c.bs >= c.kb@.len() * c.bs) by (nonlinear_arith) requires g2 >= c.kb@.len(), c.bs >= 1;
        }
        if g2 >= c.mb@.len() {
            assert(g2 * c.bs >= c.mb@.len() * c.bs) by (nonlinear_arith) requires g2 >= c.mb@.len(), c.bs >= 1;
        }
    }
    (g2, e2)
}

/// The run-start bitmap: `nw` words, row `j` set exactly when `j < n` and it starts a run of equal l_orderkey.
fn run_words(c: &Cols, nw: usize, Ghost(p): Ghost<Seq<PartView>>) -> (words: Vec<u64>)
    requires
        cols_ok(*c, p),
        c.n >= 1,
        nw * 64 >= c.n,
        nw * 64 <= c.n + 63,
    ensures
        words@.len() == nw,
        forall|j: int| 0 <= j < nw * 64 ==>
            #[trigger] M::row_bit(words@, nw as int, 0, j) == (j < c.n && M::run_start(p, j)),
{
    let mut words: Vec<u64> = Vec::new();
    let mut g: usize = 0;
    let mut gend: usize = c.bs;
    let mut prev: i128 = 0;
    let mut w: usize = 0;
    while w < nw
        invariant
            cols_ok(*c, p),
            c.n >= 1,
            nw * 64 >= c.n,
            nw * 64 <= c.n + 63,
            w <= nw,
            words@.len() == w,
            g * c.bs <= w * 64 || w * 64 >= c.n,
            gend == g * c.bs + c.bs,
            w * 64 <= gend || w * 64 >= c.n,
            w > 0 && w * 64 <= c.n ==> prev as int == LR::okey_at(p, w * 64 - 1),
            forall|v: int, i: int| 0 <= v < w && 0 <= i < 64 ==>
                #[trigger] M::bit(words@[v], i) == (64 * v + i < c.n && M::run_start(p, 64 * v + i)),
        decreases nw - w,
    {
        let mut x: u64 = 0;
        let mut i: usize = 0;
        proof {
            lemma_zero_word();
        }
        while i < 64
            invariant
                cols_ok(*c, p),
                w < nw,
                nw * 64 <= c.n + 63,
                i <= 64,
                g * c.bs <= w * 64 + i || w * 64 + i >= c.n,
                gend == g * c.bs + c.bs,
                w * 64 + i <= gend || w * 64 + i >= c.n,
                w * 64 + i > 0 && w * 64 + i <= c.n ==> prev as int == LR::okey_at(p, w * 64 + i - 1),
                forall|k: int| 0 <= k < 64 ==>
                    #[trigger] M::bit(x, k) == (k < i && 64 * w + k < c.n && M::run_start(p, 64 * w + k)),
            decreases 64 - i,
        {
            let j = w * 64 + i;
            if j < c.n {
                let (g2, e2) = step_group(c, g, gend, j, Ghost(p));
                g = g2;
                gend = e2;
                proof {
                    lemma_div_group(j as int, c.bs as int, g as int);
                }
                let k = c.kb[g] as i128 + c.kc[j] as i128;
                let s = j == 0 || k != prev;
                proof {
                    assert(k as int == LR::okey_at(p, j as int));
                    assert(s == M::run_start(p, j as int));
                    lemma_set_word(x, i as u64);
                }
                x = if s { x | (1u64 << i as u64) } else { x };
                prev = k;
            }
            i = i + 1;
        }
        words.push(x);
        proof {
            assert forall|v: int, k: int| 0 <= v < w + 1 && 0 <= k < 64 implies
                #[trigger] M::bit(words@[v], k) == (64 * v + k < c.n && M::run_start(p, 64 * v + k)) by {
                if v == w {
                    assert(words@[v] == x);
                }
            }
        }
        w = w + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < nw * 64 implies
            #[trigger] M::row_bit(words@, nw as int, 0, j) == (j < c.n && M::run_start(p, j)) by {
            let v = j / 64;
            let k = j % 64;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, 64);
            assert(0 <= v < nw);
            assert(64 * v + k == j);
            assert(0 * nw + v == v);
        }
    }
    words
}

/// Word `w` of l_shipmode bitmap `k` is correct.
pub open spec fn mword_ok(c: Cols, p: Seq<PartView>, words: Seq<u64>, nw: int, k: int, w: int) -> bool {
    forall|i: int| 0 <= i < 64 ==>
        #[trigger] M::bit(words[k * nw + w], i) == (64 * w + i < c.n && M::mode_at(p, 64 * w + i) == k)
}

/// Distinct (bitmap, word) pairs have distinct word indices.
proof fn lemma_idx(k: int, w: int, k2: int, w2: int, nw: int, nm: int)
    requires 0 <= k < nm, 0 <= w < nw, 0 <= k2 < nm, 0 <= w2 < nw,
    ensures
        0 <= k * nw + w < nm * nw,
        (k != k2 || w != w2) ==> k * nw + w != k2 * nw + w2,
{
    assert(0 <= k * nw + w < nm * nw) by (nonlinear_arith) requires 0 <= k < nm, 0 <= w < nw;
    if k != k2 {
        if k < k2 {
            assert(k * nw + w < k2 * nw + w2) by (nonlinear_arith) requires k < k2, 0 <= w < nw, 0 <= w2;
        } else {
            assert(k2 * nw + w2 < k * nw + w) by (nonlinear_arith) requires k2 < k, 0 <= w2 < nw, 0 <= w;
        }
    }
}

/// The l_shipmode bitmaps: `nm` bitmaps of `nw` words, bitmap-major; row `j` of bitmap `k` set exactly when
/// `j < n` and its dictionary index is `k`.
fn mode_words(c: &Cols, nw: usize, nm: usize, Ghost(p): Ghost<Seq<PartView>>) -> (words: Vec<u64>)
    requires
        cols_ok(*c, p),
        c.n >= 1,
        nw * 64 >= c.n,
        nw * 64 <= c.n + 63,
        1 <= nm <= 64,
    ensures
        words@.len() == nm * nw,
        forall|k: int, j: int| 0 <= k < nm && 0 <= j < nw * 64 ==>
            #[trigger] M::row_bit(words@, nw as int, k, j) == (j < c.n && M::mode_at(p, j) == k),
{
    proof {
        assert(nm * nw <= 64 * nw) by (nonlinear_arith) requires nm <= 64;
    }
    let total = nm * nw;
    let mut words: Vec<u64> = filled(total, 0u64);
    let mut acc: Vec<u64> = filled(nm, 0u64);
    let mut g: usize = 0;
    let mut gend: usize = c.bs;
    let mut w: usize = 0;
    while w < nw
        invariant
            cols_ok(*c, p),
            c.n >= 1,
            nw * 64 >= c.n,
            nw * 64 <= c.n + 63,
            1 <= nm <= 64,
            total == nm * nw,
            w <= nw,
            words@.len() == total,
            acc@.len() == nm,
            g * c.bs <= w * 64 || w * 64 >= c.n,
            gend == g * c.bs + c.bs,
            w * 64 <= gend || w * 64 >= c.n,
            forall|k: int, v: int| 0 <= k < nm && 0 <= v < w ==> #[trigger] mword_ok(*c, p, words@, nw as int, k, v),
        decreases nw - w,
    {
        // acc[k]: word w of bitmap k.
        let mut k0: usize = 0;
        while k0 < nm
            invariant
                acc@.len() == nm,
                k0 <= nm,
                forall|k: int| 0 <= k < k0 ==> #[trigger] acc@[k] == 0u64,
            decreases nm - k0,
        {
            acc.set(k0, 0u64);
            k0 = k0 + 1;
        }
        proof {
            lemma_zero_word();
        }
        let mut i: usize = 0;
        while i < 64
            invariant
                cols_ok(*c, p),
                w < nw,
                nw * 64 <= c.n + 63,
                1 <= nm <= 64,
                acc@.len() == nm,
                i <= 64,
                g * c.bs <= w * 64 + i || w * 64 + i >= c.n,
                gend == g * c.bs + c.bs,
                w * 64 + i <= gend || w * 64 + i >= c.n,
                forall|k: int, b: int| 0 <= k < nm && 0 <= b < 64 ==>
                    #[trigger] M::bit(acc@[k], b) == (b < i && 64 * w + b < c.n && M::mode_at(p, 64 * w + b) == k),
            decreases 64 - i,
        {
            let j = w * 64 + i;
            if j < c.n {
                let (g2, e2) = step_group(c, g, gend, j, Ghost(p));
                g = g2;
                gend = e2;
                proof {
                    lemma_div_group(j as int, c.bs as int, g as int);
                }
                let m = c.mb[g] as u128 + c.mc[j] as u128;
                proof {
                    assert(m as int == M::mode_at(p, j as int));
                }
                if m < nm as u128 {
                    let ghost a0 = acc@;
                    let old_word = acc[m as usize];
                    proof {
                        lemma_set_word(old_word, i as u64);
                    }
                    acc.set(m as usize, old_word | (1u64 << i as u64));
                    proof {
                        assert forall|k: int, b: int| 0 <= k < nm && 0 <= b < 64 implies
                            #[trigger] M::bit(acc@[k], b) == (b < i + 1 && 64 * w + b < c.n && M::mode_at(p, 64 * w + b) == k) by {
                            if k != m {
                                assert(acc@[k] == a0[k]);
                            }
                        }
                    }
                }
            }
            i = i + 1;
        }
        let mut k: usize = 0;
        while k < nm
            invariant
                cols_ok(*c, p),
                w < nw,
                1 <= nm <= 64,
                total == nm * nw,
                words@.len() == total,
                acc@.len() == nm,
                k <= nm,
                forall|k2: int, b: int| 0 <= k2 < nm && 0 <= b < 64 ==>
                    #[trigger] M::bit(acc@[k2], b) == (64 * w + b < c.n && M::mode_at(p, 64 * w + b) == k2),
                forall|k2: int, v: int| 0 <= k2 < nm && 0 <= v < w ==> #[trigger] mword_ok(*c, p, words@, nw as int, k2, v),
                forall|k2: int| 0 <= k2 < k ==> #[trigger] mword_ok(*c, p, words@, nw as int, k2, w as int),
            decreases nm - k,
        {
            proof {
                lemma_idx(k as int, w as int, 0, 0, nw as int, nm as int);
                assert(k * nw + w < nm * nw) by (nonlinear_arith) requires k < nm, w < nw;
            }
            let ghost w0 = words@;
            let idx = k * nw + w;
            words.set(idx, acc[k]);
            proof {
                assert forall|k2: int, v: int| 0 <= k2 < nm && 0 <= v < w implies
                    #[trigger] mword_ok(*c, p, words@, nw as int, k2, v) by {
                    lemma_idx(k as int, w as int, k2, v, nw as int, nm as int);
                    assert(mword_ok(*c, p, w0, nw as int, k2, v));
                    assert(words@[k2 * nw + v] == w0[k2 * nw + v]);
                }
                assert forall|k2: int| 0 <= k2 < k + 1 implies #[trigger] mword_ok(*c, p, words@, nw as int, k2, w as int) by {
                    lemma_idx(k as int, w as int, k2, w as int, nw as int, nm as int);
                    if k2 < k {
                        assert(mword_ok(*c, p, w0, nw as int, k2, w as int));
                        assert(words@[k2 * nw + w] == w0[k2 * nw + w]);
                    } else {
                        assert(words@[k2 * nw + w] == acc@[k2]);
                    }
                }
            }
            k = k + 1;
        }
        w = w + 1;
    }
    proof {
        assert forall|k: int, j: int| 0 <= k < nm && 0 <= j < nw * 64 implies
            #[trigger] M::row_bit(words@, nw as int, k, j) == (j < c.n && M::mode_at(p, j) == k) by {
            let v = j / 64;
            let b = j % 64;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, 64);
            assert(0 <= v < nw);
            assert(64 * v + b == j);
            assert(mword_ok(*c, p, words@, nw as int, k, v));
        }
    }
    words
}

/// The layout and the two bitmap parts over the inherited parts `p`, or the fallback `[0, 0]` with empty bitmaps.
fn bitmaps(st: &mut StoredParts, Ghost(p): Ghost<Seq<PartView>>) -> (r: (Vec<u64>, Vec<u64>, Vec<u64>))
    requires old(st)@ == p, src_ok(p),
    ensures
        final(st)@ == old(st)@,
        r.0@.len() == 2,
        r.1@.len() == r.0@[0],
        r.2@.len() == r.0@[1] * r.0@[0],
        r.0@[0] > 0 ==> LR::li_rows(p) <= r.0@[0] * 64,
        forall|j: int| 0 <= j < r.0@[0] * 64 ==>
            #[trigger] M::row_bit(r.1@, r.0@[0] as int, 0, j) == (j < LR::li_rows(p) && M::run_start(p, j)),
        forall|k: int, j: int| 0 <= k < r.0@[1] && 0 <= j < r.0@[0] * 64 ==>
            #[trigger] M::row_bit(r.2@, r.0@[0] as int, k, j) == (j < LR::li_rows(p) && M::mode_at(p, j) == k),
{
    let lay = st.extent_u64(F::LI_LAYOUT, 0, 2);
    proof {
        assert(lay@ =~= u64s(p[F::LI_LAYOUT as int]));
    }
    let n64 = lay[0];
    let bs64 = lay[1];
    proof {
        assert(n64 as int == LR::li_rows(p));
        assert(bs64 as int == LR::li_bsize(p));
    }
    let mut none: Vec<u64> = Vec::new();
    none.push(0u64);
    none.push(0u64);
    let fallback = (none, Vec::new(), Vec::new());
    if n64 == 0 || bs64 == 0 || n64 >= 0x4000_0000 || bs64 >= 0x4000_0000 {
        return fallback;
    }
    let n = n64 as usize;
    let bs = bs64 as usize;
    let kc = st.extent_u32(F::LI_ORDERKEY_CODES, 0, st.part_len(F::LI_ORDERKEY_CODES));
    let kb = st.extent_i64(F::LI_ORDERKEY_BASE, 0, st.part_len(F::LI_ORDERKEY_BASE));
    let mc = st.extent_u8(F::LI_SHIPMODE_CODES, 0, st.part_len(F::LI_SHIPMODE_CODES));
    let mb = st.extent_u64(F::LI_SHIPMODE_BASE, 0, st.part_len(F::LI_SHIPMODE_BASE));
    let nmo = st.part_len(F::LI_SHIPMODE_DICT_OFFS);
    proof {
        assert(kc@ =~= u32s(p[F::LI_ORDERKEY_CODES as int]));
        assert(kb@ =~= i64s(p[F::LI_ORDERKEY_BASE as int]));
        assert(mc@ =~= u8s(p[F::LI_SHIPMODE_CODES as int]));
        assert(mb@ =~= u64s(p[F::LI_SHIPMODE_BASE as int]));
    }
    if kc.len() != n || mc.len() != n || nmo < 2 || nmo > 65 {
        return fallback;
    }
    proof {
        assert((kb.len() as u128) * (bs as u128) <= 0xffff_ffff_ffff_ffff * 0xffff_ffff_ffffu128) by (nonlinear_arith)
            requires kb.len() <= 0xffff_ffff_ffff_ffff, bs < 0x4000_0000;
        assert((mb.len() as u128) * (bs as u128) <= 0xffff_ffff_ffff_ffff * 0xffff_ffff_ffffu128) by (nonlinear_arith)
            requires mb.len() <= 0xffff_ffff_ffff_ffff, bs < 0x4000_0000;
    }
    if (kb.len() as u128) * (bs as u128) < n as u128 || (mb.len() as u128) * (bs as u128) < n as u128 {
        return fallback;
    }
    let nm = nmo - 1;
    let c = Cols { n, bs, kc, kb, mc, mb };
    let nw = n / 64 + if n % 64 == 0 { 0 } else { 1 };
    proof {
        assert(c.kb@.len() * c.bs >= c.n) by (nonlinear_arith)
            requires (kb.len() as u128) * (bs as u128) >= n as u128, c.kb@.len() == kb@.len(), c.bs == bs, c.n == n;
        assert(c.mb@.len() * c.bs >= c.n) by (nonlinear_arith)
            requires (mb.len() as u128) * (bs as u128) >= n as u128, c.mb@.len() == mb@.len(), c.bs == bs, c.n == n;
        assert(src_ok(p));
        assert(c.n as int == LR::li_rows(p));
        assert(c.bs as int == LR::li_bsize(p));
        assert(c.n + c.bs + 64 <= usize::MAX);
        assert(c.kc@ == u32s(p[F::LI_ORDERKEY_CODES as int]));
        assert(c.kc@.len() == c.n);
        assert(c.mc@.len() == c.n);
        assert(cols_ok(c, p));
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, 64);
        assert(nw * 64 >= n && nw * 64 <= n + 63);
    }
    let rw = run_words(&c, nw, Ghost(p));
    let mw = mode_words(&c, nw, nm, Ghost(p));
    let mut lay2: Vec<u64> = Vec::new();
    lay2.push(nw as u64);
    lay2.push(nm as u64);
    (lay2, rw, mw)
}

/// The parts of li_okruns followed by the layout and the two bitmaps satisfy `represents` for every bound database.
pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> forall|db: Database| #[trigger] sources_bound(old(stores)@, db) ==>
            crate::gendb_entry::storage::represents(storage_parts(old(stores)@, owned_parts_view(p@)),
                crate::gendb_entry::storage::stored_relations(db)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost sv = stores@;
    let ghost p = sv.li_okruns;
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    proof {
        lemma_src(sv, db0);
    }
    let (lay, rw, mw) = bitmaps(&mut stores.li_okruns, Ghost(p));
    let ghost (layv, rwv, mwv) = (lay@, rw@, mw@);
    let mut parts: Vec<OwnedPart> = Vec::new();
    parts.push(OwnedPart::U64(lay));
    parts.push(OwnedPart::U64(rw));
    parts.push(OwnedPart::U64(mw));
    proof {
        let built = owned_parts_view(parts@);
        assert(built.len() == 3);
        assert(built[0] == owned_part_view(parts@[0]));
        assert(built[1] == owned_part_view(parts@[1]));
        assert(built[2] == owned_part_view(parts@[2]));
        let all = storage_parts(sv, built);
        assert(all == p + built);
        assert(all.len() == M::LI_OKMODE_PARTS);
        assert(M::okruns_parts(all) =~= p);
        assert(u64s(all[M::OKM_LAYOUT as int]) == layv);
        assert(u64s(all[M::RUN_BITS as int]) == rwv);
        assert(u64s(all[M::MODE_BITS as int]) == mwv);
        assert(all[F::LI_LAYOUT as int] == p[F::LI_LAYOUT as int]);
        assert(all[F::LI_ORDERKEY_CODES as int] == p[F::LI_ORDERKEY_CODES as int]);
        assert(all[F::LI_ORDERKEY_BASE as int] == p[F::LI_ORDERKEY_BASE as int]);
        assert(all[F::LI_SHIPMODE_CODES as int] == p[F::LI_SHIPMODE_CODES as int]);
        assert(all[F::LI_SHIPMODE_BASE as int] == p[F::LI_SHIPMODE_BASE as int]);
        assert(M::n_rows(all) == LR::li_rows(p));
        assert forall|j: int| #[trigger] M::run_start(all, j) == M::run_start(p, j) by {
            assert(LR::okey_at(all, j) == LR::okey_at(p, j));
            assert(LR::okey_at(all, j - 1) == LR::okey_at(p, j - 1));
        }
        assert forall|j: int| #[trigger] M::mode_at(all, j) == M::mode_at(p, j) by {}
        assert forall|j: int| 0 <= j < M::n_words(all) * 64 implies #[trigger] M::run_bit_ok(all, j) by {
            assert(M::row_bit(rwv, layv[0] as int, 0, j) == (j < LR::li_rows(p) && M::run_start(p, j)));
        }
        assert forall|k: int, j: int| 0 <= k < M::n_modes(all) && 0 <= j < M::n_words(all) * 64 implies
            #[trigger] M::mode_bit_ok(all, k, j) by {
            assert(M::row_bit(mwv, layv[0] as int, k, j) == (j < LR::li_rows(p) && M::mode_at(p, j) == k));
        }
        assert(M::okm_ok(all));
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies
            M::represents(all, crate::stores::li_okmode::declaration::stored_relations(db)) by {
            lemma_src(sv, db);
        }
    }
    Ok(parts)
}

} // verus!
