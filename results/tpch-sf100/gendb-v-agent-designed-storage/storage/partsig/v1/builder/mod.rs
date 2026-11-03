//! Builder of storage `partsig`: one pass over custpart's part p_name (U64 offsets + U8 bytes, `rows + 1` offsets)
//! computing every row's 64-bit trigram signature: the OR of `tri_bit` of each three consecutive bytes of the row's
//! name, or all ones when the name is not ASCII (`row_sig`). custpart's `represents` gives the offsets as byte ranges of the bytes part (`src_ok`).
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view, owned_part_view};
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::{sources_ready, sources_bound, storage_parts};
use crate::spec::value::{Database, Row};
use crate::stores::custpart::interface as ci;
use crate::stores::partsig::interface as ps;
use ci::common::colfmt::{u8s, u64s, text_of, text_parts_wf, text_range_ok};

verus! {

/// custpart's part layout part.
pub const P_LAYOUT: usize = 21;
/// custpart's p_name offsets part.
pub const P_NAME_OFFS: usize = 25;
/// custpart's p_name bytes part.
pub const P_NAME_BYTES: usize = 26;

/// What the builder needs of custpart's parts `f`: the part row count and p_name as byte ranges.
pub open spec fn src_ok(f: Seq<PartView>) -> bool {
    &&& f.len() == ci::CUSTPART_PARTS
    &&& f[P_LAYOUT as int] is U64 && u64s(f[P_LAYOUT as int]).len() == 2
    &&& f[P_NAME_OFFS as int] is U64 && f[P_NAME_BYTES as int] is U8
    &&& text_parts_wf(u64s(f[P_NAME_OFFS as int]), u8s(f[P_NAME_BYTES as int]), u64s(f[P_LAYOUT as int])[0] as int)
}

/// A bound database gives `src_ok`.
proof fn lemma_src_ok(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures src_ok(sv.custpart),
{
    let f = sv.custpart;
    let rels = crate::stores::custpart::declaration::stored_relations(db);
    assert(ci::represents(f, rels));
    let tp = f.subrange(ci::PART_FIRST as int, (ci::PART_FIRST + ci::PA_PARTS) as int);
    assert(ci::part_ok(tp, rels[1]));
    assert(tp[0] == f[P_LAYOUT as int]);
    assert(tp[4] == f[P_NAME_OFFS as int]);
    assert(tp[5] == f[P_NAME_BYTES as int]);
    assert(ci::table_layout_ok(tp, rels[1].len() as int));
}

/// OR keeps a bit that is set.
proof fn lemma_or_keeps(x: u64, y: u64, b: u64)
    requires x & b == b,
    ensures (x | y) & b == b,
{
    assert((x & b == b) ==> ((x | y) & b == b)) by (bit_vector);
}

/// OR sets the bits it adds.
proof fn lemma_or_sets(x: u64, b: u64)
    ensures (x | b) & b == b,
{
    assert((x | b) & b == b) by (bit_vector);
}

/// Byte `x` of `h | b` is below 0x80 exactly when both are.
proof fn lemma_or_ascii(h: u8, b: u8)
    ensures ((h | b) < 0x80u8) == (h < 0x80u8 && b < 0x80u8),
{
    assert(((h | b) < 0x80u8) == (h < 0x80u8 && b < 0x80u8)) by (bit_vector);
}

/// Are the bytes `y[a .. e]` ASCII?
fn range_ascii(y: &[u8], a: usize, e: usize) -> (r: bool)
    requires a <= e <= y@.len(),
    ensures r == ps::ascii_text(y@.subrange(a as int, e as int)),
{
    let ghost t = y@.subrange(a as int, e as int);
    let mut hi: u8 = 0;
    let mut i = a;
    while i < e
        invariant
            a <= i <= e <= y@.len(), t == y@.subrange(a as int, e as int),
            (hi < 0x80u8) == forall|x: int| 0 <= x < i - a ==> #[trigger] t[x] < 0x80,
        decreases e - i,
    {
        let b = y[i];
        proof {
            lemma_or_ascii(hi, b);
            assert(t[i - a] == b);
            assert((hi | b < 0x80u8) == forall|x: int| 0 <= x < i + 1 - a ==> #[trigger] t[x] < 0x80) by {
                if (hi | b) < 0x80u8 {
                    assert forall|x: int| 0 <= x < i + 1 - a implies #[trigger] t[x] < 0x80 by {
                        if x < i - a { assert(hi < 0x80u8); }
                    }
                } else {
                    if hi >= 0x80u8 {
                        let x0 = choose|x: int| 0 <= x < i - a && !(#[trigger] t[x] < 0x80);
                        assert(!(t[x0] < 0x80));
                    } else {
                        assert(!(t[i - a] < 0x80));
                    }
                }
            }
        }
        hi = hi | b;
        i = i + 1;
    }
    hi < 0x80
}

/// The signature of the text `y[a .. e]`: the OR of the bits of its trigrams, or all ones when it is not ASCII.
fn row_sig(y: &[u8], a: usize, e: usize, Ghost(n): Ghost<int>) -> (s: u64)
    requires a <= e <= y@.len(), n == y@.len(),
    ensures ps::sig_row_ok(y@.subrange(a as int, e as int), s),
{
    let ghost t = y@.subrange(a as int, e as int);
    if !range_ascii(y, a, e) {
        proof {
            assert forall|p: int| 0 <= p && p + 2 < t.len() implies #[trigger] ps::has_tri(ps::ALL, t, p) by {
                let b = ps::tri_bit(t[p], t[p + 1], t[p + 2]);
                assert(0xffff_ffff_ffff_ffffu64 & b == b) by (bit_vector);
            }
        }
        return ps::ALL;
    }
    let mut s: u64 = 0;
    let mut p = a;
    while p < e && e - p > 2
        invariant
            a <= p <= e <= y@.len(), t == y@.subrange(a as int, e as int),
            forall|q: int| 0 <= q < p - a && q + 2 < t.len() ==> #[trigger] ps::has_tri(s, t, q),
        decreases e - p,
    {
        let b = ps::tri_bit_exec(y[p], y[p + 1], y[p + 2]);
        proof {
            let q0 = p - a;
            assert(t[q0] == y@[p as int] && t[q0 + 1] == y@[p + 1] && t[q0 + 2] == y@[p + 2]);
            assert forall|q: int| 0 <= q < p + 1 - a && q + 2 < t.len() implies #[trigger] ps::has_tri(s | b, t, q) by {
                if q < q0 {
                    assert(ps::has_tri(s, t, q));
                    lemma_or_keeps(s, b, ps::tri_bit(t[q], t[q + 1], t[q + 2]));
                } else {
                    lemma_or_sets(s, b);
                }
            }
        }
        s = s | b;
        p = p + 1;
    }
    proof {
        assert forall|q: int| 0 <= q && q + 2 < t.len() implies #[trigger] ps::has_tri(s, t, q) by {
            assert(q < p - a);
        }
    }
    s
}

/// The signature of every part row, from custpart's parts `f`.
fn signatures(stores: &mut Stores, Ghost(f): Ghost<Seq<PartView>>) -> (r: Vec<u64>)
    requires old(stores)@.custpart == f, src_ok(f),
    ensures
        final(stores)@ == old(stores)@,
        r@.len() == u64s(f[P_LAYOUT as int])[0],
        forall|c: int| 0 <= c < r@.len() ==> #[trigger] ps::sig_row_ok(
            text_of(u64s(f[P_NAME_OFFS as int]), u8s(f[P_NAME_BYTES as int]), c), r@[c]),
{
    let lay = stores.custpart.extent_u64(P_LAYOUT, 0, 2);
    let n64 = lay[0];
    proof {
        assert(lay@ =~= u64s(f[P_LAYOUT as int]));
        assert(u64s(f[P_NAME_OFFS as int]).len() == n64 + 1);
    }
    let o = stores.custpart.extent_u64(P_NAME_OFFS, 0, stores.custpart.part_len(P_NAME_OFFS));
    let y = stores.custpart.extent_u8(P_NAME_BYTES, 0, stores.custpart.part_len(P_NAME_BYTES));
    let ghost ov = u64s(f[P_NAME_OFFS as int]);
    let ghost yv = u8s(f[P_NAME_BYTES as int]);
    proof {
        assert(o@ =~= ov);
        assert(y@ =~= yv);
    }
    let n = n64 as usize;
    let ylen = y.len();
    let mut sig: Vec<u64> = Vec::with_capacity(n);
    let mut c: usize = 0;
    while c < n
        invariant
            src_ok(f), n as int == u64s(f[P_LAYOUT as int])[0], o@ == ov, y@ == yv, ylen == yv.len(),
            ov == u64s(f[P_NAME_OFFS as int]), yv == u8s(f[P_NAME_BYTES as int]),
            stores@ == old(stores)@,
            c <= n, sig@.len() == c,
            forall|x: int| 0 <= x < c ==> #[trigger] ps::sig_row_ok(text_of(ov, yv, x), sig@[x]),
        decreases n - c,
    {
        proof {
            assert(text_range_ok(ov, yv, c as int));
            assert(ov.len() == n + 1);
            assert(ov[c as int] <= ov[c + 1] && ov[c + 1] <= yv.len());
        }
        let a = o[c] as usize;
        let e = o[c + 1] as usize;
        proof {
            assert(a as int == ov[c as int] && e as int == ov[c + 1]);
            assert(text_of(ov, yv, c as int) == y@.subrange(a as int, e as int));
        }
        let s = row_sig(y, a, e, Ghost(yv.len() as int));
        let ghost s0 = sig@;
        sig.push(s);
        proof {
            assert forall|x: int| 0 <= x < c + 1 implies #[trigger] ps::sig_row_ok(text_of(ov, yv, x), sig@[x]) by {
                if x < c { assert(sig@[x] == s0[x]); }
            }
        }
        c = c + 1;
    }
    sig
}

/// partsig's stored relations are custpart's (the same declaration).
proof fn lemma_same_relations(db: Database)
    ensures crate::stores::partsig::declaration::stored_relations(db) == crate::stores::custpart::declaration::stored_relations(db),
{
    assert(crate::stores::partsig::declaration::stored_cols_t0() =~= crate::stores::custpart::declaration::stored_cols_t0());
    assert(crate::stores::partsig::declaration::stored_cols_t1() =~= crate::stores::custpart::declaration::stored_cols_t1());
    assert(crate::stores::partsig::declaration::stored_relations(db) =~= crate::stores::custpart::declaration::stored_relations(db));
}

/// The parts of custpart followed by the signatures satisfy `represents` for every bound database.
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
    let ghost f = sv.custpart;
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    proof { lemma_src_ok(sv, db0); }
    let sig = signatures(stores, Ghost(f));
    let ghost gv = sig@;
    let mut parts: Vec<OwnedPart> = Vec::new();
    parts.push(OwnedPart::U64(sig));
    proof {
        let built = owned_parts_view(parts@);
        assert(built.len() == 1);
        assert(built[0] == owned_part_view(parts@[0]));
        let all = storage_parts(sv, built);
        assert(all == f + built);
        assert(all.len() == ps::PARTSIG_PARTS);
        assert(all.subrange(0, ps::CUSTPART_PARTS as int) =~= f);
        assert(all[ps::SIG as int] == built[0]);
        assert(ps::sigs(all) == gv);
        assert(all[P_LAYOUT as int] == f[P_LAYOUT as int]);
        assert(all[P_NAME_OFFS as int] == f[P_NAME_OFFS as int]);
        assert(all[P_NAME_BYTES as int] == f[P_NAME_BYTES as int]);
        assert(ps::part_rows(all) == u64s(f[P_LAYOUT as int])[0]);
        assert forall|c: int| 0 <= c < ps::part_rows(all) implies #[trigger] ps::sig_row_ok(ps::pname_of(all, c), ps::sigs(all)[c]) by {
            assert(ps::pname_of(all, c) == text_of(u64s(f[P_NAME_OFFS as int]), u8s(f[P_NAME_BYTES as int]), c));
        }
        assert(ps::sig_ok(all));
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies
            ps::represents(all, crate::stores::partsig::declaration::stored_relations(db)) by {
            lemma_same_relations(db);
        }
    }
    Ok(parts)
}

} // verus!
