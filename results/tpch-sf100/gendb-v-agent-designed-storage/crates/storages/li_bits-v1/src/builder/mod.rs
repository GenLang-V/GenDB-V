//! Builder of storage `li_bits`: the 75 parts of `facts` are inherited unchanged; this builder adds the bitmap
//! indexes of l_discount (equality, keys 0.00 .. 0.10), l_quantity (range, keys 2 .. 51) and l_shipdate (range per
//! row group, keys: the first `SHIP_KEYS_PER_GROUP` month starts after the group's base shipdate).
//!
//! Plan: one pass over facts' codes per bitmap (`bits::push_bitmap`): a word whose 64 rows lie in one row group
//! compares the codes against one code-space threshold. The discount codes (U8) are widened to U16 once so one
//! pass serves all three columns.
//!
//! Proof: `src::lemma_src` gives the part shapes; each pass ensures `word_ok` for its words; `lemma_family_rows`
//! turns the words of one family into the per-row statements of `bits_ok`; the inherited parts are facts' parts, so
//! facts' `represents` carries over unchanged. If the shapes are unexpected at run time (too many rows), the
//! bitmap parts are empty (no keys): `bits_ok` then states nothing about rows.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::gendb_entry::stored::part_len;
use crate::spec::value::Database;
use crate::stores::facts::interface as F;
use crate::stores::facts::interface::common::colfmt as FC;
use crate::stores::li_bits::interface::*;

pub mod bits;
pub mod src;
use bits::*;
use src::*;

verus! {

/// Discount keys: coefficients 0 .. 10 (0.00 .. 0.10).
pub const DISC_KEY_COUNT: usize = 11;
/// Quantity keys: coefficients 200, 300, .., 5100 (`l_quantity < 2` .. `l_quantity < 51`).
pub const QTY_KEY_COUNT: usize = 50;
/// Shipdate keys per row group.
pub const SHIP_KEYS_PER_GROUP: usize = 6;

/// The words of one family: bitmap `k` (words `k * nw ..`) marks `holds(p, value, keys[g * stride + k])`.
pub open spec fn family_ok(words: Seq<u64>, nk: int, nw: int, p: Pred, gs: Seq<u64>, n: int, base: Seq<i64>,
    codes: Seq<u16>, keys: Seq<i64>, stride: int) -> bool
{
    &&& words.len() == nk * nw
    &&& forall|k: int, w: int| 0 <= k < nk && 0 <= w < nw ==> #[trigger] word_ok(words[k * nw + w], w, p, gs, n,
        base, codes, keys, stride, k)
}

/// `k * nw + w` indexes the words of a family in order.
proof fn lemma_family_index(k: int, nw: int, w: int, nk: int)
    requires 0 <= k < nk, 0 <= w < nw,
    ensures 0 <= k * nw + w < nk * nw, k * nw + w < (k + 1) * nw, (k + 1) * nw == k * nw + nw, k * nw >= 0,
{
    assert(0 <= k * nw + w < nk * nw) by (nonlinear_arith) requires 0 <= k < nk, 0 <= w < nw;
    assert((k + 1) * nw == k * nw + nw) by (nonlinear_arith);
    assert(k * nw >= 0) by (nonlinear_arith) requires 0 <= k, 0 <= nw;
}

/// Appends the `nk` bitmaps of one family.
fn push_family(out: &mut Vec<u64>, p: &Pred, gs: &[u64], base: &[i64], codes: &[u16], keys: &[i64], stride: usize,
    nk: usize, n: usize, nw: usize)
    requires
        old(out)@.len() == 0,
        forall|k: int| 0 <= k < nk ==> pass_ok(gs@, n as int, base@, codes@, keys@, stride as int, k),
        n <= nw * 64,
        nw * 64 <= usize::MAX,
        nk * nw <= usize::MAX,
    ensures
        family_ok(final(out)@, nk as int, nw as int, *p, gs@, n as int, base@, codes@, keys@, stride as int),
{
    let mut k: usize = 0;
    while k < nk
        invariant
            k <= nk,
            forall|k: int| 0 <= k < nk ==> pass_ok(gs@, n as int, base@, codes@, keys@, stride as int, k),
            n <= nw * 64,
            nw * 64 <= usize::MAX,
            nk * nw <= usize::MAX,
            out@.len() == k * nw,
            forall|k2: int, w: int| 0 <= k2 < k && 0 <= w < nw ==> #[trigger] word_ok(out@[k2 * nw + w], w, *p, gs@,
                n as int, base@, codes@, keys@, stride as int, k2),
        decreases nk - k,
    {
        let ghost before = out@;
        proof {
            assert(pass_ok(gs@, n as int, base@, codes@, keys@, stride as int, k as int));
        }
        push_bitmap(out, p, gs, base, codes, keys, stride, k, n, nw);
        proof {
            assert((k + 1) * nw == k * nw + nw) by (nonlinear_arith);
            assert forall|k2: int, w: int| 0 <= k2 < k + 1 && 0 <= w < nw implies #[trigger] word_ok(out@[k2 * nw + w], w,
                *p, gs@, n as int, base@, codes@, keys@, stride as int, k2) by {
                lemma_family_index(k2, nw as int, w, k + 1);
                if k2 < k {
                    lemma_family_index(k2, nw as int, w, k as int);
                    assert(out@[k2 * nw + w] == before[k2 * nw + w]);
                } else {
                    assert(k2 * nw + w == before.len() + w);
                }
            }
        }
        k = k + 1;
    }
}

/// The words of a family give each row's bit.
proof fn lemma_family_row(words: Seq<u64>, nk: int, nw: int, p: Pred, gs: Seq<u64>, n: int, base: Seq<i64>,
    codes: Seq<u16>, keys: Seq<i64>, stride: int, k: int, j: int)
    requires
        family_ok(words, nk, nw, p, gs, n, base, codes, keys, stride),
        0 <= k < nk,
        0 <= j < n,
        n <= nw * 64,
    ensures
        row_bit(words, nw, k, j) == row_pred(p, gs, n, base, codes, keys, stride, k, j),
{
    let w = j / 64;
    let i = j % 64;
    assert(j == 64 * w + i);
    assert(w < nw) by (nonlinear_arith) requires j == 64 * w + i, 0 <= i < 64, j < n, n <= nw * 64;
    assert(word_ok(words[k * nw + w], w, p, gs, n, base, codes, keys, stride, k));
    assert(bit(words[k * nw + w], i) == row_pred(p, gs, n, base, codes, keys, stride, k, 64 * w + i));
}

/// A family over a column of facts gives the per-row bits of one bitmap part: bitmap `k` of row `j` is
/// `holds(p, value(j), keys[group(j) * stride + k])` with `value(j)` the frame-of-reference decoding of facts.
proof fn lemma_family_col(fp: Seq<PartView>, words: Seq<u64>, nk: int, nw: int, p: Pred, base: Seq<i64>,
    codes: Seq<u16>, codes_part: PartView, base_k: int, keys: Seq<i64>, stride: int, k: int, j: int)
    requires
        src_ok(fp),
        family_ok(words, nk, nw, p, gsv(fp), n_rows(fp), base, codes, keys, stride),
        0 <= k < nk,
        0 <= j < n_rows(fp),
        n_rows(fp) <= nw * 64,
        base == FC::i64s(fp[base_k]),
        fp[base_k] is I64,
        forall|i: int| 0 <= i < n_rows(fp) ==> #[trigger] FC::code_at(codes_part, i) == codes[i] as int,
    ensures ({
        let g = FC::group_of(gsv(fp), j);
        &&& 0 <= g < gsv(fp).len() - 1
        &&& row_bit(words, nw, k, j) == holds(p, FC::for_at(gsv(fp), fp[base_k], codes_part, j), keys[kidx(g, stride, k)] as int)
    }),
{
    let gs = gsv(fp);
    FC::lemma_group_of(gs, n_rows(fp), j);
    lemma_family_row(words, nk, nw, p, gs, n_rows(fp), base, codes, keys, stride, k, j);
    assert(FC::code_at(codes_part, j) == codes[j] as int);
}

/// The month starts (days since 2000-01-01) from January 1990 through December 2001, ascending.
fn month_starts() -> (r: Vec<i64>)
    ensures r@.len() <= 144,
{
    let mut v: Vec<i64> = Vec::new();
    let mut y: i64 = 1990;
    while y <= 2001
        invariant 1990 <= y <= 2002, v@.len() == (y - 1990) * 12,
        decreases 2002 - y,
    {
        let mut m: i64 = 1;
        while m <= 12
            invariant 1990 <= y <= 2001, 1 <= m <= 13, v@.len() == (y - 1990) * 12 + (m - 1),
            decreases 13 - m,
        {
            v.push(crate::exec::datetime::date_from_civil_exec(y, m, 1));
            m = m + 1;
        }
        y = y + 1;
    }
    v
}

/// Shipdate keys of every row group: the first `SHIP_KEYS_PER_GROUP` month starts after the group's base
/// (`i64::MAX` past the table).
fn ship_keys(sbase: &[i64], ng: usize) -> (r: Vec<i64>)
    requires sbase@.len() == ng, ng * SHIP_KEYS_PER_GROUP <= usize::MAX,
    ensures r@.len() == ng * SHIP_KEYS_PER_GROUP,
{
    let ms = month_starts();
    let mut keys: Vec<i64> = Vec::new();
    let mut g: usize = 0;
    while g < ng
        invariant
            g <= ng,
            sbase@.len() == ng,
            ng * SHIP_KEYS_PER_GROUP <= usize::MAX,
            keys@.len() == g * SHIP_KEYS_PER_GROUP,
            ms@.len() <= 144,
        decreases ng - g,
    {
        let b = sbase[g];
        let mut i: usize = 0;
        while i < ms.len() && ms[i] <= b
            invariant i <= ms.len(), ms@.len() <= 144,
            decreases ms.len() - i,
        {
            i = i + 1;
        }
        let mut t: usize = 0;
        while t < SHIP_KEYS_PER_GROUP
            invariant
                t <= SHIP_KEYS_PER_GROUP,
                keys@.len() == g * SHIP_KEYS_PER_GROUP + t,
                i <= ms.len(),
                ms@.len() <= 144,
            decreases SHIP_KEYS_PER_GROUP - t,
        {
            let x = if i + t < ms.len() { ms[i + t] } else { i64::MAX };
            keys.push(x);
            t = t + 1;
        }
        proof {
            assert((g + 1) * SHIP_KEYS_PER_GROUP == g * SHIP_KEYS_PER_GROUP + SHIP_KEYS_PER_GROUP) by (nonlinear_arith);
        }
        g = g + 1;
    }
    keys
}

/// The discount codes widened to U16.
fn widen(codes: &[u8], n: usize) -> (r: Vec<u16>)
    requires codes@.len() == n,
    ensures r@.len() == n, forall|j: int| 0 <= j < n ==> #[trigger] r@[j] as int == codes@[j] as int,
{
    let mut v: Vec<u16> = Vec::with_capacity(n);
    let mut j: usize = 0;
    while j < n
        invariant
            codes@.len() == n,
            j <= n,
            v@.len() == j,
            forall|k: int| 0 <= k < j ==> #[trigger] v@[k] as int == codes@[k] as int,
        decreases n - j,
    {
        v.push(codes[j] as u16);
        j = j + 1;
    }
    v
}

/// The keys `start, start + step, ..` (`count` of them).
fn key_range(start: i64, step: i64, count: usize) -> (r: Vec<i64>)
    requires 0 <= start <= 1000, 0 <= step <= 1000, count <= 1000,
    ensures r@.len() == count, forall|k: int| 0 <= k < count ==> #[trigger] r@[k] == start + step * k,
{
    let mut v: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < count
        invariant k <= count, count <= 1000, 0 <= start <= 1000, 0 <= step <= 1000, v@.len() == k,
            forall|k2: int| 0 <= k2 < k ==> #[trigger] v@[k2] == start + step * k2,
        decreases count - k,
    {
        proof {
            assert(step * k <= 1000 * 1000) by (nonlinear_arith) requires 0 <= step <= 1000, 0 <= k <= 1000;
            assert(step * k >= 0) by (nonlinear_arith) requires 0 <= step, 0 <= k;
        }
        v.push(start + step * k as i64);
        k = k + 1;
    }
    v
}

/// The facts extents the builder reads: row groups, then codes and bases of l_discount, l_quantity, l_shipdate.
pub struct Src {
    pub gs: &'static [u64],
    pub dcodes: &'static [u8],
    pub dbase: &'static [i64],
    pub qcodes: &'static [u16],
    pub qbase: &'static [i64],
    pub scodes: &'static [u16],
    pub sbase: &'static [i64],
    /// Stored lineitem rows.
    pub n: usize,
    /// Row groups.
    pub ng: usize,
}

/// The extents are whole parts of facts `fp`.
pub open spec fn src_view_ok(s: Src, fp: Seq<PartView>) -> bool {
    &&& src_ok(fp)
    &&& s.gs@ == gsv(fp)
    &&& s.n == n_rows(fp)
    &&& s.ng == gsv(fp).len() - 1
    &&& s.dcodes@ == fp[F::LI_DISCOUNT_CODES as int]->U8_0
    &&& s.qcodes@ == fp[F::LI_QUANTITY_CODES as int]->U16_0
    &&& s.scodes@ == fp[F::LI_SHIPDATE_CODES as int]->U16_0
    &&& s.dbase@ == FC::i64s(fp[F::LI_DISCOUNT_BASE as int])
    &&& s.qbase@ == FC::i64s(fp[F::LI_QUANTITY_BASE as int])
    &&& s.sbase@ == FC::i64s(fp[F::LI_SHIPDATE_BASE as int])
}

/// Read the facts extents.
fn read_src(stores: &mut Stores) -> (s: Src)
    requires src_ok(old(stores)@.facts),
    ensures final(stores)@ == old(stores)@, src_view_ok(s, old(stores)@.facts),
{
    let ghost fp = stores@.facts;
    let n = stores.facts.part_len(F::LI_SHIPDATE_CODES);
    let ng1 = stores.facts.part_len(F::LI_GROUPS);
    let gs = stores.facts.extent_u64(F::LI_GROUPS, 0, ng1);
    proof {
        assert(gs@ =~= gsv(fp));
        assert(gs@.len() >= 1);
    }
    let ng = ng1 - 1;
    let dcodes = stores.facts.extent_u8(F::LI_DISCOUNT_CODES, 0, n);
    let dbase = stores.facts.extent_i64(F::LI_DISCOUNT_BASE, 0, ng);
    let qcodes = stores.facts.extent_u16(F::LI_QUANTITY_CODES, 0, n);
    let qbase = stores.facts.extent_i64(F::LI_QUANTITY_BASE, 0, ng);
    let scodes = stores.facts.extent_u16(F::LI_SHIPDATE_CODES, 0, n);
    let sbase = stores.facts.extent_i64(F::LI_SHIPDATE_BASE, 0, ng);
    proof {
        assert(dcodes@ =~= fp[F::LI_DISCOUNT_CODES as int]->U8_0);
        assert(qcodes@ =~= fp[F::LI_QUANTITY_CODES as int]->U16_0);
        assert(scodes@ =~= fp[F::LI_SHIPDATE_CODES as int]->U16_0);
        assert(dbase@ =~= FC::i64s(fp[F::LI_DISCOUNT_BASE as int]));
        assert(qbase@ =~= FC::i64s(fp[F::LI_QUANTITY_BASE as int]));
        assert(sbase@ =~= FC::i64s(fp[F::LI_SHIPDATE_BASE as int]));
    }
    Src { gs, dcodes, dbase, qcodes, qbase, scodes, sbase, n, ng }
}

/// Sizes: `n <= 64 nw` and, for a table below `usize::MAX / 128` rows, every family fits `usize`.
proof fn lemma_sizes(n: int, nw: int)
    requires 0 <= n, nw == n / 64 + if n % 64 == 0 { 0int } else { 1int },
    ensures
        n <= nw * 64,
        n <= usize::MAX / 128 ==> nw * 64 <= usize::MAX && 50 * nw <= usize::MAX,
{
    assert(n == 64 * (n / 64) + n % 64);
    assert(nw * 64 <= n + 64);
}

/// The inputs of every pass are well formed.
proof fn lemma_passes(s: Src, fp: Seq<PartView>, dc16: Seq<u16>, dkeys: Seq<i64>, qkeys: Seq<i64>, skeys: Seq<i64>,
    nd: int, nq: int, ns: int)
    requires
        src_view_ok(s, fp),
        dc16.len() == s.n,
        dkeys.len() == nd, qkeys.len() == nq, skeys.len() == s.ng * ns,
        0 <= ns,
    ensures
        forall|k: int| 0 <= k < nd ==> pass_ok(s.gs@, s.n as int, s.dbase@, dc16, dkeys, 0, k),
        forall|k: int| 0 <= k < nq ==> pass_ok(s.gs@, s.n as int, s.qbase@, s.qcodes@, qkeys, 0, k),
        forall|t: int| 0 <= t < ns ==> pass_ok(s.gs@, s.n as int, s.sbase@, s.scodes@, skeys, ns, t),
{
    let gsq = s.gs@;
    assert forall|k: int| 0 <= k < nd implies pass_ok(gsq, s.n as int, s.dbase@, dc16, dkeys, 0, k) by {
        assert forall|g: int| 0 <= g < gsq.len() - 1 implies #[trigger] kidx(g, 0, k) < dkeys.len() by {}
    }
    assert forall|k: int| 0 <= k < nq implies pass_ok(gsq, s.n as int, s.qbase@, s.qcodes@, qkeys, 0, k) by {
        assert forall|g: int| 0 <= g < gsq.len() - 1 implies #[trigger] kidx(g, 0, k) < qkeys.len() by {}
    }
    assert forall|t: int| 0 <= t < ns implies pass_ok(gsq, s.n as int, s.sbase@, s.scodes@, skeys, ns, t) by {
        assert forall|g: int| 0 <= g < gsq.len() - 1 implies #[trigger] kidx(g, ns, t) < skeys.len() by {
            assert(g * ns + t < s.ng * ns) by (nonlinear_arith) requires 0 <= g < s.ng, 0 <= t < ns;
        }
    }
}

/// The per-row statements of `bits_ok` from the three families.
proof fn lemma_bits(parts: Seq<PartView>, s: Src, fp: Seq<PartView>, dc16: Seq<u16>, nw: int, nd: int, nq: int, ns: int)
    requires
        src_view_ok(s, fp),
        parts.len() == LI_BITS_PARTS,
        facts_parts(parts) == fp,
        bits_shape(parts),
        n_words(parts) == nw, n_disc(parts) == nd, n_qty(parts) == nq, n_ship(parts) == ns,
        s.n <= nw * 64,
        dc16.len() == s.n,
        forall|j: int| 0 <= j < s.n ==> #[trigger] dc16[j] as int == s.dcodes@[j] as int,
        family_ok(FC::u64s(parts[DISC_BITS as int]), nd, nw, Pred::Eq, s.gs@, s.n as int, s.dbase@, dc16,
            FC::i64s(parts[DISC_KEYS as int]), 0),
        family_ok(FC::u64s(parts[QTY_BITS as int]), nq, nw, Pred::Lt, s.gs@, s.n as int, s.qbase@, s.qcodes@,
            FC::i64s(parts[QTY_KEYS as int]), 0),
        family_ok(FC::u64s(parts[SHIP_BITS as int]), ns, nw, Pred::Lt, s.gs@, s.n as int, s.sbase@, s.scodes@,
            FC::i64s(parts[SHIP_KEYS as int]), ns),
    ensures bits_ok(parts),
{
    hide(family_ok);
    let n = s.n as int;
    assert(n_rows(facts_parts(parts)) == n);
    assert forall|k: int, j: int| 0 <= k < nd && 0 <= j < n implies #[trigger] disc_bit_ok(parts, k, j) by {
        assert forall|i: int| 0 <= i < n implies #[trigger] FC::code_at(fp[F::LI_DISCOUNT_CODES as int], i) == dc16[i] as int by {
            assert(dc16[i] as int == s.dcodes@[i] as int);
        }
        lemma_family_col(fp, FC::u64s(parts[DISC_BITS as int]), nd, nw, Pred::Eq, s.dbase@, dc16,
            fp[F::LI_DISCOUNT_CODES as int], F::LI_DISCOUNT_BASE as int, FC::i64s(parts[DISC_KEYS as int]), 0, k, j);
        assert(kidx(FC::group_of(gsv(fp), j), 0, k) == k);
    }
    assert forall|t: int, j: int| 0 <= t < nq && 0 <= j < n implies #[trigger] qty_bit_ok(parts, t, j) by {
        lemma_family_col(fp, FC::u64s(parts[QTY_BITS as int]), nq, nw, Pred::Lt, s.qbase@, s.qcodes@,
            fp[F::LI_QUANTITY_CODES as int], F::LI_QUANTITY_BASE as int, FC::i64s(parts[QTY_KEYS as int]), 0, t, j);
        assert(kidx(FC::group_of(gsv(fp), j), 0, t) == t);
    }
    assert forall|t: int, j: int| 0 <= t < ns && 0 <= j < n implies #[trigger] ship_bit_ok(parts, t, j) by {
        lemma_family_col(fp, FC::u64s(parts[SHIP_BITS as int]), ns, nw, Pred::Lt, s.sbase@, s.scodes@,
            fp[F::LI_SHIPDATE_CODES as int], F::LI_SHIPDATE_BASE as int, FC::i64s(parts[SHIP_KEYS as int]), ns, t, j);
    }
}

/// The parts of facts followed by `built`.
proof fn lemma_parts(fp: Seq<PartView>, built: Seq<PartView>)
    requires fp.len() == F::FACTS_PARTS, built.len() == 7,
    ensures ({
        let parts = fp + built;
        &&& parts.len() == LI_BITS_PARTS
        &&& facts_parts(parts) == fp
        &&& parts[BITS_LAYOUT as int] == built[0]
        &&& parts[DISC_KEYS as int] == built[1]
        &&& parts[DISC_BITS as int] == built[2]
        &&& parts[QTY_KEYS as int] == built[3]
        &&& parts[QTY_BITS as int] == built[4]
        &&& parts[SHIP_KEYS as int] == built[5]
        &&& parts[SHIP_BITS as int] == built[6]
    }),
{
    assert((fp + built).subrange(0, F::FACTS_PARTS as int) =~= fp);
}

/// The bitmap parts over the facts extents `s`.
fn build_bits(s: &Src, Ghost(fp): Ghost<Seq<PartView>>) -> (out: Vec<OwnedPart>)
    requires src_view_ok(*s, fp),
    ensures owned_parts_view(out@).len() == 7, bits_ok(fp + owned_parts_view(out@)),
{
    let n = s.n;
    let ng = s.ng;
    // tables near the address-space limit get empty bitmap parts (keeps every size below usize::MAX)
    let big = n > usize::MAX / 128 || ng > usize::MAX / 128;
    let nw: usize = n / 64 + if n % 64 == 0 { 0 } else { 1 };
    proof {
        lemma_sizes(n as int, nw as int);
    }
    let nd: usize = if big { 0 } else { DISC_KEY_COUNT };
    let nq: usize = if big { 0 } else { QTY_KEY_COUNT };
    let ns: usize = if big { 0 } else { SHIP_KEYS_PER_GROUP };
    let dkeys = key_range(0, 1, nd);
    let qkeys = key_range(200, 100, nq);
    let skeys = if big { Vec::new() } else { ship_keys(s.sbase, ng) };
    let dc16 = widen(s.dcodes, n);
    proof {
        lemma_passes(*s, fp, dc16@, dkeys@, qkeys@, skeys@, nd as int, nq as int, ns as int);
    }
    let mut dbits: Vec<u64> = Vec::new();
    let mut qbits: Vec<u64> = Vec::new();
    let mut sbits: Vec<u64> = Vec::new();
    if !big {
        proof {
            assert(nd * nw <= usize::MAX && ns * nw <= usize::MAX) by (nonlinear_arith)
                requires nd == 11, ns == 6, 50 * nw <= usize::MAX, nw >= 0;
        }
        push_family(&mut dbits, &Pred::Eq, s.gs, s.dbase, &dc16, &dkeys, 0, nd, n, nw);
        push_family(&mut qbits, &Pred::Lt, s.gs, s.qbase, s.qcodes, &qkeys, 0, nq, n, nw);
        push_family(&mut sbits, &Pred::Lt, s.gs, s.sbase, s.scodes, &skeys, ns, ns, n, nw);
    }
    let mut lay: Vec<u64> = Vec::new();
    lay.push(nw as u64);
    lay.push(nd as u64);
    lay.push(nq as u64);
    lay.push(ns as u64);
    let ghost layv = lay@;
    let ghost dkv = dkeys@;
    let ghost dbv = dbits@;
    let ghost qkv = qkeys@;
    let ghost qbv = qbits@;
    let ghost skv = skeys@;
    let ghost sbv = sbits@;
    let mut out: Vec<OwnedPart> = Vec::new();
    out.push(OwnedPart::U64(lay));
    out.push(OwnedPart::I64(dkeys));
    out.push(OwnedPart::U64(dbits));
    out.push(OwnedPart::I64(qkeys));
    out.push(OwnedPart::U64(qbits));
    out.push(OwnedPart::I64(skeys));
    out.push(OwnedPart::U64(sbits));
    proof {
        let built = owned_parts_view(out@);
        assert(built.len() == 7);
        assert(built[0] == PartView::U64(layv));
        assert(built[1] == PartView::I64(dkv));
        assert(built[2] == PartView::U64(dbv));
        assert(built[3] == PartView::I64(qkv));
        assert(built[4] == PartView::U64(qbv));
        assert(built[5] == PartView::I64(skv));
        assert(built[6] == PartView::U64(sbv));
        lemma_parts(fp, built);
        let parts = fp + built;
        assert(layv[0] == nw && layv[1] == nd && layv[2] == nq && layv[3] == ns);
        assert(family_ok(dbv, nd as int, nw as int, Pred::Eq, s.gs@, n as int, s.dbase@, dc16@, dkv, 0));
        assert(family_ok(qbv, nq as int, nw as int, Pred::Lt, s.gs@, n as int, s.qbase@, s.qcodes@, qkv, 0));
        assert(family_ok(sbv, ns as int, nw as int, Pred::Lt, s.gs@, n as int, s.sbase@, s.scodes@, skv, ns as int));
        assert(skv.len() == ng * ns);
        assert(bits_shape(parts));
        lemma_bits(parts, *s, fp, dc16@, nw as int, nd as int, nq as int, ns as int);
    }
    out
}

/// Build the bitmap parts (the inherited parts of `facts` come first, unchanged).
pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= crate::gendb_entry::parallel::MAX_WORKERS,
    ensures
        match r {
            Ok(p) => forall|db: Database| #[trigger] sources_bound(old(stores)@, db)
                ==> represents(storage_parts(old(stores)@, owned_parts_view(p@)), stored_relations(db)),
            Err(QueryError::WorkerFailed(_)) => true,
            Err(_) => false,
        },
{
    let ghost sv = stores@;
    let ghost fp = sv.facts;
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    proof {
        lemma_src(sv, db0);
    }
    let s = read_src(stores);
    let out = build_bits(&s, Ghost(fp));
    proof {
        let built = owned_parts_view(out@);
        lemma_parts(fp, built);
        assert(storage_parts(sv, built) == fp + built);
        assert forall|db: Database| #[trigger] sources_bound(sv, db)
            implies represents(storage_parts(sv, built), stored_relations(db)) by {
            lemma_src(sv, db);
        }
    }
    Ok(out)
}

} // verus!
