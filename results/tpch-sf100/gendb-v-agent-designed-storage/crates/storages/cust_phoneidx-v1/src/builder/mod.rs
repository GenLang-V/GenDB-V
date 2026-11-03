//! Builder of storage `cust_phoneidx`: the 50 parts of `custpart` are inherited unchanged; this builder adds the
//! country-code order of the customer rows and the starts of its runs.
//!
//! Plan: `order_rows` counting-sorts the rows `0 .. n` by the first two bytes of c_phone (stable, so rows ascend
//! within a key); the order is used only if `check_perm` confirms at run time that it is a bijection of `[0, n)`.
//! `cut_runs` then walks the order and starts a new run wherever the country code (`sub2`, the bytes of the first
//! two characters) differs from the current run's; that pass proves the run property. With no rows, more than
//! `u32::MAX - 1` rows or a failed check, both new parts are empty (no index).
//!
//! Proof: `src::lemma_src` restates the source facts with this storage's definitions; `cut_runs` proves the run
//! property with `sub2`, which `sub2::lemma_sub2` equates with SQL's `SUBSTRING(c_phone, 1, 2)` (`country_code`);
//! the inherited parts are the source's parts, so every restated fact carries over to the storage's parts.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::Database;
use crate::stores::cust_phoneidx::interface::*;
use crate::stores::cust_phoneidx::declaration as D;

pub mod src;
pub mod sub2;
pub mod perm;
use src::*;
use sub2::{sub2, sub2_end, sub2_end_exec, lemma_sub2};
use perm::{check_perm, perm_view_ok, covered_u32};

verus! {

/// Offsets and bytes of `n` text values.
pub open spec fn texts_ok(o: Seq<u64>, y: Seq<u8>, n: int) -> bool {
    &&& o.len() == n + 1
    &&& y.len() <= usize::MAX
    &&& forall|r: int| 0 <= r < n ==> #[trigger] o[r] <= o[r + 1] && o[r + 1] <= y.len()
}

/// The country code (first two characters, as bytes) of text value `r`.
pub open spec fn code(o: Seq<u64>, y: Seq<u8>, r: int) -> Seq<u8> {
    sub2(y.subrange(o[r] as int, o[r + 1] as int))
}

/// Positions `lo .. hi` of the order `p` name rows of the country code `c`.
pub open spec fn one_code(o: Seq<u64>, y: Seq<u8>, p: Seq<u32>, lo: int, hi: int, c: Seq<u8>) -> bool {
    forall|j: int| lo <= j < hi ==> #[trigger] code(o, y, p[j] as int) == c
}

/// Runs `rs` (closed up to the last start) of one country code each.
pub open spec fn runs_cut(o: Seq<u64>, y: Seq<u8>, p: Seq<u32>, rs: Seq<u64>) -> bool {
    forall|t: int, j: int| 0 <= t < rs.len() - 1 && #[trigger] in_run(rs, t, j) ==>
        code(o, y, p[j] as int) == code(o, y, p[rs[t] as int] as int)
}

/// Sorting key of row `r`: its first two bytes (0 for a shorter text).
fn row_key(offs: &[u64], bytes: &[u8], n: usize, r: usize) -> (k: usize)
    requires texts_ok(offs@, bytes@, n as int), r < n,
    ensures k < 65536,
{
    let s = offs[r] as usize;
    let e = offs[r + 1] as usize;
    if e - s >= 2 {
        (bytes[s] as usize) * 256 + (bytes[s + 1] as usize)
    } else {
        0
    }
}

/// The rows `0 .. n` stably counting-sorted by `row_key` (not proved to be a permutation: the caller checks it).
fn order_rows(offs: &[u64], bytes: &[u8], n: usize) -> (p: Vec<u32>)
    requires texts_ok(offs@, bytes@, n as int), n < 0xffff_ffff,
    ensures p@.len() == n,
{
    // counts[k + 1]: rows of key k, then (prefix sums) counts[k]: the next position of key k.
    let mut counts: Vec<usize> = vec![0usize; 65537];
    let mut r: usize = 0;
    while r < n
        invariant
            texts_ok(offs@, bytes@, n as int), n < 0xffff_ffff, r <= n, counts@.len() == 65537,
            forall|k: int| 0 <= k < 65537 ==> #[trigger] counts@[k] <= r,
        decreases n - r,
    {
        let k = row_key(offs, bytes, n, r);
        let c = counts[k + 1];
        counts[k + 1] = c + 1;
        r = r + 1;
    }
    let mut k: usize = 0;
    let mut acc: usize = 0;
    while k < 65537
        invariant k <= 65537, counts@.len() == 65537, acc <= 0xffff_ffff,
        decreases 65537 - k,
    {
        let c = counts[k];
        acc = if c <= 0xffff_ffff - acc { acc + c } else { 0xffff_ffff };
        counts[k] = acc;
        k = k + 1;
    }
    let mut p: Vec<u32> = vec![0u32; n];
    let mut r: usize = 0;
    while r < n
        invariant
            texts_ok(offs@, bytes@, n as int), n < 0xffff_ffff, r <= n, counts@.len() == 65537, p@.len() == n,
        decreases n - r,
    {
        let k = row_key(offs, bytes, n, r);
        let pos = counts[k];
        if pos < n {
            p[pos] = r as u32;
            counts[k] = pos + 1;
        }
        r = r + 1;
    }
    p
}

/// `y[a .. a + len] == y[b .. b + len]`.
fn same_bytes(y: &[u8], a: usize, b: usize, len: usize) -> (r: bool)
    requires a + len <= y@.len(), b + len <= y@.len(), y@.len() <= usize::MAX,
    ensures r == (y@.subrange(a as int, a + len) == y@.subrange(b as int, b + len)),
{
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len, a + len <= y@.len(), b + len <= y@.len(), y@.len() <= usize::MAX,
            forall|q: int| 0 <= q < i ==> #[trigger] y@[a + q] == y@[b + q],
        decreases len - i,
    {
        if y[a + i] != y[b + i] {
            proof {
                assert(y@.subrange(a as int, a + len)[i as int] != y@.subrange(b as int, b + len)[i as int]);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        let ya = y@.subrange(a as int, a + len);
        let yb = y@.subrange(b as int, b + len);
        assert forall|q: int| 0 <= q < len implies #[trigger] ya[q] == yb[q] by {
            assert(y@[a + q] == y@[b + q]);
        }
        assert(ya =~= yb);
    }
    true
}

/// The country code of row `r` as the byte range `(s, len)` of `bytes`.
fn code_range(offs: &[u64], bytes: &[u8], n: usize, r: usize) -> (cr: (usize, usize))
    requires texts_ok(offs@, bytes@, n as int), r < n,
    ensures
        cr.0 + cr.1 <= bytes@.len(),
        bytes@.subrange(cr.0 as int, cr.0 + cr.1) == code(offs@, bytes@, r as int),
{
    let s = offs[r] as usize;
    let e = offs[r + 1] as usize;
    let l = sub2_end_exec(bytes, s, e);
    proof {
        let b = bytes@.subrange(s as int, e as int);
        lemma_sub2(b);
        assert(sub2(b) =~= bytes@.subrange(s as int, s + l));
    }
    (s, l)
}

/// The run starts of the order `p` (a bijection of `[0, n)`, `n >= 1`): a new run wherever the country code changes.
fn cut_runs(offs: &[u64], bytes: &[u8], n: usize, p: &Vec<u32>) -> (rs: Vec<u64>)
    requires
        texts_ok(offs@, bytes@, n as int),
        1 <= n < 0xffff_ffff,
        p@.len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] p@[i] < n,
    ensures
        rs@.len() >= 2,
        rs@[0] == 0,
        rs@[rs@.len() - 1] == n,
        forall|t: int| 0 <= t < rs@.len() - 1 ==> #[trigger] rs@[t] < rs@[t + 1],
        runs_cut(offs@, bytes@, p@, rs@),
{
    let ghost (o, y) = (offs@, bytes@);
    let mut rs: Vec<u64> = Vec::new();
    rs.push(0);
    let mut first: usize = 0;
    let (mut s0, mut l0) = code_range(offs, bytes, n, p[0] as usize);
    let mut j: usize = 1;
    while j < n
        invariant
            texts_ok(o, y, n as int), o == offs@, y == bytes@,
            1 <= n < 0xffff_ffff, p@.len() == n,
            forall|i: int| 0 <= i < n ==> #[trigger] p@[i] < n,
            first < j <= n,
            rs@.len() >= 1,
            rs@[0] == 0,
            rs@[rs@.len() - 1] == first,
            forall|t: int| 0 <= t < rs@.len() - 1 ==> #[trigger] rs@[t] < rs@[t + 1],
            runs_cut(o, y, p@, rs@),
            s0 + l0 <= y.len(),
            y.subrange(s0 as int, s0 + l0) == code(o, y, p@[first as int] as int),
            one_code(o, y, p@, first as int, j as int, code(o, y, p@[first as int] as int)),
        decreases n - j,
    {
        let (s, l) = code_range(offs, bytes, n, p[j] as usize);
        let same = l == l0 && same_bytes(bytes, s, s0, l);
        let ghost c0 = code(o, y, p@[first as int] as int);
        if same {
            proof {
                assert(code(o, y, p@[j as int] as int) == c0);
            }
        } else {
            proof {
                assert(code(o, y, p@[j as int] as int) != c0) by {
                    if l == l0 {
                        assert(y.subrange(s as int, s + l) != y.subrange(s0 as int, s0 + l0));
                    } else {
                        assert(y.subrange(s as int, s + l).len() != y.subrange(s0 as int, s0 + l0).len());
                    }
                }
            }
            let ghost rs0 = rs@;
            rs.push(j as u64);
            proof {
                assert forall|t: int, q: int| 0 <= t < rs@.len() - 1 && #[trigger] in_run(rs@, t, q) implies
                    code(o, y, p@[q] as int) == code(o, y, p@[rs@[t] as int] as int) by {
                    if t < rs0.len() - 1 {
                        assert(in_run(rs0, t, q));
                    } else {
                        assert(rs@[t] == first);
                    }
                }
                assert forall|t: int| 0 <= t < rs@.len() - 1 implies #[trigger] rs@[t] < rs@[t + 1] by {
                    if t < rs0.len() - 1 {
                        assert(rs0[t] < rs0[t + 1]);
                    }
                }
            }
            first = j;
            s0 = s;
            l0 = l;
        }
        j = j + 1;
    }
    let ghost rs0 = rs@;
    rs.push(n as u64);
    proof {
        assert forall|t: int, q: int| 0 <= t < rs@.len() - 1 && #[trigger] in_run(rs@, t, q) implies
            code(o, y, p@[q] as int) == code(o, y, p@[rs@[t] as int] as int) by {
            if t < rs0.len() - 1 {
                assert(in_run(rs0, t, q));
            } else {
                assert(rs@[t] == first);
            }
        }
        assert forall|t: int| 0 <= t < rs@.len() - 1 implies #[trigger] rs@[t] < rs@[t + 1] by {
            if t < rs0.len() - 1 {
                assert(rs0[t] < rs0[t + 1]);
            }
        }
    }
    rs
}

/// The new parts meet `index_ok` over the source's parts: absent, or a checked bijection cut into runs.
pub open spec fn built_ok(cp: Seq<PartView>, p: Seq<u32>, rs: Seq<u64>, n: int) -> bool {
    ||| p.len() == 0 && rs.len() == 0
    ||| {
        &&& p.len() == n && n >= 1
        &&& perm_view_ok(p, n)
        &&& rs.len() >= 2
        &&& rs[0] == 0
        &&& rs[rs.len() - 1] == n
        &&& forall|t: int| 0 <= t < rs.len() - 1 ==> #[trigger] rs[t] < rs[t + 1]
        &&& runs_cut(phone_offs(cp), phone_bytes(cp), p, rs)
    }
}

/// The storage's parts: the inherited parts, then the order and its runs.
proof fn lemma_built(sv: StoresView, p: Seq<u32>, rs: Seq<u64>, db: Database)
    requires
        sources_bound(sv, db),
        built_ok(sv.custpart, p, rs, n_of(sv.custpart)),
    ensures
        represents(storage_parts(sv, seq![PartView::U32(p), PartView::U64(rs)]), stored_relations(db)),
{
    let cp = sv.custpart;
    lemma_src(sv, db);
    let rel = D::stored_relations(db)[0];
    let n = rel.len() as int;
    assert(n_of(cp) == n);
    let parts = storage_parts(sv, seq![PartView::U32(p), PartView::U64(rs)]);
    assert(parts.len() == PHONEIDX_PARTS);
    assert forall|k: int| 0 <= k < CUSTPART_PARTS implies #[trigger] parts[k] == cp[k] by {}
    assert(parts[PHONE_PERM as int] == PartView::U32(p));
    assert(parts[PHONE_RUNS as int] == PartView::U64(rs));
    assert(phone_offs(parts) == phone_offs(cp) && phone_bytes(parts) == phone_bytes(cp));
    assert forall|r: int| 0 <= r < n implies #[trigger] phone_range_ok(parts, r) by {
        assert(phone_range_ok(cp, r));
    }
    assert forall|r: int| 0 <= r < rel.len() implies #[trigger] rel[r] == cu_row(phone_at(parts, r)) by {
        assert(rel[r] == cu_row(phone_at(cp, r)));
    }
    assert(perm(parts) == p);
    assert(runs(parts) == rs);
    if p.len() > 0 {
        let (o, y) = (phone_offs(cp), phone_bytes(cp));
        assert forall|r: int| 0 <= r < n implies #[trigger] listed(p, r) by {
            assert(covered_u32(p, r));
            let i = choose|i: int| 0 <= i < p.len() && p[i] == r;
            assert(p[i] == r);
        }
        let m = rs.len() - 1;
        assert forall|t: int, j: int| 0 <= t < m && #[trigger] in_run(rs, t, j) implies same_code_at(parts, t, j) by {
            assert(code(o, y, p[j] as int) == code(o, y, p[rs[t] as int] as int));
            lemma_sub2(phone_at(parts, p[j] as int));
            lemma_sub2(phone_at(parts, p[rs[t] as int] as int));
        }
    }
}

/// Number of customer rows by the source's phone offsets.
pub open spec fn n_of(cp: Seq<PartView>) -> int {
    phone_offs(cp).len() - 1
}

/// Every database bound to the sources.
proof fn lemma_built_all(sv: StoresView, p: Seq<u32>, rs: Seq<u64>)
    requires built_ok(sv.custpart, p, rs, n_of(sv.custpart)),
    ensures
        forall|db: Database| #[trigger] sources_bound(sv, db) ==>
            represents(storage_parts(sv, seq![PartView::U32(p), PartView::U64(rs)]), stored_relations(db)),
{
    assert forall|db: Database| #[trigger] sources_bound(sv, db) implies
        represents(storage_parts(sv, seq![PartView::U32(p), PartView::U64(rs)]), stored_relations(db)) by {
        lemma_built(sv, p, rs, db);
    }
}

/// The c_phone offsets and bytes of the source (whole parts) and the number of customer rows.
fn read_phones(stores: &mut Stores, Ghost(sv): Ghost<StoresView>) -> (r: (&'static [u64], &'static [u8], usize))
    requires
        old(stores)@ == sv,
        exists|db: Database| #[trigger] sources_bound(sv, db),
    ensures
        final(stores)@ == sv,
        r.0@ == phone_offs(sv.custpart),
        r.1@ == phone_bytes(sv.custpart),
        r.2 == n_of(sv.custpart),
        texts_ok(r.0@, r.1@, r.2 as int),
{
    let ghost cp = sv.custpart;
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    proof {
        lemma_src(sv, db0);
    }
    let no = stores.custpart.part_len(CU_PHONE_OFFS);
    let ny = stores.custpart.part_len(CU_PHONE_BYTES);
    let offs = stores.custpart.extent_u64(CU_PHONE_OFFS, 0, no);
    let bytes = stores.custpart.extent_u8(CU_PHONE_BYTES, 0, ny);
    proof {
        assert(bytes@.len() <= usize::MAX);
        assert(offs@ =~= phone_offs(cp));
        assert(bytes@ =~= phone_bytes(cp));
        let n = n_of(cp);
        assert forall|r: int| 0 <= r < n implies #[trigger] offs@[r] <= offs@[r + 1] && offs@[r + 1] <= bytes@.len() by {
            assert(phone_range_ok(cp, r));
        }
    }
    (offs, bytes, no - 1)
}

pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
    ensures
        match r {
            Ok(p) => forall|db: Database| #[trigger] sources_bound(old(stores)@, db)
                ==> represents(storage_parts(old(stores)@, owned_parts_view(p@)), stored_relations(db)),
            Err(QueryError::WorkerFailed(_)) => true,
            Err(_) => false,
        },
{
    let ghost sv = stores@;
    let (offs, bytes, n) = read_phones(stores, Ghost(sv));
    let (p, rs): (Vec<u32>, Vec<u64>) = if n == 0 || n >= 0xffff_ffff {
        (Vec::new(), Vec::new())
    } else {
        let p = order_rows(offs, bytes, n);
        if check_perm(&p) {
            proof {
                assert forall|i: int| 0 <= i < n implies #[trigger] p@[i] < n by {}
            }
            let rs = cut_runs(offs, bytes, n, &p);
            (p, rs)
        } else {
            (Vec::new(), Vec::new())
        }
    };
    let ghost (pv, rv) = (p@, rs@);
    let mut out: Vec<OwnedPart> = Vec::new();
    out.push(OwnedPart::U32(p));
    out.push(OwnedPart::U64(rs));
    proof {
        let built = owned_parts_view(out@);
        assert(built =~= seq![PartView::U32(pv), PartView::U64(rv)]);
        lemma_built_all(sv, pv, rv);
    }
    Ok(out)
}

} // verus!
