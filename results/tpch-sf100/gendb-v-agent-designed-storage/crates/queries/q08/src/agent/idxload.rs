//! Setup of the index kernel on the calling thread: the directory slices of storage `factsdir` (`load_dirs`), tied to
//! its contract (`dirs::pdir_ok`, `dirs::odir_ok`, lineitem's key index of kind 2) for every database bound to the
//! parts, the block sizes as shifts (`shift_of`), and the dense keys of part, customer and supplier: sorted (key
//! index kind 1), distinct, and spanning exactly their row count, so row `i` holds key `first + i` (`lemma_dense`).
use vstd::prelude::*;
use vstd::arithmetic::power2::pow2;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::bound_db;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::stores::factsdir::interface as fi;
use crate::stores::factsdir::interface::dirs as fdirs;
use crate::stores::factsdir::interface::common::colfmt as fc;
use crate::stores::factsdir::interface::common::keyidx as fk;
use crate::stores::custpart::interface::common::keyidx as ck;
use crate::stores::suppliers::interface::common::keyidx as sk;
use crate::stores::factsdir::declaration as fd;
use super::model::*;
use super::kernel::*;
use super::decode::*;
use super::filters::{pf_from, pf_shape};
use super::setup::{whole_i64, whole_u32, whole_u64, first_u64};
use super::idxspec::*;
use super::idx::*;

verus! {

// ------------------------------------------------------------------------------------------------ shifts

/// `k` with `2^k == b`, or 64 when `b` is no power of two below `2^63`.
pub fn shift_of(b: usize) -> (k: usize)
    ensures k < 64 ==> pow2(k as nat) == b,
{
    proof {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
    }
    let mut k: usize = 0;
    let mut pw: u64 = 1;
    while k < 63 && pw < b as u64
        invariant
            k <= 63,
            pw as nat == pow2(k as nat),
            pow2(62) == 0x4000_0000_0000_0000,
        decreases 63 - k,
    {
        proof {
            if k < 62 {
                vstd::arithmetic::power2::lemma_pow2_strictly_increases(k as nat, 62);
            }
            vstd::arithmetic::power2::lemma_pow2_unfold((k + 1) as nat);
        }
        pw = pw * 2;
        k = k + 1;
    }
    if pw == b as u64 { k } else { 64 }
}

// ------------------------------------------------------------------------------------------------ dense keys

proof fn lemma_dense_up(key: spec_fn(int) -> int, n: int, i: int)
    requires
        0 <= i < n,
        forall|j: int| 0 <= j < n - 1 ==> #[trigger] key(j) <= key(j + 1),
        forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] key(a) != #[trigger] key(b),
    ensures key(i) >= key(0) + i,
    decreases i,
{
    if i > 0 {
        lemma_dense_up(key, n, i - 1);
        assert(key(i - 1) <= key(i));
        assert(key(i - 1) != key(i));
    }
}

proof fn lemma_dense_down(key: spec_fn(int) -> int, n: int, i: int)
    requires
        0 <= i < n,
        forall|j: int| 0 <= j < n - 1 ==> #[trigger] key(j) <= key(j + 1),
        forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] key(a) != #[trigger] key(b),
    ensures key(n - 1) >= key(i) + (n - 1 - i),
    decreases n - i,
{
    if i < n - 1 {
        lemma_dense_down(key, n, i + 1);
        assert(key(i) <= key(i + 1));
        assert(key(i) != key(i + 1));
    }
}

/// Sorted distinct keys spanning exactly `n - 1` are dense: row `i` holds key `key(0) + i`.
pub proof fn lemma_dense(key: spec_fn(int) -> int, n: int)
    requires
        n >= 1,
        forall|j: int| 0 <= j < n - 1 ==> #[trigger] key(j) <= key(j + 1),
        forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] key(a) != #[trigger] key(b),
        key(n - 1) - key(0) == n - 1,
    ensures forall|i: int| 0 <= i < n ==> #[trigger] key(i) == key(0) + i,
{
    assert forall|i: int| 0 <= i < n implies #[trigger] key(i) == key(0) + i by {
        lemma_dense_up(key, n, i);
        lemma_dense_down(key, n, i);
    }
}

/// Part keys: dense when sorted (kind 1) and the last key is `first + n - 1`.
fn part_first(f: &PFilter) -> (r: Option<i64>)
    requires pf_shape(*f),
    ensures r matches Some(first) ==> forall|i: int| 0 <= i < f.n_p ==> #[trigger] pkey(*f, i) == first + i,
{
    let n = f.n_p;
    if n == 0 {
        return Some(0);
    }
    if f.p_kind != 1 {
        return None;
    }
    proof {
        lemma_div_below(0, f.bs_p as int, f.pk_b@.len() as int);
        lemma_div_below(n - 1, f.bs_p as int, f.pk_b@.len() as int);
        assert(in_i64(pkey(*f, 0)) && in_i64(pkey(*f, n - 1)));
    }
    let first = f.pk_b[0 / f.bs_p] + f.pk_c[0] as i64;
    let last = f.pk_b[(n - 1) / f.bs_p] + f.pk_c[n - 1] as i64;
    if last as i128 - first as i128 != n as i128 - 1 {
        return None;
    }
    proof {
        let key = |i: int| pkey(*f, i);
        assert forall|j: int| 0 <= j < n - 1 implies #[trigger] key(j) <= key(j + 1) by {
            assert(ck::sorted_at(f.pk_c@, f.pk_b@, Seq::<u32>::empty(), Seq::<u64>::empty(), f.bs_p as int, f.p_kind, j));
        }
        assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies #[trigger] key(a) != #[trigger] key(b) by {
            assert(pkey(*f, a) != pkey(*f, b));
        }
        lemma_dense(key, n as int);
        assert forall|i: int| 0 <= i < f.n_p implies #[trigger] pkey(*f, i) == first + i by {
            assert(key(i) == key(0) + i);
        }
    }
    Some(first)
}

/// Customer keys: dense when sorted (kind 1) and the last key is `first + n - 1`.
fn cust_first(c: &Cols) -> (r: Option<i64>)
    requires cols_ok(*c),
    ensures r matches Some(first) ==> forall|i: int| 0 <= i < c.n_c ==> #[trigger] ck(*c, i) == first + i,
{
    let n = c.n_c;
    if n == 0 {
        return Some(0);
    }
    if c.c_kind != 1 {
        return None;
    }
    proof {
        lemma_div_below(0, c.bs_c as int, c.ck_b@.len() as int);
        lemma_div_below(n - 1, c.bs_c as int, c.ck_b@.len() as int);
        assert(in_i64(ck(*c, 0)) && in_i64(ck(*c, n - 1)));
    }
    let first = c.ck_b[0 / c.bs_c] + c.ck_c[0] as i64;
    let last = c.ck_b[(n - 1) / c.bs_c] + c.ck_c[n - 1] as i64;
    if last as i128 - first as i128 != n as i128 - 1 {
        return None;
    }
    proof {
        let key = |i: int| ck(*c, i);
        assert forall|j: int| 0 <= j < n - 1 implies #[trigger] key(j) <= key(j + 1) by {
            assert(ck::sorted_at(c.ck_c@, c.ck_b@, Seq::<u32>::empty(), Seq::<u64>::empty(), c.bs_c as int, c.c_kind, j));
        }
        assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies #[trigger] key(a) != #[trigger] key(b) by {
            assert(ck(*c, a) != ck(*c, b));
        }
        lemma_dense(key, n as int);
        assert forall|i: int| 0 <= i < c.n_c implies #[trigger] ck(*c, i) == first + i by {
            assert(key(i) == key(0) + i);
        }
    }
    Some(first)
}

/// Supplier keys: dense when sorted (kind 1) and the last key is `first + n - 1`.
fn supp_first(c: &Cols) -> (r: Option<i64>)
    requires cols_ok(*c),
    ensures r matches Some(first) ==> forall|i: int| 0 <= i < c.n_s ==> #[trigger] sk(*c, i) == first + i,
{
    let n = c.n_s;
    if n == 0 {
        return Some(0);
    }
    if c.s_kind != 1 {
        return None;
    }
    proof {
        lemma_div_below(0, c.bs_s as int, c.sk_b@.len() as int);
        lemma_div_below(n - 1, c.bs_s as int, c.sk_b@.len() as int);
        assert(in_i64(sk(*c, 0)) && in_i64(sk(*c, n - 1)));
    }
    let first = c.sk_b[0 / c.bs_s] + c.sk_c[0] as i64;
    let last = c.sk_b[(n - 1) / c.bs_s] + c.sk_c[n - 1] as i64;
    if last as i128 - first as i128 != n as i128 - 1 {
        return None;
    }
    proof {
        let key = |i: int| sk(*c, i);
        assert forall|j: int| 0 <= j < n - 1 implies #[trigger] key(j) <= key(j + 1) by {
            assert(sk::sorted_at(c.sk_c@, c.sk_b@, Seq::<u32>::empty(), Seq::<u64>::empty(), c.bs_s as int, c.s_kind, j));
        }
        assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies #[trigger] key(a) != #[trigger] key(b) by {
            assert(sk(*c, a) != sk(*c, b));
        }
        lemma_dense(key, n as int);
        assert forall|i: int| 0 <= i < c.n_s implies #[trigger] sk(*c, i) == first + i by {
            assert(key(i) == key(0) + i);
        }
    }
    Some(first)
}

// ------------------------------------------------------------------------------------------------ directories

/// The directory slices of `factsdir` as `Dirs` (shifts and first keys aside) satisfy the kernel's directory facts.
pub open spec fn dslices(sv: StoresView, d: Dirs) -> bool {
    let p = sv.factsdir;
    &&& d.ic@ == fc::u32s(p[fi::LI_KEYIDX_CODES as int]) && d.ib@ == fc::u64s(p[fi::LI_KEYIDX_BASE as int])
    &&& d.offs@ == fdirs::pdir_offs(p) && d.pkmin == fdirs::pdir_kmin(p)
    &&& d.orows@ == fdirs::odir_rows(p) && d.okmin == fdirs::odir_kmin(p)
    &&& fdirs::has_pdir(p) && fdirs::has_odir(p)
}

/// For a bound database, present directories give the kernel's directory facts.
proof fn lemma_dirs(sv: StoresView, db: Database, c: Cols, d: Dirs)
    requires
        bound_db(sv, db), cols_from(sv, c), cols_ok(c), dslices(sv, d), c.n_l < usize::MAX, d.on == d.orows@.len(),
        shift_ok(d.sl, c.bs_l) && shift_ok(d.so, c.bs_o) && shift_ok(d.sc, c.bs_c) && shift_ok(d.ss, c.bs_s),
        forall|i: int| 0 <= i < c.n_c ==> #[trigger] ck(c, i) == d.cfirst + i,
        forall|i: int| 0 <= i < c.n_s ==> #[trigger] sk(c, i) == d.sfirst + i,
    ensures dirs_ok(c, d),
{
    let p = sv.factsdir;
    let rels = fd::stored_relations(db);
    lemma_fparts(sv, db);
    assert(fi::represents(p, rels));
    let l = li_tp(sv);
    let o = or_tp(sv);
    let n = c.n_l as int;
    let no = c.n_o as int;
    assert(fi::lineitem_ok(l, rels[0]));
    assert(fi::orders_ok(o, rels[1]));
    assert(fi::table_layout_ok(l, rels[0].len() as int));
    assert(fi::table_layout_ok(o, rels[1].len() as int));
    assert(l[0] == p[0] && l[6] == p[6] && l[7] == p[7] && l[45] == p[45] && l[46] == p[46] && l[47] == p[47]);
    assert(o[0] == p[48] && o[4] == p[52] && o[5] == p[53]);
    let bs = fc::u64s(p[0])[1] as int;
    let obs = fc::u64s(p[48])[1] as int;
    assert(n == rels[0].len() && no == rels[1].len());
    assert(bs >= 1 && obs >= 1);
    // lineitem key index (kind 2: has_pdir requires it) as the kernel's row map
    let srows = fi::lineitem_rows(l, rels[0]);
    assert(fi::lineitem_cols_ok(l, srows));
    let (kc, kb, ic, ib) = (fc::u32s(l[6]), fc::i64s(l[7]), fc::u32s(l[45]), fc::u64s(l[46]));
    assert(fdirs::pdir_ok(p, n));
    assert(fk::keyidx_ok(kc, kb, ic, ib, bs, 2, n));
    let im = fk::idx_map(ic, ib, bs, n);
    assert forall|q: int| 0 <= q < n implies #[trigger] drow(c, d, q) == fdirs::pdir_irow(p, q) by {
        lemma_bs_div(c.bs_l as int, bs, n, q);
    }
    assert forall|s: int| 0 <= s < n implies #[trigger] lp(c, s) == fdirs::li_key(p, s) by {
        lemma_bs_div(c.bs_l as int, bs, n, s);
    }
    assert(dmap(c, d) =~= im) by {
        assert forall|q: int| 0 <= q < n implies dmap(c, d)[q] == im[q] by {
            assert(drow(c, d, q) == fdirs::pdir_irow(p, q));
        }
    }
    assert(d.ib@.len() * c.bs_l >= n) by {
        if bs > n && n >= 1 {
            assert(ib.len() >= 1) by (nonlinear_arith) requires ib.len() * bs >= n, n >= 1, ib.len() >= 0;
            assert(ib.len() * n >= n) by (nonlinear_arith) requires ib.len() >= 1, n >= 1;
        }
    }
    assert forall|q: int| 0 <= q < n implies #[trigger] in_dent(c, d, q) by {
        assert(fdirs::in_pentry(p, q));
        assert(fc::is_perm(im, n));
        assert(im[q] == fk::fidx(ic, ib, bs, q));
        assert(0 <= drow(c, d, q) < n);
    }
    // orders directory
    assert(fdirs::odir_ok(p, no));
    assert forall|q: int| 0 <= q < no implies #[trigger] okey(c, q) == fdirs::or_key(p, q) by {
        lemma_bs_div(c.bs_o as int, obs, no, q);
    }
    assert forall|e: int| 0 <= e < d.orows@.len() implies #[trigger] osound(c, d, e) by {
        assert(fdirs::oentry_sound(p, no, e));
    }
    assert forall|q: int| 0 <= q < no implies #[trigger] ocomplete(c, d, q) by {
        assert(fdirs::oentry_complete(p, q));
    }
    let nk = d.offs@.len() - 1;
    assert(d.ic@.len() == n);
    assert(fc::is_perm(dmap(c, d), n));
    assert(d.offs@.len() >= 1 && d.offs@[0] == 0 && d.offs@[nk] == n);
    assert(forall|e: int| 0 <= e < nk ==> #[trigger] d.offs@[e] <= d.offs@[e + 1]);
    assert(c.n_o < crate::stores::factsdir::interface::dirs::ODIR_NONE);
    assert(d.on == d.orows@.len());
}

/// The kernel's directories, when both are present, the key index has kind 2, every block size is a power of two
/// and the part, customer and supplier keys are dense; else `None` (the scan path runs).
pub fn load_dirs(st: &mut StoredParts, c: &Cols, f: &PFilter, Ghost(sv): Ghost<StoresView>, Ghost(db): Ghost<Database>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (r: Option<Dirs>)
    requires
        old(st)@ == sv.factsdir, bound_db(sv, db), cols_from(sv, *c), cols_ok(*c), pf_from(sv, ps, *f), pf_shape(*f),
    ensures
        final(st)@ == old(st)@,
        r matches Some(d) ==> dirs_ok(*c, d) && pdense(*f, d),
{
    let ghost p = sv.factsdir;
    proof {
        lemma_fparts(sv, db);
        let rels = fd::stored_relations(db);
        assert(fi::represents(p, rels));
        assert(fdirs::pdir_ok(p, rels[0].len() as int));
        assert(fdirs::odir_ok(p, rels[1].len() as int));
        let l = li_tp(sv);
        assert(fi::lineitem_ok(l, rels[0]));
        assert(fi::lineitem_cols_ok(l, fi::lineitem_rows(l, rels[0])));
        assert(l[45] == p[45] && l[46] == p[46] && l[47] == p[47]);
    }
    let pmeta = whole_i64(st, fdirs::PDIR_META);
    let ometa = whole_i64(st, fdirs::ODIR_META);
    let kind = first_u64(st, fi::LI_KEYIDX_KIND);
    if pmeta[0] != fdirs::MODE_DIRECTORY || ometa[0] != fdirs::MODE_DIRECTORY || kind != 2 || c.n_l == usize::MAX {
        return None;
    }
    let ic = whole_u32(st, fi::LI_KEYIDX_CODES);
    let ib = whole_u64(st, fi::LI_KEYIDX_BASE);
    let offs = whole_u32(st, fdirs::PDIR_OFFS);
    let orows = whole_u32(st, fdirs::ODIR_ROWS);
    let sl = shift_of(c.bs_l);
    let so = shift_of(c.bs_o);
    let sc = shift_of(c.bs_c);
    let ss = shift_of(c.bs_s);
    let sp = shift_of(f.bs_p);
    if sl >= 64 || so >= 64 || sc >= 64 || ss >= 64 || sp >= 64 {
        return None;
    }
    let pfirst = match part_first(f) {
        Some(x) => x,
        None => return None,
    };
    let cfirst = match cust_first(c) {
        Some(x) => x,
        None => return None,
    };
    let sfirst = match supp_first(c) {
        Some(x) => x,
        None => return None,
    };
    let on = orows.len();
    let d = Dirs { ic, ib, pkmin: pmeta[1], offs, okmin: ometa[1], orows, on, sl, so, sc, ss, sp, pfirst, cfirst, sfirst };
    proof {
        assert(ic@ =~= fc::u32s(p[fi::LI_KEYIDX_CODES as int]));
        assert(dslices(sv, d));
        lemma_dirs(sv, db, *c, d);
    }
    Some(d)
}

} // verus!
