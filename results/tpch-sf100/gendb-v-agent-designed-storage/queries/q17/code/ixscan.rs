//! The index path over the part rows: the (p_brand, p_container, p_size) index of storage `part_bcs` lists the part
//! rows of one brand and container as one contiguous range of index positions (the sizes are consecutive directory
//! entries), so only the ~0.1% matching part rows are visited instead of scanning 20M brand and container codes.
//!
//! - The part rows in index order (`xrows`: position `p` holds custpart's value row of part row `prow(p)`) are a
//!   permutation of custpart's value rows (`lemma_pb_link`), so sums over them equal the scan's sums over `zrows`.
//! - `link_ok`: part row `r` of part_bcs and of custpart hold the same key, brand and container (both are part row
//!   `r` of the database, canonical order).
//! - `ix_all` walks the `nb * nc` (brand, container) groups of the directory in order; a group whose brand entry is
//!   `$1` and whose container entry is `$2` (tables `bm`, `cm`) is summed by `ix_group` (serial `ix_range`, or worker
//!   tasks over sub-ranges of its positions merged in order); every other group's rows keep no lineitem row.
//! Partial sums stay inside `i128`: each is bounded by the total absolute mass (`scan::mass_max`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::join::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::link::query::proj;
use crate::link::source::lemma_proj_all_index;
use crate::stores::li_pkqty::interface as LI;
use crate::stores::part_bcs::interface as PBI;
use crate::stores::part_bcs::declaration as PBD;
use crate::stores::custpart::interface::common::colfmt as CF;
use crate::stores::custpart::interface::common::read::lemma_div_lt;
use super::vals::*;
use super::typed::*;
use super::bind::*;
use super::lookup::*;
use super::scan::{mass_max, fsum, fcnt, fmass, lemma_part_bounds, lemma_sum_of_split};

verus! {

// ------------------------------------------------------------------------------------------------ part_bcs facts

/// What the index path uses about part_bcs's parts.
pub open spec fn pb_facts(pp: Seq<PartView>) -> bool {
    let n = PBI::n_rows(pp);
    &&& PBI::pa_shape(pp, n)
    &&& PBI::idx_ok(pp, n)
    &&& forall|r: int| 0 <= r < n ==> #[trigger] PBI::dict_idx_ok(pp, r)
    &&& forall|r: int| 0 <= r < n ==> i64::MIN <= #[trigger] PBI::pkey_at(pp, r) <= i64::MAX
}

/// Part row `r` of part_bcs as the statement's part value row `[p_partkey, p_brand, p_container]`.
pub open spec fn pz(pp: Seq<PartView>, r: int) -> Row {
    seq![
        Val::Int(PBI::pkey_at(pp, r)),
        Val::Text(PBI::b_text(pp, PBI::bi_at(pp, r))),
        Val::Text(PBI::c_text(pp, PBI::ci_at(pp, r))),
    ]
}

/// custpart and part_bcs hold the same part rows in the same (canonical) order.
pub open spec fn link_ok(cp: Seq<PartView>, pp: Seq<PartView>) -> bool {
    &&& n_pa(cp) == PBI::n_rows(pp)
    &&& forall|r: int| 0 <= r < n_pa(cp) ==> #[trigger] zrow(cp, r) == pz(pp, r)
}

/// The statement's part value rows in the order of the part index.
pub open spec fn xrows(cp: Seq<PartView>, pp: Seq<PartView>) -> Seq<Row> {
    Seq::new(n_pa(cp) as nat, |p: int| zrow(cp, PBI::prow(pp, p)))
}

/// The index as a sequence of part rows.
pub open spec fn pmap(pp: Seq<PartView>) -> Seq<int> {
    Seq::new(PBI::n_rows(pp) as nat, |p: int| PBI::prow(pp, p))
}

/// For a bound database: part_bcs's facts, its link to custpart and, with the index, the part rows in index order
/// are a permutation of custpart's.
pub proof fn lemma_pb_link(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        pb_facts(sv.part_bcs),
        link_ok(sv.custpart, sv.part_bcs),
        PBI::has_idx(sv.part_bcs) ==> xrows(sv.custpart, sv.part_bcs).to_multiset() == zrows(sv.custpart).to_multiset(),
{
    let (cp, pp) = (sv.custpart, sv.part_bcs);
    lemma_pa_link(sv, db);
    lemma_tables_ok(db);
    let rels = PBD::stored_relations(db);
    assert(crate::gendb_entry::stores::stored_ok(sv, db));
    assert(PBI::represents(pp, rels));
    PBD::lemma_stored_relations(db);
    let t3 = db.tables[3];
    let rel = rels[0];
    lemma_proj_all_index(t3, PBD::stored_cols_t0());
    crate::link::source::lemma_proj_all_index(t3, pcols());
    let n = rel.len() as int;
    assert(n == t3.len());
    assert(n_pa(cp) == n);
    assert forall|r: int| 0 <= r < n implies i64::MIN <= #[trigger] PBI::pkey_at(pp, r) <= i64::MAX by {
        assert(rel[r] == PBI::row_at(pp, r));
        assert(prow_ok(t3[r]));
        assert(rel[r][0] == t3[r][0]);
    }
    assert forall|r: int| 0 <= r < n implies #[trigger] zrow(cp, r) == pz(pp, r) by {
        assert(rel[r] == PBI::row_at(pp, r));
        assert(prow_ok(t3[r]));
        assert(rel[r][0] == t3[r][0]);
        assert(rel[r][1] == t3[r][3]);
        assert(rel[r][3] == t3[r][6]);
        assert(zrows(cp)[r] == zs_of(db)[r]);
        assert(zs_of(db)[r] == proj(t3[r], pcols()));
        assert(zrow(cp, r)[0] == t3[r][0]);
        assert(zrow(cp, r)[1] == t3[r][3]);
        assert(zrow(cp, r)[2] == t3[r][6]);
        assert(zrow(cp, r) =~= pz(pp, r));
    }
    assert(forall|r: int| 0 <= r < n ==> #[trigger] PBI::dict_idx_ok(pp, r));
    if PBI::has_idx(pp) {
        let m = pmap(pp);
        assert forall|i: int| 0 <= i < n implies #[trigger] CF::covered(m, i) by {
            assert(PBI::listed(pp, n, i));
            let p = choose|p: int| 0 <= p < n && #[trigger] PBI::prow(pp, p) == i;
            assert(m[p] == i);
        }
        assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies #[trigger] m[a] != #[trigger] m[b] by {
            assert(PBI::prow(pp, a) != PBI::prow(pp, b));
        }
        assert forall|p: int| 0 <= p < n implies 0 <= #[trigger] m[p] < n by {
            assert(m[p] == PBI::prow(pp, p));
        }
        assert(CF::is_perm(m, n));
        assert(zrows(cp).len() == n);
        assert forall|p: int| 0 <= p < n implies #[trigger] xrows(cp, pp)[p] == CF::stored_rows(zrows(cp), m)[p] by {
            assert(0 <= PBI::prow(pp, p) < n);
        }
        assert(xrows(cp, pp) =~= CF::stored_rows(zrows(cp), m));
        CF::lemma_stored_rows_multiset(zrows(cp), m);
    }
}

/// Sums over the part rows in index order are the sums over custpart's order.
pub proof fn lemma_xsum_all(cp: Seq<PartView>, pp: Seq<PartView>, f: spec_fn(Row) -> int)
    requires xrows(cp, pp).to_multiset() == zrows(cp).to_multiset(),
    ensures
        sum_of(xrows(cp, pp), f) == sum_of(zrows(cp), f),
        sum_of(xrows(cp, pp).subrange(0, n_pa(cp)), f) == sum_of(zrows(cp), f),
{
    lemma_sum_of_perm(xrows(cp, pp), zrows(cp), f);
    assert(xrows(cp, pp).subrange(0, n_pa(cp)) =~= xrows(cp, pp));
}

// ------------------------------------------------------------------------------------------------ the extents

/// The part_bcs extents the index path reads (whole parts).
#[derive(Clone, Copy)]
pub struct PIdx {
    /// Number of part rows.
    pub n: usize,
    /// Brand and container dictionary sizes, p_size values of the key range.
    pub nb: usize,
    pub nc: usize,
    pub ns: usize,
    /// p_partkey codes and bases (blocks of 65536 rows).
    pub kc: &'static [u32],
    pub kb: &'static [i64],
    /// Directory offsets and the part row at each index position.
    pub offs: &'static [u32],
    pub perm: &'static [u32],
}

/// The extents are the parts, with the index present and blocks of 65536 rows.
pub open spec fn pidx_ok(px: PIdx, pp: Seq<PartView>) -> bool {
    &&& pb_facts(pp)
    &&& PBI::has_idx(pp)
    &&& PBI::bsize(pp) == fast_bs()
    &&& px.n == PBI::n_rows(pp)
    &&& px.nb == PBI::n_brands(pp)
    &&& px.nc == PBI::n_conts(pp)
    &&& px.ns == PBI::idx_ns(pp)
    &&& px.kc@ == PBI::u32s(pp[PBI::PA_PARTKEY_CODES as int])
    &&& px.kb@ == PBI::i64s(pp[PBI::PA_PARTKEY_BASE as int])
    &&& px.offs@ == PBI::idx_offs(pp)
    &&& px.perm@ == PBI::idx_perm(pp)
}

/// Entry `i` of a dictionary is the text `t`.
fn dict_entry_eq(o: &[u64], y: &[u8], i: usize, t: &[u8]) -> (r: bool)
    requires PBI::dict_ok(o@, y@), i + 1 < o@.len(),
    ensures r == (PBI::dict_text(o@, y@, i as int) == t@),
{
    let ny = y.len();
    proof {
        assert(PBI::dict_range_ok(o@, y@, i as int));
        assert(o@[i as int] <= o@[i + 1] <= ny);
    }
    let a = o[i] as usize;
    let e = o[i + 1] as usize;
    let ghost d = PBI::dict_text(o@, y@, i as int);
    if e - a != t.len() {
        return false;
    }
    let mut j: usize = 0;
    while j < t.len()
        invariant
            a <= e <= y@.len(),
            e - a == t@.len(),
            d == y@.subrange(a as int, e as int),
            d == PBI::dict_text(o@, y@, i as int),
            j <= t@.len(),
            forall|x: int| 0 <= x < j ==> d[x] == t@[x],
        decreases t.len() - j,
    {
        if y[a + j] != t[j] {
            proof {
                assert(d[j as int] != t@[j as int]);
            }
            return false;
        }
        j = j + 1;
    }
    proof {
        assert(d =~= t@);
    }
    true
}

/// Which entries of a dictionary are the text `t`.
fn dict_table(o: &[u64], y: &[u8], t: &[u8]) -> (m: Vec<bool>)
    requires PBI::dict_ok(o@, y@),
    ensures
        m@.len() == o@.len() - 1,
        forall|i: int| 0 <= i < m@.len() ==> #[trigger] m@[i] == (PBI::dict_text(o@, y@, i) == t@),
{
    let mut m: Vec<bool> = Vec::new();
    let ne = o.len() - 1;
    let mut i: usize = 0;
    while i < ne
        invariant
            PBI::dict_ok(o@, y@),
            ne == o@.len() - 1,
            i <= ne,
            m@.len() == i,
            forall|x: int| 0 <= x < i ==> #[trigger] m@[x] == (PBI::dict_text(o@, y@, x) == t@),
        decreases ne - i,
    {
        let v = dict_entry_eq(o, y, i, t);
        m.push(v);
        i = i + 1;
    }
    m
}

/// The match tables of `$1` and `$2`.
pub open spec fn match_tables_ok(pp: Seq<PartView>, bm: Seq<bool>, cm: Seq<bool>, b: Seq<u8>, c: Seq<u8>) -> bool {
    &&& bm.len() == PBI::n_brands(pp)
    &&& cm.len() == PBI::n_conts(pp)
    &&& forall|i: int| 0 <= i < bm.len() ==> #[trigger] bm[i] == (PBI::b_text(pp, i) == b)
    &&& forall|i: int| 0 <= i < cm.len() ==> #[trigger] cm[i] == (PBI::c_text(pp, i) == c)
}

/// With the index present (and blocks of 65536 rows): the extents and the match tables of `t0` (`$1`) and `t1`
/// (`$2`).
pub fn read_pidx(f: &mut StoredParts, t0: &[u8], t1: &[u8], Ghost(pp): Ghost<Seq<PartView>>)
    -> (r: Option<(PIdx, Vec<bool>, Vec<bool>)>)
    requires old(f)@ == pp, pb_facts(pp),
    ensures
        final(f)@ == pp,
        r matches Some((px, bm, cm)) ==> pidx_ok(px, pp) && match_tables_ok(pp, bm@, cm@, t0@, t1@),
{
    let meta = f.extent_i64(PBI::IDX_META, 0, 3);
    let lay = f.extent_u64(PBI::PA_LAYOUT, 0, 2);
    if meta[0] != PBI::MODE_INDEX || lay[1] != 65536 {
        return None;
    }
    let n = f.part_len(PBI::PA_PARTKEY_CODES);
    let nkb = f.part_len(PBI::PA_PARTKEY_BASE);
    let nbo = f.part_len(PBI::PA_BRAND_DOFFS);
    let nby = f.part_len(PBI::PA_BRAND_DBYTES);
    let nco = f.part_len(PBI::PA_CONT_DOFFS);
    let ncy = f.part_len(PBI::PA_CONT_DBYTES);
    let no = f.part_len(PBI::IDX_OFFS);
    let kc = f.extent_u32(PBI::PA_PARTKEY_CODES, 0, n);
    let kb = f.extent_i64(PBI::PA_PARTKEY_BASE, 0, nkb);
    let bo = f.extent_u64(PBI::PA_BRAND_DOFFS, 0, nbo);
    let by = f.extent_u8(PBI::PA_BRAND_DBYTES, 0, nby);
    let co = f.extent_u64(PBI::PA_CONT_DOFFS, 0, nco);
    let cy = f.extent_u8(PBI::PA_CONT_DBYTES, 0, ncy);
    let offs = f.extent_u32(PBI::IDX_OFFS, 0, no);
    let perm = f.extent_u32(PBI::IDX_PERM, 0, n);
    proof {
        assert(PBI::has_idx(pp));
        assert(kc@ =~= PBI::u32s(pp[PBI::PA_PARTKEY_CODES as int]));
        assert(kb@ =~= PBI::i64s(pp[PBI::PA_PARTKEY_BASE as int]));
        assert(bo@ =~= PBI::b_offs(pp));
        assert(by@ =~= PBI::b_bytes(pp));
        assert(co@ =~= PBI::c_offs(pp));
        assert(cy@ =~= PBI::c_bytes(pp));
        assert(offs@ =~= PBI::idx_offs(pp));
        assert(perm@ =~= PBI::idx_perm(pp));
    }
    let ns64 = meta[2];
    if ns64 < 1 || ns64 as u64 > no as u64 {
        return None;
    }
    let ns = ns64 as usize;
    let bm = dict_table(bo, by, t0);
    let cm = dict_table(co, cy, t1);
    let px = PIdx { n, nb: nbo - 1, nc: nco - 1, ns, kc, kb, offs, perm };
    proof {
        assert(px.ns == PBI::idx_ns(pp));
    }
    Some((px, bm, cm))
}

// ------------------------------------------------------------------------------------------------ sums over positions

/// Sums over the part index positions `a .. e`.
pub open spec fn xsum(lp: Seq<PartView>, cp: Seq<PartView>, pp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>, a: int, e: int) -> int {
    sum_of(xrows(cp, pp).subrange(a, e), fsum(lp, b, c))
}

pub open spec fn xcnt(lp: Seq<PartView>, cp: Seq<PartView>, pp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>, a: int, e: int) -> int {
    sum_of(xrows(cp, pp).subrange(a, e), fcnt(lp, b, c))
}

pub open spec fn xmass(lp: Seq<PartView>, cp: Seq<PartView>, pp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>, a: int, e: int) -> int {
    sum_of(xrows(cp, pp).subrange(a, e), fmass(lp, b, c))
}

/// A range's output: the exact sum and whether a row is kept.
pub open spec fn xout_ok(lp: Seq<PartView>, cp: Seq<PartView>, pp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>, a: int, e: int,
    out: Option<(i128, bool)>) -> bool {
    out matches Some((s, any)) ==> s == xsum(lp, cp, pp, b, c, a, e) && any == (xcnt(lp, cp, pp, b, c, a, e) > 0)
}

/// Range sums: `|sum| <= mass <= total mass`, `count >= 0`.
pub proof fn lemma_xrange_bounds(lp: Seq<PartView>, cp: Seq<PartView>, pp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>, a: int, e: int)
    requires li_facts(lp), LI::has_idx(lp), 0 <= a <= e <= n_pa(cp),
    ensures
        -xmass(lp, cp, pp, b, c, a, e) <= xsum(lp, cp, pp, b, c, a, e) <= xmass(lp, cp, pp, b, c, a, e),
        xcnt(lp, cp, pp, b, c, a, e) >= 0,
        xmass(lp, cp, pp, b, c, a, e) <= sum_of(xrows(cp, pp), fmass(lp, b, c)),
{
    let xs = xrows(cp, pp);
    let w = xs.subrange(a, e);
    assert forall|i: int| 0 <= i < w.len() implies -fmass(lp, b, c)(#[trigger] w[i]) <= fsum(lp, b, c)(w[i]) <= fmass(lp, b, c)(w[i])
        && fcnt(lp, b, c)(w[i]) >= 0 by {
        lemma_part_bounds(lp, b, c, w[i]);
    }
    crate::agent::sqlmain::lemma_sum_of_within(w, fsum(lp, b, c), fmass(lp, b, c));
    lemma_sum_of_nonneg(w, fcnt(lp, b, c));
    assert forall|i: int| 0 <= i < xs.len() implies fmass(lp, b, c)(#[trigger] xs[i]) >= 0 by {
        lemma_part_bounds(lp, b, c, xs[i]);
    }
    lemma_sum_of_sub_le(xs, fmass(lp, b, c), a, e);
}

/// Index position `p`'s part row has brand `$1` and container `$2`.
pub open spec fn pos_match(pp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>, p: int) -> bool {
    let r = PBI::prow(pp, p);
    PBI::b_text(pp, PBI::bi_at(pp, r)) == b && PBI::c_text(pp, PBI::ci_at(pp, r)) == c
}

/// Everything a range of matching positions needs.
pub open spec fn range_pre(li: LiCols, px: PIdx, lp: Seq<PartView>, cp: Seq<PartView>, pp: Seq<PartView>, b: Seq<u8>,
    c: Seq<u8>, lo: int, hi: int) -> bool {
    &&& li_cols_ok(li, lp)
    &&& pidx_ok(px, pp)
    &&& link_ok(cp, pp)
    &&& sum_of(xrows(cp, pp), fmass(lp, b, c)) <= mass_max()
    &&& 0 <= lo <= hi <= px.n
    &&& forall|p: int| lo <= p < hi ==> #[trigger] pos_match(pp, b, c, p)
}

/// The part row at index position `p` and its key.
fn part_at(px: &PIdx, p: usize, Ghost(pp): Ghost<Seq<PartView>>) -> (r: (usize, i64))
    requires pidx_ok(*px, pp), p < px.n,
    ensures
        r.0 as int == PBI::prow(pp, p as int),
        r.0 < px.n,
        r.1 as int == PBI::pkey_at(pp, r.0 as int),
    no_unwind
{
    let r = px.perm[p] as usize;
    proof {
        assert(0 <= PBI::prow(pp, p as int) < px.n);
        lemma_shift16(r as u64);
        lemma_div_lt(r as int, 65536, px.kb@.len() as int);
        assert(i64::MIN <= PBI::pkey_at(pp, r as int) <= i64::MAX);
    }
    (r, px.kb[(r as u64 >> 16u64) as usize] + px.kc[r] as i64)
}

/// The positions `lo .. hi` (all matching), one after the other.
pub fn ix_range(li: &LiCols, px: &PIdx, lo: usize, hi: usize, Ghost(lp): Ghost<Seq<PartView>>,
    Ghost(cp): Ghost<Seq<PartView>>, Ghost(pp): Ghost<Seq<PartView>>, Ghost(b): Ghost<Seq<u8>>, Ghost(c): Ghost<Seq<u8>>)
    -> (out: Option<(i128, bool)>)
    requires range_pre(*li, *px, lp, cp, pp, b, c, lo as int, hi as int),
    ensures xout_ok(lp, cp, pp, b, c, lo as int, hi as int, out),
    no_unwind
{
    let ghost xs = xrows(cp, pp);
    let mut acc: i128 = 0;
    let mut any = false;
    let mut p = lo;
    proof {
        assert(xs.subrange(lo as int, lo as int) =~= Seq::<Row>::empty());
    }
    while p < hi
        invariant
            range_pre(*li, *px, lp, cp, pp, b, c, lo as int, hi as int),
            xs == xrows(cp, pp),
            lo <= p <= hi,
            acc == xsum(lp, cp, pp, b, c, lo as int, p as int),
            any == (xcnt(lp, cp, pp, b, c, lo as int, p as int) > 0),
        decreases hi - p,
    {
        let (r, k) = part_at(px, p, Ghost(pp));
        let ghost z = xs[p as int];
        proof {
            assert(pos_match(pp, b, c, p as int));
            assert(z == zrow(cp, r as int));
            assert(zrow(cp, r as int) == pz(pp, r as int));
            assert(z =~= seq![Val::Int(k as int), Val::Text(b), Val::Text(c)]);
            lemma_sum_of_sub_push(xs, fsum(lp, b, c), lo as int, p as int);
            lemma_sum_of_sub_push(xs, fcnt(lp, b, c), lo as int, p as int);
            lemma_sum_of_sub_push(xs, fmass(lp, b, c), lo as int, p as int);
            lemma_xrange_bounds(lp, cp, pp, b, c, lo as int, p as int);
            lemma_xrange_bounds(lp, cp, pp, b, c, lo as int, p + 1);
            lemma_part_bounds(lp, b, c, z);
        }
        match part_sum(li, k, Ghost(lp), Ghost(b), Ghost(c), Ghost(z)) {
            None => return None,
            Some((s, a)) => {
                acc = acc + s;
                any = any || a;
            },
        }
        p = p + 1;
    }
    Some((acc, any))
}

// ------------------------------------------------------------------------------------------------ worker tasks

/// One worker's share of a group: the positions `lo .. hi`.
pub struct IxTask {
    pub li: LiCols,
    pub px: PIdx,
    pub lo: usize,
    pub hi: usize,
    pub lp: Ghost<Seq<PartView>>,
    pub cp: Ghost<Seq<PartView>>,
    pub pp: Ghost<Seq<PartView>>,
    pub b: Ghost<Seq<u8>>,
    pub c: Ghost<Seq<u8>>,
}

impl WorkerTask for IxTask {
    type Output = Option<(i128, bool)>;

    open spec fn pre(&self) -> bool {
        range_pre(self.li, self.px, self.lp@, self.cp@, self.pp@, self.b@, self.c@, self.lo as int, self.hi as int)
    }

    open spec fn post(&self, out: Option<(i128, bool)>) -> bool {
        xout_ok(self.lp@, self.cp@, self.pp@, self.b@, self.c@, self.lo as int, self.hi as int, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: Option<(i128, bool)>) {
        ix_range(&self.li, &self.px, self.lo, self.hi, self.lp, self.cp, self.pp, self.b, self.c)
    }
}

/// The tasks `t` of a partition `bnds` of the positions `bnds[0] .. bnds[len]` (task `t` covers
/// `bnds[t] .. bnds[t + 1]`).
pub open spec fn ix_tasks_ok(tasks: Seq<IxTask>, bnds: Seq<int>, li: LiCols, px: PIdx, lp: Seq<PartView>,
    cp: Seq<PartView>, pp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>) -> bool {
    &&& bnds.len() == tasks.len() + 1
    &&& forall|t: int| 0 <= t < tasks.len() ==> {
        &&& (#[trigger] tasks[t]).lo == bnds[t]
        &&& tasks[t].hi == bnds[t + 1]
        &&& tasks[t].lp@ == lp && tasks[t].cp@ == cp && tasks[t].pp@ == pp && tasks[t].b@ == b && tasks[t].c@ == c
        &&& tasks[t].pre()
    }
}

/// `ntasks` contiguous ranges of about equal size covering the positions `lo .. hi`.
fn make_ix_tasks(li: &LiCols, px: &PIdx, lo: usize, hi: usize, ntasks: usize, Ghost(lp): Ghost<Seq<PartView>>,
    Ghost(cp): Ghost<Seq<PartView>>, Ghost(pp): Ghost<Seq<PartView>>, Ghost(b): Ghost<Seq<u8>>, Ghost(c): Ghost<Seq<u8>>)
    -> (r: (Vec<IxTask>, Ghost<Seq<int>>))
    requires
        range_pre(*li, *px, lp, cp, pp, b, c, lo as int, hi as int),
        1 <= ntasks <= MAX_WORKERS,
    ensures
        r.0@.len() == ntasks,
        ix_tasks_ok(r.0@, r.1@, *li, *px, lp, cp, pp, b, c),
        r.1@[0] == lo,
        r.1@[ntasks as int] == hi,
{
    let len = hi - lo;
    let mut tasks: Vec<IxTask> = Vec::new();
    let ghost mut bnds: Seq<int> = seq![lo as int];
    let mut a: usize = lo;
    let mut t: usize = 0;
    while t < ntasks
        invariant
            range_pre(*li, *px, lp, cp, pp, b, c, lo as int, hi as int),
            1 <= ntasks <= MAX_WORKERS,
            len == hi - lo,
            t <= ntasks,
            lo <= a <= hi,
            t == ntasks ==> a == hi,
            tasks@.len() == t,
            bnds[0] == lo,
            bnds[t as int] == a,
            ix_tasks_ok(tasks@, bnds, *li, *px, lp, cp, pp, b, c),
        decreases ntasks - t,
    {
        proof {
            let num = (t as int + 1) * (len as int);
            assert(num <= (ntasks as int) * (len as int)) by (nonlinear_arith)
                requires num == (t as int + 1) * (len as int), t + 1 <= ntasks, len >= 0;
            assert(0 <= num <= 64 * 0xffff_ffff_ffff_ffff) by (nonlinear_arith)
                requires num == (t as int + 1) * (len as int), t + 1 <= 64, 0 <= len <= 0xffff_ffff_ffff_ffff;
            assert(num / (ntasks as int) <= len as int) by (nonlinear_arith)
                requires num <= (ntasks as int) * (len as int), ntasks >= 1, num >= 0;
        }
        let e0 = lo + ((t as u128 + 1) * len as u128 / ntasks as u128) as usize;
        let e1 = if e0 < a { a } else { e0 };
        let e = if t + 1 == ntasks { hi } else { e1 };
        let task = IxTask { li: *li, px: *px, lo: a, hi: e, lp: Ghost(lp), cp: Ghost(cp), pp: Ghost(pp), b: Ghost(b), c: Ghost(c) };
        let ghost old_tasks = tasks@;
        tasks.push(task);
        proof {
            bnds = bnds.push(e as int);
            assert forall|k: int| 0 <= k < tasks@.len() implies {
                &&& (#[trigger] tasks@[k]).lo == bnds[k]
                &&& tasks@[k].hi == bnds[k + 1]
                &&& tasks@[k].lp@ == lp && tasks@[k].cp@ == cp && tasks@[k].pp@ == pp && tasks@[k].b@ == b && tasks@[k].c@ == c
                &&& tasks@[k].pre()
            } by {
                if k < t {
                    assert(tasks@[k] == old_tasks[k]);
                }
            }
        }
        a = e;
        t = t + 1;
    }
    (tasks, Ghost(bnds))
}

/// Adds the task outputs in range order: the totals over `bnds[0] .. bnds[len]`, or `None` when a task met a
/// threshold outside the fast range.
fn merge_ix(outs: &Vec<Option<(i128, bool)>>, Ghost(tv): Ghost<Seq<IxTask>>, Ghost(bnds): Ghost<Seq<int>>,
    li: &LiCols, px: &PIdx, lo: usize, hi: usize, Ghost(lp): Ghost<Seq<PartView>>,
    Ghost(cp): Ghost<Seq<PartView>>, Ghost(pp): Ghost<Seq<PartView>>, Ghost(b): Ghost<Seq<u8>>, Ghost(c): Ghost<Seq<u8>>)
    -> (r: Option<(i128, bool)>)
    requires
        range_pre(*li, *px, lp, cp, pp, b, c, lo as int, hi as int),
        ix_tasks_ok(tv, bnds, *li, *px, lp, cp, pp, b, c),
        bnds[0] == lo,
        bnds[tv.len() as int] == hi,
        outs@.len() == tv.len(),
        forall|t: int| 0 <= t < tv.len() ==> (#[trigger] tv[t]).post(outs@[t]),
    ensures xout_ok(lp, cp, pp, b, c, lo as int, hi as int, r),
{
    let ghost xs = xrows(cp, pp);
    let mut acc: i128 = 0;
    let mut any = false;
    let mut i: usize = 0;
    proof {
        assert(xs.subrange(lo as int, lo as int) =~= Seq::<Row>::empty());
    }
    while i < outs.len()
        invariant
            range_pre(*li, *px, lp, cp, pp, b, c, lo as int, hi as int),
            ix_tasks_ok(tv, bnds, *li, *px, lp, cp, pp, b, c),
            bnds[0] == lo,
            bnds[tv.len() as int] == hi,
            outs@.len() == tv.len(),
            forall|t: int| 0 <= t < tv.len() ==> (#[trigger] tv[t]).post(outs@[t]),
            xs == xrows(cp, pp),
            i <= tv.len(),
            lo <= bnds[i as int] <= px.n,
            acc == xsum(lp, cp, pp, b, c, lo as int, bnds[i as int]),
            any == (xcnt(lp, cp, pp, b, c, lo as int, bnds[i as int]) > 0),
        decreases outs.len() - i,
    {
        let ghost (m, e) = (bnds[i as int], bnds[i + 1]);
        proof {
            assert(tv[i as int].pre());
            assert(tv[i as int].post(outs@[i as int]));
            if i + 1 < tv.len() {
                assert(tv[i + 1].pre());
                assert(tv[i + 1].lo == bnds[i + 1]);
            }
        }
        let o = outs[i];
        let (s, a) = match o {
            Some(x) => x,
            None => return None,
        };
        proof {
            lemma_sum_of_split(xs, fsum(lp, b, c), lo as int, m, e);
            lemma_sum_of_split(xs, fcnt(lp, b, c), lo as int, m, e);
            lemma_sum_of_split(xs, fmass(lp, b, c), lo as int, m, e);
            lemma_xrange_bounds(lp, cp, pp, b, c, lo as int, m);
            lemma_xrange_bounds(lp, cp, pp, b, c, m, e);
            lemma_xrange_bounds(lp, cp, pp, b, c, lo as int, e);
        }
        acc = acc + s;
        any = any || a;
        i = i + 1;
    }
    Some((acc, any))
}

/// Matching part rows per worker task (fewer tasks for a small group: thread start costs more than it saves).
pub const PARTS_PER_TASK: usize = 768;

/// The positions `lo .. hi` (all matching): serially, or split into worker tasks merged in order.
fn ix_group(li: &LiCols, px: &PIdx, lo: usize, hi: usize, workers: usize, dispatch: &mut Dispatch,
    Ghost(lp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(pp): Ghost<Seq<PartView>>,
    Ghost(b): Ghost<Seq<u8>>, Ghost(c): Ghost<Seq<u8>>)
    -> (r: Result<Option<(i128, bool)>, QueryError>)
    requires
        range_pre(*li, *px, lp, cp, pp, b, c, lo as int, hi as int),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(o) ==> xout_ok(lp, cp, pp, b, c, lo as int, hi as int, o),
        r matches Err(e) ==> e is WorkerFailed,
{
    let want = (hi - lo) / PARTS_PER_TASK;
    let ntasks = if want < workers { want } else { workers };
    if ntasks <= 1 {
        return Ok(ix_range(li, px, lo, hi, Ghost(lp), Ghost(cp), Ghost(pp), Ghost(b), Ghost(c)));
    }
    let (tasks, Ghost(bnds)) = make_ix_tasks(li, px, lo, hi, ntasks, Ghost(lp), Ghost(cp), Ghost(pp), Ghost(b), Ghost(c));
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    Ok(merge_ix(&outs, Ghost(tv), Ghost(bnds), li, px, lo, hi, Ghost(lp), Ghost(cp), Ghost(pp), Ghost(b), Ghost(c)))
}

// ------------------------------------------------------------------------------------------------ the groups

/// `(g + 1) * ns <= nb * nc * ns` for a group `g < nb * nc`, and `g * ns + ns == (g + 1) * ns`.
proof fn lemma_group_bounds(g: int, ns: int, ng: int)
    requires 0 <= g < ng, ns >= 1,
    ensures
        0 <= g * ns,
        g * ns + ns == (g + 1) * ns,
        (g + 1) * ns <= ng * ns,
{
    assert(0 <= g * ns) by (nonlinear_arith) requires g >= 0, ns >= 1;
    assert(g * ns + ns == (g + 1) * ns) by (nonlinear_arith);
    assert((g + 1) * ns <= ng * ns) by (nonlinear_arith) requires g + 1 <= ng, ns >= 1;
}

/// `h * ns + t` with `0 <= t < ns` lies in `g * ns .. (g + 1) * ns` only for `h == g`.
proof fn lemma_radix(h: int, t: int, g: int, ns: int)
    requires 0 <= t < ns, 0 <= h, 0 <= g, g * ns <= h * ns + t < g * ns + ns,
    ensures h == g,
{
    if h < g {
        assert(h * ns + ns <= g * ns) by (nonlinear_arith) requires h + 1 <= g, ns >= 0;
    } else if h > g {
        assert(g * ns + ns <= h * ns) by (nonlinear_arith) requires g + 1 <= h, ns >= 0;
    }
}

/// A position of group `g = bi * nc + ci` (entries `g * ns .. (g + 1) * ns`): its row has brand entry `bi` and
/// container entry `ci`.
proof fn lemma_zone(pp: Seq<PartView>, bi: int, ci: int, p: int)
    requires
        pb_facts(pp),
        PBI::has_idx(pp),
        0 <= bi < PBI::n_brands(pp),
        0 <= ci < PBI::n_conts(pp),
        0 <= p < PBI::n_rows(pp),
        PBI::idx_offs(pp)[(bi * PBI::n_conts(pp) + ci) * PBI::idx_ns(pp)] <= p,
        p < PBI::idx_offs(pp)[(bi * PBI::n_conts(pp) + ci) * PBI::idx_ns(pp) + PBI::idx_ns(pp)],
    ensures ({
        let r = PBI::prow(pp, p);
        &&& 0 <= r < PBI::n_rows(pp)
        &&& PBI::bi_at(pp, r) == bi
        &&& PBI::ci_at(pp, r) == ci
    }),
{
    let n = PBI::n_rows(pp);
    let (nb, nc, ns) = (PBI::n_brands(pp), PBI::n_conts(pp), PBI::idx_ns(pp));
    let g = bi * nc + ci;
    assert(0 <= bi * nc) by (nonlinear_arith) requires bi >= 0, nc >= 0;
    assert(g < nb * nc) by (nonlinear_arith) requires bi + 1 <= nb, 0 <= ci < nc, g == bi * nc + ci;
    assert(nb * nc * ns == (nb * nc) * ns) by (nonlinear_arith);
    lemma_group_bounds(g, ns, nb * nc);
    PBI::lemma_entries_exact(pp, n, g * ns, g * ns + ns, p);
    let r = PBI::prow(pp, p);
    assert(0 <= r < n);
    assert(PBI::dict_idx_ok(pp, r));
    assert(PBI::size_in(pp, r));
    let (rb, rc) = (PBI::bi_at(pp, r), PBI::ci_at(pp, r));
    let h = rb * nc + rc;
    assert(0 <= rb * nc) by (nonlinear_arith) requires rb >= 0, nc >= 0;
    let t = PBI::size_at(pp, r) - PBI::idx_smin(pp);
    assert(PBI::comp_at(pp, r) == h * ns + t);
    lemma_radix(h, t, g, ns);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(g, nc, bi, ci);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(g, nc, rb, rc);
}

/// The directory's first offset is 0 and its last is `n`.
proof fn lemma_offs_ends(pp: Seq<PartView>)
    requires pb_facts(pp), PBI::has_idx(pp),
    ensures
        PBI::idx_offs(pp)[0] == 0,
        PBI::idx_offs(pp)[PBI::idx_nkeys(pp)] == PBI::n_rows(pp),
        PBI::idx_nkeys(pp) == PBI::n_brands(pp) * PBI::n_conts(pp) * PBI::idx_ns(pp),
{
    let n = PBI::n_rows(pp);
    let nk = PBI::idx_nkeys(pp);
    let o = PBI::idx_offs(pp);
    PBI::lemma_offs_mono(pp, n, 0, nk);
    if n > 0 {
        assert(PBI::in_entry(pp, 0));
        let e = PBI::comp_at(pp, PBI::prow(pp, 0));
        PBI::lemma_offs_mono(pp, n, 0, e);
        assert(PBI::in_entry(pp, n - 1));
        let f = PBI::comp_at(pp, PBI::prow(pp, n - 1));
        PBI::lemma_offs_mono(pp, n, f + 1, nk);
    }
}

/// A group whose brand or container entry is not `$1` / `$2`: its positions add nothing.
proof fn lemma_group_zero(lp: Seq<PartView>, cp: Seq<PartView>, pp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>,
    bi: int, ci: int, lo: int, hi: int)
    requires
        li_facts(lp), LI::has_idx(lp),
        pb_facts(pp), PBI::has_idx(pp),
        link_ok(cp, pp),
        0 <= bi < PBI::n_brands(pp),
        0 <= ci < PBI::n_conts(pp),
        PBI::b_text(pp, bi) != b || PBI::c_text(pp, ci) != c,
        lo == PBI::idx_offs(pp)[(bi * PBI::n_conts(pp) + ci) * PBI::idx_ns(pp)],
        hi == PBI::idx_offs(pp)[(bi * PBI::n_conts(pp) + ci) * PBI::idx_ns(pp) + PBI::idx_ns(pp)],
        0 <= lo <= hi <= PBI::n_rows(pp),
    ensures
        sum_of(xrows(cp, pp).subrange(lo, hi), fsum(lp, b, c)) == 0,
        sum_of(xrows(cp, pp).subrange(lo, hi), fcnt(lp, b, c)) == 0,
        sum_of(xrows(cp, pp).subrange(lo, hi), fmass(lp, b, c)) == 0,
{
    let xs = xrows(cp, pp);
    let w = xs.subrange(lo, hi);
    let ys = irows(lp);
    assert forall|i: int| 0 <= i < w.len() implies fsum(lp, b, c)(#[trigger] w[i]) == 0 && fcnt(lp, b, c)(w[i]) == 0
        && fmass(lp, b, c)(w[i]) == 0 by {
        let p = lo + i;
        lemma_zone(pp, bi, ci, p);
        let r = PBI::prow(pp, p);
        let z = w[i];
        assert(z == xs[p]);
        assert(z == zrow(cp, r));
        assert(zrow(cp, r) == pz(pp, r));
        assert(z[1] != Val::Text(b) || z[2] != Val::Text(c));
        assert forall|j: int| 0 <= j < ys.len() implies !kept(ys, b, c, #[trigger] ys[j], z) by {}
        lemma_sum_of_zero(ys, tsum(ys, b, c, z));
        lemma_sum_of_zero(ys, tcnt(ys, b, c, z));
        lemma_sum_of_zero(ys, tmass(ys, b, c, z));
    }
    lemma_sum_of_zero(w, fsum(lp, b, c));
    lemma_sum_of_zero(w, fcnt(lp, b, c));
    lemma_sum_of_zero(w, fmass(lp, b, c));
}

/// A group whose brand and container entries are `$1` and `$2`: every position matches.
proof fn lemma_group_match(pp: Seq<PartView>, b: Seq<u8>, c: Seq<u8>, bi: int, ci: int, lo: int, hi: int)
    requires
        pb_facts(pp), PBI::has_idx(pp),
        0 <= bi < PBI::n_brands(pp),
        0 <= ci < PBI::n_conts(pp),
        PBI::b_text(pp, bi) == b && PBI::c_text(pp, ci) == c,
        lo == PBI::idx_offs(pp)[(bi * PBI::n_conts(pp) + ci) * PBI::idx_ns(pp)],
        hi == PBI::idx_offs(pp)[(bi * PBI::n_conts(pp) + ci) * PBI::idx_ns(pp) + PBI::idx_ns(pp)],
        hi <= PBI::n_rows(pp),
    ensures forall|p: int| lo <= p < hi ==> #[trigger] pos_match(pp, b, c, p),
{
    assert forall|p: int| lo <= p < hi implies #[trigger] pos_match(pp, b, c, p) by {
        assert(0 <= lo) by {
            lemma_offs_ends(pp);
            let (nb, nc, ns) = (PBI::n_brands(pp), PBI::n_conts(pp), PBI::idx_ns(pp));
            let g = bi * nc + ci;
            assert(0 <= bi * nc) by (nonlinear_arith) requires bi >= 0, nc >= 0;
            assert(g < nb * nc) by (nonlinear_arith) requires bi + 1 <= nb, 0 <= ci < nc, g == bi * nc + ci;
            assert(nb * nc * ns == (nb * nc) * ns) by (nonlinear_arith);
            lemma_group_bounds(g, ns, nb * nc);
            PBI::lemma_offs_mono(pp, PBI::n_rows(pp), 0, g * ns);
        }
        lemma_zone(pp, bi, ci, p);
    }
}

/// Every part row through the index: the groups in directory order, the matching ones summed by `ix_group`.
pub fn ix_all(li: &LiCols, px: &PIdx, bm: &Vec<bool>, cm: &Vec<bool>, workers: usize, dispatch: &mut Dispatch,
    Ghost(lp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(pp): Ghost<Seq<PartView>>,
    Ghost(b): Ghost<Seq<u8>>, Ghost(c): Ghost<Seq<u8>>)
    -> (r: Result<Option<(i128, bool)>, QueryError>)
    requires
        li_cols_ok(*li, lp),
        pidx_ok(*px, pp),
        link_ok(cp, pp),
        match_tables_ok(pp, bm@, cm@, b, c),
        sum_of(xrows(cp, pp), fmass(lp, b, c)) <= mass_max(),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(o) ==> xout_ok(lp, cp, pp, b, c, 0, n_pa(cp), o),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost xs = xrows(cp, pp);
    let nb = px.nb;
    let nc = px.nc;
    let ns = px.ns;
    let no = px.offs.len();
    proof {
        lemma_offs_ends(pp);
        assert(nb * nc * ns == (nb * nc) * ns) by (nonlinear_arith);
        assert(nb * nc <= (nb * nc) * ns) by (nonlinear_arith) requires ns >= 1, nb * nc >= 0;
        assert(px.offs@.len() == nb * nc * ns + 1);
        assert(no == (nb * nc) * ns + 1);
    }
    let ng = nb * nc;
    proof {
        if ng > 0 {
            assert(nb > 0 && nc > 0) by (nonlinear_arith) requires ng == nb * nc, nb >= 0, nc >= 0, ng > 0;
        }
    }
    let mut acc: i128 = 0;
    let mut any = false;
    let mut g: usize = 0;
    let mut bi: usize = 0;
    let mut ci: usize = 0;
    proof {
        assert(xs.subrange(0, 0) =~= Seq::<Row>::empty());
    }
    while g < ng
        invariant
            li_cols_ok(*li, lp),
            pidx_ok(*px, pp),
            link_ok(cp, pp),
            match_tables_ok(pp, bm@, cm@, b, c),
            sum_of(xrows(cp, pp), fmass(lp, b, c)) <= mass_max(),
            1 <= workers <= MAX_WORKERS,
            xs == xrows(cp, pp),
            nb == px.nb && nc == px.nc && ns == px.ns,
            ng == nb * nc,
            ng * ns + 1 == px.offs@.len(),
            no == px.offs@.len(),
            PBI::idx_offs(pp)[0] == 0,
            PBI::idx_offs(pp)[PBI::idx_nkeys(pp)] == PBI::n_rows(pp),
            g <= ng,
            g == bi * nc + ci,
            g < ng ==> bi < nb && ci < nc,
            acc == xsum(lp, cp, pp, b, c, 0, px.offs@[(g * ns) as int] as int),
            any == (xcnt(lp, cp, pp, b, c, 0, px.offs@[(g * ns) as int] as int) > 0),
        decreases ng - g,
    {
        proof {
            lemma_group_bounds(g as int, ns as int, ng as int);
            PBI::lemma_offs_mono(pp, px.n as int, (g * ns) as int, (g * ns + ns) as int);
            PBI::lemma_offs_mono(pp, px.n as int, (g * ns + ns) as int, PBI::idx_nkeys(pp));
        }
        let lo = px.offs[g * ns] as usize;
        let hi = px.offs[g * ns + ns] as usize;
        let ghost (gb, gc) = (bi as int, ci as int);
        proof {
            assert(g * ns == (bi * nc + ci) * ns);
        }
        if bm[bi] && cm[ci] {
            proof {
                lemma_group_match(pp, b, c, gb, gc, lo as int, hi as int);
            }
            let o = match ix_group(li, px, lo, hi, workers, dispatch, Ghost(lp), Ghost(cp), Ghost(pp), Ghost(b), Ghost(c)) {
                Ok(o) => o,
                Err(e) => return Err(e),
            };
            let (s, a) = match o {
                Some(x) => x,
                None => return Ok(None),
            };
            proof {
                lemma_sum_of_split(xs, fsum(lp, b, c), 0, lo as int, hi as int);
                lemma_sum_of_split(xs, fcnt(lp, b, c), 0, lo as int, hi as int);
                lemma_sum_of_split(xs, fmass(lp, b, c), 0, lo as int, hi as int);
                lemma_xrange_bounds(lp, cp, pp, b, c, 0, lo as int);
                lemma_xrange_bounds(lp, cp, pp, b, c, lo as int, hi as int);
                lemma_xrange_bounds(lp, cp, pp, b, c, 0, hi as int);
            }
            acc = acc + s;
            any = any || a;
        } else {
            proof {
                lemma_group_zero(lp, cp, pp, b, c, gb, gc, lo as int, hi as int);
                lemma_sum_of_split(xs, fsum(lp, b, c), 0, lo as int, hi as int);
                lemma_sum_of_split(xs, fcnt(lp, b, c), 0, lo as int, hi as int);
            }
        }
        proof {
            assert((g + 1) * ns == g * ns + ns) by (nonlinear_arith);
        }
        g = g + 1;
        ci = ci + 1;
        if ci == nc {
            ci = 0;
            bi = bi + 1;
            proof {
                assert(g == bi * nc) by (nonlinear_arith) requires g == (bi - 1) * nc + nc;
                if g < ng {
                    assert(bi < nb) by (nonlinear_arith) requires g == bi * nc, g < nb * nc, nc >= 1;
                }
            }
        } else {
            proof {
                if g < ng {
                    assert(bi < nb) by (nonlinear_arith) requires g == bi * nc + ci, g < nb * nc, ci >= 0, ci < nc;
                }
            }
        }
    }
    proof {
        assert(g * ns == PBI::idx_nkeys(pp));
    }
    Ok(Some((acc, any)))
}

} // verus!
