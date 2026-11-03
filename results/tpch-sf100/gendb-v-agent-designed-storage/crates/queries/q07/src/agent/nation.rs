//! The nation classes of a call: the nations whose name is `$1` (class 1) and/or `$2` (class 2), listed as (key,
//! class) pairs (`build_nations`). The list's class of a key (`model::nat_cls`) is the last listed nation with that
//! key, which the scan of the nation rows keeps equal to `pcls` (the class of the last nation row with that key);
//! under the nation primary key that is the database's class of the key (`lemma_nat_ctx`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::{StoredParts, part_len};
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::typing::db_wf;
use crate::link::query::proj_all;
use crate::stores::suppliers::interface::{NATION_FIRST, NA_PARTS, NA_LAYOUT, NA_GROUPS, NA_NATIONKEY_CODES,
    NA_NATIONKEY_BASE, NA_NAME_OFFS, NA_NAME_BYTES, nation_ok};
use crate::stores::suppliers::interface::common::colfmt as scf;
use crate::stores::suppliers::interface::common::read::{text_slice, lemma_for_row};
use crate::gendb_params::Params;
use super::common::keysum::*;
use super::sqlq::{ltext, texts};
use super::reduce::*;
use super::body::*;
use super::model::*;
use super::bind::{bs_ok, lemma_bs_group, lemma_proj_at, lemma_proj_all_len};
use super::open::{whole_u8, whole_u64, whole_i64, model_bs};
use super::line::{name_cls, nat_cls_db};

verus! {

/// Nation slices.
pub struct NCols {
    pub nk_codes: &'static [u8],
    pub nk_bases: &'static [i64],
    pub n_n: usize,
    pub bs_n: usize,
    pub offs: &'static [u64],
    pub bytes: &'static [u8],
}

pub open spec fn nkey(n: NCols, i: int) -> int {
    n.nk_bases@[i / n.bs_n as int] + n.nk_codes@[i] as int
}

pub open spec fn nname(n: NCols, i: int) -> Seq<u8> {
    scf::text_of(n.offs@, n.bytes@, i)
}

/// Shapes, keys in `i64`, distinct keys.
pub open spec fn ncols_ok(n: NCols) -> bool {
    &&& n.bs_n >= 1
    &&& n.nk_codes@.len() == n.n_n
    &&& n.nk_bases@.len() * n.bs_n >= n.n_n
    &&& scf::text_parts_wf(n.offs@, n.bytes@, n.n_n as int)
    &&& forall|i: int| 0 <= i < n.n_n ==> in_i64(#[trigger] nkey(n, i))
    &&& forall|a: int, b: int| 0 <= a < n.n_n && 0 <= b < n.n_n && #[trigger] nkey(n, a) == #[trigger] nkey(n, b) ==> a == b
}

/// The nation table's rows are the decoded ones.
pub open spec fn nat_link(n: NCols, db: Database) -> bool {
    &&& n.n_n == t_nat(db).len()
    &&& forall|i: int| 0 <= i < n.n_n ==> {
        &&& (#[trigger] t_nat(db)[i])[0] == Val::Int(nkey(n, i))
        &&& t_nat(db)[i][1] == Val::Text(nname(n, i))
    }
}

/// The class of a name.
pub open spec fn ncls_of(ps: Seq<Literal>, b: Seq<u8>) -> int {
    (if b == ltext(ps[0]) { 1int } else { 0 }) + (if b == ltext(ps[1]) { 2int } else { 0 })
}

/// The class of the last of the first `i` nation rows with key `v`, 0 when none.
pub open spec fn pcls(n: NCols, ps: Seq<Literal>, v: int, i: int) -> int
    decreases i,
{
    if i <= 0 { 0 } else if nkey(n, i - 1) == v { ncls_of(ps, nname(n, i - 1)) } else { pcls(n, ps, v, i - 1) }
}

proof fn lemma_pcls_none(n: NCols, ps: Seq<Literal>, v: int, i: int)
    requires forall|r: int| 0 <= r < i ==> nkey(n, r) != v,
    ensures pcls(n, ps, v, i) == 0,
    decreases i,
{
    if i > 0 {
        lemma_pcls_none(n, ps, v, i - 1);
    }
}

proof fn lemma_pcls_at(n: NCols, ps: Seq<Literal>, v: int, i: int, r: int)
    requires
        0 <= r < i <= n.n_n,
        nkey(n, r) == v,
        forall|a: int, b: int| 0 <= a < n.n_n && 0 <= b < n.n_n && #[trigger] nkey(n, a) == #[trigger] nkey(n, b) ==> a == b,
    ensures pcls(n, ps, v, i) == ncls_of(ps, nname(n, r)),
    decreases i,
{
    if r < i - 1 {
        assert(nkey(n, i - 1) != v);
        lemma_pcls_at(n, ps, v, i - 1, r);
    }
}

/// Bytewise equality.
pub fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    assert(a@ =~= b@);
    true
}

/// The nation classes of `$1` and `$2`, as (key, class) pairs of the nations with a class.
pub fn build_nations(n: &NCols, params: &Params) -> (r: (Vec<i64>, Vec<u8>))
    requires ncols_ok(*n), texts(params@),
    ensures
        r.0@.len() == r.1@.len(),
        forall|i: int| 0 <= i < r.1@.len() ==> #[trigger] r.1@[i] < 4,
        forall|v: int| #[trigger] cls_in(r.0@, r.1@, v, r.0@.len() as int) == pcls(*n, params@, v, n.n_n as int),
{
    let ghost ps = params@;
    let mut keys: Vec<i64> = Vec::new();
    let mut cls: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n.n_n
        invariant
            ncols_ok(*n), texts(ps), ps == params@,
            i <= n.n_n,
            keys@.len() == cls@.len(),
            forall|t: int| 0 <= t < cls@.len() ==> #[trigger] cls@[t] < 4,
            forall|v: int| #[trigger] cls_in(keys@, cls@, v, keys@.len() as int) == pcls(*n, ps, v, i as int),
        decreases n.n_n - i,
    {
        proof {
            crate::stores::suppliers::interface::common::read::lemma_div_lt(i as int, n.bs_n as int, n.nk_bases@.len() as int);
            assert(in_i64(nkey(*n, i as int)));
            assert(scf::text_range_ok(n.offs@, n.bytes@, i as int));
        }
        let k = n.nk_bases[i / n.bs_n] + n.nk_codes[i] as i64;
        let name = text_slice(n.offs, n.bytes, i);
        let mut cl: u8 = 0;
        if bytes_eq(name, params.p0) {
            cl = cl + 1;
        }
        if bytes_eq(name, params.p1) {
            cl = cl + 2;
        }
        proof {
            assert(ps[0] == Literal::Text(params.p0@) && ps[1] == Literal::Text(params.p1@));
            assert(cl as int == ncls_of(ps, nname(*n, i as int)));
        }
        let ghost (k0, c0) = (keys@, cls@);
        if cl != 0 {
            keys.push(k);
            cls.push(cl);
        }
        proof {
            assert forall|v: int| #[trigger] cls_in(keys@, cls@, v, keys@.len() as int) == pcls(*n, ps, v, i + 1) by {
                if cl != 0 {
                    assert(keys@.drop_last() =~= k0 && cls@.drop_last() =~= c0);
                    assert forall|t: int| 0 <= t < k0.len() implies keys@[t] == k0[t] && cls@[t] == c0[t] by {}
                    lemma_cls_in_prefix(keys@, cls@, k0, c0, v, k0.len() as int);
                } else if nkey(*n, i as int) == v {
                    assert forall|r: int| 0 <= r < i implies nkey(*n, r) != v by {}
                    lemma_pcls_none(*n, ps, v, i as int);
                }
            }
        }
        i = i + 1;
    }
    (keys, cls)
}

/// `cls_in` over a prefix of equal entries.
proof fn lemma_cls_in_prefix(nk: Seq<i64>, nc: Seq<u8>, k0: Seq<i64>, c0: Seq<u8>, v: int, m: int)
    requires
        0 <= m <= k0.len(), m <= c0.len(), m <= nk.len(), m <= nc.len(),
        forall|t: int| 0 <= t < k0.len() ==> nk[t] == k0[t] && nc[t] == c0[t],
        k0.len() <= nk.len(),
    ensures cls_in(nk, nc, v, m) == cls_in(k0, c0, v, m),
    decreases m,
{
    if m > 0 {
        lemma_cls_in_prefix(nk, nc, k0, c0, v, m - 1);
    }
}

// ------------------------------------------------------------------------------------------------ the nation parts

/// The nation slices are whole parts of storage `suppliers`.
pub open spec fn nat_from_parts(n: NCols, p: Seq<PartView>) -> bool {
    let t = p.subrange(NATION_FIRST as int, (NATION_FIRST + NA_PARTS) as int);
    &&& p.len() == crate::stores::suppliers::interface::SUPPLIERS_PARTS
    &&& t[NA_LAYOUT as int] is U64 && scf::u64s(t[NA_LAYOUT as int]).len() == 2
    &&& n.n_n as int == scf::u64s(t[NA_LAYOUT as int])[0]
    &&& bs_ok(n.bs_n as int, scf::u64s(t[NA_LAYOUT as int])[1] as int, n.n_n as int)
    &&& t[NA_NATIONKEY_CODES as int] == PartView::U8(n.nk_codes@)
    &&& t[NA_NATIONKEY_BASE as int] == PartView::I64(n.nk_bases@)
    &&& t[NA_NAME_OFFS as int] == PartView::U64(n.offs@)
    &&& t[NA_NAME_BYTES as int] == PartView::U8(n.bytes@)
}

/// Kinds of the nation parts the call opens.
pub open spec fn nat_kinds(p: Seq<PartView>) -> bool {
    &&& p.len() == crate::stores::suppliers::interface::SUPPLIERS_PARTS
    &&& p[NATION_FIRST + NA_LAYOUT] is U64 && scf::u64s(p[NATION_FIRST + NA_LAYOUT]).len() == 2
    &&& scf::u64s(p[NATION_FIRST + NA_LAYOUT])[1] >= 1
    &&& p[NATION_FIRST + NA_NATIONKEY_CODES] is U8
    &&& part_len(p[NATION_FIRST + NA_NATIONKEY_CODES]) == scf::u64s(p[NATION_FIRST + NA_LAYOUT])[0]
    &&& p[NATION_FIRST + NA_NATIONKEY_BASE] is I64
    &&& p[NATION_FIRST + NA_NAME_OFFS] is U64 && p[NATION_FIRST + NA_NAME_BYTES] is U8
}

/// The nation table's relation in storage `suppliers`.
pub open spec fn nrel(db: Database) -> Seq<Row> { crate::stores::suppliers::declaration::stored_relations(db)[2] }

pub proof fn lemma_nat_kinds(db: Database, p: Seq<PartView>)
    requires crate::stores::suppliers::interface::represents(p, crate::stores::suppliers::declaration::stored_relations(db)),
    ensures nat_kinds(p),
{
    let t = p.subrange(NATION_FIRST as int, (NATION_FIRST + NA_PARTS) as int);
    assert(nation_ok(t, nrel(db)));
    assert forall|k: int| 0 <= k < 10 implies t[k] == p[30 + k] by {}
}

/// Open the nation slices.
pub fn open_nations(st: &mut StoredParts) -> (n: NCols)
    requires nat_kinds(old(st)@),
    ensures final(st)@ == old(st)@, nat_from_parts(n, old(st)@),
{
    let ghost p = st@;
    let lay = whole_u64(st, NATION_FIRST + NA_LAYOUT);
    let nk_codes = whole_u8(st, NATION_FIRST + NA_NATIONKEY_CODES);
    let n_n = nk_codes.len();
    let bs_n = model_bs(lay[1], n_n);
    let nk_bases = whole_i64(st, NATION_FIRST + NA_NATIONKEY_BASE);
    let offs = whole_u64(st, NATION_FIRST + NA_NAME_OFFS);
    let bytes = whole_u8(st, NATION_FIRST + NA_NAME_BYTES);
    proof {
        let t = p.subrange(NATION_FIRST as int, (NATION_FIRST + NA_PARTS) as int);
        assert forall|k: int| 0 <= k < 10 implies t[k] == p[30 + k] by {}
    }
    NCols { nk_codes, nk_bases, n_n, bs_n, offs, bytes }
}

/// The nation slices: their facts and their link to the nation table.
pub proof fn lemma_nat(db: Database, p: Seq<PartView>, n: NCols)
    requires
        db.schema == crate::schema::schema_spec(), db_wf(db),
        crate::stores::suppliers::interface::represents(p, crate::stores::suppliers::declaration::stored_relations(db)),
        nat_from_parts(n, p),
        red_ok(db),
    ensures ncols_ok(n), nat_link(n, db),
{
    let t = p.subrange(NATION_FIRST as int, (NATION_FIRST + NA_PARTS) as int);
    let rel = nrel(db);
    crate::stores::suppliers::declaration::lemma_stored_relations(db);
    assert(nation_ok(t, rel));
    let nn = rel.len() as int;
    let sb = scf::u64s(t[NA_LAYOUT as int])[1] as int;
    let b = n.bs_n as int;
    let gp = t[NA_GROUPS as int];
    let cols = crate::stores::suppliers::declaration::stored_cols_t2();
    assert(cols[0] == 0 && cols[1] == 1 && cols.len() == 4);
    lemma_proj_all_len(db.tables[6], cols);
    scf::lemma_uniform_groups(gp, nn, sb);
    scf::lemma_nblocks(nn, sb);
    super::bind::lemma_bases_cover(crate::stores::facts::interface::common::colfmt::nblocks_of(nn, sb), b, sb, nn);
    assert forall|i: int| 0 <= i < nn implies {
        &&& (#[trigger] t_nat(db)[i])[0] == Val::Int(nkey(n, i))
        &&& t_nat(db)[i][1] == Val::Text(nname(n, i))
    } by {
        lemma_proj_at(db.tables[6], cols, i, 0);
        lemma_proj_at(db.tables[6], cols, i, 1);
        lemma_for_row(gp, nn, sb, t[NA_NATIONKEY_BASE as int], t[NA_NATIONKEY_CODES as int], i);
        lemma_bs_group(b, sb, nn, i);
        assert(scf::int_col(rel, 0, scf::u64s(gp), t[NA_NATIONKEY_BASE as int], t[NA_NATIONKEY_CODES as int]));
        assert(scf::text_col(rel, 1, scf::u64s(t[NA_NAME_OFFS as int]), scf::u8s(t[NA_NAME_BYTES as int])));
    }
    assert(crate::schema::schema_spec()[6].columns[0].ty == crate::spec::types::SqlType::Int8) by (compute);
    assert(crate::schema::schema_spec()[6].columns.len() == 4) by (compute);
    super::bind::lemma_int8_vals(db, 6, 0);
    assert forall|i: int| 0 <= i < n.n_n implies in_i64(#[trigger] nkey(n, i)) by {
        assert(t_nat(db)[i][0] is Int);
    }
    assert forall|a: int, b: int| 0 <= a < n.n_n && 0 <= b < n.n_n && #[trigger] nkey(n, a) == #[trigger] nkey(n, b) implies a == b by {
        assert(colv(t_nat(db)[a], 0) == colv(t_nat(db)[b], 0));
    }
}

/// The listed classes are the database's nation classes.
pub proof fn lemma_nat_ctx(db: Database, n: NCols, ps: Seq<Literal>, v: int)
    requires ncols_ok(n), nat_link(n, db), red_ok(db), texts(ps),
    ensures pcls(n, ps, v, n.n_n as int) == nat_cls_db(db, ps, v),
{
    let rows = t_nat(db);
    if has_key(rows, 0, Val::Int(v)) {
        let r = key_pos(rows, 0, Val::Int(v));
        lemma_key_row(rows, 0, Val::Int(v));
        assert(rows[r][0] == Val::Int(nkey(n, r)));
        lemma_pcls_at(n, ps, v, n.n_n as int, r);
        assert(rows[r][1] == Val::Text(nname(n, r)));
    } else {
        assert forall|r: int| 0 <= r < n.n_n implies nkey(n, r) != v by {
            assert(rows[r][0] == Val::Int(nkey(n, r)));
            if nkey(n, r) == v {
                assert(colv(rows[r], 0) == Val::Int(v));
            }
        }
        lemma_pcls_none(n, ps, v, n.n_n as int);
    }
}

} // verus!
