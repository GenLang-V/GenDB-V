//! Column views of the four flat storages Q21 reads (`flat_lineitem`, `flat_orders`, `flat_supplier`, `flat_nation`)
//! and how they denote the database tables.
//!
//! Every column is one stored part (a plain array in source row order; a text column is an offsets part and a bytes
//! part). `lk(sv)[i]` is `l_orderkey` of lineitem row `i`, `lc(sv)[i]` / `lr(sv)[i]` its commit / receipt date (days
//! since 1970-01-01), `ostat(sv, j)` the bytes of `o_orderstatus` of orders row `j`, `sname(sv, s)` the bytes of
//! `s_name` of supplier row `s`, and so on. For a database bound to the parts (`bound_db`), row `i` of a table has
//! these values at the columns' table ordinals (`lemma_*_row`), and the declared primary keys make the key columns
//! of `orders`, `supplier` and `nation` duplicate-free (`lemma_keys_unique`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::typing::*;
use crate::spec::constraints::*;
use crate::spec::types::Constraint;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::gendb_constraints::declared_db;
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::link::query::{text_at, text_wf, TextView, proj};
use crate::link::source::lemma_proj_all_index;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_lineitem::declaration as lid;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_orders::declaration as oid;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_supplier::declaration as sid;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_nation::declaration as nid;

verus! {

// ------------------------------------------------------------------------------------------------ column views

/// `l_orderkey` of every lineitem row.
pub open spec fn lk(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_ORDERKEY as int]) }

/// `l_suppkey` of every lineitem row.
pub open spec fn ls(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_SUPPKEY as int]) }

/// `l_commitdate` of every lineitem row (days since 1970-01-01).
pub open spec fn lc(sv: StoresView) -> Seq<i32> { li::i32s(sv.flat_lineitem[li::L_COMMITDATE as int]) }

/// `l_receiptdate` of every lineitem row (days since 1970-01-01).
pub open spec fn lr(sv: StoresView) -> Seq<i32> { li::i32s(sv.flat_lineitem[li::L_RECEIPTDATE as int]) }

/// `o_orderkey` of every orders row.
pub open spec fn ok(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_ORDERKEY as int]) }

/// The `o_orderstatus` text column.
pub open spec fn ostat_col(sv: StoresView) -> TextView {
    oi::text_view(sv.flat_orders, oi::O_ORDERSTATUS_OFFSETS as int, oi::O_ORDERSTATUS_BYTES as int)
}

/// `o_orderstatus` of orders row `j` (its bytes).
pub open spec fn ostat(sv: StoresView, j: int) -> Seq<u8> { text_at(ostat_col(sv), j) }

/// `s_suppkey` of every supplier row.
pub open spec fn skey(sv: StoresView) -> Seq<i64> { si::i64s(sv.flat_supplier[si::S_SUPPKEY as int]) }

/// `s_nationkey` of every supplier row.
pub open spec fn snk(sv: StoresView) -> Seq<i64> { si::i64s(sv.flat_supplier[si::S_NATIONKEY as int]) }

/// The `s_name` text column.
pub open spec fn sname_col(sv: StoresView) -> TextView {
    si::text_view(sv.flat_supplier, si::S_NAME_OFFSETS as int, si::S_NAME_BYTES as int)
}

/// `s_name` of supplier row `s` (its bytes).
pub open spec fn sname(sv: StoresView, s: int) -> Seq<u8> { text_at(sname_col(sv), s) }

/// `n_nationkey` of every nation row.
pub open spec fn nkey(sv: StoresView) -> Seq<i64> { ni::i64s(sv.flat_nation[ni::N_NATIONKEY as int]) }

/// The `n_name` text column.
pub open spec fn nname_col(sv: StoresView) -> TextView {
    ni::text_view(sv.flat_nation, ni::N_NAME_OFFSETS as int, ni::N_NAME_BYTES as int)
}

/// `n_name` of nation row `n` (its bytes).
pub open spec fn nname(sv: StoresView, n: int) -> Seq<u8> { text_at(nname_col(sv), n) }

/// Row counts of the four tables.
pub open spec fn n_l(sv: StoresView) -> int { lk(sv).len() as int }
pub open spec fn n_o(sv: StoresView) -> int { ok(sv).len() as int }
pub open spec fn n_s(sv: StoresView) -> int { skey(sv).len() as int }
pub open spec fn n_n(sv: StoresView) -> int { nkey(sv).len() as int }

// ------------------------------------------------------------------------------------------------ shapes

/// The parts have the shape of the four flat storages: every column has one value per row and every text column
/// is well formed. (A consequence of `bound_db`, `lemma_parts_shape`.)
pub open spec fn parts_shape(sv: StoresView) -> bool {
    &&& li::parts_wf(sv.flat_lineitem, n_l(sv))
    &&& oi::parts_wf(sv.flat_orders, n_o(sv))
    &&& si::parts_wf(sv.flat_supplier, n_s(sv))
    &&& ni::parts_wf(sv.flat_nation, n_n(sv))
}

/// The column facts the executable code relies on (implied by `parts_shape`).
pub open spec fn cols_shape(sv: StoresView) -> bool {
    &&& ls(sv).len() == n_l(sv)
    &&& lc(sv).len() == n_l(sv)
    &&& lr(sv).len() == n_l(sv)
    &&& text_wf(ostat_col(sv), n_o(sv))
    &&& snk(sv).len() == n_s(sv)
    &&& text_wf(sname_col(sv), n_s(sv))
    &&& text_wf(nname_col(sv), n_n(sv))
}

pub proof fn lemma_shape_cols(sv: StoresView)
    requires parts_shape(sv),
    ensures cols_shape(sv),
{
}

/// The parts of a bound database have the storages' shape, and the tables have the parts' row counts.
pub proof fn lemma_parts_shape(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        parts_shape(sv),
        cols_shape(sv),
        db.tables.len() == 8,
        db.tables[0].len() == n_l(sv),
        db.tables[1].len() == n_o(sv),
        db.tables[5].len() == n_s(sv),
        db.tables[6].len() == n_n(sv),
{
    lid::lemma_declared_schema();
    lemma_proj_all_index(db.tables[0], lid::stored_cols_t0());
    lemma_proj_all_index(db.tables[1], oid::stored_cols_t0());
    lemma_proj_all_index(db.tables[5], sid::stored_cols_t0());
    lemma_proj_all_index(db.tables[6], nid::stored_cols_t0());
    assert(lid::stored_relations(db)[0].len() == db.tables[0].len());
    assert(oid::stored_relations(db)[0].len() == db.tables[1].len());
    assert(sid::stored_relations(db)[0].len() == db.tables[5].len());
    assert(nid::stored_relations(db)[0].len() == db.tables[6].len());
}

// ------------------------------------------------------------------------------------------------ rows

/// Lineitem row `i`: arity, `l_orderkey`, `l_suppkey`, `l_commitdate`, `l_receiptdate`.
pub proof fn lemma_lineitem_row(sv: StoresView, db: Database, i: int)
    requires bound_db(sv, db), 0 <= i < db.tables[0].len(),
    ensures
        db.tables[0][i].len() == 16,
        db.tables[0][i][0] == Val::Int(lk(sv)[i] as int),
        db.tables[0][i][2] == Val::Int(ls(sv)[i] as int),
        db.tables[0][i][11] == date32_val(lc(sv)[i]),
        db.tables[0][i][12] == date32_val(lr(sv)[i]),
{
    lemma_parts_shape(sv, db);
    lid::lemma_declared_schema();
    let t = db.tables[0];
    let cols = lid::stored_cols_t0();
    let rels = lid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][i] == li::row_at(sv.flat_lineitem, i));
    assert(rels[0][i] == proj(t[i], cols));
    assert(row_in_table(t[i], db.schema[0]));
    assert(cols[0] == 0 && cols[2] == 2 && cols[11] == 11 && cols[12] == 12);
    assert(proj(t[i], cols)[0] == t[i][0]);
    assert(proj(t[i], cols)[2] == t[i][2]);
    assert(proj(t[i], cols)[11] == t[i][11]);
    assert(proj(t[i], cols)[12] == t[i][12]);
}

/// Orders row `j`: arity, `o_orderkey`, `o_orderstatus`.
pub proof fn lemma_orders_row(sv: StoresView, db: Database, j: int)
    requires bound_db(sv, db), 0 <= j < db.tables[1].len(),
    ensures
        db.tables[1][j].len() == 9,
        db.tables[1][j][0] == Val::Int(ok(sv)[j] as int),
        db.tables[1][j][2] == Val::Text(ostat(sv, j)),
{
    lemma_parts_shape(sv, db);
    oid::lemma_declared_schema();
    let t = db.tables[1];
    let cols = oid::stored_cols_t0();
    let rels = oid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][j] == oi::row_at(sv.flat_orders, j));
    assert(rels[0][j] == proj(t[j], cols));
    assert(row_in_table(t[j], db.schema[1]));
    assert(cols[0] == 0 && cols[2] == 2);
    assert(proj(t[j], cols)[0] == t[j][0]);
    assert(proj(t[j], cols)[2] == t[j][2]);
}

/// Supplier row `s`: arity, `s_suppkey`, `s_name`, `s_nationkey`.
pub proof fn lemma_supplier_row(sv: StoresView, db: Database, s: int)
    requires bound_db(sv, db), 0 <= s < db.tables[5].len(),
    ensures
        db.tables[5][s].len() == 7,
        db.tables[5][s][0] == Val::Int(skey(sv)[s] as int),
        db.tables[5][s][1] == Val::Text(sname(sv, s)),
        db.tables[5][s][3] == Val::Int(snk(sv)[s] as int),
{
    lemma_parts_shape(sv, db);
    sid::lemma_declared_schema();
    let t = db.tables[5];
    let cols = sid::stored_cols_t0();
    let rels = sid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][s] == si::row_at(sv.flat_supplier, s));
    assert(rels[0][s] == proj(t[s], cols));
    assert(row_in_table(t[s], db.schema[5]));
    assert(cols[0] == 0 && cols[1] == 1 && cols[3] == 3);
    assert(proj(t[s], cols)[0] == t[s][0]);
    assert(proj(t[s], cols)[1] == t[s][1]);
    assert(proj(t[s], cols)[3] == t[s][3]);
}

/// Nation row `n`: arity, `n_nationkey`, `n_name`.
pub proof fn lemma_nation_row(sv: StoresView, db: Database, n: int)
    requires bound_db(sv, db), 0 <= n < db.tables[6].len(),
    ensures
        db.tables[6][n].len() == 4,
        db.tables[6][n][0] == Val::Int(nkey(sv)[n] as int),
        db.tables[6][n][1] == Val::Text(nname(sv, n)),
{
    lemma_parts_shape(sv, db);
    nid::lemma_declared_schema();
    let t = db.tables[6];
    let cols = nid::stored_cols_t0();
    let rels = nid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][n] == ni::row_at(sv.flat_nation, n));
    assert(rels[0][n] == proj(t[n], cols));
    assert(row_in_table(t[n], db.schema[6]));
    assert(cols[0] == 0 && cols[1] == 1);
    assert(proj(t[n], cols)[0] == t[n][0]);
    assert(proj(t[n], cols)[1] == t[n][1]);
}

// ------------------------------------------------------------------------------------------------ primary keys

/// The values of a key column are pairwise distinct.
pub open spec fn keys_unique(s: Seq<i64>) -> bool {
    forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && #[trigger] s[a] == #[trigger] s[b] ==> a == b
}

/// A single-column primary key of table `t` makes its stored key column unique, given each row's key value.
proof fn lemma_pk_unique(db: Database, t: int, s: Seq<i64>)
    requires
        constraints_hold(declared_db(db)),
        db.schema == crate::schema::schema_spec(),
        db.tables.len() == 8, 0 <= t < 8,
        crate::gendb_constraints::declared_schema()[t].constraints.len() > 0,
        crate::gendb_constraints::declared_schema()[t].constraints[0]
            == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }),
        s.len() == db.tables[t].len(),
        forall|i: int| 0 <= i < s.len() ==> (#[trigger] db.tables[t][i]).len() > 0 && db.tables[t][i][0] == Val::Int(s[i] as int),
    ensures keys_unique(s),
{
    let ddb = declared_db(db);
    let kcols = seq![0nat];
    crate::gendb_constraints::lemma_declared_schema();
    assert forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && #[trigger] s[a] == #[trigger] s[b] implies a == b by {
        let ka = key_of(db.tables[t][a], kcols);
        let kb = key_of(db.tables[t][b], kcols);
        assert(ka[0] == db.tables[t][a][0]);
        assert(kb[0] == db.tables[t][b][0]);
        assert(crate::spec::equality::val_not_distinct(ka[0], kb[0]));
        assert(crate::spec::equality::row_not_distinct(ka, kb));
        lemma_primary_key_identifies(ddb, t, 0, kcols, true, a, b);
    }
}

/// PRIMARY KEY (o_orderkey), (s_suppkey) and (n_nationkey): the stored key columns of a bound database are unique.
pub proof fn lemma_keys_unique(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures keys_unique(ok(sv)), keys_unique(skey(sv)), keys_unique(nkey(sv)),
{
    lemma_parts_shape(sv, db);
    crate::gendb_constraints::lemma_declared_schema();
    assert forall|j: int| 0 <= j < ok(sv).len() implies (#[trigger] db.tables[1][j]).len() > 0
        && db.tables[1][j][0] == Val::Int(ok(sv)[j] as int) by {
        lemma_orders_row(sv, db, j);
    }
    lemma_pk_unique(db, 1, ok(sv));
    assert forall|s: int| 0 <= s < skey(sv).len() implies (#[trigger] db.tables[5][s]).len() > 0
        && db.tables[5][s][0] == Val::Int(skey(sv)[s] as int) by {
        lemma_supplier_row(sv, db, s);
    }
    lemma_pk_unique(db, 5, skey(sv));
    assert forall|n: int| 0 <= n < nkey(sv).len() implies (#[trigger] db.tables[6][n]).len() > 0
        && db.tables[6][n][0] == Val::Int(nkey(sv)[n] as int) by {
        lemma_nation_row(sv, db, n);
    }
    lemma_pk_unique(db, 6, nkey(sv));
}

/// The facts of the stored parts every bound database shares: their shape and the unique key columns.
pub open spec fn sv_facts(sv: StoresView) -> bool {
    &&& parts_shape(sv)
    &&& cols_shape(sv)
    &&& keys_unique(ok(sv))
    &&& keys_unique(skey(sv))
    &&& keys_unique(nkey(sv))
}

pub proof fn lemma_sv_facts(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures sv_facts(sv),
{
    lemma_parts_shape(sv, db);
    lemma_keys_unique(sv, db);
}

// ------------------------------------------------------------------------------------------------ handles

/// The stored columns Q21 reads, as whole stored parts (`&'static` slices; nothing is copied).
#[derive(Clone, Copy)]
pub struct Cols {
    pub lk: &'static [i64],
    pub ls: &'static [i64],
    pub lc: &'static [i32],
    pub lr: &'static [i32],
    pub nl: usize,
    pub ok: &'static [i64],
    pub soff: &'static [i64],
    pub sb: &'static [u8],
    pub no: usize,
    pub skey: &'static [i64],
    pub snk: &'static [i64],
    pub snoff: &'static [i64],
    pub snb: &'static [u8],
    pub ns: usize,
    pub nkey: &'static [i64],
    pub nnoff: &'static [i64],
    pub nnb: &'static [u8],
    pub nn: usize,
}

/// The handles are the stored columns of `sv`, which has the shared facts.
pub open spec fn cols_ok(c: Cols, sv: StoresView) -> bool {
    &&& sv_facts(sv)
    &&& c.lk@ == lk(sv) && c.ls@ == ls(sv) && c.lc@ == lc(sv) && c.lr@ == lr(sv) && c.nl == n_l(sv)
    &&& c.ok@ == ok(sv) && c.soff@ == ostat_col(sv).offsets && c.sb@ == ostat_col(sv).bytes && c.no == n_o(sv)
    &&& c.skey@ == skey(sv) && c.snk@ == snk(sv) && c.ns == n_s(sv)
    &&& c.snoff@ == sname_col(sv).offsets && c.snb@ == sname_col(sv).bytes
    &&& c.nkey@ == nkey(sv) && c.nn == n_n(sv)
    &&& c.nnoff@ == nname_col(sv).offsets && c.nnb@ == nname_col(sv).bytes
}

/// Reads every column Q21 needs as whole parts.
pub fn read_cols(stores: &mut Stores, Ghost(db): Ghost<Database>) -> (c: Cols)
    requires bound_db(old(stores)@, db),
    ensures final(stores)@ == old(stores)@, cols_ok(c, old(stores)@),
{
    let ghost sv = stores@;
    proof { lemma_sv_facts(sv, db); }
    let l = &mut stores.flat_lineitem;
    let nl = l.part_len(li::L_ORDERKEY);
    let p_lk = l.extent_i64(li::L_ORDERKEY, 0, nl);
    let p_ls = l.extent_i64(li::L_SUPPKEY, 0, nl);
    let p_lc = l.extent_i32(li::L_COMMITDATE, 0, nl);
    let p_lr = l.extent_i32(li::L_RECEIPTDATE, 0, nl);
    let o = &mut stores.flat_orders;
    let no = o.part_len(oi::O_ORDERKEY);
    let p_ok = o.extent_i64(oi::O_ORDERKEY, 0, no);
    let sol = o.part_len(oi::O_ORDERSTATUS_OFFSETS);
    let soff = o.extent_i64(oi::O_ORDERSTATUS_OFFSETS, 0, sol);
    let sbl = o.part_len(oi::O_ORDERSTATUS_BYTES);
    let sb = o.extent_u8(oi::O_ORDERSTATUS_BYTES, 0, sbl);
    let s = &mut stores.flat_supplier;
    let ns = s.part_len(si::S_SUPPKEY);
    let p_skey = s.extent_i64(si::S_SUPPKEY, 0, ns);
    let p_snk = s.extent_i64(si::S_NATIONKEY, 0, ns);
    let snl = s.part_len(si::S_NAME_OFFSETS);
    let snoff = s.extent_i64(si::S_NAME_OFFSETS, 0, snl);
    let snbl = s.part_len(si::S_NAME_BYTES);
    let snb = s.extent_u8(si::S_NAME_BYTES, 0, snbl);
    let n = &mut stores.flat_nation;
    let nn = n.part_len(ni::N_NATIONKEY);
    let p_nkey = n.extent_i64(ni::N_NATIONKEY, 0, nn);
    let nnl = n.part_len(ni::N_NAME_OFFSETS);
    let nnoff = n.extent_i64(ni::N_NAME_OFFSETS, 0, nnl);
    let nnbl = n.part_len(ni::N_NAME_BYTES);
    let nnb = n.extent_u8(ni::N_NAME_BYTES, 0, nnbl);
    let c = Cols { lk: p_lk, ls: p_ls, lc: p_lc, lr: p_lr, nl, ok: p_ok, soff, sb, no, skey: p_skey, snk: p_snk, snoff, snb, ns, nkey: p_nkey, nnoff, nnb, nn };
    proof {
        assert(c.lk@ =~= lk(sv));
        assert(c.ls@ =~= ls(sv));
        assert(c.lc@ =~= lc(sv));
        assert(c.lr@ =~= lr(sv));
        assert(c.ok@ =~= ok(sv));
        assert(c.soff@ =~= ostat_col(sv).offsets);
        assert(c.sb@ =~= ostat_col(sv).bytes);
        assert(c.skey@ =~= skey(sv));
        assert(c.snk@ =~= snk(sv));
        assert(c.snoff@ =~= sname_col(sv).offsets);
        assert(c.snb@ =~= sname_col(sv).bytes);
        assert(c.nkey@ =~= nkey(sv));
        assert(c.nnoff@ =~= nname_col(sv).offsets);
        assert(c.nnb@ =~= nname_col(sv).bytes);
    }
    c
}

} // verus!
