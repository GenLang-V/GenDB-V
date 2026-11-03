//! Storage `suppliers` (partsupp, supplier, nation) at the level of its parts: the values the statement reads
//! (`psk`/`pss`/`psa`, `suk`/`sun`/`sua`/`sunk`, `nak`/`nan`), what the code needs to read them (`sp_ok`: frames,
//! column shapes, value bounds, sorted partsupp keys when the key index kind is 1, distinct supplier keys), and
//! `lemma_bind_sp`: for a database whose stored relations the parts represent, these are its rows' values.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::part_len;
use crate::link::query::proj_all;
use crate::link::source::lemma_proj_all_index;
use crate::link::expr::{ival, tval};
use crate::stores::suppliers::interface as si;
use crate::stores::suppliers::interface::common::colfmt as cf;
use crate::stores::suppliers::declaration as sd;
use crate::stores::suppliers_psrun::interface as pr;
use crate::stores::suppliers_psrun::declaration as prd;
use super::typed::*;
use super::nf::{pst, st, nt};

verus! {

/// The values of a U16 part (empty for another kind).
pub open spec fn u16s(p: PartView) -> Seq<u16> {
    match p {
        PartView::U16(s) => s,
        _ => Seq::empty(),
    }
}

/// Rows of the table whose frame starts at part `t`.
pub open spec fn tn(sp: Seq<PartView>, t: int) -> int {
    cf::u64s(sp[t])[0] as int
}

/// Rows per block of that table.
pub open spec fn tbs(sp: Seq<PartView>, t: int) -> int {
    cf::u64s(sp[t])[1] as int
}

/// Value of row `j` of the FOR column with codes `t + cp` and bases `t + bp`.
pub open spec fn fv(sp: Seq<PartView>, t: int, cp: int, bp: int, j: int) -> int {
    cf::base_at(sp[t + bp], j / tbs(sp, t)) + cf::code_at(sp[t + cp], j)
}

/// Text value `j` of the column with offsets `t + op` and bytes `t + yp`.
pub open spec fn tx(sp: Seq<PartView>, t: int, op: int, yp: int, j: int) -> Seq<u8> {
    cf::text_of(cf::u64s(sp[t + op]), cf::u8s(sp[t + yp]), j)
}

/// A table frame: `[rows, block rows]` with blocks of at least one row.
pub open spec fn frame(sp: Seq<PartView>, t: int) -> bool {
    &&& sp[t] is U64
    &&& cf::u64s(sp[t]).len() == 2
    &&& tbs(sp, t) >= 1
}

/// A FOR column the code can read: I64 bases covering every block, one code per row.
pub open spec fn fcol(sp: Seq<PartView>, t: int, cp: int, bp: int) -> bool {
    &&& sp[t + bp] is I64
    &&& part_len(sp[t + cp]) == tn(sp, t)
    &&& cf::i64s(sp[t + bp]).len() * tbs(sp, t) >= tn(sp, t)
}

/// A text column the code can read.
pub open spec fn tcol(sp: Seq<PartView>, t: int, op: int, yp: int) -> bool {
    &&& sp[t + op] is U64
    &&& sp[t + yp] is U8
    &&& cf::text_parts_wf(cf::u64s(sp[t + op]), cf::u8s(sp[t + yp]), tn(sp, t))
}

pub open spec fn psk(sp: Seq<PartView>, j: int) -> int { fv(sp, 0, 2, 3, j) }
pub open spec fn pss(sp: Seq<PartView>, j: int) -> int { fv(sp, 0, 4, 5, j) }
pub open spec fn psa(sp: Seq<PartView>, j: int) -> int { fv(sp, 0, 6, 7, j) }
pub open spec fn ps_kind(sp: Seq<PartView>) -> u64 { cf::u64s(sp[12])[0] }
pub open spec fn su_kind(sp: Seq<PartView>) -> u64 { cf::u64s(sp[29])[0] }
pub open spec fn suk(sp: Seq<PartView>, x: int) -> int { fv(sp, 13, 2, 3, x) }
pub open spec fn sun(sp: Seq<PartView>, x: int) -> Seq<u8> { tx(sp, 13, 4, 5, x) }
pub open spec fn sua(sp: Seq<PartView>, x: int) -> Seq<u8> { tx(sp, 13, 6, 7, x) }
pub open spec fn sunk(sp: Seq<PartView>, x: int) -> int { fv(sp, 13, 8, 9, x) }
pub open spec fn nak(sp: Seq<PartView>, y: int) -> int { fv(sp, 30, 2, 3, y) }
pub open spec fn nan(sp: Seq<PartView>, y: int) -> Seq<u8> { tx(sp, 30, 4, 5, y) }

/// A bigint.
pub open spec fn i64r(v: int) -> bool {
    i64::MIN <= v <= i64::MAX
}

/// Partsupp keys do not decrease from row `j` to `j + 1`.
pub open spec fn ps_le(sp: Seq<PartView>, j: int) -> bool {
    psk(sp, j) <= psk(sp, j + 1)
}

/// Supplier keys do not decrease from row `x` to `x + 1`.
pub open spec fn su_le(sp: Seq<PartView>, x: int) -> bool {
    suk(sp, x) <= suk(sp, x + 1)
}

/// Partsupp at the parts' level.
pub open spec fn ps_ok(sp: Seq<PartView>) -> bool {
    &&& frame(sp, 0)
    &&& sp[2] is U32 && fcol(sp, 0, 2, 3)
    &&& sp[4] is U32 && fcol(sp, 0, 4, 5)
    &&& sp[6] is U16 && fcol(sp, 0, 6, 7)
    &&& sp[12] is U64 && cf::u64s(sp[12]).len() == 1
    &&& forall|j: int| 0 <= j < tn(sp, 0) ==> i64r(#[trigger] psk(sp, j)) && i64r(pss(sp, j)) && i64r(psa(sp, j))
    &&& ps_kind(sp) == 1 ==> forall|j: int| 0 <= j < tn(sp, 0) - 1 ==> #[trigger] ps_le(sp, j)
}

/// Supplier at the parts' level.
pub open spec fn su_ok(sp: Seq<PartView>) -> bool {
    &&& frame(sp, 13)
    &&& sp[15] is U32 && fcol(sp, 13, 2, 3)
    &&& tcol(sp, 13, 4, 5)
    &&& tcol(sp, 13, 6, 7)
    &&& sp[21] is U8 && fcol(sp, 13, 8, 9)
    &&& forall|x: int| 0 <= x < tn(sp, 13) ==> i64r(#[trigger] suk(sp, x)) && i64r(sunk(sp, x))
    &&& forall|a: int, b: int| 0 <= a < tn(sp, 13) && 0 <= b < tn(sp, 13) && a != b ==> #[trigger] suk(sp, a) != #[trigger] suk(sp, b)
    &&& sp[29] is U64 && cf::u64s(sp[29]).len() == 1
    &&& su_kind(sp) == 1 ==> forall|x: int| 0 <= x < tn(sp, 13) - 1 ==> #[trigger] su_le(sp, x)
}

/// Nation at the parts' level.
pub open spec fn na_ok(sp: Seq<PartView>) -> bool {
    &&& frame(sp, 30)
    &&& sp[32] is U8 && fcol(sp, 30, 2, 3)
    &&& tcol(sp, 30, 4, 5)
    &&& forall|y: int| 0 <= y < tn(sp, 30) ==> i64r(#[trigger] nak(sp, y))
}

pub open spec fn sp_ok(sp: Seq<PartView>) -> bool {
    &&& sp.len() == si::SUPPLIERS_PARTS
    &&& ps_ok(sp)
    &&& su_ok(sp)
    &&& na_ok(sp)
}

/// The partsupp rows of `db` hold the parts' values.
pub open spec fn ps_bound(sp: Seq<PartView>, db: Database) -> bool {
    &&& pst(db).len() == tn(sp, 0)
    &&& forall|j: int| 0 <= j < pst(db).len() ==> #[trigger] pst(db)[j][0] == Val::Int(psk(sp, j))
        && pst(db)[j][1] == Val::Int(pss(sp, j)) && pst(db)[j][2] == Val::Int(psa(sp, j))
}

/// The supplier rows of `db` hold the parts' values.
pub open spec fn su_bound(sp: Seq<PartView>, db: Database) -> bool {
    &&& st(db).len() == tn(sp, 13)
    &&& forall|x: int| 0 <= x < st(db).len() ==> #[trigger] st(db)[x][0] == Val::Int(suk(sp, x))
        && st(db)[x][1] == Val::Text(sun(sp, x)) && st(db)[x][2] == Val::Text(sua(sp, x))
        && st(db)[x][3] == Val::Int(sunk(sp, x))
}

/// The nation rows of `db` hold the parts' values.
pub open spec fn na_bound(sp: Seq<PartView>, db: Database) -> bool {
    &&& nt(db).len() == tn(sp, 30)
    &&& forall|y: int| 0 <= y < nt(db).len() ==> #[trigger] nt(db)[y][0] == Val::Int(nak(sp, y))
        && nt(db)[y][1] == Val::Text(nan(sp, y))
}

/// One FOR column of the table at `t` (`k` parts): its values and its shape.
proof fn lemma_for_col(sp: Seq<PartView>, t: int, k: int, cp: int, bp: int, rel: Seq<Row>, c: int)
    requires
        0 <= t, t + k <= sp.len(), 2 <= cp < k, 2 <= bp < k,
        si::table_layout_ok(sp.subrange(t, t + k), rel.len() as int),
        cf::int_col_at(sp.subrange(t, t + k), 1, cp, bp, rel, c),
    ensures
        frame(sp, t),
        tn(sp, t) == rel.len(),
        fcol(sp, t, cp, bp),
        forall|j: int| 0 <= j < rel.len() ==> #[trigger] rel[j][c] == Val::Int(fv(sp, t, cp, bp, j)),
{
    let tp = sp.subrange(t, t + k);
    let n = rel.len() as int;
    assert(tp[0] == sp[t] && tp[1] == sp[t + 1] && tp[cp] == sp[t + cp] && tp[bp] == sp[t + bp]);
    let bs = tbs(sp, t);
    let gp = tp[1];
    cf::lemma_uniform_groups(gp, n, bs);
    cf::lemma_nblocks(n, bs);
    assert(cf::i64s(sp[t + bp]).len() == cf::nblocks_of(n, bs));
    assert forall|j: int| 0 <= j < rel.len() implies #[trigger] rel[j][c] == Val::Int(fv(sp, t, cp, bp, j)) by {
        crate::stores::suppliers::interface::common::read::lemma_for_row(gp, n, bs, tp[bp], tp[cp], j);
    }
}

/// One text column of the table at `t`.
proof fn lemma_text_col(sp: Seq<PartView>, t: int, k: int, op: int, yp: int, rel: Seq<Row>, c: int)
    requires
        0 <= t, t + k <= sp.len(), 2 <= op < k, 2 <= yp < k,
        si::table_layout_ok(sp.subrange(t, t + k), rel.len() as int),
        cf::text_col_at(sp.subrange(t, t + k), op, yp, rel, c),
    ensures
        tcol(sp, t, op, yp),
        forall|j: int| 0 <= j < rel.len() ==> #[trigger] rel[j][c] == Val::Text(tx(sp, t, op, yp, j)),
{
    let tp = sp.subrange(t, t + k);
    assert(tp[0] == sp[t] && tp[op] == sp[t + op] && tp[yp] == sp[t + yp]);
}

/// The parts of a database's stored relations: its partsupp, supplier and nation rows and `sp_ok`.
pub proof fn lemma_bind_sp(sp: Seq<PartView>, db: Database)
    requires
        si::represents(sp, sd::stored_relations(db)),
        tables_ok(db),
    ensures
        sp_ok(sp),
        ps_bound(sp, db),
        su_bound(sp, db),
        na_bound(sp, db),
{
    let rels = sd::stored_relations(db);
    // partsupp
    let r0 = rels[0];
    let c0 = sd::stored_cols_t0();
    assert(r0 == proj_all(pst(db), c0));
    lemma_proj_all_index(pst(db), c0);
    let tp0 = sp.subrange(0, 13);
    assert(si::partsupp_ok(tp0, r0));
    lemma_for_col(sp, 0, 13, 2, 3, r0, 0);
    lemma_for_col(sp, 0, 13, 4, 5, r0, 1);
    lemma_for_col(sp, 0, 13, 6, 7, r0, 2);
    assert(tp0[2] == sp[2] && tp0[4] == sp[4] && tp0[6] == sp[6] && tp0[12] == sp[12] && tp0[0] == sp[0] && tp0[3] == sp[3]);
    assert forall|j: int| 0 <= j < pst(db).len() implies #[trigger] pst(db)[j][0] == Val::Int(psk(sp, j))
        && pst(db)[j][1] == Val::Int(pss(sp, j)) && pst(db)[j][2] == Val::Int(psa(sp, j)) by {
        assert(r0[j][0] == pst(db)[j][c0[0] as int]);
        assert(r0[j][1] == pst(db)[j][c0[1] as int]);
        assert(r0[j][2] == pst(db)[j][c0[2] as int]);
    }
    assert forall|j: int| 0 <= j < tn(sp, 0) implies i64r(#[trigger] psk(sp, j)) && i64r(pss(sp, j)) && i64r(psa(sp, j)) by {
        assert(psrow_ok(pst(db)[j]));
        assert(pst(db)[j][0] == Val::Int(psk(sp, j)));
    }
    if ps_kind(sp) == 1 {
        let bs = tbs(sp, 0);
        let n = tn(sp, 0);
        let kc = cf::u32s(sp[2]);
        let kb = cf::i64s(sp[3]);
        assert(crate::stores::suppliers::interface::common::keyidx::keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), bs, 1, n));
        assert forall|j: int| 0 <= j < tn(sp, 0) - 1 implies #[trigger] ps_le(sp, j) by {
            assert(crate::stores::suppliers::interface::common::keyidx::sorted_at(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), bs, 1, j));
        }
    }
    // supplier
    let r1 = rels[1];
    let c1 = sd::stored_cols_t1();
    assert(r1 == proj_all(st(db), c1));
    lemma_proj_all_index(st(db), c1);
    let tp1 = sp.subrange(13, 30);
    assert(si::supplier_ok(tp1, r1));
    lemma_for_col(sp, 13, 17, 2, 3, r1, 0);
    lemma_text_col(sp, 13, 17, 4, 5, r1, 1);
    lemma_text_col(sp, 13, 17, 6, 7, r1, 2);
    lemma_for_col(sp, 13, 17, 8, 9, r1, 3);
    assert(tp1[2] == sp[15] && tp1[8] == sp[21]);
    assert forall|x: int| 0 <= x < st(db).len() implies #[trigger] st(db)[x][0] == Val::Int(suk(sp, x))
        && st(db)[x][1] == Val::Text(sun(sp, x)) && st(db)[x][2] == Val::Text(sua(sp, x))
        && st(db)[x][3] == Val::Int(sunk(sp, x)) by {
        assert(r1[x][0] == st(db)[x][c1[0] as int]);
        assert(r1[x][1] == st(db)[x][c1[1] as int]);
        assert(r1[x][2] == st(db)[x][c1[2] as int]);
        assert(r1[x][3] == st(db)[x][c1[3] as int]);
    }
    assert forall|x: int| 0 <= x < tn(sp, 13) implies i64r(#[trigger] suk(sp, x)) && i64r(sunk(sp, x)) by {
        assert(srow_ok(st(db)[x]));
        assert(st(db)[x][0] == Val::Int(suk(sp, x)));
    }
    assert forall|a: int, b: int| 0 <= a < tn(sp, 13) && 0 <= b < tn(sp, 13) && a != b
        implies #[trigger] suk(sp, a) != #[trigger] suk(sp, b) by {
        assert(st(db)[a][0] != st(db)[b][0]);
        assert(st(db)[a][0] == Val::Int(suk(sp, a)));
        assert(st(db)[b][0] == Val::Int(suk(sp, b)));
    }
    assert(tp1[16] == sp[29]);
    if su_kind(sp) == 1 {
        let bs = tbs(sp, 13);
        let n = tn(sp, 13);
        let kc = cf::u32s(sp[15]);
        let kb = cf::i64s(sp[16]);
        assert(tp1[2] == sp[15] && tp1[3] == sp[16] && tp1[0] == sp[13]);
        assert(crate::stores::suppliers::interface::common::keyidx::keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), bs, 1, n));
        assert forall|x: int| 0 <= x < tn(sp, 13) - 1 implies #[trigger] su_le(sp, x) by {
            assert(crate::stores::suppliers::interface::common::keyidx::sorted_at(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), bs, 1, x));
        }
    }
    // nation
    let r2 = rels[2];
    let c2 = sd::stored_cols_t2();
    assert(r2 == proj_all(nt(db), c2));
    lemma_proj_all_index(nt(db), c2);
    let tp2 = sp.subrange(30, 40);
    assert(si::nation_ok(tp2, r2));
    lemma_for_col(sp, 30, 10, 2, 3, r2, 0);
    lemma_text_col(sp, 30, 10, 4, 5, r2, 1);
    assert(tp2[2] == sp[32]);
    assert forall|y: int| 0 <= y < nt(db).len() implies #[trigger] nt(db)[y][0] == Val::Int(nak(sp, y))
        && nt(db)[y][1] == Val::Text(nan(sp, y)) by {
        assert(r2[y][0] == nt(db)[y][c2[0] as int]);
        assert(r2[y][1] == nt(db)[y][c2[1] as int]);
    }
    assert forall|y: int| 0 <= y < tn(sp, 30) implies i64r(#[trigger] nak(sp, y)) by {
        assert(nrow_ok(nt(db)[y]));
        assert(nt(db)[y][0] == Val::Int(nak(sp, y)));
    }
}

/// The run layout `[ratio, first]` of storage suppliers_psrun.
pub open spec fn run_of(rp: Seq<PartView>) -> Seq<i64> {
    pr::run_i64s(rp[pr::RUN as int])
}

/// The run layout holds for the partsupp keys of `sp`: with `ratio >= 1`, row `j` has key `first + j / ratio`.
pub open spec fn run_holds(sp: Seq<PartView>, rp: Seq<PartView>) -> bool {
    &&& rp.len() == pr::PSRUN_PARTS
    &&& rp[pr::RUN as int] is I64
    &&& run_of(rp).len() == 2
    &&& run_of(rp)[0] >= 1 ==> forall|j: int| 0 <= j < tn(sp, 0)
        ==> #[trigger] psk(sp, j) == run_of(rp)[1] + j / (run_of(rp)[0] as int)
}

/// Both storages hold the same partsupp rows: the run layout of suppliers_psrun describes suppliers' keys.
pub proof fn lemma_bind_run(sp: Seq<PartView>, rp: Seq<PartView>, db: Database)
    requires
        pr::represents(rp, prd::stored_relations(db)),
        ps_bound(sp, db),
    ensures run_holds(sp, rp),
{
    let rels = prd::stored_relations(db);
    let r0 = rels[0];
    let c0 = prd::stored_cols_t0();
    assert(r0 == proj_all(pst(db), c0));
    lemma_proj_all_index(pst(db), c0);
    let run = run_of(rp);
    if run[0] >= 1 {
        assert forall|j: int| 0 <= j < tn(sp, 0) implies #[trigger] psk(sp, j) == run[1] + j / (run[0] as int) by {
            assert(r0[j][0] == pst(db)[j][c0[0] as int]);
            assert(c0[0] == 0);
            assert(r0[j][0] == Val::Int(run[1] + j / (run[0] as int)));
            assert(pst(db)[j][0] == Val::Int(psk(sp, j)));
        }
    }
}

} // verus!
