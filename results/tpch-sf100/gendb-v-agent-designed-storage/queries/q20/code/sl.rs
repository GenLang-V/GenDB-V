//! The statement's normal form over the storage uses' parts (`sl_*`, mirroring `nf`), and `lemma_sl_outcome`: for
//! every database bound to the parts, `nf::nf_outcome` is `sl_outcome`. The code computes `sl_outcome`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::link::join::*;
use crate::link::expr::{ival, tval};
use crate::stores::part_nameidx::interface as pi;
use crate::stores::li_pkdate::interface as li;
use super::typed::*;
use super::nf::*;
use super::bind_sp::*;
use super::bind_pl::*;

verus! {

/// Some part row of key `k` matches.
pub open spec fn sl_part_hit(pp: Seq<PartView>, pat: Seq<u8>, k: int) -> bool {
    exists|r: int| 0 <= r < pi::n_rows(pp) && pi::pkey_at(pp, r) == k && #[trigger] like_hit(pi::name_at(pp, r), pat)
}

/// Some part name makes the LIKE fail.
pub open spec fn sl_part_err(pp: Seq<PartView>, pat: Seq<u8>) -> bool {
    exists|r: int| 0 <= r < pi::n_rows(pp) && #[trigger] like_of(pi::name_at(pp, r), pat) is Err
}

/// Partsupp row `j` passes the subquery's WHERE.
pub open spec fn sl_ps_qual(sv: StoresView, pat: Seq<u8>, d0: int, d1: int, j: int) -> bool {
    let (k, su) = (psk(sv.suppliers, j), pss(sv.suppliers, j));
    &&& sl_part_hit(sv.part_nameidx, pat, k)
    &&& sl_lcnt(sv.li_pkdate, k, su, d0, d1) > 0
    &&& 200 * psa(sv.suppliers, j) > sl_lsum(sv.li_pkdate, k, su, d0, d1)
}

/// Some qualifying partsupp row has supplier `s`.
pub open spec fn sl_sk_ok(sv: StoresView, pat: Seq<u8>, d0: int, d1: int, s: int) -> bool {
    exists|j: int| 0 <= j < tn(sv.suppliers, 0) && #[trigger] sl_ps_qual(sv, pat, d0, d1, j) && pss(sv.suppliers, j) == s
}

/// Some nation row of key `kn` is named `name`.
pub open spec fn sl_nat_ok(sp: Seq<PartView>, name: Seq<u8>, kn: int) -> bool {
    exists|y: int| 0 <= y < tn(sp, 30) && #[trigger] nak(sp, y) == kn && nan(sp, y) == name
}

/// Supplier row `x` is in the result.
pub open spec fn sl_s_qual(sv: StoresView, ps: Seq<Literal>, d1: int, x: int) -> bool {
    &&& sl_sk_ok(sv, pat_of(ps), d0_of(ps), d1, suk(sv.suppliers, x))
    &&& sl_nat_ok(sv.suppliers, nname_of(ps), sunk(sv.suppliers, x))
}

/// The output row of supplier row `x`.
pub open spec fn orow(sp: Seq<PartView>, x: int) -> Row {
    seq![Val::Text(sun(sp, x)), Val::Text(sua(sp, x))]
}

/// The result rows of the first `m` supplier rows, in order.
pub open spec fn sel_rows(sv: StoresView, ps: Seq<Literal>, d1: int, m: int) -> Seq<Row>
    decreases m,
{
    if m <= 0 {
        Seq::empty()
    } else if sl_s_qual(sv, ps, d1, m - 1) {
        sel_rows(sv, ps, d1, m - 1).push(orow(sv.suppliers, m - 1))
    } else {
        sel_rows(sv, ps, d1, m - 1)
    }
}

/// The statement's body over the parts.
pub open spec fn sl_outcome(sv: StoresView, ps: Seq<Literal>, d1: int) -> Result<Seq<Row>, SqlError> {
    let sp = sv.suppliers;
    if tn(sp, 13) > 0 && tn(sp, 30) > 0 && tn(sp, 0) > 0 && sl_part_err(sv.part_nameidx, pat_of(ps)) {
        Err(SqlError::InvalidEscapeSequence)
    } else {
        Ok(sel_rows(sv, ps, d1, tn(sp, 13)))
    }
}

/// What the code needs of the parts.
pub open spec fn sl_ok(sv: StoresView) -> bool {
    &&& pp_ok(sv.part_nameidx)
    &&& lp_ok(sv.li_pkdate)
    &&& sp_ok(sv.suppliers)
    &&& run_holds(sv.suppliers, sv.suppliers_psrun)
}

/// A database bound to the parts: its rows' values are the parts' values.
pub open spec fn all_bound(sv: StoresView, db: Database) -> bool {
    &&& tables_ok(db)
    &&& pa_bound(sv.part_nameidx, db)
    &&& li_bound(sv.li_pkdate, db)
    &&& ps_bound(sv.suppliers, db)
    &&& su_bound(sv.suppliers, db)
    &&& na_bound(sv.suppliers, db)
}

pub proof fn lemma_bound(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures sl_ok(sv), all_bound(sv, db),
{
    lemma_tables_ok(db);
    lemma_bind_pp(sv.part_nameidx, db);
    lemma_bind_lp(sv.li_pkdate, db);
    lemma_bind_sp(sv.suppliers, db);
    lemma_bind_run(sv.suppliers, sv.suppliers_psrun, db);
}

proof fn lemma_part_hit_eq(sv: StoresView, db: Database, pat: Seq<u8>, k: int)
    requires all_bound(sv, db),
    ensures part_hit(db, pat, k) == sl_part_hit(sv.part_nameidx, pat, k),
{
    let pp = sv.part_nameidx;
    if part_hit(db, pat, k) {
        let i = choose|i: int| 0 <= i < pt(db).len() && pt(db)[i][0] == Val::Int(k) && #[trigger] like_hit(tval(pt(db)[i][1]), pat);
        assert(pt(db)[i][0] == Val::Int(pi::pkey_at(pp, i)));
        assert(like_hit(pi::name_at(pp, i), pat));
    }
    if sl_part_hit(pp, pat, k) {
        let r = choose|r: int| 0 <= r < pi::n_rows(pp) && pi::pkey_at(pp, r) == k && #[trigger] like_hit(pi::name_at(pp, r), pat);
        assert(pt(db)[r][0] == Val::Int(pi::pkey_at(pp, r)));
        assert(like_hit(tval(pt(db)[r][1]), pat));
    }
}

proof fn lemma_part_err_eq(sv: StoresView, db: Database, pat: Seq<u8>)
    requires all_bound(sv, db),
    ensures part_err(db, pat) == sl_part_err(sv.part_nameidx, pat),
{
    let pp = sv.part_nameidx;
    if part_err(db, pat) {
        let i = choose|i: int| 0 <= i < pt(db).len() && #[trigger] like_of(tval(pt(db)[i][1]), pat) is Err;
        assert(pt(db)[i][1] == Val::Text(pi::name_at(pp, i)));
        assert(like_of(pi::name_at(pp, i), pat) is Err);
    }
    if sl_part_err(pp, pat) {
        let r = choose|r: int| 0 <= r < pi::n_rows(pp) && #[trigger] like_of(pi::name_at(pp, r), pat) is Err;
        assert(pt(db)[r][1] == Val::Text(pi::name_at(pp, r)));
        assert(like_of(tval(pt(db)[r][1]), pat) is Err);
    }
}

proof fn lemma_ps_qual_eq(sv: StoresView, db: Database, pat: Seq<u8>, d0: int, d1: int, j: int)
    requires all_bound(sv, db), 0 <= j < pst(db).len(),
    ensures ps_qual(db, pat, d0, d1, pst(db)[j]) == sl_ps_qual(sv, pat, d0, d1, j),
{
    let sp = sv.suppliers;
    let r = pst(db)[j];
    assert(r[0] == Val::Int(psk(sp, j)) && r[1] == Val::Int(pss(sp, j)) && r[2] == Val::Int(psa(sp, j)));
    lemma_part_hit_eq(sv, db, pat, psk(sp, j));
    assert(lsum(db, psk(sp, j), pss(sp, j), d0, d1) == sl_lsum(sv.li_pkdate, psk(sp, j), pss(sp, j), d0, d1));
}

proof fn lemma_sk_ok_eq(sv: StoresView, db: Database, pat: Seq<u8>, d0: int, d1: int, s: int)
    requires all_bound(sv, db),
    ensures sk_ok(db, pat, d0, d1, s) == sl_sk_ok(sv, pat, d0, d1, s),
{
    let sp = sv.suppliers;
    if sk_ok(db, pat, d0, d1, s) {
        let i = choose|i: int| 0 <= i < pst(db).len() && #[trigger] ps_qual(db, pat, d0, d1, pst(db)[i]) && pst(db)[i][1] == Val::Int(s);
        lemma_ps_qual_eq(sv, db, pat, d0, d1, i);
        assert(pst(db)[i][1] == Val::Int(pss(sp, i)));
        assert(sl_ps_qual(sv, pat, d0, d1, i));
    }
    if sl_sk_ok(sv, pat, d0, d1, s) {
        let j = choose|j: int| 0 <= j < tn(sp, 0) && #[trigger] sl_ps_qual(sv, pat, d0, d1, j) && pss(sp, j) == s;
        lemma_ps_qual_eq(sv, db, pat, d0, d1, j);
        assert(pst(db)[j][1] == Val::Int(pss(sp, j)));
        assert(ps_qual(db, pat, d0, d1, pst(db)[j]));
    }
}

proof fn lemma_nat_ok_eq(sv: StoresView, db: Database, name: Seq<u8>, kn: int)
    requires all_bound(sv, db),
    ensures nat_ok(db, name, kn) == sl_nat_ok(sv.suppliers, name, kn),
{
    let sp = sv.suppliers;
    if nat_ok(db, name, kn) {
        let y = choose|y: int| 0 <= y < nt(db).len() && #[trigger] nt(db)[y][0] == Val::Int(kn) && nt(db)[y][1] == Val::Text(name);
        assert(nt(db)[y][0] == Val::Int(nak(sp, y)));
        assert(nak(sp, y) == kn);
    }
    if sl_nat_ok(sp, name, kn) {
        let y = choose|y: int| 0 <= y < tn(sp, 30) && #[trigger] nak(sp, y) == kn && nan(sp, y) == name;
        assert(nt(db)[y][0] == Val::Int(nak(sp, y)));
    }
}

/// Supplier row `x` qualifies in `db` exactly when it does over the parts.
pub proof fn lemma_s_qual_eq(sv: StoresView, db: Database, ps: Seq<Literal>, d1: int, x: int)
    requires all_bound(sv, db), 0 <= x < st(db).len(),
    ensures s_qual(db, ps, d1, st(db)[x]) == sl_s_qual(sv, ps, d1, x),
{
    let sp = sv.suppliers;
    assert(st(db)[x][0] == Val::Int(suk(sp, x)) && st(db)[x][3] == Val::Int(sunk(sp, x)));
    lemma_sk_ok_eq(sv, db, pat_of(ps), d0_of(ps), d1, suk(sp, x));
    lemma_nat_ok_eq(sv, db, nname_of(ps), sunk(sp, x));
}

/// The result rows of the first `m` supplier rows.
proof fn lemma_sel_rows(sv: StoresView, db: Database, ps: Seq<Literal>, d1: int, m: int)
    requires all_bound(sv, db), 0 <= m <= st(db).len(),
    ensures keep(st(db).take(m), s_qual_f(db, ps, d1)).map_values(|r: Row| out_row(r)) == sel_rows(sv, ps, d1, m),
    decreases m,
{
    let f = s_qual_f(db, ps, d1);
    let t = st(db).take(m);
    if m == 0 {
        assert(t =~= Seq::<Row>::empty());
        assert(keep(t, f).map_values(|r: Row| out_row(r)) =~= Seq::<Row>::empty());
    } else {
        lemma_sel_rows(sv, db, ps, d1, m - 1);
        assert(t.drop_last() =~= st(db).take(m - 1));
        assert(t.last() == st(db)[m - 1]);
        lemma_s_qual_eq(sv, db, ps, d1, m - 1);
        let ki = keep(st(db).take(m - 1), f);
        if f(t.last()) {
            assert(keep(t, f) == ki.push(t.last()));
            assert(out_row(st(db)[m - 1]) =~= orow(sv.suppliers, m - 1));
            assert(ki.push(t.last()).map_values(|r: Row| out_row(r)) =~= ki.map_values(|r: Row| out_row(r)).push(out_row(t.last())));
        } else {
            assert(keep(t, f) == ki);
        }
    }
}

/// For a database bound to the parts, the normal form's outcome is the parts' outcome.
pub proof fn lemma_sl_outcome(sv: StoresView, db: Database, ps: Seq<Literal>, d1: int)
    requires all_bound(sv, db),
    ensures nf_outcome(db, ps, d1) == sl_outcome(sv, ps, d1),
{
    lemma_part_err_eq(sv, db, pat_of(ps));
    lemma_sel_rows(sv, db, ps, d1, st(db).len() as int);
    assert(st(db).take(st(db).len() as int) =~= st(db));
}

} // verus!
