//! The executable column views (`NumCols`, `SubCols`, `KeyCols`) and the relations of a bound database: the rows'
//! columns the query reads are the views' values (`rows_view`); the per-sub totals of the normal form (`tsum`,
//! `tcnt`) are the scan's `rsum`/`rcnt`; sums over sub rows with a key are sums over the ranks (`rk_sum`) and, with
//! the scan's totals, the grouping's `psum` and `tsum`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::link::query::{text_wf, text_at, TextView};
use crate::link::join::sum_of;
use crate::gendb_entry::stores::StoresView;
use crate::stores::flat_sub::interface as si;
use crate::stores::flat_num::interface as ni;
use crate::agent::common::wide::*;
use crate::agent::scan::{NumCols, rsum, rcnt, lemma_rcnt_nonneg};
use crate::agent::keys::{SubCols, rank_key, lemma_qlist, lemma_qlist_prefix};
use crate::agent::groups::{KeyCols, psum};
use crate::agent::groups;
use crate::agent::run::totals_ok;
use crate::agent::nf::rows::*;
use crate::agent::nf::fromwhere::*;
use crate::agent::nf::group::coeff;
use crate::agent::nf::sums::*;

verus! {

/// The views read the stored parts.
pub open spec fn cols_of(sv: StoresView, num: &NumCols, sub: &SubCols, kc: &KeyCols) -> bool {
    let (sp, np) = (sv.flat_sub, sv.flat_num);
    &&& num.uom_text() == ni::text_view(np, ni::UOM_OFFSETS as int, ni::UOM_BYTES as int)
    &&& num.adsh_text() == ni::text_view(np, ni::ADSH_OFFSETS as int, ni::ADSH_BYTES as int)
    &&& num.value@ == ni::i128s(np[ni::VALUE as int])
    &&& sub.text() == si::text_view(sp, si::ADSH_OFFSETS as int, si::ADSH_BYTES as int)
    &&& sub.fy@ == si::i32s(sp[si::FY as int])
    &&& sub.fy_valid@ == si::u8s(sp[si::FY_VALIDITY as int])
    &&& kc.text() == si::text_view(sp, si::NAME_OFFSETS as int, si::NAME_BYTES as int)
    &&& kc.cik@ == si::i32s(sp[si::CIK as int])
    &&& kc.n == sub.n
}

/// The columns of the two relations the query reads, in terms of the views.
pub open spec fn rows_view(db: Database, num: &NumCols, sub: &SubCols, kc: &KeyCols, p1: int) -> bool {
    &&& db.tables.len() == 4
    &&& db.tables[1].len() == num.n
    &&& db.tables[0].len() == sub.n
    &&& kc.n == sub.n
    &&& forall|i: int| 0 <= i < num.n ==> {
        &&& (#[trigger] db.tables[1][i])[0] == Val::Text(num.adsh(i))
        &&& db.tables[1][i][5] == Val::Text(num.uom(i))
        &&& db.tables[1][i][7] == (Val::Num { coeff: num.val(i), scale: 4 })
    }
    &&& forall|j: int| 0 <= j < sub.n ==> {
        &&& (#[trigger] db.tables[0][j])[0] == Val::Text(sub.key(j))
        &&& db.tables[0][j][1] == Val::Int(kc.cik(j))
        &&& db.tables[0][j][2] == Val::Text(kc.name(j))
        &&& fyok(p1, db.tables[0][j]) == sub.qual(j)
    }
}

pub proof fn lemma_rows_view(sv: StoresView, db: Database, num: &NumCols, sub: &SubCols, kc: &KeyCols, p1: int)
    requires
        tables_are(sv, db), cols_of(sv, num, sub, kc),
        db.tables[1].len() == num.n, db.tables[0].len() == sub.n, sub.p1 as int == p1,
    ensures rows_view(db, num, sub, kc, p1),
{
    let (sp, np) = (sv.flat_sub, sv.flat_num);
    assert forall|i: int| 0 <= i < num.n implies {
        &&& (#[trigger] db.tables[1][i])[0] == Val::Text(num.adsh(i))
        &&& db.tables[1][i][5] == Val::Text(num.uom(i))
        &&& db.tables[1][i][7] == (Val::Num { coeff: num.val(i), scale: 4 })
    } by {
        assert(db.tables[1][i] == ni::row_at(np, i));
    }
    assert forall|j: int| 0 <= j < sub.n implies {
        &&& (#[trigger] db.tables[0][j])[0] == Val::Text(sub.key(j))
        &&& db.tables[0][j][1] == Val::Int(kc.cik(j))
        &&& db.tables[0][j][2] == Val::Text(kc.name(j))
        &&& fyok(p1, db.tables[0][j]) == sub.qual(j)
    } by {
        assert(db.tables[0][j] == si::row_at(sp, j));
        assert(db.tables[0][j][10] == si::fy_value(sp, j));
    }
}

// ------------------------------------------------------------------------------------------- per-sub totals

/// The totals of the num rows `0..m` for sub row `y` (adsh `key`).
proof fn lemma_tsum_prefix(db: Database, num: &NumCols, sub: &SubCols, kc: &KeyCols, p1: int, p0: Seq<u8>, y: Row,
    key: Seq<u8>, m: int)
    requires rows_view(db, num, sub, kc, p1), y[0] == Val::Text(key), 0 <= m <= num.n,
    ensures
        sum_of(db.tables[1].subrange(0, m), tsum_fn(p0, y)) == rsum(num, p0, key, 0, m),
        sum_of(db.tables[1].subrange(0, m), tcnt_fn(p0, y)) == rcnt(num, p0, key, 0, m),
    decreases m,
{
    let s = db.tables[1].subrange(0, m);
    if m > 0 {
        lemma_tsum_prefix(db, num, sub, kc, p1, p0, y, key, m - 1);
        assert(s.drop_last() =~= db.tables[1].subrange(0, m - 1));
        let x = db.tables[1][m - 1];
        assert(s.last() == x);
        assert(hitp(p0, x, y) == (num.uom(m - 1) == p0 && num.adsh(m - 1) == key));
        assert(coeff(x[7]) == num.val(m - 1));
    } else {
        assert(s =~= Seq::<Row>::empty());
    }
}

/// Sub row `j`'s total and count are the scan's.
pub proof fn lemma_tsum_rsum(db: Database, num: &NumCols, sub: &SubCols, kc: &KeyCols, p1: int, p0: Seq<u8>, j: int)
    requires rows_view(db, num, sub, kc, p1), 0 <= j < sub.n,
    ensures
        tsum(db.tables[1], p0, db.tables[0][j]) == rsum(num, p0, sub.key(j), 0, num.n as int),
        tcnt(db.tables[1], p0, db.tables[0][j]) == rcnt(num, p0, sub.key(j), 0, num.n as int),
{
    lemma_tsum_prefix(db, num, sub, kc, p1, p0, db.tables[0][j], sub.key(j), num.n as int);
    assert(db.tables[1].subrange(0, num.n as int) =~= db.tables[1]);
}

// ------------------------------------------------------------------------------------------- sums over ranks

/// The sum of the totals of the ranks below `m` whose sub row has key `k` (`kf` of the sub row).
pub open spec fn rk_sum(num: &NumCols, sub: &SubCols, p0: Seq<u8>, kf: spec_fn(int) -> Row, k: Row, m: int) -> int
    decreases m,
{
    if m <= 0 {
        0
    } else {
        rk_sum(num, sub, p0, kf, k, m - 1)
            + if kf(sub.qlist(sub.n as int)[m - 1]) == k { rsum(num, p0, rank_key(sub, m - 1), 0, num.n as int) } else { 0 }
    }
}

/// The number of their rows.
pub open spec fn rk_cnt(num: &NumCols, sub: &SubCols, p0: Seq<u8>, kf: spec_fn(int) -> Row, k: Row, m: int) -> int
    decreases m,
{
    if m <= 0 {
        0
    } else {
        rk_cnt(num, sub, p0, kf, k, m - 1)
            + if kf(sub.qlist(sub.n as int)[m - 1]) == k { rcnt(num, p0, rank_key(sub, m - 1), 0, num.n as int) } else { 0 }
    }
}

/// A by-sub sum over the sub rows `0..m` is the rank sum over the ranks of those rows.
proof fn lemma_subs_prefix(db: Database, num: &NumCols, sub: &SubCols, kc: &KeyCols, p0: Seq<u8>, p1: int,
    skey: spec_fn(Row) -> Row, kf: spec_fn(int) -> Row, k: Row, m: int)
    requires
        rows_view(db, num, sub, kc, p1), 0 <= m <= sub.n,
        forall|j: int| 0 <= j < sub.n ==> #[trigger] skey(db.tables[0][j]) == kf(j),
    ensures ({
        let s = db.tables[0].subrange(0, m);
        let a = sub.qlist(m).len() as int;
        &&& sum_of(s, gsum_fn(db.tables[1], p0, p1, skey, k)) == rk_sum(num, sub, p0, kf, k, a)
        &&& sum_of(s, gcnt_fn(db.tables[1], p0, p1, skey, k)) == rk_cnt(num, sub, p0, kf, k, a)
    }),
    decreases m,
{
    let s = db.tables[0].subrange(0, m);
    if m > 0 {
        lemma_subs_prefix(db, num, sub, kc, p0, p1, skey, kf, k, m - 1);
        assert(s.drop_last() =~= db.tables[0].subrange(0, m - 1));
        let y = db.tables[0][m - 1];
        assert(s.last() == y);
        lemma_qlist_prefix(sub, m, sub.n as int);
        lemma_qlist(sub, m);
        let a0 = sub.qlist(m - 1).len() as int;
        if sub.qual(m - 1) {
            assert(sub.qlist(m) == sub.qlist(m - 1).push(m - 1));
            assert(sub.qlist(m)[a0] == m - 1);
            assert(sub.qlist(sub.n as int)[a0] == sub.qlist(m)[a0]);
            lemma_tsum_rsum(db, num, sub, kc, p1, p0, m - 1);
            assert(rank_key(sub, a0) == sub.key(m - 1));
            assert(skey(y) == kf(m - 1));
        } else {
            assert(sub.qlist(m) == sub.qlist(m - 1));
            assert(!fyok(p1, y));
        }
    } else {
        assert(s =~= Seq::<Row>::empty());
    }
}

/// A group's SUM and COUNT by sub row are rank sums over all ranks.
pub proof fn lemma_subs_ranks(db: Database, num: &NumCols, sub: &SubCols, kc: &KeyCols, p0: Seq<u8>, p1: int,
    skey: spec_fn(Row) -> Row, kf: spec_fn(int) -> Row, k: Row)
    requires
        rows_view(db, num, sub, kc, p1),
        forall|j: int| 0 <= j < sub.n ==> #[trigger] skey(db.tables[0][j]) == kf(j),
    ensures ({
        let nq = sub.qlist(sub.n as int).len() as int;
        &&& gsum_subs(db.tables[0], db.tables[1], p0, p1, skey, k) == rk_sum(num, sub, p0, kf, k, nq)
        &&& gcnt_subs(db.tables[0], db.tables[1], p0, p1, skey, k) == rk_cnt(num, sub, p0, kf, k, nq)
    }),
{
    lemma_subs_prefix(db, num, sub, kc, p0, p1, skey, kf, k, sub.n as int);
    assert(db.tables[0].subrange(0, sub.n as int) =~= db.tables[0]);
}

/// Rank counts are not negative, and positive exactly when some such rank has a row.
pub proof fn lemma_rk_cnt(num: &NumCols, sub: &SubCols, p0: Seq<u8>, kf: spec_fn(int) -> Row, k: Row, m: int)
    requires 0 <= m,
    ensures
        rk_cnt(num, sub, p0, kf, k, m) >= 0,
        (rk_cnt(num, sub, p0, kf, k, m) > 0) == exists|a: int| 0 <= a < m && kf(sub.qlist(sub.n as int)[a]) == k
            && #[trigger] rcnt(num, p0, rank_key(sub, a), 0, num.n as int) > 0,
    decreases m,
{
    if m > 0 {
        lemma_rk_cnt(num, sub, p0, kf, k, m - 1);
        lemma_rcnt_nonneg(num, p0, rank_key(sub, m - 1), 0, num.n as int);
        if exists|a: int| 0 <= a < m && kf(sub.qlist(sub.n as int)[a]) == k
            && #[trigger] rcnt(num, p0, rank_key(sub, a), 0, num.n as int) > 0 {
            let a = choose|a: int| 0 <= a < m && kf(sub.qlist(sub.n as int)[a]) == k
                && #[trigger] rcnt(num, p0, rank_key(sub, a), 0, num.n as int) > 0;
            if a < m - 1 {
                assert(rk_cnt(num, sub, p0, kf, k, m - 1) > 0);
            }
        }
    }
}

/// The scan's totals and the grouping's `psum`/`tsum`: rank sums (ranks without rows have total 0).
pub proof fn lemma_psum_rk(num: &NumCols, sub: &SubCols, kc: &KeyCols, p0: Seq<u8>, qr: Seq<usize>, tot: Seq<Wide>,
    seen: Seq<bool>, k: Row, m: int)
    requires
        totals_ok(num, sub, p0, tot, seen, num.n as int),
        qr.len() == sub.qlist(sub.n as int).len(),
        forall|t: int| 0 <= t < qr.len() ==> #[trigger] qr[t] as int == sub.qlist(sub.n as int)[t],
        0 <= m <= qr.len(),
    ensures
        psum(kc, qr, tot, seen, k, m) == rk_sum(num, sub, p0, okey_fn(kc), k, m),
        groups::tsum(qr, tot, seen, m) == rk_sum(num, sub, p0, unit_fn(), Seq::<Val>::empty(), m),
    decreases m,
{
    if m > 0 {
        lemma_psum_rk(num, sub, kc, p0, qr, tot, seen, k, m - 1);
        let key = rank_key(sub, m - 1);
        assert(wval(tot[m - 1]) == rsum(num, p0, key, 0, num.n as int));
        assert(seen[m - 1] == (rcnt(num, p0, key, 0, num.n as int) > 0));
        if !seen[m - 1] {
            lemma_rcnt_nonneg(num, p0, key, 0, num.n as int);
            crate::agent::run::lemma_rcnt_zero(num, p0, key, 0, num.n as int);
        }
        assert(okey_fn(kc)(sub.qlist(sub.n as int)[m - 1]) == kc.okey(qr[m - 1] as int));
    }
}

/// The outer key of a sub row and the unit key.
pub open spec fn okey_fn(kc: &KeyCols) -> spec_fn(int) -> Row {
    |j: int| kc.okey(j)
}

pub open spec fn ikey_fn(kc: &KeyCols) -> spec_fn(int) -> Row {
    |j: int| seq![Val::Int(kc.cik(j))]
}

pub open spec fn unit_fn() -> spec_fn(int) -> Row {
    |j: int| Seq::<Val>::empty()
}

} // verus!
