//! Builder of storage `lisupp`, derived from `facts` (which it extends: the parts of `facts` come first, unchanged).
//!
//! It reads the l_suppkey column of the stored lineitem rows of `facts` (U32 codes, I64 bases over uniform blocks),
//! lists the stored rows in key order with a counting sort (`sort::counting_sort`, an unproved heuristic), and keeps
//! that list as a key index of kind 2 only when the run-time checks confirm a bijection of the rows
//! (`perm::check_perm32`) in nondecreasing key order (`sort::check_sorted`); otherwise kind 0 (no order known).
//!
//! Proof: for every database bound to `facts`, the inherited lineitem parts satisfy this storage's `li_ok` over the
//! four stored columns (`lemma_li_ok`: `facts` states the same layout over all fifteen stored columns, with the same
//! definitions under another module path), and the new parts satisfy `index_ok`.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::{sources_ready, sources_bound, storage_parts};
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::stored::part_len;
use crate::spec::value::*;
use crate::link::query::{proj, proj_all};
use crate::link::source::lemma_proj_all_index;
use crate::stores::lisupp::interface::*;
use crate::stores::lisupp::interface::common::colfmt::*;
use crate::stores::lisupp::interface::common::keyidx::*;
use crate::stores::lisupp::declaration::{stored_relations, stored_cols_t0};
use crate::stores::facts::interface as fi;
use crate::stores::facts::declaration as fd;

pub mod perm;
pub mod sort;

use perm::*;
use sort::*;

verus! {

// ------------------------------------------------------------------------------------------------ facts of facts

/// The lineitem parts of `facts` (the first parts of the source and of this storage).
pub open spec fn ftp(sv: StoresView) -> Seq<PartView> {
    sv.facts.subrange(0, LI_PARTS as int)
}

/// What `facts` states of its lineitem parts for a bound database.
proof fn lemma_facts_li(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures
        sv.facts.len() == fi::FACTS_PARTS,
        fi::lineitem_ok(ftp(sv), fd::stored_relations(db)[0]),
{
    assert(fi::represents(sv.facts, fd::stored_relations(db)));
}

/// A frame-of-reference value is the same under both copies of the column format.
proof fn lemma_for_at_same(gp: PartView, n: int, bs: int, base: PartView, codes: PartView, j: int)
    requires
        groups_part_ok(gp, n, bs),
        0 <= j < n,
    ensures
        for_at(u64s(gp), base, codes, j) == fi::common::colfmt::for_at(fi::common::colfmt::u64s(gp), base, codes, j),
{
    crate::stores::lisupp::interface::common::read::lemma_for_row(gp, n, bs, base, codes, j);
    assert(fi::common::colfmt::groups_part_ok(gp, n, bs));
    fi::common::read::lemma_for_row(gp, n, bs, base, codes, j);
}

/// The layout facts of `facts` in this storage's terms.
proof fn lemma_layout(tp: Seq<PartView>, n: int)
    requires fi::table_layout_ok(tp, n),
    ensures
        table_layout_ok(tp, n),
        groups_part_ok(tp[1], n, u64s(tp[0])[1] as int),
{
}

/// A bijection under the `facts` copy of the definitions is one under this storage's copy.
proof fn lemma_is_perm_same(m: Seq<int>, n: int)
    requires fi::common::colfmt::is_perm(m, n),
    ensures is_perm(m, n),
{
    assert forall|i: int| 0 <= i < n implies #[trigger] covered(m, i) by {
        assert(fi::common::colfmt::covered(m, i));
    }
}

/// A zone map under the `facts` copy of the definitions is one under this storage's copy.
proof fn lemma_zone_same(tp: Seq<PartView>, gp: int, cp: int, bp: int, zp: int)
    requires fi::common::colfmt::zone_at(tp, gp, cp, bp, zp),
    ensures zone_at(tp, gp, cp, bp, zp),
{
    let gs = gs_at(tp, gp);
    let z = i64s(tp[zp]);
    assert forall|g: int, j: int| #[trigger] in_group(gs, g, j) implies base_at(tp[bp], g) + code_at(tp[cp], j) <= z[g] by {
        assert(fi::common::colfmt::in_group(fi::common::colfmt::gs_at(tp, gp), g, j));
    }
}

/// The row map of `facts` is this storage's row map.
proof fn lemma_map_same(tp: Seq<PartView>, n: int)
    requires fi::table_layout_ok(tp, n),
    ensures
        li_map(tp, n) == fi::lineitem_map(tp, n),
{
    lemma_layout(tp, n);
    let bs = u64s(tp[0])[1] as int;
    let a = li_map(tp, n);
    let b = fi::lineitem_map(tp, n);
    assert forall|j: int| 0 <= j < n implies a[j] == b[j] by {
        lemma_for_at_same(tp[1], n, bs, tp[LI_PERM_BASE as int], tp[LI_PERM_CODES as int], j);
    }
    assert(a =~= b);
}

/// Column `cs` of this storage's stored rows is column `cf` of the stored rows of `facts`.
pub open spec fn col_from(srows: Seq<Row>, frows: Seq<Row>, cs: int, cf: int) -> bool {
    &&& srows.len() == frows.len()
    &&& forall|j: int| 0 <= j < srows.len() ==> #[trigger] srows[j][cs] == frows[j][cf]
}

/// An integer column carries over.
proof fn lemma_int_col(tp: Seq<PartView>, n: int, cp: int, bp: int, srows: Seq<Row>, frows: Seq<Row>, cs: int, cf: int)
    requires
        fi::table_layout_ok(tp, n),
        frows.len() == n,
        col_from(srows, frows, cs, cf),
        fi::common::colfmt::int_col_at(tp, 1, cp, bp, frows, cf),
    ensures
        int_col_at(tp, 1, cp, bp, srows, cs),
{
    lemma_layout(tp, n);
    let bs = u64s(tp[0])[1] as int;
    assert(for_i64_shape(tp, 1, cp, bp, srows.len() as int));
    assert forall|j: int| 0 <= j < srows.len() implies #[trigger] srows[j][cs] == Val::Int(for_at(gs_at(tp, 1), tp[bp], tp[cp], j)) by {
        lemma_for_at_same(tp[1], n, bs, tp[bp], tp[cp], j);
        assert(frows[j][cf] == Val::Int(fi::common::colfmt::for_at(fi::common::colfmt::gs_at(tp, 1), tp[bp], tp[cp], j)));
    }
}

/// A numeric column carries over.
proof fn lemma_num_col(tp: Seq<PartView>, n: int, cp: int, bp: int, srows: Seq<Row>, frows: Seq<Row>, cs: int, cf: int, scale: nat)
    requires
        fi::table_layout_ok(tp, n),
        frows.len() == n,
        col_from(srows, frows, cs, cf),
        fi::common::colfmt::num_col_at(tp, 1, cp, bp, frows, cf, scale),
    ensures
        num_col_at(tp, 1, cp, bp, srows, cs, scale),
{
    lemma_layout(tp, n);
    let bs = u64s(tp[0])[1] as int;
    assert(for_i64_shape(tp, 1, cp, bp, srows.len() as int));
    assert forall|j: int| 0 <= j < srows.len() implies #[trigger] srows[j][cs] == (Val::Num { coeff: for_at(gs_at(tp, 1), tp[bp], tp[cp], j), scale }) by {
        lemma_for_at_same(tp[1], n, bs, tp[bp], tp[cp], j);
        assert(frows[j][cf] == (Val::Num { coeff: fi::common::colfmt::for_at(fi::common::colfmt::gs_at(tp, 1), tp[bp], tp[cp], j), scale }));
    }
}

/// A date column carries over.
proof fn lemma_date_col(tp: Seq<PartView>, n: int, cp: int, bp: int, srows: Seq<Row>, frows: Seq<Row>, cs: int, cf: int)
    requires
        fi::table_layout_ok(tp, n),
        frows.len() == n,
        col_from(srows, frows, cs, cf),
        fi::common::colfmt::date_col_at(tp, 1, cp, bp, frows, cf),
    ensures
        date_col_at(tp, 1, cp, bp, srows, cs),
{
    lemma_layout(tp, n);
    let bs = u64s(tp[0])[1] as int;
    assert(for_i64_shape(tp, 1, cp, bp, srows.len() as int));
    assert forall|j: int| 0 <= j < srows.len() implies #[trigger] srows[j][cs] == Val::Date(for_at(gs_at(tp, 1), tp[bp], tp[cp], j)) by {
        lemma_for_at_same(tp[1], n, bs, tp[bp], tp[cp], j);
        assert(frows[j][cf] == Val::Date(fi::common::colfmt::for_at(fi::common::colfmt::gs_at(tp, 1), tp[bp], tp[cp], j)));
    }
}

/// The stored relation of this storage and of `facts`: lineitem projected on 4 and 15 columns.
proof fn lemma_rels(db: Database)
    ensures
        stored_relations(db)[0].len() == db.tables[0].len(),
        fd::stored_relations(db)[0].len() == db.tables[0].len(),
        forall|i: int| 0 <= i < db.tables[0].len() ==> (#[trigger] stored_relations(db)[0][i]).len() == 4
            && stored_relations(db)[0][i][0] == fd::stored_relations(db)[0][i][2]
            && stored_relations(db)[0][i][1] == fd::stored_relations(db)[0][i][5]
            && stored_relations(db)[0][i][2] == fd::stored_relations(db)[0][i][6]
            && stored_relations(db)[0][i][3] == fd::stored_relations(db)[0][i][10],
{
    let t = db.tables[0];
    lemma_proj_all_index(t, stored_cols_t0());
    lemma_proj_all_index(t, fd::stored_cols_t0());
    assert forall|i: int| 0 <= i < t.len() implies (#[trigger] stored_relations(db)[0][i]).len() == 4
        && stored_relations(db)[0][i][0] == fd::stored_relations(db)[0][i][2]
        && stored_relations(db)[0][i][1] == fd::stored_relations(db)[0][i][5]
        && stored_relations(db)[0][i][2] == fd::stored_relations(db)[0][i][6]
        && stored_relations(db)[0][i][3] == fd::stored_relations(db)[0][i][10] by {
        assert(stored_relations(db)[0][i] == proj(t[i], stored_cols_t0()));
        assert(fd::stored_relations(db)[0][i] == proj(t[i], fd::stored_cols_t0()));
    }
}

/// For every database bound to `facts`, the inherited lineitem parts hold this storage's four columns.
pub proof fn lemma_li_ok(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures li_ok(ftp(sv), stored_relations(db)[0]),
{
    lemma_facts_li(sv, db);
    lemma_rels(db);
    let tp = ftp(sv);
    let frel = fd::stored_relations(db)[0];
    let srel = stored_relations(db)[0];
    let n = srel.len() as int;
    assert(fi::table_layout_ok(tp, n));
    lemma_layout(tp, n);
    lemma_map_same(tp, n);
    let m = li_map(tp, n);
    assert(perm_col_at(tp, LI_GROUPS as int, LI_PERM_CODES as int, LI_PERM_BASE as int, n)) by {
        assert(fi::common::colfmt::perm_col_at(tp, 1, 2, 3, n));
        assert(fi::lineitem_map(tp, n) == fi::common::colfmt::for_map(fi::common::colfmt::gs_at(tp, 1), tp[3], tp[2], n));
        lemma_is_perm_same(m, n);
        assert(for_u64_shape(tp, 1, 2, 3, n));
    }
    let srows = li_rows(tp, srel);
    let frows = fi::lineitem_rows(tp, frel);
    assert(srows == stored_rows(srel, m));
    assert(frows == fi::common::colfmt::stored_rows(frel, fi::lineitem_map(tp, n)));
    assert(frows.len() == n);
    assert forall|j: int| 0 <= j < n implies 0 <= #[trigger] m[j] < n by {
        assert(is_perm(m, n));
    }
    assert(col_from(srows, frows, 0, 2) && col_from(srows, frows, 1, 5) && col_from(srows, frows, 2, 6) && col_from(srows, frows, 3, 10)) by {
        assert forall|j: int| 0 <= j < n implies #[trigger] srows[j] == srel[m[j]] && frows[j] == frel[m[j]] by {}
    }
    assert(fi::lineitem_cols_ok(tp, frows));
    lemma_int_col(tp, n, LI_SUPPKEY_CODES as int, LI_SUPPKEY_BASE as int, srows, frows, 0, 2);
    lemma_num_col(tp, n, LI_EXTENDEDPRICE_CODES as int, LI_EXTENDEDPRICE_BASE as int, srows, frows, 1, 5, 2);
    lemma_num_col(tp, n, LI_DISCOUNT_CODES as int, LI_DISCOUNT_BASE as int, srows, frows, 2, 6, 2);
    lemma_date_col(tp, n, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, srows, frows, 3, 10);
    assert(fi::common::colfmt::zone_at(tp, 1, 28, 29, 30));
    lemma_zone_same(tp, 1, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, LI_SHIPDATE_ZMAX as int);
    assert(rows_width(srel, 4));
}

// ------------------------------------------------------------------------------------------------ the key column

/// The l_suppkey key column of the inherited parts is well shaped, for every bound database.
proof fn lemma_keys_wf(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures ({
        let tp = ftp(sv);
        let n = stored_relations(db)[0].len() as int;
        let bs = u64s(tp[LI_LAYOUT as int])[1] as int;
        &&& tp[LI_SUPPKEY_CODES as int] is U32
        &&& tp[LI_SUPPKEY_BASE as int] is I64
        &&& tp[LI_LAYOUT as int] is U64
        &&& u64s(tp[LI_LAYOUT as int]).len() == 2
        &&& keys_wf(u32s(tp[LI_SUPPKEY_CODES as int]), i64s(tp[LI_SUPPKEY_BASE as int]), bs, n)
        &&& n + bs <= u64::MAX
    }),
{
    lemma_li_ok(sv, db);
    let tp = ftp(sv);
    let srel = stored_relations(db)[0];
    let n = srel.len() as int;
    let bs = u64s(tp[LI_LAYOUT as int])[1] as int;
    let srows = li_rows(tp, srel);
    assert(int_col_at(tp, 1, LI_SUPPKEY_CODES as int, LI_SUPPKEY_BASE as int, srows, 0));
    lemma_uniform_groups(tp[1], n, bs);
    lemma_nblocks(n, bs);
}

/// Kind 0 (no order known) holds for any well-shaped key column.
proof fn lemma_keyidx_none(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bsize: int, n: int)
    requires keys_wf(kc, kb, bsize, n), n >= 0,
    ensures keyidx_ok(kc, kb, ic, ib, bsize, 0, n),
{
}

/// Kind 2: the rows listed by `p` (index bases all zero) are a bijection in nondecreasing key order.
proof fn lemma_keyidx_perm(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bsize: int, n: int)
    requires
        keys_wf(kc, kb, bsize, n),
        ic.len() == n,
        ib.len() * bsize >= n,
        forall|g: int| 0 <= g < ib.len() ==> #[trigger] ib[g] == 0,
        is_perm(map32(ic), n),
        forall|r: int| 0 <= r < n - 1 ==> (#[trigger] ic[r]) < n && ic[r + 1] < n
            && fkey(kc, kb, bsize, ic[r] as int) <= fkey(kc, kb, bsize, ic[r + 1] as int),
    ensures keyidx_ok(kc, kb, ic, ib, bsize, 2, n),
{
    assert forall|r: int| 0 <= r < n implies #[trigger] fidx(ic, ib, bsize, r) == ic[r] as int by {
        crate::stores::lisupp::interface::common::read::lemma_div_lt(r, bsize, ib.len() as int);
    }
    assert(idx_map(ic, ib, bsize, n) =~= map32(ic));
    assert forall|r: int| 0 <= r < n - 1 implies #[trigger] sorted_at(kc, kb, ic, ib, bsize, 2, r) by {
        assert(fidx(ic, ib, bsize, r) == ic[r] as int);
        assert(fidx(ic, ib, bsize, r + 1) == ic[r + 1] as int);
        assert(ic[r] < n);
    }
}

// ------------------------------------------------------------------------------------------------ build

/// `n` zeros.
pub open spec fn zeros(n: nat) -> Seq<u64> {
    Seq::new(n, |_g: int| 0u64)
}

/// The new parts: index codes, zero bases and the kind.
fn index_parts(ic: Vec<u32>, nb: usize, kind: u64) -> (p: Vec<OwnedPart>)
    ensures
        owned_parts_view(p@) == seq![PartView::U32(ic@), PartView::U64(zeros(nb as nat)), PartView::U64(seq![kind])],
{
    let ghost icv = ic@;
    let ib = crate::gendb_entry::work::filled(nb, 0u64);
    proof {
        assert(ib@ =~= zeros(nb as nat));
    }
    let mut kv: Vec<u64> = Vec::new();
    kv.push(kind);
    let mut p: Vec<OwnedPart> = Vec::new();
    p.push(OwnedPart::U32(ic));
    p.push(OwnedPart::U64(ib));
    p.push(OwnedPart::U64(kv));
    proof {
        assert(kv@ =~= seq![kind]);
        assert(owned_parts_view(p@) =~= seq![PartView::U32(icv), PartView::U64(zeros(nb as nat)), PartView::U64(seq![kind])]);
    }
    p
}

pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> forall|db: Database| #[trigger] sources_bound(old(stores)@, db) ==>
            represents(storage_parts(old(stores)@, owned_parts_view(p@)), stored_relations(db)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost sv = stores@;
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    proof {
        lemma_facts_li(sv, db0);
        lemma_keys_wf(sv, db0);
        lemma_rels(db0);
    }
    let ghost tp = ftp(sv);
    let ghost n0 = stored_relations(db0)[0].len() as int;
    proof {
        assert(tp[LI_SUPPKEY_CODES as int] == sv.facts[LI_SUPPKEY_CODES as int]);
        assert(tp[LI_SUPPKEY_BASE as int] == sv.facts[LI_SUPPKEY_BASE as int]);
        assert(tp[LI_LAYOUT as int] == sv.facts[LI_LAYOUT as int]);
    }
    let f = &mut stores.facts;
    let n = f.part_len(LI_SUPPKEY_CODES);
    let nb = f.part_len(LI_SUPPKEY_BASE);
    let lay = f.extent_u64(LI_LAYOUT, 0, 2);
    let bs64 = lay[1];
    let kc = f.extent_u32(LI_SUPPKEY_CODES, 0, n);
    let kb = f.extent_i64(LI_SUPPKEY_BASE, 0, nb);
    proof {
        assert(kc@ =~= u32s(tp[LI_SUPPKEY_CODES as int]));
        assert(kb@ =~= i64s(tp[LI_SUPPKEY_BASE as int]));
        assert(n == n0);
        assert(lay@ =~= u64s(tp[LI_LAYOUT as int]));
    }
    let mut kind: u64 = 0;
    let mut ic: Vec<u32> = Vec::new();
    if n <= u32::MAX as usize && bs64 <= usize::MAX as u64 {
        let bs = bs64 as usize;
        match counting_sort(kc, kb, bs, n) {
            Some(p) => {
                if check_perm32(&p) && check_sorted(kc, kb, bs, n, &p) {
                    kind = 2;
                    ic = p;
                }
            },
            None => {},
        }
    }
    let ghost icv = ic@;
    let ghost ibv = zeros(nb as nat);
    let ghost bsi = bs64 as int;
    proof {
        if kind == 2 {
            assert forall|g: int| 0 <= g < ibv.len() implies #[trigger] ibv[g] == 0 by {}
            lemma_keyidx_perm(kc@, kb@, icv, ibv, bsi, n as int);
        } else {
            lemma_keyidx_none(kc@, kb@, icv, ibv, bsi, n as int);
        }
    }
    let parts = index_parts(ic, nb, kind);
    proof {
        let built = owned_parts_view(parts@);
        let all = storage_parts(sv, built);
        assert(all == sv.facts + built);
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies represents(all, stored_relations(db)) by {
            lemma_facts_li(sv, db);
            lemma_li_ok(sv, db);
            lemma_keys_wf(sv, db);
            assert(all.len() == LISUPP_PARTS);
            assert(all.subrange(0, LI_PARTS as int) =~= ftp(sv));
            assert(all[LI_SUPPKEY_CODES as int] == sv.facts[LI_SUPPKEY_CODES as int]);
            assert(all[LI_SUPPKEY_BASE as int] == sv.facts[LI_SUPPKEY_BASE as int]);
            assert(all[LI_LAYOUT as int] == sv.facts[LI_LAYOUT as int]);
            assert(all[SX_CODES as int] == PartView::U32(icv));
            assert(all[SX_BASES as int] == PartView::U64(ibv));
            assert(all[SX_KIND as int] == PartView::U64(seq![kind]));
            assert(stored_relations(db)[0].len() == n);
            assert(index_ok(all, stored_relations(db)[0].len() as int));
        }
    }
    Ok(parts)
}

} // verus!
