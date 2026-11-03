//! What the two storages give about a bound database (`bound_db`), in terms of the views the scans read (`Cv`):
//! - custpart (`customer_ok`): customer row `i`'s c_custkey is `kb[i / bs] + kc[i]`, its c_phone is
//!   `text_of(poffs, pbytes, i)`, its c_acctbal coefficient (scale 2) is `ab[i / bs] + ac[i]`;
//! - orders_custidx (`represents`): in directory mode, the entry of key `k` is empty exactly when no orders row has
//!   o_custkey `k`, and a key outside the directory has no row; in fallback mode the keys are stored per row.
//! `shape_ok` is what the extent requests need; `rows_match` relates every row of the views to the database.
use vstd::prelude::*;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::*;
use crate::link::query::proj_all;
use crate::link::expr::{ival, tval};
use crate::link::source::lemma_proj_all_index;
use crate::stores::custpart::interface as CP;
use crate::stores::custpart::interface::common::colfmt as CPC;
use crate::stores::orders_custidx::interface as IX;
use super::model::*;
use super::sql::*;

verus! {

// ------------------------------------------------------------------------------------------------ shapes

/// The part kinds and lengths the query requests.
pub open spec fn shape_ok(sv: StoresView) -> bool {
    let (pc, pi) = (sv.custpart, sv.orders_custidx);
    let n = CPC::u32s(pc[2]).len();
    &&& pc.len() == CP::CUSTPART_PARTS
    &&& pc[0] is U64 && CPC::u64s(pc[0]).len() == 2 && CPC::u64s(pc[0])[1] >= 1
    &&& pc[2] is U32 && pc[3] is I64 && pc[10] is U64 && pc[11] is U8 && pc[12] is U32 && pc[13] is I64
    &&& CPC::u64s(pc[10]).len() == n + 1
    &&& CPC::u32s(pc[12]).len() == n
    &&& pi.len() == IX::CUSTIDX_PARTS
    &&& pi[0] is I64 && pi[1] is U32 && pi[3] is I64
    &&& IX::idx_i64s(pi[0]).len() == 2
}

/// The views the query built from the parts.
pub open spec fn views_of(sv: StoresView, v: Cv) -> bool {
    let (pc, pi) = (sv.custpart, sv.orders_custidx);
    let meta = IX::idx_i64s(pi[0]);
    let offs = IX::idx_u32s(pi[1]);
    &&& v.kc == CPC::u32s(pc[2]) && v.kb == CPC::i64s(pc[3])
    &&& v.poffs == CPC::u64s(pc[10]) && v.pbytes == CPC::u8s(pc[11])
    &&& v.ac == CPC::u32s(pc[12]) && v.ab == CPC::i64s(pc[13])
    &&& v.n == CPC::u32s(pc[2]).len()
    &&& v.bs >= 1
    &&& forall|i: int| 0 <= i < v.n ==> #[trigger] (i / v.bs) == i / (CPC::u64s(pc[0])[1] as int)
    &&& v.dir == (meta[0] == IX::MODE_DIRECTORY && offs.len() >= 1)
    &&& v.kmin == meta[1] as int
    &&& v.offs == offs
    &&& v.nk == (if offs.len() >= 1 { offs.len() - 1 } else { 0 })
    &&& v.keys == IX::idx_i64s(pi[3])
    &&& v.n_o == v.keys.len()
}

// ------------------------------------------------------------------------------------------------ customer

/// The customer columns the query reads, out of custpart's `customer_ok`.
pub open spec fn cust_cols(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& CP::table_layout_ok(tp, rel.len() as int)
    &&& CPC::int_col_at(tp, CP::CU_GROUPS as int, CP::CU_CUSTKEY_CODES as int, CP::CU_CUSTKEY_BASE as int, rel, 0)
    &&& tp[CP::CU_CUSTKEY_CODES as int] is U32
    &&& CPC::text_col_at(tp, CP::CU_PHONE_OFFS as int, CP::CU_PHONE_BYTES as int, rel, 4)
    &&& CPC::num_col_at(tp, CP::CU_GROUPS as int, CP::CU_ACCTBAL_CODES as int, CP::CU_ACCTBAL_BASE as int, rel, 5, 2)
    &&& tp[CP::CU_ACCTBAL_CODES as int] is U32
}

/// The customer table of custpart's `represents`.
proof fn lemma_cust_table(p: Seq<PartView>, db: Database)
    requires CP::represents(p, crate::stores::custpart::declaration::stored_relations(db)),
    ensures
        cust_cols(p.subrange(CP::CUSTOMER_FIRST as int, (CP::CUSTOMER_FIRST + CP::CU_PARTS) as int),
            crate::stores::custpart::declaration::stored_relations(db)[0]),
        p.len() == CP::CUSTPART_PARTS,
{
    hide(CP::part_ok);
    hide(CPC::dict_col_at);
    hide(crate::stores::custpart::interface::common::keyidx::keyidx_ok);
}

/// `j / b < nblocks(n, b)` for `j < n`.
proof fn lemma_div_lt_blocks(j: int, n: int, b: int)
    requires 0 <= j < n, b >= 1,
    ensures j / b < (n + b - 1) / b,
{
    assert(j / b <= (n - 1) / b) by (nonlinear_arith) requires 0 <= j <= n - 1, b >= 1;
    assert((n - 1) / b < (n + b - 1) / b) by (nonlinear_arith) requires n >= 1, b >= 1;
}

/// A FOR value through custpart's reader lemma.
proof fn lemma_for_row(gp: PartView, base: PartView, codes: PartView, n: int, bs: int, i: int)
    requires CPC::groups_part_ok(gp, n, bs), 0 <= i < n, base is I64, codes is U32,
    ensures CPC::for_at(CPC::u64s(gp), base, codes, i) == CPC::i64s(base)[i / bs] + CPC::u32s(codes)[i],
{
    crate::stores::custpart::interface::common::read::lemma_for_row(gp, n, bs, base, codes, i);
}

/// Customer row `i` in the views.
pub open spec fn crow_match(v: Cv, db: Database, i: int) -> bool {
    &&& ctab(db)[i][0] == Val::Int(rkey(v, i))
    &&& ctab(db)[i][4] == Val::Text(rtext(v, i))
    &&& ctab(db)[i][5] == (Val::Num { coeff: racct(v, i), scale: 2 })
    &&& (i / v.bs) < v.ab.len() && (i / v.bs) < v.kb.len()
}

/// custpart's `represents` gives every customer row in the views.
proof fn lemma_cust(sv: StoresView, db: Database, v: Cv)
    requires
        CP::represents(sv.custpart, crate::stores::custpart::declaration::stored_relations(db)),
        views_of(sv, v),
    ensures
        v.n == ctab(db).len(),
        v.poffs.len() == v.n + 1,
        forall|i: int| 0 <= i < v.n ==> #[trigger] v.poffs[i] <= v.poffs[i + 1] && v.poffs[i + 1] <= v.pbytes.len(),
        forall|i: int| 0 <= i < v.n ==> #[trigger] crow_match(v, db, i),
        v.ac.len() == v.n,
{
    hide(CP::represents);
    let p = sv.custpart;
    lemma_cust_table(p, db);
    let rels = crate::stores::custpart::declaration::stored_relations(db);
    let tp = p.subrange(CP::CUSTOMER_FIRST as int, (CP::CUSTOMER_FIRST + CP::CU_PARTS) as int);
    let rel = rels[0];
    lemma_proj_all_index(db.tables[2], crate::stores::custpart::declaration::stored_cols_t0());
    let n = ctab(db).len() as int;
    assert(rel.len() == n);
    assert(tp[0] == p[0] && tp[1] == p[1] && tp[2] == p[2] && tp[3] == p[3] && tp[10] == p[10] && tp[11] == p[11]
        && tp[12] == p[12] && tp[13] == p[13]);
    let bsz = CPC::u64s(p[0])[1] as int;
    let gs = CPC::u64s(p[1]);
    assert(CPC::groups_part_ok(p[1], n, bsz));
    assert(CPC::int_col_at(tp, 1, 2, 3, rel, 0));
    assert(CPC::num_col_at(tp, 1, 12, 13, rel, 5, 2));
    assert(CPC::text_col_at(tp, 10, 11, rel, 4));
    assert(gs == CPC::uniform_gs(n, bsz));
    assert(crate::gendb_entry::stored::part_len(p[3]) == gs.len() - 1);
    assert(crate::gendb_entry::stored::part_len(p[13]) == gs.len() - 1);
    assert(crate::gendb_entry::stored::part_len(p[2]) == n);
    assert(crate::gendb_entry::stored::part_len(p[12]) == n);
    CPC::lemma_uniform_groups(p[1], n, bsz);
    assert(v.n == n);
    assert(CPC::text_parts_wf(v.poffs, v.pbytes, n));
    assert forall|i: int| 0 <= i < v.n implies #[trigger] v.poffs[i] <= v.poffs[i + 1] && v.poffs[i + 1] <= v.pbytes.len() by {
        assert(CPC::text_range_ok(v.poffs, v.pbytes, i));
    }
    assert forall|i: int| 0 <= i < v.n implies #[trigger] crow_match(v, db, i) by {
        lemma_for_row(p[1], p[3], p[2], n, bsz, i);
        lemma_for_row(p[1], p[13], p[12], n, bsz, i);
        lemma_div_lt_blocks(i, n, bsz);
        assert(i / v.bs == i / bsz);
        assert(rel[i][0] == Val::Int(CPC::for_at(gs, p[3], p[2], i)));
        assert(rel[i][4] == Val::Text(CPC::text_of(v.poffs, v.pbytes, i)));
        assert(rel[i][5] == (Val::Num { coeff: CPC::for_at(gs, p[13], p[12], i), scale: 2 }));
        assert(rel[i][0] == db.tables[2][i][0]);
        assert(rel[i][4] == db.tables[2][i][4]);
        assert(rel[i][5] == db.tables[2][i][5]);
    }
}

// ------------------------------------------------------------------------------------------------ orders index

/// No row of `rel[..m]` has key `k` exactly when the count is zero.
proof fn lemma_count_zero(rel: Seq<Row>, k: int, m: int)
    requires 0 <= m <= rel.len(),
    ensures (IX::count_key(rel, k, m) == 0) == (forall|r: int| 0 <= r < m ==> #[trigger] rel[r][0] != Val::Int(k)),
    decreases m,
{
    if m > 0 {
        lemma_count_zero(rel, k, m - 1);
        if IX::count_key(rel, k, m) == 0 {
            assert forall|r: int| 0 <= r < m implies #[trigger] rel[r][0] != Val::Int(k) by {
                if r < m - 1 {} else {}
            }
        }
    }
}

/// orders_custidx's `represents` gives the absence of orders of every key.
proof fn lemma_index(sv: StoresView, db: Database, v: Cv, k: int)
    requires
        IX::represents(sv.orders_custidx, crate::stores::orders_custidx::declaration::stored_relations(db)),
        views_of(sv, v),
    ensures noord_key(v, k) == !has_ord(db, k),
{
    let p = sv.orders_custidx;
    let rels = crate::stores::orders_custidx::declaration::stored_relations(db);
    let rel = rels[0];
    lemma_proj_all_index(db.tables[1], crate::stores::orders_custidx::declaration::stored_cols_t0());
    let n = otab(db).len() as int;
    assert(rel.len() == n);
    assert forall|r: int| 0 <= r < n implies #[trigger] rel[r][0] == otab(db)[r][1] by {
        assert(rel[r][0] == db.tables[1][r][1]);
    }
    let meta = IX::idx_i64s(p[0]);
    if meta[0] == IX::MODE_DIRECTORY {
        let offs = IX::idx_u32s(p[1]);
        let nk = offs.len() - 1;
        let kmin = meta[1] as int;
        assert(IX::directory_ok(kmin, nk, offs, IX::idx_u32s(p[2]), rel));
        assert(v.dir && v.nk == nk && v.kmin == kmin);
        lemma_count_zero(rel, k, n);
        if kmin <= k < kmin + nk {
            let e = k - kmin;
            assert(offs[e + 1] - offs[e] == IX::count_key(rel, kmin + e, n));
        } else {
            IX::lemma_directory_outside(kmin, nk, offs, IX::idx_u32s(p[2]), rel, k);
        }
        if has_ord(db, k) {
            let j = choose|j: int| 0 <= j < otab(db).len() && #[trigger] otab(db)[j][1] == Val::Int(k);
            assert(rel[j][0] == Val::Int(k));
        }
        if !has_ord(db, k) {
            assert forall|r: int| 0 <= r < n implies #[trigger] rel[r][0] != Val::Int(k) by {
                assert(rel[r][0] == otab(db)[r][1]);
            }
        }
    } else {
        assert(!v.dir);
        let keys = IX::idx_i64s(p[3]);
        assert(keys.len() == n);
        assert forall|r: int| 0 <= r < n implies #[trigger] otab(db)[r][1] == Val::Int(keys[r] as int) by {
            assert(rel[r][0] == Val::Int(keys[r] as int));
        }
        if has_ord(db, k) {
            let j = choose|j: int| 0 <= j < otab(db).len() && #[trigger] otab(db)[j][1] == Val::Int(k);
            assert(otab(db)[j][1] == Val::Int(keys[j] as int));
            assert(keys[j] == k);
        }
        if !has_ord(db, k) {
            assert forall|r: int| 0 <= r < v.n_o implies #[trigger] v.keys[r] != k by {
                assert(otab(db)[r][1] == Val::Int(keys[r] as int));
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ binding

/// The shapes of the parts, for a bound database.
pub proof fn lemma_shape(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures shape_ok(sv),
{
    let p = sv.custpart;
    lemma_cust_table(p, db);
    let tp = p.subrange(CP::CUSTOMER_FIRST as int, (CP::CUSTOMER_FIRST + CP::CU_PARTS) as int);
    let rel = crate::stores::custpart::declaration::stored_relations(db)[0];
    let n = rel.len() as int;
    assert(tp[0] == p[0] && tp[1] == p[1] && tp[2] == p[2] && tp[3] == p[3] && tp[10] == p[10] && tp[11] == p[11]
        && tp[12] == p[12] && tp[13] == p[13]);
    let bsz = CPC::u64s(p[0])[1] as int;
    assert(CPC::groups_part_ok(p[1], n, bsz));
    assert(CPC::int_col_at(tp, 1, 2, 3, rel, 0));
    assert(CPC::num_col_at(tp, 1, 12, 13, rel, 5, 2));
    assert(CPC::text_col_at(tp, 10, 11, rel, 4));
    assert(crate::gendb_entry::stored::part_len(p[2]) == n);
    assert(crate::gendb_entry::stored::part_len(p[12]) == n);
    assert(CPC::text_parts_wf(CPC::u64s(p[10]), CPC::u8s(p[11]), n));
}

/// Every row of the views, for a bound database.
pub open spec fn rows_match(v: Cv, db: Database) -> bool {
    &&& db_ok(db)
    &&& v.n == ctab(db).len()
    &&& forall|i: int| 0 <= i < v.n ==> #[trigger] row_match(v, db, i)
}

/// Customer row `i`: phone, balance, key and the absence of its orders.
pub open spec fn row_match(v: Cv, db: Database, i: int) -> bool {
    &&& crow_ok(ctab(db)[i])
    &&& rtext(v, i) == cphone(ctab(db)[i])
    &&& racct(v, i) == cacct(ctab(db)[i])
    &&& rkey(v, i) == ckey(ctab(db)[i])
    &&& rnoord(v, i) == !has_ord(db, ckey(ctab(db)[i]))
}

/// A bound database: the views describe it, and they meet `cv_ok`.
pub proof fn lemma_bind(sv: StoresView, db: Database, v: Cv)
    requires
        bound_db(sv, db),
        views_of(sv, v),
        v.n < 0x1_0000_0000_0000_0000,
        v.pbytes.len() <= usize::MAX,
        v.ps.len() == 7,
    ensures
        rows_match(v, db),
        cv_ok(v),
{
    lemma_db_ok(db);
    lemma_cust(sv, db, v);
    assert forall|i: int| 0 <= i < v.n implies #[trigger] row_match(v, db, i) by {
        assert(crow_match(v, db, i));
        assert(crow_ok(ctab(db)[i]));
        lemma_index(sv, db, v, rkey(v, i));
    }
    assert forall|i: int| 0 <= i < v.n implies -acct_bound() < #[trigger] racct(v, i) < acct_bound() by {
        assert(row_match(v, db, i));
        assert(crow_ok(ctab(db)[i]));
    }
    assert forall|i: int| 0 <= i < v.n implies i64::MIN <= #[trigger] rkey(v, i) <= i64::MAX by {
        assert(row_match(v, db, i));
        assert(crow_ok(ctab(db)[i]));
    }
    assert forall|i: int| 0 <= i < v.n implies #[trigger] (i / v.bs) < v.ab.len() && i / v.bs < v.kb.len() by {
        assert(crow_match(v, db, i));
    }
    let p = sv.orders_custidx;
    let rels = crate::stores::orders_custidx::declaration::stored_relations(db);
    lemma_proj_all_index(db.tables[1], crate::stores::orders_custidx::declaration::stored_cols_t0());
    if !v.dir {
        let meta = IX::idx_i64s(p[0]);
        assert(meta[0] != IX::MODE_DIRECTORY);
    }
}

} // verus!
