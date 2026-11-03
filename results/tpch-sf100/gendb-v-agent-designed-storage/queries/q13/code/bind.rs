//! What the four storages give about a bound database (`bound_db`), in terms of the part views the query reads:
//! - `cust_ok` (custpart): customer row `i`'s c_custkey is `ckey(i) = cb[i / bs] + cc[i]`; with key flag 1 the keys
//!   are nondecreasing;
//! - `okeys_ok` (facts): with key index kind 2, canonical orders row `r` is stored row `fsrow(r)` and its o_custkey
//!   is `fokey(r)`;
//! - `text_ok` (factext_trislice): o_comment of row `r` is `text_of(offs, bytes, r)`, its signature words are at
//!   `sig[2 r]`, `sig[2 r + 1]`, and the bit-sliced parts 13, 14 hold the same bits (`slices_ok`);
//! - `index_ok` (orders_custidx): in directory mode, entry `k - kmin` has exactly the orders rows with o_custkey
//!   `k` (`count_key`), and every key lies in the directory's range; otherwise the keys are stored per row.
use vstd::prelude::*;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::*;
use crate::link::query::proj_all;
use crate::link::expr::ival;
use crate::link::source::lemma_proj_all_index;
use crate::stores::custpart::interface as CP;
use crate::stores::custpart::interface::common::colfmt as CPC;
use crate::stores::custpart::interface::common::keyidx as CPK;
use crate::stores::facts::interface as FA;
use crate::stores::facts::interface::common::colfmt as FAC;
use crate::stores::facts::interface::common::keyidx as FAK;
use crate::stores::factext_trislice::interface as TX;
use crate::stores::factext_trislice::interface::common::colfmt as TXC;
use crate::stores::factext_trislice::interface::trisig::sig_of;
use crate::stores::orders_custidx::interface as IX;
use super::sql::*;
use super::count::ckey;

verus! {

// ------------------------------------------------------------------------------------------------ customer

/// Customer row `i`'s key is in the key column at `ckey(i)`.
pub open spec fn crow_ok(p: Seq<PartView>, db: Database, i: int) -> bool {
    let bs = CPC::u64s(p[0])[1] as int;
    &&& (i / bs) < CPC::i64s(p[3]).len()
    &&& ctab(db)[i][0] == Val::Int(ckey(CPC::u32s(p[2]), CPC::i64s(p[3]), bs, i))
}

/// custpart: the customer key column (FOR codes `p[2]`, bases `p[3]`, groups of `p[0][1]` rows) and its key flag.
pub open spec fn cust_ok(p: Seq<PartView>, db: Database) -> bool {
    let n = ctab(db).len() as int;
    let bs = CPC::u64s(p[0])[1] as int;
    let (cc, cb) = (CPC::u32s(p[2]), CPC::i64s(p[3]));
    &&& p.len() == CP::CUSTPART_PARTS
    &&& p[0] is U64 && CPC::u64s(p[0]).len() == 2 && CPC::u64s(p[0])[0] == n
    &&& bs >= 1
    &&& p[2] is U32 && p[3] is I64 && cc.len() == n
    &&& p[20] is U64 && CPC::u64s(p[20]).len() == 1
    &&& forall|i: int| 0 <= i < n ==> #[trigger] crow_ok(p, db, i)
    &&& CPC::u64s(p[20])[0] == 1 ==> forall|i: int| 0 <= i < n - 1 ==> #[trigger] ckey(cc, cb, bs, i) <= ckey(cc, cb, bs, i + 1)
}

/// `j / b < nblocks(n, b)` for `j < n`.
proof fn lemma_div_lt_blocks(j: int, n: int, b: int)
    requires 0 <= j < n, b >= 1,
    ensures j / b < (n + b - 1) / b,
{
    assert(j / b <= (n - 1) / b) by (nonlinear_arith) requires 0 <= j <= n - 1, b >= 1;
    assert((n - 1) / b < (n + b - 1) / b) by (nonlinear_arith) requires n >= 1, b >= 1;
}

/// The customer facts the query uses, out of custpart's `customer_ok`.
pub open spec fn cust_cols(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& CP::table_layout_ok(tp, rel.len() as int)
    &&& CPC::int_col_at(tp, CP::CU_GROUPS as int, CP::CU_CUSTKEY_CODES as int, CP::CU_CUSTKEY_BASE as int, rel, 0)
    &&& tp[CP::CU_CUSTKEY_CODES as int] is U32
    &&& tp[CP::CU_KEYIDX_KIND as int] is U64 && CPC::u64s(tp[CP::CU_KEYIDX_KIND as int]).len() == 1
    &&& CPK::keyidx_ok(CPC::u32s(tp[CP::CU_CUSTKEY_CODES as int]), CPC::i64s(tp[CP::CU_CUSTKEY_BASE as int]),
            Seq::<u32>::empty(), Seq::<u64>::empty(), CPC::u64s(tp[CP::CU_LAYOUT as int])[1] as int,
            CPC::u64s(tp[CP::CU_KEYIDX_KIND as int])[0], rel.len() as int)
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
    hide(CPC::int_col_at);
    hide(CPC::text_col_at);
    hide(CPC::dict_col_at);
    hide(CPC::num_col_at);
    hide(CPK::keyidx_ok);
    hide(CP::table_layout_ok);
}

/// A customer key value through custpart's reader lemma (in its own context, away from the group quantifiers).
proof fn lemma_cust_row(gp: PartView, base: PartView, codes: PartView, n: int, bs: int, i: int)
    requires CPC::groups_part_ok(gp, n, bs), 0 <= i < n, base is I64, codes is U32,
    ensures CPC::for_at(CPC::u64s(gp), base, codes, i) == ckey(CPC::u32s(codes), CPC::i64s(base), bs, i),
{
    crate::stores::custpart::interface::common::read::lemma_for_row(gp, n, bs, base, codes, i);
}

/// custpart's `represents` gives `cust_ok`.
pub proof fn lemma_cust(p: Seq<PartView>, db: Database)
    requires CP::represents(p, crate::stores::custpart::declaration::stored_relations(db)),
    ensures cust_ok(p, db),
{
    hide(CP::represents);
    lemma_cust_table(p, db);
    let rels = crate::stores::custpart::declaration::stored_relations(db);
    let tp = p.subrange(CP::CUSTOMER_FIRST as int, (CP::CUSTOMER_FIRST + CP::CU_PARTS) as int);
    let rel = rels[0];
    lemma_proj_all_index(db.tables[2], crate::stores::custpart::declaration::stored_cols_t0());
    let n = ctab(db).len() as int;
    assert(rel.len() == n);
    assert(tp[0] == p[0] && tp[1] == p[1] && tp[2] == p[2] && tp[3] == p[3] && tp[20] == p[20]);
    let bs = CPC::u64s(p[0])[1] as int;
    let (cc, cb) = (CPC::u32s(p[2]), CPC::i64s(p[3]));
    let gs = CPC::u64s(p[1]);
    assert(CPC::groups_part_ok(p[1], n, bs));
    assert(CPC::int_col_at(tp, CP::CU_GROUPS as int, CP::CU_CUSTKEY_CODES as int, CP::CU_CUSTKEY_BASE as int, rel, 0));
    assert(gs == CPC::uniform_gs(n, bs));
    assert(cb.len() == CPC::nblocks_of(n, bs));
    assert forall|i: int| 0 <= i < n implies #[trigger] crow_ok(p, db, i) by {
        lemma_cust_row(p[1], p[3], p[2], n, bs, i);
        lemma_div_lt_blocks(i, n, bs);
        assert((i / bs) < cb.len());
        assert(CPC::for_at(gs, p[3], p[2], i) == ckey(cc, cb, bs, i));
        assert(rel[i][0] == Val::Int(CPC::for_at(gs, p[3], p[2], i)));
        assert(rel[i][0] == db.tables[2][i][0]);
    }
    let kind = CPC::u64s(p[20])[0];
    assert(CPK::keyidx_ok(cc, cb, Seq::<u32>::empty(), Seq::<u64>::empty(), bs, kind, n));
    if kind == 1 {
        assert forall|i: int| 0 <= i < n - 1 implies #[trigger] ckey(cc, cb, bs, i) <= ckey(cc, cb, bs, i + 1) by {
            assert(CPK::sorted_at(cc, cb, Seq::<u32>::empty(), Seq::<u64>::empty(), bs, kind, i));
            assert(CPK::irow(kind, Seq::<u32>::empty(), Seq::<u64>::empty(), bs, i) == i);
            assert(CPK::irow(kind, Seq::<u32>::empty(), Seq::<u64>::empty(), bs, i + 1) == i + 1);
            assert(CPK::fkey(cc, cb, bs, i) == ckey(cc, cb, bs, i));
            assert(CPK::fkey(cc, cb, bs, i + 1) == ckey(cc, cb, bs, i + 1));
        }
    }
    assert(p.len() == CP::CUSTPART_PARTS);
    assert(p[0] is U64 && CPC::u64s(p[0]).len() == 2 && CPC::u64s(p[0])[0] == n);
    assert(bs >= 1);
    assert(p[2] is U32 && p[3] is I64 && cc.len() == n);
    assert(p[20] is U64 && CPC::u64s(p[20]).len() == 1);
}

// ------------------------------------------------------------------------------------------------ orders keys

/// Stored row of canonical orders row `r` under the key index (`ib[r / bs] + ic[r]`).
pub open spec fn fsrow(ic: Seq<u32>, ib: Seq<u64>, bs: int, r: int) -> int {
    ib[r / bs] + ic[r]
}

/// o_custkey of canonical orders row `r` through the key index.
pub open spec fn fokey(ic: Seq<u32>, ib: Seq<u64>, kc: Seq<u32>, kb: Seq<i64>, bs: int, r: int) -> int {
    kb[fsrow(ic, ib, bs, r) / bs] + kc[fsrow(ic, ib, bs, r)]
}

/// facts: the orders frame, o_custkey column and key index; with kind 2, the key of every canonical row.
pub open spec fn okeys_ok(p: Seq<PartView>, db: Database) -> bool {
    let n = otab(db).len() as int;
    let bs = FAC::u64s(p[48])[1] as int;
    let (ic, ib, kc, kb) = (FAC::u32s(p[71]), FAC::u64s(p[72]), FAC::u32s(p[54]), FAC::i64s(p[55]));
    &&& p.len() == FA::FACTS_PARTS
    &&& p[48] is U64 && FAC::u64s(p[48]).len() == 2 && FAC::u64s(p[48])[0] == n
    &&& bs >= 1
    &&& p[54] is U32 && p[55] is I64 && p[71] is U32 && p[72] is U64
    &&& p[73] is U64 && FAC::u64s(p[73]).len() == 1
    &&& kc.len() == n
    &&& FAC::u64s(p[73])[0] == 2 ==> {
            &&& ic.len() == n
            &&& forall|r: int| 0 <= r < n ==> #[trigger] orow_ok(p, db, r)
        }
}

/// Canonical orders row `r`: its stored row and o_custkey through the key index.
pub open spec fn orow_ok(p: Seq<PartView>, db: Database, r: int) -> bool {
    let n = otab(db).len() as int;
    let bs = FAC::u64s(p[48])[1] as int;
    let (ic, ib, kc, kb) = (FAC::u32s(p[71]), FAC::u64s(p[72]), FAC::u32s(p[54]), FAC::i64s(p[55]));
    &&& (r / bs) < ib.len()
    &&& 0 <= fsrow(ic, ib, bs, r) < n
    &&& fsrow(ic, ib, bs, r) / bs < kb.len()
    &&& otab(db)[r][1] == Val::Int(fokey(ic, ib, kc, kb, bs, r))
    &&& i64::MIN <= fokey(ic, ib, kc, kb, bs, r) <= i64::MAX
}

/// `r / b < m` when `m * b >= n` and `r < n`.
proof fn lemma_div_lt_len(r: int, n: int, b: int, m: int)
    requires 0 <= r < n, b >= 1, m * b >= n,
    ensures r / b < m,
{
    assert(r / b < m) by (nonlinear_arith) requires 0 <= r < n, b >= 1, m * b >= n;
}

/// The orders facts the query uses, out of facts' `orders_ok`.
pub open spec fn orders_cols(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    let n = rel.len() as int;
    let rows = FA::orders_rows(tp, rel);
    let kind = FAC::u64s(tp[FA::OR_KEYIDX_KIND as int])[0];
    let bs = FAC::u64s(tp[FA::OR_LAYOUT as int])[1] as int;
    let (ic, ib) = (FAC::u32s(tp[FA::OR_KEYIDX_CODES as int]), FAC::u64s(tp[FA::OR_KEYIDX_BASE as int]));
    &&& tp.len() == FA::OR_PARTS
    &&& FA::table_layout_ok(tp, n)
    &&& FAC::perm_col_at(tp, FA::OR_GROUPS as int, FA::OR_PERM_CODES as int, FA::OR_PERM_BASE as int, n)
    &&& tp[FA::OR_CUSTKEY_CODES as int] is U32
    &&& FAC::int_col_at(tp, FA::OR_GROUPS as int, FA::OR_CUSTKEY_CODES as int, FA::OR_CUSTKEY_BASE as int, rows, 1)
    &&& tp[FA::OR_KEYIDX_CODES as int] is U32 && tp[FA::OR_KEYIDX_BASE as int] is U64
    &&& tp[FA::OR_KEYIDX_KIND as int] is U64 && FAC::u64s(tp[FA::OR_KEYIDX_KIND as int]).len() == 1
    &&& FAK::keyidx_ok(FAC::u32s(tp[FA::OR_ORDERKEY_CODES as int]), FAC::i64s(tp[FA::OR_ORDERKEY_BASE as int]), ic, ib, bs, kind, n)
    &&& kind == 2 ==> forall|r: int| 0 <= r < n ==> #[trigger] FA::orders_map(tp, n)[FAK::fidx(ic, ib, bs, r)] == r
}

/// The orders table of facts' `represents`.
proof fn lemma_orders_table(p: Seq<PartView>, db: Database)
    requires FA::represents(p, crate::stores::facts::declaration::stored_relations(db)),
    ensures
        orders_cols(p.subrange(FA::ORDERS_FIRST as int, (FA::ORDERS_FIRST + FA::OR_PARTS) as int),
            crate::stores::facts::declaration::stored_relations(db)[1]),
        p.len() == FA::FACTS_PARTS,
{
    hide(FA::lineitem_ok);
    hide(FAC::int_col_at);
    hide(FAC::dict_col_at);
    hide(FAC::num_col_at);
    hide(FAC::date_col_at);
    hide(FAC::zone_at);
    hide(FAC::perm_col_at);
    hide(FAK::keyidx_ok);
    hide(FA::table_layout_ok);
    hide(crate::stores::facts::interface::cluster::clustered);
    let tp = p.subrange(FA::ORDERS_FIRST as int, (FA::ORDERS_FIRST + FA::OR_PARTS) as int);
    let rel = crate::stores::facts::declaration::stored_relations(db)[1];
    assert(FA::orders_ok(tp, rel));
    assert(FA::orders_rows(tp, rel).len() == rel.len());
}

/// An o_custkey value through facts' reader lemma (in its own context, away from the group quantifiers).
proof fn lemma_orders_row(gp: PartView, base: PartView, codes: PartView, n: int, bs: int, s: int)
    requires FAC::groups_part_ok(gp, n, bs), 0 <= s < n, base is I64, codes is U32,
    ensures FAC::for_at(FAC::u64s(gp), base, codes, s) == FAC::i64s(base)[s / bs] + FAC::u32s(codes)[s],
{
    crate::stores::facts::interface::common::read::lemma_for_row(gp, n, bs, base, codes, s);
}

/// facts' `represents` gives `okeys_ok`.
pub proof fn lemma_okeys(p: Seq<PartView>, db: Database)
    requires
        FA::represents(p, crate::stores::facts::declaration::stored_relations(db)),
        db_facts(db),
    ensures okeys_ok(p, db),
{
    hide(FA::represents);
    hide(FA::orders_ok);
    let rels = crate::stores::facts::declaration::stored_relations(db);
    lemma_orders_table(p, db);
    let tp = p.subrange(FA::ORDERS_FIRST as int, (FA::ORDERS_FIRST + FA::OR_PARTS) as int);
    let rel = rels[1];
    lemma_proj_all_index(db.tables[1], crate::stores::facts::declaration::stored_cols_t1());
    let n = otab(db).len() as int;
    assert(rel.len() == n);
    assert(tp[0] == p[48] && tp[1] == p[49] && tp[2] == p[50] && tp[3] == p[51]);
    assert(tp[6] == p[54] && tp[7] == p[55] && tp[23] == p[71] && tp[24] == p[72] && tp[25] == p[73]);
    let bs = FAC::u64s(p[48])[1] as int;
    let (ic, ib, kc, kb) = (FAC::u32s(p[71]), FAC::u64s(p[72]), FAC::u32s(p[54]), FAC::i64s(p[55]));
    let gs = FAC::u64s(p[49]);
    assert(FAC::groups_part_ok(p[49], n, bs));
    assert(gs == FAC::uniform_gs(n, bs));
    let rows = FA::orders_rows(tp, rel);
    assert(kb.len() == FAC::nblocks_of(n, bs));
    if FAC::u64s(p[73])[0] == 2 {
        let kind = FAC::u64s(p[73])[0];
        assert forall|r: int| 0 <= r < n implies #[trigger] orow_ok(p, db, r) by {
            lemma_div_lt_len(r, n, bs, ib.len() as int);
            let s = fsrow(ic, ib, bs, r);
            assert(s == FAK::fidx(ic, ib, bs, r));
            assert(FAK::idx_map(ic, ib, bs, n)[r] == s);
            assert(0 <= s < n);
            assert(FA::orders_map(tp, n)[s] == r);
            lemma_orders_row(p[49], p[55], p[54], n, bs, s);
            lemma_div_lt_blocks(s, n, bs);
            assert(rows[s] == rel[r]);
            assert(rows[s][1] == Val::Int(FAC::for_at(gs, p[55], p[54], s)));
            assert(rel[r][1] == db.tables[1][r][1]);
            assert(i64::MIN <= ival(otab(db)[r][1]) <= i64::MAX);
        }
    }
}

// ------------------------------------------------------------------------------------------------ text

/// factext_trislice: the o_comment text, signatures and bit-sliced signatures of every orders row.
pub open spec fn text_ok(p: Seq<PartView>, db: Database) -> bool {
    let n = otab(db).len() as int;
    let (sig, offs, bytes) = (TXC::u64s(p[12]), TXC::u64s(p[10]), TXC::u8s(p[11]));
    &&& p.len() == TX::FACTEXT_TRISLICE_PARTS
    &&& p[10] is U64 && p[11] is U8 && p[12] is U64
    &&& TX::slices_ok(p, n)
    &&& sig.len() == 2 * n
    &&& offs.len() == n + 1
    &&& forall|r: int| 0 <= r < n ==> #[trigger] offs[r] <= offs[r + 1] && offs[r + 1] <= bytes.len()
    &&& forall|r: int| 0 <= r < n ==> {
            &&& otext(otab(db)[r]) == #[trigger] TXC::text_of(offs, bytes, r)
            &&& sig[2 * r] == sig_of(TXC::text_of(offs, bytes, r), 0)
            &&& sig[2 * r + 1] == sig_of(TXC::text_of(offs, bytes, r), 1)
        }
}

/// factext_trislice's `represents` gives `text_ok`.
pub proof fn lemma_text(p: Seq<PartView>, db: Database)
    requires TX::represents(p, crate::stores::factext_trislice::declaration::stored_relations(db)),
    ensures text_ok(p, db),
{
    let rels = crate::stores::factext_trislice::declaration::stored_relations(db);
    lemma_proj_all_index(db.tables[1], crate::stores::factext_trislice::declaration::stored_cols_t1());
    let n = otab(db).len() as int;
    assert(rels[1].len() == n);
    let (offs, bytes) = (TXC::u64s(p[10]), TXC::u8s(p[11]));
    let base = p.subrange(0, TX::FACTEXT_PARTS as int);
    assert(TX::base_represents(base, rels));
    let tp = base.subrange(TX::ORDERS_FIRST as int, (TX::ORDERS_FIRST + TX::OT_PARTS) as int);
    assert(TX::orders_ok(tp, rels[1]));
    assert(tp[TX::OT_COMMENT_OFFS as int] == p[10] && tp[TX::OT_COMMENT_BYTES as int] == p[11]);
    assert(TXC::text_parts_wf(offs, bytes, n));
    assert forall|r: int| 0 <= r < n implies #[trigger] offs[r] <= offs[r + 1] && offs[r + 1] <= bytes.len() by {
        assert(TXC::text_range_ok(offs, bytes, r));
    }
    assert forall|r: int| 0 <= r < n implies {
        &&& otext(otab(db)[r]) == #[trigger] TXC::text_of(offs, bytes, r)
        &&& TXC::u64s(p[12])[2 * r] == sig_of(TXC::text_of(offs, bytes, r), 0)
        &&& TXC::u64s(p[12])[2 * r + 1] == sig_of(TXC::text_of(offs, bytes, r), 1)
    } by {
        TX::lemma_comment_sig(p, rels, r);
        assert(rels[1][r][1] == db.tables[1][r][8]);
    }
    assert(TX::slices_ok(p, rels[1].len() as int));
}

// ------------------------------------------------------------------------------------------------ index

/// The indexed relation: o_custkey of every orders row.
pub open spec fn idxrel(db: Database) -> Seq<Row> {
    crate::stores::orders_custidx::declaration::stored_relations(db)[0]
}

/// orders_custidx: the directory (mode 1) or the keys per row (any other mode).
pub open spec fn index_ok(p: Seq<PartView>, db: Database) -> bool {
    let n = otab(db).len() as int;
    let meta = IX::idx_i64s(p[0]);
    let offs = IX::idx_u32s(p[1]);
    let keys = IX::idx_i64s(p[3]);
    &&& p.len() == IX::CUSTIDX_PARTS
    &&& p[0] is I64 && p[1] is U32 && p[2] is U32 && p[3] is I64
    &&& meta.len() == 2
    &&& idxrel(db).len() == n
    &&& forall|r: int| 0 <= r < n ==> #[trigger] idxrel(db)[r][0] == otab(db)[r][1]
    &&& meta[0] == IX::MODE_DIRECTORY ==> {
            &&& offs.len() >= 1
            &&& IX::directory_ok(meta[1] as int, offs.len() - 1, offs, IX::idx_u32s(p[2]), idxrel(db))
        }
    &&& meta[0] != IX::MODE_DIRECTORY ==> {
            &&& keys.len() == n
            &&& forall|r: int| 0 <= r < n ==> #[trigger] otab(db)[r][1] == Val::Int(keys[r] as int)
        }
}

/// orders_custidx's `represents` gives `index_ok`.
pub proof fn lemma_index(p: Seq<PartView>, db: Database)
    requires IX::represents(p, crate::stores::orders_custidx::declaration::stored_relations(db)),
    ensures index_ok(p, db),
{
    let rels = crate::stores::orders_custidx::declaration::stored_relations(db);
    lemma_proj_all_index(db.tables[1], crate::stores::orders_custidx::declaration::stored_cols_t0());
    let n = otab(db).len() as int;
    assert forall|r: int| 0 <= r < n implies #[trigger] idxrel(db)[r][0] == otab(db)[r][1] by {
        assert(idxrel(db)[r][0] == db.tables[1][r][1]);
    }
    if IX::idx_i64s(p[0])[0] != IX::MODE_DIRECTORY {
        assert forall|r: int| 0 <= r < n implies #[trigger] otab(db)[r][1] == Val::Int(IX::idx_i64s(p[3])[r] as int) by {
            assert(rels[0][r][0] == Val::Int(IX::idx_i64s(p[3])[r] as int));
        }
    }
}

/// Everything the query reads, for a bound database.
pub open spec fn bind_ok(sv: StoresView, db: Database) -> bool {
    &&& db_facts(db)
    &&& cust_ok(sv.custpart, db)
    &&& okeys_ok(sv.facts, db)
    &&& text_ok(sv.factext_trislice, db)
    &&& index_ok(sv.orders_custidx, db)
}

/// A bound database meets `bind_ok`.
pub proof fn lemma_bind(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures bind_ok(sv, db),
{
    lemma_db_facts(db);
    lemma_cust(sv.custpart, db);
    lemma_okeys(sv.facts, db);
    lemma_text(sv.factext_trislice, db);
    lemma_index(sv.orders_custidx, db);
}

/// The part kinds and lengths the query reads (from `bind_ok`, without its per-row facts).
pub open spec fn shape_ok(sv: StoresView, db: Database) -> bool {
    let (pc, pf, pt, pi) = (sv.custpart, sv.facts, sv.factext_trislice, sv.orders_custidx);
    let n = otab(db).len() as int;
    let m = ctab(db).len() as int;
    &&& pc.len() == CP::CUSTPART_PARTS && pc[0] is U64 && CPC::u64s(pc[0]).len() == 2 && CPC::u64s(pc[0])[1] >= 1
    &&& pc[2] is U32 && pc[3] is I64 && CPC::u32s(pc[2]).len() == m && pc[20] is U64 && CPC::u64s(pc[20]).len() == 1
    &&& pf.len() == FA::FACTS_PARTS && pf[48] is U64 && FAC::u64s(pf[48]).len() == 2 && FAC::u64s(pf[48])[1] >= 1
    &&& pf[54] is U32 && pf[55] is I64 && pf[71] is U32 && pf[72] is U64 && pf[73] is U64 && FAC::u64s(pf[73]).len() == 1
    &&& pt.len() == TX::FACTEXT_TRISLICE_PARTS && pt[10] is U64 && pt[11] is U8 && pt[12] is U64
    &&& TXC::u64s(pt[12]).len() == 2 * n && TXC::u64s(pt[10]).len() == n + 1
    &&& pi.len() == IX::CUSTIDX_PARTS && pi[0] is I64 && pi[1] is U32 && pi[2] is U32 && pi[3] is I64
    &&& IX::idx_i64s(pi[0]).len() == 2
}

/// `bind_ok` gives `shape_ok`.
pub proof fn lemma_shape(sv: StoresView, db: Database)
    requires bind_ok(sv, db),
    ensures shape_ok(sv, db), db_facts(db),
{
}

/// What the directory inversion needs (`canon_keys`).
pub open spec fn canon_pre(p: Seq<PartView>, db: Database) -> bool {
    let rel = idxrel(db);
    let n = otab(db).len() as int;
    let dir = IX::idx_i64s(p[0])[0] == IX::MODE_DIRECTORY;
    let offs = IX::idx_u32s(p[1]);
    let keys0 = IX::idx_i64s(p[3]);
    &&& rel.len() == n
    &&& forall|r: int| 0 <= r < n ==> (#[trigger] rel[r][0]) is Int && i64::MIN <= ival(rel[r][0]) <= i64::MAX
    &&& dir ==> offs.len() >= 1 && IX::directory_ok(IX::idx_i64s(p[0])[1] as int, offs.len() - 1, offs, IX::idx_u32s(p[2]), rel)
    &&& !dir ==> keys0.len() == n && forall|r: int| 0 <= r < n ==> #[trigger] rel[r][0] == Val::Int(keys0[r] as int)
}

/// `bind_ok` gives `canon_pre`.
pub proof fn lemma_canon_pre(sv: StoresView, db: Database)
    requires bind_ok(sv, db),
    ensures canon_pre(sv.orders_custidx, db),
{
    let n = otab(db).len() as int;
    assert forall|r: int| 0 <= r < n implies (#[trigger] idxrel(db)[r][0]) is Int && i64::MIN <= ival(idxrel(db)[r][0]) <= i64::MAX by {
        assert(idxrel(db)[r][0] == otab(db)[r][1]);
    }
}

} // verus!
