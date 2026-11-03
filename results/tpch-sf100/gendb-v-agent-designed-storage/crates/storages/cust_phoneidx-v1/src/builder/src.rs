//! What the builder reads from storage `custpart` (customer, canonical row order), stated with this storage's
//! interface definitions over the source parts `cp`: for a database bound to the source, the c_phone column shape
//! and the value of every row (`src_ok`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::sources::StoresView;
use crate::gendb_entry::sources_bound;
use crate::spec::value::{Database, Row, Val};
use crate::link::source::lemma_proj_all_index;
use crate::stores::custpart::interface as C;
use crate::stores::custpart::interface::common::colfmt as CF;
use crate::stores::custpart::declaration as CD;
use crate::stores::cust_phoneidx::declaration as D;
use crate::stores::cust_phoneidx::interface::*;

verus! {

/// Everything the builder uses about the source parts `cp` and this storage's relation `rel`.
pub open spec fn src_ok(cp: Seq<PartView>, rel: Seq<Row>) -> bool {
    let n = rel.len() as int;
    &&& cp.len() == CUSTPART_PARTS
    &&& cp[CU_PHONE_OFFS as int] is U64 && phone_offs(cp).len() == n + 1
    &&& cp[CU_PHONE_BYTES as int] is U8
    &&& forall|r: int| 0 <= r < n ==> #[trigger] phone_range_ok(cp, r)
    &&& rows_ok(cp, rel)
}

/// For a database bound to `custpart`, its parts and this storage's relation meet `src_ok`.
pub proof fn lemma_src(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures src_ok(sv.custpart, D::stored_relations(db)[0]),
{
    let cp = sv.custpart;
    let crels = CD::stored_relations(db);
    assert(C::represents(cp, crels));
    let tp = cp.subrange(C::CUSTOMER_FIRST as int, (C::CUSTOMER_FIRST + C::CU_PARTS) as int);
    assert(C::customer_ok(tp, crels[0]));
    assert(CF::text_col_at(tp, C::CU_PHONE_OFFS as int, C::CU_PHONE_BYTES as int, crels[0], 4));
    assert(tp[10] == cp[10]);
    assert(tp[11] == cp[11]);
    let t2 = db.tables[2];
    let rel = D::stored_relations(db)[0];
    lemma_proj_all_index(t2, CD::stored_cols_t0());
    lemma_proj_all_index(t2, D::stored_cols_t0());
    let n = rel.len() as int;
    assert(n == crels[0].len());
    let (o, y) = (phone_offs(cp), phone_bytes(cp));
    assert(o == CF::u64s(tp[10]) && y == CF::u8s(tp[11]));
    assert forall|r: int| 0 <= r < n implies #[trigger] phone_range_ok(cp, r) by {
        assert(CF::text_range_ok(o, y, r));
    }
    assert forall|r: int| 0 <= r < n implies #[trigger] rel[r] == cu_row(phone_at(cp, r)) by {
        assert(crels[0][r][4] == Val::Text(CF::text_of(o, y, r)));
        assert(CD::stored_cols_t0()[4] == 4);
        assert(D::stored_cols_t0()[0] == 4);
        assert(rel[r][0] == t2[r][4]);
        assert(crels[0][r][4] == t2[r][4]);
        assert(rel[r] =~= cu_row(phone_at(cp, r)));
    }
}

} // verus!
