//! Decoded column views (`common::forview`) of storage `custpart`'s frame-of-reference columns, from the storage's
//! column predicates (`int_col_at`, `num_col_at`, `date_col_at`, `zone_at`) over uniform row blocks. One copy of
//! these lemmas per storage: each storage interface carries its own `common::colfmt`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::part_len;
use crate::stores::custpart::interface::common::colfmt as cf;
use crate::stores::custpart::interface::common::read as rd;
use crate::agent::common::forview::*;

verus! {

/// The base part of a FOR column over uniform blocks of `bs` rows has a base for every block.
proof fn lemma_bases(tp: Seq<PartView>, gp: int, bp: int, n: int, bs: int)
    requires
        cf::groups_part_ok(tp[gp], n, bs),
        part_len(tp[bp]) == cf::gs_at(tp, gp).len() - 1,
    ensures part_len(tp[bp]) * bs >= n,
{
    cf::lemma_uniform_groups(tp[gp], n, bs);
    cf::lemma_nblocks(n, bs);
}

/// A bigint column with U32 codes and I64 bases.
pub proof fn lemma_int32(tp: Seq<PartView>, gp: int, cp: int, bp: int, rows: Seq<Row>, c: int, bs: int)
    requires
        cf::int_col_at(tp, gp, cp, bp, rows, c),
        cf::groups_part_ok(tp[gp], rows.len() as int, bs),
        tp[cp] is U32,
        forall|j: int| 0 <= j < rows.len() ==> (#[trigger] rows[j][c]) is Int
            && i64::MIN <= rows[j][c]->Int_0 <= i64::MAX,
    ensures
        col32_ok(cf::u32s(tp[cp]), cf::i64s(tp[bp]), bs, rows.len() as int),
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][c] == Val::Int(fv32(cf::u32s(tp[cp]), cf::i64s(tp[bp]), bs, j)),
{
    let n = rows.len() as int;
    assert forall|j: int| 0 <= j < n implies #[trigger] rows[j][c] == Val::Int(fv32(cf::u32s(tp[cp]), cf::i64s(tp[bp]), bs, j)) by {
        rd::lemma_for_row(tp[gp], n, bs, tp[bp], tp[cp], j);
    }
    lemma_bases(tp, gp, bp, n, bs);
    assert forall|j: int| 0 <= j < n implies i64::MIN <= #[trigger] fv32(cf::u32s(tp[cp]), cf::i64s(tp[bp]), bs, j) <= i64::MAX by {
        assert(rows[j][c] == Val::Int(fv32(cf::u32s(tp[cp]), cf::i64s(tp[bp]), bs, j)));
    }
}

/// A bigint column with U8 codes and I64 bases.
pub proof fn lemma_int8(tp: Seq<PartView>, gp: int, cp: int, bp: int, rows: Seq<Row>, c: int, bs: int)
    requires
        cf::int_col_at(tp, gp, cp, bp, rows, c),
        cf::groups_part_ok(tp[gp], rows.len() as int, bs),
        tp[cp] is U8,
        forall|j: int| 0 <= j < rows.len() ==> (#[trigger] rows[j][c]) is Int
            && i64::MIN <= rows[j][c]->Int_0 <= i64::MAX,
    ensures
        col8_ok(cf::u8s(tp[cp]), cf::i64s(tp[bp]), bs, rows.len() as int),
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][c] == Val::Int(fv8(cf::u8s(tp[cp]), cf::i64s(tp[bp]), bs, j)),
{
    let n = rows.len() as int;
    assert forall|j: int| 0 <= j < n implies #[trigger] rows[j][c] == Val::Int(fv8(cf::u8s(tp[cp]), cf::i64s(tp[bp]), bs, j)) by {
        rd::lemma_for_row(tp[gp], n, bs, tp[bp], tp[cp], j);
    }
    lemma_bases(tp, gp, bp, n, bs);
    assert forall|j: int| 0 <= j < n implies i64::MIN <= #[trigger] fv8(cf::u8s(tp[cp]), cf::i64s(tp[bp]), bs, j) <= i64::MAX by {
        assert(rows[j][c] == Val::Int(fv8(cf::u8s(tp[cp]), cf::i64s(tp[bp]), bs, j)));
    }
}

/// A numeric(15, 2) column with U32 codes and I64 bases.
pub proof fn lemma_num32(tp: Seq<PartView>, gp: int, cp: int, bp: int, rows: Seq<Row>, c: int, bs: int)
    requires
        cf::num_col_at(tp, gp, cp, bp, rows, c, 2),
        cf::groups_part_ok(tp[gp], rows.len() as int, bs),
        tp[cp] is U32,
        forall|j: int| 0 <= j < rows.len() ==> abs((#[trigger] rows[j][c])->Num_coeff) < pow10(15),
    ensures
        col32_ok(cf::u32s(tp[cp]), cf::i64s(tp[bp]), bs, rows.len() as int),
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][c]
            == (Val::Num { coeff: fv32(cf::u32s(tp[cp]), cf::i64s(tp[bp]), bs, j), scale: 2 }),
        forall|j: int| 0 <= j < rows.len() ==> abs(#[trigger] fv32(cf::u32s(tp[cp]), cf::i64s(tp[bp]), bs, j)) < pow10(15),
{
    let n = rows.len() as int;
    assert(pow10(15) == 1000000000000000) by (compute);
    assert forall|j: int| 0 <= j < n implies #[trigger] rows[j][c]
        == (Val::Num { coeff: fv32(cf::u32s(tp[cp]), cf::i64s(tp[bp]), bs, j), scale: 2 }) by {
        rd::lemma_for_row(tp[gp], n, bs, tp[bp], tp[cp], j);
    }
    lemma_bases(tp, gp, bp, n, bs);
    assert forall|j: int| 0 <= j < n implies abs(#[trigger] fv32(cf::u32s(tp[cp]), cf::i64s(tp[bp]), bs, j)) < pow10(15) by {
        assert(rows[j][c] == (Val::Num { coeff: fv32(cf::u32s(tp[cp]), cf::i64s(tp[bp]), bs, j), scale: 2 }));
    }
}

/// A numeric(15, 2) column with U8 codes and I64 bases.
pub proof fn lemma_num8(tp: Seq<PartView>, gp: int, cp: int, bp: int, rows: Seq<Row>, c: int, bs: int)
    requires
        cf::num_col_at(tp, gp, cp, bp, rows, c, 2),
        cf::groups_part_ok(tp[gp], rows.len() as int, bs),
        tp[cp] is U8,
        forall|j: int| 0 <= j < rows.len() ==> abs((#[trigger] rows[j][c])->Num_coeff) < pow10(15),
    ensures
        col8_ok(cf::u8s(tp[cp]), cf::i64s(tp[bp]), bs, rows.len() as int),
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][c]
            == (Val::Num { coeff: fv8(cf::u8s(tp[cp]), cf::i64s(tp[bp]), bs, j), scale: 2 }),
        forall|j: int| 0 <= j < rows.len() ==> abs(#[trigger] fv8(cf::u8s(tp[cp]), cf::i64s(tp[bp]), bs, j)) < pow10(15),
{
    let n = rows.len() as int;
    assert(pow10(15) == 1000000000000000) by (compute);
    assert forall|j: int| 0 <= j < n implies #[trigger] rows[j][c]
        == (Val::Num { coeff: fv8(cf::u8s(tp[cp]), cf::i64s(tp[bp]), bs, j), scale: 2 }) by {
        rd::lemma_for_row(tp[gp], n, bs, tp[bp], tp[cp], j);
    }
    lemma_bases(tp, gp, bp, n, bs);
    assert forall|j: int| 0 <= j < n implies abs(#[trigger] fv8(cf::u8s(tp[cp]), cf::i64s(tp[bp]), bs, j)) < pow10(15) by {
        assert(rows[j][c] == (Val::Num { coeff: fv8(cf::u8s(tp[cp]), cf::i64s(tp[bp]), bs, j), scale: 2 }));
    }
}

/// A date column with U16 codes and I64 bases.
pub proof fn lemma_date16(tp: Seq<PartView>, gp: int, cp: int, bp: int, rows: Seq<Row>, c: int, bs: int)
    requires
        cf::date_col_at(tp, gp, cp, bp, rows, c),
        cf::groups_part_ok(tp[gp], rows.len() as int, bs),
        tp[cp] is U16,
        forall|j: int| 0 <= j < rows.len() ==> i64::MIN <= (#[trigger] rows[j][c])->Date_0 <= i64::MAX,
    ensures
        col16_ok(cf_u16s(tp[cp]), cf::i64s(tp[bp]), bs, rows.len() as int),
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][c] == Val::Date(fv16(cf_u16s(tp[cp]), cf::i64s(tp[bp]), bs, j)),
{
    let n = rows.len() as int;
    assert forall|j: int| 0 <= j < n implies #[trigger] rows[j][c] == Val::Date(fv16(cf_u16s(tp[cp]), cf::i64s(tp[bp]), bs, j)) by {
        rd::lemma_for_row(tp[gp], n, bs, tp[bp], tp[cp], j);
    }
    lemma_bases(tp, gp, bp, n, bs);
    assert forall|j: int| 0 <= j < n implies i64::MIN <= #[trigger] fv16(cf_u16s(tp[cp]), cf::i64s(tp[bp]), bs, j) <= i64::MAX by {
        assert(rows[j][c] == Val::Date(fv16(cf_u16s(tp[cp]), cf::i64s(tp[bp]), bs, j)));
    }
}

/// The values of a U16 part (empty for another kind).
pub open spec fn cf_u16s(p: PartView) -> Seq<u16> {
    match p {
        PartView::U16(s) => s,
        _ => Seq::empty(),
    }
}

/// A zone map over a U16 FOR column: every row's value lies between its block's base and maximum.
pub proof fn lemma_zone16(tp: Seq<PartView>, gp: int, cp: int, bp: int, zp: int, n: int, bs: int)
    requires
        cf::zone_at(tp, gp, cp, bp, zp),
        cf::groups_part_ok(tp[gp], n, bs),
        cf::for_shape(cf::gs_at(tp, gp), tp[bp], tp[cp], n),
        tp[cp] is U16, tp[bp] is I64,
    ensures
        cf::i64s(tp[zp]).len() == part_len(tp[bp]),
        forall|j: int| 0 <= j < n ==> cf::i64s(tp[bp])[j / bs] <= #[trigger] fv16(cf_u16s(tp[cp]), cf::i64s(tp[bp]), bs, j)
            <= cf::i64s(tp[zp])[j / bs],
{
    assert forall|j: int| 0 <= j < n implies cf::i64s(tp[bp])[j / bs] <= #[trigger] fv16(cf_u16s(tp[cp]), cf::i64s(tp[bp]), bs, j)
        <= cf::i64s(tp[zp])[j / bs] by {
        rd::lemma_for_row(tp[gp], n, bs, tp[bp], tp[cp], j);
        assert(cf::in_group(cf::gs_at(tp, gp), j / bs, j));
    }
}

} // verus!
