//! Assembly of encoded columns into stored parts: the uniform group part, base vectors as I64 or U64 parts, and
//! the lemmas that turn the encoder's per-block guarantees (`forenc::for_col_ok`) and the text copy's guarantee
//! into the interface's column predicates (`colfmt::*_col_at`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{owned_part_view, PartView};
use crate::spec::value::{Row, Val};
use crate::link::query::{text_at, TextView};
use crate::builder::iface::common::colfmt::*;
use crate::builder::common::codes::Code;
use crate::builder::common::colsrc::*;
use crate::builder::common::dict::*;
use crate::builder::common::forenc::*;

verus! {

/// The uniform group part of `n` rows in blocks of `bsize` rows.
pub fn groups_part(n: usize, bsize: usize) -> (p: OwnedPart)
    requires
        1 <= bsize,
        n + bsize <= usize::MAX,
    ensures
        groups_part_ok(owned_part_view(p), n as int, bsize as int),
{
    let nb = block_count(n, bsize);
    let mut gs: Vec<u64> = Vec::with_capacity(nb + 1);
    let mut g: usize = 0;
    while g < nb
        invariant
            1 <= bsize,
            nb == nblocks(n as int, bsize as int),
            nb > 0 ==> (nb - 1) * bsize < n,
            g <= nb,
            gs@.len() == g,
            forall|h: int| 0 <= h < g ==> #[trigger] gs@[h] == (h * bsize) as u64,
        decreases nb - g,
    {
        proof {
            assert(g * bsize <= (nb - 1) * bsize) by (nonlinear_arith) requires g <= nb - 1, bsize >= 1;
            assert(g * bsize >= 0) by (nonlinear_arith) requires g >= 0, bsize >= 1;
        }
        gs.push((g * bsize) as u64);
        g = g + 1;
    }
    gs.push(n as u64);
    proof {
        assert(nblocks_of(n as int, bsize as int) == nb);
        assert(gs@ =~= uniform_gs(n as int, bsize as int));
    }
    OwnedPart::U64(gs)
}

/// Bases of a signed column as `i64`.
pub fn bases_i64(b: &Vec<i128>) -> (v: Vec<i64>)
    requires forall|i: int| 0 <= i < b@.len() ==> i64::MIN <= #[trigger] b@[i] <= i64::MAX,
    ensures
        v@.len() == b@.len(),
        forall|i: int| 0 <= i < b@.len() ==> #[trigger] v@[i] as int == b@[i] as int,
{
    let mut v: Vec<i64> = Vec::with_capacity(b.len());
    let mut i: usize = 0;
    while i < b.len()
        invariant
            i <= b@.len(),
            v@.len() == i,
            forall|k: int| 0 <= k < b@.len() ==> i64::MIN <= #[trigger] b@[k] <= i64::MAX,
            forall|k: int| 0 <= k < i ==> #[trigger] v@[k] as int == b@[k] as int,
        decreases b@.len() - i,
    {
        v.push(b[i] as i64);
        i = i + 1;
    }
    v
}

/// Bases of a dictionary-index column as `u64`.
pub fn bases_u64(b: &Vec<i128>) -> (v: Vec<u64>)
    requires forall|i: int| 0 <= i < b@.len() ==> 0 <= #[trigger] b@[i] <= u64::MAX,
    ensures
        v@.len() == b@.len(),
        forall|i: int| 0 <= i < b@.len() ==> #[trigger] v@[i] as int == b@[i] as int,
{
    let mut v: Vec<u64> = Vec::with_capacity(b.len());
    let mut i: usize = 0;
    while i < b.len()
        invariant
            i <= b@.len(),
            v@.len() == i,
            forall|k: int| 0 <= k < b@.len() ==> 0 <= #[trigger] b@[k] <= u64::MAX,
            forall|k: int| 0 <= k < i ==> #[trigger] v@[k] as int == b@[k] as int,
        decreases b@.len() - i,
    {
        v.push(b[i] as u64);
        i = i + 1;
    }
    v
}

/// The bases and zone maxima of an encoded column lie in the range of its base kind.
pub proof fn lemma_col_ranges<C: Code>(col: ForCol<C>, src: ValSrc, rm: RowMap, n: int, bsize: int)
    requires
        for_col_ok(col, src, rm, n, bsize),
    ensures
        forall|g: int| 0 <= g < col.bases@.len() ==> in_base_range(src, #[trigger] col.bases@[g] as int),
        forall|g: int| 0 <= g < col.zmax@.len() ==> in_base_range(src, #[trigger] col.zmax@[g] as int),
{
    assert forall|g: int| 0 <= g < col.bases@.len() implies in_base_range(src, #[trigger] col.bases@[g] as int) by {
        assert(block_ok(src, rm, n, bsize, g, col.bases@[g], col.zmax@[g], col.codes@, 0));
    }
    assert forall|g: int| 0 <= g < col.zmax@.len() implies in_base_range(src, #[trigger] col.zmax@[g] as int) by {
        assert(block_ok(src, rm, n, bsize, g, col.bases@[g], col.zmax@[g], col.codes@, 0));
    }
}

/// Row `j` lies in the block `j / bsize`, which `forenc` encoded.
proof fn lemma_row_block(n: int, bsize: int, j: int) -> (g: int)
    requires
        1 <= bsize,
        0 <= j < n,
    ensures
        0 <= g < nblocks(n, bsize),
        g * bsize <= j < (g + 1) * bsize,
        blk_lo(bsize, g) <= j < blk_hi(n, bsize, g),
{
    let g = j / bsize;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, bsize);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, bsize);
    assert(bsize * g == g * bsize) by (nonlinear_arith);
    assert((g + 1) * bsize == g * bsize + bsize) by (nonlinear_arith);
    assert(g >= 0) by (nonlinear_arith) requires g * bsize + j % bsize == j, j >= 0, j % bsize < bsize, bsize >= 1;
    let m = n + bsize - 1;
    let nb = m / bsize;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m, bsize);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(m, bsize);
    assert(bsize * nb == nb * bsize) by (nonlinear_arith);
    assert(g < nb) by (nonlinear_arith)
        requires g * bsize <= j, j < n, nb * bsize + m % bsize == m, m == n + bsize - 1, m % bsize < bsize, bsize >= 1;
    g
}

/// The parts of an encoded column decode, row by row, to its source values (the groups are the uniform blocks).
pub proof fn lemma_for_decode<C: Code>(tp: Seq<PartView>, gp: int, cp: int, bp: int, col: ForCol<C>, src: ValSrc,
    rm: RowMap, n: int, bsize: int)
    requires
        0 <= gp < tp.len(),
        0 <= cp < tp.len(),
        0 <= bp < tp.len(),
        groups_part_ok(tp[gp], n, bsize),
        for_col_ok(col, src, rm, n, bsize),
        tp[cp] == C::part_of(col.codes@),
        tp[bp] is I64 || tp[bp] is U64,
        crate::gendb_entry::stored::part_len(tp[bp]) == col.bases@.len(),
        forall|g: int| 0 <= g < col.bases@.len() ==> #[trigger] base_at(tp[bp], g) == col.bases@[g] as int,
    ensures
        for_shape(gs_at(tp, gp), tp[bp], tp[cp], n),
        forall|j: int| 0 <= j < n ==> #[trigger] for_at(gs_at(tp, gp), tp[bp], tp[cp], j) == src_val(src, rm_at(rm, j)),
{
    C::lemma_part_of(col.codes@);
    lemma_uniform_groups(tp[gp], n, bsize);
    assert(nblocks_of(n, bsize) == nblocks(n, bsize));
    assert forall|j: int| 0 <= j < n implies #[trigger] for_at(gs_at(tp, gp), tp[bp], tp[cp], j) == src_val(src, rm_at(rm, j)) by {
        let g = lemma_row_block(n, bsize, j);
        lemma_uniform_in_group(tp[gp], n, bsize, g, j);
        assert(block_ok(src, rm, n, bsize, g, col.bases@[g], col.zmax@[g], col.codes@, 0));
        assert(col.bases@[g] + C::val(col.codes@[j - 0]) == src_val(src, rm_at(rm, j)));
        assert(code_at(tp[cp], j) == C::val(col.codes@[j]));
    }
}

/// The zone part of an encoded column bounds every group's values from above.
pub proof fn lemma_zone<C: Code>(tp: Seq<PartView>, gp: int, cp: int, bp: int, zp: int, col: ForCol<C>, src: ValSrc,
    rm: RowMap, n: int, bsize: int, z: Seq<i64>)
    requires
        0 <= gp < tp.len(),
        0 <= cp < tp.len(),
        0 <= bp < tp.len(),
        0 <= zp < tp.len(),
        groups_part_ok(tp[gp], n, bsize),
        for_col_ok(col, src, rm, n, bsize),
        tp[cp] == C::part_of(col.codes@),
        forall|g: int| 0 <= g < col.bases@.len() ==> #[trigger] base_at(tp[bp], g) == col.bases@[g] as int,
        tp[zp] == PartView::I64(z),
        z.len() == col.zmax@.len(),
        forall|g: int| 0 <= g < z.len() ==> #[trigger] z[g] as int == col.zmax@[g] as int,
    ensures
        zone_at(tp, gp, cp, bp, zp),
{
    C::lemma_part_of(col.codes@);
    lemma_uniform_groups(tp[gp], n, bsize);
    let gs = gs_at(tp, gp);
    assert forall|g: int, j: int| #[trigger] in_group(gs, g, j) implies base_at(tp[bp], g) + code_at(tp[cp], j) <= z[g] by {
        lemma_groups_bounds(gs, n, g + 1);
        assert(gs[g] == g * bsize);
        assert(blk_lo(bsize, g) <= j < blk_hi(n, bsize, g)) by {
            lemma_nblocks(n, bsize);
            if g + 1 < nblocks_of(n, bsize) {
                assert(gs[g + 1] == (g + 1) * bsize);
            } else {
                assert(gs[g + 1] == n);
                assert((g + 1) * bsize >= n);
            }
        }
        assert(block_ok(src, rm, n, bsize, g, col.bases@[g], col.zmax@[g], col.codes@, 0));
        assert(col.bases@[g] + C::val(col.codes@[j - 0]) == src_val(src, rm_at(rm, j)));
    }
}

/// A bigint column whose FOR parts decode to its source values (stored row `j` is canonical row `rm_at(rm, j)`).
pub proof fn lemma_int_col(tp: Seq<PartView>, gp: int, cp: int, bp: int, rows: Seq<Row>, c: int, src: ValSrc, rm: RowMap)
    requires
        0 <= gp < tp.len() && 0 <= cp < tp.len() && 0 <= bp < tp.len(),
        tp[bp] is I64,
        for_shape(gs_at(tp, gp), tp[bp], tp[cp], rows.len() as int),
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] for_at(gs_at(tp, gp), tp[bp], tp[cp], j) == src_val(src, rm_at(rm, j)),
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][c] == Val::Int(src_val(src, rm_at(rm, j))),
    ensures
        int_col_at(tp, gp, cp, bp, rows, c),
{
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] rows[j][c] == Val::Int(for_at(gs_at(tp, gp), tp[bp], tp[cp], j)) by {
        assert(for_at(gs_at(tp, gp), tp[bp], tp[cp], j) == src_val(src, rm_at(rm, j)));
    }
}

/// A numeric column of scale `scale` whose FOR parts decode to its source coefficients.
pub proof fn lemma_num_col(tp: Seq<PartView>, gp: int, cp: int, bp: int, rows: Seq<Row>, c: int, scale: nat, src: ValSrc, rm: RowMap)
    requires
        0 <= gp < tp.len() && 0 <= cp < tp.len() && 0 <= bp < tp.len(),
        tp[bp] is I64,
        for_shape(gs_at(tp, gp), tp[bp], tp[cp], rows.len() as int),
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] for_at(gs_at(tp, gp), tp[bp], tp[cp], j) == src_val(src, rm_at(rm, j)),
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][c] == (Val::Num { coeff: src_val(src, rm_at(rm, j)), scale }),
    ensures
        num_col_at(tp, gp, cp, bp, rows, c, scale),
{
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] rows[j][c] == (Val::Num { coeff: for_at(gs_at(tp, gp), tp[bp], tp[cp], j), scale }) by {
        assert(for_at(gs_at(tp, gp), tp[bp], tp[cp], j) == src_val(src, rm_at(rm, j)));
    }
}

/// A date column whose FOR parts decode to its source dates (days since 2000-01-01).
pub proof fn lemma_date_col(tp: Seq<PartView>, gp: int, cp: int, bp: int, rows: Seq<Row>, c: int, src: ValSrc, rm: RowMap)
    requires
        0 <= gp < tp.len() && 0 <= cp < tp.len() && 0 <= bp < tp.len(),
        tp[bp] is I64,
        for_shape(gs_at(tp, gp), tp[bp], tp[cp], rows.len() as int),
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] for_at(gs_at(tp, gp), tp[bp], tp[cp], j) == src_val(src, rm_at(rm, j)),
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][c] == Val::Date(src_val(src, rm_at(rm, j))),
    ensures
        date_col_at(tp, gp, cp, bp, rows, c),
{
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] rows[j][c] == Val::Date(for_at(gs_at(tp, gp), tp[bp], tp[cp], j)) by {
        assert(for_at(gs_at(tp, gp), tp[bp], tp[cp], j) == src_val(src, rm_at(rm, j)));
    }
}

/// A dictionary column whose FOR parts decode to each value's dictionary index.
pub proof fn lemma_dict_col(tp: Seq<PartView>, gp: int, cp: int, bp: int, op: int, yp: int, rows: Seq<Row>, c: int,
    t: TextView, da: &Arc<Dict>, rm: RowMap, nsrc: int)
    requires
        0 <= gp < tp.len() && 0 <= cp < tp.len() && 0 <= bp < tp.len() && 0 <= op < tp.len() && 0 <= yp < tp.len(),
        tp[bp] is U64,
        tp[op] == PartView::U64(da.offs@),
        tp[yp] == PartView::U8(da.bytes@),
        dict_wf(**da),
        rm_wf(rm, nsrc),
        rows.len() == nsrc,
        forall|i: int| 0 <= i < nsrc ==> #[trigger] dict_has(**da, text_at(t, i)),
        for_shape(gs_at(tp, gp), tp[bp], tp[cp], rows.len() as int),
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] for_at(gs_at(tp, gp), tp[bp], tp[cp], j) == dict_index_of(**da, text_at(t, rm_at(rm, j))),
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][c] == Val::Text(text_at(t, rm_at(rm, j))),
    ensures
        dict_col_at(tp, gp, cp, bp, op, yp, rows, c),
{
    let d = **da;
    assert forall|j: int| 0 <= j < rows.len() implies {
        &&& 0 <= for_at(gs_at(tp, gp), tp[bp], tp[cp], j) < u64s(tp[op]).len() - 1
        &&& #[trigger] rows[j][c] == Val::Text(text_of(u64s(tp[op]), u8s(tp[yp]), for_at(gs_at(tp, gp), tp[bp], tp[cp], j)))
    } by {
        let i = rm_at(rm, j);
        match rm {
            RowMap::Identity => {},
            RowMap::Map(v) => { assert(v@[j] < nsrc); },
        }
        assert(dict_has(d, text_at(t, i)));
        let x = choose|x: int| 0 <= x < dict_k(d) && dict_entry(d, x) == text_at(t, i);
        lemma_dict_index_of(d, text_at(t, i), x);
        assert(for_at(gs_at(tp, gp), tp[bp], tp[cp], j) == x);
    }
}

/// A plain text column copied in stored order.
pub proof fn lemma_text_col(tp: Seq<PartView>, op: int, yp: int, rows: Seq<Row>, c: int, offs: Seq<u64>, bytes: Seq<u8>,
    t: TextView, rm: RowMap)
    requires
        0 <= op < tp.len() && 0 <= yp < tp.len(),
        tp[op] == PartView::U64(offs),
        tp[yp] == PartView::U8(bytes),
        text_parts_wf(offs, bytes, rows.len() as int),
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] text_of(offs, bytes, j) == text_at(t, rm_at(rm, j)),
        forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j][c] == Val::Text(text_at(t, rm_at(rm, j))),
    ensures
        text_col_at(tp, op, yp, rows, c),
{
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] rows[j][c] == Val::Text(text_of(offs, bytes, j)) by {
        assert(text_of(offs, bytes, j) == text_at(t, rm_at(rm, j)));
    }
}

/// A copy of a `u64` vector.
pub fn copy_u64s(v: &Vec<u64>) -> (r: Vec<u64>)
    ensures r@ == v@,
{
    let mut r: Vec<u64> = Vec::with_capacity(v.len());
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
        proof { assert(r@ =~= v@.subrange(0, i as int)); }
    }
    proof { assert(v@.subrange(0, v@.len() as int) =~= v@); }
    r
}

/// A copy of a byte vector.
pub fn copy_u8s(v: &Vec<u8>) -> (r: Vec<u8>)
    ensures r@ == v@,
{
    let mut r: Vec<u8> = Vec::with_capacity(v.len());
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
        proof { assert(r@ =~= v@.subrange(0, i as int)); }
    }
    proof { assert(v@.subrange(0, v@.len() as int) =~= v@); }
    r
}

/// The row map column of a permuted table decodes to the (bijective) stored-to-canonical map `v`.
pub proof fn lemma_perm_col(tp: Seq<PartView>, gp: int, cp: int, bp: int, n: int, v: Seq<u64>)
    requires
        0 <= gp < tp.len() && 0 <= cp < tp.len() && 0 <= bp < tp.len(),
        tp[bp] is U64,
        for_shape(gs_at(tp, gp), tp[bp], tp[cp], n),
        v.len() == n,
        is_perm(crate::builder::common::perm::map_view(v), n),
        forall|j: int| 0 <= j < n ==> #[trigger] for_at(gs_at(tp, gp), tp[bp], tp[cp], j) == v[j] as int,
    ensures
        perm_col_at(tp, gp, cp, bp, n),
        for_map(gs_at(tp, gp), tp[bp], tp[cp], n) == crate::builder::common::perm::map_view(v),
{
    assert(for_map(gs_at(tp, gp), tp[bp], tp[cp], n) =~= crate::builder::common::perm::map_view(v));
}

/// A stored-to-canonical map vector, shared with worker tasks, is a well-formed bijective row map.
pub proof fn lemma_map_rm(rmv: Arc<Vec<u64>>, n: int)
    requires
        rmv@.len() == n,
        is_perm(crate::builder::common::perm::map_view(rmv@), n),
    ensures
        rm_wf(RowMap::Map(rmv), n),
        crate::builder::common::textcopy::rm_perm(RowMap::Map(rmv), n),
        forall|j: int| 0 <= j < n ==> #[trigger] rm_at(RowMap::Map(rmv), j) == rmv@[j] as int,
{
    let m = crate::builder::common::perm::map_view(rmv@);
    assert forall|j: int| 0 <= j < n implies #[trigger] rmv@[j] < n by {
        assert(0 <= m[j] < n);
    }
    assert(crate::builder::common::textcopy::rm_seq(RowMap::Map(rmv), n) =~= m);
}

} // verus!
