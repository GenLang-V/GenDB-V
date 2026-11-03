//! The source columns the builder reads from storage `suppliers`, as frame-of-reference values
//! `base[j / bsize] + code[j]` (U32 codes, I64 bases): s_acctbal (coefficient of scale 2) of every supplier row and
//! ps_suppkey of every partsupp row (`open_col`), tied to the stored relations (`acct_rows`, `suppkey_rows`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::StoredParts;
use crate::spec::value::{Row, Val};
use crate::spec::types::{Column, SqlType};
use crate::spec::typing::value_in_column;
use crate::spec::int::{int_in_range, IntKind};
use crate::spec::numeric::pow10;
use crate::link::source::rows_in_columns;
use crate::stores::suppliers::interface as S;
use crate::stores::suppliers::declaration as SD;
use crate::stores::suppliers::interface::common::colfmt as CF;
use crate::stores::suppliers::interface::common::read as CR;

verus! {

/// Part indices (in storage `suppliers`) of the two columns the builder reads.
pub const SU_LAYOUT: usize = 13;
pub const SU_GROUPS: usize = 14;
pub const SU_ACCT_CODES: usize = 25;
pub const SU_ACCT_BASE: usize = 26;
pub const PS_LAYOUT: usize = 0;
pub const PS_GROUPS: usize = 1;
pub const PS_SUPP_CODES: usize = 4;
pub const PS_SUPP_BASE: usize = 5;

/// Value of row `j` of a frame-of-reference column.
pub open spec fn for_val(c: Seq<u32>, b: Seq<i64>, bs: int, j: int) -> int {
    b[j / bs] + c[j]
}

/// A frame-of-reference column of `n` rows: every row has its base, and its value is an `i64`.
pub open spec fn col_ok(c: Seq<u32>, b: Seq<i64>, bs: int, n: int) -> bool {
    &&& bs >= 1
    &&& c.len() == n
    &&& forall|j: int| 0 <= j < n ==> #[trigger] (j / bs) < b.len()
    &&& forall|j: int| 0 <= j < n ==> i64::MIN <= #[trigger] for_val(c, b, bs, j) <= i64::MAX
}

/// s_acctbal of every supplier row is the column's value.
pub open spec fn acct_rows(s: Seq<Row>, c: Seq<u32>, b: Seq<i64>, bs: int) -> bool {
    forall|j: int| 0 <= j < s.len() ==> #[trigger] s[j][5] == (Val::Num { coeff: for_val(c, b, bs, j), scale: 2 })
}

/// ps_suppkey of every partsupp row is the column's value.
pub open spec fn suppkey_rows(ps: Seq<Row>, c: Seq<u32>, b: Seq<i64>, bs: int) -> bool {
    forall|k: int| 0 <= k < ps.len() ==> #[trigger] ps[k][1] == Val::Int(for_val(c, b, bs, k))
}

/// The block size the builder uses: the stored one, clamped to the row count (every row keeps its group).
pub open spec fn eff_bs(b0: int, n: int) -> int {
    if b0 <= n { b0 } else { n }
}

/// Clamping the block size to `n` keeps every row's group.
proof fn lemma_eff(b0: int, n: int)
    requires b0 >= 1, n >= 1,
    ensures eff_bs(b0, n) >= 1, forall|j: int| 0 <= j < n ==> #[trigger] (j / eff_bs(b0, n)) == j / b0,
{
    let b = eff_bs(b0, n);
    assert forall|j: int| 0 <= j < n implies #[trigger] (j / b) == j / b0 by {
        if b0 > n {
            assert(j / b == 0) by (nonlinear_arith) requires 0 <= j < b;
            assert(j / b0 == 0) by (nonlinear_arith) requires 0 <= j < b0;
        }
    }
}

/// A numeric(15,2) value's coefficient fits `i64`.
proof fn lemma_num15(v: Val, coeff: int)
    requires
        value_in_column(v, Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }),
        v == (Val::Num { coeff, scale: 2 }),
    ensures i64::MIN <= coeff <= i64::MAX,
{
    assert(pow10(15) == 1000000000000000) by (compute);
}

/// The row facts of a frame-of-reference column (I64 bases, U32 codes) of the table parts `tp` at the stored block
/// size, given the per-row fact `cell(j)` the interface states for it.
proof fn lemma_col(tp: Seq<PartView>, n: int, cp: int, bp: int)
    requires
        S::table_layout_ok(tp, n),
        CF::for_i64_shape(tp, 1, cp, bp, n),
        tp[cp] is U32,
    ensures ({
        let bt = CF::u64s(tp[0])[1] as int;
        &&& bt >= 1
        &&& CF::u32s(tp[cp]).len() == n
        &&& forall|j: int| 0 <= j < n ==> #[trigger] (j / bt) < CF::i64s(tp[bp]).len()
        &&& forall|j: int| 0 <= j < n ==> #[trigger] CF::for_at(CF::u64s(tp[1]), tp[bp], tp[cp], j)
                == for_val(CF::u32s(tp[cp]), CF::i64s(tp[bp]), bt, j)
    }),
{
    let bt = CF::u64s(tp[0])[1] as int;
    let gp = tp[1];
    CF::lemma_uniform_groups(gp, n, bt);
    CF::lemma_nblocks(n, bt);
    assert forall|j: int| 0 <= j < n implies #[trigger] (j / bt) < CF::i64s(tp[bp]).len() by {
        assert(j / bt < CF::nblocks_of(n, bt)) by {
            assert(j / bt <= (n - 1) / bt) by (nonlinear_arith) requires 0 <= j <= n - 1, bt >= 1;
            assert(((n - 1) / bt) * bt <= n - 1) by (nonlinear_arith) requires n >= 1, bt >= 1;
            assert((n - 1) / bt < (n + bt - 1) / bt) by (nonlinear_arith) requires n >= 1, bt >= 1;
        }
    }
    assert forall|j: int| 0 <= j < n implies #[trigger] CF::for_at(CF::u64s(tp[1]), tp[bp], tp[cp], j)
        == for_val(CF::u32s(tp[cp]), CF::i64s(tp[bp]), bt, j) by {
        CR::lemma_for_row(gp, n, bt, tp[bp], tp[cp], j);
    }
}

/// The s_acctbal column of the supplier rows `s` (storage suppliers' parts `p`).
pub proof fn lemma_acct_src(p: Seq<PartView>, s: Seq<Row>)
    requires
        p.len() == S::SUPPLIERS_PARTS,
        S::supplier_ok(p.subrange(S::SUPPLIER_FIRST as int, (S::SUPPLIER_FIRST + S::SU_PARTS) as int), s),
        rows_in_columns(s, SD::stored_columns_t1()),
    ensures ({
        let bt = CF::u64s(p[SU_LAYOUT as int])[1] as int;
        let (c, b) = (CF::u32s(p[SU_ACCT_CODES as int]), CF::i64s(p[SU_ACCT_BASE as int]));
        &&& p[SU_LAYOUT as int] is U64 && CF::u64s(p[SU_LAYOUT as int]).len() == 2
        &&& CF::u64s(p[SU_LAYOUT as int])[0] == s.len()
        &&& p[SU_ACCT_CODES as int] is U32 && p[SU_ACCT_BASE as int] is I64
        &&& col_ok(c, b, bt, s.len() as int)
        &&& acct_rows(s, c, b, bt)
    }),
{
    let tp = p.subrange(S::SUPPLIER_FIRST as int, (S::SUPPLIER_FIRST + S::SU_PARTS) as int);
    let n = s.len() as int;
    assert(tp[0] == p[SU_LAYOUT as int]);
    assert(tp[1] == p[SU_GROUPS as int]);
    assert(tp[12] == p[SU_ACCT_CODES as int]);
    assert(tp[13] == p[SU_ACCT_BASE as int]);
    assert(S::table_layout_ok(tp, n));
    assert(CF::num_col_at(tp, 1, 12, 13, s, 5, 2));
    lemma_col(tp, n, 12, 13);
    let bt = CF::u64s(tp[0])[1] as int;
    let (c, b) = (CF::u32s(tp[12]), CF::i64s(tp[13]));
    assert forall|j: int| 0 <= j < n implies #[trigger] s[j][5] == (Val::Num { coeff: for_val(c, b, bt, j), scale: 2 }) by {
        assert(CF::for_at(CF::u64s(tp[1]), tp[13], tp[12], j) == for_val(c, b, bt, j));
    }
    assert forall|j: int| 0 <= j < n implies i64::MIN <= #[trigger] for_val(c, b, bt, j) <= i64::MAX by {
        assert(s[j][5] == (Val::Num { coeff: for_val(c, b, bt, j), scale: 2 }));
        assert(s[j].len() == SD::stored_columns_t1().len());
        assert(value_in_column(s[j][5], SD::stored_columns_t1()[5]));
        lemma_num15(s[j][5], for_val(c, b, bt, j));
    }
}

/// The ps_suppkey column of the partsupp rows `ps` (storage suppliers' parts `p`).
pub proof fn lemma_suppkey_src(p: Seq<PartView>, ps: Seq<Row>)
    requires
        p.len() == S::SUPPLIERS_PARTS,
        S::partsupp_ok(p.subrange(S::PARTSUPP_FIRST as int, (S::PARTSUPP_FIRST + S::PS_PARTS) as int), ps),
        rows_in_columns(ps, SD::stored_columns_t0()),
    ensures ({
        let bt = CF::u64s(p[PS_LAYOUT as int])[1] as int;
        let (c, b) = (CF::u32s(p[PS_SUPP_CODES as int]), CF::i64s(p[PS_SUPP_BASE as int]));
        &&& p[PS_LAYOUT as int] is U64 && CF::u64s(p[PS_LAYOUT as int]).len() == 2
        &&& CF::u64s(p[PS_LAYOUT as int])[0] == ps.len()
        &&& p[PS_SUPP_CODES as int] is U32 && p[PS_SUPP_BASE as int] is I64
        &&& col_ok(c, b, bt, ps.len() as int)
        &&& suppkey_rows(ps, c, b, bt)
    }),
{
    let tp = p.subrange(S::PARTSUPP_FIRST as int, (S::PARTSUPP_FIRST + S::PS_PARTS) as int);
    let n = ps.len() as int;
    assert(tp[0] == p[PS_LAYOUT as int]);
    assert(tp[1] == p[PS_GROUPS as int]);
    assert(tp[4] == p[PS_SUPP_CODES as int]);
    assert(tp[5] == p[PS_SUPP_BASE as int]);
    assert(S::table_layout_ok(tp, n));
    assert(CF::int_col_at(tp, 1, 4, 5, ps, 1));
    lemma_col(tp, n, 4, 5);
    let bt = CF::u64s(tp[0])[1] as int;
    let (c, b) = (CF::u32s(tp[4]), CF::i64s(tp[5]));
    assert forall|k: int| 0 <= k < n implies #[trigger] ps[k][1] == Val::Int(for_val(c, b, bt, k)) by {
        assert(CF::for_at(CF::u64s(tp[1]), tp[5], tp[4], k) == for_val(c, b, bt, k));
    }
    assert forall|k: int| 0 <= k < n implies i64::MIN <= #[trigger] for_val(c, b, bt, k) <= i64::MAX by {
        assert(ps[k][1] == Val::Int(for_val(c, b, bt, k)));
        assert(ps[k].len() == SD::stored_columns_t0().len());
        assert(value_in_column(ps[k][1], SD::stored_columns_t0()[1]));
        assert(int_in_range(IntKind::Int8, for_val(c, b, bt, k)));
    }
}

/// The same column facts at the clamped block size.
pub proof fn lemma_eff_col(c: Seq<u32>, b: Seq<i64>, b0: int, n: int)
    requires col_ok(c, b, b0, n), n >= 1,
    ensures
        col_ok(c, b, eff_bs(b0, n), n),
        forall|j: int| 0 <= j < n ==> #[trigger] for_val(c, b, eff_bs(b0, n), j) == for_val(c, b, b0, j),
{
    lemma_eff(b0, n);
    let e = eff_bs(b0, n);
    assert forall|j: int| 0 <= j < n implies #[trigger] for_val(c, b, e, j) == for_val(c, b, b0, j) by {
        assert(j / e == j / b0);
    }
    assert forall|j: int| 0 <= j < n implies #[trigger] (j / e) < b.len() by {
        assert(j / e == j / b0);
    }
    assert forall|j: int| 0 <= j < n implies i64::MIN <= #[trigger] for_val(c, b, e, j) <= i64::MAX by {
        assert(for_val(c, b, e, j) == for_val(c, b, b0, j));
    }
}

/// The codes, bases and clamped block size of one column of `suppliers` (`n >= 1` rows), read from the layout part
/// `lp` and the code/base parts `cp`/`bp`.
pub fn open_col(st: &mut StoredParts, lp: usize, cp: usize, bp: usize, n: usize) -> (r: (&'static [u32], &'static [i64], usize))
    requires
        n >= 1,
        lp < old(st)@.len(), cp < old(st)@.len(), bp < old(st)@.len(),
        old(st)@[lp as int] is U64 && CF::u64s(old(st)@[lp as int]).len() == 2,
        old(st)@[cp as int] is U32 && old(st)@[bp as int] is I64,
        col_ok(CF::u32s(old(st)@[cp as int]), CF::i64s(old(st)@[bp as int]), CF::u64s(old(st)@[lp as int])[1] as int, n as int),
    ensures
        final(st)@ == old(st)@,
        r.0@ == CF::u32s(old(st)@[cp as int]),
        r.1@ == CF::i64s(old(st)@[bp as int]),
        r.2 as int == eff_bs(CF::u64s(old(st)@[lp as int])[1] as int, n as int),
        col_ok(r.0@, r.1@, r.2 as int, n as int),
        forall|j: int| 0 <= j < n ==> #[trigger] for_val(r.0@, r.1@, r.2 as int, j)
            == for_val(r.0@, r.1@, CF::u64s(old(st)@[lp as int])[1] as int, j),
{
    let ghost p = st@;
    let lay = st.extent_u64(lp, 0, 2);
    proof { assert(lay@ =~= CF::u64s(p[lp as int])); }
    let b64 = lay[1];
    let bs: usize = if b64 <= n as u64 { b64 as usize } else { n };
    let nb = st.part_len(bp);
    let c = st.extent_u32(cp, 0, n);
    let b = st.extent_i64(bp, 0, nb);
    proof {
        assert(c@ =~= CF::u32s(p[cp as int]));
        assert(b@ =~= CF::i64s(p[bp as int]));
        lemma_eff_col(c@, b@, b64 as int, n as int);
    }
    (c, b, bs)
}

} // verus!
