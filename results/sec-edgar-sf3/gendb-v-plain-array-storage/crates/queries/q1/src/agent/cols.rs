//! The columns the query reads, as whole stored parts: of `pre` adsh, line, stmt (with validity) and rfile; of
//! `sub` adsh (the dictionary of adsh values). Text columns keep their raw offsets into their whole bytes part, so
//! value `i` is `bytes[off[i] .. off[i + 1]]` (`text_of`). `corr(c, t)` relates the columns to the rows `t` of
//! `pre` (`pre_rows` of the stored parts), `sub_corr` the sub adsh column to the rows of `sub`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::link::query::{text_at, text_wf, TextView};
use crate::stores::flat_pre::interface as pre_if;
use crate::stores::flat_sub::interface as sub_if;
use crate::agent::spec::*;

verus! {

/// The columns of `pre` the query reads, as whole parts, and the adsh column of `sub` (byte lengths carried for
/// `no_unwind` code).
#[derive(Clone, Copy)]
pub struct Cols {
    pub n: usize,
    pub adsh_off: &'static [i64],
    pub adsh: &'static [u8],
    pub adsh_len: usize,
    pub line: &'static [i32],
    pub stmt_off: &'static [i64],
    pub stmt: &'static [u8],
    pub stmt_len: usize,
    pub stmt_valid: &'static [u8],
    pub rfile_off: &'static [i64],
    pub rfile: &'static [u8],
    pub rfile_len: usize,
    pub m: usize,
    pub sub_off: &'static [i64],
    pub sub: &'static [u8],
    pub sub_len: usize,
}

/// Value `i` of a text column given as offsets and bytes.
pub open spec fn text_of(off: Seq<i64>, bytes: Seq<u8>, i: int) -> Seq<u8> {
    bytes.subrange(off[i] as int, off[i + 1] as int)
}

/// Offsets of `n` values, each a byte range of `bytes`.
pub open spec fn text_ok(off: Seq<i64>, bytes: Seq<u8>, n: int) -> bool {
    &&& off.len() == n + 1
    &&& forall|i: int| 0 <= i < n ==> 0 <= #[trigger] off[i] <= off[i + 1] <= bytes.len()
}

impl Cols {
    /// stmt bytes of row `i`.
    pub open spec fn stext(&self, i: int) -> Seq<u8> {
        text_of(self.stmt_off@, self.stmt@, i)
    }

    /// rfile bytes of row `i`.
    pub open spec fn rtext(&self, i: int) -> Seq<u8> {
        text_of(self.rfile_off@, self.rfile@, i)
    }

    /// adsh bytes of row `i`.
    pub open spec fn atext(&self, i: int) -> Seq<u8> {
        text_of(self.adsh_off@, self.adsh@, i)
    }

    /// adsh bytes of `sub` row `j`.
    pub open spec fn subtext(&self, j: int) -> Seq<u8> {
        text_of(self.sub_off@, self.sub@, j)
    }
}

/// Shapes: lengths and well-formed offsets of every column.
pub open spec fn cols_wf(c: Cols) -> bool {
    &&& text_ok(c.adsh_off@, c.adsh@, c.n as int) && c.adsh_len == c.adsh@.len()
    &&& text_ok(c.stmt_off@, c.stmt@, c.n as int) && c.stmt_len == c.stmt@.len()
    &&& text_ok(c.rfile_off@, c.rfile@, c.n as int) && c.rfile_len == c.rfile@.len()
    &&& c.line@.len() == c.n
    &&& c.stmt_valid@.len() == c.n
    &&& text_ok(c.sub_off@, c.sub@, c.m as int) && c.sub_len == c.sub@.len()
}

/// Row `r` is row `i` of the columns.
pub open spec fn row_corr(c: Cols, r: Row, i: int) -> bool {
    &&& r.len() == 10
    &&& (r[3] is Null) == (c.stmt_valid@[i] == 0)
    &&& c.stmt_valid@[i] != 0 ==> r[3] == Val::Text(c.stext(i))
    &&& r[5] == Val::Text(c.rtext(i))
    &&& r[0] == Val::Text(c.atext(i))
    &&& r[2] == Val::Int(c.line@[i] as int)
}

/// `t` is the table the columns of `pre` hold.
pub open spec fn corr(c: Cols, t: Seq<Row>) -> bool {
    &&& t.len() == c.n
    &&& forall|i: int| 0 <= i < c.n ==> #[trigger] row_corr(c, t[i], i)
}

/// `s` is the table whose adsh column the `sub` columns hold.
pub open spec fn sub_corr(c: Cols, s: Seq<Row>) -> bool {
    &&& s.len() == c.m
    &&& forall|j: int| 0 <= j < c.m ==> (#[trigger] s[j]).len() == 20 && s[j][0] == Val::Text(c.subtext(j))
}

/// The rows `pre`'s parts represent (`rels[0]` of `represents`).
pub open spec fn pre_rows(parts: Seq<PartView>) -> Seq<Row> {
    Seq::new((pre_if::i64s(parts[pre_if::ADSH_OFFSETS as int]).len() - 1) as nat, |i: int| pre_if::row_at(parts, i))
}

/// The rows `sub`'s parts represent.
pub open spec fn sub_rows(parts: Seq<PartView>) -> Seq<Row> {
    Seq::new((sub_if::i64s(parts[sub_if::ADSH_OFFSETS as int]).len() - 1) as nat, |i: int| sub_if::row_at(parts, i))
}

/// Represented parts hold `pre_rows`.
pub proof fn lemma_pre_rows(parts: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires pre_if::represents(parts, rels),
    ensures rels[0] == pre_rows(parts),
{
    assert(rels[0] =~= pre_rows(parts));
}

/// Represented parts hold `sub_rows`.
pub proof fn lemma_sub_rows(parts: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires sub_if::represents(parts, rels),
    ensures rels[0] == sub_rows(parts),
{
    assert(rels[0] =~= sub_rows(parts));
}

/// Qualifying rows have the same key exactly when their stmt and rfile bytes are equal.
pub proof fn lemma_key_eq(c: Cols, t: Seq<Row>, i: int, j: int)
    requires
        corr(c, t), 0 <= i < c.n, 0 <= j < c.n, qual(t[i]), qual(t[j]),
    ensures
        (key_of(t[i]) == key_of(t[j])) == (c.stext(i) == c.stext(j) && c.rtext(i) == c.rtext(j)),
        key_of(t[i]) == seq![Val::Text(c.stext(i)), Val::Text(c.rtext(i))],
{
    assert(row_corr(c, t[i], i));
    assert(row_corr(c, t[j], j));
    if key_of(t[i]) == key_of(t[j]) {
        assert(key_of(t[i])[0] == key_of(t[j])[0]);
        assert(key_of(t[i])[1] == key_of(t[j])[1]);
    }
    if c.stext(i) == c.stext(j) && c.rtext(i) == c.rtext(j) {
        assert(key_of(t[i]) =~= key_of(t[j]));
    }
    assert(key_of(t[i]) =~= seq![Val::Text(c.stext(i)), Val::Text(c.rtext(i))]);
}

/// Reads the columns of both storages (whole parts) from the stores.
pub fn load_cols(stores: &mut Stores) -> (c: Cols)
    requires
        exists|rp: Seq<Seq<Row>>, rs: Seq<Seq<Row>>| pre_if::represents(old(stores)@.flat_pre, rp)
            && sub_if::represents(old(stores)@.flat_sub, rs),
    ensures
        final(stores)@ == old(stores)@,
        cols_wf(c),
        corr(c, pre_rows(old(stores)@.flat_pre)),
        sub_corr(c, sub_rows(old(stores)@.flat_sub)),
{
    let ghost sv = stores@;
    let ghost (rp, rs) = choose|rp: Seq<Seq<Row>>, rs: Seq<Seq<Row>>| pre_if::represents(sv.flat_pre, rp)
        && sub_if::represents(sv.flat_sub, rs);
    let ghost pp = sv.flat_pre;
    let ghost sp = sv.flat_sub;
    proof {
        lemma_pre_rows(pp, rp);
        lemma_sub_rows(sp, rs);
    }
    let n = stores.flat_pre.part_len(pre_if::ADSH_OFFSETS) - 1;
    let adsh_len = stores.flat_pre.part_len(pre_if::ADSH_BYTES);
    let stmt_len = stores.flat_pre.part_len(pre_if::STMT_BYTES);
    let rfile_len = stores.flat_pre.part_len(pre_if::RFILE_BYTES);
    let adsh_off = stores.flat_pre.extent_i64(pre_if::ADSH_OFFSETS, 0, n + 1);
    let adsh = stores.flat_pre.extent_u8(pre_if::ADSH_BYTES, 0, adsh_len);
    let line = stores.flat_pre.extent_i32(pre_if::LINE, 0, n);
    let stmt_off = stores.flat_pre.extent_i64(pre_if::STMT_OFFSETS, 0, n + 1);
    let stmt = stores.flat_pre.extent_u8(pre_if::STMT_BYTES, 0, stmt_len);
    let stmt_valid = stores.flat_pre.extent_u8(pre_if::STMT_VALIDITY, 0, n);
    let rfile_off = stores.flat_pre.extent_i64(pre_if::RFILE_OFFSETS, 0, n + 1);
    let rfile = stores.flat_pre.extent_u8(pre_if::RFILE_BYTES, 0, rfile_len);
    let m = stores.flat_sub.part_len(sub_if::ADSH_OFFSETS) - 1;
    let sub_len = stores.flat_sub.part_len(sub_if::ADSH_BYTES);
    let sub_off = stores.flat_sub.extent_i64(sub_if::ADSH_OFFSETS, 0, m + 1);
    let sub = stores.flat_sub.extent_u8(sub_if::ADSH_BYTES, 0, sub_len);
    let c = Cols {
        n, adsh_off, adsh, adsh_len, line, stmt_off, stmt, stmt_len, stmt_valid, rfile_off, rfile, rfile_len,
        m, sub_off, sub, sub_len,
    };
    proof {
        assert(adsh_off@ =~= pre_if::i64s(pp[pre_if::ADSH_OFFSETS as int]));
        assert(adsh@ =~= pre_if::u8s(pp[pre_if::ADSH_BYTES as int]));
        assert(stmt_off@ =~= pre_if::i64s(pp[pre_if::STMT_OFFSETS as int]));
        assert(stmt@ =~= pre_if::u8s(pp[pre_if::STMT_BYTES as int]));
        assert(rfile_off@ =~= pre_if::i64s(pp[pre_if::RFILE_OFFSETS as int]));
        assert(rfile@ =~= pre_if::u8s(pp[pre_if::RFILE_BYTES as int]));
        assert(line@ =~= pre_if::i32s(pp[pre_if::LINE as int]));
        assert(stmt_valid@ =~= pre_if::u8s(pp[pre_if::STMT_VALIDITY as int]));
        assert(sub_off@ =~= sub_if::i64s(sp[sub_if::ADSH_OFFSETS as int]));
        assert(sub@ =~= sub_if::u8s(sp[sub_if::ADSH_BYTES as int]));
        let t = pre_rows(pp);
        assert forall|i: int| 0 <= i < c.n implies #[trigger] row_corr(c, t[i], i) by {
            assert(t[i] == pre_if::row_at(pp, i));
        }
        let s = sub_rows(sp);
        assert forall|j: int| 0 <= j < c.m implies (#[trigger] s[j]).len() == 20 && s[j][0] == Val::Text(c.subtext(j)) by {
            assert(s[j] == sub_if::row_at(sp, j));
        }
    }
    c
}

} // verus!
