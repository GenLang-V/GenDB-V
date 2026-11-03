//! The qualifying nations on the calling thread: for each nation row, the number of region rows joining it with
//! `r_name = $1` (`q5spec::r_cnt`, counted exactly); a nation with such a region row enters the list with its key
//! and the group of its name (`chain::qlist_ok`). Groups are the distinct nation names, first occurrence first.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::stored::StoredParts;
use crate::link::join::*;
use crate::stores::suppliers::interface as si;
use crate::stores::suppliers::interface::common::colfmt as scf;
use crate::agent::q5spec::*;
use crate::agent::lookup::*;
use crate::agent::chain::*;
use crate::agent::world::*;
use crate::agent::setup::*;
use crate::agent::common::forview::*;
use crate::agent::common::sums::*;
use crate::agent::views_suppliers as vs;

verus! {

/// The group names as byte sequences.
pub open spec fn names_view(g: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    g.map_values(|v: Vec<u8>| v@)
}

/// The qualifying-nation list and the group names.
pub struct QList {
    pub qkey: Vec<i64>,
    pub qgrp: Vec<usize>,
    pub gnames: Vec<Vec<u8>>,
    pub qrow: Ghost<Seq<int>>,
}

/// A text column of `n` rows (suppliers' text parts): offsets, bytes and the row values.
pub struct TextCol8 {
    pub offs: &'static [u64],
    pub bytes: &'static [u8],
}

/// Value `j` of a text column as owned bytes.
fn copy_text(t: &TextCol8, j: usize) -> (v: Vec<u8>)
    requires j + 1 < t.offs@.len(), scf::text_range_ok(t.offs@, t.bytes@, j as int),
    ensures v@ == scf::text_of(t.offs@, t.bytes@, j as int),
{
    let s = crate::stores::suppliers::interface::common::read::text_slice(t.offs, t.bytes, j);
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant i <= s@.len(), v@ == s@.subrange(0, i as int),
        decreases s@.len() - i,
    {
        v.push(s[i]);
        i = i + 1;
        proof {
            assert(v@ =~= s@.subrange(0, i as int));
        }
    }
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    v
}

/// Byte equality of a slice and a vector.
fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant a@.len() == b@.len(), i <= a@.len(), forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

/// The group of a name among the existing groups (`None`: a new name).
fn find_group(gnames: &Vec<Vec<u8>>, name: &[u8]) -> (r: Option<usize>)
    ensures
        r matches Some(g) ==> g < gnames@.len() && gnames@[g as int]@ == name@,
        r is None ==> forall|g: int| 0 <= g < gnames@.len() ==> #[trigger] gnames@[g]@ != name@,
{
    let mut g: usize = 0;
    while g < gnames.len()
        invariant g <= gnames@.len(), forall|i: int| 0 <= i < g ==> #[trigger] gnames@[i]@ != name@,
        decreases gnames@.len() - g,
    {
        if bytes_eq(gnames[g].as_slice(), name) {
            return Some(g);
        }
        g = g + 1;
    }
    None
}

/// The region rows joining nation row `i` with `r_name = $1`, counted.
fn count_regions(rk_c: &'static [u8], rk_b: &'static [i64], rdiv: Div, n_r: usize, rnames: &TextCol8,
    nreg: i64, name: &[u8], rs: Ghost<Rels>, n: Ghost<Row>) -> (cnt: usize)
    requires
        rdiv.ok(), col8_ok(rk_c@, rk_b@, rdiv.bs as int, n_r as int),
        rs@.r.len() == n_r,
        scf::text_parts_wf(rnames.offs@, rnames.bytes@, n_r as int),
        forall|r: int| 0 <= r < n_r ==> #[trigger] rs@.r[r][0] == Val::Int(fv8(rk_c@, rk_b@, rdiv.bs as int, r))
            && rs@.r[r][1] == Val::Text(scf::text_of(rnames.offs@, rnames.bytes@, r)),
        n@[2] == Val::Int(nreg as int),
    ensures cnt as int == r_cnt(rs@.r, n@, name@),
{
    let ghost f = |x: Row| r_term(n@, name@, x);
    let mut cnt: usize = 0;
    let mut r: usize = 0;
    proof {
        lemma_sum_range_empty(rs@.r, f, 0);
    }
    while r < n_r
        invariant
            rdiv.ok(), col8_ok(rk_c@, rk_b@, rdiv.bs as int, n_r as int),
            rs@.r.len() == n_r,
            scf::text_parts_wf(rnames.offs@, rnames.bytes@, n_r as int),
            forall|r: int| 0 <= r < n_r ==> #[trigger] rs@.r[r][0] == Val::Int(fv8(rk_c@, rk_b@, rdiv.bs as int, r))
                && rs@.r[r][1] == Val::Text(scf::text_of(rnames.offs@, rnames.bytes@, r)),
            n@[2] == Val::Int(nreg as int),
            f == (|x: Row| r_term(n@, name@, x)),
            r <= n_r,
            cnt <= r,
            cnt as int == sum_of(rs@.r.subrange(0, r as int), f),
        decreases n_r - r,
    {
        let rk = get8(rk_c, rk_b, rdiv, n_r, r);
        proof {
            assert(scf::text_range_ok(rnames.offs@, rnames.bytes@, r as int));
            lemma_sum_range_step(rs@.r, f, 0, r as int);
        }
        let mut hit = false;
        if rk == nreg {
            let s = crate::stores::suppliers::interface::common::read::text_slice(rnames.offs, rnames.bytes, r);
            if bytes_eq(s, name) {
                hit = true;
            }
        }
        proof {
            let x = rs@.r[r as int];
            assert(x[0] == Val::Int(fv8(rk_c@, rk_b@, rdiv.bs as int, r as int)));
            assert(x[0] == Val::Int(rk as int));
            assert(hit == (n@[2] == x[0] && x[1] == Val::Text(name@)));
            assert(f(x) == if hit { 1int } else { 0int });
        }
        if hit {
            cnt = cnt + 1;
        }
        r = r + 1;
    }
    proof {
        lemma_sum_range_all(rs@.r, f);
    }
    cnt
}

/// The nation and region columns the qualifying list reads.
pub struct DimCols {
    pub nk_c: &'static [u8],
    pub nk_b: &'static [i64],
    pub nr_c: &'static [u8],
    pub nr_b: &'static [i64],
    pub nnames: TextCol8,
    pub n_n: usize,
    pub ndiv: Div,
    pub rk_c: &'static [u8],
    pub rk_b: &'static [i64],
    pub rnames: TextCol8,
    pub n_r: usize,
    pub rdiv: Div,
}

pub open spec fn dim_cols_ok(d: DimCols, rs: Rels) -> bool {
    &&& d.ndiv.ok() && d.rdiv.ok()
    &&& rs.n.len() == d.n_n && rs.r.len() == d.n_r
    &&& col8_ok(d.nk_c@, d.nk_b@, d.ndiv.bs as int, d.n_n as int)
    &&& col8_ok(d.nr_c@, d.nr_b@, d.ndiv.bs as int, d.n_n as int)
    &&& col8_ok(d.rk_c@, d.rk_b@, d.rdiv.bs as int, d.n_r as int)
    &&& scf::text_parts_wf(d.nnames.offs@, d.nnames.bytes@, d.n_n as int)
    &&& scf::text_parts_wf(d.rnames.offs@, d.rnames.bytes@, d.n_r as int)
    &&& forall|i: int| 0 <= i < d.n_n ==> #[trigger] rs.n[i][0] == Val::Int(fv8(d.nk_c@, d.nk_b@, d.ndiv.bs as int, i))
            && rs.n[i][2] == Val::Int(fv8(d.nr_c@, d.nr_b@, d.ndiv.bs as int, i))
            && rs.n[i][1] == Val::Text(scf::text_of(d.nnames.offs@, d.nnames.bytes@, i))
    &&& forall|r: int| 0 <= r < d.n_r ==> #[trigger] rs.r[r][0] == Val::Int(fv8(d.rk_c@, d.rk_b@, d.rdiv.bs as int, r))
            && rs.r[r][1] == Val::Text(scf::text_of(d.rnames.offs@, d.rnames.bytes@, r))
}

/// Read the nation and region columns.
pub fn read_dims(sp: &mut StoredParts, rs: Ghost<Rels>, psupp: Ghost<Seq<Row>>) -> (d: DimCols)
    requires
        si::represents(old(sp)@, seq![psupp@, rs@.s, rs@.n, rs@.r]),
        rels_shapes(rs@),
    ensures
        final(sp)@ == old(sp)@,
        dim_cols_ok(d, rs@),
{
    let ghost parts = sp@;
    let ghost tn = parts.subrange(30, 40);
    let ghost tr = parts.subrange(40, 48);
    let ghost nrel = rs@.n;
    let ghost rrel = rs@.r;
    proof {
        assert(si::nation_ok(tn, nrel));
        assert(si::region_ok(tr, rrel));
        assert(forall|i: int| 0 <= i < 10 ==> #[trigger] tn[i] == parts[30 + i]);
        assert(forall|i: int| 0 <= i < 8 ==> #[trigger] tr[i] == parts[40 + i]);
    }
    let nlay = whole_u64(sp, 30 + si::NA_LAYOUT);
    let n_n = sp.part_len(30 + si::NA_NATIONKEY_CODES);
    let (ndiv, _) = div_for(nlay[1], n_n);
    let nk_c = whole_u8(sp, 30 + si::NA_NATIONKEY_CODES);
    let nk_b = whole_i64(sp, 30 + si::NA_NATIONKEY_BASE);
    let nr_c = whole_u8(sp, 30 + si::NA_REGIONKEY_CODES);
    let nr_b = whole_i64(sp, 30 + si::NA_REGIONKEY_BASE);
    let no = whole_u64(sp, 30 + si::NA_NAME_OFFS);
    let ny = whole_u8(sp, 30 + si::NA_NAME_BYTES);
    let rlay = whole_u64(sp, 40 + si::RE_LAYOUT);
    let n_r = sp.part_len(40 + si::RE_REGIONKEY_CODES);
    let (rdiv, _) = div_for(rlay[1], n_r);
    let rk_c = whole_u8(sp, 40 + si::RE_REGIONKEY_CODES);
    let rk_b = whole_i64(sp, 40 + si::RE_REGIONKEY_BASE);
    let ro = whole_u64(sp, 40 + si::RE_NAME_OFFS);
    let ry = whole_u8(sp, 40 + si::RE_NAME_BYTES);
    proof {
        let nn = nrel.len() as int;
        let nr = rrel.len() as int;
        assert forall|j: int| 0 <= j < nn implies (#[trigger] nrel[j][0]) is Int && i64::MIN <= nrel[j][0]->Int_0 <= i64::MAX by {}
        assert forall|j: int| 0 <= j < nn implies (#[trigger] nrel[j][2]) is Int && i64::MIN <= nrel[j][2]->Int_0 <= i64::MAX by {}
        assert forall|j: int| 0 <= j < nr implies (#[trigger] rrel[j][0]) is Int && i64::MIN <= rrel[j][0]->Int_0 <= i64::MAX by {}
        let (bn, bn2) = (nlay@[1] as int, ndiv.bs as int);
        let (br, br2) = (rlay@[1] as int, rdiv.bs as int);
        vs::lemma_int8(tn, 1, 2, 3, nrel, 0, bn);
        vs::lemma_int8(tn, 1, 6, 7, nrel, 2, bn);
        vs::lemma_int8(tr, 1, 2, 3, rrel, 0, br);
        lemma_col8_rebase(nk_c@, nk_b@, bn, bn2, nn);
        lemma_col8_rebase(nr_c@, nr_b@, bn, bn2, nn);
        lemma_col8_rebase(rk_c@, rk_b@, br, br2, nr);
        assert forall|i: int| 0 <= i < nn implies #[trigger] nrel[i][0] == Val::Int(fv8(nk_c@, nk_b@, bn2, i))
            && nrel[i][2] == Val::Int(fv8(nr_c@, nr_b@, bn2, i))
            && nrel[i][1] == Val::Text(scf::text_of(no@, ny@, i)) by {
            assert(nrel[i][0] == Val::Int(fv8(nk_c@, nk_b@, bn, i)));
            assert(nrel[i][2] == Val::Int(fv8(nr_c@, nr_b@, bn, i)));
        }
        assert forall|r: int| 0 <= r < nr implies #[trigger] rrel[r][0] == Val::Int(fv8(rk_c@, rk_b@, br2, r))
            && rrel[r][1] == Val::Text(scf::text_of(ro@, ry@, r)) by {
            assert(rrel[r][0] == Val::Int(fv8(rk_c@, rk_b@, br, r)));
        }
    }
    DimCols { nk_c, nk_b, nr_c, nr_b, nnames: TextCol8 { offs: no, bytes: ny }, n_n, ndiv,
        rk_c, rk_b, rnames: TextCol8 { offs: ro, bytes: ry }, n_r, rdiv }
}

/// The qualifying-nation list of region name `$1` (bytes `name`).
pub fn build_qlist(d: &DimCols, name: &[u8], rs: Ghost<Rels>, prm: Ghost<Prm>) -> (q: QList)
    requires
        dim_cols_ok(*d, rs@),
        keys_unique(rs@.r),
        name@ == prm@.name,
    ensures
        qlist_ok(rs@, prm@, q.qkey@, q.qgrp@, q.qrow@, names_view(q.gnames@)),
{
    let mut qkey: Vec<i64> = Vec::new();
    let mut qgrp: Vec<usize> = Vec::new();
    let mut gnames: Vec<Vec<u8>> = Vec::new();
    let ghost mut qrow: Seq<int> = Seq::empty();
    let mut i: usize = 0;
    while i < d.n_n
        invariant
            dim_cols_ok(*d, rs@),
            keys_unique(rs@.r),
            name@ == prm@.name,
            i <= d.n_n,
            qkey@.len() == qgrp@.len() && qrow.len() == qkey@.len(),
            forall|q: int| 0 <= q < qkey@.len() ==> #[trigger] qentry_ok(rs@, prm@, qkey@, qgrp@, qrow, names_view(gnames@), q),
            forall|q: int| 0 <= q < qkey@.len() ==> #[trigger] qrow[q] < i,
            forall|j: int| 0 <= j < i && r_cnt(rs@.r, #[trigger] rs@.n[j], prm@.name) != 0 ==>
                exists|q: int| 0 <= q < qkey@.len() && qrow[q] == j,
            forall|a: int, b: int| 0 <= a < gnames@.len() && 0 <= b < gnames@.len() && a != b ==>
                #[trigger] names_view(gnames@)[a] != #[trigger] names_view(gnames@)[b],
        decreases d.n_n - i,
    {
        let ghost n = rs@.n[i as int];
        let nreg = get8(d.nr_c, d.nr_b, d.ndiv, d.n_n, i);
        proof {
            assert(rs@.n[i as int][0] == Val::Int(fv8(d.nk_c@, d.nk_b@, d.ndiv.bs as int, i as int)));
        }
        let ghost oqk = qkey@;
        let ghost oqg = qgrp@;
        let ghost oqr = qrow;
        let ghost onames = names_view(gnames@);
        let cnt = count_regions(d.rk_c, d.rk_b, d.rdiv, d.n_r, &d.rnames, nreg, name, rs, Ghost(n));
        proof {
            lemma_r_cnt_le1(rs@.r, n, name@);
        }
        if cnt != 0 {
            let nk = get8(d.nk_c, d.nk_b, d.ndiv, d.n_n, i);
            proof {
                assert(scf::text_range_ok(d.nnames.offs@, d.nnames.bytes@, i as int));
            }
            let nm = copy_text(&d.nnames, i);
            let gi = match find_group(&gnames, nm.as_slice()) {
                Some(g) => g,
                None => {
                    let ghost old_names = names_view(gnames@);
                    let g = gnames.len();
                    gnames.push(nm);
                    proof {
                        assert(names_view(gnames@) =~= old_names.push(nm@));
                    }
                    g
                },
            };
            let ghost old_q = qkey@.len();
            qkey.push(nk);
            qgrp.push(gi);
            proof {
                qrow = qrow.push(i as int);
                let nv = names_view(gnames@);
                assert(forall|g: int| 0 <= g < onames.len() ==> #[trigger] nv[g] == onames[g]);
                assert(qentry_ok(rs@, prm@, qkey@, qgrp@, qrow, nv, old_q as int));
                assert forall|q: int| 0 <= q < qkey@.len() implies #[trigger] qentry_ok(rs@, prm@, qkey@, qgrp@, qrow, nv, q) by {
                    if q < old_q {
                        assert(qentry_ok(rs@, prm@, oqk, oqg, oqr, onames, q));
                        assert(qkey@[q] == oqk[q] && qgrp@[q] == oqg[q] && qrow[q] == oqr[q]);
                    }
                }
                assert forall|q: int| 0 <= q < qkey@.len() implies #[trigger] qrow[q] < i + 1 by {
                    if q < old_q {
                        assert(qrow[q] == oqr[q]);
                    }
                }
                assert forall|j: int| 0 <= j < i + 1 && r_cnt(rs@.r, #[trigger] rs@.n[j], prm@.name) != 0 implies
                    exists|q: int| 0 <= q < qkey@.len() && qrow[q] == j by {
                    if j < i {
                        let q = choose|q: int| 0 <= q < oqk.len() && oqr[q] == j;
                        assert(qrow[q] == j);
                    } else {
                        assert(qrow[old_q as int] == j);
                    }
                }
            }
        } else {
            proof {
                assert forall|j: int| 0 <= j < i + 1 && r_cnt(rs@.r, #[trigger] rs@.n[j], prm@.name) != 0 implies
                    exists|q: int| 0 <= q < qkey@.len() && qrow[q] == j by {
                    if j == i {
                        assert(r_cnt(rs@.r, n, name@) == 0);
                    }
                }
            }
        }
        i = i + 1;
    }
    QList { qkey, qgrp, gnames, qrow: Ghost(qrow) }
}

} // verus!
