//! The calling thread's reads of the parts: `load_ctx` builds the worker context (every slice the kernel reads, with
//! `Ctx::wf`), `nation_slices`, `part_slices` and `supplier_text` the slices the calling thread reads itself.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::stores::part_nameidx::interface as pi;
use crate::stores::li_pkdate::interface as li;
use crate::stores::suppliers::interface::common::colfmt as cf;
use super::nf::*;
use super::bind_sp::*;
use super::bind_pl::*;
use super::sl::*;
use super::kctx::*;

verus! {

/// The nation keys named `$3` (`Ctx::wf_su`'s nation facts).
pub open spec fn natk_ok(sp: Seq<crate::gendb_entry::layout::PartView>, name: Seq<u8>, v: Seq<i64>) -> bool {
    &&& forall|i: int| 0 <= i < v.len() ==> #[trigger] sl_nat_ok(sp, name, v[i] as int)
    &&& forall|y: int| 0 <= y < tn(sp, 30) && nan(sp, y) == name ==> exists|i: int| 0 <= i < v.len() && #[trigger] v[i] == nak(sp, y)
}

/// The parameters of the partsupp position guess (`Ctx::guess`; any values are correct).
fn guess_params(spk: &[u32], spkb: &[i64], nps: usize, psbs: usize) -> (r: (i64, u64, u64)) {
    if nps > 0 && psbs > 0 && spkb.len() > 0 {
        let last = nps - 1;
        let gl = last / psbs;
        if gl < spkb.len() && last < spk.len() {
            let k0 = spkb[0] as i128 + spk[0] as i128;
            let kl = spkb[gl] as i128 + spk[last] as i128;
            if k0 >= i64::MIN as i128 && k0 <= i64::MAX as i128 && kl >= k0 && kl - k0 < 0x8000_0000 && nps <= 0x8000_0000 {
                return (k0 as i64, nps as u64, (kl - k0 + 1) as u64);
            }
        }
    }
    (0, 0, 0)
}

/// The context of the worker tasks.
pub fn load_ctx(stores: &mut Stores, Ghost(ps): Ghost<Seq<Literal>>, d0: i64, d1: i64, natk: Vec<i64>) -> (c: Ctx)
    requires
        sl_ok(old(stores)@),
        d0 == d0_of(ps),
        -0x1_0000_0000 <= d0 <= 0x1_0000_0000,
        -0x1_0000_0000 <= d1 <= 0x1_0000_0000,
        natk_ok(old(stores)@.suppliers, nname_of(ps), natk@),
    ensures
        final(stores)@ == old(stores)@,
        c.wf(),
        c.sv@ == old(stores)@, c.ps@ == ps, c.d1g@ == d1 as int,
{
    let ghost sv = stores@;
    let ghost pp = sv.part_nameidx;
    let ghost lp = sv.li_pkdate;
    let ghost sp = sv.suppliers;
    // part
    let np = stores.part_nameidx.part_len(pi::PA_PARTKEY_CODES);
    let pk = stores.part_nameidx.extent_u32(pi::PA_PARTKEY_CODES, 0, np);
    let npkb = stores.part_nameidx.part_len(pi::PA_PARTKEY_BASE);
    let pkb = stores.part_nameidx.extent_i64(pi::PA_PARTKEY_BASE, 0, npkb);
    let play = stores.part_nameidx.extent_u64(pi::PA_LAYOUT, 0, 2);
    let pbs = bsize_of(play[1]);
    proof {
        assert(pk@ =~= pi::u32s(pp[pi::PA_PARTKEY_CODES as int]));
        assert(pkb@ =~= pi::i64s(pp[pi::PA_PARTKEY_BASE as int]));
    }
    // partsupp
    let nps = stores.suppliers.part_len(2);
    let spk = stores.suppliers.extent_u32(2, 0, nps);
    let n3 = stores.suppliers.part_len(3);
    let spkb = stores.suppliers.extent_i64(3, 0, n3);
    let n4 = stores.suppliers.part_len(4);
    let ssk = stores.suppliers.extent_u32(4, 0, n4);
    let n5 = stores.suppliers.part_len(5);
    let sskb = stores.suppliers.extent_i64(5, 0, n5);
    let n6 = stores.suppliers.part_len(6);
    let sav = stores.suppliers.extent_u16(6, 0, n6);
    let n7 = stores.suppliers.part_len(7);
    let savb = stores.suppliers.extent_i64(7, 0, n7);
    let pslay = stores.suppliers.extent_u64(0, 0, 2);
    let psbs = bsize_of(pslay[1]);
    let kind = stores.suppliers.extent_u64(12, 0, 1);
    let sorted = kind[0] == 1;
    let (gk0, gnum, gden) = guess_params(spk, spkb, nps, psbs);
    proof {
        assert(spk@ =~= cf::u32s(sp[2]));
        assert(spkb@ =~= cf::i64s(sp[3]));
        assert(ssk@ =~= cf::u32s(sp[4]));
        assert(sskb@ =~= cf::i64s(sp[5]));
        assert(sav@ =~= u16s(sp[6]));
        assert(savb@ =~= cf::i64s(sp[7]));
    }
    // lineitem
    let nl = stores.li_pkdate.part_len(li::LI_PARTKEY_CODES);
    let lkey = stores.li_pkdate.extent_u32(li::LI_PARTKEY_CODES, 0, nl);
    let m7 = stores.li_pkdate.part_len(li::LI_PARTKEY_BASE);
    let lkeyb = stores.li_pkdate.extent_i64(li::LI_PARTKEY_BASE, 0, m7);
    let m8 = stores.li_pkdate.part_len(li::LI_SUPPKEY_CODES);
    let lsk = stores.li_pkdate.extent_u32(li::LI_SUPPKEY_CODES, 0, m8);
    let m9 = stores.li_pkdate.part_len(li::LI_SUPPKEY_BASE);
    let lskb = stores.li_pkdate.extent_i64(li::LI_SUPPKEY_BASE, 0, m9);
    let m12 = stores.li_pkdate.part_len(li::LI_QUANTITY_CODES);
    let lq = stores.li_pkdate.extent_u16(li::LI_QUANTITY_CODES, 0, m12);
    let m13 = stores.li_pkdate.part_len(li::LI_QUANTITY_BASE);
    let lqb = stores.li_pkdate.extent_i64(li::LI_QUANTITY_BASE, 0, m13);
    let m28 = stores.li_pkdate.part_len(li::LI_SHIPDATE_CODES);
    let ldt = stores.li_pkdate.extent_u16(li::LI_SHIPDATE_CODES, 0, m28);
    let m29 = stores.li_pkdate.part_len(li::LI_SHIPDATE_BASE);
    let ldtb = stores.li_pkdate.extent_i64(li::LI_SHIPDATE_BASE, 0, m29);
    let llay = stores.li_pkdate.extent_u64(li::LI_LAYOUT, 0, 2);
    let lbs = bsize_of(llay[1]);
    let meta = stores.li_pkdate.extent_i64(li::IDX_META, 0, 3);
    let idx = meta[0] == li::MODE_INDEX;
    let kmin = meta[1];
    let dbase = meta[2];
    let m76 = stores.li_pkdate.part_len(li::IDX_OFFS);
    let offs = stores.li_pkdate.extent_u32(li::IDX_OFFS, 0, m76);
    let m77 = stores.li_pkdate.part_len(li::IDX_ROWS);
    let irows = stores.li_pkdate.extent_u32(li::IDX_ROWS, 0, m77);
    let m78 = stores.li_pkdate.part_len(li::IDX_DATES);
    let idates = stores.li_pkdate.extent_u16(li::IDX_DATES, 0, m78);
    let nkeys = if m76 >= 1 { m76 - 1 } else { 0 };
    let lo = d0 as i128 - dbase as i128;
    let hi = d1 as i128 - dbase as i128;
    let dlo: i64 = if lo < -1 { -1 } else if lo > 65536 { 65536 } else { lo as i64 };
    let dhi: i64 = if hi < -1 { -1 } else if hi > 65536 { 65536 } else { hi as i64 };
    proof {
        assert(lkey@ =~= li::u32s(lp[li::LI_PARTKEY_CODES as int]));
        assert(lkeyb@ =~= li::i64s(lp[li::LI_PARTKEY_BASE as int]));
        assert(lsk@ =~= li::u32s(lp[li::LI_SUPPKEY_CODES as int]));
        assert(lskb@ =~= li::i64s(lp[li::LI_SUPPKEY_BASE as int]));
        assert(lq@ =~= li::u16s(lp[li::LI_QUANTITY_CODES as int]));
        assert(lqb@ =~= li::i64s(lp[li::LI_QUANTITY_BASE as int]));
        assert(ldt@ =~= li::u16s(lp[li::LI_SHIPDATE_CODES as int]));
        assert(ldtb@ =~= li::i64s(lp[li::LI_SHIPDATE_BASE as int]));
        assert(offs@ =~= li::idx_offs(lp));
        assert(irows@ =~= li::idx_rows(lp));
        assert(idates@ =~= li::idx_dates(lp));
        assert(meta@ =~= li::idx_meta(lp));
    }
    // supplier
    let ns = stores.suppliers.part_len(15);
    let suk = stores.suppliers.extent_u32(15, 0, ns);
    let n16 = stores.suppliers.part_len(16);
    let sukb = stores.suppliers.extent_i64(16, 0, n16);
    let n21 = stores.suppliers.part_len(21);
    let snk = stores.suppliers.extent_u8(21, 0, n21);
    let n22 = stores.suppliers.part_len(22);
    let snkb = stores.suppliers.extent_i64(22, 0, n22);
    let slay = stores.suppliers.extent_u64(13, 0, 2);
    let sbs = bsize_of(slay[1]);
    let sbase: i64 = if ns > 0 && n16 > 0 {
        let v = sukb[0] as i128 + suk[0] as i128;
        if v >= i64::MIN as i128 && v <= i64::MAX as i128 { v as i64 } else { 0 }
    } else {
        0
    };
    proof {
        assert(suk@ =~= cf::u32s(sp[15]));
        assert(sukb@ =~= cf::i64s(sp[16]));
        assert(snk@ =~= cf::u8s(sp[21]));
        assert(snkb@ =~= cf::i64s(sp[22]));
    }
    // the partsupp run layout of suppliers_psrun
    let run = stores.suppliers_psrun.extent_i64(crate::stores::suppliers_psrun::interface::RUN, 0, 2);
    let runok = run[0] >= 1 && run[0] <= 0x1_0000;
    let ratio: usize = if runok { run[0] as usize } else { 1 };
    let first: i64 = run[1];
    proof {
        assert(run@ =~= run_of(sv.suppliers_psrun).subrange(0, 2));
        assert(run@[0] == run_of(sv.suppliers_psrun)[0] && run@[1] == run_of(sv.suppliers_psrun)[1]);
    }
    let kind_su = stores.suppliers.extent_u64(29, 0, 1);
    let su_sorted = kind_su[0] == 1;
    let natn = natk.len();
    let psh = shift_of(pbs);
    let pssh = shift_of(psbs);
    let lsh = shift_of(lbs);
    let ssh = shift_of(sbs);
    let gmul: u64 = if gden > 0 && gnum % gden == 0 { gnum / gden } else { 0 };
    let mut c = Ctx {
        sv: Ghost(sv), ps: Ghost(ps), d1g: Ghost(d1 as int),
        np, pbs, psh, pk, pkb,
        nps, psbs, pssh, sorted, runok, ratio, first, gk0, gnum, gden, gmul, spk, spkb, ssk, sskb, sav, savb,
        nl, lbs, lsh, idx, kmin, nkeys, offs, irows, idates, dlo, dhi,
        lkey, lkeyb, lsk, lskb, lq, lqb, ldt, ldtb, d0, d1,
        ns, sbs, ssh, sbase, dense: false, suk, sukb, snk, snkb,
        natk, natn,
    };
    // dense supplier keys: sorted, distinct, from sbase to sbase + ns - 1
    if su_sorted && c.ns > 0 {
        let s0 = c.get_suk(0);
        let sl = c.get_suk(c.ns - 1);
        if s0 == c.sbase && sl as i128 == c.sbase as i128 + (c.ns as i128 - 1) {
            proof {
                assert(kind_su@[0] == su_kind(sp));
                lemma_dense(sp, c.sbase as int);
            }
            c.dense = true;
        }
    }
    c
}

/// Nation keys and names.
pub struct NationSlices {
    pub nk: &'static [u8],
    pub nkb: &'static [i64],
    pub nbs: usize,
    pub noffs: &'static [u64],
    pub nbytes: &'static [u8],
    pub nn: usize,
}

pub fn nation_slices(stores: &mut Stores) -> (r: NationSlices)
    requires sl_ok(old(stores)@),
    ensures
        final(stores)@ == old(stores)@,
        r.nn == tn(old(stores)@.suppliers, 30), r.nbs as int == bmin(tbs(old(stores)@.suppliers, 30)),
        r.nk@ == cf::u8s(old(stores)@.suppliers[32]), r.nkb@ == cf::i64s(old(stores)@.suppliers[33]),
        r.noffs@ == cf::u64s(old(stores)@.suppliers[34]), r.nbytes@ == cf::u8s(old(stores)@.suppliers[35]),
{
    let ghost sp = stores@.suppliers;
    let nn = stores.suppliers.part_len(32);
    let nk = stores.suppliers.extent_u8(32, 0, nn);
    let n33 = stores.suppliers.part_len(33);
    let nkb = stores.suppliers.extent_i64(33, 0, n33);
    let n34 = stores.suppliers.part_len(34);
    let noffs = stores.suppliers.extent_u64(34, 0, n34);
    let n35 = stores.suppliers.part_len(35);
    let nbytes = stores.suppliers.extent_u8(35, 0, n35);
    let lay = stores.suppliers.extent_u64(30, 0, 2);
    let nbs = bsize_of(lay[1]);
    proof {
        assert(nk@ =~= cf::u8s(sp[32]));
        assert(nkb@ =~= cf::i64s(sp[33]));
        assert(noffs@ =~= cf::u64s(sp[34]));
        assert(nbytes@ =~= cf::u8s(sp[35]));
    }
    NationSlices { nk, nkb, nbs, noffs, nbytes, nn }
}

/// Part names and the name order.
pub struct PartSlices {
    pub offs: &'static [u64],
    pub bytes: &'static [u8],
    pub perm: &'static [u32],
    pub np: usize,
}

pub fn part_slices(stores: &mut Stores) -> (r: PartSlices)
    requires sl_ok(old(stores)@),
    ensures
        final(stores)@ == old(stores)@,
        r.np == pi::n_rows(old(stores)@.part_nameidx),
        r.offs@ == pi::name_offs(old(stores)@.part_nameidx),
        r.bytes@ == pi::name_bytes(old(stores)@.part_nameidx),
        r.perm@ == pi::perm(old(stores)@.part_nameidx),
{
    let ghost pp = stores@.part_nameidx;
    let np = stores.part_nameidx.part_len(pi::PA_PARTKEY_CODES);
    let n25 = stores.part_nameidx.part_len(pi::PA_NAME_OFFS);
    let offs = stores.part_nameidx.extent_u64(pi::PA_NAME_OFFS, 0, n25);
    let n26 = stores.part_nameidx.part_len(pi::PA_NAME_BYTES);
    let bytes = stores.part_nameidx.extent_u8(pi::PA_NAME_BYTES, 0, n26);
    let n50 = stores.part_nameidx.part_len(pi::NAME_PERM);
    let perm = stores.part_nameidx.extent_u32(pi::NAME_PERM, 0, n50);
    proof {
        assert(offs@ =~= pi::name_offs(pp));
        assert(bytes@ =~= pi::name_bytes(pp));
        assert(perm@ =~= pi::perm(pp));
    }
    PartSlices { offs, bytes, perm, np }
}

/// Supplier names and addresses.
pub struct SupplierText {
    pub sno: &'static [u64],
    pub snb: &'static [u8],
    pub sao: &'static [u64],
    pub sab: &'static [u8],
}

pub fn supplier_text(stores: &mut Stores) -> (r: SupplierText)
    requires sl_ok(old(stores)@),
    ensures
        final(stores)@ == old(stores)@,
        r.sno@ == cf::u64s(old(stores)@.suppliers[17]), r.snb@ == cf::u8s(old(stores)@.suppliers[18]),
        r.sao@ == cf::u64s(old(stores)@.suppliers[19]), r.sab@ == cf::u8s(old(stores)@.suppliers[20]),
{
    let ghost sp = stores@.suppliers;
    let n17 = stores.suppliers.part_len(17);
    let sno = stores.suppliers.extent_u64(17, 0, n17);
    let n18 = stores.suppliers.part_len(18);
    let snb = stores.suppliers.extent_u8(18, 0, n18);
    let n19 = stores.suppliers.part_len(19);
    let sao = stores.suppliers.extent_u64(19, 0, n19);
    let n20 = stores.suppliers.part_len(20);
    let sab = stores.suppliers.extent_u8(20, 0, n20);
    proof {
        assert(sno@ =~= cf::u64s(sp[17]));
        assert(snb@ =~= cf::u8s(sp[18]));
        assert(sao@ =~= cf::u64s(sp[19]));
        assert(sab@ =~= cf::u8s(sp[20]));
    }
    SupplierText { sno, snb, sao, sab }
}

} // verus!
