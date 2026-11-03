//! The fast path from the matching part keys to the qualifying supplier keys (`fast_supp`): the key bitmaps
//! (`keys`), one parallel scan of partsupp and lineitem against them whose outputs are split into part-key buckets
//! (`scan`, `bucket`), the decisions of the matching partsupp rows per bucket (`decide`), and the set of their
//! supplier keys (`supp`). It returns `None` when a layout fact it relies on fails (keys outside the bitmap range, a
//! bucket outgrowing its region, a bucket's partsupp rows not in ascending part-key order); the query then takes the
//! general path.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::tables::*;
use crate::agent::cols::*;
use crate::agent::keys::*;
use crate::agent::pspass::*;
use crate::agent::scan::*;
use crate::agent::decide::*;
use crate::agent::common::buckets::{bk, bucket_mult};
use crate::agent::normal::in_part;
use crate::agent::common::bitset::wbit;
use crate::agent::supp::*;
use crate::agent::den_li::sizes_ok;

verus! {

/// Buckets of a serial call: small enough buckets that a bucket's slots stay in a core's cache.
pub const NB_SERIAL: usize = 64;

/// The qualifying supplier keys by the fast path; `Ok(None)` when its layout facts fail.
pub fn fast_supp(c: &Cols, keys: &Vec<i64>, dlo: i32, dhi: i32, workers: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<Option<SuppSet>, WorkerFailure>)
    requires
        cols_ok(*c, sv), model_ok(sv), sizes_ok(sv), 1 <= workers <= MAX_WORKERS,
        keys_decide(ints(keys@), sv, ps),
    ensures r matches Ok(Some(ss)) ==> supp_ok(ss, sv, ps, dlo as int, dhi as int),
{
    let ghost ks = ints(keys@);
    // the output buffers hold three values per row
    if c.nl > usize::MAX / 4 || c.nps > usize::MAX / 4 {
        return Ok(None);
    }
    let kb = match build_keybits(keys) {
        Some(kb) => kb,
        None => { return Ok(None); },
    };
    // one bucket per worker (a serial call: NB_SERIAL buckets, decided one after another)
    let nb = if workers == 1 { NB_SERIAL } else { workers };
    let km = if kb.kmax == 0 { 1 } else { kb.kmax };
    let bm = bucket_mult(km, nb);
    proof {
        // every matching part key lies in the bitmap's range, so in a bucket below nb
        assert forall|v: int| #[trigger] in_part(sv, ps, v) implies bk(v as i64, bm) < nb by {
            assert(ks.contains(v));
            assert(wbit(kb.bits@, v));
            let w = v as u64;
            assert(w < km);
            assert((w as i64) == (v as i64));
            assert(bk(w as i64, bm) < nb);
        }
    }
    let outs = match scan_pass(c, Arc::new(kb), dlo, dhi, workers, nb, bm, dispatch, Ghost(sv), Ghost(ps), Ghost(ks)) {
        Ok(o) => o,
        Err(e) => { return Err(e); },
    };
    let res = match decide_pass(outs, workers, workers, nb, bm, dispatch, Ghost(sv), Ghost(ps), Ghost(ks), Ghost(dlo as int), Ghost(dhi as int)) {
        Ok(Some(r)) => r,
        Ok(None) => { return Ok(None); },
        Err(e) => { return Err(e); },
    };
    let ss = supp_from_decisions(&res, nb, bm, Ghost(sv), Ghost(ps), Ghost(dlo as int), Ghost(dhi as int));
    Ok(Some(ss))
}

} // verus!
