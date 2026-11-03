//! The output rows: for a selected customer, `c_custkey, c_name, revenue, c_acctbal, n_name, c_address, c_phone,
//! c_comment` read through the storages' readers (`cust_row` of `agent::normal`), and zero-filled buffers.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::bound_db;
use crate::exec::value::{EVal, view_row};
use crate::link::query::text_at;
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_customer::declaration as cid;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_nation::declaration as nid;
use crate::agent::cols::*;
use crate::agent::normal::*;
use crate::agent::xcols::*;
use crate::agent::cagg::nation_of;

verus! {

/// `n` zeros (a fresh zeroed allocation).
pub fn zeros_i64(n: usize) -> (v: Vec<i64>)
    ensures v@.len() == n, forall|i: int| 0 <= i < n ==> #[trigger] v@[i] == 0,
{
    vec![0i64; n]
}

pub fn zeros_usize(n: usize) -> (v: Vec<usize>)
    ensures v@.len() == n, forall|i: int| 0 <= i < n ==> #[trigger] v@[i] == 0,
{
    vec![0usize; n]
}

/// A copy of the bytes of a text value.
pub fn to_vec(s: &[u8]) -> (v: Vec<u8>)
    ensures v@ == s@,
{
    let n = s.len();
    let mut v: Vec<u8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant n == s@.len(), i <= n, v@ == s@.subrange(0, i as int),
        decreases n - i,
    {
        v.push(s[i]);
        i = i + 1;
        assert(v@ =~= s@.subrange(0, i as int));
    }
    assert(s@.subrange(0, n as int) =~= s@);
    v
}

/// The output row of customer `a` (whose nation exists) with revenue `s` (scale 4).
pub fn out_row(stores: &mut Stores, c: &Cols, a: usize, s: i128, Ghost(db): Ghost<Database>) -> (row: Vec<EVal>)
    requires bound_db(old(stores)@, db), cols_ok(*c, old(stores)@), a < c.nc, natok(old(stores)@, a as int),
    ensures final(stores)@ == old(stores)@, view_row(row@) == cust_row(old(stores)@, a as int, s as int),
{
    let ghost sv = stores@;
    let n = match nation_of(c, a, Ghost(sv)) {
        Some(n) => n,
        None => {
            vstd::pervasive::unreached()
        },
    };
    proof {
        lemma_nat_row(sv, a as int);
        assert(nk(sv)[n as int] == nk(sv)[nat_row(sv, a as int)]);
        assert(n as int == nat_row(sv, a as int));
        lemma_parts_shape(sv, db);
        cid::lemma_stored_relations(db);
        nid::lemma_stored_relations(db);
    }
    let ghost rc = cid::stored_relations(db);
    let ghost rn = nid::stored_relations(db);
    let name = ci::read_c_name_at(&mut stores.flat_customer, a, Ghost(rc));
    let addr = ci::read_c_address_at(&mut stores.flat_customer, a, Ghost(rc));
    let phone = ci::read_c_phone_at(&mut stores.flat_customer, a, Ghost(rc));
    let comm = ci::read_c_comment_at(&mut stores.flat_customer, a, Ghost(rc));
    let acct = ci::read_c_acctbal(&mut stores.flat_customer, a, a + 1, Ghost(rc));
    let nname = ni::read_n_name_at(&mut stores.flat_nation, n, Ghost(rn));
    proof {
        assert(stores@ == sv);
        assert(rc[0][a as int] == ci::row_at(sv.flat_customer, a as int));
        assert(rn[0][n as int] == ni::row_at(sv.flat_nation, n as int));
        assert(rc[0][a as int + 0] == rc[0][a as int]);
    }
    let mut row: Vec<EVal> = Vec::new();
    row.push(EVal::Int(c.ck[a]));
    row.push(EVal::Text(to_vec(name)));
    row.push(EVal::Num { coeff: s, scale: 4 });
    row.push(EVal::Num { coeff: acct[0], scale: 2 });
    row.push(EVal::Text(to_vec(nname)));
    row.push(EVal::Text(to_vec(addr)));
    row.push(EVal::Text(to_vec(phone)));
    row.push(EVal::Text(to_vec(comm)));
    proof {
        assert(view_row(row@) =~= cust_row(sv, a as int, s as int));
    }
    row
}

} // verus!
