//! The Q12 answer from per-ship-mode-entry sums: one row `[l_shipmode, high, low]` per dictionary entry with a
//! qualifying line, in dictionary order (the dictionary is sorted bytewise, which is the ORDER BY order of text), is
//! an allowed output of the statement on every database bound to the parts (`lemma_meets_rows`); a sum beyond int8
//! is the statement's error 22003 (`lemma_meets_overflow`); an error of `$3 + 1 year` is the statement's error when
//! the product is non-empty (`lemma_meets_date_err`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::{Answer, answer_meets, bound_db, outcome_ok};
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::runtime::QueryError;
use crate::exec::value::{EVal, view_row};
use crate::link::query::view_rows;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::int::*;
use crate::spec::scalar::compare;
use crate::spec::order::*;
use crate::spec::limits::int8_max;
use crate::spec::text::lex_cmp;
use crate::link::query::{gcount, gsum, QuerySpec};
use crate::query::{query_spec_at, param_domain};
use crate::bridge::relation::lemma_product_rows_elems;
use crate::stores::facts::interface::common::colfmt::*;
use crate::agent::common::isum::isum_caps;
use super::model::*;
use super::sql::*;
use super::bind::*;
use super::joinsum::*;

verus! {

/// The sums `hs` (high) and `ls` (low) are the normal form's group sums of every ship-mode entry.
pub open spec fn totals_ok(db: Database, ps: Seq<Literal>, hi: int, mo: Seq<u64>, my: Seq<u8>, hs: Seq<usize>,
    ls: Seq<usize>) -> bool {
    &&& hs.len() == mo.len() - 1
    &&& ls.len() == mo.len() - 1
    &&& forall|d: int| 0 <= d < hs.len() ==>
            #[trigger] hs[d] as int == gsum(q12_g(prm_of(ps, hi)), xs_of(db), key_d(mo, my, d), 0)
    &&& forall|d: int| 0 <= d < ls.len() ==>
            #[trigger] ls[d] as int == gsum(q12_g(prm_of(ps, hi)), xs_of(db), key_d(mo, my, d), 1)
}

/// Every sum fits int8.
pub open spec fn sums_fit(hs: Seq<usize>, ls: Seq<usize>) -> bool {
    &&& forall|d: int| 0 <= d < hs.len() ==> #[trigger] hs[d] <= int8_max()
    &&& forall|d: int| 0 <= d < ls.len() ==> #[trigger] ls[d] <= int8_max()
}

/// The entries `ds` are exactly the entries with a qualifying line (a nonzero sum), in increasing order.
pub open spec fn entries_ok(hs: Seq<usize>, ls: Seq<usize>, ds: Seq<int>) -> bool {
    &&& forall|i: int| 0 <= i < ds.len() ==> 0 <= #[trigger] ds[i] < hs.len() && hs[ds[i]] + ls[ds[i]] > 0
    &&& forall|i: int, j: int| 0 <= i < j < ds.len() ==> #[trigger] ds[i] < #[trigger] ds[j]
    &&& forall|d: int| 0 <= d < hs.len() && #[trigger] hs[d] + ls[d] > 0 ==> ds.contains(d)
}

/// The output row of ship-mode entry `d`.
pub open spec fn entry_row(mo: Seq<u64>, my: Seq<u8>, hs: Seq<usize>, ls: Seq<usize>, d: int) -> Row {
    seq![Val::Text(text_of(mo, my, d)), Val::Int(hs[d] as int), Val::Int(ls[d] as int)]
}

proof fn lemma_sorted_out(mo: Seq<u64>, my: Seq<u8>, hs: Seq<usize>, ls: Seq<usize>, ds: Seq<int>, out: Seq<Row>)
    requires
        dict_sorted(mo, my, mo.len() - 1),
        hs.len() == mo.len() - 1,
        entries_ok(hs, ls, ds),
        out.len() == ds.len(),
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == entry_row(mo, my, hs, ls, ds[i]),
    ensures sorted_by(order_keys(), out),
{
    let k = mo.len() - 1;
    assert forall|i: int, j: int| 0 <= i < j < out.len() implies keys_cmp(order_keys(), #[trigger] out[i], #[trigger] out[j]) <= 0 by {
        let (a, b) = (text_of(mo, my, ds[i]), text_of(mo, my, ds[j]));
        lemma_dict_order(mo, my, k, ds[i], ds[j]);
        assert(out[i][0] == Val::Text(a) && out[j][0] == Val::Text(b));
        assert(compare(Val::Text(a), Val::Text(b)) == Some(lex_cmp(a, b)));
        let key = order_keys()[0];
        assert(key_cmp(key, out[i], out[j]) == lex_cmp(a, b));
        assert(keys_cmp(order_keys(), out[i], out[j]) == key_cmp(key, out[i], out[j]));
    }
}

/// The product of the FROM tables is empty unless both stored relations have rows.
pub proof fn lemma_full_len(db: Database)
    requires db_ok(db),
    ensures full_rows(db).len() > 0 ==> orel_of(db).len() > 0 && lrel_of(db).len() > 0,
{
    lemma_product_rows_elems(db.tables[1], db.tables[0]);
    lemma_stored_positions(db);
    crate::stores::facts::declaration::lemma_stored_relations(db);
    let (a, b) = (db.tables[1].len() as int, db.tables[0].len() as int);
    if a == 0 || b == 0 {
        assert(a * b == 0) by (nonlinear_arith) requires a == 0 || b == 0;
    }
}

/// Every group sum of the normal form fits int8 when the entries' sums do.
proof fn lemma_caps(db: Database, parts: Seq<PartView>, c: Cols, po: Seq<u64>, py: Seq<u8>, mo: Seq<u64>, my: Seq<u8>,
    ps: Seq<Literal>, hi: int, hs: Seq<usize>, ls: Seq<usize>)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
        dicts_from_parts(parts, po, py, mo, my),
        totals_ok(db, ps, hi, mo, my, hs, ls),
        sums_fit(hs, ls),
    ensures
        isum_caps(q12_g(prm_of(ps, hi)), xs_of(db)),
{
    let g = q12_g(prm_of(ps, hi));
    let xs = xs_of(db);
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() implies int_in_range(IntKind::Int8, #[trigger] gsum(g, xs, k, j)) by {
        lemma_count_sums(prm_of(ps, hi), xs, k);
        assert(g.aggs.len() == 2);
        if gcount(g, xs, k) > 0 {
            lemma_keys_complete(db, parts, c, po, py, mo, my, prm_of(ps, hi), k);
            let d = choose|d: int| 0 <= d < mo.len() - 1 && k == key_d(mo, my, d);
            assert(hs[d] as int == gsum(g, xs, key_d(mo, my, d), 0));
            assert(ls[d] as int == gsum(g, xs, key_d(mo, my, d), 1));
        }
    }
}

/// The answer rows are an allowed output on database `db`.
pub proof fn lemma_rows_answer(db: Database, parts: Seq<PartView>, c: Cols, po: Seq<u64>, py: Seq<u8>, mo: Seq<u64>,
    my: Seq<u8>, ps: Seq<Literal>, hi: int, hs: Seq<usize>, ls: Seq<usize>, ds: Seq<int>, out: Seq<Row>)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
        dicts_from_parts(parts, po, py, mo, my),
        param_domain(ps),
        full_rows(db).len() > 0 ==> hi_ok(lo_of(ps), hi),
        totals_ok(db, ps, hi, mo, my, hs, ls),
        sums_fit(hs, ls),
        entries_ok(hs, ls, ds),
        out.len() == ds.len(),
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == entry_row(mo, my, hs, ls, ds[i]),
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    let prm = prm_of(ps, hi);
    let g = q12_g(prm);
    let xs = xs_of(db);
    let k = mo.len() - 1;
    lemma_rows_model(db, parts, c, po, py, mo, my);
    lemma_caps(db, parts, c, po, py, mo, my, ps, hi, hs, ls);
    lemma_body(db, ps, hi);
    let ks = ds.map_values(|d: int| key_d(mo, my, d));
    assert forall|i: int, j: int| 0 <= i < ks.len() && 0 <= j < ks.len() && i != j implies ks[i] != ks[j] by {
        if i < j {
            lemma_dict_distinct(mo, my, k, ds[i], ds[j]);
        } else {
            lemma_dict_distinct(mo, my, k, ds[j], ds[i]);
        }
        assert(ks[i][0] != ks[j][0]);
    }
    assert(ks.no_duplicates());
    assert forall|kr: Row| #[trigger] ks.contains(kr) <==> gcount(g, xs, kr) > 0 by {
        lemma_count_sums(prm, xs, kr);
        if ks.contains(kr) {
            let i = choose|i: int| 0 <= i < ks.len() && ks[i] == kr;
            assert(hs[ds[i]] as int == gsum(g, xs, key_d(mo, my, ds[i]), 0));
            assert(ls[ds[i]] as int == gsum(g, xs, key_d(mo, my, ds[i]), 1));
        }
        if gcount(g, xs, kr) > 0 {
            lemma_keys_complete(db, parts, c, po, py, mo, my, prm, kr);
            let d = choose|d: int| 0 <= d < k && kr == key_d(mo, my, d);
            assert(hs[d] as int == gsum(g, xs, key_d(mo, my, d), 0));
            assert(ls[d] as int == gsum(g, xs, key_d(mo, my, d), 1));
            assert(ds.contains(d));
            let i = choose|i: int| 0 <= i < ds.len() && ds[i] == d;
            assert(ks[i] == kr);
        }
    }
    assert forall|i: int| 0 <= i < ks.len() implies (#[trigger] ks[i]).len() == 1 by {}
    assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i] == group_row(g, xs, ks[i]) by {
        let d = ds[i];
        assert(hs[d] as int == gsum(g, xs, key_d(mo, my, d), 0));
        assert(ls[d] as int == gsum(g, xs, key_d(mo, my, d), 1));
        assert(out[i] =~= group_row(g, xs, ks[i]));
    }
    lemma_sorted_out(mo, my, hs, ls, ds, out);
    lemma_answer(db, ps, hi, ks, out);
}

/// A sum beyond int8 is the statement's error 22003 on database `db`.
pub proof fn lemma_sum_overflow(db: Database, parts: Seq<PartView>, mo: Seq<u64>, my: Seq<u8>, ps: Seq<Literal>,
    hi: int, hs: Seq<usize>, ls: Seq<usize>, d: int)
    requires
        bound(db, parts),
        param_domain(ps),
        full_rows(db).len() > 0 ==> hi_ok(lo_of(ps), hi),
        totals_ok(db, ps, hi, mo, my, hs, ls),
        0 <= d < hs.len(),
        hs[d] > int8_max() || ls[d] > int8_max(),
    ensures
        ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)),
{
    let prm = prm_of(ps, hi);
    let g = q12_g(prm);
    let xs = xs_of(db);
    let kd = key_d(mo, my, d);
    lemma_count_sums(prm, xs, kd);
    let j0 = if hs[d] > int8_max() { 0int } else { 1int };
    assert(hs[d] as int == gsum(g, xs, kd, 0));
    assert(ls[d] as int == gsum(g, xs, kd, 1));
    lemma_body_sum_err(db, ps, hi, kd, j0);
}

// ------------------------------------------------------------------------------------------------ every database

/// The facts parts the query reads: storage `li_okmode`'s first 75 parts (facts' parts, kept unchanged through
/// li_okruns).
pub open spec fn fparts(sv: StoresView) -> Seq<PartView> {
    sv.li_okmode.subrange(0, crate::stores::li_okruns::interface::FACTS_PARTS as int)
}

/// li_okmode's stored relations are facts' (the same declaration).
pub proof fn lemma_same_relations(db: Database)
    ensures crate::stores::li_okmode::declaration::stored_relations(db)
        == crate::stores::facts::declaration::stored_relations(db),
{
    assert(crate::stores::li_okmode::declaration::stored_cols_t0() =~= crate::stores::facts::declaration::stored_cols_t0());
    assert(crate::stores::li_okmode::declaration::stored_cols_t1() =~= crate::stores::facts::declaration::stored_cols_t1());
    assert(crate::stores::li_okmode::declaration::stored_relations(db)
        =~= crate::stores::facts::declaration::stored_relations(db));
}

/// The entry's `bound_db` gives `bound` over the facts parts of storage `li_okmode`, li_okruns' run facts over its
/// first 76 parts, and li_okmode's bitmaps.
pub proof fn lemma_bound(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        bound(db, fparts(sv)),
        crate::stores::li_okmode::interface::represents(sv.li_okmode,
            crate::stores::facts::declaration::stored_relations(db)),
        crate::stores::li_okruns::interface::represents(
            crate::stores::li_okmode::interface::okruns_parts(sv.li_okmode),
            crate::stores::facts::declaration::stored_relations(db)),
{
    lemma_same_relations(db);
    let p76 = crate::stores::li_okmode::interface::okruns_parts(sv.li_okmode);
    assert(p76.subrange(0, crate::stores::li_okruns::interface::FACTS_PARTS as int) =~= fparts(sv));
}

/// li_okruns' run starts (part 75 of li_okmode) satisfy the model's run facts: its l_orderkey decoding is the
/// model's.
pub proof fn lemma_starts_model(db: Database, sv: StoresView, c: Cols)
    requires
        bound_db(sv, db),
        cols_from_parts(c, fparts(sv)),
    ensures
        sv.li_okmode.len() == crate::stores::li_okmode::interface::LI_OKMODE_PARTS,
        sv.li_okmode[crate::stores::li_okruns::interface::RUN_STARTS as int] is U32,
        super::runs::starts_ok(c, u32s(sv.li_okmode[crate::stores::li_okruns::interface::RUN_STARTS as int])),
{
    use crate::stores::li_okruns::interface as lr;
    lemma_bound(sv, db);
    let parts = crate::stores::li_okmode::interface::okruns_parts(sv.li_okmode);
    let fp = fparts(sv);
    let st = lr::starts(parts);
    assert(lr::runs_ok(parts));
    assert(parts[lr::RUN_STARTS as int] == sv.li_okmode[lr::RUN_STARTS as int]);
    assert(parts[p_ll()] == fp[p_ll()]);
    assert(parts[p_lkc()] == fp[p_lkc()]);
    assert(parts[p_lkb()] == fp[p_lkb()]);
    assert(lr::li_rows(parts) == c.n_l);
    let sbs = lr::li_bsize(parts);
    assert(sbs == u64s(fp[p_ll()])[1]);
    assert forall|j: int| 0 <= j < c.n_l implies #[trigger] lr::okey_at(parts, j) == lkey(c, j) by {
        lemma_bs_group(c.bs_l as int, sbs, c.n_l as int, j);
    }
    assert forall|k: int| 0 <= k < st.len() - 1 implies #[trigger] super::runs::run_wf(c, st, k) by {
        assert(lr::run_ok(parts, k));
        let a = st[k] as int;
        let b = st[k + 1] as int;
        assert forall|j: int| a <= j < b implies #[trigger] lkey(c, j) == lkey(c, a) by {
            assert(lr::okey_at(parts, j) == lr::okey_at(parts, a));
            assert(lr::okey_at(parts, j) == lkey(c, j));
            assert(lr::okey_at(parts, a) == lkey(c, a));
        }
        if b < c.n_l {
            assert(lr::okey_at(parts, b) == lkey(c, b));
            assert(lr::okey_at(parts, b - 1) == lkey(c, b - 1));
        }
    }
}

/// li_okmode's bitmaps over the model: with words present (`nw > 0`), the run-start bitmap marks the model's run
/// starts and l_shipmode bitmap `k` the rows of mode entry `k`.
pub proof fn lemma_bits_model(db: Database, sv: StoresView, c: Cols, b: super::runs::Bits)
    requires
        bound_db(sv, db),
        cols_from_parts(c, fparts(sv)),
        b.run@ == u64s(sv.li_okmode[crate::stores::li_okmode::interface::RUN_BITS as int]),
        b.mode@ == u64s(sv.li_okmode[crate::stores::li_okmode::interface::MODE_BITS as int]),
        b.nw == b.run@.len(),
        b.nw > 0,
        b.nm == u64s(sv.li_okmode[crate::stores::li_okmode::interface::OKM_LAYOUT as int])[1],
    ensures super::runs::bits_ok(c, b),
{
    use crate::stores::li_okruns::interface as lr;
    use crate::stores::li_okmode::interface as om;
    lemma_bound(sv, db);
    let parts = sv.li_okmode;
    let fp = fparts(sv);
    assert(om::okm_ok(parts));
    assert(om::n_words(parts) == b.nw);
    assert(parts[p_ll()] == fp[p_ll()]);
    assert(parts[p_lkc()] == fp[p_lkc()]);
    assert(parts[p_lkb()] == fp[p_lkb()]);
    assert(parts[p_lmc()] == fp[p_lmc()]);
    assert(parts[p_lmb()] == fp[p_lmb()]);
    assert(om::n_rows(parts) == c.n_l);
    let sbs = lr::li_bsize(parts);
    assert(sbs == u64s(fp[p_ll()])[1]);
    assert forall|j: int| 0 <= j < c.n_l implies #[trigger] lr::okey_at(parts, j) == lkey(c, j) by {
        lemma_bs_group(c.bs_l as int, sbs, c.n_l as int, j);
    }
    assert forall|j: int| 0 <= j < c.n_l implies #[trigger] om::mode_at(parts, j) == lmode(c, j) by {
        lemma_bs_group(c.bs_l as int, sbs, c.n_l as int, j);
    }
    assert forall|j: int| 0 <= j < c.n_l implies #[trigger] super::runs::run_bit(b, j) == super::runs::lstart(c, j) by {
        assert(om::run_bit_ok(parts, j));
        if j > 0 {
            assert(lr::okey_at(parts, j - 1) == lkey(c, j - 1));
        }
        assert(lr::okey_at(parts, j) == lkey(c, j));
    }
    assert forall|k: int, j: int| 0 <= k < b.nm && 0 <= j < c.n_l implies
        #[trigger] super::runs::mode_bit(b, k, j) == (lmode(c, j) == k) by {
        assert(om::mode_bit_ok(parts, k, j));
        assert(om::mode_at(parts, j) == lmode(c, j));
    }
}

/// On a non-empty product, an error of `$3 + 1 year` answers every bound database.
pub proof fn lemma_meets_date_err(sv: StoresView, ps: Seq<Literal>, e: SqlError)
    requires
        param_domain(ps),
        parts_shape(fparts(sv)),
        u64s(fparts(sv)[p_ol()])[0] > 0,
        u64s(fparts(sv)[p_ll()])[0] > 0,
        hi_value(lo_of(ps)) == Err::<int, SqlError>(e),
    ensures
        answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::SqlError(e))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(e))) by {
        lemma_bound(sv, db);
        lemma_parts_shape(db, fparts(sv));
        lemma_stored_positions(db);
        crate::stores::facts::declaration::lemma_stored_relations(db);
        lemma_product_rows_elems(db.tables[1], db.tables[0]);
        let (a, b) = (db.tables[1].len() as int, db.tables[0].len() as int);
        assert(a * b > 0) by (nonlinear_arith) requires a > 0, b > 0;
        lemma_body_date_err(db, ps);
    }
}

/// The model's counts over every stored lineitem row are the group sums of every bound database.
pub proof fn lemma_meets_totals(sv: StoresView, c: Cols, w: Win, po: Seq<u64>, py: Seq<u8>, mo: Seq<u64>, my: Seq<u8>,
    ps: Seq<Literal>, hi: int, hs: Seq<usize>, ls: Seq<usize>)
    requires
        cols_from_parts(c, fparts(sv)),
        dicts_from_parts(fparts(sv), po, py, mo, my),
        win_matches(w, prm_of(ps, hi), po, py, mo, my),
        keys_distinct(c),
        hs.len() == mo.len() - 1,
        ls.len() == mo.len() - 1,
        forall|d: int| 0 <= d < hs.len() ==> #[trigger] hs[d] as int == cnt(c, w, 0, d, 0, c.n_l as int),
        forall|d: int| 0 <= d < ls.len() ==> #[trigger] ls[d] as int == cnt(c, w, 1, d, 0, c.n_l as int),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> totals_ok(db, ps, hi, mo, my, hs, ls),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies totals_ok(db, ps, hi, mo, my, hs, ls) by {
        lemma_bound(sv, db);
        assert forall|d: int| 0 <= d < hs.len() implies #[trigger] hs[d] as int
            == gsum(q12_g(prm_of(ps, hi)), xs_of(db), key_d(mo, my, d), 0) by {
            lemma_gsum_cnt(db, fparts(sv), c, w, prm_of(ps, hi), po, py, mo, my, 0, d);
        }
        assert forall|d: int| 0 <= d < ls.len() implies #[trigger] ls[d] as int
            == gsum(q12_g(prm_of(ps, hi)), xs_of(db), key_d(mo, my, d), 1) by {
            lemma_gsum_cnt(db, fparts(sv), c, w, prm_of(ps, hi), po, py, mo, my, 1, d);
        }
    }
}

/// A sum beyond int8 answers every bound database with error 22003.
pub proof fn lemma_meets_overflow(sv: StoresView, mo: Seq<u64>, my: Seq<u8>, ps: Seq<Literal>, hi: int,
    hs: Seq<usize>, ls: Seq<usize>, d: int)
    requires
        param_domain(ps),
        parts_shape(fparts(sv)),
        u64s(fparts(sv)[p_ol()])[0] > 0 && u64s(fparts(sv)[p_ll()])[0] > 0 ==> hi_ok(lo_of(ps), hi),
        forall|db: Database| #[trigger] bound_db(sv, db) ==> totals_ok(db, ps, hi, mo, my, hs, ls),
        0 <= d < hs.len(),
        hs[d] > int8_max() || ls[d] > int8_max(),
    ensures
        answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))) by {
        lemma_bound(sv, db);
        lemma_parts_shape(db, fparts(sv));
        lemma_full_len(db);
        lemma_sum_overflow(db, fparts(sv), mo, my, ps, hi, hs, ls, d);
    }
}

/// The answer rows answer every bound database.
pub proof fn lemma_meets_rows(sv: StoresView, c: Cols, po: Seq<u64>, py: Seq<u8>, mo: Seq<u64>, my: Seq<u8>,
    ps: Seq<Literal>, hi: int, hs: Seq<usize>, ls: Seq<usize>, ds: Seq<int>, rows: Vec<Vec<EVal>>)
    requires
        cols_from_parts(c, fparts(sv)),
        dicts_from_parts(fparts(sv), po, py, mo, my),
        param_domain(ps),
        u64s(fparts(sv)[p_ol()])[0] > 0 && u64s(fparts(sv)[p_ll()])[0] > 0 ==> hi_ok(lo_of(ps), hi),
        forall|db: Database| #[trigger] bound_db(sv, db) ==> totals_ok(db, ps, hi, mo, my, hs, ls),
        sums_fit(hs, ls),
        entries_ok(hs, ls, ds),
        rows@.len() == ds.len(),
        forall|i: int| 0 <= i < rows@.len() ==> #[trigger] view_row(rows@[i]@) == entry_row(mo, my, hs, ls, ds[i]),
    ensures
        answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Rows(rows))),
{
    crate::link::outcome::lemma_view_rows(rows@);
    let out = view_rows(rows@);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
        lemma_bound(sv, db);
        lemma_parts_shape(db, fparts(sv));
        lemma_full_len(db);
        lemma_rows_answer(db, fparts(sv), c, po, py, mo, my, ps, hi, hs, ls, ds, out);
    }
}

} // verus!
