// FRAMEWORK FILE: statement argument type of GenDB query crates over stored data (fixed query entry v4;
// gendb-runtime, `runtime/verus/gendb_arguments.rs`).
//
// Copied unchanged into every query crate as `crate::gendb_arguments`; storage crates do not carry it. Authors
// cannot edit it. Types only: no specifications, proofs, `assume`, `admit` or `external_body`. The trusted query shim
// (`shim_v4/query.rs`) builds these values from the host's argument descriptors and calls the verified
// `crate::gendb_entry::abi_query`; the verified binder `crate::gendb_params::bind_params` decides the declared
// parameter domain (`ParamRefused` outside it) before any author code runs.
//
// It extends the shared `crate::gendb_abi::ParamArg` (unchanged: that file belongs to every storage's dependency
// closure, and changing it would end the reuse of every admitted storage) by `text`.
use vstd::prelude::*;
use crate::gendb_abi::CivilDate;

verus! {

/// One statement argument, for one free parameter (slot order = ascending placeholder index).
/// `Int`: `integer`/`bigint` value; `Num`: `numeric(p, s)` coefficient at the declared scale `s`; `Date`: civil date;
/// `Text`: the bytes of a `text` value, viewed as `Literal::Text(bytes@)`. The host sends the UTF-8 bytes of the
/// requested string and keeps them unchanged until the calling process exits (like stored parts), so the slice is
/// valid for the whole call, including every worker the verified code joins before returning. Any byte string is
/// representable; the binder admits exactly those without a NUL byte (`spec::typing::text_ok`).
#[derive(Clone, Copy)]
pub enum QueryArg {
    Int(i64),
    Num(i128),
    Date(CivilDate),
    Text(&'static [u8]),
}

} // verus!
