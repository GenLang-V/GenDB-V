// FRAMEWORK FILE: verified column-domain decisions of the v3 entry (`verification/obligations/gendb_entry/source_check.rs`).
//
// Copied unchanged into every v3 candidate crate as `crate::gendb_entry::source_check`. Authors cannot edit
// it; they may call it. Checked by Verus with `--no-cheating` together with the candidate; no `assume`,
// `admit` or `external_body`.
//
// The generated `crate::gendb_source` states the input domain of the delivered source columns as the SQL
// column domain of the declared schema (`spec::typing::value_in_column`: integer ranges, numeric precision
// and scale, valid dates, text without NUL bytes within its declared character length, canonical `char(n)`).
// `abi_build` decides that domain with these functions before the author's builder runs, so the builder
// receives it as a precondition and a database in `db_wf` never yields `InvalidInput`
// (`gendb_entry::theorem_build_total`).
//
// Value views of the ABI element kinds (also used by `gendb_source::table_t{j}`):
// - I32 as `integer` / I64 as `bigint`: `Val::Int(x)`;
// - I128 as `numeric(p, s)`: `Val::Num { coeff: x, scale: s }`;
// - I32 as `date` (Date32, days since 1970-01-01): `Val::Date(x - 10957)` (PostgreSQL days since 2000-01-01);
// - Utf8: `Val::Text(text_at(column, i))`.
use vstd::prelude::*;
use crate::spec::value::Val;
use crate::spec::types::{Column as SqlColumn, SqlType};
use crate::spec::typing::{value_in_column, text_ok, utf8_chars};
use crate::spec::numeric::{abs, pow10};
use crate::spec::int::{int_in_range, IntKind};
use crate::exec::numeric::pow10_exec;
use crate::link::query::{TextCol, TextView, text_at, text_wf};
use super::work::text_bytes;

verus! {

/// Date32 (days since 1970-01-01) as a VERUS_SQL date (days since 2000-01-01).
pub open spec fn date32_val(x: i32) -> Val {
    Val::Date(x as int - 10957)
}

pub open spec fn int32_values_in(c: Seq<i32>, col: SqlColumn) -> bool {
    forall|i: int| 0 <= i < c.len() ==> #[trigger] value_in_column(Val::Int(c[i] as int), col)
}

pub open spec fn int64_values_in(c: Seq<i64>, col: SqlColumn) -> bool {
    forall|i: int| 0 <= i < c.len() ==> #[trigger] value_in_column(Val::Int(c[i] as int), col)
}

pub open spec fn decimal_values_in(c: Seq<i128>, scale: nat, col: SqlColumn) -> bool {
    forall|i: int| 0 <= i < c.len() ==> #[trigger] value_in_column(Val::Num { coeff: c[i] as int, scale }, col)
}

pub open spec fn date32_values_in(c: Seq<i32>, col: SqlColumn) -> bool {
    forall|i: int| 0 <= i < c.len() ==> #[trigger] value_in_column(date32_val(c[i]), col)
}

pub open spec fn text_values_in(t: TextView, n: int, col: SqlColumn) -> bool {
    forall|i: int| 0 <= i < n ==> #[trigger] value_in_column(Val::Text(text_at(t, i)), col)
}

fn int_value_in(x: i64, col: SqlColumn) -> (b: bool)
    ensures b == value_in_column(Val::Int(x as int), col),
{
    match col.ty {
        SqlType::Int4 => -0x8000_0000i64 <= x && x <= 0x7fff_ffffi64,
        SqlType::Int8 => true,
        _ => false,
    }
}

pub fn int32_column_in(c: &[i32], col: SqlColumn) -> (b: bool)
    ensures b == int32_values_in(c@, col),
{
    let mut i: usize = 0;
    while i < c.len()
        invariant i <= c@.len(), forall|k: int| 0 <= k < i ==> #[trigger] value_in_column(Val::Int(c@[k] as int), col),
        decreases c@.len() - i,
    {
        if !int_value_in(c[i] as i64, col) {
            return false;
        }
        i = i + 1;
    }
    true
}

pub fn int64_column_in(c: &[i64], col: SqlColumn) -> (b: bool)
    ensures b == int64_values_in(c@, col),
{
    let mut i: usize = 0;
    while i < c.len()
        invariant i <= c@.len(), forall|k: int| 0 <= k < i ==> #[trigger] value_in_column(Val::Int(c@[k] as int), col),
        decreases c@.len() - i,
    {
        if !int_value_in(c[i], col) {
            return false;
        }
        i = i + 1;
    }
    true
}

/// `numeric(p, s)` columns of the ABI have `p <= 38` (an `i128` coefficient).
pub fn decimal_column_in(c: &[i128], scale: u32, col: SqlColumn) -> (b: bool)
    requires col.ty matches SqlType::Numeric { precision, .. } ==> precision <= 38,
    ensures b == decimal_values_in(c@, scale as nat, col),
{
    let (precision, s) = match col.ty {
        SqlType::Numeric { precision, scale } => (precision, scale),
        _ => {
            if c.len() == 0 {
                return true;
            }
            proof {
                assert(!value_in_column(Val::Num { coeff: c@[0] as int, scale: scale as nat }, col));
            }
            return false;
        },
    };
    if s != scale {
        if c.len() == 0 {
            return true;
        }
        proof {
            assert(!value_in_column(Val::Num { coeff: c@[0] as int, scale: scale as nat }, col));
        }
        return false;
    }
    let bound = match pow10_exec(precision) {
        Some(p) => p,
        None => {
            proof {
                crate::spec::numeric::lemma_pow10_monotone(precision as nat, 38);
                crate::spec::numeric::lemma_pow10_positive(precision as nat);
                assert(pow10(38) == 100000000000000000000000000000000000000) by (compute);
                assert(false);
            }
            return false;
        },
    };
    let mut i: usize = 0;
    while i < c.len()
        invariant
            i <= c@.len(),
            bound as int == pow10(precision as nat),
            col.ty == (SqlType::Numeric { precision, scale: s }),
            s == scale,
            forall|k: int| 0 <= k < i ==> #[trigger] value_in_column(Val::Num { coeff: c@[k] as int, scale: scale as nat }, col),
        decreases c@.len() - i,
    {
        let x = c[i];
        if x <= -bound || x >= bound {
            proof {
                assert(!value_in_column(Val::Num { coeff: c@[i as int] as int, scale: scale as nat }, col));
            }
            return false;
        }
        i = i + 1;
    }
    true
}

pub fn date32_column_in(c: &[i32], col: SqlColumn) -> (b: bool)
    ensures b == date32_values_in(c@, col),
{
    let is_date = match col.ty { SqlType::Date => true, _ => false };
    let mut i: usize = 0;
    while i < c.len()
        invariant i <= c@.len(), is_date == (col.ty is Date), forall|k: int| 0 <= k < i ==> #[trigger] value_in_column(date32_val(c@[k]), col),
        decreases c@.len() - i,
    {
        let x = c[i];
        // date_valid(x - 10957): -2451545 <= x - 10957 < 2147483494 - 2451545.
        if !is_date || x < -2440588 || x >= 2145042906 {
            proof {
                assert(!value_in_column(date32_val(c@[i as int]), col));
            }
            return false;
        }
        i = i + 1;
    }
    true
}

/// `text_ok`: no NUL byte.
fn no_nul(b: &[u8]) -> (r: bool)
    ensures r == text_ok(b@),
{
    let mut i: usize = 0;
    while i < b.len()
        invariant i <= b@.len(), forall|k: int| 0 <= k < i ==> #[trigger] b@[k] != 0u8,
        decreases b@.len() - i,
    {
        if b[i] == 0u8 {
            return false;
        }
        i = i + 1;
    }
    true
}

proof fn lemma_utf8_chars_step(b: Seq<u8>, i: int)
    requires 0 <= i < b.len(),
    ensures
        utf8_chars(b.subrange(0, i + 1)) == utf8_chars(b.subrange(0, i)) + if 0x80u8 <= b[i] < 0xC0u8 { 0nat } else { 1nat },
        utf8_chars(b.subrange(0, i)) <= i,
    decreases i,
{
    let s = b.subrange(0, i + 1);
    assert(s.drop_last() =~= b.subrange(0, i));
    assert(s.last() == b[i]);
    if i > 0 {
        lemma_utf8_chars_step(b, i - 1);
    } else {
        assert(b.subrange(0, 0) =~= Seq::<u8>::empty());
    }
}

/// `utf8_chars`: bytes that are not UTF-8 continuation bytes.
fn char_count(b: &[u8]) -> (r: u64)
    ensures r as nat == utf8_chars(b@),
{
    let mut n: u64 = 0;
    let mut i: usize = 0;
    proof {
        assert(b@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while i < b.len()
        invariant i <= b@.len(), n as nat == utf8_chars(b@.subrange(0, i as int)), n <= i,
        decreases b@.len() - i,
    {
        proof {
            lemma_utf8_chars_step(b@, i as int);
        }
        let x = b[i];
        if !(0x80u8 <= x && x < 0xC0u8) {
            n = n + 1;
        }
        i = i + 1;
    }
    proof {
        assert(b@.subrange(0, b@.len() as int) =~= b@);
    }
    n
}

fn text_value_in(c: &TextCol, i: usize, col: SqlColumn) -> (b: bool)
    requires
        i + 1 < c.offsets@.len(),
        0 <= c.offsets@[i as int],
        c.offsets@[i as int] <= c.offsets@[i + 1],
        c.offsets@[i + 1] <= c.bytes@.len(),
    ensures b == value_in_column(Val::Text(text_at(c@, i as int)), col),
{
    let bytes = text_bytes(c, i);
    match col.ty {
        SqlType::Text => no_nul(bytes),
        SqlType::Varchar { max_chars } => no_nul(bytes) && char_count(bytes) <= max_chars as u64,
        SqlType::Bpchar { len } => {
            let n = bytes.len();
            no_nul(bytes) && char_count(bytes) <= len as u64 && (n == 0 || bytes[n - 1] != 0x20u8)
        },
        _ => false,
    }
}

pub fn text_column_in(c: &TextCol, n: usize, col: SqlColumn) -> (b: bool)
    requires text_wf(c@, n as int),
    ensures b == text_values_in(c@, n as int, col),
{
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            text_wf(c@, n as int),
            forall|k: int| 0 <= k < i ==> #[trigger] value_in_column(Val::Text(text_at(c@, k)), col),
        decreases n - i,
    {
        assert(0 <= c.offsets@[i as int] <= c.offsets@[i + 1] <= c.bytes@.len());
        if !text_value_in(c, i, col) {
            return false;
        }
        i = i + 1;
    }
    true
}

} // verus!
