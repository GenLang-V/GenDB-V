//! PostgreSQL constants of the value domains (PostgreSQL 18; the datetime constants are those of
//! `src/include/datatype/timestamp.h`, unchanged since PostgreSQL 10; the numeric ones are from `numeric.c`).
//! These are PostgreSQL's own type limits, not GenDB caps. The executable domain (`exec::domain`) is separate.
use vstd::prelude::*;

verus! {

/// `integer` (int4) range: `[-2^31, 2^31)`.
pub open spec fn int4_min() -> int { -0x8000_0000 }
pub open spec fn int4_max() -> int { 0x7fff_ffff }
/// `bigint` (int8) range: `[-2^63, 2^63)`.
pub open spec fn int8_min() -> int { -0x8000_0000_0000_0000 }
pub open spec fn int8_max() -> int { 0x7fff_ffff_ffff_ffff }

/// `numeric`: at most `NUMERIC_WEIGHT_MAX + 1 = 32768` base-10000 digits before the decimal point, i.e. an
/// absolute value below `10^131072`; a larger result is the error "value overflows numeric format" (22003).
pub open spec fn numeric_int_digits_max() -> nat { 131072 }
/// `numeric` display scale limit (`NUMERIC_DSCALE_MAX = 0x3FFF`). The typed fragment refuses static scales
/// above it (`spec::typing`), so the denotation never needs PostgreSQL's rounding at this limit.
pub open spec fn numeric_dscale_max() -> nat { 16383 }
/// `numeric(p, s)` typmod limit (`NUMERIC_MAX_PRECISION`).
pub open spec fn numeric_max_precision() -> nat { 1000 }
/// `varchar(n)` / `char(n)` typmod limit in characters (`MaxAttrSize` = 10 MiB, `anychar_typmod_in`: "length for
/// type varchar cannot exceed 10485760").
pub open spec fn char_length_max() -> nat { 10485760 }

/// Microseconds per day (`USECS_PER_DAY`).
pub const USECS_PER_DAY: i64 = 86_400_000_000;
/// Julian day of 2000-01-01 (`POSTGRES_EPOCH_JDATE`). Dates and timestamps are counted from this epoch, as in
/// PostgreSQL's `DateADT` and `Timestamp`.
pub open spec fn postgres_epoch_jdate() -> int { 2451545 }
/// Days from the Unix epoch 1970-01-01 to the PostgreSQL epoch 2000-01-01.
pub open spec fn unix_to_postgres_days() -> int { 10957 }
/// `date` range `[DATETIME_MIN_JULIAN - POSTGRES_EPOCH_JDATE, DATE_END_JULIAN - POSTGRES_EPOCH_JDATE)`.
pub open spec fn date_min() -> int { 0 - postgres_epoch_jdate() }
pub open spec fn date_end() -> int { 2147483494 - postgres_epoch_jdate() }
/// First date that no longer converts to `timestamp` (`TIMESTAMP_END_JULIAN - POSTGRES_EPOCH_JDATE`).
pub open spec fn timestamp_end_date() -> int { 109203528 - postgres_epoch_jdate() }
/// `timestamp` range `[MIN_TIMESTAMP, END_TIMESTAMP)` in microseconds since 2000-01-01 00:00:00.
pub open spec fn timestamp_min() -> int { -211813488000000000 }
pub open spec fn timestamp_end() -> int { 9223371331200000000 }

} // verus!
