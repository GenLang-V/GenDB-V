//! The user's run controls: submission, provider-cost, retry and per-call wall-time guards, and exact dollars.
//!
//! Guards are user choices. When the user sets none, a request says `"unset"` explicitly; the controller never
//! invents a value, and there is no model-turn cap. `max_author_tool_turns` is a retired launch setting that is read
//! and preserved for historical records only.

use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::fmt;

/// Request spelling of an explicitly unset guard.
pub const UNSET_TEXT: &str = "unset";
/// In-memory value of an unset count guard.
pub const UNSET_COUNT: u32 = u32::MAX;
/// In-memory value of an unset seconds guard.
pub const UNSET_SECONDS: u64 = u64::MAX;

/// A dollar amount could not be parsed or summed exactly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MoneyError(pub &'static str);

impl fmt::Display for MoneyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0)
    }
}

impl std::error::Error for MoneyError {}

/// Exact US dollars with 18 decimal places, serialized as a decimal string. Arithmetic never uses binary floats.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Money(pub u128);

impl Money {
    /// Units per dollar.
    const SCALE: u128 = 1_000_000_000_000_000_000;
    /// An explicitly unset dollar guard (written `"unset"`): no provider-cost stop applies.
    pub const UNSET: Money = Money(u128::MAX);

    pub fn is_unset(self) -> bool {
        self == Self::UNSET
    }

    /// Remaining allowance of guard `self` after `spent`; an unset guard stays unset.
    pub fn remaining_after(self, spent: Money) -> Money {
        if self.is_unset() { self } else { Money(self.0.saturating_sub(spent.0)) }
    }

    /// `self - other`, zero when `other` is larger (a known overshoot below zero is none).
    pub fn saturating_sub(self, other: Money) -> Money {
        Money(self.0.saturating_sub(other.0))
    }

    /// Exact sum; unset absorbs (a sum involving an unset guard is unset).
    pub fn checked_sum(self, other: Money) -> Result<Money, MoneyError> {
        if self.is_unset() || other.is_unset() {
            return Ok(Self::UNSET);
        }
        self.0.checked_add(other.0).map(Money).ok_or(MoneyError("dollar total overflow"))
    }

    /// Parse a nonnegative decimal (optionally with an exponent, as provider receipts may print) or `"unset"`.
    /// More than 18 decimal places is refused rather than rounded.
    pub fn parse(text: &str) -> Result<Self, MoneyError> {
        if text == UNSET_TEXT {
            return Ok(Self::UNSET);
        }
        let (mantissa, exponent) = match text.split_once(['e', 'E']) {
            None => (text, 0i32),
            Some((mantissa, exponent)) => {
                (mantissa, exponent.parse::<i32>().map_err(|_| MoneyError("invalid dollar exponent"))?)
            }
        };
        if mantissa.starts_with('-') || mantissa.is_empty() {
            return Err(MoneyError("dollars must be nonnegative"));
        }
        let (whole, fraction) = mantissa.split_once('.').unwrap_or((mantissa, ""));
        if whole.is_empty() || !whole.chars().chain(fraction.chars()).all(|c| c.is_ascii_digit()) {
            return Err(MoneyError("invalid decimal dollars"));
        }
        let digits = format!("{whole}{fraction}").parse::<u128>().map_err(|_| MoneyError("dollars overflow"))?;
        // Scale digits (which carry `fraction.len()` decimal places) to 18 places.
        let shift = 18i64 + i64::from(exponent) - fraction.len() as i64;
        if !(-38..=38).contains(&shift) {
            return Err(MoneyError("dollar precision/range unsupported"));
        }
        let units = if shift >= 0 {
            digits.checked_mul(10u128.pow(shift as u32)).ok_or(MoneyError("dollars overflow"))?
        } else {
            let divisor = 10u128.pow((-shift) as u32);
            if digits % divisor != 0 {
                return Err(MoneyError("dollar precision exceeds 18 places"));
            }
            digits / divisor
        };
        Ok(Self(units))
    }

    /// Shortest exact decimal text (no trailing zeros), or `"unset"`.
    pub fn decimal(self) -> String {
        if self.is_unset() {
            return UNSET_TEXT.into();
        }
        let (whole, fraction) = (self.0 / Self::SCALE, self.0 % Self::SCALE);
        if fraction == 0 {
            whole.to_string()
        } else {
            format!("{whole}.{fraction:018}").trim_end_matches('0').to_string()
        }
    }
}

impl Serialize for Money {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.decimal())
    }
}

impl<'de> Deserialize<'de> for Money {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Self::parse(&String::deserialize(deserializer)?).map_err(serde::de::Error::custom)
    }
}

/// How the dollar guard is enforced.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum SpendPolicy {
    /// A hard cap; only a transport that can enforce one (`Capability::hard_usd_cap`) accepts it.
    StrictUsd,
    /// Historical spelling of the provider-cost stop guard: no new call starts once reported cost plus outstanding
    /// reservations reach the guard. It is not a hard cap.
    EstimatedUsd,
}

/// JSON of a count guard as written in requests: a number or `"unset"`.
pub fn count_guard(value: u32) -> Value {
    if value == UNSET_COUNT { Value::from(UNSET_TEXT) } else { Value::from(value) }
}

/// Prompt text of a count guard.
pub fn count_guard_text(value: u32) -> String {
    if value == UNSET_COUNT { UNSET_TEXT.into() } else { value.to_string() }
}

/// Serde for a numeric guard: a JSON number, or `"unset"` (stored as the type's maximum).
mod guard {
    use serde::{Deserialize, Deserializer, Serializer};

    pub trait Unset: Copy + PartialEq + Into<u64> + TryFrom<u64> {
        const UNSET: Self;
    }
    impl Unset for u32 {
        const UNSET: u32 = super::UNSET_COUNT;
    }
    impl Unset for u64 {
        const UNSET: u64 = super::UNSET_SECONDS;
    }

    pub fn serialize<S: Serializer, T: Unset>(value: &T, serializer: S) -> Result<S::Ok, S::Error> {
        if *value == T::UNSET { serializer.serialize_str(super::UNSET_TEXT) } else { serializer.serialize_u64((*value).into()) }
    }

    pub fn deserialize<'de, D: Deserializer<'de>, T: Unset>(deserializer: D) -> Result<T, D::Error> {
        // Through Value: the crate enables serde_json arbitrary_precision, whose numbers do not pass through untagged
        // enums.
        match serde_json::Value::deserialize(deserializer)? {
            serde_json::Value::String(text) if text == super::UNSET_TEXT => Ok(T::UNSET),
            serde_json::Value::Number(number) => number
                .as_u64()
                .and_then(|n| T::try_from(n).ok())
                .ok_or_else(|| serde::de::Error::custom("guard must be a nonnegative integer in range")),
            other => Err(serde::de::Error::custom(format!("guard must be a number or \"unset\", not {other}"))),
        }
    }
}

/// Upper bound of `max_retries_per_iteration` when it is set (validation of the user's control).
const MAX_SET_RETRIES_PER_ITERATION: u32 = 16;

/// The user's controls of one author session.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Limits {
    /// Candidate-submission guard; `"unset"` = none.
    #[serde(with = "guard")]
    pub max_iterations: u32,
    /// Provider-cost stop guard; `"unset"` = none.
    pub max_cost_usd: Money,
    pub spend_policy: SpendPolicy,
    /// Additional author calls after the first one for each candidate submission; `"unset"` = none.
    #[serde(with = "guard")]
    pub max_retries_per_iteration: u32,
    /// Retired launch setting, retained only to read and preserve historical records. Ignored for author invocation,
    /// validation and resume identity; zero (omitted) does not impose a turn cap.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub max_author_tool_turns: u32,
    /// Wall-time guard of one author call, in seconds; `"unset"` = none.
    #[serde(with = "guard")]
    pub author_timeout_seconds: u64,
}

fn is_zero(value: &u32) -> bool {
    *value == 0
}

impl Limits {
    /// The current controls without the retired turn setting.
    pub fn active(&self) -> Self {
        Self { max_author_tool_turns: 0, ..self.clone() }
    }

    pub fn validate(&self) -> Result<(), String> {
        let retries_in_range = self.max_retries_per_iteration <= MAX_SET_RETRIES_PER_ITERATION
            || self.max_retries_per_iteration == UNSET_COUNT;
        if self.max_iterations == 0 || self.max_cost_usd.0 == 0 || self.author_timeout_seconds == 0 || !retries_in_range {
            return Err("positive iterations, dollars, timeout and at most 16 retries required".into());
        }
        Ok(())
    }

    /// Equal apart from the retired turn setting.
    pub fn same_active_limits(&self, other: &Self) -> bool {
        self.active() == other.active()
    }
}

/// Remove the retired turn setting from the declared limit locations of a request, for identity comparison only:
/// `/limits`, `/shared_design_limits`, `/request/limits` and `/queries/*/limits`. Other task payload fields, even with
/// the same name, stay. Saved requests and ledgers are never rewritten.
pub fn request_without_retired_turn_cap(mut request: Value) -> Value {
    fn clear(limits: &mut Value) {
        if let Some(limits) = limits.as_object_mut() {
            limits.remove("max_author_tool_turns");
        }
    }
    for pointer in ["/limits", "/shared_design_limits", "/request/limits"] {
        if let Some(limits) = request.pointer_mut(pointer) {
            clear(limits);
        }
    }
    if let Some(queries) = request.get_mut("queries").and_then(Value::as_array_mut) {
        for query in queries {
            if let Some(limits) = query.get_mut("limits") {
                clear(limits);
            }
        }
    }
    request
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use serde_json::json;

    pub(crate) fn limits() -> Limits {
        Limits {
            max_iterations: 2,
            max_cost_usd: Money::parse("1").unwrap(),
            spend_policy: SpendPolicy::EstimatedUsd,
            max_retries_per_iteration: 1,
            max_author_tool_turns: 0,
            author_timeout_seconds: 5,
        }
    }

    #[test]
    fn exact_money() {
        let sum = Money::parse("0.1").unwrap().checked_sum(Money::parse("0.2").unwrap()).unwrap();
        assert_eq!(sum.decimal(), "0.3");
        assert_eq!(Money::parse("1.2e-7").unwrap().decimal(), "0.00000012");
        assert!(Money::parse("-1").is_err());
        assert!(Money::parse("0.0000000000000000001").is_err(), "19 places are refused, not rounded");
    }

    #[test]
    fn numeric_guards_round_trip_and_unset_is_explicit() {
        let numeric = limits();
        assert_eq!(serde_json::from_str::<Limits>(&serde_json::to_string(&numeric).unwrap()).unwrap(), numeric);
        let unset: Limits = serde_json::from_value(json!({"max_iterations":"unset","max_cost_usd":"unset",
            "spend_policy":"estimated_usd","max_retries_per_iteration":"unset","author_timeout_seconds":"unset"}))
        .unwrap();
        unset.validate().unwrap();
        assert_eq!((unset.max_iterations, unset.max_cost_usd, unset.author_timeout_seconds), (UNSET_COUNT, Money::UNSET, UNSET_SECONDS));
        let back = serde_json::to_value(&unset).unwrap();
        for field in ["max_iterations", "max_cost_usd", "author_timeout_seconds", "max_retries_per_iteration"] {
            assert_eq!(back[field], "unset", "{field}");
        }
        assert!(serde_json::from_value::<Limits>(json!({"max_iterations":"none","max_cost_usd":"1",
            "spend_policy":"estimated_usd","max_retries_per_iteration":1,"author_timeout_seconds":1}))
        .is_err());
    }

    #[test]
    fn retired_turn_cap_request_compatibility_is_narrow() {
        let mut historical = limits();
        historical.max_author_tool_turns = 4;
        let old = json!(historical);
        let new = json!(historical.active());
        assert!(new.get("max_author_tool_turns").is_none());
        let decoded: Limits = serde_json::from_value(new.clone()).unwrap();
        decoded.validate().unwrap();
        for turns in [0, 1, 100, u32::MAX] {
            let mut legacy = new.clone();
            legacy["max_author_tool_turns"] = json!(turns);
            let legacy: Limits = serde_json::from_value(legacy).unwrap();
            legacy.validate().unwrap();
            assert!(legacy.same_active_limits(&decoded));
            assert_eq!(json!(legacy.active()), new);
        }
        let old_workload = json!({"shared_design_limits":old,"queries":[{"sql":"fixture","limits":old}]});
        let new_workload = json!({"shared_design_limits":new,"queries":[{"sql":"fixture","limits":new}]});
        assert_eq!(request_without_retired_turn_cap(old_workload.clone()), request_without_retired_turn_cap(new_workload.clone()));
        for pointer in ["/shared_design_limits/max_cost_usd", "/queries/0/limits/max_iterations", "/queries/0/sql"] {
            let mut changed = new_workload.clone();
            *changed.pointer_mut(pointer).unwrap() = json!("changed");
            assert_ne!(request_without_retired_turn_cap(old_workload.clone()), request_without_retired_turn_cap(changed));
        }
        let task = json!({"request":{"task":{"max_author_tool_turns":100}}});
        assert_eq!(request_without_retired_turn_cap(task.clone()), task);
    }
}
