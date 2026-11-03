//! What follows an author call that the provider ended without output (`ProviderCondition`), decided before the next
//! call of the same iteration:
//! - rate limited or another API error: wait, then resume the same provider session with a short continuation message
//!   ([`continuation_prompt`]; the session already holds the full prompt, and repeating it would only fill its
//!   context). The deadline is the provider's reset time when it lies in the future, otherwise the last receipt's
//!   end plus a bounded exponential backoff ([`retry_deadline`]). There is no retry-count or total-time cap; the
//!   user's guards and process signals still apply.
//! - context exhausted in a resumed session: that session is not resumed ([`session_resumable`]); the next call
//!   starts a fresh session, whose prompt carries the attempt handoff.
//! - account refused (authentication, permission, billing), or context exhausted on a fresh session's first call: a
//!   named refusal
//!   (`ControllerError::Author`, stage `provider_refusal`) that stops the run resumably; it is never retried silently.
//!
//! Each decision is recomputed from durable records (receipts and the transport's call records), so a restarted
//! controller continues the same wait instead of calling at once. A wait is recorded as [`PROVIDER_WAIT_FILE`] in the
//! failed call's directory and logged on stderr.
//!
//! **The operator's end of a wait** (`gendb engine operator-resume`): when the provider's limit is over
//! before the recorded deadline (for example, a weekly limit reset early), the operator stops the controller and
//! records [`WaitCleared`] as [`PROVIDER_WAIT_CLEARED_FILE`] beside the wait's record ([`clear_recorded_wait`]; written
//! once, never replaced). A wait whose call has a clearing record written after the wait began (the end of that call)
//! is cleared ([`ProviderWait::cleared`]): the relaunched controller logs the clearing on stderr, marks the wait's
//! record `cleared` (its fields kept, the clearing added) and calls at once, still in the same provider session with
//! the short continuation message. If the provider is still limited, that call fails and a new wait starts as usual
//! (its consecutive count goes on). A running controller does not read the record; the command refuses while one
//! runs.

use super::ControllerError;
use super::author::{AuthorTransport, ProviderCondition};
use super::layout::RunLayout;
use super::ledger::{Call, LedgerState};
use super::records::{self, RecordError};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::path::Path;

/// The first backoff wait (no provider reset time known).
pub const BACKOFF_BASE_MS: u64 = 60_000;
/// The longest single backoff wait; the waits themselves are not counted or capped.
pub const BACKOFF_MAX_MS: u64 = 3_600_000;
/// The record of a wait, in the directory of the call whose condition caused it.
pub const PROVIDER_WAIT_FILE: &str = "provider-wait.json";
/// The operator's record that the wait after a call is over ([`WaitCleared`]), beside [`PROVIDER_WAIT_FILE`].
pub const PROVIDER_WAIT_CLEARED_FILE: &str = "provider-wait-cleared.json";

/// A wait before the next call of an iteration.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct ProviderWait {
    /// The call the provider ended.
    pub after_call: u64,
    pub condition: ProviderCondition,
    /// Consecutive rate-limited or API-error calls of the iteration ending with `after_call` (counted up to the
    /// point where the backoff stops growing).
    pub consecutive: u32,
    /// `provider_reset` (the provider's reported reset time) or `exponential_backoff`.
    pub basis: &'static str,
    pub deadline_unix_ms: u64,
    /// The operator's clearing of this wait, recorded after the wait began: the next call starts at once.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cleared: Option<WaitCleared>,
}

/// The operator's record that the wait after a call is over before its deadline ([`PROVIDER_WAIT_CLEARED_FILE`],
/// written once by [`clear_recorded_wait`]).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaitCleared {
    pub format_version: u32,
    /// The call the cleared wait follows.
    pub after_call: u64,
    /// The cleared wait's deadline, as its record held it when it was cleared.
    pub deadline_unix_ms: u64,
    /// Who cleared it (`operator` for `gendb engine operator-resume`).
    pub by: String,
    /// The operator's reason, as written.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    pub cleared_unix_ms: u64,
}

fn waitable(condition: &ProviderCondition) -> bool {
    matches!(condition, ProviderCondition::RateLimited { .. } | ProviderCondition::ApiError { .. })
}

/// The backoff after `consecutive` waitable failures: `BACKOFF_BASE_MS · 2^(consecutive−1)`, at most `BACKOFF_MAX_MS`.
pub fn backoff_ms(consecutive: u32) -> u64 {
    let doublings = consecutive.saturating_sub(1).min(32);
    BACKOFF_BASE_MS.saturating_mul(1u64 << doublings).min(BACKOFF_MAX_MS)
}

/// The number of consecutive failures after which the backoff stops growing (counting further changes nothing).
fn backoff_saturation() -> u32 {
    (1..).find(|&n| backoff_ms(n) == BACKOFF_MAX_MS).unwrap_or(1)
}

/// When the next call may start after `condition`, and on which basis: the provider's reset time if it lies after
/// `now_unix_ms`; otherwise the end of the failed call plus [`backoff_ms`].
pub fn retry_deadline(condition: &ProviderCondition, consecutive: u32, last_ended_unix_ms: u64, now_unix_ms: u64) -> (u64, &'static str) {
    match condition {
        ProviderCondition::RateLimited { resets_at_unix_ms: Some(reset), .. } if *reset > now_unix_ms => (*reset, "provider_reset"),
        _ => (last_ended_unix_ms.saturating_add(backoff_ms(consecutive)), "exponential_backoff"),
    }
}

/// The condition that ended the settled call `call` without output, if the transport recognizes one.
fn condition_of<A: AuthorTransport>(author: &A, layout: &RunLayout, call: &Call) -> Option<ProviderCondition> {
    let receipt = call.receipt.as_ref().filter(|receipt| receipt.output.is_none())?;
    author.provider_condition(&layout.call(call.id), receipt)
}

/// Whether a later call may resume the provider session of `earlier`: the session exists and did not end with an
/// exhausted context.
pub fn session_resumable<A: AuthorTransport>(author: &A, layout: &RunLayout, earlier: &Call) -> bool {
    author.provider_session_exists(&layout.call(earlier.id))
        && condition_of(author, layout, earlier) != Some(ProviderCondition::ContextExhausted)
}

/// The wait (if any) before the next call of the current iteration, from the latest settled call of that iteration,
/// with the operator's clearing of it when one was recorded after the wait began ([`clearing_of`]).
/// `Err`: a provider refusal that retrying cannot fix, or an unreadable clearing record.
pub fn wait_before_next_call<A: AuthorTransport>(state: &LedgerState, layout: &RunLayout, author: &A) -> Result<Option<ProviderWait>, ControllerError> {
    let iteration = state.iterations + 1;
    let mut calls = state.calls.iter().rev().filter(|call| call.iteration == iteration);
    let Some(latest) = calls.next() else { return Ok(None) };
    let Some(condition) = condition_of(author, layout, latest) else { return Ok(None) };
    let refusal = |detail: String| ControllerError::Author { stage: "provider_refusal", detail };
    match condition {
        ProviderCondition::AccountRefused { reason } => {
            return Err(refusal(format!("call {} was refused by the provider ({reason}: authentication, permission or billing); fix the provider account, then resume this session", latest.id)));
        }
        ProviderCondition::ContextExhausted if !state.resumes_provider_session(latest) => {
            return Err(refusal(format!("call {} started a fresh provider session and its first prompt already exhausted the provider context; a retry would fail the same way", latest.id)));
        }
        ProviderCondition::ContextExhausted => return Ok(None),
        _ => {}
    }
    let mut consecutive = 1;
    let saturation = backoff_saturation();
    for earlier in calls {
        if consecutive >= saturation || !condition_of(author, layout, earlier).as_ref().is_some_and(waitable) {
            break;
        }
        consecutive += 1;
    }
    let ended = latest.receipt.as_ref().map_or(0, |receipt| receipt.ended_unix_ms);
    let (deadline_unix_ms, basis) = retry_deadline(&condition, consecutive, ended, records::now_unix_ms());
    let cleared = clearing_of(layout, latest.id, ended)?;
    Ok(Some(ProviderWait { after_call: latest.id, condition, consecutive, basis, deadline_unix_ms, cleared }))
}

/// The operator's clearing of the wait after call `call`: its [`PROVIDER_WAIT_CLEARED_FILE`] when that names the call
/// and was written after `began_unix_ms` (the end of the call, when the wait began). An older record clears nothing.
fn clearing_of(layout: &RunLayout, call: u64, began_unix_ms: u64) -> Result<Option<WaitCleared>, RecordError> {
    let path = layout.call(call).join(PROVIDER_WAIT_CLEARED_FILE);
    if !path.is_file() {
        return Ok(None);
    }
    let cleared: WaitCleared = records::read_json(&path)?;
    Ok((cleared.after_call == call && cleared.cleared_unix_ms > began_unix_ms).then_some(cleared))
}

/// Record the operator's clearing of the wait the session in `layout` is in (`gendb engine operator-resume`, module
/// documentation): the latest call of the session's current iteration has a recorded wait ([`PROVIDER_WAIT_FILE`]
/// with status `waiting`) and no clearing yet. The caller makes sure no controller runs the session: a running
/// controller does not read the record, its next launch does. Refused (`Err`, nothing written) when there is no wait
/// to clear.
pub fn clear_recorded_wait(layout: &RunLayout, by: &str, reason: Option<&str>) -> Result<WaitCleared, RecordError> {
    let refused = |detail: String| RecordError::new(layout.root(), format!("no wait to clear: {detail}"));
    if !layout.ledger().is_file() {
        return Err(refused("the session has no ledger".into()));
    }
    let state: LedgerState = records::read_json(&layout.ledger())?;
    if state.closed.is_some() {
        return Err(refused("the session is closed".into()));
    }
    let Some(call) = state.calls.last().filter(|call| call.iteration == state.iterations + 1) else {
        return Err(refused("the session has no call since its last submission".into()));
    };
    let wait_record = layout.call(call.id).join(PROVIDER_WAIT_FILE);
    if !wait_record.is_file() {
        return Err(refused(format!("its latest call {} has no recorded provider wait ({})", call.id, wait_record.display())));
    }
    let recorded: Value = records::read_json(&wait_record)?;
    if recorded["status"] != "waiting" || recorded["wait"]["after_call"] != call.id {
        return Err(refused(format!("the wait after call {} is not waiting (status {})", call.id, recorded["status"])));
    }
    let deadline_unix_ms = recorded["wait"]["deadline_unix_ms"].as_u64().ok_or_else(|| RecordError::new(&wait_record, "the wait has no deadline_unix_ms"))?;
    let path = layout.call(call.id).join(PROVIDER_WAIT_CLEARED_FILE);
    if path.exists() {
        return Err(refused(format!("the wait after call {} was cleared already ({}); relaunch the controller", call.id, path.display())));
    }
    let reason = reason.map(str::trim).filter(|reason| !reason.is_empty()).map(str::to_owned);
    let cleared = WaitCleared { format_version: 1, after_call: call.id, deadline_unix_ms, by: by.into(), reason, cleared_unix_ms: records::now_unix_ms() };
    records::write_new_json(&path, &cleared)?;
    Ok(cleared)
}

/// Record the wait, block until its deadline through the transport, then record that it elapsed. A wait the operator
/// cleared does not block ([`resume_cleared_wait`]).
pub fn wait_for_deadline<A: AuthorTransport>(author: &mut A, layout: &RunLayout, wait: &ProviderWait) -> Result<(), ControllerError> {
    let record = layout.call(wait.after_call).join(PROVIDER_WAIT_FILE);
    if let Some(cleared) = &wait.cleared {
        return Ok(resume_cleared_wait(layout, &record, wait, cleared)?);
    }
    let waiting_since = records::now_unix_ms();
    let entry = |status: &str| {
        json!({"format_version":1,"status":status,"wait":wait,"deadline_utc":utc_text(wait.deadline_unix_ms),
            "waiting_since_unix_ms":waiting_since,
            "next":"resume the same provider session with a short continuation message (a fresh session if it no longer exists)"})
    };
    records::write_json_atomic(&record, &entry("waiting"))?;
    eprintln!("{}: provider {} after call {}; waiting until {} ({}, consecutive {})", layout.root().display(),
        condition_text(&wait.condition), wait.after_call, utc_text(wait.deadline_unix_ms), wait.basis, wait.consecutive);
    author.wait_for_provider(wait.deadline_unix_ms);
    let mut elapsed = entry("elapsed");
    elapsed["resumed_unix_ms"] = json!(records::now_unix_ms());
    Ok(records::write_json_atomic(&record, &elapsed)?)
}

/// A wait the operator cleared: log it on stderr and mark the wait's `record` `cleared` (its recorded fields kept, the
/// clearing and the resume time added; the clearing record stays as written). No wait.
fn resume_cleared_wait(layout: &RunLayout, record: &Path, wait: &ProviderWait, cleared: &WaitCleared) -> Result<(), RecordError> {
    let reason = cleared.reason.as_deref().map(|reason| format!(" ({reason})")).unwrap_or_default();
    eprintln!("{}: provider {} after call {}: the wait until {} ({}, consecutive {}) was cleared by the {} at {}{reason}; calling now",
        layout.root().display(), condition_text(&wait.condition), wait.after_call, utc_text(wait.deadline_unix_ms), wait.basis, wait.consecutive,
        cleared.by, utc_text(cleared.cleared_unix_ms));
    let mut entry = if record.is_file() {
        records::read_json(record)?
    } else {
        json!({"format_version":1,"wait":wait,"deadline_utc":utc_text(wait.deadline_unix_ms)})
    };
    entry["status"] = json!("cleared");
    entry["cleared"] = json!(cleared);
    entry["resumed_unix_ms"] = json!(records::now_unix_ms());
    records::write_json_atomic(record, &entry)
}

fn condition_text(condition: &ProviderCondition) -> String {
    match condition {
        ProviderCondition::RateLimited { status, .. } => match status {
            Some(status) => format!("rate limit (HTTP {status})"),
            None => "rate limit".into(),
        },
        ProviderCondition::ApiError { status } => match status {
            Some(status) => format!("API error (HTTP {status})"),
            None => "API error".into(),
        },
        ProviderCondition::ContextExhausted => "context exhausted".into(),
        ProviderCondition::AccountRefused { reason } => format!("account refused ({reason})"),
    }
}

/// The prompt of the call that resumes a session after a wait: what happened and that nothing else changed. The full
/// instructions stay earlier in the session. A wait the operator cleared says when it ended and until when it was set.
pub fn continuation_prompt(wait: &ProviderWait, prompt_file: &Path) -> String {
    let deadline = format!("{} ({})", utc_text(wait.deadline_unix_ms), wait.basis.replace('_', " "));
    let waited = match &wait.cleared {
        None => deadline,
        Some(cleared) => format!("{}, when the run's operator ended the wait (it was set until {deadline}),", utc_text(cleared.cleared_unix_ms)),
    };
    format!(
        "# Continue after a provider interruption\n\nYour previous call in this session (call {}) was ended by the provider, not by you: {}. GenDB waited until {waited} and now resumes this same session. Nothing else changed: the task, the limits, the ledger and your workspace are as you left them, and your complete instructions are earlier in this session (every call's prompt is saved beside this one, {}). Continue from where you stopped and finish with your submission as instructed.\n",
        wait.after_call,
        condition_text(&wait.condition),
        prompt_file.display()
    )
}

/// `unix_ms` as `YYYY-MM-DDTHH:MM:SSZ` (proleptic Gregorian calendar, UTC).
pub fn utc_text(unix_ms: u64) -> String {
    let seconds = unix_ms / 1000;
    let (days, of_day) = ((seconds / 86_400) as i64, seconds % 86_400);
    // Civil date from days since 1970-01-01 (H. Hinnant's algorithm).
    let shifted = days + 719_468;
    let era = shifted.div_euclid(146_097);
    let day_of_era = shifted.rem_euclid(146_097);
    let year_of_era = (day_of_era - day_of_era / 1460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_index = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_index + 2) / 5 + 1;
    let month = if month_index < 10 { month_index + 3 } else { month_index - 9 };
    let year = year_of_era + era * 400 + i64::from(month <= 2);
    format!("{year:04}-{month:02}-{day:02}T{:02}:{:02}:{:02}Z", of_day / 3600, of_day % 3600 / 60, of_day % 60)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deadline_uses_a_future_provider_reset_else_bounded_doubling_backoff() {
        let limited = |reset| ProviderCondition::RateLimited { status: Some(429), resets_at_unix_ms: reset };
        // 1791042000 s = 2026-10-03T15:40:00Z, a provider reset time in the future of the failed call.
        assert_eq!(retry_deadline(&limited(Some(1_791_042_000_000)), 1, 1_791_030_000_000, 1_791_030_000_500), (1_791_042_000_000, "provider_reset"));
        assert_eq!(utc_text(1_791_042_000_000), "2026-10-03T15:40:00Z");
        // A reset already past (or unknown), and a server error, fall back to the backoff from the failed call's end.
        assert_eq!(retry_deadline(&limited(Some(1_000)), 2, 5_000, 6_000), (5_000 + 120_000, "exponential_backoff"));
        assert_eq!(retry_deadline(&limited(None), 1, 5_000, 6_000), (65_000, "exponential_backoff"));
        assert_eq!(retry_deadline(&ProviderCondition::ApiError { status: Some(529) }, 3, 0, 1), (240_000, "exponential_backoff"));
        assert_eq!([1, 2, 6, 7, 1_000].map(backoff_ms), [60_000, 120_000, 1_920_000, BACKOFF_MAX_MS, BACKOFF_MAX_MS]);
        assert_eq!(backoff_saturation(), 7);
        assert_eq!(utc_text(951_782_400_000), "2000-02-29T00:00:00Z");
    }

    use crate::controller::layout::PROMPT_FILE;
    use crate::controller::limits::{Money, tests::limits};
    use crate::controller::test_support::{FixtureAuthor, receipt, scratch_root};
    use std::fs;

    /// A settled call of iteration 1 that the provider ended without output at `ended_unix_ms`.
    fn ended_call(id: u64, ended_unix_ms: u64) -> Call {
        let call = Call { id, iteration: 1, attempt: id as u32, started_unix_ms: 0, reservation_usd: Money::UNSET, receipt: None, provider_session: None, resumes_provider_session: false, usage_in_resumed_session: false };
        let mut settled = receipt(&call, "s", None);
        settled.ended_unix_ms = ended_unix_ms;
        Call { receipt: Some(settled), ..call }
    }

    /// A session with no submission whose ledger holds `calls`, each rate limited by the provider until `reset`.
    fn rate_limited_session(name: &str, calls: Vec<Call>, reset: u64) -> (RunLayout, LedgerState, FixtureAuthor) {
        let layout = RunLayout::new(&scratch_root(name));
        let mut author = FixtureAuthor::default();
        for call in &calls {
            fs::create_dir_all(layout.call(call.id)).unwrap();
            author.conditions.insert(call.id, ProviderCondition::RateLimited { status: Some(429), resets_at_unix_ms: Some(reset) });
        }
        let state = LedgerState {
            format_version: 1,
            request: json!({}),
            session_id: "s".into(),
            limits: limits(),
            iterations: 0,
            calls,
            receipt_reconciliations: vec![],
            predispatch_recoveries: vec![],
            preparation_context_revisions: vec![],
            trials: vec![],
            incumbent: None,
            closed: None,
        };
        records::write_json_atomic(&layout.ledger(), &state).unwrap();
        (layout, state, author)
    }

    /// Done-checks: a recorded wait with no clearing still waits; the operator's clearing ends it (no wait,
    /// the wait's record marked `cleared`, the continuation message says so); a clearing older than the wait does not
    /// clear it; the clearing is refused when there is no wait to clear, and written once.
    #[test]
    fn an_operators_clearing_ends_only_the_wait_it_follows() {
        let now = records::now_unix_ms();
        let reset = now + 86_400_000;
        let ended = now - 60_000;
        let (layout, state, mut author) = rate_limited_session("provider-wait-cleared", vec![ended_call(1, ended)], reset);
        let wait = wait_before_next_call(&state, &layout, &author).unwrap().unwrap();
        assert_eq!((wait.after_call, wait.basis, wait.deadline_unix_ms, wait.cleared.clone()), (1, "provider_reset", reset, None), "no clearing: it waits");
        assert!(clear_recorded_wait(&layout, "operator", None).unwrap_err().to_string().contains("no wait to clear: its latest call 1 has no recorded provider wait"));

        // A controller stopped during the wait left its record `waiting`.
        let waiting = json!({"format_version":1,"status":"waiting","wait":wait,"deadline_utc":utc_text(reset),"waiting_since_unix_ms":ended + 5});
        records::write_json_atomic(&layout.call(1).join(PROVIDER_WAIT_FILE), &waiting).unwrap();
        let cleared = clear_recorded_wait(&layout, "operator", Some("  the weekly limit was reset early \n")).unwrap();
        assert_eq!((cleared.after_call, cleared.deadline_unix_ms, cleared.by.as_str(), cleared.reason.as_deref()), (1, reset, "operator", Some("the weekly limit was reset early")));
        assert!(clear_recorded_wait(&layout, "operator", None).unwrap_err().to_string().contains("was cleared already"), "written once");
        assert_eq!(records::read_json::<WaitCleared>(&layout.call(1).join(PROVIDER_WAIT_CLEARED_FILE)).unwrap(), cleared);

        let wait = wait_before_next_call(&state, &layout, &author).unwrap().unwrap();
        assert_eq!(wait.cleared.as_ref(), Some(&cleared));
        wait_for_deadline(&mut author, &layout, &wait).unwrap();
        assert!(author.waits.is_empty(), "a cleared wait does not wait");
        let record: Value = records::read_json(&layout.call(1).join(PROVIDER_WAIT_FILE)).unwrap();
        assert_eq!((record["status"].as_str(), &record["cleared"], &record["waiting_since_unix_ms"]), (Some("cleared"), &json!(cleared), &json!(ended + 5)), "the wait's record is kept, marked cleared");
        let prompt_file = layout.call(2).join(PROMPT_FILE);
        let continuation = continuation_prompt(&wait, &prompt_file);
        assert!(continuation.contains(&format!("GenDB waited until {}, when the run's operator ended the wait (it was set until {} (provider reset)), and now resumes this same session.", utc_text(cleared.cleared_unix_ms), utc_text(reset))), "{continuation}");
        let uncleared = ProviderWait { cleared: None, ..wait.clone() };
        assert!(continuation_prompt(&uncleared, &prompt_file).contains(&format!("GenDB waited until {} (provider reset) and now resumes this same session.", utc_text(reset))), "an ordinary wait's message is unchanged");
        assert!(clear_recorded_wait(&layout, "operator", None).unwrap_err().to_string().contains("is not waiting"));

        // A clearing written before the wait began (here: before its call ended), or naming another call, clears nothing.
        for stale in [WaitCleared { cleared_unix_ms: ended - 1, ..cleared.clone() }, WaitCleared { after_call: 7, ..cleared.clone() }] {
            fs::write(layout.call(1).join(PROVIDER_WAIT_CLEARED_FILE), serde_json::to_vec(&stale).unwrap()).unwrap();
            assert_eq!(wait_before_next_call(&state, &layout, &author).unwrap().unwrap().cleared, None, "{stale:?}");
        }
        fs::remove_dir_all(layout.root()).ok();

        // The provider still limited after a cleared wait: the next call's wait starts as usual, its count goes on.
        let (layout, state, author) = rate_limited_session("provider-wait-after-clearing", vec![ended_call(1, ended), ended_call(2, now)], reset);
        fs::write(layout.call(1).join(PROVIDER_WAIT_CLEARED_FILE), serde_json::to_vec(&cleared).unwrap()).unwrap();
        let next = wait_before_next_call(&state, &layout, &author).unwrap().unwrap();
        assert_eq!((next.after_call, next.consecutive, next.deadline_unix_ms, next.cleared), (2, 2, reset, None));
        assert!(clear_recorded_wait(&layout, "operator", None).unwrap_err().to_string().contains("its latest call 2 has no recorded provider wait"));
        fs::remove_dir_all(layout.root()).ok();
    }
}
