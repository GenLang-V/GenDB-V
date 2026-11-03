//! Bounded storage of rows answers in a result file. A diagnostic engine job can return answers of millions of rows
//! (an author's own statement at a large scale), and every call's answer would otherwise be written in full, twice
//! (the rows as PostgreSQL output text and the exact wire as hex). An answer over an [`AnswerBound`] is stored as its
//! [`StoredAnswer`] summary (row count, the SHA-256 and size of its result wire) with its first rows within the bound;
//! the rest of it is not stored. An answer within the bound is stored in full, as before.
//!
//! Two places apply the bound, each where the full answer is no longer needed:
//! - the child ([`stored_rows`]), for a job whose caller compares no rows (`WorkerRequest::answer_bound`): only the
//!   first rows are ever rendered, and the full answer never reaches the file;
//! - the caller ([`bounded_observation`], through `super::parent::store_bounded_result`), for a job whose answers it
//!   compared in full from the file it read: afterwards the file is evidence only.
//!
//! Nothing here touches an answer that is compared: a comparison always reads the full answer.

use crate::abi::CallOutcome;
use gendb_sqlspec::codec::HostValue;
use gendb_sqlspec::pg_text::{NonUtf8Text, value_json};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};

use super::protocol::CallObservation;

/// How much of a rows answer is stored: the first rows, at most `rows` rows and at most `row_text_bytes` bytes of their
/// compact JSON text (each row an array of PostgreSQL output text values).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AnswerBound {
    pub rows: u64,
    pub row_text_bytes: u64,
}

impl AnswerBound {
    /// The framework's bound of a stored answer that is not compared (or whose comparison failed): 100 rows and
    /// 1 MiB of row text.
    pub const STORED: AnswerBound = AnswerBound { rows: 100, row_text_bytes: 1 << 20 };

    /// The bound in words, as the records and the author's tool answers state it.
    pub fn describe(&self) -> String {
        format!("at most {} rows and {} bytes of row text", self.rows, self.row_text_bytes)
    }
}

/// A rows answer stored over its bound: `CallObservation::rows` then holds only its first `stored_rows` rows, and the
/// call's `result_wire` is absent (its size and digest are here).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StoredAnswer {
    /// Rows of the whole answer.
    pub rows: u64,
    /// Rows kept in the result file (the answer's first rows, in its order).
    pub stored_rows: u64,
    /// Bytes of the call's result wire (the exact answer, SQLSpec result codec) and its SHA-256, lowercase hex.
    pub wire_bytes: u64,
    pub wire_sha256: String,
    /// The bound the answer was stored under.
    pub bound: AnswerBound,
}

impl StoredAnswer {
    fn of(wire: &[u8], rows: usize, stored_rows: usize, bound: AnswerBound) -> Self {
        Self {
            rows: rows as u64,
            stored_rows: stored_rows as u64,
            wire_bytes: wire.len() as u64,
            wire_sha256: Sha256::digest(wire).iter().map(|b| format!("{b:02x}")).collect(),
            bound,
        }
    }

    /// The answer in words: `"<rows> rows; stored: the first <k> ..., the rest not stored; SHA-256 ..."`.
    pub fn describe(&self) -> String {
        format!(
            "{} rows; stored: the first {} rows ({}), the rest not stored; SHA-256 of the result wire {} ({} bytes)",
            self.rows,
            self.stored_rows,
            self.bound.describe(),
            self.wire_sha256,
            self.wire_bytes
        )
    }
}

/// The first rows of `rows` within `bound`: rows are taken in order while both the row count and the total of their
/// compact JSON text stay within it. At most `bound.rows` rows are read from the iterator.
fn first_rows<E>(rows: impl Iterator<Item = Result<Vec<Value>, E>>, bound: AnswerBound) -> Result<Vec<Vec<Value>>, E> {
    let mut kept = vec![];
    let mut text_bytes = 0u64;
    for row in rows.take(usize::try_from(bound.rows).unwrap_or(usize::MAX)) {
        let row = row?;
        let size = serde_json::to_vec(&row).map_or(u64::MAX, |text| text.len() as u64);
        text_bytes = text_bytes.saturating_add(size);
        if text_bytes > bound.row_text_bytes {
            break;
        }
        kept.push(row);
    }
    Ok(kept)
}

/// Child side: the rows of an `Ok` call to store, rendered as PostgreSQL output text. Within `bound`, every row and no
/// summary (the wire stays in `outcome`); over it, the first rows and their [`StoredAnswer`], with the wire taken out
/// of `outcome`. Only the stored rows are rendered.
pub(super) fn stored_rows(outcome: &mut CallOutcome, rows: &[Vec<HostValue>], bound: AnswerBound) -> Result<(Vec<Vec<Value>>, Option<StoredAnswer>), NonUtf8Text> {
    let kept = first_rows(rows.iter().map(|row| row.iter().map(value_json).collect()), bound)?;
    if kept.len() == rows.len() {
        return Ok((kept, None));
    }
    let wire = outcome.result_wire.take().unwrap_or_default();
    let stored = StoredAnswer::of(&wire, rows.len(), kept.len(), bound);
    Ok((kept, Some(stored)))
}

/// Caller side: `observation` with its rows answer stored under `bound`, when that answer is over it (`None`: nothing to
/// cut: no rows answer, already stored bounded, or within the bound). Only the kept rows are copied.
pub fn bounded_observation(observation: &CallObservation, bound: AnswerBound) -> Option<CallObservation> {
    let rows = observation.rows.as_ref().filter(|_| observation.stored_answer.is_none())?;
    let wire = observation.outcome.result_wire.as_deref()?;
    let kept = first_rows(rows.iter().map(|row| Ok::<_, std::convert::Infallible>(row.clone())), bound).unwrap_or_else(|never| match never {});
    if kept.len() == rows.len() {
        return None;
    }
    let stored = StoredAnswer::of(wire, rows.len(), kept.len(), bound);
    let outcome = &observation.outcome;
    Some(CallObservation {
        binding: observation.binding,
        workers: observation.workers,
        repetition: observation.repetition,
        outcome: CallOutcome {
            status: outcome.status,
            sql_error: outcome.sql_error,
            result_wire: None,
            parts_delivered: outcome.parts_delivered,
            dispatch: outcome.dispatch.clone(),
            usage: outcome.usage.clone(),
            storage_requests: outcome.storage_requests.clone(),
        },
        rows: Some(kept),
        sql_error: observation.sql_error.clone(),
        process_io: observation.process_io,
        peak_anon_bytes: observation.peak_anon_bytes,
        samples: observation.samples.clone(),
        stored_answer: Some(stored),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abi::{CallStatus, CallUsage, DispatchEvidence};
    use gendb_sqlspec::codec::encode_result_rows;

    fn answer(rows: usize, text: &str) -> Vec<Vec<HostValue>> {
        (0..rows).map(|i| vec![HostValue::Int(i as i64), HostValue::Text(text.as_bytes().to_vec())]).collect()
    }

    fn ok_outcome(rows: &[Vec<HostValue>]) -> CallOutcome {
        CallOutcome {
            status: CallStatus::Ok,
            sql_error: None,
            result_wire: Some(encode_result_rows(rows)),
            parts_delivered: 0,
            dispatch: DispatchEvidence::default(),
            usage: CallUsage::default(),
            storage_requests: vec![],
        }
    }

    /// Over the row bound the child keeps the first rows, the count, the wire's size and SHA-256, and drops the wire;
    /// within the bound it stores every row and keeps the wire. The byte bound cuts wide rows too.
    #[test]
    fn the_child_stores_an_answer_over_the_bound_as_its_summary_and_first_rows() {
        let bound = AnswerBound { rows: 3, row_text_bytes: 1 << 20 };
        let many = answer(10, "x");
        let mut outcome = ok_outcome(&many);
        let wire = outcome.result_wire.clone().unwrap();
        let (kept, stored) = stored_rows(&mut outcome, &many, bound).unwrap();
        let stored = stored.expect("over the bound");
        assert_eq!(kept, (0..3).map(|i| vec![Value::from(i), Value::from("x")]).collect::<Vec<_>>());
        assert_eq!((stored.rows, stored.stored_rows, stored.wire_bytes), (10, 3, wire.len() as u64));
        assert_eq!(stored.wire_sha256, Sha256::digest(&wire).iter().map(|b| format!("{b:02x}")).collect::<String>());
        assert!(outcome.result_wire.is_none(), "the full answer is not stored");
        assert!(stored.describe().starts_with("10 rows; stored: the first 3 rows (at most 3 rows and 1048576 bytes of row text), the rest not stored; SHA-256 of the result wire "));

        let few = answer(3, "x");
        let mut outcome = ok_outcome(&few);
        let (kept, stored) = stored_rows(&mut outcome, &few, bound).unwrap();
        assert!(stored.is_none() && kept.len() == 3 && outcome.result_wire.is_some(), "an answer within the bound is stored in full");

        let wide = answer(3, &"y".repeat(100));
        let mut outcome = ok_outcome(&wide);
        let (kept, stored) = stored_rows(&mut outcome, &wide, AnswerBound { rows: 3, row_text_bytes: 250 }).unwrap();
        assert_eq!((kept.len(), stored.map(|s| s.stored_rows)), (2, Some(2)), "two rows of 106 bytes fit 250 bytes, three do not");
    }

    /// The caller's cut of a full observation: the same summary and rows as the child's, the wire dropped, every other
    /// field kept; nothing to cut within the bound or for an answer already stored bounded.
    #[test]
    fn the_caller_cuts_a_full_observation_like_the_child() {
        let bound = AnswerBound { rows: 2, row_text_bytes: 1 << 20 };
        let rows = answer(5, "z");
        let outcome = ok_outcome(&rows);
        let full = CallObservation {
            binding: Some(0),
            workers: 4,
            repetition: 1,
            outcome: outcome.clone(),
            rows: Some(rows.iter().map(|r| r.iter().map(|v| value_json(v).unwrap()).collect()).collect()),
            sql_error: None,
            process_io: None,
            peak_anon_bytes: Some(7),
            samples: None,
            stored_answer: None,
        };
        let cut = bounded_observation(&full, bound).expect("over the bound");
        let mut child_outcome = outcome.clone();
        let (child_rows, child_stored) = stored_rows(&mut child_outcome, &rows, bound).unwrap();
        assert_eq!((cut.rows.as_ref(), cut.stored_answer.as_ref()), (Some(&child_rows), child_stored.as_ref()));
        assert_eq!(cut.outcome, child_outcome);
        assert_eq!((cut.binding, cut.workers, cut.repetition, cut.peak_anon_bytes), (Some(0), 4, 1, Some(7)));
        assert!(bounded_observation(&cut, bound).is_none(), "already stored bounded");
        assert!(bounded_observation(&full, AnswerBound { rows: 5, row_text_bytes: 1 << 20 }).is_none(), "within the bound");
    }
}
