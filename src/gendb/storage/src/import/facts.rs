//! Source data facts, computed once while a capture is prepared: per captured column its row and
//! NULL counts, minimum and maximum, an estimated distinct count, sortedness, and for integer columns the value range and
//! key density (estimated distinct values per value in `[min, max]`).
//!
//! When: right after the import or extension writes the newly captured columns, over exactly those columns, while
//! their pages are hot; a reused capture copies its base's facts, an extension merges the base's facts with the new
//! columns'. No later step reads source data again to compute them.
//!
//! Who reads them: only the workload storage author (its contract inputs). Query authors learn about the data only
//! from the storages' contracts and descriptions, so nothing they read can disagree with what a storage proves.
//!
//! These are descriptive statistics, not proof inputs: the distinct count is a HyperLogLog estimate (2^14 registers,
//! about 1% standard error), text bounds are byte order truncated to [`TEXT_BOUND_BYTES`].

use super::error::{ImportError, Result};
use crate::io::{NATIVE_TYPE_I32, NATIVE_TYPE_I64, NATIVE_TYPE_I128, NATIVE_TYPE_UTF8, NativeColumn, SourceColumns};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::path::Path;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

/// File name of the facts, in a prepared root.
pub const DATA_FACTS_FILE: &str = "data-facts.json";
/// Longest prefix of a text bound reported.
pub const TEXT_BOUND_BYTES: usize = 48;
const HLL_BITS: u32 = 14;

/// The facts of one captured column.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ColumnFacts {
    pub table: String,
    pub column: String,
    pub ordinal: usize,
    /// `i32` (also dates: days since 1970-01-01), `i64`, `i128` (decimal coefficient at the declared scale), `utf8`.
    pub native: String,
    pub rows: u64,
    pub nulls: u64,
    pub min: Value,
    pub max: Value,
    pub distinct_estimate: u64,
    /// `ascending`, `descending`, `constant` or `unsorted` (in capture row order, non-NULL values).
    pub sorted: String,
    /// Fraction of adjacent non-NULL pairs in non-decreasing order.
    pub ascending_pair_fraction: f64,
    /// Integer columns: `max - min + 1`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub value_range: Option<String>,
    /// Integer columns: `distinct_estimate / value_range` (1.0: every value of the range occurs).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub key_density: Option<f64>,
    /// Text columns: mean and largest byte length.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mean_bytes: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_bytes: Option<u64>,
}

/// `data-facts.json`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct DataFacts {
    pub format_version: u32,
    pub columns: Vec<ColumnFacts>,
}

impl DataFacts {
    /// The facts of the prepared root `root` (absent: none recorded).
    pub fn read(root: &Path) -> Result<Option<Self>> {
        let path = root.join(DATA_FACTS_FILE);
        if !path.is_file() {
            return Ok(None);
        }
        let bytes = std::fs::read(&path).map_err(ImportError::file(&path))?;
        Ok(Some(serde_json::from_slice(&bytes).map_err(|e| ImportError::prepared(&path, format!("data facts: {e}")))?))
    }

    /// Write the facts of the new prepared root `root`: `base`'s (if any) with `added` replacing or extending them.
    pub fn write(root: &Path, base: Option<DataFacts>, added: Vec<ColumnFacts>) -> Result<()> {
        let mut columns: Vec<ColumnFacts> = base.map(|b| b.columns).unwrap_or_default();
        columns.retain(|c| !added.iter().any(|a| a.table == c.table && a.ordinal == c.ordinal));
        columns.extend(added);
        columns.sort_by(|a, b| (&a.table, a.ordinal).cmp(&(&b.table, b.ordinal)));
        let path = root.join(DATA_FACTS_FILE);
        let bytes = serde_json::to_vec_pretty(&DataFacts { format_version: 1, columns }).map_err(|e| ImportError::prepared(&path, e.to_string()))?;
        std::fs::write(&path, bytes).map_err(ImportError::file(&path))
    }
}

/// The facts of the columns `selected` (`(table, ordinal)`) of `columns`, computed in parallel, one column per task.
pub fn compute_facts(columns: &SourceColumns, selected: &[(String, usize)]) -> Vec<ColumnFacts> {
    let descriptors = columns.descriptors();
    let work: Vec<(String, String, usize, ReadOnlyColumn)> = columns
        .bindings()
        .iter()
        .filter_map(|b| {
            let ordinal = b.original_index?;
            let field = b.field.as_ref()?;
            selected.contains(&(b.table.clone(), ordinal)).then(|| (b.table.clone(), field.name.clone(), ordinal, ReadOnlyColumn(descriptors[b.descriptor_index])))
        })
        .collect();
    let next = AtomicUsize::new(0);
    let out = Mutex::new(vec![]);
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get()).min(work.len().max(1));
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    let Some((table, column, ordinal, descriptor)) = work.get(i) else { break };
                    // SAFETY: the descriptor borrows buffers `columns` owns for this whole call.
                    if let Some(facts) = unsafe { column_facts(table, column, *ordinal, &descriptor.0) } {
                        out.lock().expect("facts lock").push(facts);
                    }
                }
            });
        }
    });
    out.into_inner().expect("facts lock")
}

/// A column descriptor read by one facts task. Its buffers are immutable and owned by the `SourceColumns` the caller
/// holds for the whole computation, so sharing the pointers between the scoped threads is sound.
struct ReadOnlyColumn(NativeColumn);
// SAFETY: see the type's documentation (read-only buffers outliving every scoped thread).
unsafe impl Sync for ReadOnlyColumn {}
// SAFETY: as above.
unsafe impl Send for ReadOnlyColumn {}

/// Running statistics of one column's non-NULL values in row order.
struct Running<T> {
    min: Option<T>,
    max: Option<T>,
    previous: Option<T>,
    ascending_pairs: u64,
    descending_pairs: u64,
    pairs: u64,
    hll: Vec<u8>,
}

impl<T: PartialOrd + Clone> Running<T> {
    fn new() -> Self {
        Self { min: None, max: None, previous: None, ascending_pairs: 0, descending_pairs: 0, pairs: 0, hll: vec![0; 1 << HLL_BITS] }
    }

    fn add(&mut self, value: T, hash: u64) {
        if let Some(previous) = &self.previous {
            self.pairs += 1;
            self.ascending_pairs += (*previous <= value) as u64;
            self.descending_pairs += (*previous >= value) as u64;
        }
        if self.min.as_ref().is_none_or(|m| value < *m) {
            self.min = Some(value.clone());
        }
        if self.max.as_ref().is_none_or(|m| value > *m) {
            self.max = Some(value.clone());
        }
        self.previous = Some(value);
        let register = (hash >> (64 - HLL_BITS)) as usize;
        let rank = ((hash << HLL_BITS) | (1 << (HLL_BITS - 1))).leading_zeros() as u8 + 1;
        self.hll[register] = self.hll[register].max(rank);
    }

    fn sorted(&self) -> &'static str {
        match (self.ascending_pairs == self.pairs, self.descending_pairs == self.pairs) {
            (true, true) => "constant",
            (true, false) => "ascending",
            (false, true) => "descending",
            (false, false) => "unsorted",
        }
    }

    fn ascending_fraction(&self) -> f64 {
        if self.pairs == 0 { 1.0 } else { self.ascending_pairs as f64 / self.pairs as f64 }
    }

    /// HyperLogLog estimate with the small-range (linear counting) correction.
    fn distinct(&self) -> u64 {
        let m = (1u64 << HLL_BITS) as f64;
        let sum: f64 = self.hll.iter().map(|&r| 2f64.powi(-(r as i32))).sum();
        let estimate = 0.7213 / (1.0 + 1.079 / m) * m * m / sum;
        let zeros = self.hll.iter().filter(|&&r| r == 0).count();
        let value = if estimate <= 2.5 * m && zeros > 0 { m * (m / zeros as f64).ln() } else { estimate };
        value.round() as u64
    }
}

/// A 64-bit mix of an integer (SplitMix64 finalizer).
fn mix(mut x: u64) -> u64 {
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d049bb133111eb);
    x ^ (x >> 31)
}

fn hash_bytes(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in bytes {
        h = (h ^ b as u64).wrapping_mul(0x100000001b3);
    }
    mix(h)
}

/// The facts of one native column.
///
/// # Safety
/// The descriptor's buffers must be valid for its declared length and type.
unsafe fn column_facts(table: &str, column: &str, ordinal: usize, c: &NativeColumn) -> Option<ColumnFacts> {
    let rows = u64::try_from(c.len).ok()?;
    let n = rows as usize;
    let valid = |i: usize| c.validity.is_null() || unsafe { *c.validity.add(i) } != 0;
    let nulls = (0..n).filter(|&i| !valid(i)).count() as u64;
    let base = |native: &str, min: Value, max: Value, distinct: u64, sorted: &str, ascending: f64| ColumnFacts {
        table: table.into(),
        column: column.into(),
        ordinal,
        native: native.into(),
        rows,
        nulls,
        min,
        max,
        distinct_estimate: distinct,
        sorted: sorted.into(),
        ascending_pair_fraction: ascending,
        value_range: None,
        key_density: None,
        mean_bytes: None,
        max_bytes: None,
    };
    let integer = |native: &str, running: Running<i128>| {
        let mut facts = base(native, json!(running.min.map(|v| v.to_string())), json!(running.max.map(|v| v.to_string())), running.distinct(), running.sorted(), running.ascending_fraction());
        if let (Some(min), Some(max)) = (running.min, running.max) {
            let range = max.saturating_sub(min).saturating_add(1);
            facts.value_range = Some(range.to_string());
            facts.key_density = Some(facts.distinct_estimate as f64 / range as f64);
        }
        facts
    };
    match c.type_tag {
        NATIVE_TYPE_I32 | NATIVE_TYPE_I64 | NATIVE_TYPE_I128 => {
            let mut running = Running::<i128>::new();
            for i in (0..n).filter(|&i| valid(i)) {
                let v: i128 = unsafe {
                    match c.type_tag {
                        NATIVE_TYPE_I32 => *c.values.cast::<i32>().add(i) as i128,
                        NATIVE_TYPE_I64 => *c.values.cast::<i64>().add(i) as i128,
                        _ => std::ptr::read_unaligned(c.values.cast::<i128>().add(i)),
                    }
                };
                running.add(v, mix(v as u64 ^ mix((v >> 64) as u64)));
            }
            let native = match c.type_tag {
                NATIVE_TYPE_I32 => "i32",
                NATIVE_TYPE_I64 => "i64",
                _ => "i128",
            };
            Some(integer(native, running))
        }
        NATIVE_TYPE_UTF8 => {
            let mut running = Running::<&[u8]>::new();
            let (mut total, mut longest) = (0u64, 0u64);
            for i in (0..n).filter(|&i| valid(i)) {
                let (start, end) = unsafe { (*c.offsets.add(i), *c.offsets.add(i + 1)) };
                let text: &[u8] = unsafe { std::slice::from_raw_parts(c.bytes.add(start as usize), (end - start) as usize) };
                total += text.len() as u64;
                longest = longest.max(text.len() as u64);
                running.add(text, hash_bytes(text));
            }
            let bound = |v: Option<&[u8]>| json!(v.map(|t| String::from_utf8_lossy(&t[..t.len().min(TEXT_BOUND_BYTES)]).into_owned()));
            let present = rows - nulls;
            let mut facts = base("utf8", bound(running.min), bound(running.max), running.distinct(), running.sorted(), running.ascending_fraction());
            facts.mean_bytes = Some(if present == 0 { 0.0 } else { total as f64 / present as f64 });
            facts.max_bytes = Some(longest);
            Some(facts)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn running_statistics_and_distinct_estimates() {
        let mut running = Running::<i128>::new();
        for v in 0..100_000i128 {
            running.add(v, mix(v as u64));
        }
        assert_eq!((running.min, running.max, running.sorted()), (Some(0), Some(99_999), "ascending"));
        let estimate = running.distinct() as f64;
        assert!((estimate - 100_000.0).abs() / 100_000.0 < 0.05, "{estimate}");
        let mut few = Running::<i128>::new();
        for v in [3i128, 1, 3, 2, 1] {
            few.add(v, mix(v as u64));
        }
        assert_eq!((few.distinct(), few.sorted()), (3, "unsorted"));
    }
}
