//! Hardware of a workload run: the worker counts the user requests (every evaluation and serving cell runs at each),
//! and a read-only observation of the host the run executes on, recorded in author context (including the crash-dump
//! setting every process of the run inherits, `crash_dumps`).

use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// The runtime ABI's largest worker count (`gendb_runtime` refuses more).
pub const MAX_WORKERS: usize = 64;

/// The user's requested worker counts.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Hardware {
    /// Distinct positive worker counts, each at most the CPUs available to this process (and [`MAX_WORKERS`]).
    pub threads: Vec<usize>,
}

impl Hardware {
    pub fn validate(&self) -> Result<(), String> {
        let distinct: BTreeSet<_> = self.threads.iter().collect();
        if distinct.is_empty() || distinct.len() != self.threads.len() || distinct.contains(&0) {
            return Err("hardware.threads must be distinct positive worker counts".into());
        }
        let available = std::thread::available_parallelism().map_err(|e| format!("available parallelism: {e}"))?.get().min(MAX_WORKERS);
        if self.threads.iter().any(|workers| *workers > available) {
            return Err(format!("hardware.threads {:?} exceeds the {available} workers available to this process", self.threads));
        }
        Ok(())
    }
}

/// Read-only description of the host: CPU affinity, topology and caches, memory and NUMA nodes. Observed once per
/// process from `/proc` and sysfs; no timing and no data is read. Missing metadata is `null`/empty.
pub fn observe_host() -> Value {
    static OBSERVED: OnceLock<Value> = OnceLock::new();
    OBSERVED.get_or_init(observe_host_now).clone()
}

fn observe_host_now() -> Value {
    let status = fs::read_to_string("/proc/self/status").unwrap_or_default();
    let status_field = |key: &str| status.lines().find_map(|line| line.strip_prefix(key)).map(str::trim).map(str::to_string);
    let affinity = status_field("Cpus_allowed_list:");
    let cpus = affinity.as_deref().map(cpu_list).unwrap_or_default();
    let topology = cpu_topology(&cpus);
    let cpuinfo = fs::read_to_string("/proc/cpuinfo").unwrap_or_default();
    let first_cpu = cpuinfo.split("\n\n").next().unwrap_or_default();
    let cpu_field = |key: &str| {
        first_cpu.lines().find_map(|line| line.split_once(':').filter(|(name, _)| name.trim() == key).map(|(_, value)| value.trim().to_string()))
    };
    let meminfo = fs::read_to_string("/proc/meminfo").unwrap_or_default();
    let memory_bytes = |key: &str| {
        meminfo
            .lines()
            .find_map(|line| line.split_once(':').filter(|(name, _)| *name == key))
            .and_then(|(_, value)| value.split_whitespace().next()?.parse::<u64>().ok())
            .and_then(|kib| kib.checked_mul(1024))
    };
    json!({"source":"read-only process affinity, /proc/cpuinfo, /proc/meminfo and sysfs topology/cache metadata; once per process; no timing or data scan",
        "observed_unix_ms":super::records::now_unix_ms(),
        "cpu_model":cpu_field("model name"),"cpu_features":cpu_field("flags"),
        "affinity_cpu_list":affinity,"logical_cpus_in_affinity":cpus.len(),
        "physical_cores_in_affinity":(topology.cores > 0).then_some(topology.cores),
        "packages_in_affinity":(topology.packages > 0).then_some(topology.packages),"caches":topology.caches,
        "host_memory_bytes":{"total":memory_bytes("MemTotal"),"available":memory_bytes("MemAvailable"),"swap_free":memory_bytes("SwapFree")},
        "numa_nodes":numa_nodes(),"allowed_memory_nodes":status_field("Mems_allowed_list:"),
        "crash_dumps":super::crash_dumps::observe(),
        "memory_scope":"host observations, not reserved capacity or a process quota",
        "missing_metadata":"null/empty observations mean unavailable; the requested worker counts are recorded separately (hardware)"})
}

/// Logical CPU ids of a kernel CPU list such as `0-3,8,10-11`. Malformed parts are skipped.
fn cpu_list(text: &str) -> Vec<usize> {
    text.trim()
        .split(',')
        .flat_map(|part| {
            let (start, end) = part.split_once('-').unwrap_or((part, part));
            match (start.parse::<usize>(), end.parse::<usize>()) {
                (Ok(start), Ok(end)) if start <= end && end - start <= 65536 => (start..=end).collect(),
                _ => Vec::new(),
            }
        })
        .collect()
}

struct CpuTopology {
    packages: usize,
    cores: usize,
    /// One entry per distinct cache kind: level, type, size, line and how many CPUs share each instance.
    caches: Vec<Value>,
}

fn cpu_topology(cpus: &[usize]) -> CpuTopology {
    let read = |path: &Path| fs::read_to_string(path).ok().map(|text| text.trim().to_string());
    let (mut packages, mut cores, mut caches) = (BTreeSet::new(), BTreeSet::new(), BTreeSet::new());
    for cpu in cpus {
        let root = PathBuf::from(format!("/sys/devices/system/cpu/cpu{cpu}"));
        if let (Some(package), Some(core)) = (read(&root.join("topology/physical_package_id")), read(&root.join("topology/core_id"))) {
            packages.insert(package.clone());
            cores.insert((package, core));
        }
        for index in fs::read_dir(root.join("cache")).into_iter().flatten().flatten().map(|entry| entry.path()) {
            let fields = ["level", "type", "size", "coherency_line_size", "shared_cpu_list"].map(|name| read(&index.join(name)));
            if let [Some(level), Some(kind), Some(size), Some(line), Some(shared)] = fields {
                caches.insert((level, kind, size, line, shared));
            }
        }
    }
    let mut instances = BTreeMap::new();
    for (level, kind, size, line, shared) in caches {
        *instances.entry((level, kind, size, line, cpu_list(&shared).len())).or_insert(0usize) += 1;
    }
    let caches = instances
        .into_iter()
        .map(|((level, kind, size, line, sharing), count)| {
            json!({"level":level,"type":kind,"size_per_instance":size,"line_bytes":line,
                "logical_cpus_sharing_each_instance":sharing,"instances_visible_to_affinity":count})
        })
        .collect();
    CpuTopology { packages: packages.len(), cores: cores.len(), caches }
}

fn numa_nodes() -> Vec<Value> {
    let read = |path: &Path| fs::read_to_string(path).ok().map(|text| text.trim().to_string());
    let mut nodes: Vec<Value> = fs::read_dir("/sys/devices/system/node")
        .into_iter()
        .flatten()
        .flatten()
        .filter_map(|entry| {
            let name = entry.file_name().to_string_lossy().into_owned();
            name.strip_prefix("node").is_some_and(|id| id.parse::<u32>().is_ok()).then(|| {
                json!({"node":name,"cpu_list":read(&entry.path().join("cpulist")),"distance":read(&entry.path().join("distance"))})
            })
        })
        .collect();
    nodes.sort_by_key(|node| node["node"].to_string());
    nodes
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn worker_counts_must_be_distinct_positive_and_available() {
        assert!(Hardware { threads: vec![1] }.validate().is_ok());
        assert!(Hardware { threads: vec![] }.validate().is_err());
        assert!(Hardware { threads: vec![0] }.validate().is_err());
        assert!(Hardware { threads: vec![1, 1] }.validate().is_err());
        assert!(Hardware { threads: vec![MAX_WORKERS + 1] }.validate().is_err());
        assert_eq!(cpu_list("0-2,5,x,7-6"), vec![0, 1, 2, 5]);
    }
}
