//! Build identity of this runtime: the exact source text compiled into this binary plus its compiler settings.
//!
//! A worker request names the identity of the build that wrote it ([`WorkerBuildIdentity`]); the worker refuses a
//! request from another build before opening anything, so parent and child always agree on the request/result
//! protocol, input delivery, ABI host and result codec. Admitted packages record the same identity for the trusted
//! host items of their TCB.
//!
//! The sources are embedded at compile time (`include_str!`): nothing is read from the working tree or the installed
//! toolchain at run time, and no data is hashed. The identity is a SHA-256 digest of that embedded text (about
//! 200 KB), computed once per process.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::sync::OnceLock;

/// Every source file compiled into this binary that decides how a worker delivers inputs, loads a library, calls an
/// entry, stores parts and reports or serves the outcome: this crate (without its tests), the Verus ABI/shim framework
/// files it pins, the storage I/O it maps inputs and parts with, and the SQLSpec result codec. `(path, text)`.
const EXECUTION_SOURCES: &[(&str, &str)] = &[
    ("runtime/build.rs", include_str!("../build.rs")),
    ("runtime/src/lib.rs", include_str!("lib.rs")),
    ("runtime/src/abi.rs", include_str!("abi.rs")),
    ("runtime/src/abi/arguments.rs", include_str!("abi/arguments.rs")),
    ("runtime/src/abi/call.rs", include_str!("abi/call.rs")),
    ("runtime/src/abi/engine.rs", include_str!("abi/engine.rs")),
    ("runtime/src/abi/error.rs", include_str!("abi/error.rs")),
    ("runtime/src/abi/library.rs", include_str!("abi/library.rs")),
    ("runtime/src/abi/loader.rs", include_str!("abi/loader.rs")),
    ("runtime/src/abi/outcome.rs", include_str!("abi/outcome.rs")),
    ("runtime/src/abi/part_sink.rs", include_str!("abi/part_sink.rs")),
    ("runtime/src/abi/parts.rs", include_str!("abi/parts.rs")),
    ("runtime/src/abi/records.rs", include_str!("abi/records.rs")),
    ("runtime/src/abi/storage_library.rs", include_str!("abi/storage_library.rs")),
    ("runtime/src/answer.rs", include_str!("answer.rs")),
    ("runtime/src/identity.rs", include_str!("identity.rs")),
    ("runtime/src/process_stop.rs", include_str!("process_stop.rs")),
    ("runtime/src/serve.rs", include_str!("serve.rs")),
    ("runtime/src/serve/asset.rs", include_str!("serve/asset.rs")),
    ("runtime/src/serve/engine.rs", include_str!("serve/engine.rs")),
    ("runtime/src/serve/error.rs", include_str!("serve/error.rs")),
    ("runtime/src/serve/executor.rs", include_str!("serve/executor.rs")),
    ("runtime/src/serve/statement.rs", include_str!("serve/statement.rs")),
    ("runtime/src/worker.rs", include_str!("worker.rs")),
    ("runtime/src/worker/child.rs", include_str!("worker/child.rs")),
    ("runtime/src/worker/error.rs", include_str!("worker/error.rs")),
    ("runtime/src/worker/inputs.rs", include_str!("worker/inputs.rs")),
    ("runtime/src/worker/parent.rs", include_str!("worker/parent.rs")),
    ("runtime/src/worker/process_io.rs", include_str!("worker/process_io.rs")),
    ("runtime/src/worker/protocol.rs", include_str!("worker/protocol.rs")),
    ("runtime/src/worker/sampler.rs", include_str!("worker/sampler.rs")),
    ("runtime/src/worker/stored_answer.rs", include_str!("worker/stored_answer.rs")),
    ("runtime/src/worker/watchdog.rs", include_str!("worker/watchdog.rs")),
    ("runtime/verus/gendb_abi.rs", include_str!("../verus/gendb_abi.rs")),
    ("runtime/verus/gendb_arguments.rs", include_str!("../verus/gendb_arguments.rs")),
    ("runtime/verus/gendb_shim.rs", include_str!("../verus/gendb_shim.rs")),
    ("runtime/verus/shim_v4/records.rs", include_str!("../verus/shim_v4/records.rs")),
    ("runtime/verus/shim_v4/storage_build.rs", include_str!("../verus/shim_v4/storage_build.rs")),
    ("runtime/verus/shim_v4/storage_build_nullable.rs", include_str!("../verus/shim_v4/storage_build_nullable.rs")),
    ("runtime/verus/shim_v4/storage_derive.rs", include_str!("../verus/shim_v4/storage_derive.rs")),
    ("runtime/verus/shim_v4/query.rs", include_str!("../verus/shim_v4/query.rs")),
    ("runtime/verus/engine_shim.rs", include_str!("../verus/engine_shim.rs")),
    ("runtime/verus/engine_codec.rs", include_str!("../verus/engine_codec.rs")),
    ("storage/src/io.rs", include_str!("../../storage/src/io.rs")),
    ("storage/src/io/archive.rs", include_str!("../../storage/src/io/archive.rs")),
    ("storage/src/io/column.rs", include_str!("../../storage/src/io/column.rs")),
    ("storage/src/io/column_files.rs", include_str!("../../storage/src/io/column_files.rs")),
    ("storage/src/io/error.rs", include_str!("../../storage/src/io/error.rs")),
    ("storage/src/io/ipc.rs", include_str!("../../storage/src/io/ipc.rs")),
    ("storage/src/io/parts.rs", include_str!("../../storage/src/io/parts.rs")),
    ("storage/src/io/read_only.rs", include_str!("../../storage/src/io/read_only.rs")),
    ("storage/src/io/source_columns.rs", include_str!("../../storage/src/io/source_columns.rs")),
    ("sqlspec/src/codec.rs", include_str!("../../sqlspec/src/codec.rs")),
    ("sqlspec/src/pg_text.rs", include_str!("../../sqlspec/src/pg_text.rs")),
];

/// Compiler settings of this build (exported by `build.rs`); `debug_assertions` is appended at use.
const BUILD_SETTINGS: &str = concat!(
    "profile=",
    env!("GENDB_BUILD_PROFILE"),
    "|opt=",
    env!("GENDB_BUILD_OPT_LEVEL"),
    "|debug=",
    env!("GENDB_BUILD_DEBUG"),
    "|rustflags=",
    env!("GENDB_BUILD_CARGO_ENCODED_RUSTFLAGS"),
    "|target=",
    env!("GENDB_BUILD_TARGET"),
);

/// `gendb-runtime/<crate version>+sha256:<digest>` over every [`EXECUTION_SOURCES`] entry (path and exact text) and
/// the build settings.
pub fn runtime_build_identity() -> &'static str {
    static IDENTITY: OnceLock<String> = OnceLock::new();
    IDENTITY.get_or_init(|| {
        let mut digest = Sha256::new();
        for (path, text) in EXECUTION_SOURCES {
            digest.update(path.as_bytes());
            digest.update([0]);
            digest.update(text.as_bytes());
            digest.update([0]);
        }
        digest.update(BUILD_SETTINGS.as_bytes());
        digest.update(format!("|assertions={}", cfg!(debug_assertions)).as_bytes());
        let hex: String = digest.finalize().iter().map(|byte| format!("{byte:02x}")).collect();
        format!("gendb-runtime/{}+sha256:{hex}", env!("CARGO_PKG_VERSION"))
    })
}

/// The build a worker request was written by. JSON `{"runtime": "gendb-runtime/0.1.0+sha256:..."}`; a request of
/// the earlier GenDB version (fields `registry`, `gate`, `runtime`, `compiler`) never equals it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WorkerBuildIdentity {
    pub runtime: String,
}

impl WorkerBuildIdentity {
    pub fn current() -> Self {
        Self { runtime: runtime_build_identity().to_string() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Stable within a process, names this crate, and covers every source module of the crate.
    #[test]
    fn identity_is_stable_and_covers_the_crate_modules() {
        assert_eq!(runtime_build_identity(), runtime_build_identity());
        assert!(runtime_build_identity().starts_with("gendb-runtime/0.1.0+sha256:"), "{}", runtime_build_identity());
        assert_eq!(runtime_build_identity().len(), "gendb-runtime/0.1.0+sha256:".len() + 64);
        let listed: Vec<&str> = EXECUTION_SOURCES.iter().map(|(path, _)| *path).collect();
        let source_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut modules = vec![];
        for entry in std::fs::read_dir(&source_root)
            .unwrap()
            .chain(["abi", "serve", "worker"].iter().flat_map(|dir| std::fs::read_dir(source_root.join(dir)).unwrap()))
        {
            let path = entry.unwrap().path();
            let relative = path.strip_prefix(source_root.parent().unwrap()).unwrap().to_string_lossy().into_owned();
            if relative.ends_with(".rs") && !relative.ends_with("tests.rs") {
                modules.push(format!("runtime/{relative}"));
            }
        }
        for module in &modules {
            assert!(listed.contains(&module.as_str()), "{module} is not part of the runtime identity");
        }
    }
}
