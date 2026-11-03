//! The authors of a workload run: the workload storage author (when the request asks for the storage phase) and one
//! provider session per query, each wrapped so that its work holds the host activity lease (timed measurements then
//! never overlap an author's builds or tools).

use super::WorkloadError;
use super::lifecycle::{author_inspection_directory, storage_inspection_directory};
use crate::controller::author::{AuthorCall, AuthorTransport, Capability, ProviderCondition};
use crate::controller::ledger::{Call, PREDISPATCH_REFUSAL_PREFIX, Receipt};
use crate::controller::limits::Money;
use crate::controller::records::now_unix_ms;
use crate::providers::claude_code::declared_usage_scope;
use crate::providers::{AuthorModel, ClaudeCode, LocalToolServer};
use crate::query::host_locks::HostLocks;
use serde_json::Value;
use std::path::Path;

/// Words after the gendb executable that start the author's local-tool MCP server (`gendb author-tools mcp`); the
/// server receives the tool context and a fresh evidence directory as its two final arguments.
pub const LOCAL_TOOL_SERVER_WORDS: [&str; 2] = ["author-tools", "mcp"];

/// The authors of one workload run: the storage author (`None` without the storage phase) and one per query.
pub struct WorkloadAuthors<A> {
    pub storage: Option<A>,
    pub queries: Vec<A>,
}

/// Inspect the configured Claude Code executable once per author (`--version`/`--help` only, never inference), each a
/// transport of the request's `model`, with evidence under `<run>/author-inspection/{workload-storage,query-NNNN}`.
/// `framework_executable` (the running gendb binary) serves the authors' local tools. A version without a declared usage scope is refused here, before any data
/// or author work: its receipts could not be counted exactly (the pinned version is explicit configuration, never
/// switched).
pub fn inspect_authors(
    author_executable: &Path,
    model: AuthorModel,
    framework_executable: &Path,
    root: &Path,
    queries: usize,
    storage_phase: bool,
) -> Result<WorkloadAuthors<ClaudeCode>, WorkloadError> {
    let tool_server = LocalToolServer {
        program: framework_executable.to_path_buf(),
        arguments: LOCAL_TOOL_SERVER_WORDS.iter().map(|word| word.to_string()).collect(),
    };
    let inspect = |evidence: &Path| -> Result<ClaudeCode, String> {
        let author = ClaudeCode::inspect(author_executable.to_path_buf(), model, evidence, tool_server.clone()).map_err(|error| error.to_string())?;
        let version = author.capability().version;
        if declared_usage_scope(&version).is_none() {
            return Err(format!(
                "Claude Code {version} ({}) has no declared usage scope for its reported cost and tokens; configure an inspected version",
                author_executable.display()
            ));
        }
        Ok(author)
    };
    let storage = if storage_phase { Some(inspect(&storage_inspection_directory(root)).map_err(WorkloadError::StorageAuthor)?) } else { None };
    let queries = (0..queries)
        .map(|query| inspect(&author_inspection_directory(root, query)).map_err(|detail| WorkloadError::Author { query, detail }))
        .collect::<Result<_, _>>()?;
    Ok(WorkloadAuthors { storage, queries })
}

/// An author whose provider work holds the host activity lease. A transport that leases every shell tool itself
/// (`tool_activity_lock`) runs without a whole-invocation lease; otherwise the whole invocation holds one. Every
/// other hook is the inner transport's.
pub struct HostLeasedAuthor<T> {
    inner: T,
    host_locks: HostLocks,
}

impl<T: AuthorTransport> HostLeasedAuthor<T> {
    pub fn new(inner: T, host_locks: HostLocks) -> Self {
        Self { inner, host_locks }
    }

    /// `Ok(true)`: the transport leases each tool itself; `Ok(false)`: the caller must hold a lease for the call.
    fn install_tool_leases(&mut self) -> Result<bool, String> {
        self.host_locks.validate()?;
        self.inner.tool_activity_lock(&self.host_locks.activity_lock)
    }
}

impl<T: AuthorTransport> AuthorTransport for HostLeasedAuthor<T> {
    fn capability(&self) -> Capability {
        self.inner.capability()
    }

    fn preflight(&mut self) -> Result<(), String> {
        self.host_locks.validate()?;
        self.inner.preflight()?;
        self.install_tool_leases()?;
        Ok(())
    }

    fn render_only(&self) -> bool {
        self.inner.render_only()
    }

    fn definitely_not_dispatched(&self, call_dir: &Path) -> Result<bool, String> {
        self.inner.definitely_not_dispatched(call_dir)
    }

    fn tool_activity_lock(&mut self, path: &Path) -> Result<bool, String> {
        self.inner.tool_activity_lock(path)
    }

    fn provider_session_exists(&self, call_dir: &Path) -> bool {
        self.inner.provider_session_exists(call_dir)
    }

    fn usage_scope(&self) -> Option<crate::controller::ledger::UsageScope> {
        self.inner.usage_scope()
    }

    fn configure_context(&mut self, context: &Value) -> Result<(), String> {
        self.inner.configure_context(context)
    }

    fn invoke(&mut self, request: &AuthorCall) -> Receipt {
        let lease = self.install_tool_leases().and_then(|per_tool| if per_tool { Ok(None) } else { self.host_locks.activity().map(Some) });
        match lease {
            Ok(_lease) => self.inner.invoke(request),
            Err(error) => predispatch_refusal(request.call, request.session_id, &error),
        }
    }

    fn recover_receipt(&self, call: &Call, session_id: &str, call_dir: &Path, workspace: &Path) -> Result<Option<Receipt>, String> {
        self.inner.recover_receipt(call, session_id, call_dir, workspace)
    }

    fn provider_condition(&self, call_dir: &Path, receipt: &Receipt) -> Option<ProviderCondition> {
        self.inner.provider_condition(call_dir, receipt)
    }

    /// The wait holds no host activity lease: measurements may run meanwhile.
    fn wait_for_provider(&mut self, until_unix_ms: u64) {
        self.inner.wait_for_provider(until_unix_ms)
    }
}

/// The receipt of a call refused before any provider launch: zero cost, no tokens, no result, no time.
fn predispatch_refusal(call: &Call, session_id: &str, error: &str) -> Receipt {
    Receipt {
        call_id: call.id,
        session_id: session_id.into(),
        ended_unix_ms: now_unix_ms(),
        elapsed_ms: 0,
        reported_cost_usd: Some(Money::default()),
        billed_cost_usd: None,
        tokens: None,
        outcome: format!("{PREDISPATCH_REFUSAL_PREFIX}{error}"),
        raw_result: None,
        output: None,
        usage_scope: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::ledger::Ledger;
    use crate::controller::limits::tests::limits;
    use crate::controller::records;
    use crate::controller::test_support::{FixtureAuthor, scratch_root};
    use serde_json::json;

    fn locks(root: &Path) -> HostLocks {
        HostLocks { activity_lock: root.join("activity.lock"), build_lock: root.join("build.lock"), race_lock: root.join("race.lock") }
    }

    /// The wrapper forwards receipt recovery (a lost call stays recoverable) and the provider-condition hooks (the
    /// controller's waits depend on them), and refuses a call it cannot lease with a pre-dispatch refusal receipt
    /// (zero cost, no time) without invoking the provider.
    #[test]
    fn leased_author_forwards_recovery_and_refuses_unleased_calls_before_dispatch() {
        let root = scratch_root("leased-author");
        records::create_dir(&root).unwrap();
        let mut ledger = Ledger::open(&root, json!({"fixture":true}), limits()).unwrap();
        let call = ledger.begin_call().unwrap();
        let call_dir = root.join("calls/0001");
        records::create_dir(&call_dir).unwrap();
        let session = ledger.state.session_id.clone();
        records::write_new_json(&call_dir.join("fixture-terminal-result.json"), &json!({"session_id":session,"subtype":"success","duration_ms":7,"usage_scope":"session"})).unwrap();
        let mut author = HostLeasedAuthor::new(FixtureAuthor::default(), locks(&root));
        let recovered = author.recover_receipt(&call, &session, &call_dir, &root).unwrap().expect("forwarded recovery");
        assert_eq!(recovered.elapsed_ms, 7);
        author.inner.conditions.insert(call.id, ProviderCondition::ContextExhausted);
        assert_eq!(author.provider_condition(&call_dir, &recovered), Some(ProviderCondition::ContextExhausted));
        author.wait_for_provider(42);
        assert_eq!(author.inner.waits, vec![42]);

        let mut unleased = HostLeasedAuthor::new(FixtureAuthor::default(), locks(Path::new("relative")));
        let workspace = root.join("author");
        let request = AuthorCall { call: &call, session_id: &session, resume: false, prompt: "p", workspace: &workspace, call_dir: &call_dir, limits: &limits() };
        let refusal = unleased.invoke(&request);
        assert!(refusal.predispatch_refusal(), "{}", refusal.outcome);
        assert_eq!(unleased.inner.calls, 0);

        let mut leased = HostLeasedAuthor::new(FixtureAuthor::default(), locks(&root));
        assert_eq!(leased.invoke(&request).outcome, "success");
        assert_eq!(leased.inner.calls, 1);
    }
}
