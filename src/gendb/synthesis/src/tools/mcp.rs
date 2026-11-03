//! The `gendb_local` stdio MCP server started by the provider for one author call: a thin client that lists the
//! tools, forwards each job call to the session's retained role (workload storage, query or engine) and answers `wait`
//! itself. It opens no data, compiles nothing and holds no lock. It writes `service.json` when ready,
//! `mcp-protocol.json` (the JSON-RPC methods it answered), a `refused-NNNN.json` for each job call whose arguments it
//! refused, and `service-finished.json` when the provider closes its stdin.
//!
//! Threads, so that no call waits behind another call's job:
//! - the reader answers `initialize`, `ping` and `tools/list` at once and hands every other call on;
//! - one forwarder takes the job calls in the order received and forwards one at a time, as the role runs a session's
//!   jobs one at a time; a job is answered only when it ends, which can take long (a whole-crate check, or a trial's
//!   wait for another session's timing lease);
//! - each [`WAIT_TOOL`] call gets its own thread: it answers from the calls this server received (their state and
//!   answers) or, for a job this server did not receive (an earlier server process of the same call), from the job's
//!   records, as soon as the job ends or after its bound with the job's status (queued or running). It takes no lock and
//!   runs nothing, so an author waits for a job without a Bash command, which would hold the shared activity lease that
//!   a timed job needs alone to start;
//! - a progress reporter: for every unanswered call whose client sent a `progressToken` (queued, running or waiting) it
//!   sends an MCP progress notification every [`PROGRESS_INTERVAL`] until the answer, so the client's silence limit
//!   (Claude Code: 1800 s for stdio servers) aborts no call that is still queued or running. This adds no deadline; the
//!   client's own limits are unchanged.

use super::{LocalJobArguments, LocalToolContext, CONTEXT_FORMAT, WAIT_TOOL, WaitArguments, compact_job_record, tool_list};
use crate::controller::records::{now_unix_ms, read_json, write_json_atomic, write_new_json};
use crate::controller::session::forward_job;
use gendb_verification::admission::{AdmissionError, FailureClass};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::io::{BufRead, Write};
use std::path::{Path, PathBuf};
use std::sync::mpsc::{Receiver, channel};
use std::sync::{Condvar, Mutex, MutexGuard, PoisonError};
use std::time::{Duration, Instant};

/// Usage text of the server command (the provider appends these two arguments).
pub const USAGE: &str = "CONTEXT.json FRESH_EVIDENCE_DIRECTORY: serve the gendb_local tools of one author call over stdio MCP";

/// How often an unanswered tool call reports progress (a framework scheduling constant, far below the client's silence
/// limit; not a deadline).
pub const PROGRESS_INTERVAL: Duration = Duration::from_secs(60);

/// How often a `wait` looks again at the job records (a job this server forwards also wakes its waiters when answered).
const WAIT_POLL: Duration = Duration::from_secs(1);

fn response(id: Value, result: Value) -> Value {
    json!({"jsonrpc":"2.0","id":id,"result":result})
}

fn error(id: Value, code: i64, message: &str) -> Value {
    json!({"jsonrpc":"2.0","id":id,"error":{"code":code,"message":message}})
}

/// The MCP result of a tool call: `value` as text and as structured content.
fn tool_result(is_error: bool, value: Value) -> Value {
    json!({"content":[{"type":"text","text":value.to_string()}],"structuredContent":value,"isError":is_error})
}

/// The failure class a forwarding error names by its prefix; any other error came from the tool path.
fn forwarding_error_class(error: &str) -> FailureClass {
    FailureClass::ALL.into_iter().find(|class| error.starts_with(&format!("{}:", class.name()))).unwrap_or(FailureClass::ToolFailure)
}

/// Write one JSON-RPC message as a line.
fn send(output: &Mutex<impl Write>, message: &Value) -> Result<(), String> {
    let mut output = output.lock().map_err(|_| "MCP output lock poisoned".to_string())?;
    serde_json::to_writer(&mut *output, message).map_err(|e| e.to_string())?;
    output.write_all(b"\n").and_then(|_| output.flush()).map_err(|e| e.to_string())
}

/// Where one received tool call stands.
enum CallState {
    /// A job call waiting for the forwarder, behind earlier job calls.
    Queued,
    /// A job call forwarded to the role, which runs it (a trial or profile includes its wait for the timing lease).
    Forwarded,
    /// A `wait` call, waiting.
    Waiting,
    /// Answered: the MCP result sent to the client.
    Answered(Value),
}

/// One `tools/call` this server received.
struct ReceivedCall {
    /// 1-based, in the order received (the ordinal of a client refusal record).
    ordinal: u64,
    tool: String,
    /// A job call's `job_name` argument (`None` for a `wait` call, or when the arguments name none).
    job_name: Option<String>,
    progress_token: Option<Value>,
    received: Instant,
    /// The last progress value sent: whole seconds since `received`, strictly increasing as MCP requires.
    reported_seconds: u64,
    next_report: Instant,
    state: CallState,
}

impl ReceivedCall {
    fn is_job(&self) -> bool {
        self.tool != WAIT_TOOL
    }

    fn answered(&self) -> bool {
        matches!(self.state, CallState::Answered(_))
    }
}

/// Every tool call this server received, shared by its threads; `changed` is notified on every change.
#[derive(Default)]
struct Calls {
    table: Mutex<CallTable>,
    changed: Condvar,
}

#[derive(Default)]
struct CallTable {
    calls: Vec<ReceivedCall>,
    /// The provider closed stdin: no call follows.
    input_closed: bool,
    /// The forwarder has ended too: no job answer follows, and the progress reporter ends.
    forwarding_ended: bool,
}

/// What a `wait` finds about a job.
enum JobStatus {
    /// The MCP result of the job's call (this server's answer, or rebuilt from the job's `result.json`).
    Ended(Value),
    /// Queued behind `ahead` earlier unanswered job calls of this server.
    Queued { ahead: usize },
    /// Started by the role (its job directory, when it exists yet).
    Running { directory: Option<PathBuf> },
    /// No job of that name: neither received by this server nor recorded under the call's evidence directory.
    Unknown,
}

impl CallTable {
    /// The latest job call named `job_name`.
    fn latest_job(&self, job_name: &str) -> Option<&ReceivedCall> {
        self.calls.iter().rev().find(|call| call.is_job() && call.job_name.as_deref() == Some(job_name))
    }

    /// The unanswered job calls received before `ordinal`.
    fn jobs_ahead(&self, ordinal: u64) -> usize {
        self.calls.iter().filter(|call| call.is_job() && call.ordinal < ordinal && !call.answered()).count()
    }

}

impl Calls {
    /// The table; a panicked thread leaves it usable (each change is one assignment).
    fn lock(&self) -> MutexGuard<'_, CallTable> {
        self.table.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Record a received call; returns its ordinal.
    fn receive(&self, tool: &str, job_name: Option<String>, progress_token: Option<Value>, state: CallState) -> u64 {
        let mut table = self.lock();
        let ordinal = table.calls.len() as u64 + 1;
        let received = Instant::now();
        table.calls.push(ReceivedCall { ordinal, tool: tool.into(), job_name, progress_token, received, reported_seconds: 0, next_report: received + PROGRESS_INTERVAL, state });
        self.changed.notify_all();
        ordinal
    }

    fn set(&self, ordinal: u64, state: CallState) {
        let mut table = self.lock();
        if let Some(call) = table.calls.iter_mut().find(|call| call.ordinal == ordinal) {
            call.state = state;
        }
        self.changed.notify_all();
    }

    fn close_input(&self) {
        self.lock().input_closed = true;
        self.changed.notify_all();
    }

    fn end_forwarding(&self) {
        self.lock().forwarding_ended = true;
        self.changed.notify_all();
    }

    /// What this server knows of the latest job call named `job_name`; `None` when it received none.
    fn job_status(&self, job_name: &str) -> Option<JobStatus> {
        let table = self.lock();
        let call = table.latest_job(job_name)?;
        Some(match &call.state {
            CallState::Answered(answer) => JobStatus::Ended(answer.clone()),
            CallState::Queued => JobStatus::Queued { ahead: table.jobs_ahead(call.ordinal) },
            CallState::Forwarded | CallState::Waiting => JobStatus::Running { directory: None },
        })
    }

    /// Wait for a change, at most `timeout`; `false` once the input is closed (no one reads a later answer).
    fn wait_for_change(&self, timeout: Duration) -> bool {
        let table = self.lock();
        if table.input_closed {
            return false;
        }
        let (table, _) = self.changed.wait_timeout(table, timeout).unwrap_or_else(PoisonError::into_inner);
        !table.input_closed
    }
}

/// Serve the tools of `context_path` until `input` ends; job evidence goes under `evidence_root`.
pub fn serve(context_path: &Path, evidence_root: &Path, input: impl BufRead, output: impl Write + Send) -> Result<(), String> {
    let output = Mutex::new(output);
    let context_path = context_path.canonicalize().map_err(|e| format!("{}: {e}", context_path.display()))?;
    let context: LocalToolContext = read_json(&context_path).map_err(|e| e.to_string())?;
    if context.format_version != CONTEXT_FORMAT || context.author_workspace.as_os_str().is_empty() {
        return Err("unsupported local-job context".into());
    }
    std::fs::create_dir_all(evidence_root).map_err(|e| format!("{}: {e}", evidence_root.display()))?;
    let evidence_root = evidence_root.canonicalize().map_err(|e| e.to_string())?;
    // Overwritten when the provider restarts the server within one call (as in the earlier GenDB version).
    write_json_atomic(&evidence_root.join("service.json"), &json!({"format_version":1,"status":"ready","transport":"stdio_mcp_thin_client",
        "context":context_path,"prepared_owner_opens":0,"retained_owner_service":context.session_service.service_record,
        "pid":std::process::id(),"diagnostic_only":true}))
    .map_err(|e| e.to_string())?;
    // A provider may report this server connected yet offer its tools to no turn; the methods it actually answered
    // are recorded so the trajectory audit can tell a missing handshake from an unused tool.
    let protocol_record = evidence_root.join("mcp-protocol.json");
    let mut served = BTreeMap::<String, Value>::new();
    let calls = Calls::default();
    let (context, evidence_root, calls, output) = (&context, evidence_root.as_path(), &calls, &output);
    let (jobs, queue) = channel::<(Value, Value, u64)>();
    let (read, forwarded) = std::thread::scope(|scope| {
        let forwarder = scope.spawn(move || forward_jobs(queue, context, evidence_root, calls, output));
        scope.spawn(move || report_progress(calls, output));
        let read = (|| -> Result<(), String> {
            for line in input.lines() {
                let line = line.map_err(|e| e.to_string())?;
                if line.trim().is_empty() {
                    continue;
                }
                let request: Value = serde_json::from_str(&line).map_err(|e| e.to_string())?;
                let id = request.get("id").cloned().unwrap_or(Value::Null);
                let method = request["method"].as_str().unwrap_or("");
                let now = now_unix_ms();
                let entry = served.entry(method.to_string()).or_insert_with(|| json!({"count":0,"first_unix_ms":now,"last_unix_ms":now}));
                entry["count"] = json!(entry["count"].as_u64().unwrap_or(0) + 1);
                entry["last_unix_ms"] = json!(now);
                if method != "tools/call" {
                    // Job records already cover tool calls; keep this write off that path.
                    write_json_atomic(&protocol_record, &json!({"format_version":1,"pid":std::process::id(),"served_methods":served,
                        "scope":"JSON-RPC methods this stdio server actually received and answered; tool call detail stays in the per-job records"}))
                    .map_err(|e| e.to_string())?;
                }
                let answer = match method {
                    "initialize" => Some(response(id, json!({"protocolVersion":request.pointer("/params/protocolVersion").and_then(Value::as_str).unwrap_or("2024-11-05"),
                        "capabilities":{"tools":{"listChanged":false}},"serverInfo":{"name":"gendb-local","version":"1"}}))),
                    "ping" => Some(response(id, json!({}))),
                    "tools/list" => Some(response(id, json!({"tools":tool_list(context)}))),
                    "tools/call" => {
                        let tool = request.pointer("/params/name").and_then(Value::as_str).unwrap_or("");
                        let token = request.pointer("/params/_meta/progressToken").cloned();
                        if tool == WAIT_TOOL {
                            let ordinal = calls.receive(tool, None, token, CallState::Waiting);
                            scope.spawn(move || {
                                let answer = wait_for_job(calls, evidence_root, &request);
                                calls.set(ordinal, CallState::Answered(answer.clone()));
                                // A failed write is not this thread's to report: the reader's and the forwarder's
                                // writes on the same output fail too.
                                let _ = send(output, &response(id, answer));
                            });
                        } else {
                            let job_name = request.pointer("/params/arguments/job_name").and_then(Value::as_str).map(String::from);
                            let ordinal = calls.receive(tool, job_name, token, CallState::Queued);
                            jobs.send((id, request, ordinal)).map_err(|_| "the job forwarder stopped".to_string())?;
                        }
                        None
                    }
                    method if method.starts_with("notifications/") => None,
                    _ => Some(error(id, -32601, "method not found")),
                };
                if let Some(answer) = answer {
                    send(output, &answer)?;
                }
            }
            Ok(())
        })();
        // The forwarder answers the job calls received so far, then ends; waits end at once.
        drop(jobs);
        calls.close_input();
        let forwarded = forwarder.join().unwrap_or_else(|_| Err("the job forwarder panicked".into()));
        calls.end_forwarding();
        (read, forwarded)
    });
    // A forwarder that stopped (its output failed) also stops the reader: its error is the cause.
    forwarded.and(read)?;
    let table = calls.lock();
    let job_calls = table.calls.iter().filter(|call| call.is_job()).count();
    write_json_atomic(&evidence_root.join("service-finished.json"), &json!({"format_version":1,"status":"stopped","jobs":job_calls,
        "waits":table.calls.len() - job_calls,"prepared_owner_opens":0,"pid":std::process::id()}))
    .map_err(|e| e.to_string())
}

/// The forwarder: each job call in the order received, one at a time, answered when its job ends.
fn forward_jobs(queue: Receiver<(Value, Value, u64)>, context: &LocalToolContext, evidence_root: &Path, calls: &Calls, output: &Mutex<impl Write>) -> Result<(), String> {
    for (id, request, ordinal) in queue {
        calls.set(ordinal, CallState::Forwarded);
        let answer = call_tool(context, evidence_root, &request, ordinal);
        calls.set(ordinal, CallState::Answered(answer.clone()));
        send(output, &response(id, answer))?;
    }
    Ok(())
}

/// One job `tools/call`: parse the arguments, forward the job, answer its compact record (`isError` for a refusal).
fn call_tool(context: &LocalToolContext, evidence_root: &Path, request: &Value, ordinal: u64) -> Value {
    let name = request.pointer("/params/name").and_then(Value::as_str).unwrap_or("");
    let arguments = request.pointer("/params/arguments").cloned().unwrap_or(Value::Null);
    let parsed = serde_json::from_value::<LocalJobArguments>(arguments);
    let client_refusal = parsed.is_err();
    let forwarded = match parsed {
        Ok(arguments) => forward_job(&context.session_service, evidence_root, name, json!(arguments)),
        Err(error) => Err(format!("invalid tool arguments: {error}")),
    };
    match forwarded {
        Ok(record) => {
            let compact = compact_job_record(&record);
            tool_result(compact["status"] == "refused", compact)
        }
        Err(error) => {
            let class = if client_refusal { FailureClass::MissingInput } else { forwarding_error_class(&error) };
            let mut refused = json!({"format_version":1,"job_id":ordinal,"action":name,"status":"refused","failure_class":class,"stage":name,
                "error":error,"diagnostic_only":true,"official_measurement":false});
            if client_refusal {
                let path: PathBuf = evidence_root.join(format!("refused-{ordinal:04}.json"));
                refused["refusal_record"] = json!(path);
                let _ = write_new_json(&path, &refused);
            }
            tool_result(true, refused)
        }
    }
}

/// One `wait` call: the job's answer as soon as the latest job named `job_name` ends; else, after the call's bound
/// (`wait_seconds`) or once the input is closed, its status. A job this server did not receive is read from its newest
/// job directory (`<NNNN>-<job_name>`) under `evidence_root`; a name found nowhere for one poll interval is a
/// `missing_input` refusal. Takes no lock and runs nothing.
fn wait_for_job(calls: &Calls, evidence_root: &Path, request: &Value) -> Value {
    let refusal = |error: String| {
        tool_result(true, json!({"format_version":1,"action":WAIT_TOOL,"status":"refused","failure_class":FailureClass::MissingInput,"error":error,
            "diagnostic_only":true,"official_measurement":false}))
    };
    let arguments = request.pointer("/params/arguments").cloned().unwrap_or(Value::Null);
    let checked = serde_json::from_value::<WaitArguments>(arguments)
        .map_err(|e| AdmissionError::missing_input(format!("invalid tool arguments: {e}")))
        .and_then(|arguments| arguments.bound().map(|bound| (arguments, bound)));
    let (arguments, bound) = match checked {
        Ok(checked) => checked,
        Err(error) => return refusal(error.to_string()),
    };
    let job_name = arguments.job_name.as_str();
    let started = Instant::now();
    let mut unknown_since: Option<Instant> = None;
    loop {
        let status = match calls.job_status(job_name) {
            // Forwarded by this server: the role's job directory, once the role has started it.
            Some(JobStatus::Running { .. }) => match job_record(evidence_root, job_name) {
                JobStatus::Running { directory } => JobStatus::Running { directory },
                _ => JobStatus::Running { directory: None },
            },
            Some(status) => status,
            None => job_record(evidence_root, job_name),
        };
        let status = match status {
            JobStatus::Ended(answer) => return answer,
            JobStatus::Unknown => {
                // Its call may still be arriving: refused only when one poll interval passed without it, whatever the bound.
                let left = WAIT_POLL.saturating_sub(unknown_since.get_or_insert_with(Instant::now).elapsed());
                if left.is_zero() || !calls.wait_for_change(left) {
                    return refusal(format!("no local job named {job_name} in this author call (its jobs are under {})", evidence_root.display()));
                }
                continue;
            }
            JobStatus::Queued { ahead } => json!({"status":"queued","jobs_ahead":ahead}),
            JobStatus::Running { directory } => json!({"status":"running","job_directory":directory}),
        };
        let left = bound.saturating_sub(started.elapsed());
        if left.is_zero() || !calls.wait_for_change(left.min(WAIT_POLL)) {
            let mut answer = json!({"format_version":1,"action":WAIT_TOOL,"job_name":job_name,"waited_ms":started.elapsed().as_millis() as u64,
                "next":"the job has not ended: call wait again (it holds no lock)","diagnostic_only":true,"official_measurement":false});
            if let (Some(answer), Some(status)) = (answer.as_object_mut(), status.as_object()) {
                answer.extend(status.clone());
            }
            return tool_result(false, answer);
        }
    }
}

/// What the job records under `evidence_root` say of the newest job named `job_name` (the highest `<NNNN>` of its
/// `<NNNN>-<job_name>` directories): ended (its `result.json` holds a final status), running, or unknown.
fn job_record(evidence_root: &Path, job_name: &str) -> JobStatus {
    let suffix = format!("-{job_name}");
    let newest = std::fs::read_dir(evidence_root)
        .into_iter()
        .flatten()
        .flatten()
        .filter_map(|entry| {
            let name = entry.file_name().into_string().ok()?;
            let number = name.strip_suffix(&suffix).filter(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))?.parse::<u64>().ok()?;
            Some((number, entry.path()))
        })
        .max_by_key(|(number, _)| *number);
    let Some((_, directory)) = newest else { return JobStatus::Unknown };
    match read_json::<Value>(&directory.join("result.json")) {
        // Written once when the job ends (create, then write): a partial file reads as still running.
        Ok(record) if record["status"] == "completed" || record["status"] == "refused" => {
            let compact = compact_job_record(&record);
            JobStatus::Ended(tool_result(compact["status"] == "refused", compact))
        }
        _ => JobStatus::Running { directory: Some(directory) },
    }
}

/// The progress reporter (module documentation), until the input is closed and the forwarder has ended. A notification
/// is written while the table is locked, so none follows its call's answer (an answer is recorded before it is sent).
fn report_progress(calls: &Calls, output: &Mutex<impl Write>) {
    let mut table = calls.lock();
    loop {
        if table.forwarding_ended {
            return;
        }
        let now = Instant::now();
        let ahead: Vec<usize> = table.calls.iter().map(|call| table.jobs_ahead(call.ordinal)).collect();
        let mut next_due = now + PROGRESS_INTERVAL;
        for (call, ahead) in table.calls.iter_mut().zip(ahead) {
            if call.answered() {
                continue;
            }
            let Some(token) = call.progress_token.clone() else { continue };
            if now >= call.next_report {
                let seconds = call.received.elapsed().as_secs().max(call.reported_seconds + 1);
                call.reported_seconds = seconds;
                call.next_report = now + PROGRESS_INTERVAL;
                let message = match &call.state {
                    CallState::Queued => format!("{} job queued for {seconds} s: {ahead} earlier job(s) of this author call ahead (a session runs its jobs one at a time)", call.tool),
                    CallState::Waiting => format!("wait still waiting after {seconds} s"),
                    _ => format!("{} job still running after {seconds} s (this includes any wait for another session's timing lease)", call.tool),
                };
                // A failed write is not this thread's to report: the answer's write on the same output fails too.
                let _ = send(output, &json!({"jsonrpc":"2.0","method":"notifications/progress",
                    "params":{"progressToken":token,"progress":seconds,"message":message}}));
            }
            next_due = next_due.min(call.next_report);
        }
        table = calls.changed.wait_timeout(table, next_due.saturating_duration_since(Instant::now())).unwrap_or_else(PoisonError::into_inner).0;
    }
}

/// The server command's entry: `args` are the two trailing arguments the provider appends.
pub fn main(args: &[String]) -> Result<(), String> {
    let [context, evidence] = args else { return Err(USAGE.into()) };
    let stdin = std::io::stdin();
    serve(Path::new(context), Path::new(evidence), stdin.lock(), std::io::stdout())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::records::random_uuid;
    use crate::controller::session::LocalSessionEndpoint;
    use crate::tools::{AuthorRole, MAX_WAIT_SECONDS, ToolAction};
    use std::io::{BufReader, Cursor, Read};
    use std::os::unix::net::{UnixListener, UnixStream};
    use std::sync::Arc;

    /// A query author's tool context over a fixture role socket, in fresh scratch under `TMPDIR`: `(scratch root,
    /// context file, evidence directory, the role's listener, its socket directory)`.
    fn fixture_context() -> (PathBuf, PathBuf, PathBuf, UnixListener, PathBuf) {
        let tmp = PathBuf::from(std::env::var_os("TMPDIR").expect("TMPDIR must name a scratch directory"));
        let root = tmp.join(format!("r9-mcp-{}", random_uuid().unwrap()));
        let (author, evidence) = (root.join("author"), root.join("calls/0001/local-jobs"));
        std::fs::create_dir_all(&author).unwrap();
        // A Unix socket path must stay short: the `sockets` directory of TMPDIR.
        let sockets = tmp.join("sockets").join(random_uuid().unwrap());
        std::fs::create_dir_all(&sockets).unwrap();
        let socket = sockets.join("s");
        let listener = UnixListener::bind(&socket).unwrap();
        let endpoint = LocalSessionEndpoint { format_version: 1, socket: socket.clone(), token: "fixture-token".into(), query_root: root.clone(), service_record: root.join("service.json") };
        let context = LocalToolContext { format_version: CONTEXT_FORMAT, role: AuthorRole::Query, author_workspace: author.canonicalize().unwrap(), session_service: endpoint,
            worker_counts: vec![1, 32, 64], statements: vec![], author_contract: author.join("contract/verus/index.json"), fixed_flat: false, engine_bindings: vec![], workloads: vec![] };
        let context_path = author.join("local-tool.json");
        write_new_json(&context_path, &context).unwrap();
        (root, context_path, evidence, listener, sockets)
    }

    /// The thin client lists the tools (the job tools, then `wait`), forwards a typed call to the retained service over
    /// its socket, and refuses unknown arguments on the client with a durable record; it opens nothing else (the earlier
    /// version's `integrated_local_jobs.rs`, driven in-process instead of through the binary).
    #[test]
    fn mcp_client_lists_tools_forwards_typed_jobs_and_refuses_unknown_arguments() {
        let (root, context_path, evidence, listener, sockets) = fixture_context();
        let service = std::thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut bytes = vec![];
            stream.read_to_end(&mut bytes).unwrap();
            let request: Value = serde_json::from_slice(&bytes).unwrap();
            assert_eq!((request["token"].as_str(), request["action"].as_str()), (Some("fixture-token"), Some("trial")));
            assert_eq!(request["arguments"], json!({"candidate":"verus-query.json","job_name":"t1","workers":32}));
            assert!(request["evidence_root"].as_str().unwrap().ends_with("local-jobs"));
            serde_json::to_writer(&mut stream, &json!({"ok":{"format_version":1,"job_id":1,"action":"trial","status":"completed","result":{"status":"allowed","workers":32},
                "diagnostic_only":true,"official_measurement":false}})).unwrap();
        });
        let lines = [
            json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}),
            json!({"jsonrpc":"2.0","method":"notifications/initialized"}),
            json!({"jsonrpc":"2.0","id":2,"method":"tools/list","params":{}}),
            json!({"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"trial","arguments":{"candidate":"verus-query.json","job_name":"t1","workers":32}}}),
            json!({"jsonrpc":"2.0","id":4,"method":"tools/call","params":{"name":"profile","arguments":{"job_name":"bad","join_build_sides":[]}}}),
        ];
        let input: String = lines.iter().map(|l| format!("{l}\n")).collect();
        let mut output = vec![];
        serve(&context_path, &evidence, Cursor::new(input), &mut output).unwrap();
        service.join().unwrap();
        let answers: Vec<Value> = String::from_utf8(output).unwrap().lines().map(|l| serde_json::from_str(l).unwrap()).collect();
        assert_eq!(answers.len(), 4, "a notification has no answer");
        assert_eq!(answers[0]["result"]["serverInfo"]["name"], "gendb-local");
        let listed = answers[1]["result"]["tools"].as_array().unwrap();
        let names: Vec<&str> = listed.iter().map(|t| t["name"].as_str().unwrap()).collect();
        assert_eq!(names, ToolAction::ALL.map(ToolAction::name).into_iter().chain([WAIT_TOOL]).collect::<Vec<_>>());
        assert_eq!(listed[9]["inputSchema"]["properties"]["workers"]["enum"], json!([1, 32, 64]));
        assert!(listed[6]["inputSchema"]["properties"]["modules"].is_object() && listed[8]["inputSchema"]["properties"]["timeout_seconds"].is_object());
        assert_eq!(listed[8]["inputSchema"]["properties"]["verification"]["enum"], json!(["whole_crate", "not_run"]));
        assert!(listed[7]["inputSchema"]["properties"].get("verification").is_none(), "compile stays the verified run");
        assert!(listed[3]["inputSchema"]["required"].as_array().unwrap().contains(&json!("storage")));
        assert!(listed[8]["inputSchema"]["properties"].get("statement").is_none(), "a query author runs its one statement");
        assert_eq!(listed[11]["inputSchema"]["required"], json!(["job_name"]));
        assert_eq!(listed[11]["inputSchema"]["properties"]["wait_seconds"]["maximum"], json!(MAX_WAIT_SECONDS));
        let completed = &answers[2]["result"];
        assert_eq!((completed["isError"].as_bool(), completed["structuredContent"]["summary"]["workers"].as_u64()), (Some(false), Some(32)));
        let refused = &answers[3]["result"]["structuredContent"];
        assert_eq!((answers[3]["result"]["isError"].as_bool(), refused["failure_class"].as_str()), (Some(true), Some("missing_input")));
        assert!(refused["error"].as_str().unwrap().contains("join_build_sides"), "{refused}");
        assert!(PathBuf::from(refused["refusal_record"].as_str().unwrap()).is_file());
        let started: Value = read_json(&evidence.join("service.json")).unwrap();
        assert_eq!(started["prepared_owner_opens"], 0);
        let finished: Value = read_json(&evidence.join("service-finished.json")).unwrap();
        assert_eq!((finished["jobs"].as_u64(), finished["waits"].as_u64()), (Some(2), Some(0)));
        let protocol: Value = read_json(&evidence.join("mcp-protocol.json")).unwrap();
        assert_eq!(protocol["served_methods"]["initialize"]["count"], 1);
        std::fs::remove_dir_all(&root).unwrap();
        std::fs::remove_dir_all(&sockets).unwrap();
    }

    /// The server's output, read by the test while the server writes it.
    #[derive(Clone, Default)]
    struct SharedOutput(Arc<Mutex<Vec<u8>>>);

    impl Write for SharedOutput {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            self.0.lock().unwrap().extend_from_slice(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    impl SharedOutput {
        /// The result answering request `id`, once written within `patience`.
        fn answer(&self, id: u64, patience: Duration) -> Option<Value> {
            let started = Instant::now();
            loop {
                let text = String::from_utf8(self.0.lock().unwrap().clone()).unwrap();
                let found = text.lines().map(|l| serde_json::from_str::<Value>(l).unwrap()).find(|message| message["id"] == id);
                if found.is_some() || started.elapsed() >= patience {
                    return found.map(|message| message["result"].clone());
                }
                std::thread::sleep(Duration::from_millis(10));
            }
        }
    }

    /// `wait` is answered while this call's jobs run and queue (it waits behind no job, and the thin client
    /// takes no lock), returns a job's own answer as soon as the job ends, answers its status (running, or queued with
    /// the jobs ahead) when its bound passes first, reads the job records of a job an earlier server process received,
    /// and refuses a name found nowhere. The job calls are still forwarded one at a time, in the order received.
    #[test]
    fn wait_answers_while_jobs_run_and_returns_each_job_when_it_ends() {
        let (root, context_path, evidence, listener, sockets) = fixture_context();
        // Records of an earlier server process of the same call: one ended job, one still running.
        std::fs::create_dir_all(evidence.join("0009-earlier")).unwrap();
        write_new_json(&evidence.join("0009-earlier/result.json"), &json!({"format_version":1,"job_id":9,"action":"check","status":"completed","result":{"status":"frozen"},
            "error":null,"result_record":evidence.join("0009-earlier/result.json"),"diagnostic_only":true,"official_measurement":false})).unwrap();
        std::fs::create_dir_all(evidence.join("0010-started")).unwrap();
        write_new_json(&evidence.join("0010-started/request.json"), &json!({"job_id":10})).unwrap();
        // The role: each job is answered when the test releases it.
        let (accepted_send, accepted) = std::sync::mpsc::channel::<String>();
        let (release_send, release) = std::sync::mpsc::channel::<()>();
        let service = std::thread::spawn(move || {
            for job_id in [1, 2] {
                let (mut stream, _) = listener.accept().unwrap();
                let mut bytes = vec![];
                stream.read_to_end(&mut bytes).unwrap();
                let request: Value = serde_json::from_slice(&bytes).unwrap();
                accepted_send.send(request["arguments"]["job_name"].as_str().unwrap().to_string()).unwrap();
                release.recv().unwrap();
                serde_json::to_writer(&mut stream, &json!({"ok":{"format_version":1,"job_id":job_id,"action":"trial","status":"completed","result":{"status":"allowed","workers":32},
                    "diagnostic_only":true,"official_measurement":false}})).unwrap();
            }
        });
        let (mut client, server_end) = UnixStream::pair().unwrap();
        let output = SharedOutput::default();
        let server = {
            let (context_path, evidence, output) = (context_path.clone(), evidence.clone(), output.clone());
            std::thread::spawn(move || serve(&context_path, &evidence, BufReader::new(server_end), output))
        };
        let mut request = |id: u64, method: &str, params: Value| writeln!(client, "{}", json!({"jsonrpc":"2.0","id":id,"method":method,"params":params})).unwrap();
        let trial = |job_name: &str| json!({"name":"trial","arguments":{"candidate":"verus-query.json","job_name":job_name,"workers":32},"_meta":{"progressToken":job_name}});
        let wait = |job_name: &str, seconds: u64| json!({"name":WAIT_TOOL,"arguments":{"job_name":job_name,"wait_seconds":seconds}});
        let status = |result: &Value| (result["isError"].as_bool().unwrap(), result["structuredContent"]["status"].as_str().unwrap().to_string());
        let soon = Duration::from_secs(5);
        request(1, "initialize", json!({}));
        assert!(output.answer(1, soon).is_some());
        request(3, "tools/call", trial("t1"));
        assert_eq!(accepted.recv_timeout(soon).unwrap(), "t1", "the first job is forwarded at once");
        request(4, "tools/call", trial("t2"));
        // While t1 runs (its answer pending), waits are answered.
        request(5, "tools/call", wait("t1", 0));
        let running = output.answer(5, soon).expect("a wait is answered while the job runs");
        assert_eq!(status(&running), (false, "running".to_string()), "{running}");
        assert_eq!(running["structuredContent"]["job_name"], "t1");
        request(6, "tools/call", wait("t2", 0));
        let queued = output.answer(6, soon).unwrap();
        assert_eq!((status(&queued), queued["structuredContent"]["jobs_ahead"].as_u64()), ((false, "queued".to_string()), Some(1)), "{queued}");
        // The bound is respected: a 1 s wait answers the status after about 1 s.
        let started = Instant::now();
        request(7, "tools/call", wait("t2", 1));
        let bounded = output.answer(7, soon).unwrap();
        assert_eq!(status(&bounded), (false, "queued".to_string()));
        assert!(started.elapsed() >= Duration::from_secs(1) && started.elapsed() < Duration::from_secs(4), "{:?}", started.elapsed());
        // A name found nowhere is refused after one poll interval without its call, whatever else changes meanwhile.
        let asked = Instant::now();
        request(8, "tools/call", wait("never-started", 0));
        let unknown = output.answer(8, soon).unwrap();
        assert_eq!((status(&unknown), unknown["structuredContent"]["failure_class"].as_str()), ((true, "refused".to_string()), Some("missing_input")), "{unknown}");
        assert!(asked.elapsed() >= WAIT_POLL, "{:?}", asked.elapsed());
        request(10, "tools/call", wait("earlier", 0));
        let earlier = output.answer(10, soon).unwrap();
        assert_eq!((status(&earlier), earlier["structuredContent"]["job_id"].as_u64()), ((false, "completed".to_string()), Some(9)), "{earlier}");
        request(11, "tools/call", wait("started", 0));
        let started_elsewhere = output.answer(11, soon).unwrap();
        assert_eq!(status(&started_elsewhere), (false, "running".to_string()));
        assert!(started_elsewhere["structuredContent"]["job_directory"].as_str().unwrap().ends_with("0010-started"), "{started_elsewhere}");
        // A long wait returns the job's own answer as soon as the job ends.
        request(9, "tools/call", wait("t1", 60));
        assert!(output.answer(9, Duration::from_millis(300)).is_none(), "the wait waits while the job runs");
        assert!(output.answer(3, Duration::ZERO).is_none(), "t1 has not ended");
        let released = Instant::now();
        release_send.send(()).unwrap();
        let ended = output.answer(9, soon).expect("the wait ends with the job");
        assert!(released.elapsed() < Duration::from_secs(3), "{:?}", released.elapsed());
        assert_eq!(ended, output.answer(3, soon).unwrap(), "the job's own answer");
        assert_eq!(status(&ended), (false, "completed".to_string()));
        // The second job is forwarded only after the first ended.
        assert_eq!(accepted.recv_timeout(soon).unwrap(), "t2");
        release_send.send(()).unwrap();
        assert_eq!(output.answer(4, soon).unwrap()["structuredContent"]["job_id"], 2);
        drop(request);
        drop(client);
        server.join().unwrap().unwrap();
        service.join().unwrap();
        let finished: Value = read_json(&evidence.join("service-finished.json")).unwrap();
        assert_eq!((finished["jobs"].as_u64(), finished["waits"].as_u64()), (Some(2), Some(7)));
        std::fs::remove_dir_all(&root).unwrap();
        std::fs::remove_dir_all(&sockets).unwrap();
    }
}
