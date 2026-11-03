//! One retained role owner per author session. The role (with its prepared data, compiled builds and caches) lives on
//! one owner thread, which serves both the controller's stage calls and the author's local diagnostic jobs. The
//! author's tool process is only a thin client: it forwards typed job requests over a Unix socket.
//!
//! Protocol (`LocalJobRequest`, format 1): the client writes one JSON request and shuts down its write side; the
//! owner answers `{"ok": <job record>}` or `{"error": <message>}`. The token of this session and an evidence
//! directory under the session's `calls/` are required. A malformed or dead client is a per-job refusal (recorded as
//! `service-refused-NNNN.json` when the job was authorized), never a reason to drop the prepared role. The five-second
//! read deadline covers request framing only; an accepted job may run as long as it needs.
//!
//! The socket is a file under the configured scratch directory (`$TMPDIR/sockets/<uuid>/s`) at any depth: Linux limits
//! `sockaddr_un.sun_path` to 108 bytes, so both sides bind and connect through the short name
//! `/proc/self/fd/<fd of the socket's directory>/s` ([`short_socket_name`]), as other Linux services reach long socket
//! paths. The endpoint keeps the socket's real path.

use super::ControllerError;
use super::author::CandidateSubmission;
use super::ledger::Trial;
use super::records;
use super::role::{QualificationAttempt, SeededIncumbent, SynthesisRole};
use super::run::RunRequest;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::fs::File;
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::thread::{self, JoinHandle};
use std::time::Duration;

/// Wire format version of `LocalJobRequest` and `LocalSessionEndpoint`.
pub const LOCAL_SESSION_FORMAT: u32 = 1;
/// Bound of one framed job request (the request carries paths and arguments, never data).
const MAX_LOCAL_REQUEST_BYTES: u64 = 1024 * 1024;
const REQUEST_FRAMING_TIMEOUT: Duration = Duration::from_secs(5);
const RESPONSE_WRITE_TIMEOUT: Duration = Duration::from_secs(5);
/// Idle wait between polls of stage calls and socket connections on the owner thread.
const OWNER_POLL_INTERVAL: Duration = Duration::from_millis(2);

/// How the author's tool client reaches this session's retained role (written into the author tool context).
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct LocalSessionEndpoint {
    pub format_version: u32,
    pub socket: PathBuf,
    pub token: String,
    /// The author session's run directory.
    pub query_root: PathBuf,
    /// This owner's service record.
    pub service_record: PathBuf,
}

/// One author-local job request on the wire.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LocalJobRequest {
    pub format_version: u32,
    pub token: String,
    /// The tool client's evidence directory; must lie under the session's `calls/`.
    pub evidence_root: PathBuf,
    pub action: String,
    /// Role-defined job arguments, validated by the role.
    pub arguments: Value,
}

/// A role that also answers the author's local diagnostic jobs (check, verify, compile, trial, profile, …). Local
/// jobs are diagnostics only: never submissions, never official measurements.
#[allow(async_fn_in_trait)]
pub trait LocalJobs {
    /// Called once before the owner thread starts; the role passes the endpoint to its author tool context.
    fn attach_local_session(&mut self, endpoint: &LocalSessionEndpoint);

    /// Run one authorized job; `evidence_root` is canonical and under the session's `calls/`, `job_id` counts this
    /// owner's authorized jobs from 1. `Ok` is the job record returned to the client.
    async fn run_local_job(&mut self, evidence_root: &Path, action: &str, arguments: Value, job_id: u64) -> Result<Value, String>;
}

type OwnerTask<R> = Box<dyn FnOnce(&mut R, &tokio::runtime::Runtime) + Send>;

/// A `SynthesisRole` whose stages run on the retained owner thread of the role it wraps.
pub struct RetainedRole<R: SynthesisRole> {
    tasks: Option<mpsc::Sender<OwnerTask<R>>>,
    owner: Option<JoinHandle<()>>,
    policy: R::Policy,
    /// This owner's fresh socket directory, removed when the owner stops.
    socket_root: PathBuf,
}

/// Each owner process writes a new service record; a restarted controller keeps earlier records immutable.
fn service_record_path(service_root: &Path) -> PathBuf {
    let first = service_root.join("service.json");
    if first.exists() {
        service_root.join(format!("service-restart-{}-{}.json", records::now_unix_ms(), std::process::id()))
    } else {
        first
    }
}

impl<R: SynthesisRole + LocalJobs + Send + 'static> RetainedRole<R> {
    /// Start the owner thread of `role` for the session in `session_root`. The socket lives in a fresh directory
    /// under `socket_dir` (configured scratch, never the system `/tmp`; any depth, see the module documentation).
    pub fn start(mut role: R, session_root: &Path, socket_dir: &Path) -> Result<Self, ControllerError> {
        let service_root = session_root.join("local-session");
        records::create_dir(&service_root)?;
        let socket_root = socket_dir.join(records::random_uuid()?);
        records::create_dir(&socket_root)?;
        let socket = socket_root.join("s");
        let endpoint = LocalSessionEndpoint {
            format_version: LOCAL_SESSION_FORMAT,
            socket,
            token: records::random_uuid()?,
            query_root: session_root.to_path_buf(),
            service_record: service_record_path(&service_root),
        };
        role.attach_local_session(&endpoint);
        let policy = role.policy();
        let (tasks, task_queue) = mpsc::channel::<OwnerTask<R>>();
        let (ready_send, ready) = mpsc::sync_channel::<Result<(), String>>(1);
        let owner = thread::spawn(move || {
            if let Err(error) = serve(&mut role, &endpoint, &service_root, &task_queue, &ready_send) {
                let _ = ready_send.try_send(Err(error.clone()));
                let path = records::next_free_record(&service_root, "service-error.json", "service-error");
                let _ = records::write_new_json(&path, &json!({"status":"failed","error":error}));
            }
        });
        ready
            .recv()
            .map_err(|_| ControllerError::Session("owner thread ended before it was ready".into()))?
            .map_err(ControllerError::Session)?;
        Ok(Self { tasks: Some(tasks), owner: Some(owner), policy, socket_root })
    }

    /// Run `task` on the owner thread and wait for its result.
    fn on_owner<T: Send + 'static>(
        &self,
        task: impl FnOnce(&mut R, &tokio::runtime::Runtime) -> T + Send + 'static,
    ) -> Result<T, String> {
        let (answer, result) = mpsc::channel();
        let task: OwnerTask<R> = Box::new(move |role, runtime| {
            let _ = answer.send(task(role, runtime));
        });
        let tasks = self.tasks.as_ref().ok_or("retained role service stopped")?;
        tasks.send(task).map_err(|_| "retained role service unavailable".to_string())?;
        result.recv().map_err(|_| "retained role response unavailable".to_string())
    }
}

impl<R: SynthesisRole> Drop for RetainedRole<R> {
    fn drop(&mut self) {
        // Disconnecting the task channel stops the owner loop.
        drop(self.tasks.take());
        if let Some(owner) = self.owner.take() {
            let _ = owner.join();
        }
        // The socket and its fresh directory belong to this owner only (records stay in the session directory).
        let _ = std::fs::remove_file(self.socket_root.join("s"));
        let _ = std::fs::remove_dir(&self.socket_root);
    }
}

impl<R: SynthesisRole + LocalJobs + Send + 'static> SynthesisRole for RetainedRole<R> {
    type Policy = R::Policy;

    fn policy(&self) -> R::Policy {
        self.policy.clone()
    }

    async fn prepare(&mut self, request: &RunRequest, workspace: &Path) -> Result<Value, String> {
        let (request, workspace) = (request.clone(), workspace.to_path_buf());
        self.on_owner(move |role, runtime| runtime.block_on(role.prepare(&request, &workspace)))?
    }

    async fn freeze(&mut self, workspace: &Path, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<Value, String> {
        let (workspace, frozen_dir, submission) = (workspace.to_path_buf(), frozen_dir.to_path_buf(), submission.clone());
        self.on_owner(move |role, runtime| runtime.block_on(role.freeze(&workspace, &frozen_dir, &submission)))?
    }

    async fn evaluate(&mut self, frozen_dir: &Path, candidate: &Value) -> Result<Value, String> {
        let (frozen_dir, candidate) = (frozen_dir.to_path_buf(), candidate.clone());
        self.on_owner(move |role, runtime| runtime.block_on(role.evaluate(&frozen_dir, &candidate)))?
    }

    async fn qualify(&mut self, frozen_dir: &Path, evaluation: &Value) -> Result<Value, String> {
        let (frozen_dir, evaluation) = (frozen_dir.to_path_buf(), evaluation.clone());
        self.on_owner(move |role, runtime| runtime.block_on(role.qualify(&frozen_dir, &evaluation)))?
    }

    async fn refresh_shared_facts(&mut self) -> Result<Value, String> {
        self.on_owner(move |role, runtime| runtime.block_on(role.refresh_shared_facts()))?
    }

    async fn close(&mut self, trials: &[Trial], qualification: &[QualificationAttempt]) -> Result<Value, String> {
        let (trials, qualification) = (trials.to_vec(), qualification.to_vec());
        self.on_owner(move |role, runtime| runtime.block_on(role.close(&trials, &qualification)))?
    }

    async fn policy_exclusion(&mut self, evaluation: &Value) -> Result<Option<String>, String> {
        let evaluation = evaluation.clone();
        self.on_owner(move |role, runtime| runtime.block_on(role.policy_exclusion(&evaluation)))?
    }

    async fn import_frozen(&mut self, source: &Path, frozen_dir: &Path) -> Result<Value, String> {
        let (source, frozen_dir) = (source.to_path_buf(), frozen_dir.to_path_buf());
        self.on_owner(move |role, runtime| runtime.block_on(role.import_frozen(&source, &frozen_dir)))?
    }

    async fn seed_incumbent(&mut self, source: &Path, workspace: &Path) -> Result<SeededIncumbent, String> {
        let (source, workspace) = (source.to_path_buf(), workspace.to_path_buf());
        self.on_owner(move |role, runtime| runtime.block_on(role.seed_incumbent(&source, &workspace)))?
    }
}

/// The owner loop: stage calls from the controller and job connections from the author's tool client, until the
/// controller drops its `RetainedRole`.
fn serve<R: LocalJobs>(
    role: &mut R,
    endpoint: &LocalSessionEndpoint,
    service_root: &Path,
    task_queue: &mpsc::Receiver<OwnerTask<R>>,
    ready: &mpsc::SyncSender<Result<(), String>>,
) -> Result<(), String> {
    let listener = short_socket_name(&endpoint.socket)
        .and_then(|(_directory, name)| UnixListener::bind(name))
        .map_err(|e| format!("{}: {e}", endpoint.socket.display()))?;
    listener.set_nonblocking(true).map_err(|e| e.to_string())?;
    records::write_new_json(&endpoint.service_record, &json!({"format_version":LOCAL_SESSION_FORMAT,"status":"ready",
        "socket":endpoint.socket,"pid":std::process::id(),
        "owner":"one retained role for local jobs, submissions, qualification and final measurement",
        "prepared_owner_instances":1,"query_root":endpoint.query_root}))
    .map_err(|e| e.to_string())?;
    ready.send(Ok(())).map_err(|e| e.to_string())?;
    // Stage futures and compiled artifacts stay on this thread; they need not be Send.
    let runtime = tokio::runtime::Builder::new_current_thread().enable_all().build().map_err(|e| e.to_string())?;
    let mut authorized_jobs = 0u64;
    loop {
        match task_queue.try_recv() {
            Ok(task) => task(role, &runtime),
            Err(mpsc::TryRecvError::Disconnected) => break,
            Err(mpsc::TryRecvError::Empty) => {}
        }
        match listener.accept() {
            Ok((mut stream, _)) => {
                let answer = answer_local_job(&mut stream, role, &runtime, endpoint, &mut authorized_jobs);
                let response = match answer {
                    Ok(record) => json!({"ok":record}),
                    Err(error) => json!({"error":error}),
                };
                // The provider may have killed its tool client after the job completed: the durable job record stays
                // and the service continues even when this response has no reader.
                let _ = stream.set_write_timeout(Some(RESPONSE_WRITE_TIMEOUT));
                if serde_json::to_writer(&mut stream, &response).is_ok() {
                    let _ = stream.flush();
                }
            }
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {}
            Err(error) => return Err(error.to_string()),
        }
        thread::sleep(OWNER_POLL_INTERVAL);
    }
    let finished = records::next_free_record(service_root, "service-finished.json", "service-finished");
    records::write_new_json(&finished, &json!({"format_version":LOCAL_SESSION_FORMAT,"status":"stopped",
        "local_jobs":authorized_jobs,"prepared_owner_instances":1}))
    .map_err(|e| e.to_string())
}

/// Read, authorize and run one job request.
fn answer_local_job<R: LocalJobs>(
    stream: &mut UnixStream,
    role: &mut R,
    runtime: &tokio::runtime::Runtime,
    endpoint: &LocalSessionEndpoint,
    authorized_jobs: &mut u64,
) -> Result<Value, String> {
    stream.set_read_timeout(Some(REQUEST_FRAMING_TIMEOUT)).map_err(|e| e.to_string())?;
    let mut bytes = vec![];
    stream.take(MAX_LOCAL_REQUEST_BYTES + 1).read_to_end(&mut bytes).map_err(|e| e.to_string())?;
    if bytes.len() as u64 > MAX_LOCAL_REQUEST_BYTES {
        return Err("local-session request exceeds limit".into());
    }
    let request: LocalJobRequest = serde_json::from_slice(&bytes).map_err(|e| format!("local-session request: {e}"))?;
    if request.format_version != LOCAL_SESSION_FORMAT || request.token != endpoint.token {
        return Err("local-session authorization refused".into());
    }
    let evidence = request.evidence_root.canonicalize().map_err(|e| e.to_string())?;
    let calls = endpoint.query_root.join("calls").canonicalize().map_err(|e| e.to_string())?;
    if !evidence.starts_with(&calls) {
        return Err("local-job evidence must remain under this query's calls".into());
    }
    *authorized_jobs += 1;
    let job_id = *authorized_jobs;
    let result = runtime.block_on(role.run_local_job(&evidence, &request.action, request.arguments, job_id));
    if let Err(error) = &result {
        let _ = records::write_new_json(
            &evidence.join(format!("service-refused-{job_id:04}.json")),
            &json!({"format_version":LOCAL_SESSION_FORMAT,"job_id":job_id,"action":request.action,"status":"refused",
                "stage":"service","error":error,"diagnostic_only":true,"official_measurement":false}),
        );
    }
    result
}

/// A name for the Unix socket at `socket` that fits `sun_path` whatever the length of its directory's path:
/// `/proc/self/fd/<fd>/<file name>`, through the returned open handle of the socket's directory (Linux). Bind or connect
/// while the handle is alive; the socket itself is the file at `socket`.
fn short_socket_name(socket: &Path) -> std::io::Result<(File, PathBuf)> {
    let unnamed = || std::io::Error::new(std::io::ErrorKind::InvalidInput, format!("{}: a socket path needs a directory and a file name", socket.display()));
    let (directory, name) = (socket.parent().ok_or_else(unnamed)?, socket.file_name().ok_or_else(unnamed)?);
    let handle = File::open(directory)?;
    let short = PathBuf::from(format!("/proc/self/fd/{}", handle.as_raw_fd())).join(name);
    Ok((handle, short))
}

/// Client side: forward one job to the retained owner and wait for its answer.
pub fn forward_job(endpoint: &LocalSessionEndpoint, evidence_root: &Path, action: &str, arguments: Value) -> Result<Value, String> {
    let request = LocalJobRequest {
        format_version: LOCAL_SESSION_FORMAT,
        token: endpoint.token.clone(),
        evidence_root: evidence_root.to_path_buf(),
        action: action.into(),
        arguments,
    };
    let mut stream = short_socket_name(&endpoint.socket)
        .and_then(|(_directory, name)| UnixStream::connect(name))
        .map_err(|e| format!("retained local-session unavailable: {e}"))?;
    serde_json::to_writer(&mut stream, &request).map_err(|e| e.to_string())?;
    stream.shutdown(std::net::Shutdown::Write).map_err(|e| e.to_string())?;
    let mut bytes = vec![];
    stream.read_to_end(&mut bytes).map_err(|e| e.to_string())?;
    let response: Value = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    response
        .get("ok")
        .cloned()
        .ok_or_else(|| response["error"].as_str().unwrap_or("local-session response invalid").to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::test_support::{FixturePolicy, scratch_root};

    /// A role whose local jobs echo their arguments and refuse the action "refuse".
    struct EchoRole {
        endpoint: Option<LocalSessionEndpoint>,
        prepared: u32,
    }

    impl SynthesisRole for EchoRole {
        type Policy = FixturePolicy;
        fn policy(&self) -> FixturePolicy {
            FixturePolicy::default()
        }
        async fn prepare(&mut self, _: &RunRequest, _: &Path) -> Result<Value, String> {
            self.prepared += 1;
            Ok(json!({"prepared":self.prepared,"endpoint":self.endpoint}))
        }
        async fn freeze(&mut self, _: &Path, _: &Path, _: &CandidateSubmission) -> Result<Value, String> {
            Err("not used".into())
        }
        async fn evaluate(&mut self, _: &Path, _: &Value) -> Result<Value, String> {
            Err("not used".into())
        }
        async fn qualify(&mut self, _: &Path, _: &Value) -> Result<Value, String> {
            Err("not used".into())
        }
        async fn close(&mut self, trials: &[Trial], _: &[QualificationAttempt]) -> Result<Value, String> {
            Ok(json!({"trials":trials.len()}))
        }
    }

    impl LocalJobs for EchoRole {
        fn attach_local_session(&mut self, endpoint: &LocalSessionEndpoint) {
            self.endpoint = Some(endpoint.clone());
        }
        async fn run_local_job(&mut self, evidence: &Path, action: &str, arguments: Value, job_id: u64) -> Result<Value, String> {
            if action == "refuse" {
                return Err("missing_input: fixture refusal".into());
            }
            Ok(json!({"status":"completed","job_id":job_id,"action":action,"arguments":arguments,"evidence":evidence}))
        }
    }

    #[test]
    fn restarted_controller_keeps_the_earlier_service_record() {
        let root = scratch_root("session-restart");
        records::create_dir(&root).unwrap();
        let first = service_record_path(&root);
        assert_eq!(first, root.join("service.json"));
        records::write_new_json(&first, &json!({"pid":1})).unwrap();
        let bytes = std::fs::read(&first).unwrap();
        let second = service_record_path(&root);
        assert_ne!(second, first);
        assert!(second.file_name().unwrap().to_str().unwrap().starts_with("service-restart-"));
        records::write_new_json(&second, &json!({"pid":2})).unwrap();
        assert_eq!(std::fs::read(&first).unwrap(), bytes);
    }

    /// Stage calls and author jobs reach the same retained role; refused and unauthorized jobs keep the owner alive.
    #[tokio::test]
    async fn one_owner_serves_stages_and_local_jobs() {
        let root = scratch_root("retained-role");
        let evidence = root.join("calls/0001/local-jobs");
        records::create_dir(&evidence).unwrap();
        // A socket directory deeper than `sun_path` holds (108 bytes) serves: bind and connect go through
        // `/proc/self/fd/<fd>/s` while the socket file stays at its real path.
        let sockets = scratch_root("sockets-deeper-than-a-unix-socket-path-may-be-because-sun-path-holds-only-108-bytes").join("sockets");
        assert!(sockets.join("00000000-0000-0000-0000-000000000000/s").as_os_str().len() > 108, "{}", sockets.display());
        let mut retained = RetainedRole::start(EchoRole { endpoint: None, prepared: 0 }, &root, &sockets).unwrap();
        let request = RunRequest { format_version: 1, task: json!({}), limits: crate::controller::limits::tests::limits(), continue_from: None };
        let context = retained.prepare(&request, &root).await.unwrap();
        assert_eq!(context["prepared"], 1);
        let endpoint: LocalSessionEndpoint = serde_json::from_value(context["endpoint"].clone()).unwrap();
        use std::os::unix::fs::FileTypeExt;
        assert!(std::fs::metadata(&endpoint.socket).unwrap().file_type().is_socket(), "the socket is the file at the endpoint's real path");
        let echoed = forward_job(&endpoint, &evidence, "trial", json!({"workers":1})).unwrap();
        assert_eq!((echoed["job_id"].as_u64(), echoed["arguments"]["workers"].as_u64()), (Some(1), Some(1)));
        let refused = forward_job(&endpoint, &evidence, "refuse", json!({})).unwrap_err();
        assert!(refused.contains("fixture refusal"), "{refused}");
        assert!(evidence.canonicalize().unwrap().join("service-refused-0002.json").is_file());
        let mut wrong_token = endpoint.clone();
        wrong_token.token = "other".into();
        assert!(forward_job(&wrong_token, &evidence, "trial", json!({})).unwrap_err().contains("authorization refused"));
        assert!(forward_job(&endpoint, &root, "trial", json!({})).unwrap_err().contains("under this query's calls"));
        assert_eq!(retained.prepare(&request, &root).await.unwrap()["prepared"], 2, "the same role instance answers");
        drop(retained);
        let finished: Value = records::read_json(&root.join("local-session/service-finished.json")).unwrap();
        assert_eq!(finished["local_jobs"], 2, "only authorized jobs are counted");
        assert!(root.join("local-session/service.json").is_file());
    }
}
