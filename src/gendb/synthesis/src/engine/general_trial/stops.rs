//! Stops of the general line's controller on the trial fixture (FRAMEWORK TESTS ONLY). Same
//! environment as the other trial tests (`TMPDIR`, `GENDB_WORKER`, `GENDB_BUILD_LOCK`, `GENDB_TRIAL_DIR`; run with
//! `-- --ignored`); no provider and no paid call.
//!
//! - [`storage_registration_resumes_once`] (run S): one branch over the slowed root; b1's first submission reads the
//!   storage `marked` (built from the flat storage of region with an empty added part: a storage change at the plain
//!   storage's size, within the original data size) with version 0
//!   materializing twice. Launch 1 is
//!   killed by SIGKILL just after the storage's registration, before the engine's admission. Launch 2 admits the engine
//!   once from its intent, reusing that registration: one engine version over the root, one registered version of
//!   `marked`, which the engine version reads; the tree has no gap and the finding states its effect.
//! - [`owner_stop_leaves_no_child_and_the_relaunch_resumes`] (run T): the user's stop (`gendb_runtime::process_stop`)
//!   through the real `gendb` executable. `gendb engine prepare` is stopped by SIGTERM while `rust_verify` checks
//!   version 0, then relaunched: version 0 is admitted once (evaluated again in a fresh directory). `gendb engine
//!   synthesize`, whose author is a stand-in for the Claude Code CLI ([`write_fake_author`]: the real transport, Bash
//!   guardian and recovery; no provider), is stopped by SIGTERM during b1's first call while the stand-in's tool
//!   processes run (a Bash call in a session of its own with a background job and a `setsid` job, and a helper in the
//!   provider's group), then relaunched: the stopped call is recovered from its terminal result, the next call continues
//!   the provider session, and the budget stops the run. After each stop: the controller ended by SIGTERM, every process
//!   seen just before the stop (descendants and tagged processes, by pid and start) has ended, every process group they
//!   were in is empty, the stop record lists no survivor, and `leftovers` lists nothing.

use super::*;
use crate::controller::layout::RunLayout;
use gendb_artifacts::verus::storage_versions;
use gendb_runtime::process_stop::{self, Launch, ProcessStat, ProcessTable, RECORD_DIRECTORY, leftovers};
use std::ffi::OsStr;
use std::os::unix::process::ExitStatusExt;
use std::time::{Duration, Instant};

/// The one scale of runs S and T: `s1`, its original data size (the budget for changed storage)
/// ten times the plain storage's, so the storage `marked` is within it.
fn single_scale(fixture: &TrialFixture) -> [TrialScale<'_>; 1] {
    [TrialScale { name: "s1", data: 0, capture: &fixture.s1_capture, original_data_bytes: fixture.s1_flat_bytes * 10 }]
}

// ------------------------------------------------------------------------------------------------ run S

#[test]
#[ignore = "runs the pinned frontend, Verus and the gendb worker on tiny data; TMPDIR, GENDB_WORKER, GENDB_BUILD_LOCK, GENDB_TRIAL_DIR; -- --ignored"]
fn storage_registration_resumes_once() {
    let fixture = TrialFixture::prepare();
    let dir = run_folder("S");
    let library = dir.join("library");
    fixture.seed_library(&library);
    let shape = RunShape { branches: 1, budget: "2", cadence: "never", author_executable: Path::new("fixture") };
    let request_path = fixture.request_with(&dir.join("request.json"), &library, &dir.join("home"), &single_scale(&fixture), &shape);
    let request = WorkloadRequest::read(&request_path).unwrap();
    let run = dir.join("run");
    seed_slowed_root(&request, &run, &dir);
    let engine_dir = engine_directory(&run.canonicalize().unwrap());
    let store = ObjectStore::open_existing(&library).unwrap();
    let order = json!({"mode":"synthesize","request":request_path,"run":run,"script":"S"});
    // 1. Killed just after the storage's registration, before the engine's admission.
    let first = launch_child("1-killed-after-storage-registration", &dir, &order, Some(super::super::acceptance::CRASH_AFTER_STORAGE_REGISTRATION));
    assert_eq!(first.signal, Some(libc::SIGKILL), "{first:?}");
    assert_eq!(engine_versions(&store).unwrap().len(), 1, "only the root: killed before the engine's admission");
    let registered = storage_versions(&store, "marked").unwrap();
    assert_eq!(registered.len(), 1, "the storage was registered before the kill");
    let package = registered[0].1.package;
    let frozen = RunLayout::new(&super::super::sessions::session_directory(&engine_dir, "b1", 1)).iteration(1).join("frozen");
    assert!(frozen.join(super::super::acceptance::ADMITTING_FILE).is_file() && !frozen.join("admitted.json").is_file(), "the intent is written, the admission not");
    // 2. Relaunch: admitted once from the intent, the registration reused; the budget stops the run.
    let second = launch_child("2-admitted-once", &dir, &order, None);
    assert_eq!(second.code, Some(0), "{second:?}");
    let summary = latest_summary(&run);
    assert_eq!((summary["status"].as_str(), summary["reason"].as_str()), (Some("stopped"), Some("budget_limit")), "{summary}");
    let versions = engine_versions(&store).unwrap();
    assert_eq!(versions.len(), 2, "the root and b1's submission, admitted once");
    let registered = storage_versions(&store, "marked").unwrap();
    assert_eq!(registered.len(), 1, "no second registration of the storage");
    let read = versions[1].package.storage_uses.iter().find(|u| u.name == "marked").map(|u| u.package);
    assert_eq!(read, Some(package), "the version reads the storage registered before the kill");
    let tree = VersionTree::read(&engine_dir).unwrap();
    let ids: Vec<&str> = tree.versions().map(|n| n.id.as_str()).collect();
    assert_eq!(ids, ["v000", "v001"], "one tree version per library version, no gap");
    assert_eq!(tree.attempts().count(), 0, "{:?}", tree.attempts().map(|n| (&n.id, &n.reason)).collect::<Vec<_>>());
    let admitted: Value = read_json(&frozen.join("admitted.json")).unwrap();
    let admission = &admitted["record"]["admission"];
    assert_eq!(admission["registrations_reused"]["storages"][0]["name"], "marked", "{admission}");
    assert_eq!(admission["registrations_reused"]["storages"][0]["package"], json!(package));
    assert_eq!(admission["registrations"], json!([]), "nothing registered again");
    assert!(admission["recovered"].is_null(), "admitted from the intent, not adopted");
    let intent: Value = read_json(&frozen.join(super::super::acceptance::ADMITTING_FILE)).unwrap();
    let evaluation = PathBuf::from(intent["evaluation"].as_str().unwrap());
    assert!(evaluation.join("admission").is_dir() && evaluation.join("admission-1").is_dir(), "each attempt of the admission has its own directory under {}", evaluation.display());
    let version: Value = read_json(&engine_dir.join("versions/v001/version.json")).unwrap();
    let uses: Vec<&str> = version["storage"]["uses"].as_array().unwrap().iter().filter_map(|u| u["name"].as_str()).collect();
    assert!(uses.contains(&"marked"), "{uses:?}");
    let findings = tree::read_lines(&engine_dir.join(tree::FINDINGS_FILE)).unwrap();
    let finding = findings.iter().find(|f| f["node"] == "v001").expect("v001's finding");
    assert!(!finding["effect"].is_null(), "the resumed admission's finding states its effect: {finding}");
    let evidence = json!({"fixture":fixture.dir,"run":run,"library":library,"request":request_path,
        "launches":[format!("{first:?}"),format!("{second:?}")],"summary":summary,"storage":{"name":"marked","package":package,"registered_versions":registered.len()},
        "engine_versions":versions.iter().map(|v| json!({"version":v.version,"package":v.package_id,"uses":v.package.storage_uses})).collect::<Vec<_>>(),
        "admission":admission,"finding":finding});
    write_json_atomic(&dir.join("evidence.json"), &evidence).unwrap();
    eprintln!("run S: {}", dir.display());
}

// ------------------------------------------------------------------------------------------------ run T

/// The stand-in author's call records: `fake-ready.json` (its pids) in the call directory.
const FAKE_READY: &str = "fake-ready.json";

#[test]
#[ignore = "runs the gendb executable (frontend, Verus, worker) and a stand-in author CLI on tiny data; TMPDIR, GENDB_WORKER, GENDB_BUILD_LOCK, GENDB_TRIAL_DIR; -- --ignored"]
fn owner_stop_leaves_no_child_and_the_relaunch_resumes() {
    let fixture = TrialFixture::prepare();
    let dir = run_folder("T");
    let library = dir.join("library");
    fixture.seed_library(&library);
    let author = write_fake_author(&dir);
    let shape = RunShape { branches: 1, budget: "2", cadence: "never", author_executable: &author };
    let request = fixture.request_with(&dir.join("request.json"), &library, &dir.join("home"), &single_scale(&fixture), &shape);
    let run = dir.join("run");
    let store = ObjectStore::open_existing(&library).unwrap();
    let prepare: [&OsStr; 4] = ["engine".as_ref(), "prepare".as_ref(), request.as_os_str(), run.as_os_str()];
    let synthesize: [&OsStr; 4] = ["engine".as_ref(), "synthesize".as_ref(), request.as_os_str(), run.as_os_str()];

    // 1. `gendb engine prepare`, stopped by SIGTERM while rust_verify checks version 0 (its whole-crate build directory
    //    exists; the preparation's statement checks run rust_verify earlier).
    let v0_build = |run: &Path| run.join("engine/seed-v0/evaluation/verus-build").is_dir();
    let verus = stop_by_term("1-prepare-stopped-during-verus", &dir, cli(&prepare), &run, &|seen: &[Seen], run: &Path| v0_build(run) && seen.iter().any(|p| p.name == "rust_verify"));
    assert!(verus.stopped_names.contains("rust_verify"), "{:?}", verus.stopped_names);
    assert_eq!(engine_versions(&store).unwrap().len(), 0, "nothing admitted before the stop");
    // 2. Relaunch: version 0 is evaluated again in a fresh directory and admitted once.
    let second = launch_cli("2-prepare-relaunch", &dir, &prepare);
    assert_eq!(second.code, Some(0), "{second:?}");
    assert_eq!(engine_versions(&store).unwrap().len(), 1, "version 0 admitted once");
    let engine_dir = engine_directory(&run.canonicalize().unwrap());
    let seed = engine_dir.join("seed-v0");
    assert!(seed.join("evaluation").is_dir() && seed.join("evaluation-1").is_dir(), "the stopped evaluation and the relaunch's");
    let admitted: Value = read_json(&seed.join("admitted.json")).unwrap();
    assert_eq!(admitted["admission"]["evaluation"], json!(seed.join("evaluation-1")));

    // 3. `gendb engine synthesize`, stopped by SIGTERM during b1's first call while the author's tool processes run.
    let call_dir = RunLayout::new(&super::super::sessions::session_directory(&engine_dir, "b1", 1)).call(1);
    let author_call = stop_by_term("3-synthesize-stopped-during-the-author-call", &dir, cli(&synthesize), &run, &|_: &[Seen], _: &Path| call_dir.join(FAKE_READY).is_file());
    let fake: Value = read_json(&call_dir.join(FAKE_READY)).unwrap();
    for (name, pid) in fake.as_object().unwrap() {
        let pid = pid.as_i64().unwrap() as i32;
        assert!(author_call.seen.iter().any(|p| p.pid == pid), "{name} ({pid}) was not among the controller's processes before the stop");
    }
    let groups = &author_call.stop["owned_groups"];
    assert!(groups.as_array().unwrap().iter().any(|g| g["what"].as_str().unwrap().starts_with("author provider") && g["signal"] == "SIGINT"), "{groups}");
    let transcript = fs::read_to_string(call_dir.join("stdout.jsonl")).unwrap();
    let last: Value = serde_json::from_str(transcript.lines().last().unwrap()).unwrap();
    assert_eq!(last["type"], "result", "the provider wrote its terminal result on SIGINT");
    assert!(!call_dir.join("process-exit.json").exists(), "the supervising thread parked: the stopped call is not settled");
    // 4. Relaunch: the stopped call is recovered from its transcript, the next call continues the provider session,
    //    and the budget stops the run.
    let fourth = launch_cli("4-synthesize-relaunch", &dir, &synthesize);
    assert_eq!(fourth.code, Some(0), "{fourth:?}");
    let summary = latest_summary(&run);
    assert_eq!((summary["status"].as_str(), summary["reason"].as_str()), (Some("stopped"), Some("budget_limit")), "{summary}");
    let recovery: Value = read_json(&call_dir.join("controller-loss-recovery.json")).unwrap();
    assert_eq!(recovery["kind"], "controller_loss_receipt_recovery", "{recovery}");
    let second_call = RunLayout::new(&super::super::sessions::session_directory(&engine_dir, "b1", 1)).call(2);
    let invocation: Value = read_json(&second_call.join("invocation.json")).unwrap();
    assert!(invocation["argv"].as_array().unwrap().iter().any(|a| a == "--resume"), "the next call continues the provider session: {}", invocation["argv"]);
    let left = leftovers(&run).unwrap();
    assert_eq!(left.processes, Vec::<Value>::new(), "{left:?}");
    let evidence = json!({"fixture":fixture.dir,"run":run,"library":library,"request":request,"author":author,
        "stops":[verus.evidence(),author_call.evidence()],"relaunches":[format!("{second:?}"),format!("{fourth:?}")],
        "summary":summary,"recovery":recovery,"fake_author_pids":fake,"leftovers":left.processes});
    write_json_atomic(&dir.join("evidence.json"), &evidence).unwrap();
    eprintln!("run T: {}", dir.display());
}

/// A process of a controller seen just before its stop: pid, start, process group and command name.
#[derive(Clone, Debug)]
pub(super) struct Seen {
    pub pid: i32,
    pub start_ticks: u64,
    pub process_group: i32,
    pub name: String,
}

/// One stop by SIGTERM ([`stop_by_term`]): the launch, what was seen just before, the stop record and the names of
/// what it stopped.
pub(super) struct TermStop {
    pub name: String,
    pub launch: Launch,
    pub seen: Vec<Seen>,
    pub stop: Value,
    pub stopped_names: BTreeSet<String>,
    pub elapsed_ms: u64,
}

impl TermStop {
    pub(super) fn evidence(&self) -> Value {
        json!({"launch":self.name,"controller":self.launch.id,"elapsed_ms":self.elapsed_ms,"stopped_names":self.stopped_names,
            "seen":self.seen.iter().map(|p| json!({"pid":p.pid,"process_group":p.process_group,"name":p.name})).collect::<Vec<_>>(),"stop":self.stop})
    }
}

/// The live processes of `launch` now (`ProcessTable::of_launch`: descendants and processes carrying its tag).
fn seen_now(launch: &Launch) -> Vec<Seen> {
    let table = ProcessTable::read().unwrap();
    table
        .of_launch(launch, &BTreeSet::new())
        .into_iter()
        .map(|p| Seen {
            pid: p.stat.pid,
            start_ticks: p.stat.start_ticks,
            process_group: p.stat.process_group,
            name: fs::read_to_string(format!("/proc/{}/comm", p.stat.pid)).unwrap_or_default().trim().to_string(),
        })
        .collect()
}

/// The `gendb` executable with `arguments`.
fn cli(arguments: &[&OsStr]) -> Command {
    let mut command = Command::new(worker());
    command.args(arguments);
    command
}

/// Start `command` (a controller of `run`: `gendb engine ...`, or a trial child), wait until `ready(seen, run)` holds
/// for its processes, stop it with SIGTERM, and check the stop (module documentation).
pub(super) fn stop_by_term(name: &str, dir: &Path, mut command: Command, run: &Path, ready: &dyn Fn(&[Seen], &Path) -> bool) -> TermStop {
    let log = dir.join(format!("launch-{name}.log"));
    let out = fs::File::create(&log).unwrap();
    let mut child = command.env_remove("GENDB_TEST_CRASH_AT").stdin(std::process::Stdio::null()).stdout(out.try_clone().unwrap()).stderr(out).spawn().unwrap();
    let pid = child.id() as i32;
    let waited = Instant::now();
    let launch = loop {
        let records = run.join(RECORD_DIRECTORY);
        let found = fs::read_dir(&records).into_iter().flatten().flatten().filter_map(|e| {
            let name = e.file_name().to_string_lossy().into_owned();
            (name.starts_with("launch-") && name.ends_with(".json")).then(|| read_json::<Value>(&e.path()).ok()).flatten()
        });
        if let Some(launch) = found.filter_map(|r| serde_json::from_value::<Launch>(r["launch"].clone()).ok()).find(|l| l.pid == pid) {
            break launch;
        }
        assert!(child.try_wait().unwrap().is_none(), "{name}: the controller ended before its launch record ({})", log.display());
        assert!(waited.elapsed() < Duration::from_secs(60), "{name}: no launch record ({})", log.display());
        std::thread::sleep(Duration::from_millis(100));
    };
    let seen = loop {
        let seen = seen_now(&launch);
        if ready(&seen, run) {
            break seen_now(&launch);
        }
        assert!(child.try_wait().unwrap().is_none(), "{name}: the controller ended before the stop point ({})", log.display());
        assert!(waited.elapsed() < Duration::from_secs(1800), "{name}: the stop point never came ({})", log.display());
        std::thread::sleep(Duration::from_millis(200));
    };
    let stopped = Instant::now();
    // SAFETY: kill(2) on the controller this test started and has not reaped.
    unsafe {
        libc::kill(pid, libc::SIGTERM);
    }
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        assert!(stopped.elapsed() < process_stop::GRACE + process_stop::KILL_WAIT + Duration::from_secs(60), "{name}: the controller did not end after SIGTERM");
        std::thread::sleep(Duration::from_millis(100));
    };
    let elapsed_ms = stopped.elapsed().as_millis() as u64;
    eprintln!("launch {name}: stopped by SIGTERM; ended {status:?} after {elapsed_ms} ms ({})", log.display());
    assert_eq!(status.signal(), Some(libc::SIGTERM), "{name}: the controller ends with the stop signal ({})", log.display());
    let stop: Value = read_json(&run.join(RECORD_DIRECTORY).join(format!("stop-{}.json", launch.id))).unwrap();
    assert_eq!((stop["signal"].as_str(), stop["survivors"].clone()), (Some("SIGTERM"), json!([])), "{name}: {stop}");
    // Every process seen just before the stop has ended, and every process group it was in is empty (the test's own
    // group, which the controller shares here, aside).
    // SAFETY: getpgrp has no preconditions.
    let own_group = unsafe { libc::getpgrp() };
    let settled = Instant::now();
    loop {
        let alive: Vec<&Seen> = seen.iter().filter(|p| ProcessStat::read(p.pid).is_some_and(|s| s.start_ticks == p.start_ticks && !matches!(s.state, 'Z' | 'X' | 'x'))).collect();
        let groups: BTreeSet<i32> = seen.iter().map(|p| p.process_group).filter(|g| *g != own_group).collect();
        let in_groups: Vec<i32> = groups.iter().copied().filter(|g| group_has_members(*g)).collect();
        if alive.is_empty() && in_groups.is_empty() {
            break;
        }
        assert!(settled.elapsed() < Duration::from_secs(10), "{name}: left after the stop: {alive:?}; non-empty process groups {in_groups:?}");
        std::thread::sleep(Duration::from_millis(100));
    }
    let left = leftovers(run).unwrap();
    assert_eq!(left.processes, Vec::<Value>::new(), "{name}: {left:?}");
    let stopped_names: BTreeSet<String> = seen.iter().map(|p| p.name.clone()).collect();
    TermStop { name: name.into(), launch, seen, stop, stopped_names, elapsed_ms }
}

/// Whether any live process is in process group `group`.
fn group_has_members(group: i32) -> bool {
    // SAFETY: kill(2) with signal 0 only checks whether the group exists.
    unsafe { libc::kill(-group, 0) == 0 }
}

/// Write the stand-in for the Claude Code CLI (`<dir>/fake-claude.py`, TRIAL FIXTURE): it answers the transport's
/// inspection (`--version` 2.1.286, `--help` with every launch flag); a fresh call writes the init event, starts one Bash
/// tool call as Claude Code does (the configured shell, GenDB's guardian, in a session of its own; the shell starts a
/// background job and a `setsid` job) and a helper in its own process group, records their pids in `fake-ready.json`
/// and waits; on SIGINT it writes its terminal result (session total 1) and exits 130. A resumed call (`--resume`)
/// writes the init event and a terminal result (session total 2) at once. Neither submits.
fn write_fake_author(dir: &Path) -> PathBuf {
    let flags = crate::providers::claude_code::LAUNCH_FLAGS.join(" ");
    let script = format!(
        r#"#!/usr/bin/env python3
# TRIAL FIXTURE (general engine trial, run T; framework test only): a stand-in for the Claude Code CLI. No provider.
import json, os, signal, subprocess, sys, time
args = sys.argv[1:]
if args == ['--version']:
    print('2.1.286 (Claude Code)')
    sys.exit(0)
if args == ['--help']:
    print('{flags}')
    sys.exit(0)

def value(flag):
    return args[args.index(flag) + 1] if flag in args else None

resumed = '--resume' in args
session = value('--resume') if resumed else value('--session-id')
model = value('--model')
tools = ['Bash', 'Read', 'Write', 'Edit'] + [t for t in (value('--allowedTools') or '').split(',') if t]
call_dir = os.environ['TMPDIR']

def emit(event):
    print(json.dumps(event), flush=True)

def result(total):
    emit({{'type': 'result', 'subtype': 'error_during_execution', 'session_id': session, 'total_cost_usd': total, 'duration_ms': 1000,
          'num_turns': 1, 'modelUsage': {{model: {{'inputTokens': 10, 'outputTokens': 10, 'cacheReadInputTokens': 0, 'cacheCreationInputTokens': 0}}}}}})

def stop(signum, frame):
    result('1')
    os._exit(130)

signal.signal(signal.SIGINT, stop)
emit({{'type': 'system', 'subtype': 'init', 'session_id': session, 'model': model, 'tools': tools,
      'mcp_servers': [{{'name': 'gendb_local', 'status': 'connected'}}]}})
if resumed:
    result('2')
    sys.exit(1)
command = 'sleep 600 & echo $! > tool-child; setsid sleep 600 > /dev/null 2>&1 < /dev/null & echo $! > tool-setsid; wait'
tool = subprocess.Popen([os.environ['CLAUDE_CODE_SHELL'], '-c', command], cwd=call_dir, start_new_session=True)
helper = subprocess.Popen(['sleep', '600'])
pids = {{'provider': os.getpid(), 'tool_proxy': tool.pid, 'helper': helper.pid}}
deadline = time.time() + 300
for name in ['tool-child', 'tool-setsid']:
    path = os.path.join(call_dir, name)
    while time.time() < deadline:
        text = open(path).read().strip() if os.path.exists(path) else ''
        if text:
            pids[name] = int(text)
            break
        time.sleep(0.05)
ready = os.path.join(call_dir, '{FAKE_READY}')
with open(ready + '.tmp', 'w') as out:
    json.dump(pids, out)
os.rename(ready + '.tmp', ready)
while True:
    time.sleep(1)
"#
    );
    let path = dir.join("fake-claude.py");
    fs::write(&path, script).unwrap();
    fs::set_permissions(&path, <fs::Permissions as std::os::unix::fs::PermissionsExt>::from_mode(0o700)).unwrap();
    path
}
