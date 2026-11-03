//! The Claude Code transport against fake provider executables (Python scripts), through its public API and the
//! generic controller: launch contract, one continued session, init-event stops, the wall guard, inspection, Bash
//! activity leases and controller-loss recovery. No paid call is made; scratch lives under `TMPDIR`.
//!
//! These tests spawn processes, so they run in this separate test binary: a child forked by one test must never hold a
//! copy of a descriptor another test just released (the controller's resume tests reopen `controller.lock`).

use gendb_synthesis::controller::author::{AuthorCall, AuthorTransport, CandidateSubmission};
use gendb_synthesis::controller::ledger::{Call, Receipt, Trial, UsageScope};
use gendb_synthesis::controller::limits::{Limits, Money, SpendPolicy};
use gendb_synthesis::controller::records;
use gendb_synthesis::controller::role::{PromptInput, QualificationAttempt, RolePolicy, SynthesisRole};
use gendb_synthesis::controller::run::{RunRequest, StopReason, run};
use gendb_synthesis::providers::claude_code::{DEFAULT_MODEL, InspectionError, LAUNCH_FLAGS};
use gendb_synthesis::providers::{AuthorModel, ClaudeCode, LocalToolServer};
use serde_json::{Value, json};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

fn scratch(name: &str) -> PathBuf {
    let tmp = std::env::var_os("TMPDIR").expect("TMPDIR must name a scratch directory");
    let root = PathBuf::from(tmp).join(format!("r12-{name}-{}", records::random_uuid().unwrap()));
    fs::create_dir_all(&root).unwrap();
    root.canonicalize().unwrap()
}

fn call(id: u64) -> Call {
    Call { id, iteration: id as u32, attempt: 1, started_unix_ms: 0, reservation_usd: Money::parse("1").unwrap(), receipt: None, provider_session: None, resumes_provider_session: false, usage_in_resumed_session: false }
}

fn limits(timeout_seconds: u64) -> Limits {
    Limits {
        max_iterations: 2,
        max_cost_usd: Money::parse("1").unwrap(),
        spend_policy: SpendPolicy::EstimatedUsd,
        max_retries_per_iteration: 1,
        max_author_tool_turns: 0,
        author_timeout_seconds: timeout_seconds,
    }
}

fn server() -> LocalToolServer {
    LocalToolServer { program: "/usr/bin/gendb-fixture".into(), arguments: vec!["author-tools".into(), "mcp".into()] }
}

fn local_tool_names() -> Vec<String> {
    ["check", "verify", "compile", "trial", "profile"].map(|tool| format!("mcp__gendb_local__{tool}")).into()
}

fn read(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).unwrap()).unwrap()
}

/// A fake Claude Code executable: answers `--version` with `version` and `--help` with every launch flag, and runs
/// `body` (Python, with `args` = argv) for a call. Inspection never reaches `body`. The transport pins the default model.
fn fake_cli(root: &Path, name: &str, version: &str, body: &str) -> ClaudeCode {
    fake_cli_of(root, name, version, body, AuthorModel::default())
}

fn fake_cli_of(root: &Path, name: &str, version: &str, body: &str, model: AuthorModel) -> ClaudeCode {
    let executable = root.join(format!("{name}.py"));
    fs::write(
        &executable,
        format!(
            "#!/usr/bin/env python3\nimport json,os,pathlib,signal,subprocess,sys,time,fcntl\nargs=sys.argv[1:]\nif args==['--version']: print('{version}'); sys.exit(0)\nif args==['--help']: print('{}'); sys.exit(0)\n{body}\n",
            LAUNCH_FLAGS.join(" ")
        ),
    )
    .unwrap();
    fs::set_permissions(&executable, fs::Permissions::from_mode(0o700)).unwrap();
    // A process another test forks while this file is open for writing holds a copy of that descriptor until it execs;
    // executing the file meanwhile fails with ETXTBSY. Retry briefly; any other error is the test's failure.
    for _ in 0..50 {
        match ClaudeCode::inspect(executable.clone(), model, root, server()) {
            Err(InspectionError::Unavailable(e)) if e.kind() == std::io::ErrorKind::ExecutableFileBusy => {
                std::thread::sleep(Duration::from_millis(20))
            }
            inspected => return inspected.unwrap(),
        }
    }
    panic!("{} stayed busy", executable.display())
}

fn invoke(transport: &mut ClaudeCode, call: &Call, resume: bool, prompt: &str, workspace: &Path, call_dir: &Path, limits: &Limits) -> Receipt {
    transport.invoke(&AuthorCall { call, session_id: "same-session", resume, prompt, workspace, call_dir, limits })
}

#[test]
fn cost_receipt_survives_subprocess_failure_and_wall_guard() {
    let root = scratch("cost-exit");
    for (name, ending) in [("failed", "raise SystemExit(7)"), ("timeout", "time.sleep(10)")] {
        let body = format!(
            "s=args[args.index('--session-id')+1]\nprint(json.dumps({{'type':'result','session_id':s,'subtype':'error_during_execution','total_cost_usd':'0.375'}}),flush=True)\n{ending}"
        );
        let mut transport = fake_cli(&root, name, "fixture", &body);
        let r = invoke(&mut transport, &call(1), false, "fixture", &root, &root.join(name), &limits(1));
        assert_eq!(r.provider_cost().unwrap().decimal(), "0.375", "{name}: {r:?}");
        assert!(r.output.is_none() && r.raw_result.is_some());
        assert_eq!(r.usage_scope, None, "an uninspected version declares no scope");
        let expected = if name == "timeout" { "author_timeout; usage remains unknown until reconciled" } else { "error_during_execution; incomplete token usage" };
        assert_eq!(r.outcome, expected);
    }
}

/// I2 (q3-run-01 query call 2): the MCP server connected but its tools were absent from the provider init event; the
/// whole call was paid for and only then refused. The call now stops at that event, as it does for another model.
#[test]
fn disqualifying_init_event_stops_the_call_before_its_paid_work() {
    let root = scratch("init-stop");
    let context = root.join("local-tool.json");
    fs::write(&context, "{}").unwrap();
    for (name, model, tools, expected) in [
        ("missing-tools", DEFAULT_MODEL, "['Bash','Read','Write','Edit','Glob','Grep','StructuredOutput']", "missing required local tools"),
        ("other-model", "claude-haiku-4-5", "['Bash','Read']+args[args.index('--allowedTools')+1].split(',')", "Claude did not select the requested model"),
    ] {
        let body = format!(
            r#"s=args[args.index('--session-id')+1]
print(json.dumps({{'type':'system','subtype':'init','session_id':s,'model':'{model}','tools':{tools},
    'mcp_servers':[{{'name':'gendb_local','status':'connected'}}]}}),flush=True)
def stop(*_):
    print(json.dumps({{'type':'result','session_id':s,'subtype':'error_during_execution',
        'total_cost_usd':'0.002','terminal_reason':'aborted_streaming'}}),flush=True)
    raise SystemExit(130)
signal.signal(signal.SIGINT,stop)
time.sleep(600)"#
        );
        let mut transport = fake_cli(&root, name, "fixture", &body);
        transport.configure_context(&json!({"local_tools":{"mcp_context":context,"required_tools":local_tool_names()}})).unwrap();
        let started = Instant::now();
        let dir = root.join(name);
        let r = invoke(&mut transport, &call(1), false, "fixture", &root, &dir, &limits(600));
        assert!(started.elapsed() < Duration::from_secs(20), "{name}: {:?}", started.elapsed());
        assert!(r.outcome.contains(expected), "{name}: {}", r.outcome);
        assert!(r.output.is_none());
        assert_eq!(r.provider_cost().unwrap().decimal(), "0.002", "the provider's own terminal result accounts the usage");
        let abort = &read(&dir.join("process-exit.json"))["init_capability_abort"];
        assert_eq!((abort["stopped_at_provider_init"].clone(), abort["signal"].clone()), (json!(true), json!("SIGINT")));
        let capabilities = read(&dir.join("tool-capabilities.json"));
        assert_eq!(capabilities["init_capability_abort"]["stopped_at_provider_init"], true);
        let missing = if name == "missing-tools" { 5 } else { 0 };
        assert_eq!(capabilities["missing_required_tools"].as_array().unwrap().len(), missing);
    }
}

#[test]
fn inspection_retains_complete_help_and_refuses_failed_help_or_missing_flags() {
    let root = scratch("inspection");
    let executable = root.join("fixture.py");
    let source = format!(
        r#"#!/usr/bin/env python3
import os,stat,sys
if sys.argv[1:] == ['--version']:
    print('fixture 1'); sys.exit(0)
assert sys.argv[1:] == ['--help'], 'inspection must never dispatch inference'
help_text = 'x'*9000 + '\n{}\n'
# Model the installed CLI's successful-but-truncated pipe output.
sys.stdout.write(help_text[:8192] if stat.S_ISFIFO(os.fstat(1).st_mode) else help_text)
"#,
        LAUNCH_FLAGS.join(" ")
    );
    let write = |source: &str| {
        fs::write(&executable, source).unwrap();
        fs::set_permissions(&executable, fs::Permissions::from_mode(0o700)).unwrap();
    };
    write(&source);
    let evidence = root.join("first");
    let transport = ClaudeCode::inspect(executable.clone(), AuthorModel::default(), &evidence, server()).unwrap();
    assert_eq!(transport.capability().version, "fixture 1");
    let inspection = fs::read_dir(&evidence).unwrap().next().unwrap().unwrap().path();
    assert!(read(&inspection.join("help.json"))["stdout_bytes"].as_u64().unwrap() > 8192);
    assert!(fs::read_to_string(inspection.join("help.stdout.txt")).unwrap().contains("--session-id"));
    // Complete-looking output does not override a failed capability command.
    write(&format!("{source}\nsys.exit(7)\n"));
    let error = ClaudeCode::inspect(executable.clone(), AuthorModel::default(), &root, server()).err().unwrap().to_string();
    assert!(error.contains("help inspection failed") && error.contains('7'), "{error}");
    write(&source.replace(" --strict-mcp-config", ""));
    let error = ClaudeCode::inspect(executable, AuthorModel::default(), &root, server()).err().unwrap().to_string();
    assert!(error.starts_with("Claude transport lacks --strict-mcp-config; evidence "), "{error}");
}

#[test]
fn activity_adapter_versions_are_explicit() {
    let root = scratch("activity-versions");
    for (version, supported) in [("2.1.270", true), ("2.1.273", true), ("2.1.274", false), ("2.1.280", true), ("fixture", false)] {
        let mut transport = fake_cli(&root, &format!("v{version}"), &format!("{version} (fixture)"), "sys.exit(1)");
        assert_eq!(transport.tool_activity_lock(&root.join("activity.lock")).is_ok(), supported, "{version}");
        assert!(transport.tool_activity_lock(Path::new("relative.lock")).is_err());
    }
}

/// The installed guardian of a real invocation passes the guardian's 13 unpaid subprocess cases, run by the fake
/// provider itself through `CLAUDE_CODE_SHELL` (exactly the wrapper and environment the provider receives).
#[test]
fn activity_shell_guardian_lifecycle_inside_an_invocation() {
    let root = scratch("activity-shell");
    let guardian_test = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/providers/claude_code/activity_shell_test.py");
    let body = format!(
        r#"s=args[args.index('--session-id')+1]
assert os.environ['BASH_DEFAULT_TIMEOUT_MS']==os.environ['BASH_MAX_TIMEOUT_MS']=='42000'
check=subprocess.run(['/usr/bin/python3','{}',os.environ['CLAUDE_CODE_SHELL']],capture_output=True)
pathlib.Path('guardian-test.txt').write_bytes(check.stdout+check.stderr)
print(json.dumps({{'type':'result','session_id':s,'subtype':'success' if check.returncode==0 else 'error_during_execution','total_cost_usd':'0'}}))
sys.exit(check.returncode)"#,
        guardian_test.display()
    );
    let mut transport = fake_cli(&root, "guardian", "2.1.280 (fixture)", &body);
    assert!(transport.tool_activity_lock(&root.join("activity.lock")).unwrap());
    let r = invoke(&mut transport, &call(1), false, "fixture", &root, &root.join("call"), &limits(42));
    let report = fs::read_to_string(root.join("guardian-test.txt")).unwrap();
    // The fixture result has no `modelUsage`: the refused outcome also names the incomplete token usage.
    assert_eq!(r.outcome, "transport_error: successful result without model/init or successful exit; incomplete token usage", "{report}");
    let summary: Value = serde_json::from_str(report.lines().last().unwrap()).unwrap();
    assert_eq!((summary["status"].clone(), summary["cases"].clone(), summary["paid_calls"].clone()), (json!("passed"), json!(13), json!(0)));
    let activity = &read(&root.join("call/invocation.json"))["tool_activity"];
    assert_eq!((activity["default_timeout_ms"].clone(), activity["max_timeout_ms"].clone()), (json!(42000), json!(42000)));
}

/// A fake Claude Code 2.1.280 for whole sessions: checks the launch contract, keeps the session in its working
/// directory (the author workspace), reports session-cumulative `total_cost_usd`/`modelUsage` like the real CLI and
/// per-invocation `usage`/`duration_ms`, and submits a manifest it wrote. The first call of a session must create it,
/// later calls must resume it. [`fake_session`] defines `expected`, the transport's model id, which it also reports.
const FAKE_SESSION: &str = r#"assert args[args.index('--model')+1]==expected and args[args.index('--effort')+1]=='high'
assert '--fallback-model' not in args and not any(arg.startswith('--max-turns') for arg in args)
assert args[args.index('--permission-mode')+1]=='bypassPermissions' and '--allow-dangerously-skip-permissions' in args
assert args[args.index('--output-format')+1]=='stream-json' and '--verbose' in args and '--print' in args
assert args[args.index('--tools')+1]=='Read,Write,Edit,Glob,Grep,Bash'
allowed=args[args.index('--allowedTools')+1].split(',')
assert args[args.index('--setting-sources')+1]=='' and '--strict-mcp-config' in args
cfg=json.loads(pathlib.Path(args[args.index('--mcp-config')+1]).read_text())['mcpServers']['gendb_local']
assert cfg['command']=='/usr/bin/gendb-fixture' and cfg['args'][:2]==['author-tools','mcp'] and pathlib.Path(cfg['args'][2]).is_file()
assert os.environ['CLAUDE_CODE_DISABLE_AUTO_MEMORY']=='1' and os.environ['ANTHROPIC_SMALL_FAST_MODEL']==expected
assert pathlib.Path(os.environ['TMPDIR'])==pathlib.Path(args[args.index('--mcp-config')+1]).parent
if 'CLAUDE_CODE_SHELL' in os.environ:
    # Model inference holds no activity lease; each shell tool call acquires its own.
    wrapper=pathlib.Path(os.environ['CLAUDE_CODE_SHELL'])
    lock=json.loads((wrapper.parent/'activity-config.json').read_text())['activity_lock']
    with open(lock,'a') as fd: fcntl.flock(fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
    assert 'CLAUDE_CODE_SHELL_PREFIX' not in os.environ
    assert subprocess.check_output([str(wrapper),'-c','printf shell-ok'])==b'shell-ok'
    assert subprocess.check_output([str(wrapper),'-c','-l','printf login-ok'])==b'login-ok'
resume='--resume' in args
sid=args[args.index('--resume' if resume else '--session-id')+1]
state_path=pathlib.Path('fake-session-%s.json'%sid)
state=json.loads(state_path.read_text()) if state_path.exists() else None
assert (state is not None)==resume and (state is None or state['session']==sid)
prompt=sys.stdin.read()
calls=(state or {'calls':0})['calls']+1
state_path.write_text(json.dumps({'session':sid,'calls':calls}))
pathlib.Path('c%d'%calls).mkdir(exist_ok=True)
pathlib.Path('c%d/candidate.json'%calls).write_text('{}')
per_call={'inputTokens':10,'outputTokens':100,'cacheReadInputTokens':1000,'cacheCreationInputTokens':50}
cumulative={k:v*calls for k,v in per_call.items()}
print(json.dumps({'type':'system','subtype':'init','session_id':sid,'model':expected,'claude_code_version':'2.1.280',
    'tools':['Read','Write','Edit','Glob','Grep','Bash']+allowed,'mcp_servers':[{'name':'gendb_local','status':'connected'}]}))
print(json.dumps({'type':'assistant','session_id':sid,'message':{'content':[{'type':'text','text':'working on %d prompt bytes'%len(prompt)}]}}))
print(json.dumps({'type':'result','subtype':'success','session_id':sid,'total_cost_usd':0.25*calls,'duration_ms':7,
    'usage':{'input_tokens':10,'output_tokens':100,'cache_read_input_tokens':1000,'cache_creation_input_tokens':50},
    'modelUsage':{expected:dict(cumulative,costUSD=0.25*calls)},
    'structured_output':{'candidate_manifest':'c%d/candidate.json'%calls,'rationale':'revision','data_access_analysis':'required columns'}}))"#;

/// A fake Claude Code 2.1.280 session CLI for a transport of `model`.
fn fake_session(root: &Path, model: AuthorModel) -> ClaudeCode {
    fake_cli_of(root, "claude", "2.1.280 (Claude Code)", &format!("expected='{}'\n{FAKE_SESSION}", model.id()), model)
}

#[test]
fn one_session_continues_across_calls_with_bash_leases_and_session_scoped_receipts() {
    let root = scratch("fake-session");
    let mut transport = fake_session(&root, AuthorModel::default());
    assert!(transport.tool_activity_lock(&root.join("activity.lock")).unwrap());
    let workspace = root.join("author");
    fs::create_dir_all(&workspace).unwrap();
    fs::write(workspace.join("local-tool.json"), "{}").unwrap();
    let context = json!({"local_tools":{"mcp_context":workspace.join("local-tool.json"),"required_tools":local_tool_names(),"transport":"typed stdio MCP"}});
    transport.configure_context(&context).unwrap();
    assert!(transport.definitely_not_dispatched(&root.join("call1")).unwrap());
    let limits = limits(5);
    let first = invoke(&mut transport, &call(1), false, "first", &workspace, &root.join("call1"), &limits);
    assert_eq!(first.outcome, "success");
    assert!(!transport.definitely_not_dispatched(&root.join("call1")).unwrap());
    let second = invoke(&mut transport, &call(2), true, "feedback", &workspace, &root.join("call2"), &limits);
    assert_eq!((second.outcome.as_str(), first.session_id.as_str()), ("success", second.session_id.as_str()));
    assert_eq!(second.output.as_ref().unwrap()["candidate_manifest"], "c2/candidate.json");
    assert_eq!((first.usage_scope, second.usage_scope), (Some(UsageScope::Session), Some(UsageScope::Session)));
    assert_eq!((first.provider_cost().unwrap().decimal(), second.provider_cost().unwrap().decimal()), ("0.25".into(), "0.5".into()));
    assert_eq!(second.tokens.as_ref().map(|t| (t.input, t.output)), Some((20, 200)), "session-cumulative modelUsage");
    let invocation = read(&root.join("call2/invocation.json"));
    assert_eq!(invocation["usage_scope"], "session");
    assert_eq!((invocation["tool_activity"]["default_timeout_ms"].clone(), invocation["tool_activity"]["max_timeout_ms"].clone()), (json!(5000), json!(5000)));
    assert_eq!(invocation["session_environment"]["variables"], json!({"CLAUDE_CODE_DISABLE_AUTO_MEMORY":"1","ANTHROPIC_SMALL_FAST_MODEL":"claude-opus-5-5","DISABLE_AUTOUPDATER":"1"}));
    let argv: Vec<String> = serde_json::from_value(invocation["argv"].clone()).unwrap();
    assert_eq!(argv[argv.iter().position(|a| a == "--allowedTools").unwrap() + 1], local_tool_names().join(","));
    assert_eq!(argv[argv.len() - 2..], ["--resume".to_string(), "same-session".into()]);
    let capabilities = read(&root.join("call2/tool-capabilities.json"));
    assert_eq!((capabilities["missing_required_tools"].clone(), capabilities["mcp_servers"][0]["status"].clone()), (json!([]), json!("connected")));
    let usage = read(&root.join("call2/model-usage.json"));
    assert_eq!((usage["pinned_model"].as_str(), usage["other_models"].clone()), (Some(DEFAULT_MODEL), json!([])));
    // The visible transcript keeps every provider event.
    assert_eq!(fs::read_to_string(root.join("call2/stdout.jsonl")).unwrap().lines().count(), 3);
}

/// A transport of a selected model launches, pins the helper model, accepts the init and records usage and capability
/// with that model; the default model's launch is unchanged (previous test).
#[test]
fn selected_author_model_is_launched_pinned_and_recorded() {
    let root = scratch("selected-model");
    let model = AuthorModel::Sonnet55;
    let mut transport = fake_session(&root, model);
    let workspace = root.join("author");
    fs::create_dir_all(&workspace).unwrap();
    fs::write(workspace.join("local-tool.json"), "{}").unwrap();
    transport.configure_context(&json!({"local_tools":{"mcp_context":workspace.join("local-tool.json"),"required_tools":local_tool_names()}})).unwrap();
    assert_eq!(transport.capability().model, "claude-sonnet-5-5");
    let receipt = invoke(&mut transport, &call(1), false, "first", &workspace, &root.join("call1"), &limits(5));
    assert_eq!(receipt.outcome, "success");
    let invocation = read(&root.join("call1/invocation.json"));
    let argv: Vec<String> = serde_json::from_value(invocation["argv"].clone()).unwrap();
    assert_eq!(argv[argv.iter().position(|a| a == "--model").unwrap() + 1], model.id());
    assert_eq!(invocation["session_environment"]["variables"]["ANTHROPIC_SMALL_FAST_MODEL"], model.id());
    assert_eq!((invocation["capability"]["model"].as_str(), invocation["capability"]["effort"].as_str()), (Some(model.id()), Some("high")));
    let usage = read(&root.join("call1/model-usage.json"));
    assert_eq!((usage["pinned_model"].as_str(), usage["other_models"].clone()), (Some(model.id()), json!([])));
}

fn provider_stream(session: &str, cost: &str, terminal: bool) -> String {
    let init = json!({"type":"system","subtype":"init","session_id":session,"model":DEFAULT_MODEL});
    let result = json!({"type":"result","subtype":"error_during_execution","session_id":session,
        "duration_ms":1_071_344u64,"total_cost_usd":cost,"terminal_reason":"aborted_streaming",
        "modelUsage":{DEFAULT_MODEL:{"inputTokens":38,"outputTokens":29551,"cacheReadInputTokens":10,"cacheCreationInputTokens":12}}});
    if terminal { format!("{init}\n{result}\n") } else { format!("{init}\n{}\n", json!({"type":"assistant","session_id":session})) }
}

/// A lost call's records as `invoke` leaves them after dispatch: `invocation.json` (a minimal historical record,
/// without the CLI version) and the provider stream.
fn lost_call_dir(base: &Path, call: &Call, stream: &str) -> PathBuf {
    let dir = base.join(format!("calls/{:04}", call.id));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("invocation.json"), json!({"call":call}).to_string()).unwrap();
    // Coarse filesystem clocks can stamp an immediate write before dispatch time.
    std::thread::sleep(Duration::from_millis(50));
    fs::write(dir.join("stdout.jsonl"), stream).unwrap();
    dir.canonicalize().unwrap()
}

/// Controller loss after dispatch: settle once from the actual terminal provider result when no invocation process
/// survives; refuse incomplete or foreign streams and record why.
#[test]
fn controller_loss_receipt_requires_terminal_result_session_and_no_live_invocation() {
    let base = scratch("lost-call");
    let transport = fake_cli(&base, "claude", "2.1.280 (Claude Code)", "sys.exit(1)");
    let workspace = base.join("author");
    let call = Call { id: 4, iteration: 3, attempt: 1, started_unix_ms: 1, reservation_usd: Money::parse("13").unwrap(), receipt: None, provider_session: None, resumes_provider_session: false, usage_in_resumed_session: false };
    let recover = |call: &Call, session: &str, dir: &Path| transport.recover_receipt(call, session, dir, &workspace).unwrap();
    let refusal = |dir: &Path| read(&dir.join("controller-loss-recovery-refused.json"))["reason"].as_str().unwrap().to_string();
    let dir = lost_call_dir(&base, &call, &provider_stream("session-a", "7.2810115", true));
    // A live process holding the provider stream or the call TMPDIR blocks settlement.
    for tmpdir in [false, true] {
        let mut command = std::process::Command::new("sleep");
        command.arg("30");
        if tmpdir {
            command.env("TMPDIR", &dir);
        } else {
            command.stdout(fs::OpenOptions::new().append(true).open(dir.join("stdout.jsonl")).unwrap());
        }
        let mut child = command.spawn().unwrap();
        assert_eq!(recover(&call, "session-a", &dir), None);
        let reason = refusal(&dir);
        assert!(reason.contains("invocation processes still alive") && reason.contains(&child.id().to_string()), "{reason}");
        child.kill().unwrap();
        child.wait().unwrap();
    }
    let receipt = recover(&call, "session-a", &dir).unwrap();
    assert_eq!(receipt.provider_cost(), Some(Money::parse("7.2810115").unwrap()));
    assert_eq!(receipt.elapsed_ms, 1_071_344);
    assert!(receipt.output.is_none());
    assert_eq!(receipt.outcome, "controller_loss_recovery: error_during_execution");
    assert_eq!(receipt.tokens.as_ref().unwrap().output, 29551);
    assert_eq!(receipt.usage_scope, None, "a record without the CLI version declares no scope");
    assert_eq!(read(&dir.join("controller-loss-recovery.json"))["output_accepted"], false);
    assert!(!dir.join("process-exit.json").exists());
    // Wrong session, incomplete stream, trailing event and mismatched invocation refuse.
    assert_eq!(recover(&call, "session-b", &dir), None);
    assert!(refusal(&dir).contains("different session"));
    for (name, stream) in [
        ("incomplete", provider_stream("session-a", "1", false)),
        ("trailing", format!("{}{}\n", provider_stream("session-a", "1", true), json!({"type":"assistant"}))),
    ] {
        let dir = lost_call_dir(&base.join(name), &call, &stream);
        assert_eq!(recover(&call, "session-a", &dir), None);
        assert!(refusal(&dir).contains("exactly one terminal result"), "{name}");
    }
    let other = Call { id: 5, ..call.clone() };
    let other_dir = base.join("calls/0005");
    fs::create_dir_all(&other_dir).unwrap();
    for name in ["invocation.json", "stdout.jsonl"] {
        fs::copy(dir.join(name), other_dir.join(name)).unwrap();
    }
    assert_eq!(recover(&other, "session-a", &other_dir), None);
    assert!(refusal(&other_dir).contains("different call"));
    // A call directory that does not exist has nothing to recover.
    assert_eq!(recover(&call, "session-a", &base.join("calls/0009")), None);
}

#[derive(Clone)]
struct FirstEligible;

impl RolePolicy for FirstEligible {
    fn author_prompt(&self, input: &PromptInput) -> String {
        format!("iteration {} of the fixture role; ledger {}", input.iteration, input.ledger)
    }

    fn search_stop(&self, _context: &Value, trials: &[Trial]) -> Option<StopReason> {
        trials.iter().any(Trial::eligible).then_some(StopReason::FirstEligibleCandidate)
    }
}

/// A scripted role: declares the local tools, freezes only the submission, rejects the first evaluation.
struct SecondSubmissionEligible {
    evaluated: u32,
}

impl SynthesisRole for SecondSubmissionEligible {
    type Policy = FirstEligible;

    fn policy(&self) -> FirstEligible {
        FirstEligible
    }

    async fn prepare(&mut self, _: &RunRequest, workspace: &Path) -> Result<Value, String> {
        let context = workspace.join("local-tool.json");
        fs::write(&context, "{}").map_err(|e| e.to_string())?;
        Ok(json!({"local_tools":{"mcp_context":context,"required_tools":local_tool_names()}}))
    }

    async fn freeze(&mut self, _: &Path, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<Value, String> {
        fs::create_dir_all(frozen_dir).map_err(|e| e.to_string())?;
        Ok(json!({"manifest":submission.candidate_manifest}))
    }

    async fn evaluate(&mut self, _: &Path, _: &Value) -> Result<Value, String> {
        self.evaluated += 1;
        Ok(json!({"eligible":self.evaluated > 1,"score_ns":100,"status":"fixture"}))
    }

    async fn qualify(&mut self, _: &Path, _: &Value) -> Result<Value, String> {
        Ok(json!({"qualified":true}))
    }

    async fn close(&mut self, _: &[Trial], qualification: &[QualificationAttempt]) -> Result<Value, String> {
        Ok(json!({"selected":!qualification.is_empty()}))
    }
}

/// The transport inside the generic controller: each attempt (submission) runs in a fresh provider session, and each
/// session's receipts are counted by their declared session scope.
#[tokio::test]
async fn controller_starts_a_fresh_provider_session_per_attempt_and_counts_each_once() {
    let root = scratch("controller-session");
    let mut transport = fake_session(&root, AuthorModel::default());
    let request = RunRequest {
        format_version: 1,
        task: json!({"fixture":"r12"}),
        limits: Limits { max_iterations: 3, max_cost_usd: Money::parse("5").unwrap(), ..limits(60) },
        continue_from: None,
    };
    let mut role = SecondSubmissionEligible { evaluated: 0 };
    let summary = run(&request, &root.join("run"), &mut transport, &mut role).await.unwrap();
    assert_eq!((summary["status"].clone(), summary["reason"].clone(), summary["calls"].clone()), (json!("closed"), json!("first_eligible_candidate"), json!(2)));
    assert_eq!(summary["reported_cost_usd"], "0.5", "two fresh sessions of 0.25 each: {summary}");
    assert_eq!(summary["accounting"]["raw_receipt_sum_usd"], "0.5");
    assert_eq!(summary["accounting"]["tokens"]["output"], 200);
    assert_eq!(summary["accounting"]["counted_by_call"][1]["basis"], "session_first");
    let ledger = read(&root.join("run/ledger.json"));
    let receipts: Vec<&Value> = ledger["calls"].as_array().unwrap().iter().map(|call| &call["receipt"]).collect();
    assert!(receipts.iter().all(|receipt| receipt["usage_scope"] == "session" && receipt["elapsed_ms"].as_u64().is_some()));
    let second_argv = read(&root.join("run/calls/0002/invocation.json"))["argv"].clone();
    assert!(!second_argv.as_array().unwrap().iter().any(|argument| argument == "--resume"), "a new attempt never resumes");
    assert_ne!(receipts[0]["session_id"], receipts[1]["session_id"]);
}
