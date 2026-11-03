//! Pinned Verus through `gendb_verification::verus`: tiny fixtures only (no query code).
//! The toolchain tests need the installed toolchain (`GENDB_VERUS_HOME`, default `<repository>/toolchains`);
//! run them with `--ignored`. The refusal test needs no toolchain.
use gendb_verification::verus::{
    compile_unverified, freeze_crate, rule, run_verus, CodegenOptions, FrameworkSource, FreezeError, FrozenCrate, VerusMode, VerusOptions,
    VerusOutcome, VerusRun, VerusToolchain, NO_VERIFY,
};
use std::path::{Path, PathBuf};

/// Framework crate root for the fixtures.
const LIB_RS: &str = "#![allow(unused)]\npub mod gendb_workers;\npub mod agent;\nmod gendb_shim;\n";

/// Fixture framework module: verified pass-throughs over vstd spawn/join.
const WORKERS_RS: &str = r#"use vstd::prelude::*;
verus! {
#[verifier::reject_recursive_types(T)]
pub struct Worker<T> { handle: vstd::thread::JoinHandle<T> }
impl<T> Worker<T> {
    pub closed spec fn predicate(&self, r: T) -> bool { self.handle.predicate(r) }
}
pub fn spawn_worker<F, T>(f: F) -> (w: Worker<T>)
    where F: FnOnce() -> T + Send + 'static, T: Send + 'static,
    requires f.requires(()),
    ensures forall|r: T| #[trigger] w.predicate(r) ==> f.ensures((), r),
{
    Worker { handle: vstd::thread::spawn(f) }
}
pub fn join_worker<T>(w: Worker<T>) -> (r: Result<T, ()>)
    ensures r matches Ok(v) ==> w.predicate(v),
{
    w.handle.join()
}
}
"#;

/// Fixture trusted C ABI shim (outside verus!, not scanned).
const SHIM_RS: &str = r#"
#[unsafe(no_mangle)]
pub unsafe extern "C" fn gendb_fixture_sum(ptr: *const i64, len: usize, out: *mut i128) -> i32 {
    if len > 1_000_000_000 { return 2; }
    let v: &'static [i64] = if len == 0 { &[] } else { unsafe { std::slice::from_raw_parts(ptr, len) } };
    match crate::agent::sum_two(v) {
        Ok(x) => { unsafe { *out = x; } 0 }
        Err(()) => 1,
    }
}
"#;

/// Author fixture: exact i128 sum of a slice, split over one spawned worker.
const AGENT_OK: &str = r#"use vstd::prelude::*;
use crate::gendb_workers::{spawn_worker, join_worker};
verus! {
pub open spec fn sum_spec(s: Seq<i64>) -> int decreases s.len() {
    if s.len() == 0 { 0 } else { sum_spec(s.drop_last()) + s.last() as int }
}
proof fn lemma_sum_append(a: Seq<i64>, b: Seq<i64>)
    ensures sum_spec(a + b) == sum_spec(a) + sum_spec(b),
    decreases b.len(),
{
    if b.len() == 0 { assert(a + b =~= a); } else {
        lemma_sum_append(a, b.drop_last());
        assert((a + b).drop_last() =~= a + b.drop_last());
    }
}
fn sum_range(v: &[i64], lo: usize, hi: usize) -> (r: i128)
    requires lo <= hi <= v.len(), hi - lo <= 1_000_000_000,
    ensures r as int == sum_spec(v@.subrange(lo as int, hi as int)),
        -((hi - lo) as int) * 0x8000_0000_0000_0000 <= r as int <= ((hi - lo) as int) * 0x8000_0000_0000_0000,
{
    let mut acc: i128 = 0;
    let mut i = lo;
    while i < hi
        invariant lo <= i <= hi <= v.len(), hi - lo <= 1_000_000_000,
            acc as int == sum_spec(v@.subrange(lo as int, i as int)),
            -((i - lo) as int) * 0x8000_0000_0000_0000 <= acc as int <= ((i - lo) as int) * 0x8000_0000_0000_0000,
        decreases hi - i,
    {
        assert(v@.subrange(lo as int, i as int + 1).drop_last() =~= v@.subrange(lo as int, i as int));
        acc = acc + v[i] as i128;
        i = i + 1;
    }
    acc
}
pub fn sum_two(v: &'static [i64]) -> (r: Result<i128, ()>)
    requires v.len() <= 1_000_000_000,
    ensures r matches Ok(x) ==> x as int == sum_spec(v@),
{
    let mid = v.len() / 2;
    let w = spawn_worker(move || -> (r: i128)
        requires mid <= v.len() <= 1_000_000_000,
        ensures r as int == sum_spec(v@.subrange(0, mid as int)),
            -(mid as int) * 0x8000_0000_0000_0000 <= r as int <= (mid as int) * 0x8000_0000_0000_0000,
    { sum_range(v, 0, mid) });
    let right = sum_range(v, mid, v.len());
    match join_worker(w) {
        Ok(left) => {
            proof {
                lemma_sum_append(v@.subrange(0, mid as int), v@.subrange(mid as int, v.len() as int));
                assert(v@.subrange(0, mid as int) + v@.subrange(mid as int, v.len() as int) =~= v@);
            }
            Ok(left + right)
        }
        Err(()) => Err(()),
    }
}
}
"#;

/// Author items that implementation ownership accepts (inserted into `AGENT_OK`'s `verus!` block).
const OWN_IMPLS: &str = "pub struct Local { x: u64 }\nimpl Local { pub open spec fn x_of(&self) -> int { self.x as int } }\n\
    impl View for Local { type V = int; open spec fn view(&self) -> int { self.x as int } }\n\
    pub trait Doubled { spec fn doubled(&self) -> int; }\nimpl Doubled for u64 { open spec fn doubled(&self) -> int { 2 * *self } }\n";

/// A fresh directory under Cargo's per-target scratch directory (never the system temporary directory).
fn scratch(name: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let d = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("verus-toolchain-test-{name}-{}-{nanos}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn framework() -> Vec<FrameworkSource> {
    [("lib.rs", LIB_RS), ("gendb_workers.rs", WORKERS_RS), ("gendb_shim.rs", SHIM_RS)]
        .into_iter()
        .map(|(p, t)| FrameworkSource { path: p.into(), text: t.into() })
        .collect()
}

fn options() -> VerusOptions {
    VerusOptions { crate_name: "gendb_fixture".into(), codegen: CodegenOptions { opt_level: 3, target_cpu: None }, num_threads: Some(4) }
}

fn author(dir: &Path, text: &str) -> PathBuf {
    let agent = dir.join("workspace-agent");
    std::fs::create_dir_all(&agent).unwrap();
    std::fs::write(agent.join("mod.rs"), text).unwrap();
    agent
}

type SumFn = unsafe extern "C" fn(*const i64, usize, *mut i128) -> i32;

fn call_sum(library: &Path, values: &[i64]) -> (i32, i128) {
    let path = std::ffi::CString::new(library.to_str().unwrap()).unwrap();
    unsafe {
        let handle = libc::dlopen(path.as_ptr(), libc::RTLD_NOW | libc::RTLD_LOCAL);
        assert!(!handle.is_null(), "dlopen failed");
        let symbol = libc::dlsym(handle, c"gendb_fixture_sum".as_ptr());
        assert!(!symbol.is_null(), "entry symbol missing");
        let f: SumFn = std::mem::transmute(symbol);
        // The shim treats the input as 'static: leak a copy for the process lifetime.
        let owned: &'static [i64] = Box::leak(values.to_vec().into_boxed_slice());
        let mut out = 0i128;
        let rc = f(owned.as_ptr(), owned.len(), &mut out);
        (rc, out)
    }
}

#[test]
#[ignore = "requires the pinned Verus installation"]
fn pinned_version_matches() {
    let tc = VerusToolchain::from_env().unwrap();
    let v = tc.version().unwrap();
    assert_eq!(v["verus"]["commit"], "671956ec527d3b7164779f767bdbfe769bedce6c");
}

#[test]
#[ignore = "requires the pinned Verus installation"]
fn verified_fixture_compiles_to_loadable_library() {
    let tc = VerusToolchain::from_env().unwrap();
    let dir = scratch("ok");
    let frozen = freeze_crate(&author(&dir, AGENT_OK), &framework(), &dir.join("verus")).unwrap();
    assert_eq!(frozen.agent_files, vec!["mod.rs".to_string()]);
    // Frozen snapshot is read-only.
    assert!(std::fs::write(frozen.root.join("src/agent/mod.rs"), "x").is_err());

    let checked = run_verus(&tc, &frozen, &options(), VerusMode::Verify, &dir.join("verify")).unwrap();
    assert_eq!(checked.outcome, VerusOutcome::Verified, "{}\n{}", checked.detail, checked.stderr);
    assert!(checked.artifact.is_none());

    let run = run_verus(&tc, &frozen, &options(), VerusMode::VerifyAndCompile, &dir.join("build")).unwrap();
    assert_eq!(run.outcome, VerusOutcome::Compiled, "{}\n{}", run.detail, run.stderr);
    let summary = run.verification.clone().unwrap();
    assert!(summary.success && summary.errors == 0 && summary.verified > 0 && summary.is_verifying_entire_crate);
    assert!(run.invocation.args.contains(&"--no-cheating".to_string()));
    assert!(!run.invocation.args.iter().any(|a| a == "--no-verify"));
    let lib = run.artifact.clone().unwrap();
    let big = [i64::MAX; 7];
    for values in [&[][..], &[5][..], &[1, 2, 3, 4, 5][..], &big[..], &[i64::MIN, i64::MIN, i64::MIN][..]] {
        let expected: i128 = values.iter().map(|v| *v as i128).sum();
        assert_eq!(call_sum(&lib, values), (0, expected), "{values:?}");
    }
    println!("verified={} wall_ms={}", summary.verified, run.wall_ns / 1_000_000);
}

#[test]
#[ignore = "requires the pinned Verus installation"]
fn failed_proof_writes_no_library() {
    let tc = VerusToolchain::from_env().unwrap();
    let dir = scratch("proof");
    // Wrong implementation: returns only the right half.
    let wrong = AGENT_OK.replace("Ok(left + right)", "Ok(right)");
    let frozen = freeze_crate(&author(&dir, &wrong), &framework(), &dir.join("verus")).unwrap();
    let run = run_verus(&tc, &frozen, &options(), VerusMode::VerifyAndCompile, &dir.join("build")).unwrap();
    assert_eq!(run.outcome, VerusOutcome::ProofFailure, "{}\n{}", run.detail, run.stderr);
    assert_eq!(run.outcome.failure_class(), Some("proof_failure"));
    assert!(run.artifact.is_none() && !dir.join("build/libgendb_fixture.so").exists());
    let d = run.diagnostics.iter().find(|d| d.level == "error").unwrap();
    assert_eq!(d.message, "postcondition not satisfied");
    assert!(d.file.as_deref().unwrap().ends_with("src/agent/mod.rs") && d.line.is_some());
    println!("{}", run.rendered_errors());
}

/// Publish `run`'s build (as qualification does) and ask admission whether it is evidence.
fn admission_verdict(tc: &VerusToolchain, dir: &Path, frozen: &FrozenCrate, run: &VerusRun) -> Result<(), String> {
    use gendb_artifacts::verus::{check_build_evidence, publish_build, VerusBuildInput, VerusBuildPurposeV1, VerusSourceOwnerV1, VerusTcbV1, VERUS_TCB_KIND};
    let store = gendb_artifacts::ObjectStore::open(dir.join("library")).unwrap();
    let tcb = store.put(1, VERUS_TCB_KIND, &VerusTcbV1 { items: vec![], refusal_rules: serde_json::json!([]) }).unwrap();
    let owned = |files: &[String], owner| files.iter().map(|f| (f.clone(), owner)).collect::<Vec<_>>();
    let mut sources = owned(&frozen.framework_files, VerusSourceOwnerV1::Framework);
    sources.extend(owned(&frozen.author_files, VerusSourceOwnerV1::Agent));
    let build = publish_build(&store, VerusBuildInput {
        purpose: VerusBuildPurposeV1::Candidate,
        provider_identity: tc.version().unwrap().to_string(),
        argv: run.invocation.args.clone(),
        environment: run.invocation.env.clone(),
        exit_code: run.exit_code,
        stdout: &run.stdout,
        frozen_directory: &frozen.root,
        sources,
        library_path: run.artifact.as_deref().unwrap(),
        wall_ns: run.wall_ns,
        tcb,
    })
    .unwrap();
    check_build_evidence(&store, build).map(|_| ()).map_err(|e| e.to_string())
}

/// The diagnostic `--no-verify` build: an unproved crate compiles into a working library that admission refuses as
/// evidence (the verified build of the correct crate is accepted by the same check), compiler errors are still named
/// refusals, and whether `--no-cheating` still refuses `assume` without verification is recorded.
#[test]
#[ignore = "requires the pinned Verus installation"]
fn unverified_compile_skips_proofs_but_not_compiler_errors() {
    let tc = VerusToolchain::from_env().unwrap();
    let dir = scratch("unverified");
    let wrong = AGENT_OK.replace("Ok(left + right)", "Ok(right)");
    let frozen = freeze_crate(&author(&dir.join("wrong"), &wrong), &framework(), &dir.join("wrong/verus")).unwrap();
    let run = compile_unverified(&tc, &frozen, &options(), &dir.join("wrong/build")).unwrap();
    assert_eq!(run.outcome, VerusOutcome::CompiledUnverified, "{}\n{}", run.detail, run.stderr);
    assert!(run.invocation.args.iter().any(|a| a == NO_VERIFY) && run.invocation.args.iter().any(|a| a == "--no-cheating"));
    assert_eq!(call_sum(run.artifact.as_ref().unwrap(), &[1, 2, 3, 4]), (0, 7), "the unproved (wrong) code runs: right half only");
    let refused = admission_verdict(&tc, &dir.join("wrong"), &frozen, &run).unwrap_err();
    assert!(refused.contains("--no-verify"), "{refused}");
    println!("unverified: verification summary {:?}; admission: {refused}", run.verification);

    let good = freeze_crate(&author(&dir.join("good"), AGENT_OK), &framework(), &dir.join("good/verus")).unwrap();
    let verified = run_verus(&tc, &good, &options(), VerusMode::VerifyAndCompile, &dir.join("good/build")).unwrap();
    assert_eq!(verified.outcome, VerusOutcome::Compiled, "{}", verified.detail);
    admission_verdict(&tc, &dir.join("good"), &good, &verified).expect("the verified build is evidence");

    let typed = AGENT_OK.replace("Ok(left + right)", "Ok(true)");
    let frozen = freeze_crate(&author(&dir.join("typed"), &typed), &framework(), &dir.join("typed/verus")).unwrap();
    let run = compile_unverified(&tc, &frozen, &options(), &dir.join("typed/build")).unwrap();
    assert_eq!(run.outcome, VerusOutcome::Rejected, "{}\n{}", run.detail, run.stderr);
    assert!(run.artifact.is_none());
    println!("type error: {}", run.detail);

    let cheat = AGENT_OK.replace("let mid = v.len() / 2;", "proof { assume(false); } let mid = v.len() / 2;");
    let frozen = freeze_crate(&author(&dir.join("assume"), &cheat), &framework(), &dir.join("assume/verus")).unwrap();
    let run = compile_unverified(&tc, &frozen, &options(), &dir.join("assume/build")).unwrap();
    assert!(matches!(run.outcome, VerusOutcome::Rejected | VerusOutcome::CompiledUnverified), "{:?}: {}\n{}", run.outcome, run.detail, run.stderr);
    println!("assume under --no-verify --no-cheating: {:?}: {}", run.outcome, run.detail);
}

#[test]
#[ignore = "requires the pinned Verus installation"]
fn no_cheating_rejects_assume() {
    let tc = VerusToolchain::from_env().unwrap();
    let dir = scratch("assume");
    let cheat = AGENT_OK.replace("let mid = v.len() / 2;", "proof { assume(false); } let mid = v.len() / 2;");
    let frozen = freeze_crate(&author(&dir, &cheat), &framework(), &dir.join("verus")).unwrap();
    let run = run_verus(&tc, &frozen, &options(), VerusMode::VerifyAndCompile, &dir.join("build")).unwrap();
    assert_eq!(run.outcome, VerusOutcome::Rejected, "{}\n{}", run.detail, run.stderr);
    assert!(run.detail.contains("not allowed with --no-cheating"), "{}", run.detail);
    assert_eq!(run.outcome.failure_class(), Some("refusal"));
    assert!(run.artifact.is_none());
}

#[test]
fn refusal_list_runs_before_verus() {
    let dir = scratch("refused");
    let cases = [
        ("cfg", AGENT_OK.replace("pub fn sum_two", "#[cfg(verus_keep_ghost_body)]\npub fn sum_two"), rule::ATTRIBUTE),
        ("loop", AGENT_OK.replace("    while i < hi", "    #[verifier::assume_termination]\n    while i < hi"), rule::VERIFIER_ATTRIBUTE),
        ("drop", format!("{AGENT_OK}\nimpl Drop for Worker {{ fn drop(&mut self) {{}} }}\n"), rule::OUTSIDE_VERUS),
        ("thread", AGENT_OK.replace("spawn_worker(move", "vstd::thread::spawn(move"), rule::DIRECT_THREAD),
        // A method added to a framework type, and a macro that names the crate, directly or through a supported name.
        ("foreign-impl", AGENT_OK.replace("pub open spec fn sum_spec", &(OWN_IMPLS.replace("impl Local {", "impl<T> crate::gendb_workers::Worker<T> {") + "pub open spec fn sum_spec")), rule::IMPL_OWNERSHIP),
        ("module-path", AGENT_OK.replace("let mid = v.len() / 2;", "let mid = v.len() / 2; let _here = module_path!();"), rule::MACRO),
        ("macro-alias", format!("use std::module_path as seq;\n{AGENT_OK}"), rule::MACRO_IMPORT),
        // Trait objects and vstd's rwlock escape the termination checks; the termination probes are refused whole.
        ("dyn", AGENT_OK.replace("pub open spec fn sum_spec", "pub trait Step { fn step(&self) -> u64; }\npub fn via(s: &dyn Step) -> u64 { s.step() }\npub open spec fn sum_spec"), rule::DYN_TRAIT_OBJECT),
        ("rwlock", format!("use vstd::rwlock::RwLock;\n{AGENT_OK}"), rule::VSTD_RWLOCK),
        ("probe-h5b", include_str!("fixtures/verus_termination/h5b-dyn-recursion-false-ensures.rs").into(), rule::DYN_TRAIT_OBJECT),
        ("probe-i5", include_str!("fixtures/verus_termination/i5-proof-recursion-through-dyn.rs").into(), rule::DYN_TRAIT_OBJECT),
        ("probe-k1", include_str!("fixtures/verus_termination/k1-dyn-false-wrong-answer.rs").into(), rule::DYN_TRAIT_OBJECT),
        ("probe-h7", include_str!("fixtures/verus_termination/h7-rwlock-double-acquire.rs").into(), rule::VSTD_RWLOCK),
    ];
    for (name, text, rule) in cases {
        let case = dir.join(name);
        std::fs::create_dir_all(&case).unwrap();
        match freeze_crate(&author(&case, &text), &framework(), &case.join("verus")) {
            Err(FreezeError::Refused { findings }) => {
                assert!(findings.iter().any(|f| f.rule == rule && f.file == "mod.rs" && f.line > 0), "{name}: {findings:?}")
            }
            other => panic!("{name}: expected refusal, got {other:?}"),
        }
        // The refused snapshot is kept, read-only.
        assert!(case.join("verus/src/agent/mod.rs").exists());
    }
    // The author's own types, methods, trait implementations and traits are accepted.
    let case = dir.join("own-impls");
    let own = AGENT_OK.replace("pub open spec fn sum_spec", &format!("{OWN_IMPLS}pub open spec fn sum_spec"));
    freeze_crate(&author(&case, &own), &framework(), &case.join("verus")).unwrap();
    // A symlink in the author directory is refused by the file-set rule.
    let case = dir.join("symlink");
    let agent = author(&case, AGENT_OK);
    std::os::unix::fs::symlink("/etc/hostname", agent.join("data.rs")).unwrap();
    match freeze_crate(&agent, &framework(), &case.join("verus")) {
        Err(FreezeError::Refused { findings }) => assert!(findings.iter().any(|f| f.rule == rule::FILE_SET && f.file == "data.rs")),
        other => panic!("expected refusal, got {other:?}"),
    }
}
