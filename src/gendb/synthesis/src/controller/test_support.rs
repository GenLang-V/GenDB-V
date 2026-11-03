//! Test fixtures of the controller: a scripted author transport, a scripted role and its policy. No provider process
//! or data is involved.

use super::author::{AuthorCall, AuthorTransport, CandidateSubmission, Capability, ProviderCondition};
use super::ledger::{Call, Receipt, Tokens, Trial, UsageScope};
use super::limits::Money;
use super::records;
use super::role::{PromptInput, QualificationAttempt, RolePolicy, SynthesisRole};
use super::run::{RunRequest, StopReason};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

/// A fresh scratch directory path under `TMPDIR` (a scratch directory, never the system `/tmp`).
pub fn scratch_root(name: &str) -> PathBuf {
    let tmp = std::env::var_os("TMPDIR").expect("TMPDIR must name a scratch directory");
    PathBuf::from(tmp).join(format!("r11-{name}-{}", records::random_uuid().unwrap()))
}

pub fn submission() -> Value {
    json!(CandidateSubmission {
        candidate_manifest: "candidate.json".into(),
        rationale: "revision".into(),
        data_access_analysis: "reuse retained columns".into(),
    })
}

/// A receipt as the fixture provider reports it.
pub fn receipt(call: &Call, session: &str, cost: Option<&str>) -> Receipt {
    Receipt {
        call_id: call.id,
        session_id: session.into(),
        ended_unix_ms: records::now_unix_ms(),
        elapsed_ms: 1,
        reported_cost_usd: cost.map(|c| Money::parse(c).unwrap()),
        billed_cost_usd: None,
        tokens: None,
        outcome: "error".into(),
        raw_result: None,
        output: None,
        usage_scope: None,
    }
}

/// Scripted author transport.
pub struct FixtureAuthor {
    /// Provider invocations (refusals before launch are not counted).
    pub calls: u32,
    pub resumes: Vec<bool>,
    pub prompts: Vec<String>,
    /// Provider-reported cost of each successful call.
    pub cost: &'static str,
    /// `preflight` succeeds.
    pub ready: bool,
    /// Refuse every call before launch, with a zero-usage transport refusal.
    pub refuse: bool,
    /// Prove non-dispatch of calls whose directory has no `invocation.json`.
    pub prove: bool,
    /// Report the terminal result's cost only in `raw_result` (no recorded cost or tokens); `None` = no cost at all.
    pub raw_cost_only: Option<Option<&'static str>>,
    /// Scripted provider calls, one per invocation in order: a condition ends the call with a provider error and no
    /// output; `None` (or past the end) is an ordinary submission. A non-empty script makes every receipt report
    /// session-scoped totals (`cost` per invocation, accumulated per provider session) and leave the provider result
    /// record, so its session can be resumed.
    pub script: Vec<Option<ProviderCondition>>,
    /// The condition each scripted call ended with, by call id (`provider_condition`).
    pub conditions: BTreeMap<u64, ProviderCondition>,
    /// The deadlines the controller waited for (`wait_for_provider`; the fixture never sleeps).
    pub waits: Vec<u64>,
    /// The provider session of each invocation.
    pub sessions: Vec<String>,
    /// The session-scoped total reported so far per provider session (scripted calls).
    pub session_totals: BTreeMap<String, Money>,
    /// A render-only transport (`AuthorTransport::render_only`).
    pub render_only: bool,
}

impl Default for FixtureAuthor {
    fn default() -> Self {
        Self {
            calls: 0,
            resumes: vec![],
            prompts: vec![],
            cost: "0.1",
            ready: true,
            refuse: false,
            prove: false,
            raw_cost_only: None,
            script: vec![],
            conditions: BTreeMap::new(),
            waits: vec![],
            sessions: vec![],
            session_totals: BTreeMap::new(),
            render_only: false,
        }
    }
}

impl AuthorTransport for FixtureAuthor {
    fn render_only(&self) -> bool {
        self.render_only
    }

    /// A call left a provider result record: its provider session exists.
    fn provider_session_exists(&self, call_dir: &Path) -> bool {
        call_dir.join("fixture-terminal-result.json").is_file()
    }

    fn capability(&self) -> Capability {
        Capability {
            transport: "fixture".into(),
            executable: "fixture".into(),
            version: "1".into(),
            model: "claude-opus-5-5".into(),
            effort: "high".into(),
            persistent_sessions: true,
            hard_usd_cap: false,
            cost_semantics: "fixture".into(),
        }
    }

    fn preflight(&mut self) -> Result<(), String> {
        if self.ready { Ok(()) } else { Err("fixture adapter unavailable".into()) }
    }

    fn definitely_not_dispatched(&self, call_dir: &Path) -> Result<bool, String> {
        Ok(self.prove && !call_dir.join("invocation.json").exists())
    }

    fn invoke(&mut self, request: &AuthorCall) -> Receipt {
        let call = request.call;
        if self.refuse {
            let mut refusal = receipt(call, request.session_id, Some("0"));
            refusal.elapsed_ms = 0;
            refusal.outcome = "activity_lock_refusal:fixture uninspected adapter".into();
            return refusal;
        }
        self.calls += 1;
        self.resumes.push(request.resume);
        self.prompts.push(request.prompt.to_string());
        self.sessions.push(request.session_id.to_string());
        let mut settled = receipt(call, request.session_id, Some(self.cost));
        settled.elapsed_ms = 2;
        settled.tokens = Some(Tokens::default());
        settled.outcome = "success".into();
        settled.raw_result = Some(json!({"session_id":request.session_id}));
        settled.output = Some(submission());
        if !self.script.is_empty() {
            let condition = self.script.get(self.calls as usize - 1).cloned().flatten();
            let total = self.session_totals.entry(request.session_id.to_string()).or_default();
            *total = total.checked_sum(Money::parse(self.cost).unwrap()).unwrap();
            let raw = json!({"session_id":request.session_id,"total_cost_usd":total.decimal(),"is_error":condition.is_some()});
            fs::write(request.call_dir.join("fixture-terminal-result.json"), raw.to_string()).unwrap();
            settled.reported_cost_usd = None;
            settled.usage_scope = Some(UsageScope::Session);
            settled.raw_result = Some(raw);
            if let Some(condition) = condition {
                settled.outcome = "provider_error: fixture".into();
                settled.output = None;
                self.conditions.insert(call.id, condition);
            }
            return settled;
        }
        if let Some(raw_cost) = self.raw_cost_only {
            settled.reported_cost_usd = None;
            settled.tokens = None;
            settled.raw_result = Some(match raw_cost {
                Some(cost) => json!({"session_id":request.session_id,"total_cost_usd":cost}),
                None => json!({"session_id":request.session_id}),
            });
        }
        settled
    }

    fn provider_condition(&self, _call_dir: &Path, receipt: &Receipt) -> Option<ProviderCondition> {
        self.conditions.get(&receipt.call_id).cloned()
    }

    fn wait_for_provider(&mut self, until_unix_ms: u64) {
        self.waits.push(until_unix_ms);
    }

    /// The fixture transport's durable record of a lost call is `fixture-terminal-result.json` (a provider terminal
    /// result); without it usage cannot be established.
    fn recover_receipt(&self, call: &Call, session_id: &str, call_dir: &Path, _workspace: &Path) -> Result<Option<Receipt>, String> {
        let path = call_dir.join("fixture-terminal-result.json");
        if !path.is_file() {
            return Ok(None);
        }
        let raw: Value = serde_json::from_slice(&fs::read(&path).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
        if raw["session_id"].as_str() != Some(session_id) {
            return Ok(None);
        }
        let mut recovered = receipt(call, session_id, None);
        recovered.elapsed_ms = raw["duration_ms"].as_u64().unwrap_or(0);
        recovered.outcome = format!("controller_loss_recovery: {}", raw["subtype"].as_str().unwrap_or("unknown"));
        recovered.usage_scope = raw["usage_scope"].as_str().map(|_| UsageScope::Session);
        recovered.raw_result = Some(raw);
        Ok(Some(recovered))
    }
}

/// Scripted role decisions.
#[derive(Clone, Default)]
pub struct FixturePolicy {
    pub stop_at_first_eligible: bool,
    /// Reevaluate an evaluation refused with "fixture archive transport refused" (revision `fixture-transport-v2`).
    pub repair: bool,
    /// Objective: some eligible exact median below this many nanoseconds.
    pub objective_below_ns: Option<u64>,
}

impl RolePolicy for FixturePolicy {
    /// The fixture prompt is the JSON of its inputs, so tests can read what the controller supplied.
    fn author_prompt(&self, input: &PromptInput) -> String {
        json!({"iteration":input.iteration,"ledger":input.ledger,"feedback":input.feedback,"context":input.context,"handoff":input.handoff}).to_string()
    }

    fn objective_status(&self, context: &Value, trials: &[Trial]) -> Value {
        let Some(target) = self.objective_below_ns else {
            return json!({"status":"not_configured","context":context["contract"]});
        };
        let met = trials.iter().filter(|trial| trial.eligible()).flat_map(Trial::medians).any(|(_, _, ns)| ns < target);
        json!({"status":if met {"met"} else {"unmet"},"target_ns":target})
    }

    fn search_stop(&self, _context: &Value, trials: &[Trial]) -> Option<StopReason> {
        (self.stop_at_first_eligible && trials.iter().any(Trial::eligible)).then_some(StopReason::FirstEligibleCandidate)
    }

    fn repair_revision(&self, evaluation: &Value) -> Option<&'static str> {
        (self.repair && evaluation["error"] == "fixture archive transport refused").then_some("fixture-transport-v2")
    }
}

/// Scripted role stages.
#[derive(Default)]
pub struct FixtureRole {
    pub policy: FixturePolicy,
    pub prepared: u32,
    pub evaluated: u32,
    pub qualified: u32,
    pub fail_prepare: bool,
    pub fail_freeze: bool,
    /// The first this-many evaluations are ineligible.
    pub reject_evaluations: u32,
    /// The first this-many evaluations fail in the framework (`tool_failure`).
    pub framework_failures: u32,
    /// Every submission freezes the same captured module source.
    pub unchanged_module: bool,
    /// Eligible evaluations report one exact measurement with this median.
    pub median_ns: Option<u64>,
    /// The policy excludes recorded evaluations with these scores (`policy_exclusion`).
    pub excluded_scores: Vec<u64>,
    /// Frozen candidates imported from another session (`import_frozen`).
    pub imports: u32,
    /// `close` fails (a controller stopped before its closure).
    pub fail_close: bool,
    /// When non-empty, the n-th evaluation (from 1) is eligible with the n-th score (`median_ns` and the rules above
    /// are then not used).
    pub scores: Vec<u64>,
    /// Incumbents written into the workspace (`seed_incumbent`).
    pub seeded: u32,
}

impl SynthesisRole for FixtureRole {
    type Policy = FixturePolicy;

    fn policy(&self) -> FixturePolicy {
        self.policy.clone()
    }

    async fn prepare(&mut self, _: &RunRequest, _: &Path) -> Result<Value, String> {
        self.prepared += 1;
        if self.fail_prepare { Err("fixture preparation failed".into()) } else { Ok(json!({"contract":"fixture"})) }
    }

    async fn freeze(&mut self, _: &Path, frozen_dir: &Path, _: &CandidateSubmission) -> Result<Value, String> {
        if self.fail_freeze {
            return Err("invalid candidate manifest".into());
        }
        fs::create_dir_all(frozen_dir).map_err(|e| e.to_string())?;
        if !self.unchanged_module {
            return Ok(json!({"frozen":true}));
        }
        let source = frozen_dir.join("module-0.rs");
        fs::write(&source, "module-body").map_err(|e| e.to_string())?;
        Ok(json!({"modules":[{"source":source,"items":["query"]}],"representation":{"name":"identity"}}))
    }

    async fn evaluate(&mut self, _: &Path, _: &Value) -> Result<Value, String> {
        self.evaluated += 1;
        if let Some(score) = self.scores.get(self.evaluated as usize - 1) {
            return Ok(json!({"eligible":true,"score_ns":score,"status":"diagnostic_exact"}));
        }
        if self.evaluated <= self.framework_failures {
            return Ok(json!({"eligible":false,"status":"tool_failure","failure_class":"tool_failure","error":"tool_failure: fixture"}));
        }
        if self.evaluated <= self.reject_evaluations {
            return Ok(json!({"eligible":false,"error":"fixture design refused"}));
        }
        Ok(match self.median_ns {
            Some(median) => json!({"eligible":true,"score_ns":median,"status":"diagnostic_exact",
                "measurements":[{"workers":1,"status":"exact","median_ns":median,"samples_ns":[1,2,3]}]}),
            None => json!({"eligible":true,"score_ns":100 / self.evaluated}),
        })
    }

    async fn qualify(&mut self, _: &Path, _: &Value) -> Result<Value, String> {
        self.qualified += 1;
        Ok(json!({"qualified":true}))
    }

    async fn close(&mut self, _: &[Trial], qualification: &[QualificationAttempt]) -> Result<Value, String> {
        if self.fail_close {
            return Err("fixture close failed".into());
        }
        Ok(json!({"selected":!qualification.is_empty()}))
    }

    async fn policy_exclusion(&mut self, evaluation: &Value) -> Result<Option<String>, String> {
        let excluded = evaluation["score_ns"].as_u64().is_some_and(|score| self.excluded_scores.contains(&score));
        Ok(excluded.then(|| "storage_policy_excluded: fixture exclusion".to_string()))
    }

    /// Writes a marker into the workspace; the source's recorded evaluation is `<source>/evaluation.json`.
    async fn seed_incumbent(&mut self, source: &Path, workspace: &Path) -> Result<crate::controller::SeededIncumbent, String> {
        self.seeded += 1;
        fs::create_dir_all(workspace).map_err(|e| e.to_string())?;
        fs::write(workspace.join("incumbent-manifest.json"), "{}").map_err(|e| e.to_string())?;
        Ok(crate::controller::SeededIncumbent {
            submission: CandidateSubmission { candidate_manifest: "incumbent-manifest.json".into(), rationale: "earlier".into(), data_access_analysis: "earlier".into() },
            source_evaluation: source.join("evaluation.json"),
            provenance: json!({"source_session":source,"source_iteration":1}),
        })
    }

    /// Copies the source's frozen files (the fixture freeze writes `module-0.rs` at most) and names the source.
    async fn import_frozen(&mut self, source: &Path, frozen_dir: &Path) -> Result<Value, String> {
        self.imports += 1;
        fs::create_dir(frozen_dir).map_err(|e| e.to_string())?;
        for entry in fs::read_dir(source).map_err(|e| e.to_string())? {
            let path = entry.map_err(|e| e.to_string())?.path();
            fs::copy(&path, frozen_dir.join(path.file_name().unwrap())).map_err(|e| e.to_string())?;
        }
        Ok(json!({"frozen":true,"imported_from":source}))
    }
}
