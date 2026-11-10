//! The fixed Markdown sections of the general engine line's prompt, assembled by `prompts::engine_policy::general_author_prompt` with the call's
//! data sections (`prompts::engine_facts::general`).
//!
//! Order: goal (build the fastest verified engine as soon as possible, and the score that decides), the request's main
//! direction when it sets one, how to work (work fast, global view, freedom, sub-agents), what is fixed with the line's
//! rules, storage with the budget rule and the `physical_only` policy, the interpreter as fallback, design and proofs
//! (with the design space map, information only), the loop, inputs, tools, the submission and the processes appendix.
//! Every rule is stated once, where a reader looks for it; other sections point to it by the section's name. Pure
//! reference detail is in contract files the texts name (`storage-authoring.md`, `task.json` `fixed_files`).
//!
//! The texts teach the framework in plain words: no worked example, no threshold for the author's choices, and no name
//! of a query, template, table or column (a unit test checks the TPC-H and SEC-EDGAR names, the storage policy included). The general
//! line keeps its own copies of the texts it shares in meaning
//! with the other lines (the storage policy, proof, reuse, parallelism and check-economy advice, the processes
//! appendix), so the schema and per-query lines render as before.
//!
//! A request's `engine.emphasis` (`controller::request::EngineEmphasis`) adds one section after the
//! goal that makes a direction the main one from the first version ([`emphasis_section`]: `co_optimization`, data and
//! query co-optimization); without it the section is absent and every other section is the same.
//!
//! Two shapes of the run ([`Shape`]): **one line** (one branch: every version builds on the best
//! version, and nothing is said of branches, other branches' directions, merges or rebases), or **branches** (the
//! island model, kept for runs with several branches). Numbers that are facts of the run are
//! placeholders the policy fills from the context: `@CALL_LIMIT@`, `@MEMORY_LIMIT@`, `@BRANCHES@`, `@VARIANT_KINDS@`.
//!
//! Two kinds of run by workloads ([`Workloads`]): **one workload** (every text as before), or a **stage run** (one
//! engine for a goal workload and kept workloads, the context's `general.stage`). A
//! stage run adds the section Stage 2 after the goal and the main direction ([`GENERAL_STAGE`]) and changes four texts:
//! the goal (the goal workload's score; one scale per workload), what is fixed (ownership of the workload modules, one
//! crate per workload, the rules over every workload with the one-word name rule and rule 8 on workload modules), and
//! the loop (the evaluation's order; no scale move). Its workload names are the placeholders
//! `@GOAL_WORKLOAD@` and `@KEPT_WORKLOADS@`. The fixed texts name no table, column or template of either workload (unit
//! test, TPC-H and SEC-EDGAR names).
//!
//! A run of `engine.workloads` ([`Workloads::Set`]: one engine, general for any
//! schema, data and query of SQLSpec, tuned for the counted workloads; the context's `general.workloads`) adds the
//! section One engine for every workload in Stage 2's place ([`GENERAL_WORKLOADS`]): every counted workload decides
//! through the combined score, the check workloads must verify and answer, the root's sides, one crate per workload,
//! storage families, the default module and plans, the user's transition, storage, inputs and tools per workload and
//! the global view. It changes the goal (the combined score; one scale per workload), what is fixed (ownership of the
//! default module, families and plans; rules 8 to 12) and the loop (the evaluation's order; no
//! scale move). Its workload names are placeholders too (`@PRIMARY_WORKLOAD@`,
//! `@COUNTED_WORKLOADS@`, `@CHECK_WORKLOADS@`, `@KEPT_MEMBERS@`); the fixed texts also name no table, column or template
//! of the check fixture `anyschema` (unit test). When the request accepts only versions that are one engine
//! (`engine.workloads.require_one_engine`, the context's `general.require_one_engine`), that section states the rule in
//! one paragraph after its opening ([`GENERAL_ONE_ENGINE_RULE`]); without it the section is as before.

/// Whether the run serves one workload, or several with one engine (a stage run: the context's
/// `general.stage`; a run of `engine.workloads`: the context's `general.workloads`), which decides the
/// texts about workloads, crates, storage families and the order of a submission's evaluation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Workloads {
    /// One workload: the texts as before stage runs.
    One,
    /// A stage run: one engine for a goal workload, whose score decides every submission, and kept workloads, which are
    /// verified, timed against the parent and shown, never deciding. Its texts name the workloads by the placeholders
    /// `@GOAL_WORKLOAD@` and `@KEPT_WORKLOADS@`, which the policy fills from the context.
    Stage,
    /// A run of `engine.workloads`: one engine for several workloads, each with a
    /// role: counted (its score is part of the combined score that decides every submission), check (verified and
    /// answered by every submission, never timed) or kept (timed and shown, never deciding); one crate per workload,
    /// storage families, the default module and plans. Its texts name the workloads by the placeholders
    /// `@PRIMARY_WORKLOAD@`, `@COUNTED_WORKLOADS@`, `@CHECK_WORKLOADS@` and `@KEPT_MEMBERS@`, which the policy fills
    /// from the context's workloads view ([`workloads_of`]).
    Set,
}

impl Workloads {
    /// The workloads of the run of a session's prepared context.
    pub fn of_context(context: &serde_json::Value) -> Self {
        if workloads_of(context).is_some() {
            Workloads::Set
        } else if stage_of(context).is_some() {
            Workloads::Stage
        } else {
            Workloads::One
        }
    }
}

/// The workloads view of a session's context in a run of `engine.workloads` (the workloads fixture,
/// `prompts::engine_facts::general::workloads`): the copy refreshed before each call (top-level `workloads`), else the
/// one the session was prepared with (`general.workloads`); `None` for every other run.
pub fn workloads_of(context: &serde_json::Value) -> Option<&serde_json::Value> {
    [&context["workloads"], &context["general"]["workloads"]].into_iter().find(|workloads| workloads.as_array().is_some_and(|w| !w.is_empty()))
}

/// The stage view of a session's context (the stage fixture, `prompts::engine_facts::general::stage`): the copy refreshed
/// before each call (`stage`), else the one the session was prepared with (`general.stage`); `None` for a run with one
/// workload.
pub fn stage_of(context: &serde_json::Value) -> Option<&serde_json::Value> {
    [&context["stage"], &context["general"]["stage"]].into_iter().find(|stage| stage.is_object())
}

/// The shape of a general-line run, which decides the texts about versions and branches.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shape {
    /// One branch: one line of versions, each built on the best version so far (the head).
    OneLine,
    /// Several branches (island model): branch heads, a main-line head, directions and merges.
    Branches,
}

impl Shape {
    /// The shape of a run with `branches` branch slots.
    pub fn of_branches(branches: usize) -> Self {
        if branches <= 1 { Shape::OneLine } else { Shape::Branches }
    }

    /// The shape of the run of a session's prepared context (`context.general.branches`: its branch slots).
    pub fn of_context(context: &serde_json::Value) -> Self {
        Self::of_branches(context["general"]["branches"].as_array().map_or(1, Vec::len))
    }

    /// How the texts name the best version: the head of the one line, or the main-line head over all branches.
    pub fn head(self) -> &'static str {
        match self {
            Shape::OneLine => "head",
            Shape::Branches => "main-line head",
        }
    }
}

/// The contract file with the reference detail of adding a storage (`prompts::engine_contract::general`).
pub const STORAGE_AUTHORING_FILE: &str = "storage-authoring.md";

/// GOAL: build the fastest verified engine as soon as possible; first finish every template, then cut the total time;
/// the score that decides every submission; the scale ladder (a stage run or a run of several workloads: one scale per
/// workload) and the run's end. In a stage run the goal and the score are the goal workload's; in a run of several
/// workloads ([`Workloads::Set`]) every counted workload's, summed in the combined score.
pub fn goal(shape: Shape, workloads: Workloads) -> String {
    let budget = match shape {
        Shape::OneLine => "the run's budget (provider-reported dollars)",
        Shape::Branches => "the run's budget (provider-reported dollars, shared by all branches)",
    };
    const ONE_SCORE: &str = "decides every submission (`performance.json`): F = the finished cells; G = the sum over the worker counts of your total / the faster baseline's total, an unfinished cell counting as the call limit. Better means a larger F, or the same F and a smaller G; G below 1 at a worker count beats the faster baseline there.";
    const ONE_SCALE_PER_WORKLOAD: &str = "**One scale per workload.** Each workload stays at its scale for the whole run (CURRENT FACTS, Workloads). Beating both baselines is a milestone";
    let (engine, templates, cells, total, score, scales) = match workloads {
        Workloads::One => (
            "",
            "the training templates",
            "At the current scale every cell",
            "At each worker count, bring your total (the sum of your cell times over the templates)",
            format!("**The score** {ONE_SCORE}"),
            format!("**The scale ladder.** The run starts at the first scale of its ladder and moves to the next when the {} finishes every cell at the current scale (CURRENT FACTS, Scale). Beating both baselines at a scale is a milestone", shape.head()),
        ),
        Workloads::Stage => (
            "",
            "the training templates of the goal workload @GOAL_WORKLOAD@",
            "On the goal workload, at its scale, every cell",
            "At each worker count, bring your total (the sum of your cell times over the templates)",
            format!("**The goal workload's score** {ONE_SCORE}"),
            ONE_SCALE_PER_WORKLOAD.to_string(),
        ),
        Workloads::Set => (
            " one engine for every workload of this run,",
            "the training templates of every counted workload (@COUNTED_WORKLOADS@)",
            "On every counted workload, at its scale, every cell",
            "On every counted workload and at each worker count, bring your total (the sum of your cell times over its templates)",
            "**The combined score** decides every submission (`performance.json`): per counted workload, F = its finished cells and G = the sum over its worker counts of your total / the faster baseline's total, an unfinished cell counting as the call limit; the combined F and G are the sums over the counted workloads. Better means a larger combined F, or the same F and a smaller combined G; a workload's ratio below 1 at a worker count beats the faster baseline there. A gain on one workload can outweigh a loss on another; every timing is shown per workload (CURRENT FACTS, Workloads).".to_string(),
            ONE_SCALE_PER_WORKLOAD.to_string(),
        ),
    };
    format!(
        r#"# Goal

**Build the fastest verified engine, as soon as possible:**{engine} faster than the best state-of-the-art engines, DuckDB and Umbra, on {templates} at every worker count.

1. **Finish every template.** {cells} (one template at one worker count) must finish: each of its calls ends within the call limit (@CALL_LIMIT@) and its answers agree with the saved answers.
2. **Then cut the total time.** {total} below the faster baseline's total, then as far below it as you can.
3. {score}
4. {scales}, not a stop: the work goes on until {budget} is used or the user stops the run."#
    )
}

/// MAIN DIRECTION: data and query co-optimization from the first version (request `engine.emphasis:
/// "co_optimization"`). It says where to put the work; what the Storage section states (the
/// budget and what follows from it, the rebuild at each scale) is not repeated, and it does not say how to split the
/// work across sub-agents (that is the lead's choice, How to work).
pub const GENERAL_CO_OPTIMIZATION: &str = r#"# Main direction: data and query co-optimization

This run makes data and query co-optimization (Storage) the main direction, from the first version. It says where to put the work; the goal, the rules, the storage policy and the loop are unchanged.

1. **Design the data and the queries together:** the storage layout, the column access layer and the operators as one design. Choose the encodings (narrow integers, dictionary codes for text, compact offsets), the sort order, the clustering and the skipping metadata together with the algorithms that read them.
2. **Build the access layer for encoded columns from the start.** Your operators then work on the encoded data, not on a plain copy of it; operators written first for the plain columns would have to be written again.
3. **The first storage change must compress** (the budget, Storage). Re-encoding the largest table alone can be enough."#;

/// A CONTINUED ENGINE (request `engine.seed_version`: the engine evolves over time; the proof gives
/// every supported query its answer, the agents add speed for new patterns): this run's root is another run's version,
/// its training set adds templates that engine was not built for, and the user's rule for the others. The seed, its
/// templates and the new ones are the context's (`general.seed`, filled by `engine_policy`), so the text names none.
pub const GENERAL_CONTINUED: &str = r#"# A continued engine

This run continues the engine of an earlier run. Its root `v000` is version @SEED_VERSION@ of the run `@SEED_RUN@`: that version's code, storages and notebook (`NOTES.md`), verified whole and timed alone again here (the earlier run's records are not inputs). Unlike the ladder in the Goal, this run starts and stays at the last scale of its ladder; its first scale only checks the variants.

- **Built for:** @SEED_TEMPLATES@. **New to it:** @NEW_TEMPLATES@. The engine already answers the new ones correctly (every version is verified for every supported query), but its fast paths were built for the shapes of the others.
- **Make the new templates fast** with general techniques: what speeds them up should also serve future queries of similar shapes, never one statement. CURRENT FACTS shows `v000`'s cells and profile for every template.
- **Keep what it was built for.** The score counts every template; the user asks that the engine not lose its performance on the templates it was built for.
- **Baselines.** A template that Umbra did not time has DuckDB's saved time as its baseline (`files.templates`); Umbra's total then does not exist, and DuckDB's total is the target at every worker count (CURRENT FACTS, Score)."#;

/// The section of a continued run ([`GENERAL_CONTINUED`]) when the session's context has `general.seed`; `None`
/// otherwise, and the section is then absent.
pub fn continued_section(context: &serde_json::Value) -> Option<&'static str> {
    context["general"]["seed"].is_object().then_some(GENERAL_CONTINUED)
}

/// The section of the request's `engine.emphasis` as a session's context carries it (`general.emphasis`), placed after
/// the goal; `None` when the request sets none (or an unknown value), and the section is then absent.
pub fn emphasis_section(context: &serde_json::Value) -> Option<&'static str> {
    use crate::controller::request::EngineEmphasis;
    match context["general"]["emphasis"].as_str() {
        Some(name) if name == EngineEmphasis::CoOptimization.name() => Some(GENERAL_CO_OPTIMIZATION),
        _ => None,
    }
}

/// STAGE 2: in a stage run,
/// after the goal and the main direction, what the second workload changes: the goal workload decides, the kept
/// workloads are verified, timed and shown; the out-of-the-box record; one crate per workload with its module; general
/// code with a small plan per workload (the user's direction: storage code serves any supported schema and data, a new workload
/// needs a new plan, not new code; the head's storage code written for the kept workload's tables is replaced by general
/// code and a plan); storage, inputs and tools per workload; the global view across workloads. The evaluation's order
/// is in the loop ([`the_loop`]), the rules in What is fixed ([`fixed`]).
pub const GENERAL_STAGE: &str = r#"# Stage 2: a second workload

This run is the second stage of one engine. The version it starts from was built for @KEPT_WORKLOADS@; the same engine now also serves @GOAL_WORKLOAD@.

- **The goal: make the same engine fast on @GOAL_WORKLOAD@.** Its score decides every submission (Goal).
- **Keep @KEPT_WORKLOADS@.** Every submission must verify, and agree with the saved answers, on every workload. A kept workload is timed against the parent for every accepted version and shown (CURRENT FACTS, Workloads), but it does not decide. The user asks that the engine not lose its performance there. How a submission is evaluated across workloads: The loop.
- **Out of the box.** When the run was prepared, GenDB froze, checked and, where it could, timed that version's code on @GOAL_WORKLOAD@: CURRENT FACTS, Out of the box.
- **One engine, one crate per workload.** `src/agent/**` is the engine, shared by every workload. Each workload adds a small module, `workloads/<name>/**`: for workload W, GenDB copies `workloads/W/**` into W's crate as `src/agent/workload/**` at freeze and verifies that crate whole against the same fixed entry, over W's schema, storages and declared constraints. Shared code reaches the module as `crate::agent::workload::…`, so every module offers the same items; rustc checks each crate. Never create `src/agent/workload` in your workspace (refused). Without any `workloads/` directory, `src/agent/**` alone is every workload's crate.
- **General code, small plans.** Query processing and the code that builds and reads storages (layouts, encodings, compression, indexes, metadata) are general: written for any supported schema and data, parameterized by tables, columns and types, never for one benchmark's tables; @GOAL_WORKLOAD@ and @KEPT_WORKLOADS@ are two cases that test it. A workload module holds only its plan (data: which tables and columns get which layout, encoding or index) and the opening of its storages as the engine's tables, with the proofs that needs (rule 8); a new workload should need a new plan, not new code. The storage code the start version wrote for the tables of @KEPT_WORKLOADS@ is to be replaced in this stage by general code and a plan: its storages are then built once by the general builders, and @KEPT_WORKLOADS@ must keep verifying and answering correctly. CURRENT FACTS shows each module's size.
- **Storage per workload.** The manifest lists each workload's uses (`workloads[]`: `{name, storage_uses, modules}`; the top-level `storage_uses` is empty and `modules` lists the shared files; its schema: `task.json` `manifest`). Each workload has its own library, plain storage and budget; coverage, one copy of each column, the policy and the budget rule (Storage) hold per workload, at its scale.
- **Inputs and tools per workload.** Each workload's templates, data, bindings, baselines and budget rule: `files.workloads.<name>`. The tools take `workload` (default: the goal): which crate, data, library and saved answers a job uses. Check a kept workload's crate before you submit: a submission better on the goal that fails on a kept workload is refused.
- **Global view across workloads.** Look for what the workloads share; a technique that speeds up both counts twice."#;

/// The Stage 2 section ([`GENERAL_STAGE`]) when the session's context has a stage view ([`stage_of`]); `None` for a run
/// with one workload, and the section is then absent.
pub fn stage_section(context: &serde_json::Value) -> Option<&'static str> {
    stage_of(context).map(|_| GENERAL_STAGE)
}

/// ONE ENGINE FOR EVERY WORKLOAD: in a run of
/// `engine.workloads`, after the goal and the main direction, in Stage 2's place: the roles; every counted workload
/// decides through the combined score, with the user's keep rule and no guard; the check workloads verify and answer;
/// the root's sides, both verified versions; one crate per workload; storage families, the default module and plans;
/// the user's transition; storage, inputs and tools per workload; the global view. The
/// evaluation's order is in the loop ([`the_loop`]), the rules (8 to 12) in What is fixed ([`fixed`]), the family
/// detail in [`STORAGE_AUTHORING_FILE`].
pub const GENERAL_WORKLOADS: &str = r#"# One engine for every workload

This run builds one engine for several workloads, each with its own schema, data, templates, library and scale. The user's words: "make it one engine, general to support any schema, data, and query supported by SQLSpec", with its performance tuned for the counted workloads; "in the future, it will be open-sourced and I will evolve it for more schemas, workloads, and hardwares". Every workload has a role (CURRENT FACTS, Workloads): counted (@COUNTED_WORKLOADS@), check (@CHECK_WORKLOADS@) and kept (@KEPT_MEMBERS@).

- **Every counted workload decides, through the sum.** Each submission is timed on every counted workload against the parent's side of that workload, and the combined score decides (Goal). The user asks that the engine not lose its performance on any workload. No guard refuses a loss on one workload that a larger gain on another outweighs, but every timing shows each workload.
- **A check workload must verify and answer.** It has a schema and data of its own (GenDB's generality fixture: tiny data over every stored SQLSpec type, nullable and NOT NULL columns, single, composite and text keys, an empty table and an all-NULL column). Every submission verifies its crate whole and answers every template at every visible binding there with the saved answers, before any timing (rule 12); it is never timed and not in the score. Shared code that depends on another workload's schema does not compile, verify or answer there.
- **A kept workload** is verified, timed against the parent's side of that workload and shown for every accepted version, never deciding.
- **The root's sides.** This run's root `v000` has one side per workload, each verified whole and timed alone (a check workload: answered) when the run was prepared (CURRENT FACTS, The root's sides). A workload with a seed gets that seed's code, module and storages; a workload without one gets the primary seed's code where it verifies there, else version 0. Your workspace starts from the side of @PRIMARY_WORKLOAD@, the primary workload, with its notebook. Every other side's code, module, storage author files, notebook and manifest are read-only under `root-sides/<name>/` in your workspace, and the code of the sides' common ancestor under `root-sides/ancestor/` when GenDB found one. Each side is a verified version, so you may start from either; how to merge them (for example with `diff3` against the ancestor) is your choice. Your first workspace holds only the primary's module: until you bring another workload's module over from its side (`root-sides/<name>/code/workloads/`) or move that workload to the default module and families, its crate does not freeze, so merging is the first submission's work. The first submission is judged on each workload against that workload's side.
- **One engine, one crate per workload.** `src/agent/**` is the engine, shared by every workload. At freeze GenDB composes one crate per workload from `src/agent/**`, that workload's module copied in as `src/agent/workload/**` (its own `workloads/<name>/**` where rule 11 allows one, else the default module `workloads/default/**`) and the instances of the storage families it reads, all over that workload's schema, storages and declared constraints; each crate is verified whole against the same fixed entry. Shared code reaches the module as `crate::agent::workload::…`, so every module offers the same items; rustc checks each crate. Never create `src/agent/workload` in your workspace (refused).
- **Storage families, written once.** A storage you add is a storage family (rule 9): one shared builder and interface under `storages/<family>/`, whose store is `crate::stores::<family>` in every instance. GenDB composes it into each workload that reads it as one storage over that workload's whole schema (every table and column), built from its plain flat storages, with the part slots of the family's template expanded per table and column type, and two generated files that make the builder and the opening schema-free: `schema_exec.rs` (`crate::schema_exec`: each column's type and nullability at run time) and `whole_schema.rs` (`crate::whole_schema`: `lemma_<family>`, the store's relations are every table of the schema). Then it is an ordinary storage: verified, built, checked against the policy and the budget, and admitted in that workload's library. The family's files and the template's parts: `storage-authoring.md`.
- **The default module and plans.** The default module `workloads/default/` is shared code (scanned like `src/agent/**`, with rule 8): it opens the family stores, or before the first family the plain flat storages, by table id. A workload tunes a family only through its plan `plans/<name>/<family>.rs` (else the family's `default_plan.rs`): data only (rule 10), such as which table to sort by which column or which columns get zone maps, checked by the builder at run time (an inapplicable entry is ignored, never unsound) and never read by the engine, which learns the layout from the stored parts. A new schema then needs no code, only an optional plan.
- **The transition**. By the end, every workload is served by the default module over storage families. The start version is not general: its workload-specific storages and the own modules that open them (CURRENT FACTS, Workloads) are allowed only as inherited, and they are to be replaced early: put a workload on a family, rebuild its storages with the family's builder at its scale, then delete its own module (rule 11 then requires it). Every version on the way stays verified and correct on every workload. CURRENT FACTS shows each workload's own module, inherited storages and plan.
- **Storage per workload.** The manifest names the families (`families[]`), the default module's files (`default_modules`) and each workload's uses (`workloads[]`: `{name, storage_uses, modules}`; its schema: `task.json` `manifest`; where `workloads/`, `plans/` and `storages/` lie: `task.json` `you_own`). Each workload has its own library, plain storage and budget; coverage, one copy of each column, the policy and the budget rule (Storage) hold per workload, at its scale; a check workload's storage is exempt from the budget.
- **Inputs and tools per workload.** Each workload's templates, data, bindings, baselines and budget rule: `files.workloads.<name>`. The tools take `workload` (default: the primary): which crate, data, library and saved answers a job uses. Check every workload's crate before you submit, the check workloads' included: a submission that fails on any workload is refused.
- **Global view across workloads.** Look for what the workloads share: a general technique speeds up every workload whose templates have its pattern, and each of them counts in the score."#;

/// ONLY ONE ENGINE IS ACCEPTED (request `engine.workloads.require_one_engine`; `engine::stage::one_engine`): one
/// paragraph of the section One engine for every workload, after its opening paragraph, only when the request sets the
/// rule (the context's `general.require_one_engine`): the next accepted version must be one engine, what one engine
/// is, the refusal before any build or timing, and that the first one may be slower (generality first).
pub const GENERAL_ONE_ENGINE_RULE: &str = "**Only a version that is one engine can be accepted now** (the request's `engine.workloads.require_one_engine`). One engine: every workload is served by the default module `workloads/default/` over storage families (or plain flat storages); no workload has a module of its own, and no workload reads an inherited workload-specific storage (CURRENT FACTS, Workloads; `version.json` `general.one_engine`). A submission that is not one engine is refused right after its freeze, before any build or timing (`not_one_engine`). Generality comes first: while the head is not one engine, the first one-engine version may be slower than the head; it is accepted when it is correct (every crate verified whole, its storages built, every check workload's answers and every counted cell finished with agreeing answers), and from then on the combined score decides as before.";

/// The section One engine for every workload ([`GENERAL_WORKLOADS`]) when the session's context has a workloads view
/// ([`workloads_of`]), with [`GENERAL_ONE_ENGINE_RULE`] after its opening paragraph when the context sets
/// `general.require_one_engine`; `None` for every other run, and the section is then absent.
pub fn workloads_section(context: &serde_json::Value) -> Option<String> {
    workloads_of(context)?;
    if context["general"]["require_one_engine"] != true {
        return Some(GENERAL_WORKLOADS.to_string());
    }
    // The opening paragraph ends where the first bullet starts.
    let (opening, bullets) = GENERAL_WORKLOADS.split_once("\n\n- ")?;
    Some(format!("{opening}\n\n{GENERAL_ONE_ENGINE_RULE}\n\n- {bullets}"))
}

/// HOW TO WORK: fast development and fast measurement (measure first, profile, time only what a
/// change affects, submit verified batches), the global view, freedom, sub-agents (at most 5, in
/// the foreground; each task sized with care, neither so small that proofs and evaluations take most of its
/// cost nor so large that no measurement comes back for long) and orientation.
pub const GENERAL_HOW_TO_WORK: &str = r#"# How to work

Speed of development is part of the goal: the sooner a faster verified version is accepted, the sooner the next one builds on it.

- **Measure first, prove later.** Proofs are the most expensive part. Build an idea unverified and time it (`trial` and `profile` with `verification: "not_run"`; Tools) before you write its proofs, comparing alternatives where that is cheap. Keep what measures fast, drop the rest, and prove only the design the measurements chose, iterating with module-scoped checks.
- **Profile the templates you work on** (`profile`): where their time goes decides the next change. No profile follows an admission.
- **Time only what a change can affect** (`trial` with `templates`), not the whole matrix: the evaluation times every cell anyway.
- **Submit verified batches.** This session waits while GenDB evaluates each submission; how long that takes at this scale is in CURRENT FACTS (Scale). The longer it takes, the more verified improvements one submission should carry: verify several, then submit them together; do not submit a one-line change alone.
- **Global view.** You see every training template and the data together: their SQL (`files.templates`), what each one reads and where its time goes (CURRENT FACTS), and the data facts (`files.data`). Look across the templates for shared features (operators, join shapes and keys, predicates, subquery shapes such as EXISTS, IN, scalar and correlated, grouping and sorting, data types, key and sort properties of the data), choose general techniques that speed up many templates at once, and rank your work by its total gain over all templates and worker counts: that is what the score sums.
- **Freedom.** You decide everything: the architecture, the algorithms, the data layout, the parallelism and the proofs. Be creative and aggressive: try bold ideas from research papers, from other systems, and new ones of your own; small safe steps alone will not beat the best engines. Large redesigns are welcome: keep a general path behind your fast paths, so every version stays complete and a partial redesign can still be submitted. A slower or refused submission costs only its evaluation: the best version is always kept, and every attempt stays on record for later sessions. Nothing here asks for a particular technique; the design space map (Design and proofs) is information only.
- **Sub-agents.** You may start sub-agents with the `Agent` tool, at most 5 at a time, when the work splits into independent parts (for example one operator, one storage layout, one proof module each). You stay the lead: give each one part, its own files (modules) and a clear specification of what to build and prove (no two edit the same file); then integrate the parts, verify the whole crate, measure and submit. Size each sub-agent's task with care: too small, and most of the cost goes to proofs and evaluations; too large, and no measurement comes back for a long time, and the session grows long and complex. A good task ends with a verified, measured gain that can go into the next submission. Start them in the foreground: several `Agent` calls in one message run in parallel, and you wait for all of them; a background sub-agent ends your turn early and forces an early submission. Tell each one the rules of this prompt (your workspace only, the inputs named here, signal only its own processes); its tool calls are part of this session's record and cost. Sub-agents are optional: use them when they make the work faster.
- **Orient yourself.** A fresh session reads `NOTES.md`, `TREE.md`, `FINDINGS.md`, the last evaluation (CURRENT FACTS) and `ENGINE_MAP.md` (every module of your crate with its header and items) before the sources."#;

/// FIXED: the claim and the entry, the supported set and the entry's statuses, ownership, the whole-crate check, and the
/// general line's rules (`rules.json` `engine_rules`). A stage run ([`Workloads::Stage`]) owns a module per workload and
/// verifies one crate per workload; its rules cover every workload's names and constants, check the variants per
/// workload and add rule 8, the workload modules' rule. A run of several workloads ([`Workloads::Set`])
/// also owns the default module, the storage families and the plans, and adds rules 9 to 12 (R3
/// `storage_family_required`, R4 `plan_is_data`, R5 `workload_module_scope`, R6 the check workloads).
pub fn fixed(workloads: Workloads) -> String {
    // A stage run and a run of several workloads share the per-workload texts (one crate per workload, the union of the
    // workloads' names, the variants per workload, rule 8).
    let stage = workloads != Workloads::One;
    let set = workloads == Workloads::Set;
    let own = if set {
        r#"- **You own** `src/agent/**` (the engine, shared by every workload), `workloads/default/**` (the default module), `workloads/<name>/**` (a workload's own module, only where rule 11 allows one), `storages/<family>/**` (the storage families you write), `plans/<name>/<family>.rs` (a workload's plans) and the author roots of storages you add (One engine for every workload). The entry, its claim and statuses, the AST codec and every framework file of each workload's crate and of each family instance are fixed and regenerated at freeze for that workload's schema and storages (the file list: `task.json` `fixed_files`)."#
    } else if stage {
        r#"- **You own** `src/agent/**` (the engine, shared by every workload), `workloads/<name>/**` (each workload's module, Stage 2) and the author roots of storages you add. The entry, its claim and statuses, the AST codec and every framework file of each workload's crate are fixed and regenerated at freeze for that workload's schema and storages (the file list: `task.json` `fixed_files`)."#
    } else {
        r#"- **You own** `src/agent/**` of the engine crate and the author roots of storages you add. The entry, its claim and statuses, the AST codec and every framework file of your crate are fixed and regenerated at freeze (the file list: `task.json` `fixed_files`)."#
    };
    let whole = if stage { r#"- **Every version is verified whole:** Verus checks each workload's whole crate with `--no-cheating`."# } else { r#"- **Every version is verified whole:** Verus checks the whole crate with `--no-cheating`."# };
    let one_word = if stage { r#" In this run the names are those of every workload's schema, and a column name of one word (no `_`) is refused only inside a literal: as an identifier or a segment of one it is reported, not refused."# } else { "" };
    let constants_of = if stage { " (of any workload)" } else { "" };
    let variants = if stage {
        r#"6. **Variants** (gating): frozen rewrites of a workload's templates that keep their meaning exactly must return their template's saved answers; an evaluation checks each workload's variants at that workload's first scale (their kinds and counts: CURRENT FACTS). The final evaluation also times them against their templates and reports the ratios to the reviewer, with no threshold; a large ratio is a reason for review."#
    } else {
        r#"6. **Variants** (gating): frozen rewrites of each template that keep its meaning exactly (kinds: @VARIANT_KINDS@) must return their template's saved answers; every evaluation checks each of them at the first scale of the ladder. The final evaluation also times them against their templates and reports the ratios to the reviewer, with no threshold; a large ratio is a reason for review."#
    };
    let workload_modules = if set {
        r#"
8. **Workload modules process no queries** (`workload_module_statement`, gating): files under `agent/workload/` (the default module or a workload's own module, in each crate) name no statement type, AST path or the AST codec (`EOrderedQuery`, `EQuery`, `EPred`, `EExpr`, `exec::ast`, `spec::ast`, `gendb_ast_codec` and the like). A module opens its workload's storages as the engine's tables, with the proofs that needs; its size and item kinds are reported with every evaluation.
9. **New storages are family storages** (`storage_family_required`, gating): every storage a submission adds is a use of a storage family (`{name, family}` in a workload's `storage_uses`); a storage of one workload's own (a `workspace` use) is refused. Uses of the inherited admitted storages stay allowed.
10. **Plans are data** (`plan_is_data`, gating): a plan `plans/<name>/<family>.rs` and a family's `default_plan.rs` hold only `use` lines, comments, `verus!` and one `pub fn plan()` without parameters whose body is data: struct literals, paths, constructors with an uppercase name, `vec![…]`, numbers, `true` and `false`. No function or method call, operator, text literal, `if`, `match`, loop, `let`, closure or proof block (the exact rule: `rules.json`).
11. **Own modules only beside inherited storage** (`workload_module_scope`, gating): a workload that reads only family storages and plain flat storages has no module of its own and uses the default module; `workloads/<name>/` is allowed only while that workload reads an inherited storage that is neither a family's nor a plain flat storage.
12. **Check workloads verify and answer** (gating): every check workload's crate verifies whole, and every template at every visible binding agrees with the saved answers there."#
    } else if stage {
        r#"
8. **Workload modules process no queries** (`workload_module_statement`, gating): files under `agent/workload/` (a workload's module in its crate) name no statement type, AST path or the AST codec (`EOrderedQuery`, `EQuery`, `EPred`, `EExpr`, `exec::ast`, `spec::ast`, `gendb_ast_codec` and the like). A workload module holds its workload's plan and opens its storages as the engine's tables, with the proofs that needs; its size and item kinds are reported with every evaluation (Stage 2)."#
    } else {
        ""
    };
    format!(
        r#"# What is fixed

- **The claim** (`final-claim.json`; the engine entry `gendb-verus-engine-entry-v1`, `fixed/engine_entry.rs`): for every supported query and every database bound to the stored parts under the declared integrity constraints, the engine's answer is an outcome the SQL meaning allows: allowed rows (any tie order, any tie choice at a LIMIT boundary), the exact SQL error, or `Capacity` only outside `capacity_domain`. Under the trusted assumptions every call terminates with such an outcome.
- **The supported set:** every query with `wf_ordered(schema_spec(), q)`, the whole SQLSpec fragment over this schema, nested to any depth, correlated subqueries included. The entry decides it with the verified `check_ordered` before your code runs; you cannot narrow it, and every version answers every supported query. Before your code, the entry also returns `Refused` (a worker count outside 1..=64), `Malformed` (AST bytes that do not decode) and `ParamRefused` (a decoded query that is not well typed).
{own} The one author-facing signature is `crate::agent::engine` (`obligations.json` `engine`): it receives the stored parts of every storage the engine reads (`Stores`), the query, the worker count and the parallel dispatch, and its ensures must imply `answer_meets(old(stores)@, view_ordered(*q), r)`.
{whole} Never weaken, assume or bypass the claim: the source scanner refuses `assume`, `admit`, `external_body` and similar escapes (`rules.json`).

## The rules of this line

Checked at freeze and again at admission (`rules.json` `engine_rules`):

1. **The interpreter is allowed** inside your proof (Fallback).
2. **No schema names in engine code** (`schema_name`, gating). Engine code works for any schema, so it names none of this one. In the code of your `agent/` files and of the interface and builder files of every storage you add: no column name of the schema as an identifier, as `_`-separated segments of an identifier (in any case), or inside a string, byte string or char literal; and no table name of the schema inside such a literal or after `stores::` or `stores.`. Comments are not scanned; other table-name words in identifiers are reported, not refused.{one_word} Schema knowledge enters as data: `schema_exec()`, the generated access by table id and column id (`crate::flat_tables`; `crate::sources_flat` in a storage builder) and storage declarations.
3. **No template constants** (`template_constant`, gating): your `agent/` files contain no text or date constant of a training template's SQL{constants_of}, and no table of AST fragments with fixed table or column indices (`ast_fragment_table`).
4. **No template dispatch** (review): no decision on a whole query's shape or constants ("if this is that template, run that code"), no per-query tuning tables, no rule keyed to literal values. A planner rule fires on a local pattern for any tables and columns that meet its stated facts; fusing a chain such as scan, filter and aggregate is fine. Cost constants are global.
5. **No state between calls** (gating): no `static` items; every call starts from the stored parts.
{variants}
7. **State your reasons:** each submission's `rationale` names the query classes each change speeds up, and each part of a storage you add carries a `data_policy.why` that names its general use.{workload_modules}"#
    )
}

/// STORAGE: the plain storage and its generated access, the uses, adding storage (the detail in
/// [`STORAGE_AUTHORING_FILE`]), one copy, the budget rule (as in the template runs: plain storage only
/// as is, any storage change within the original data size) and what follows from it, data-level and query-level
/// co-optimization, checked flags and what is known about the data. The policy follows ([`GENERAL_STORAGE_POLICY`]).
pub const GENERAL_STORAGE: &str = r#"# Storage

- **The plain storage** is version 0's: one generated flat storage per table (`storages.json`), every column of the table once, in table order. `crate::flat_tables`, generated with your crate and checked by Verus with it, reads any table by table id and column id, each item specified against the bound database (`column_slice`: rows `lo..hi` of one column as stored, without a copy; `materialize_database` for the interpreter; every item: `storage-authoring.md`).
- **Uses.** `verus-engine.json` names the storages the engine reads; together they store every column of every table (`engine_storage_coverage_incomplete`). Their interfaces are copied into your crate as `stores/<name>/interface/**`.
- **Adding storage.** You may add storages built from admitted storages (`built_from`; with `extends` a storage keeps a source's parts, linked and never rebuilt, and adds parts after them). A storage built from source columns is refused (`storage_not_built_from_admitted`). Its builder is verified, and GenDB builds its asset in a worker child from the sources' assets. Name a storage you add without a table name, and write its builder and interface over its declaration and the generated access: rule 2 covers them. How to write one (the builder's access to its sources, the interface, the plain-columns vocabulary `files.plain_columns`, the `data_policy` kinds and refusal codes): contract `storage-authoring.md`.
- **One copy of each column** across the storages a version reads (the policy below): a new layout of a column takes the place, in your uses, of the storage that holds the column now.
- **The storage budget** (`files.budget_rule`; the same rule as the template runs), decided at each submission's evaluation and again at admission. A version that reads only the plain storage is allowed as is, at every scale, whatever its size. A version with any storage change (a new layout, encoding, index or metadata: any storage it reads that is not a plain flat storage, or that it adds) must keep its serving storage, every part file of the storages it reads counted once, at most the original data size of the scale (the raw generator text size). The plain storage is about 1.4 times the original size (CURRENT FACTS, Storage), so a storage change must first compress or re-encode the data below the original size; only the space saved can hold indexes, skipping metadata and other structures.
- **Data and query co-optimization** is encouraged: layout, sort order, encodings and compression can store the data in much less space than the plain storage, and operators can work on the encoded data directly. At each new scale GenDB builds your storages again with the same verified builders, so storage work carries to every scale.
- **Data facts as checked flags.** The engine is proved for every bound database. A fact that holds only for this data (key density, sortedness, clustering) must be a stored flag that a storage builder checks, with its meaning stated in `represents`, guarding a fast path at run time with the general path behind it.
- **What you know about the data** comes from the storages' contracts and descriptions and from the data facts (`files.data`: value ranges, distinct counts, sortedness, key density, text lengths)."#;

/// The `physical_only` storage policy (revision 2), the general line's copy of
/// `prompts::sections::PHYSICAL_ONLY_POLICY` as a subsection of Storage: the same rules, the declaration's kinds and
/// refusal codes in [`STORAGE_AUTHORING_FILE`]. Its co-clustering example is schema neutral (a child table clustered
/// by its parent's key).
pub const GENERAL_STORAGE_POLICY: &str = r#"## Storage policy: physical_only

Store each table's data **once**, and optimize the physical organization of that one copy freely. Beside it, keep only metadata over it: own-table key indexes, permutations, skip metadata and layout offsets. Do not store a second copy of any column, query computation or cross-table correspondences before the measured call. Verus does not check this classification; your declarations and published sources are reviewed.

**Allowed** (all of it counts against the storage budget and is reported openly in `data_policy`; rule of thumb: techniques already standard in academia and industry are allowed, as long as each table's data is stored once):
- **One copy of each table's rows (base payload)** in any column layout, partitioning, sorting or clustering. Every row is kept. Lossless encodings and compression. One copy may span several parts (for example codes, dictionary and offsets of a text column, or disjoint partitions).
- **Co-clustering:** a table's row order may follow another table's order (for example the rows of a child table clustered by the key of the parent table it references), provided nothing cross-table is stored: keys used only to choose the order are not stored, and a query that relies on two tables lining up checks their keys at run time.
- **Indexes of one table:** its own key values to its own row positions or ranges. The key values may repeat values of the stored copy; an index carries no other column's values.
- **Permutations:** row positions only, into the one copy, giving another sort order.
- **Skip metadata** computed from one table's own rows or blocks: min/max zone maps, Bloom filters (including trigram Bloom filters for LIKE), statistics.
- **Run offsets and row counts that describe a layout**, even when the layout's groups match a query's GROUP BY: a sorted, run-length-encoded layout gives group sizes for free, as in column stores. Queries must still read and combine the actual values.
- Readers over all of these.

**Not allowed**
- A second copy of any column's values, full or partial, in any order or encoding, in the same or another storage (for example a re-sorted copy of a table): keep another order as a permutation.
- Covering indexes: an index carrying copies of columns other than its keys.
- Stored query-derived values (expression results such as `price*(1-discount)`), or tables holding only a predicate's matching rows.
- Materialized joins or denormalized rows: another table's values copied beside a row, or join results.
- Cross-table row locators, even position-only: join indexes, row-match maps, or another table's keys, row positions or match ranges.
- Precomputed EXISTS / NOT EXISTS / IN flags or other subquery answers.
- Stored aggregates of values: group or block sums, prefix sums, aggregate value bounds (such as revenue bounds), cubes.
- Cached answers, or any state kept across measured calls.

**Boundary.** Each column's values are stored once across the serving storage; every other stored entry is an index key with its own row positions, a row position, or metadata over one table's own rows. Filtering, joins, sorting, aggregation and temporary structures happen inside each measured call and are timed. When a structure is uncertain, choose the conservative form and say why in `data_policy`.

**Declaration.** Every storage manifest declares `data_policy` for each part: `{part, table, kind, columns, why}` (the kinds and every refusal code: `storage-authoring.md`). A storage without a declaration is refused, and so is any storage or set of uses that would store a column's values a second time: checked before every build (unverified builds included), at evaluation and at registration."#;

/// The Storage section as the prompt shows it: [`GENERAL_STORAGE`] with its policy subsection.
pub fn storage_section() -> String {
    format!("{GENERAL_STORAGE}\n\n{GENERAL_STORAGE_POLICY}")
}

/// FALLBACK: the verified interpreter inside the proof, with its costs stated plainly.
pub const GENERAL_FALLBACK: &str = r#"# Fallback: the verified interpreter

SQLSpec's verified interpreter is part of your crate (`exec/**`): call it inside your proof to keep every version complete while your own operators cover more and more queries. A fallback outside the proof is not allowed: nothing outside your crate ever answers a query.

- **Whole statement:** `exec_ordered` over a database materialized from the stored parts (`crate::flat_tables::materialize_database`). @VERSION_ZERO_IS@; its proof is the interpreter's theorem plus the uniqueness of the bound database (`lemma_flat_database_unique`).
- **Per operator:** the interpreter's operator functions over rows you computed: `exec_filter`, `exec_project`, `exec_group_by`, `exec_aggregate`, `exec_left_join` (`exec::relational::{ops, group}`) and the expression path `exec_expr`. They read a database only for subqueries inside conditions; the toolkit's locality lemma (`lemma_query_local`, `engine_link`) lets you materialize only the tables a subquery reads.
- **Its costs, plainly:** every call materializes every table it reads, copying each value; FROM lists and inner joins become materialized cross products; AND and OR evaluate both sides; every subquery runs again for every outer row, uncorrelated ones included; GROUP BY and the top-level sort are quadratic; it uses one thread. Alone, it finishes only small single-table work at scale; version 0's profile shows where its time goes."#;

/// DESIGN AND PROOFS: planner plus operators, the semantic side conditions H1-H5, the engine toolkit, proof advice,
/// reuse of the search index and general modules, parallelism, readability, and the design space map (information
/// only).
pub fn design_and_proofs(shape: Shape) -> String {
    let (accepted, entry_names) = match shape {
        Shape::OneLine => ("every accepted version", "its version and measured effect"),
        Shape::Branches => ("every accepted version of every branch", "its branch, version and measured effect"),
    };
    format!(
        r#"# Design and proofs

- **Planner plus operators** suits a verified engine: a planner that turns the AST into a physical plan by local rules, each rule justified by one generic equivalence lemma with its side conditions; physical operators, each proved to refine its plan node's meaning; scans proved against each storage's `represents`. Heuristic choices (access path, join order and algorithm) need no proof; only the rewrites do.
- **Semantic side conditions.** SQLSpec's exact meaning decides which rewrites are sound:
  - H1, strict evaluation and the first error: AND and OR evaluate both sides; Filter and Project report the first error in canonical row order. A plan that skips rows or evaluates an expression on other rows needs the expression total there (it never errs and stays in the machine domain); a plan that only reorders rows needs its possible errors uniform or total.
  - H2, representatives: GROUP BY and DISTINCT keep the first member's key; MIN, MAX and DISTINCT aggregates pick among SQL-equal values; equal numerics of different display scales are different outputs. Order independence needs scale-exact keys and arguments.
  - H3, capacity: a plan may not need a machine intermediate wider than the canonical evaluation's.
  - H4, correlation: a subquery sees the outer row; evaluating it once needs context independence, and decorrelation needs equality-correlation lemmas with column-shift bookkeeping.
  - H5, row order: order is observable only through H1, H2 and the top-level LIMIT; `ordered_ok` allows any tie order.
- **The engine toolkit** (`engine_link/**` in your crate) holds generic lemmas for these conditions (bag equality, locality, totality classes, congruence, decorrelation, column maps, joins, keys, top-k); `files.toolkit` indexes each of its modules with its header and items. Use them or write your own.
- **Proofs.** Decompose a proof into small lemmas, each with a narrow purpose (one row-evaluation step, one loop invariant step, one merge step). Verify modules or single functions while you iterate (`toolchain.json` `scoped_verify`); the official check is always the whole crate. On an rlimit failure, profile it: `verus --profile` (through `toolchain.json` `direct_verus`, run from `verus-tmp/`; see `direct_profiling`) shows which definitions are over-expanded. Then hide those definitions (`#[verifier::opaque]` / `hide`, revealed only where needed), add one-step unfold lemmas, or split the proof. **Do not raise rlimit.**
- **Reuse.** Before writing a piece yourself, search the index of reusable implementations (`files.search_index`: each item's name, one-line description and specification; copies under `admitted-code/`): {accepted}, the modules of attempts that verified but were not accepted (marked `verified, not accepted`), the admitted storages, and the run's read-only reuse libraries (marked `reuse`; their per-query programs may spell their query's constants, which your rules refuse). Each engine entry names {entry_names}. Copy a module as is or adapt it: nothing is composed automatically or trusted because of where it came from, and Verus checks everything again in your crate. Call the framework's public helper lemmas in `link/**` and `bridge/**` instead of copying them. A naturally general piece of code or proof (sort, codec, dictionary, key directory, top-k, LIKE, GROUP BY lemma, parallel split and merge) may go in its own module under `src/agent/common/`, with a specification that mentions no query constants and no single layout and a one-line `//!` description; GenDB indexes it at admission for later authors.
- **Parallelism.** The worker count of a cell is the **maximum** the call may use, not a requirement: fewer threads, or a serial path, is fine where it is faster (`parallel.json`).
- **Readability.** Write readable code, specifications and proofs: meaningful names, one purpose per function, units (rows, bytes, days, scales), a short header per module (`//!`; its first sentence becomes the module's line in `ENGINE_MAP.md` and in the search index), and proof steps explained where they are not obvious. Versions are published and read by people and by later sessions.
- **Design space map:** known options, as information only. Use any of them, combine them, or do something else entirely.
  - Architecture: vectorized interpretation over typed column chunks; push-based pipelines; morsel-driven parallelism; operator fusion of scan, filter and aggregate; specialized operator variants chosen at plan time.
  - Rewrites: predicate pushdown; projection pruning; constant folding (closed parameter arithmetic); join reordering; decorrelation and unnesting of EXISTS / IN / scalar subqueries; semi-join reduction; early or partial aggregation; common subexpressions.
  - Cost estimation: heuristics; stored statistics (min/max, distinct-count sketches, histograms, sampling); learned models.
  - Joins: hash (with radix partitioning), sort-merge, index nested loop over own-table key indexes, direct-mapped join on dense keys guarded by a checked flag, semi and anti joins, Bloom filters passed sideways.
  - Aggregation: hash, dense array, sort-based, streaming over clustered input; per-thread partial states with merge.
  - Sorting: radix sort, merge sort, top-k heaps; sorting on codes.
  - Storage (built from the plain storage; one copy; within the budget): sort order and clustering, partitioning, dictionary / frame-of-reference / bit-packing / run-length encodings, operating on codes, zone maps and other skipping metadata, own-table key indexes, permutations.
  - Parallelism: morsels over storage blocks (`fork_join`), partitioned build and probe, parallel merge.
  - Proof patterns: H1-H5 and the engine toolkit above; permutation witnesses; a general path behind fast paths."#
    )
}

/// The evaluation steps of a submission (shared by both shapes; `rejected` names what stays when a submission is not
/// accepted, `admitted` what follows its admission). A stage run freezes every workload's crate, then
/// verifies, builds and times the goal workload, decides on the goal's score, and only then verifies, builds, times
/// (recorded, never deciding) and checks the variants of every kept workload, and admits in every workload's library.
fn evaluation_steps(rejected: &str, admitted: &str, workloads: Workloads) -> String {
    const TIMING: &str = "for every cell, parent and candidate run back to back in fresh worker children under one timing lease, the order alternating from cell to cell, the load average recorded; each side of a cell is 1 warm call and @TIMED_CALLS@, and the median hot call is the cell's time (a warm call over the limit leaves the cell unfinished); every answer is compared with the saved answers (the exact rule, with the wait for a quiet host, the parent cells not run again and the re-timing of suspicious pairs: `performance.json` `submission_timing`)";
    let steps = match workloads {
        Workloads::One => format!(
            r#"- **The evaluation of a submission**, every step gating, in order:
  1. freeze: the manifest, the storage uses, coverage of every column, the source rules (central scan, no `static` items, this line's rules) and storage composition;
  2. Verus on the whole crate with `--no-cheating`, 0 errors;
  3. storages: the new storages built, the storage policy and the budget (Storage);
  4. an interleaved timing against the parent at the current scale: {TIMING};
  5. the score decision (Goal): the submission is accepted only if its score is better than the parent's in that same timing; otherwise it is recorded as an attempt and {rejected};
  6. every variant runs at the first scale of the ladder, one call each at 64 workers, for its answer only; every answer must agree;
  7. admission as the next version ({admitted}."#
        ),
        Workloads::Stage => format!(
            r#"- **The evaluation of a submission**, in order, every step gating except where said (Stage 2):
  1. freeze of every workload's crate (`src/agent/**` with that workload's module): the manifest, each workload's storage uses, coverage of every column, the source rules (central scan, no `static` items, this line's rules) and storage composition;
  2. Verus on the goal workload's whole crate with `--no-cheating`, 0 errors;
  3. the goal's storages: the new storages built, the storage policy and the budget (Storage);
  4. an interleaved timing against the parent on the goal workload at its scale: {TIMING};
  5. the score decision (Goal): the submission is accepted only if the goal workload's score is better than the parent's in that same timing; otherwise it is recorded as an attempt and {rejected}, and no kept workload is verified or timed;
  6. then for every kept workload, in its own library: Verus on its whole crate (0 errors), its new storages, the policy and its budget; an interleaved timing against the parent's side of that workload at its scale, in the same way (recorded and shown, never deciding: a slower or unfinished cell does not refuse the submission, a wrong answer does); its variants at its first scale, one call each at 64 workers, for their answers only, every answer agreeing;
  7. admission in every workload's library with the same lineage, as the next version ({admitted}."#
        ),
        Workloads::Set => format!(
            r#"- **The evaluation of a submission**, in order, every step gating except where said (One engine for every workload):
  1. freeze of every workload's crate (`src/agent/**` with that workload's module, and the instances of the families it reads): the manifest, each workload's storage uses, coverage of every column, the source rules over every workload's names (central scan, no `static` items, this line's rules) and storage composition;
  2. Verus on every workload's whole crate with `--no-cheating`, 0 errors;
  3. every workload's storages, in its own library: the new storages and family instances built, the storage policy, one copy and the budget (Storage; a check workload is exempt from the budget);
  4. every check workload: every template at every visible binding at the smallest and the largest worker count, one call each, every answer agreeing with the saved answers; this comes before any timing;
  5. on every counted workload, an interleaved timing against the parent's side of that workload at its scale: {TIMING};
  6. the score decision (Goal): the submission is accepted only if the combined score is better than the parent's, from those same timings; otherwise it is recorded as an attempt with every workload's timing and {rejected}, and no kept workload is timed;
  7. then every kept workload: an interleaved timing against the parent's side of that workload at its scale, in the same way (recorded and shown, never deciding: a slower or unfinished cell does not refuse the submission, a wrong answer does);
  8. every workload's variants at its first scale, one call each at 64 workers, for their answers only, every answer agreeing;
  9. admission in every workload's library with the same lineage, as the next version ({admitted}."#
        ),
    };
    format!(
        r#"{steps}

  A wrong answer refuses the submission and is flagged for the operator's review. A failure of the framework is not yours: that submission is evaluated again.
- **The final evaluation** is separate: the full protocol (the version timed alone, 1 warm + 3 hot calls per cell at every worker count, every template at every visible binding, the variants timed at the scale, and a profile) runs only for the final numbers, never for a submission.
- **Framework safety limits**, the same for every version: every engine call ends at @CALL_LIMIT@ of wall time and at @MEMORY_LIMIT@ of anonymous memory, and such a call leaves its cell unfinished. They are not goals; they keep one slow version from blocking the shared host."#
    )
}

/// LOOP: the line or the branches, the session across submissions, the evaluation, the final evaluation, the limits,
/// the notebook, the findings log and when a session ends. The score is in the goal, the timing queue in Tools.
/// In a stage run ([`Workloads::Stage`]) and in a run of several workloads ([`Workloads::Set`]) the evaluation has
/// its own order, and in both no session ends for a scale move (each workload stays at its scale).
pub fn the_loop(shape: Shape, workloads: Workloads) -> String {
    let stage = workloads != Workloads::One;
    const NOTEBOOK_HEADINGS: &str = "Keep these headings: `## Direction` (what you work on now), `## Design`, `## Tried` (each idea with its measured numbers), `## Ideas`, `## Proof notes`. Keep it current and short; replace stale content. GenDB copies it into every version and attempt folder.";
    const CONTINUES: &str = "- **Your session continues after each submission.** You submit (Submission); GenDB evaluates the submission while this session waits; the next message in this same session is the evaluation with the facts that changed, and you keep your working context.";
    match shape {
        Shape::OneLine => format!(
            r#"# The loop

- **One line of versions.** Each version builds on the best version: a submission's parent is the head, the best version so far (the version this session started from, or your last accepted submission), and an accepted submission becomes the new head. Only admitted versions count: work you have not submitted is in no version, and a later session starts from the head.
{CONTINUES}
{steps}
- **The notebook `NOTES.md`** is the line's memory. {NOTEBOOK_HEADINGS}
- **The findings log** `FINDINGS.md` is written by GenDB only: after every evaluated submission, the change, its measured effect against its parent and the submission's `findings`. Read it; never write it.
- **When a session ends.** A session ends only at an evaluation, and only when you asked for it (`next_session: "fresh"`){ends}. The work then continues in a fresh session{after_move} that starts from your notebook, `TREE.md`, `FINDINGS.md` and the last evaluation. Nothing else ends a session: there is no turn cap and no time cap. Between sessions the run may pause for a review; the work then continues from its files."#,
            steps = evaluation_steps("the head stays", "`vNNN`), its folder and its node in the version tree; it becomes the head", workloads),
            ends = if stage { " or when the provider has compacted this session's context" } else { ", when the provider has compacted this session's context, or when the run moves to the next scale (Goal)" },
            after_move = if stage { "" } else { " (after a move, at the new scale)" }
        ),
        Shape::Branches => format!(
            r#"# The loop

{CONTINUES}
- **The parent** is your branch head: your branch's newest version (the version this session started from, or your last accepted submission). Set `base: main_line_head` in the manifest to rebase onto the main-line head instead; the main-line head is then the parent. Only admitted versions count: work you have not submitted is in no version, and your branch's next session starts from its head (a merge session from the main-line head).
{steps}
- **Branches (island model).** Up to @BRANCHES@ branches explore in parallel, each in its own sessions. Each branch states its **direction** on its first submission (`direction`: the areas it explores, how it differs from the other branches' directions, what it expects to gain per class of queries). The other branches' directions are in CURRENT FACTS. All branches share the version tree, the findings log, the timing queue and the proved parts in the search index.
- **The main line.** The main-line head is the best version over all branches. A branch version whose recorded score beats the main-line head's is timed against it, interleaved; the winner is the main-line head. When a branch's session ends while its head has gains the main line has not taken, the branch's next session is a **merge session**: seeded from the main-line head, with the branch head beside it; its submissions are judged against the main-line head, and an accepted merge becomes the main-line head.
- **The notebook `NOTES.md`** is your branch's memory. {NOTEBOOK_HEADINGS}
- **The findings log** `FINDINGS.md` is written by GenDB only: after every evaluated submission of any branch, the change, its measured effect against its parent and the submission's `findings`. Read it; never write it.
- **When a session ends.** A session ends only at an evaluation, and only when you asked for it (`next_session: "fresh"`), when the provider has compacted this session's context{ends}. The branch then continues in a fresh session{after_move} that starts from your notebook, `TREE.md`, `FINDINGS.md` and the last evaluation. Nothing else ends a session: there is no turn cap and no time cap. Between sessions the run may pause for a review; the branch then continues from its files."#,
            steps = evaluation_steps(
                "the branch head stays",
                "`vNNN`, numbered across branches), its folder and its node in the version tree; then the main line (below)",
                workloads
            ),
            ends = if stage { " or when a merge is accepted" } else { ", when a merge is accepted, or when the run moves to the next scale (Goal; every branch's session then ends at its next evaluation)" },
            after_move = if stage { "" } else { " (after a move, at the new scale)" }
        ),
    }
}

/// INPUTS: the contract, the run's records, lookup, what is not an input, conduct.
pub fn inputs(shape: Shape) -> String {
    let tree_fields = match shape {
        Shape::OneLine => "every version and attempt with its parent and score",
        Shape::Branches => "every version and attempt with its parents, branch, direction and score",
    };
    format!(
        r#"# Inputs and conduct

- **Read `files.author_contract` first.** It maps every input: the task and the claim, the templates (`files.templates`: SQL, parameters, visible bindings, saved baseline times), the versions and attempts per scale (`files.versions_detail`), the storages (interfaces, readers, contracts, sizes) and the stored-parts read API, the schema and the integrity constraints, the data facts, the toolkit index and the proof library, parallelism, the fixed definitions and the source rules, the toolchain and the tools with their result fields, the failure classes and accounting, and the timing protocol, the score, the limits and the budget rule. A contract file this prompt names by its file name alone (`rules.json`, `storage-authoring.md`, ...) is in that file's directory.
- **The run's records**, read-only: `TREE.md` and `tree.json` ({tree_fields}), `FINDINGS.md`, every version's folder (`files.versions_records`/vNNN: code, reading view, notes, cells, the interleaved timing, the variants' answers; `PROFILE.md` where one was recorded) and every attempt's (`attempts/<label>-aNNN`, beside `files.versions_records`). Your workspace holds read-only copies of the versions this session works from (`files.versions`).
- **Look items up before reading framework files:** `index.json` `commands.api_lookup`, `files.toolkit`, `files.engine_map`, grep inside your crate, and the vstd sources. Read the regions you need, not whole toolkit files.
- **Not inputs:** other GenDB runs, old outputs, other libraries, scratch directories, tests, fixtures, repository source or history, host or controller source, and any statement or binding file the framework does not give you. Do not read, list or search them; every tool call is recorded and audited.
- **Do not** alter ledger, library, reference, record or authority files; hash or fingerprint whole datasets; or launch inference or agents other than your sub-agents."#
    )
}

/// TOOLS: the typed tools, trials and profiles, unverified runs, the limits and the one timing queue, the check economy.
pub const GENERAL_TOOLS: &str = r#"# Tools

- **Typed `gendb_local` tools** (`tools.json`): the engine tools over a `verus-engine.json` (`check`, `verify`, `compile`, `trial`, `profile`); the storage tools (`storage_check`, `storage_verify`, `storage_compile`, `storage_build`, `storage_register`); and `catalog`, which re-reads the library (admitted storages and their bytes). You may also run the pinned Verus toolchain directly (`toolchain.json`). Use them as often as useful. Local runs are diagnostics; only the evaluation of a submission is official.
- **`trial`** times the training matrix by default: every template at the timing binding x every configured worker count (`templates`, `binding` or `workers` narrow it), 1 warm + 1 hot call per cell (`hot_calls` asks for more), each answer compared with the saved answers. It reports per cell your median, the faster baseline's time and the ratio, plus the totals per worker count when every template ran. With `sql` it runs your own statements instead (no saved answer: status and rows only).
- **`profile`**: one cell (`workers`, and one template or one `sql` statement), 1 warm + 1 measured call, with the hot functions of the measured call by sampled self time (`PROFILE.md` in the job; the method is in `performance.json`): which of your functions, and which interpreter or library functions, take the time.
- **Unverified runs.** `trial` and `profile` accept `verification: "not_run"`: the frozen crate is compiled with `rust_verify --no-verify` (no proof obligation checked; source rules and `--no-cheating` unchanged) and run on the real data with the same comparisons. `storage_build` accepts the same for an unverified storage build. Every such result is labelled `diagnostic_unverified`; it never counts as a submission, proof, admission or official measurement. Instrumentation inside the crate (clock reads, logging) needs `external_body`, which every GenDB job refuses; keep it in your own scratch builds.
- **Limits and the timing queue.** Every call of a trial or profile runs under the call and memory limits (The loop). Trials and profiles (yours and your sub-agents') and the run's evaluations share one timing queue on this host: two timings never overlap, so they wait for each other. Times from different windows are never compared; only the interleaved timing decides.
- **Check economy.** A proof check or compile of identical crate content is reused, never rerun; results say `reused`. Once a check passes, repeat it only after a meaningful code or specification change, to diagnose a concrete failure, or to settle a check that is still unresolved. Do not sweep solver settings (rlimit, seeds) or rerun passing proofs to measure margin. Trials, repairs and the measurements your design needs are not limited by this."#;

/// Where `candidate_manifest` points on the engine line (the controller's rule, `controller::author::
/// CANDIDATE_MANIFEST_RULE`, in the engine's terms), as the contract (`task.json` `manifest.rule`) states it.
pub const ENGINE_MANIFEST_RULE: &str = "candidate_manifest names your existing verus-engine.json inside your workspace, workspace-relative (for example verus-engine.json, or c2/verus-engine.json for a manifest in a subfolder) or absolute inside the workspace; the local tools' candidate argument follows the same rule, and GenDB records the normalized workspace-relative path";

/// The submission rule of the general line (`manifest` names the manifest file).
pub fn general_submission(manifest: &str, shape: Shape) -> String {
    let fields = match shape {
        Shape::OneLine => "`direction` (optional: one short line on what this session works on), `findings` (short measured lessons for the findings log) and `next_session` (`continue` by default, or `fresh`)",
        Shape::Branches => "`direction` (required on your branch's first submission), `findings` (short measured lessons for the findings log), `next_session` (`continue` by default, or `fresh`) and `base` (`branch_head` by default, or `main_line_head`)",
    };
    format!(
        r#"# Submission

A submission is the call's structured JSON result `{{candidate_manifest, rationale, data_access_analysis}}`; the schema is enforced.
- `candidate_manifest` names your existing `{manifest}` inside your workspace: workspace-relative (for example `verus-engine.json`, or `c2/verus-engine.json` for a manifest in a subfolder) or absolute. The local tools' candidate argument follows the same rule.
- `rationale` (the changes, and the query classes each speeds up) and `data_access_analysis` (how the engine reads its storages) are short, nonempty texts.
- The manifest may also set {fields}; `task.json` has its schema.

Write `NOTES.md` first: a later fresh session continues the work from it."#
    )
}

/// PROCESSES: the rules of a shared host, the general line's copy of `prompts::sections::PROCESSES_APPENDIX` (the
/// same rules; its `<run>` placeholder is `<job>` here, because `<…>` also names the key paths' directories).
pub const GENERAL_PROCESSES_APPENDIX: &str = r#"# Appendix: processes on a shared host

This host is shared with other sessions running the same tools. You may start, background and stop your own checks, compiles and trials whenever useful, within these rules.

- **Need a result? Run in the foreground.** A Bash call that finishes within its timeout returns only after its command and every process it started have exited, with the command's exit status.
- **A call that reaches its Bash timeout is not stopped.** The provider moves it to a background task (its answer says so), and it keeps running with every process it started. So for a long run, do one of these:
  - bound it below the call's timeout with `timeout -k 10 <seconds> <command>`: TERM goes to the command and its children in timeout's process group, then KILL 10 s later. A child that calls `setsid` leaves that group.
  - or start it in its own recorded process group: `setsid <command> > <log> 2>&1 & echo $! > <job>.pgid`. The recorded number is both its PID and its group: `ps -o pid,etime,args -g $(cat <job>.pgid)` shows it, and `kill -TERM -- -$(cat <job>.pgid)` stops it with every child.
- **Each Bash call runs in its own process group** (`$GENDB_BASH_CALL_GROUP` inside the call), and a call moved to the background keeps that group. `kill -TERM -- -<that group>` stops that call, and GenDB's shell guardian then kills and reaps everything it started. To recover the group of a background call, use what you recorded (for example `echo $GENDB_BASH_CALL_GROUP > <job>.group` before a long command) or your own process tree (`pstree -p -a $GENDB_AUTHOR_PROVIDER_PID`); then signal exactly that PID or group.
- **Do not start a run in the background and poll its log for completion text.** The poll cannot see the process exit, so text that never appears (a refused option, a crash) makes it wait out its whole timeout. For direct `rust_verify` runs, use the foreground route in `toolchain.json` (`direct_verus`).
- **Wait for a local job with the `wait` tool; never wait or poll for one inside a Bash call.** Every Bash call holds the host's shared activity lock until it ends, and a timed job (`trial`, `profile`) needs that lock alone to start, with your session's later jobs queued behind it: a Bash call that waits for a job delays that very job. `wait` holds no lock; it returns the job's result when the job ends, or its status after at most `wait_seconds`.
- **Never kill by executable name, command pattern or user:** no `pkill`, `killall`, `pgrep -f ... | xargs kill` or `ps | grep | kill`. Never signal a process outside your own tree, `gendb_local` jobs or GenDB's evaluation.
- **Crash dumps.** GenDB starts its processes and your Bash commands with Linux `coredump_filter` 0 (the value actually set: CURRENT FACTS, Host). A crash is still reported by the host's crash handler, but its dump holds no memory contents. Keep that setting for your processes."#;

/// The opening of a continued call (the provider session already holds the full prompt).
pub const GENERAL_CONTINUATION: &str = "\
# EVALUATION OF YOUR SUBMISSION

This session continues. The goal, the rules and the paths of this provider session's first prompt hold unchanged (@FIRST_PROMPT@). Below: the evaluation of your submission, then the facts that changed, the ledger and your latest local jobs. Continue the work: verify the next improvements and submit them together.";

/// The opening of a continued call after GenDB changed the instructions (the CHANGED INSTRUCTIONS section comes
/// first).
pub const GENERAL_CONTINUATION_AFTER_CHANGES: &str = "\
# EVALUATION OF YOUR SUBMISSION

This session continues. The paths of this provider session's first prompt hold (@FIRST_PROMPT@), and its instructions hold with the changes above (CHANGED INSTRUCTIONS). Below: the evaluation of your submission, then the facts that changed, the ledger and your latest local jobs. Continue the work: verify the next improvements and submit them together.";

/// The heading of a call that resumes its provider session after a stopped call ([`resumed_after_stop_opening`]).
pub const RESUMED_AFTER_STOP_HEADING: &str = "# YOUR PREVIOUS CALL WAS STOPPED";

/// The opening of a call that resumes its provider session after the session's previous call `stopped_call` was
/// stopped from outside (`prompts::engine_policy`: its receipt was rebuilt after the controller was lost, and its output
/// is never accepted). `first_prompt` names the provider session's first prompt; with `changed`, the CHANGED
/// INSTRUCTIONS section comes first.
pub fn resumed_after_stop_opening(stopped_call: u64, first_prompt: &str, changed: bool) -> String {
    let hold = if changed {
        format!("the paths of this provider session's first prompt hold ({first_prompt}), and its instructions hold with the changes above (CHANGED INSTRUCTIONS)")
    } else {
        format!("the goal, the rules and the paths of this provider session's first prompt hold unchanged ({first_prompt})")
    };
    format!(
        "{RESUMED_AFTER_STOP_HEADING}\n\nYour previous call (call {stopped_call}) was stopped before it ended, by the run's operator or a stop of GenDB's controller; it submitted nothing. This call resumes the same provider session: your context is kept, and {hold}. Your workspace is as that call left it; sub-agents and commands that were running then ended with it, so check any file they were writing before you use it. Below: the facts now, the ledger and the stopped call's local jobs. Continue the work."
    )
}

/// The head of the CHANGED INSTRUCTIONS section of a continued call (`prompts::engine_policy`): the sections that
/// follow it are new or replace the sections of the same name in the provider session's first prompt.
pub const CHANGED_INSTRUCTIONS_HEADING: &str = "# CHANGED INSTRUCTIONS";

/// The CHANGED INSTRUCTIONS section's opening: `first` names the provider session's first prompt, `count` the changed
/// sections given in full after it, `removed` the sections that no longer apply.
pub fn changed_instructions_opening(first: &str, count: usize, removed: &[String]) -> String {
    let mut text = format!("{CHANGED_INSTRUCTIONS_HEADING}\n\nGenDB changed the instructions of this run after this provider session's first prompt ({first}).");
    match count {
        0 => {}
        1 => text.push_str(" The section below is new or replaces the section of the same name there, in full."),
        n => text.push_str(&format!(" The {n} sections below are new or replace the sections of the same name there, in full.")),
    }
    if !removed.is_empty() {
        let names: Vec<String> = removed.iter().map(|name| format!("`# {name}`")).collect();
        // A removed section's content may have moved into another section (a merge), so the text does not say it
        // no longer applies: whatever of it still holds is in the changed sections, or in the first prompt's others.
        let place = if count == 0 { "the other sections of the first prompt" } else { "the sections below" };
        text.push_str(&format!(" These sections of the first prompt are removed, and whatever of them still holds is in {place}: {}.", names.join(", ")));
    }
    text.push_str(" Every other section of the first prompt holds unchanged. The changes apply from now on, also to the work in progress.");
    text
}

/// The line that closes the changed sections.
pub const CHANGED_INSTRUCTIONS_END: &str = "(End of the changed instructions.)";

/// Every fixed section of the full prompt of `shape` and `workloads`, the emphasis section included (and the Stage 2
/// section in a stage run, the One engine for every workload section in a run of several workloads, the
/// continued-engine section in a run of one workload), for checks over their words (the storage policy subsection
/// [`GENERAL_STORAGE_POLICY`] is checked beside them).
pub fn all_sections(shape: Shape, workloads: Workloads) -> Vec<String> {
    let mut sections = vec![
        goal(shape, workloads),
        GENERAL_CO_OPTIMIZATION.into(),
        GENERAL_HOW_TO_WORK.into(),
        fixed(workloads),
        GENERAL_STORAGE.into(),
        GENERAL_FALLBACK.into(),
        design_and_proofs(shape),
        the_loop(shape, workloads),
        inputs(shape),
        GENERAL_TOOLS.into(),
        GENERAL_PROCESSES_APPENDIX.into(),
    ];
    match workloads {
        Workloads::Stage => sections.insert(2, GENERAL_STAGE.into()),
        Workloads::Set => sections.insert(2, GENERAL_WORKLOADS.into()),
        // A continued run (`engine.seed_version`) has one workload.
        Workloads::One => sections.insert(1, GENERAL_CONTINUED.into()),
    }
    sections
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The sections name no query, template, table or column of TPC-H (they teach the framework only), and the
    /// design space map has one line per area.
    #[test]
    fn the_sections_name_no_query_or_schema() {
        for shape in [Shape::OneLine, Shape::Branches] {
            let text = all_sections(shape, Workloads::One).join("\n") + GENERAL_STORAGE_POLICY + &general_submission("verus-engine.json", shape) + GENERAL_CONTINUATION + GENERAL_CONTINUATION_AFTER_CHANGES
                + &changed_instructions_opening("`calls/0001/prompt.txt`", 2, &["Branches".into()])
                + &resumed_after_stop_opening(1, "`calls/0001/prompt.txt`", false) + &resumed_after_stop_opening(1, "`calls/0001/prompt.txt`", true);
            let words: Vec<&str> = text.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).collect();
            for name in ["Q01", "Q06", "Q09", "Q21", "lineitem", "orders", "customer", "partsupp", "supplier", "nation", "region", "l_shipdate", "o_orderdate"] {
                assert!(!words.contains(&name), "the general sections name no query or table: {name}");
            }
        }
        let map = design_and_proofs(Shape::OneLine);
        for area in ["Architecture", "Rewrites", "Cost estimation", "Joins", "Aggregation", "Sorting", "Storage (built from the plain storage; one copy; within the budget)", "Parallelism", "Proof patterns"] {
            assert!(map.contains(&format!("\n  - {area}: ")), "{area}");
        }
    }

    /// The fixed texts (every fixed section of a stage run, the Stage 2
    /// section included, of a run of several workloads, the One engine for every workload section included, and of a run
    /// with one workload, in both shapes) name no table, column or template of TPC-H, SEC-EDGAR or the check fixture
    /// `anyschema` and no workload: the workloads are the context's (`@GOAL_WORKLOAD@`, `@KEPT_WORKLOADS@`,
    /// `@PRIMARY_WORKLOAD@`, `@COUNTED_WORKLOADS@`, `@CHECK_WORKLOADS@`, `@KEPT_MEMBERS@`). SEC-EDGAR's one-word column names that are ordinary words (`value`,
    /// `version`, `name`, `line`, ...) cannot be absent from English texts; its other column names, its table names as
    /// words (`sub` only outside `sub-agent`) and its templates are checked.
    #[test]
    fn the_stage_texts_name_no_workload_table_column_or_template() {
        const SEC_COLUMNS: [&str; 28] = ["adsh", "afs", "cik", "cityba", "coreg", "countryba", "countryinc", "crdr", "datatype", "ddate", "fp", "fy", "fye", "inpth", "iord", "nciks",
            "plabel", "prevrpt", "qtrs", "rfile", "sic", "stmt", "stprba", "tlabel", "uom", "wksi", "aciks", "negating"];
        const SEC_TABLES_AND_TEMPLATES: [&str; 9] = ["num", "tag", "pre", "Q1", "Q2", "Q3", "Q4", "Q6", "Q24"];
        const TPCH: [&str; 13] = ["Q01", "Q06", "Q09", "Q21", "lineitem", "orders", "customer", "partsupp", "supplier", "nation", "region", "l_shipdate", "o_orderdate"];
        const WORKLOADS: [&str; 7] = ["sec", "SEC", "EDGAR", "tpch", "TPC", "TPCH", "anyschema"];
        // The check fixture `benchmarks/anyschema`: its tables and its columns (its templates X01 to X31
        // below).
        const ANYSCHEMA: [&str; 32] = ["ax_owner", "ax_kind", "ax_item", "ax_event", "ax_void", "ow_id", "ow_name", "ow_rank", "ow_born", "ow_credit", "ow_weight", "ow_note", "ow_code",
            "kd_code", "kd_group", "kd_weight", "it_owner", "it_line", "it_kind", "it_qty", "it_price", "it_day", "it_flag", "it_tiny", "ev_seq", "ev_owner", "ev_line", "ev_at",
            "ev_amount", "ev_memo", "vd_id", "vd_text"];
        for (shape, workloads) in [(Shape::OneLine, Workloads::Stage), (Shape::Branches, Workloads::Stage), (Shape::OneLine, Workloads::One), (Shape::Branches, Workloads::One),
            (Shape::OneLine, Workloads::Set), (Shape::Branches, Workloads::Set)] {
            let text = all_sections(shape, workloads).join("\n") + GENERAL_STORAGE_POLICY + &general_submission("verus-engine.json", shape) + GENERAL_ONE_ENGINE_RULE;
            let words: Vec<&str> = text.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).collect();
            for name in SEC_COLUMNS.iter().chain(&SEC_TABLES_AND_TEMPLATES).chain(&TPCH).chain(&WORKLOADS).chain(&ANYSCHEMA) {
                assert!(!words.contains(name), "a stage text names {name}");
            }
            for template in (1..=31).map(|i| format!("X{i:02}")) {
                assert!(!words.contains(&template.as_str()), "a text names the fixture template {template}");
            }
            // `sub` as a word only in `sub-agent`.
            let lower = text.to_lowercase();
            let identifier = |c: char| c.is_ascii_alphanumeric() || c == '_';
            for (at, _) in lower.match_indices("sub") {
                let word = !lower[..at].ends_with(identifier) && !lower[at + 3..].starts_with(identifier);
                assert!(!word || lower[at + 3..].starts_with("-agent"), "a stage text names the table sub: {}", &lower[at.saturating_sub(40)..(at + 40).min(lower.len())]);
            }
        }
    }

    /// The texts of a run of several workloads: the section One engine
    /// for every workload follows the goal and the main direction in Stage 2's place, says what decides (the combined
    /// score, no guard, the user's keep rule), the check workloads, the root's sides, the crate composition, families,
    /// the default module and plans, the transition, storage, inputs and tools per workload and the global view; the
    /// goal, what is fixed (rules 8 to 12) and the loop (the evaluation's order) change only as such a run needs;
    /// every rule has one home; the One and Stage texts are unchanged (their goldens).
    #[test]
    fn the_workloads_texts_say_what_decides_what_is_checked_and_how_the_code_stays_general() {
        for said in ["# One engine for every workload", "\"make it one engine, general to support any schema, data, and query supported by SQLSpec\"",
            "counted (@COUNTED_WORKLOADS@), check (@CHECK_WORKLOADS@) and kept (@KEPT_MEMBERS@)", "**Every counted workload decides, through the sum.**",
            "The user asks that the engine not lose its performance on any workload. No guard refuses a loss", "**A check workload must verify and answer.**",
            "an empty table and an all-NULL column", "before any timing (rule 12)", "Your workspace starts from the side of @PRIMARY_WORKLOAD@, the primary workload",
            "read-only under `root-sides/<name>/` in your workspace", "`root-sides/ancestor/`", "Each side is a verified version, so you may start from either",
            "**Storage families, written once.** A storage you add is a storage family (rule 9)", "`schema_exec.rs`", "`whole_schema.rs` (`crate::whole_schema`: `lemma_<family>`",
            "**The default module and plans.**", "`plans/<name>/<family>.rs`", "data only (rule 10)", "A new schema then needs no code, only an optional plan.",
            "By the end, every workload is served by the default module over storage families.", "they are to be replaced early", "(rule 11 then requires it)",
            "`families[]`", "`files.workloads.<name>`", "The tools take `workload` (default: the primary)", "a check workload's storage is exempt from the budget"] {
            assert!(GENERAL_WORKLOADS.contains(said), "{said}");
        }
        let goal = goal(Shape::OneLine, Workloads::Set);
        assert!(goal.contains("**Build the fastest verified engine, as soon as possible:** one engine for every workload of this run, faster than") && goal.contains("of every counted workload (@COUNTED_WORKLOADS@)")
            && goal.contains("3. **The combined score** decides every submission") && goal.contains("the combined F and G are the sums over the counted workloads")
            && goal.contains("4. **One scale per workload.**") && !goal.contains("ladder"), "{goal}");
        let fixed = fixed(Workloads::Set);
        for said in ["`workloads/default/**` (the default module)", "`storages/<family>/**`", "`plans/<name>/<family>.rs`", "Verus checks each workload's whole crate",
            "a column name of one word (no `_`) is refused only inside a literal", "a training template's SQL (of any workload)", "8. **Workload modules process no queries**",
            "(the default module or a workload's own module, in each crate)", "9. **New storages are family storages** (`storage_family_required`, gating)", "10. **Plans are data** (`plan_is_data`, gating)",
            "11. **Own modules only beside inherited storage** (`workload_module_scope`, gating)", "12. **Check workloads verify and answer** (gating)"] {
            assert!(fixed.contains(said), "{said}\n{fixed}");
        }
        assert!(!fixed.contains("@VARIANT_KINDS@") && !fixed.contains("(Stage 2)"), "{fixed}");
        for shape in [Shape::OneLine, Shape::Branches] {
            let the_loop = the_loop(shape, Workloads::Set);
            for said in ["1. freeze of every workload's crate", "2. Verus on every workload's whole crate", "4. every check workload: every template at every visible binding at the smallest and the largest worker count",
                "this comes before any timing", "5. on every counted workload, an interleaved timing against the parent's side of that workload",
                "6. the score decision (Goal): the submission is accepted only if the combined score is better", "and no kept workload is timed;",
                "8. every workload's variants at its first scale", "9. admission in every workload's library with the same lineage"] {
                assert!(the_loop.contains(said), "{shape:?}: {said}\n{the_loop}");
            }
            assert!(!the_loop.contains("next scale") && !the_loop.contains("after a move"), "{shape:?}");
        }
        let mut sections = all_sections(Shape::OneLine, Workloads::Set);
        sections.push(GENERAL_STORAGE_POLICY.into());
        sections.push(general_submission("verus-engine.json", Shape::OneLine));
        let headings: Vec<&str> = sections.iter().filter_map(|s| s.lines().next()).collect();
        assert_eq!(headings[..4], ["# Goal", "# Main direction: data and query co-optimization", "# One engine for every workload", "# How to work"]);
        assert!(sections.iter().all(|s| !s.starts_with("# Stage 2")), "no Stage 2 section");
        for phrase in ["`storage_family_required`", "`plan_is_data`", "`workload_module_scope`", "Never create `src/agent/workload`", "The tools take `workload`", "no kept workload is timed",
            "The user asks that the engine not lose its performance on any workload", "A new schema then needs no code", "whatever its size", "share one timing queue", "at most 5 at a time"] {
            assert_eq!(sections.iter().filter(|s| s.contains(phrase)).count(), 1, "stated once: {phrase}");
        }
    }

    /// The one-engine rule (request `engine.workloads.require_one_engine`): stated in one paragraph after the
    /// opening of One engine for every workload only when the context sets `general.require_one_engine`; without it the
    /// section is byte for byte as before, and a run of one workload has no such section.
    #[test]
    fn the_one_engine_rule_is_stated_only_when_the_request_sets_it() {
        let set = serde_json::json!({"general":{"workloads":[{"name":"w","role":"counted"}]}});
        assert_eq!(workloads_section(&set).as_deref(), Some(GENERAL_WORKLOADS), "unset: the section as before");
        assert_eq!(workloads_section(&serde_json::json!({"general":{"require_one_engine":true}})), None, "no workloads view: no section");
        let mut required = set.clone();
        required["general"]["require_one_engine"] = serde_json::json!(true);
        let section = workloads_section(&required).unwrap();
        let (opening, rest) = GENERAL_WORKLOADS.split_once("\n\n- ").unwrap();
        assert!(section.starts_with(&format!("{opening}\n\n{GENERAL_ONE_ENGINE_RULE}\n\n- **Every counted workload decides")), "{section}");
        assert_eq!(section.len(), GENERAL_WORKLOADS.len() + GENERAL_ONE_ENGINE_RULE.len() + 2);
        assert!(section.ends_with(rest));
        for said in ["**Only a version that is one engine can be accepted now**", "`engine.workloads.require_one_engine`", "the default module `workloads/default/` over storage families",
            "no workload has a module of its own", "no workload reads an inherited workload-specific storage", "`general.one_engine`", "before any build or timing (`not_one_engine`)",
            "Generality comes first", "the first one-engine version may be slower than the head", "every counted cell finished with agreeing answers",
            "from then on the combined score decides as before"] {
            assert!(GENERAL_ONE_ENGINE_RULE.contains(said), "{said}");
        }
        assert!(!GENERAL_ONE_ENGINE_RULE.contains("\n"), "one paragraph");
    }

    /// The Stage 2 texts: the section follows the goal, says what
    /// decides and what is kept, the module convention with its rule, general code with a plan per workload (a new workload
    /// needs a new plan, not new code; the start version's storage code for the kept workload is replaced by general code
    /// and a plan, its storages rebuilt once), storage, inputs and tools per workload and the global view; the goal, what is
    /// fixed and the loop change only as a stage run needs, and every stage rule has one home.
    #[test]
    fn the_stage_texts_say_what_decides_what_is_kept_and_how_workloads_share_one_engine() {
        for said in ["# Stage 2: a second workload", "**The goal: make the same engine fast on @GOAL_WORKLOAD@.** Its score decides every submission (Goal).",
            "**Keep @KEPT_WORKLOADS@.** Every submission must verify, and agree with the saved answers, on every workload.", "but it does not decide. The user asks that the engine not lose its performance there.",
            "CURRENT FACTS, Out of the box", "GenDB copies `workloads/W/**` into W's crate as `src/agent/workload/**` at freeze", "Never create `src/agent/workload` in your workspace (refused).",
            "written for any supported schema and data, parameterized by tables, columns and types, never for one benchmark's tables", "a new workload should need a new plan, not new code",
            "is to be replaced in this stage by general code and a plan: its storages are then built once by the general builders, and @KEPT_WORKLOADS@ must keep verifying and answering correctly",
            "CURRENT FACTS shows each module's size", "`workloads[]`: `{name, storage_uses, modules}`", "`files.workloads.<name>`", "The tools take `workload` (default: the goal)",
            "a technique that speeds up both counts twice"] {
            assert!(GENERAL_STAGE.contains(said), "{said}");
        }
        let goal = goal(Shape::OneLine, Workloads::Stage);
        assert!(goal.contains("on the training templates of the goal workload @GOAL_WORKLOAD@ at every worker count") && goal.contains("3. **The goal workload's score** decides every submission")
            && goal.contains("4. **One scale per workload.**") && !goal.contains("ladder"), "{goal}");
        let fixed = fixed(Workloads::Stage);
        assert!(fixed.contains("`workloads/<name>/**` (each workload's module, Stage 2)") && fixed.contains("Verus checks each workload's whole crate")
            && fixed.contains("a column name of one word (no `_`) is refused only inside a literal") && fixed.contains("a training template's SQL (of any workload)")
            && fixed.contains("an evaluation checks each workload's variants at that workload's first scale") && !fixed.contains("@VARIANT_KINDS@")
            && fixed.ends_with("8. **Workload modules process no queries** (`workload_module_statement`, gating): files under `agent/workload/` (a workload's module in its crate) name no statement type, AST path or the AST codec (`EOrderedQuery`, `EQuery`, `EPred`, `EExpr`, `exec::ast`, `spec::ast`, `gendb_ast_codec` and the like). A workload module holds its workload's plan and opens its storages as the engine's tables, with the proofs that needs; its size and item kinds are reported with every evaluation (Stage 2)."), "{fixed}");
        for shape in [Shape::OneLine, Shape::Branches] {
            let the_loop = the_loop(shape, Workloads::Stage);
            assert!(the_loop.contains("1. freeze of every workload's crate") && the_loop.contains("otherwise it is recorded as an attempt and") && the_loop.contains("and no kept workload is verified or timed;")
                && the_loop.contains("6. then for every kept workload, in its own library: Verus on its whole crate (0 errors)") && the_loop.contains("(recorded and shown, never deciding: a slower or unfinished cell does not refuse the submission, a wrong answer does)")
                && the_loop.contains("7. admission in every workload's library with the same lineage, as the next version (`vNNN`") && !the_loop.contains("next scale") && !the_loop.contains("after a move"), "{shape:?}: {the_loop}");
        }
        let mut sections = all_sections(Shape::OneLine, Workloads::Stage);
        sections.push(general_submission("verus-engine.json", Shape::OneLine));
        let headings: Vec<&str> = sections.iter().filter_map(|s| s.lines().next()).collect();
        assert_eq!(headings[..4], ["# Goal", "# Main direction: data and query co-optimization", "# Stage 2: a second workload", "# How to work"]);
        for phrase in ["a technique that speeds up both counts twice", "never for one benchmark's tables", "`workload_module_statement`", "Never create `src/agent/workload`", "The tools take `workload`",
            "no kept workload is verified or timed", "The user asks that the engine not lose its performance there"] {
            assert_eq!(sections.iter().filter(|s| s.contains(phrase)).count(), 1, "stated once: {phrase}");
        }
    }

    /// One line: the texts say that each version builds on the best version, and nothing of
    /// islands, other branches, merges, rebases or the main line; the multi-branch texts keep them. Both keep the
    /// user's emphasis (the goal first, work fast, the global view, freedom, sub-agents).
    #[test]
    fn one_line_texts_say_nothing_of_branches() {
        let one_line = all_sections(Shape::OneLine, Workloads::One).join("\n") + &general_submission("verus-engine.json", Shape::OneLine);
        assert!(one_line.contains("Each version builds on the best version"), "{one_line}");
        let lower = one_line.to_lowercase();
        for absent in ["island", "branch", "merge session", "accepted merge", "main_line_head", "main-line", "main line", "rebase", "base:", "@branches@"] {
            assert!(!lower.contains(absent), "one line: {absent}");
        }
        let branches = all_sections(Shape::Branches, Workloads::One).join("\n") + &general_submission("verus-engine.json", Shape::Branches);
        for kept in ["Branches (island model)", "merge session", "base: main_line_head", "Up to @BRANCHES@ branches", "`direction` (required on your branch's first submission)", "shared by all branches"] {
            assert!(branches.contains(kept), "branches: {kept}");
        }
        for emphasis in ["**Build the fastest verified engine, as soon as possible:**", "# How to work", "Speed of development is part of the goal", "**Measure first, prove later.**",
            "prove only the design the measurements chose", "**Submit verified batches.**", "do not submit a one-line change alone", "**Time only what a change can affect** (`trial` with `templates`)",
            "**Profile the templates you work on**", "**Global view.**", "shared features", "rank your work by its total gain over all templates and worker counts", "**Freedom.** You decide everything",
            "Be creative and aggressive", "**Sub-agents.**", "at most 5 at a time", "Size each sub-agent's task with care", "Start them in the foreground"] {
            assert!(one_line.contains(emphasis) && branches.contains(emphasis), "{emphasis}");
        }
    }

    /// The loop describes the development evaluation: 1 warm call and the run's timed hot calls per cell
    /// (`@TIMED_CALLS@`), the median hot call the cell's time, the variants at the first scale for their answers only
    /// and no qualification at the other bindings; the full protocol only for the final numbers; no profile after an
    /// admission (How to work). Nothing asks for a submission per verified gain.
    #[test]
    fn the_loop_describes_the_development_evaluation() {
        for shape in [Shape::OneLine, Shape::Branches] {
            let text = the_loop(shape, Workloads::One);
            for kept in ["each side of a cell is 1 warm call and @TIMED_CALLS@, and the median hot call is the cell's time", "every variant runs at the first scale of the ladder, one call each at 64 workers, for its answer only",
                "**The final evaluation** is separate: the full protocol (the version timed alone, 1 warm + 3 hot calls per cell at every worker count", "runs only for the final numbers, never for a submission", "`performance.json` `submission_timing`"] {
                assert!(text.contains(kept), "{shape:?}: {kept}");
            }
            for gone in ["other visible bindings", "8. a profile", "1 warm + 3 hot calls per cell, the cell's time", "1 hot call, and the hot call's time"] {
                assert!(!text.contains(gone), "{shape:?}: {gone}");
            }
        }
        assert!(GENERAL_HOW_TO_WORK.contains("No profile follows an admission"));
        let all = all_sections(Shape::OneLine, Workloads::One).join("\n") + GENERAL_CONTINUATION + GENERAL_CONTINUATION_AFTER_CHANGES;
        for gone in ["Submit each verified gain at once", "as soon as it verifies", "Submit early and often"] {
            assert!(!all.contains(gone), "{gone}");
        }
    }

    /// Each rule is stated once. The budget rule, the score, the timing queue, the sub-agent rules (with the
    /// sizing of each sub-agent's task) and the batching advice each have one home; the other sections point
    /// to it by name. No section prescribes how to split the work across sub-agents.
    #[test]
    fn each_rule_has_one_home() {
        let mut sections = all_sections(Shape::OneLine, Workloads::One);
        sections.push(GENERAL_STORAGE_POLICY.into());
        sections.push(general_submission("verus-engine.json", Shape::OneLine));
        let homes = |phrase: &str| sections.iter().filter(|s| s.contains(phrase)).count();
        for phrase in ["whatever its size", "the raw generator text size", "G = the sum over the worker counts", "share one timing queue", "at most 5 at a time",
            "Start them in the foreground", "submit them together",
            "Size each sub-agent's task with care: too small, and most of the cost goes to proofs and evaluations; too large, and no measurement comes back for a long time, and the session grows long and complex. A good task ends with a verified, measured gain that can go into the next submission.", "No profile follows an admission", "Write `NOTES.md` first", "Your session continues after each submission",
            "Only admitted versions count", "how long that takes at this scale",
            "builds your storages again with the same verified builders", "Re-encoding the largest table alone can be enough", "Every storage manifest declares `data_policy`"] {
            assert_eq!(homes(phrase), 1, "stated once: {phrase}");
        }
        // Without the emphasis section, every rule still has its home.
        let plain: Vec<&String> = sections.iter().filter(|s| !s.starts_with("# Main direction")).collect();
        for phrase in ["whatever its size", "share one timing queue", "at most 5 at a time", "Size each sub-agent's task with care", "builds your storages again with the same verified builders"] {
            assert_eq!(plain.iter().filter(|s| s.contains(phrase)).count(), 1, "{phrase}");
        }
        for gone in ["Split the work across sub-agents", "one for the storage builder"] {
            assert_eq!(homes(gone), 0, "no prescribed split: {gone}");
        }
    }
}
