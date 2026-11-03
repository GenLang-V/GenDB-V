//! Synthesis: the public workload controller, query authoring, author prompts and tools, and provider sessions with
//! accounting. Outside the TCB: nothing here can change the fixed obligations; admission decisions belong to
//! `gendb_verification::admission`.
//!
//! - [`controller`]: the public entries `synthesize`, `preflight` (no author) and `serve` of one workload run
//!   (`controller::workload_run`, run as `gendb synthesize|preflight|serve REQUEST RUN_DIR`), the generic author-session
//!   loop, its ledger and the user's iteration/money controls;
//! - [`workload`]: the workload storage role (one session before the queries: shared storages);
//! - [`engine`]: the schema-engine target (timing matrices, totals and the stop decision; its role comes later);
//! - [`query`]: one statement's session (preflight, references, evaluation over storages, qualification, close,
//!   serving) and its query role;
//! - [`storage`]: storage authoring shared by both roles (manifest, freeze, check-and-build, registration, catalog,
//!   capture extension);
//! - [`published`]: a published run folder (GenDB-V results), read for its packages' author files (`gendb import`);
//! - [`tools`]: the authors' local tools (`gendb author-tools mcp`) and the session bench both roles run them on;
//! - [`prompts`]: the roles' prompts, objectives and generated author contracts;
//! - [`providers`]: the Claude Code author session;
//! - [`workload_folder`]: a workload folder (`schema.sql`, `queries/`, data, bindings, `gendb.toml`) read into requests.
//!
//! New synthesis uses the storage-aware path only (storage entries v1, v2 and derived; query entry v4, or v5 under
//! declared integrity constraints). Saved v3 packages are served by
//! the serving route (`gendb_runtime::serve`); the native synthesis loops stayed in
//! the earlier GenDB version.

pub mod controller;
pub mod engine;
pub mod file_lock;
pub mod output;
pub mod prompts;
pub mod providers;
pub mod published;
pub mod query;
pub mod storage;
pub mod tools;
pub mod workload;
pub mod workload_folder;
