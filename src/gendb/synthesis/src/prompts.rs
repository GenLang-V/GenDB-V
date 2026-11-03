//! Author inputs of both roles: prompts and objectives (`policy`: the query role's and the workload storage role's
//! `RolePolicy`; `sections`: the prompts' fixed Markdown sections; `data_sections`: each call's data sections), and the generated author contract bundles of the author workspaces (`brief`: `contract/verus/**` of
//! a query author, `brief::storage`: `contract/storage/**` of the workload storage author).
//!
//! The schema-engine author's inputs are the `engine_*` modules: `engine_sections` (the prompt's fixed sections),
//! `engine_policy` (its `RolePolicy`: prompt assembly, round objective), `engine_facts` (its CURRENT FACTS head and the
//! handoff of earlier rounds) and `engine_contract` (the contract bundle `contract/engine/**`, the toolkit index and the
//! crate map `ENGINE_MAP.md`). The general engine line (`engine.line: "general"`) adds `engine_general_sections` (its
//! prompt's fixed sections) and `engine_facts::general` (its data sections); `engine_policy::general_author_prompt`
//! assembles its prompt and `engine_contract` writes its contract. `instructions` splits a prompt into its instruction
//! sections with their digests, so a continued call can give the sections that changed since its provider session's
//! first prompt (CHANGED INSTRUCTIONS).
//!
//! Every input is generated from the enforcing code and the statement instance, with no query-specific hint. The
//! author should not need framework source beyond the crate it owns and reads (the SQLSpec library, the fixed entry
//! and the generated statement files).
//!
//! Sources: the earlier version's `integrated_author.rs` (verified prompt and objective) and
//! `integrated_verus_brief.rs`; the native modular contract (`author_contract.rs`) stayed in that version.

pub mod brief;
mod data_sections;
pub mod engine_contract;
pub mod engine_facts;
pub mod engine_general_sections;
pub mod engine_policy;
pub mod engine_sections;
pub mod instructions;
pub mod policy;
pub mod sections;

pub use policy::{EarlyStop, Objective, RuntimeTarget, StoragePolicy, VerifiedQueryPolicy};
