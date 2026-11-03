//! The schema-engine synthesis target: one verified
//! engine for every well-typed query on the TPC-H schema, built in rounds against the 22-template training set.
//!
//! - [`timing`]: the official template matrix (1 warm + 3 hot calls per cell, median), the variant matrix (1 warm +
//!   1 hot) and the variant/template ratio report, over a child-call interface the engine entry is wired to;
//! - [`totals`]: per-template and total hot medians per worker count against the saved DuckDB/Umbra baselines, the gap,
//!   ratios and margin, the qualifications, and the stop decision; pure arithmetic over saved records;
//! - [`score`]: the general-engine score of a version at one scale (finished cells, then the time normalized by the
//!   faster baseline per worker count), with unfinished cells counted at the call limit;
//! - [`race`]: the interleaved timing of a candidate against its parent in one window (ABBA pairs under one timing
//!   lease, load averages, the skip rules, the re-timing of suspicious pairs) and the score decision;
//! - [`quiet`]: the quiet-moment gate before each timing pair (the host's 1-minute load average below a quarter of the
//!   CPUs, at most ten minutes);
//! - [`profile`]: profile jobs (sampled self time per function, per-call resources) and `PROFILE.md`;
//! - [`facts`]: the training set (templates, visible bindings, frozen variants), their encoded engine statements and
//!   the training facts authors read;
//! - [`submission`]: the engine manifest `verus-engine.json`, the freeze of a submission into an engine crate, and its
//!   Verus builds;
//! - [`serving`]: serving SQL statements (or AST bytes) from an engine library's admitted engine version
//!   (`gendb serve-engine`);
//! - [`role`]: the engine role of one round's author session (workspace seeding, evaluation with qualification, the
//!   official and variant matrices and the totals, the version's admission; the engine tools) and the admission
//!   interface its cells and versions go through;
//! - [`rounds`]: the engine run: rounds, versions, the stop, the run summary, and the `gendb engine` routes.
//!
//! The general line (request `engine.line: "general"`) adds:
//! - [`tree`]: the version tree (versions, attempts, parents, branches, heads), the findings log and the operator's flags;
//! - [`sessions`]: one session of a branch (records, provider context, when it ends, its policy) and the run's spend;
//! - [`protocol`]: the two evaluation plans: the development evaluation of every submission (1 warm + 1 hot call per
//!   cell, variants at the first scale for their answers only) and the final evaluation for reporting (the full
//!   protocol);
//! - [`acceptance`]: a submission's evaluation (the interleaved timing against its parent, the decision, admission with
//!   lineage, the version folder, the main-line head);
//! - [`branches`]: the run (version 0, the branch slots, merges, the review cadence, the scale ladder, the stop) and
//!   `gendb engine prepare`;
//! - [`asset_upkeep`]: when the run library's superseded derived storage assets are released and which heads keep
//!   theirs (`storage::asset_release`);
//! - [`final_evaluation`]: `gendb engine final-evaluation`, the full protocol of one version at one scale (operator only);
//! - [`operator_note`]: `gendb engine operator-note`, a note from the run's operator shown once at the top of a
//!   branch's next author call;
//! - [`operator_resume`]: `gendb engine operator-resume`, the operator's end of a branch's provider wait (the
//!   controller stopped), so the relaunched controller calls at once;
//! - [`re_evaluation`]: `gendb engine re-evaluate`, the development evaluation of a recorded attempt again with its
//!   recorded build and race, its suspicious pairs re-timed (operator only);
//! - [`stage`]: runs of several workloads (`engine.stage`: a goal workload and kept workloads;
//!   `engine.workloads`: counted, check and kept workloads decided by the combined score), each workload with its own
//!   crate and library: their evaluation, the root (one side per workload), the version records per workload and the
//!   context's view of the workloads;
//! - [`export`]: `gendb engine export`, the engine source of one accepted version as a folder a later run seeds from;
//! - `general_trial` (tests only): the $0 fixture trial of the whole general loop with a scripted author.

pub mod acceptance;
pub mod asset_upkeep;
pub mod branches;
pub mod export;
pub mod facts;
pub mod final_evaluation;
#[cfg(test)]
mod general_trial;
pub mod operator_note;
pub mod operator_resume;
pub mod profile;
pub mod protocol;
pub mod quiet;
pub mod race;
pub mod re_evaluation;
#[cfg(test)]
mod replay_fixture;
pub mod role;
pub mod rounds;
pub mod score;
pub mod serving;
pub mod sessions;
pub mod stage;
pub mod submission;
pub mod timing;
pub mod totals;
pub mod tree;
