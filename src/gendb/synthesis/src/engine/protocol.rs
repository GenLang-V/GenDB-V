//! The general line's two evaluation protocols: fast feedback during development (1 warm + 1 hot call per cell, the
//! variants checked at the first scale), and the full protocol (1 warm + 3 hot) only for the final evaluation of the
//! performance.
//!
//! - [`DEVELOPMENT`]: every timing of the run (a submission's evaluation and the main-line race, `engine::acceptance`;
//!   a scale move, `engine::branches`). Each timed cell is 1 warm + 1 hot call and the hot call's time is the cell's
//!   time. A submission's variants run at the first scale of the ladder only, one call each, for their answers only (no
//!   time is read). No qualification at the other visible bindings and no automatic profile. Version 0 is timed the
//!   same way and keeps its checks and profile ([`VERSION_ZERO`]).
//! - [`FINAL`]: the final evaluation of one admitted version at one scale for reporting (`gendb engine final-evaluation`,
//!   `engine::final_evaluation`; run by the operator, never automatically). Each timed cell is 1 warm + 3 hot calls (the protocol
//!   the saved baselines were measured with) and its time the median hot call; the qualification at every visible
//!   binding; the variants timed at that scale (1 warm + 1 hot, with the variant/template ratio report); and a profile.
//!
//! Both plans run their variants at [`QUALIFICATION_WORKERS`] workers and compare every answer with the saved answers; a
//! wrong answer refuses a submission. At the evaluated scale only the variants of the templates finished at every worker
//! count run (a call of another one would only reach the limit); at the first scale every variant with AST bytes of its
//! own runs (every template finishes there and an answer check is cheap;
//! [`VariantRun::finished_templates_only`]).
//! The plans decide only how much is measured, never what is accepted: the score decision, the storage rules and the
//! admission are the same under both.

use super::timing::{OFFICIAL_CALLS, VARIANT_CALLS};
use gendb_verification::admission::engine::QUALIFICATION_WORKERS;
use serde::Serialize;
use serde_json::{Value, json};

/// Calls per timed cell of the development plan: 1 warm, then 1 hot (the cell's time).
pub const DEVELOPMENT_CELL_CALLS: u32 = 2;
/// Calls per variant when only its answer is checked: one call, no time read.
pub const ANSWER_CALLS: u32 = 1;

/// How and where a plan runs the variants.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum VariantRun {
    /// One call per variant at the ladder's first scale, for its answer only.
    AnswersAtFirstScale,
    /// 1 warm + 1 hot call per variant at the evaluated scale: its answers checked and its time reported against its
    /// template's (`engine::timing::variant_ratios`, no threshold).
    TimedAtScale,
}

impl VariantRun {
    /// Calls per variant.
    pub fn calls(self) -> u32 {
        match self {
            Self::AnswersAtFirstScale => ANSWER_CALLS,
            Self::TimedAtScale => VARIANT_CALLS,
        }
    }

    /// The ladder index of the scale the variants run at, for an evaluation at ladder index `evaluated`.
    pub fn scale_index(self, evaluated: usize) -> usize {
        match self {
            Self::AnswersAtFirstScale => 0,
            Self::TimedAtScale => evaluated,
        }
    }

    /// The one worker count the variants run at.
    pub fn workers(self) -> usize {
        QUALIFICATION_WORKERS
    }

    /// Whether only the variants of the templates finished at every worker count of the plan's timing run (at the
    /// evaluated scale), or every variant with AST bytes of its own (at the first scale).
    pub fn finished_templates_only(self) -> bool {
        match self {
            Self::AnswersAtFirstScale => false,
            Self::TimedAtScale => true,
        }
    }
}

/// What one evaluation measures (module documentation).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct EvaluationPlan {
    /// `development` or `final`, as records name the plan.
    pub name: &'static str,
    /// Calls per timed cell (the first warm); the cell's time is the median of the hot calls.
    pub cell_calls: u32,
    /// Qualification of the finished templates at every visible binding (one call each at 64 workers).
    pub qualification: bool,
    /// The variants: every one at the first scale, or those of the finished templates at the evaluated scale.
    pub variants: VariantRun,
    /// A profile of the timed version (every template at the worker count of its largest gap).
    pub profile: bool,
}

impl EvaluationPlan {
    /// Hot calls per timed cell.
    pub fn hot_calls(&self) -> u32 {
        self.cell_calls.saturating_sub(1)
    }

    /// The plan as records and the contract state it.
    pub fn record(&self) -> Value {
        json!({"plan":self.name,"cell":format!("1 warm + {} hot calls per timed cell, the cell's time the median hot call", self.hot_calls()),
            "cell_calls":self.cell_calls,"qualification":self.qualification,
            "variants":{"run":self.variants,"calls":self.variants.calls(),"workers":self.variants.workers(),
                "of":if self.variants.finished_templates_only() { "the templates finished at every worker count" } else { "every template (each variant with AST bytes of its own)" },
                "scale":match self.variants { VariantRun::AnswersAtFirstScale => "the first scale of the ladder", VariantRun::TimedAtScale => "the evaluated scale" }},
            "profile":self.profile})
    }
}

/// The development evaluation (module documentation): every timing of the run.
pub const DEVELOPMENT: EvaluationPlan =
    EvaluationPlan { name: "development", cell_calls: DEVELOPMENT_CELL_CALLS, qualification: false, variants: VariantRun::AnswersAtFirstScale, profile: false };

/// The final evaluation for reporting (module documentation): the full protocol.
pub const FINAL: EvaluationPlan = EvaluationPlan { name: "final", cell_calls: OFFICIAL_CALLS, qualification: true, variants: VariantRun::TimedAtScale, profile: true };

/// Version 0 (`engine::branches::seed_version_zero`, framework work once per run at the first scale): timed like every
/// development timing (its cells are the first parent record), with the finished checks and the profile it always had
/// (the first session reads where the interpreter's time goes).
pub const VERSION_ZERO: EvaluationPlan =
    EvaluationPlan { name: "version_0", cell_calls: DEVELOPMENT_CELL_CALLS, qualification: true, variants: VariantRun::TimedAtScale, profile: true };

#[cfg(test)]
mod tests {
    use super::*;

    /// The development plan : each timed cell 1 warm + 1 hot; the variants planned at the
    /// ladder's first scale, one call each, whatever scale is evaluated; no qualification and no profile.
    #[test]
    fn the_development_plan_is_one_warm_one_hot_with_answer_only_variants_at_the_first_scale() {
        assert_eq!((DEVELOPMENT.cell_calls, DEVELOPMENT.hot_calls()), (2, 1));
        assert_eq!(DEVELOPMENT.variants, VariantRun::AnswersAtFirstScale);
        assert_eq!(DEVELOPMENT.variants.calls(), 1, "one call per variant, for its answer");
        assert!(!DEVELOPMENT.variants.finished_templates_only(), "every variant with AST bytes of its own, not only the finished templates'");
        for evaluated in [0, 1, 2] {
            assert_eq!(DEVELOPMENT.variants.scale_index(evaluated), 0, "variants at the first scale when the run is at ladder index {evaluated}");
        }
        assert!(!DEVELOPMENT.qualification, "no qualification at the other visible bindings");
        assert!(!DEVELOPMENT.profile, "no automatic profile");
        assert_eq!(DEVELOPMENT.record()["cell"], "1 warm + 1 hot calls per timed cell, the cell's time the median hot call");
    }

    /// The final plan has the full protocol: 1 warm + 3 hot calls per cell (the baselines' protocol), qualification at
    /// every visible binding, the variants timed at the evaluated scale (1 warm + 1 hot), and a profile.
    #[test]
    fn the_final_plan_has_the_full_protocol() {
        assert_eq!((FINAL.cell_calls, FINAL.hot_calls()), (4, 3));
        assert_eq!(FINAL.cell_calls, gendb_verification::admission::execution::TIMED_REPETITIONS);
        assert!(FINAL.qualification && FINAL.profile);
        assert_eq!((FINAL.variants, FINAL.variants.calls(), FINAL.variants.workers()), (VariantRun::TimedAtScale, 2, 64));
        assert_eq!(FINAL.variants.scale_index(2), 2, "the final evaluation times the variants at its own scale");
        assert!(FINAL.variants.finished_templates_only(), "at the evaluated scale only the finished templates' variants");
    }
}
