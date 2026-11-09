//! Exact prepared-reference configuration and execution outcomes.
use serde::Serialize;
#[derive(Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum Status {
    Running,
    Completed,
    Failed,
    Skipped,
}
#[derive(Serialize)]
pub(super) struct TreeBorrows {
    pub precise_interior_mut: bool,
    pub implicit_writes: bool,
}
#[derive(Serialize)]
pub(super) struct Config {
    pub same_tcx: bool,
    pub borrow_tracker: &'static str,
    pub tree_borrows: TreeBorrows,
    pub validation: String,
    pub alignment_check: String,
    pub isolated_op: String,
    pub ignore_leaks: bool,
    pub provenance_mode: String,
    pub rng_seed: Option<u64>,
    pub data_race_detector: bool,
    pub weak_memory_emulation: bool,
    pub track_outdated_loads: bool,
    pub genmc: bool,
    pub native_libraries: usize,
    pub cmpxchg_weak_failure_rate: f64,
    pub preemption_rate: f64,
    pub backtrace_style: String,
    pub mute_stdout_stderr: bool,
    pub num_cpus: u32,
    pub address_reuse_rate: f64,
    pub address_reuse_cross_thread_rate: f64,
    pub fixed_scheduling: bool,
    pub float_nondeterminism: bool,
    pub float_rounding_error_mode: String,
    pub short_fd_operations: bool,
    pub collect_leak_backtraces: bool,
    pub environment_policy: &'static str,
    pub args: Vec<String>,
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Outcome {
    ExitZero,
    MiriEvaluationError { exit_code: i32 },
    GuestNonzeroExit { exit_code: i32 },
    MiriPanicked,
}
#[derive(Serialize)]
#[serde(untagged)]
pub(super) enum Result {
    Executed {
        status: Status,
        config: Config,
        outcome: Outcome,
    },
    Skipped {
        status: Status,
        reason: &'static str,
        same_tcx: bool,
    },
}
impl Result {
    pub fn status(&self) -> Status {
        match self {
            Self::Executed { status, .. } | Self::Skipped { status, .. } => *status,
        }
    }
    pub fn skipped() -> Self {
        Self::Skipped {
            status: Status::Skipped,
            reason: "crate_is_not_executable",
            same_tcx: true,
        }
    }
}
#[derive(Serialize)]
pub(super) struct Sidecar {
    pub snapshot_fnv1a64: String,
    pub snapshot_byte_length: u64,
    pub snapshot_path: String,
    pub last_reserved_source_alloc_id: u64,
    pub rustc_commit: &'static str,
    pub miri_commit: &'static str,
    pub reference_contract: &'static str,
    pub status: Status,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reference: Option<Result>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skipped_reference_has_no_execution_payload() {
        let result = Result::skipped();
        assert!(result.status() == Status::Skipped);
        assert_eq!(
            serde_json::to_string(&result).unwrap(),
            r#"{"status":"skipped","reason":"crate_is_not_executable","same_tcx":true}"#
        );
    }

    #[test]
    fn failure_outcomes_retain_their_exit_evidence() {
        assert_eq!(
            serde_json::to_string(&Outcome::MiriEvaluationError { exit_code: 7 }).unwrap(),
            r#"{"kind":"miri_evaluation_error","exit_code":7}"#
        );
        assert_eq!(
            serde_json::to_string(&Outcome::MiriPanicked).unwrap(),
            r#"{"kind":"miri_panicked"}"#
        );
        assert_eq!(
            serde_json::to_string(&Status::Failed).unwrap(),
            r#""failed""#
        );
        let record = Sidecar {
            snapshot_fnv1a64: "0123".into(),
            snapshot_byte_length: 4,
            snapshot_path: "snapshot.json".into(),
            last_reserved_source_alloc_id: 9,
            rustc_commit: "rustc",
            miri_commit: "miri",
            reference_contract: "same_tcx",
            status: Status::Running,
            reference: None,
        };
        assert!(
            !serde_json::to_string(&record)
                .unwrap()
                .contains("\"reference\":")
        );
    }
}
