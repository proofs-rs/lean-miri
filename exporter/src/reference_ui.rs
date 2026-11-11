//! Opt-in UI configuration; flag order follows pinned src/bin/miri.rs:471–559.
pub(super) fn apply_flags(config: &mut miri::MiriConfig, flags: &[String]) -> Result<(), String> {
    for flag in flags {
        match flag.as_str() {
            "-Zmiri-tree-borrows" => config.borrow_tracker = Some(miri::BorrowTrackerMethod::TreeBorrows(
                miri::TreeBorrowsParams { precise_interior_mut: true, implicit_writes: false })),
            "-Zmiri-disable-stacked-borrows" => config.borrow_tracker = None,
            "-Zmiri-tree-borrows-implicit-writes" | "-Zmiri-tree-borrows-no-precise-interior-mut" => {
                let Some(miri::BorrowTrackerMethod::TreeBorrows(params)) = &mut config.borrow_tracker else {
                    return Err(format!("{flag} requires Tree Borrows"));
                };
                if flag == "-Zmiri-tree-borrows-implicit-writes" { params.implicit_writes = true; }
                else { params.precise_interior_mut = false; }
            }
            "-Zmiri-disable-validation" => config.validation = miri::ValidationMode::No,
            "-Zmiri-recursive-validation" => config.validation = miri::ValidationMode::Deep,
            "-Zmiri-disable-alignment-check" => config.check_alignment = miri::AlignmentCheck::None,
            "-Zmiri-symbolic-alignment-check" => config.check_alignment = miri::AlignmentCheck::Symbolic,
            "-Zmiri-strict-provenance" => config.provenance_mode = miri::ProvenanceMode::Strict,
            "-Zmiri-permissive-provenance" => config.provenance_mode = miri::ProvenanceMode::Permissive,
            "-Zmiri-ignore-leaks" => { config.ignore_leaks = true; config.collect_leak_backtraces = false; }
            "-Zmiri-fixed-schedule" => config.fixed_scheduling = true,
            "-Zmiri-disable-data-race-detector" => { config.data_race_detector = false; config.weak_memory_emulation = false; }
            "-Zmiri-deterministic-concurrency" => {
                config.fixed_scheduling = true;
                config.address_reuse_cross_thread_rate = 0.0;
                config.cmpxchg_weak_failure_rate = 0.0;
                config.weak_memory_emulation = false;
            }
            other => return Err(format!("unsupported UI runtime flag: {other}")),
        }
    }
    Ok(())
}

pub(super) fn configure(config: &mut miri::MiriConfig) -> Result<bool, String> {
    let flags = match std::env::var("LEAN_MIRI_REFERENCE_UI_FLAGS_JSON") {
        Ok(raw) => serde_json::from_str::<Vec<String>>(&raw)
            .map_err(|error| format!("invalid LEAN_MIRI_REFERENCE_UI_FLAGS_JSON: {error}"))?,
        Err(std::env::VarError::NotPresent) => Vec::new(),
        Err(error) => return Err(format!("cannot read UI runtime flags: {error}")),
    };
    apply_flags(config, &flags)?;
    let empty = match std::env::var("LEAN_MIRI_REFERENCE_EMPTY_ENV") {
        Ok(value) if value == "1" => true,
        Ok(value) if value == "0" || value.is_empty() => false,
        Err(std::env::VarError::NotPresent) => false,
        _ => return Err("LEAN_MIRI_REFERENCE_EMPTY_ENV must be 0 or 1".into()),
    };
    config.env = if empty { Vec::new() } else { std::env::vars_os().collect() };
    if empty { config.seed = Some(0); }
    Ok(empty)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn flags(values: &[&str]) -> Vec<String> { values.iter().map(|value| (*value).into()).collect() }

    #[test]
    fn tree_selection_resets_parameters_and_rejects_disabled_tracking() {
        let mut config = miri::MiriConfig::default();
        apply_flags(&mut config, &flags(&["-Zmiri-tree-borrows", "-Zmiri-tree-borrows-implicit-writes",
            "-Zmiri-tree-borrows-no-precise-interior-mut", "-Zmiri-tree-borrows"])).unwrap();
        let Some(miri::BorrowTrackerMethod::TreeBorrows(params)) = &config.borrow_tracker else { panic!("Tree Borrows required") };
        assert!(params.precise_interior_mut);
        assert!(!params.implicit_writes);
        assert!(apply_flags(&mut config, &flags(&["-Zmiri-disable-stacked-borrows",
            "-Zmiri-tree-borrows-implicit-writes"])).is_err());
        assert!(apply_flags(&mut config, &flags(&["-Zmiri-unknown"])).is_err());
    }

    #[test]
    fn deterministic_concurrency_preserves_race_detection_and_leak_flags_are_coupled() {
        let mut config = miri::MiriConfig::default();
        apply_flags(&mut config, &flags(&["-Zmiri-deterministic-concurrency", "-Zmiri-ignore-leaks"])).unwrap();
        assert!(config.data_race_detector);
        assert!(config.fixed_scheduling);
        assert!(!config.weak_memory_emulation);
        assert_eq!(config.address_reuse_cross_thread_rate, 0.0);
        assert_eq!(config.cmpxchg_weak_failure_rate, 0.0);
        assert!(config.ignore_leaks);
        assert!(!config.collect_leak_backtraces);
    }
}
