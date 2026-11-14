use std::process::Command;

const PINNED_COMMIT: &str = "8144389c895da997dbdecaa635e41d6a50be6ffd";

fn output(command: &mut Command, description: &str) -> String {
    let result = command
        .output()
        .unwrap_or_else(|error| panic!("cannot run {description}: {error}"));
    if !result.status.success() {
        panic!(
            "{description} failed: {}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
    String::from_utf8(result.stdout)
        .unwrap_or_else(|error| panic!("{description} returned non-UTF8 output: {error}"))
}

fn main() {
    println!("cargo:rerun-if-env-changed=RUSTC");
    println!("cargo:rerun-if-env-changed=LEAN_MIRI_INITIAL_SNAPSHOT_DRIVER");
    println!("cargo:rerun-if-env-changed=LEAN_MIRI_INITIAL_SNAPSHOT_DRIVER_SHA256");
    if std::env::var_os("CARGO_FEATURE_CTFE_INITIAL_GLOBAL_SNAPSHOT").is_some() {
        let driver=std::fs::canonicalize(std::env::var_os("LEAN_MIRI_INITIAL_SNAPSHOT_DRIVER")
            .expect("audited snapshot feature requires exact driver path")).expect("audited driver path must exist");
        let expected=std::env::var("LEAN_MIRI_INITIAL_SNAPSHOT_DRIVER_SHA256").expect("audited snapshot feature requires exact driver SHA256");
        assert!(expected.len()==64 && expected.bytes().all(|byte|byte.is_ascii_hexdigit()),"invalid audited driver SHA256");
        let observed=output(Command::new("sha256sum").arg(&driver),"audited compiler driver SHA256");
        assert_eq!(observed.split_whitespace().next(),Some(expected.as_str()),"audited compiler driver changed");
        println!("cargo:rustc-env=LEAN_MIRI_INITIAL_SNAPSHOT_DRIVER={}",driver.display());
        println!("cargo:rustc-env=LEAN_MIRI_INITIAL_SNAPSHOT_DRIVER_SHA256={expected}");
    }
    let rustc = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let version = output(
        Command::new(&rustc).arg("--version").arg("--verbose"),
        "build rustc --version --verbose",
    );
    let commit = version
        .lines()
        .find_map(|line| line.strip_prefix("commit-hash: "))
        .unwrap_or_else(|| panic!("build rustc did not report commit-hash: {version}"));
    assert_eq!(
        commit, PINNED_COMMIT,
        "exporter must be built by the exact pinned rustc; from the repository root run bash tools/setup-rustc-exporter.sh, then cargo +miri-exporter-8144389c895d test --locked --manifest-path exporter/Cargo.toml (see docs/development.md)"
    );
    let sysroot = output(
        Command::new(&rustc).arg("--print").arg("sysroot"),
        "rustc --print sysroot",
    );
    println!(
        "cargo:rustc-env=LEAN_MIRI_PINNED_RUSTC_SYSROOT={}",
        sysroot.trim()
    );
    println!("cargo:rustc-env=LEAN_MIRI_PINNED_RUSTC_COMMIT={PINNED_COMMIT}");
}
