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
        "exporter must be built by the exact pinned rustc"
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
