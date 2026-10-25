use std::path::Path;
use std::process::Command;

fn run(program: &str, args: &[&str]) {
    let exporter = Path::new(env!("CARGO_MANIFEST_DIR"));
    let root = exporter.parent().unwrap();
    let mut command = Command::new(program);
    command.args(args).current_dir(exporter);
    // Cargo supplies the executable for the selected profile/target directory.
    // Never build recursively from a fixture running under cargo test.
    command.env("EXPORTER_BIN", env!("CARGO_BIN_EXE_lean-miri-mir-exporter"));
    for (name, default) in [
        ("RUSTUP_HOME", root.join(".rustup")),
        ("CARGO_HOME", root.join(".cargo")),
        ("MIRI_SYSROOT", root.join("scratch/miri-sysroot")),
    ] {
        if std::env::var_os(name).is_none() {
            command.env(name, default);
        }
    }
    let output = command.output().unwrap_or_else(|error| {
        panic!("cannot run {program} {args:?}: {error}; install bash and Python 3")
    });
    assert!(
        output.status.success(),
        "{program} {args:?} failed ({}):\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn python_unit_tests() {
    run(
        "python3",
        &[
            "-m",
            "unittest",
            "discover",
            "-s",
            "tests",
            "-p",
            "test_*.py",
        ],
    );
}

#[test]
fn mir_fixtures() {
    run("bash", &["test-fixture.sh"]);
}

#[test]
fn variadic_fixture() {
    run("bash", &["test-variadic-fixture.sh"]);
}

#[test]
fn call_transfer_fixture() {
    run("bash", &["test-call-transfer-fixture.sh"]);
}

#[test]
fn instance_mir_ctfe_fixture() {
    run("bash", &["test-instance-mir-ctfe-fixture.sh"]);
}
