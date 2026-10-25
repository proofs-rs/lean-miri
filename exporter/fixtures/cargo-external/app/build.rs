use std::env;
use std::process::Command;

fn main() {
    // cargo-miri uses itself as both RUSTC and RUSTC_WRAPPER because build
    // scripts sometimes call the RUSTC environment value directly. Verify our
    // wrapper preserves a direct rustc version query through the pinned driver.
    let rustc = env::var_os("RUSTC").expect("Cargo must provide RUSTC to build scripts");
    let output = Command::new(rustc)
        .arg("--version")
        .arg("--verbose")
        .output()
        .expect("invoke configured RUSTC");
    assert!(output.status.success(), "configured RUSTC query failed");
    let version = String::from_utf8(output.stdout).expect("rustc version output is UTF-8");
    assert!(
        version.contains("commit-hash: 8144389c895da997dbdecaa635e41d6a50be6ffd"),
        "build script observed a different rustc revision: {version}"
    );
}
