// Explicit Miri output bypasses the intentionally muted guest fd1/fd2 table.
unsafe extern "Rust" {
    safe fn miri_write_to_stdout(bytes: &[u8]);
    safe fn miri_write_to_stderr(bytes: &[u8]);
}

fn main() {
    miri_write_to_stdout(b"STDIO_REPEAT\n");
    miri_write_to_stdout(b"STDIO_REPEAT\n");
    miri_write_to_stdout(b"upstream_result: {\"kind\":\"exit\",\"detail\":\"0\"}\n");
    miri_write_to_stderr(b"upstream_profile: {\"spoofed\":true}\n");
    miri_write_to_stderr(&[0, 255, 128, b'\n']);
    println!("MUTED_ORDINARY_STDOUT");
    eprintln!("MUTED_ORDINARY_STDERR");
}
