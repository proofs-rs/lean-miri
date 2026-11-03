//! QA transport adapter. It never creates or rewrites a Miri reference sidecar.
#[path = "../typed_abi.rs"]
mod typed_abi;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args.len() != 2 { return Err("usage: prepare-abi-snapshot INPUT.json OUTPUT.json".into()); }
    if std::fs::canonicalize(&args[0])? == std::fs::canonicalize(&args[1]).unwrap_or_default() {
        return Err("input and output must be different files".into());
    }
    let mut document: serde_json::Value = serde_json::from_reader(std::io::BufReader::new(std::fs::File::open(&args[0])?))?;
    let (arguments, functions) = typed_abi::pack(&mut document)?;
    let mut writer = std::io::BufWriter::new(std::fs::File::create(&args[1])?);
    serde_json::to_writer(&mut writer, &document)?;
    std::io::Write::flush(&mut writer)?;
    eprintln!("typed ABI transport: {arguments} argument records, {functions} function records; no reference sidecar generated");
    Ok(())
}
