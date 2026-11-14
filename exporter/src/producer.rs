//! Input identity for compiler-produced MIR. Hashes identify actual consumed
//! artifacts; a directory spelling or target triple never certifies a Miri
//! sysroot. Consumers must compare against their pinned reference manifest.
use rustc_middle::ty::TyCtxt;
use std::fs;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

#[derive(serde::Serialize)]
pub(super) struct Artifact {
    path: String,
    sha256: String,
    size_bytes: u64,
    crate_name: String,
    kind: String,
    within_sysroot: bool,
    sysroot_relative_path: Option<String>,
}
#[derive(serde::Serialize)]
pub(super) struct Evidence {
    sysroot_path: String,
    hash_algorithm: &'static str,
    sysroot_manifest_sha256: String,
    loaded_artifacts_manifest_sha256: String,
    artifacts: Vec<Artifact>,
    requested_cfg_miri: bool,
    miri_default_args: &'static [&'static str],
    rustc_args: Vec<String>,
    effective_panic_strategy: &'static str,
    mir_opt_level: Option<usize>,
    mir_enable_passes: Vec<(String, bool)>,
    mir_preserve_ub: bool,
    extra_const_ub_checks: bool,
    always_encode_mir: bool,
    deduplicate_diagnostics: bool,
    qualification: &'static str,
}
// Alphabetical field order preserves the existing manifest hash input exactly.
#[derive(serde::Serialize)]
struct ManifestKey<'a> {
    crate_name: &'a str,
    kind: &'a str,
    sha256: &'a str,
    size_bytes: u64,
}
#[derive(serde::Serialize)]
struct SysrootKey<'a> {
    crate_name: &'a str,
    kind: &'a str,
    relative_path: Option<&'a str>,
    sha256: &'a str,
    size_bytes: u64,
}
pub const MIRI_DEFAULT_ARGS: &[&str] = &[
    "--cfg=miri",
    "-Zalways-encode-mir",
    "-Zextra-const-ub-checks",
    "-Zmir-preserve-ub",
    "-Zmir-opt-level=0",
    "-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums",
    "-Zmir-enable-passes=-ReferencePropagation,-GVN",
    "-Zdeduplicate-diagnostics=no",
];
fn digest_output(output: std::process::Output) -> Result<String, String> {
    if !output.status.success() {
        return Err(format!(
            "sha256sum failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let output = String::from_utf8(output.stdout).map_err(|e| e.to_string())?;
    let digest = output
        .split_whitespace()
        .next()
        .ok_or("sha256sum returned no digest")?;
    if digest.len() != 64 || !digest.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("invalid sha256sum output".into());
    }
    Ok(digest.to_ascii_lowercase())
}
pub(super) fn hash_file(path: &Path) -> Result<(String, u64), String> {
    let file = fs::File::open(path).map_err(|e| e.to_string())?;
    let before = file.metadata().map_err(|e| e.to_string())?;
    let after_file = file.try_clone().map_err(|e| e.to_string())?;
    let output = Command::new("sha256sum")
        .stdin(Stdio::from(file))
        .output()
        .map_err(|e| e.to_string())?;
    let digest = digest_output(output)?;
    let after = after_file.metadata().map_err(|e| e.to_string())?;
    if before.len() != after.len() || before.modified().ok() != after.modified().ok() {
        return Err("artifact changed while hashing".into());
    }
    Ok((digest, after.len()))
}
fn hash_bytes(bytes: &[u8]) -> Result<String, String> {
    let mut child = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| e.to_string())?;
    child
        .stdin
        .take()
        .ok_or("sha256sum stdin missing")?
        .write_all(bytes)
        .map_err(|e| e.to_string())?;
    digest_output(child.wait_with_output().map_err(|e| e.to_string())?)
}
fn artifact(path: &Path, crate_name: &str, kind: &str, sysroot: &Path) -> Result<Artifact, String> {
    let canonical =
        fs::canonicalize(path).map_err(|error| format!("{}: {error}", path.display()))?;
    let text = canonical.to_str().ok_or("artifact path is not UTF-8")?;
    let (hash, size) =
        hash_file(&canonical).map_err(|error| format!("{}: {error}", path.display()))?;
    Ok(Artifact {
        path: text.to_owned(),
        sha256: hash,
        size_bytes: size,
        crate_name: crate_name.to_owned(),
        kind: kind.to_owned(),
        within_sysroot: canonical.starts_with(sysroot),
        sysroot_relative_path: canonical
            .strip_prefix(sysroot)
            .ok()
            .and_then(|path| path.to_str())
            .map(str::to_owned),
    })
}

pub fn evidence(tcx: TyCtxt<'_>, rustc_args: &[String]) -> Result<Evidence, String> {
    let sysroot = tcx.sess.opts.sysroot.path();
    let canonical =
        fs::canonicalize(sysroot).map_err(|error| format!("sysroot canonicalization: {error}"))?;
    let mut artifacts = Vec::new();
    let root = canonical.as_path();
    for &number in tcx.crates(()) {
        let source = tcx.used_crate_source(number);
        let name = tcx.crate_name(number).to_string();
        for (kind, path) in [
            ("rlib", &source.rlib),
            ("rmeta", &source.rmeta),
            ("dylib", &source.dylib),
            ("sdylib_interface", &source.sdylib_interface),
        ] {
            if let Some(path) = path {
                artifacts.push(artifact(path, &name, kind, root)?);
            }
        }
    }
    artifacts.sort_by(|a, b| a.path.cmp(&b.path).then(a.kind.cmp(&b.kind)));

    let sysroot_entries = artifacts
        .iter()
        .filter(|v| v.within_sysroot)
        .map(|v| SysrootKey {
            crate_name: &v.crate_name,
            kind: &v.kind,
            relative_path: v.sysroot_relative_path.as_deref(),
            sha256: &v.sha256,
            size_bytes: v.size_bytes,
        })
        .collect::<Vec<_>>();
    let mut loaded_entries = artifacts
        .iter()
        .map(|v| ManifestKey {
            crate_name: &v.crate_name,
            kind: &v.kind,
            sha256: &v.sha256,
            size_bytes: v.size_bytes,
        })
        .map(|key| serde_json::to_string(&key).map_err(|e| e.to_string()))
        .collect::<Result<Vec<_>, _>>()?;
    loaded_entries.sort();
    let manifest = hash_bytes(&serde_json::to_vec(&sysroot_entries).map_err(|e| e.to_string())?)?;
    let loaded_manifest = hash_bytes(format!("[{}]", loaded_entries.join(",")).as_bytes())?;
    let args = rustc_args.to_vec();
    let cfg_miri = args.iter().any(|v| v == "--cfg=miri")
        || args.windows(2).any(|v| v[0] == "--cfg" && v[1] == "miri");
    let panic = match tcx.sess.panic_strategy() {
        rustc_target::spec::PanicStrategy::Unwind => "unwind",
        rustc_target::spec::PanicStrategy::Abort => "abort",
        rustc_target::spec::PanicStrategy::ImmediateAbort => "immediate-abort",
    };
    Ok(Evidence {
        sysroot_path: root.to_string_lossy().into_owned(),
        hash_algorithm: "sha256",
        sysroot_manifest_sha256: manifest,
        loaded_artifacts_manifest_sha256: loaded_manifest,
        artifacts,
        requested_cfg_miri: cfg_miri,
        miri_default_args: MIRI_DEFAULT_ARGS,
        rustc_args: args,
        effective_panic_strategy: panic,
        mir_opt_level: tcx.sess.opts.unstable_opts.mir_opt_level,
        mir_enable_passes: tcx.sess.opts.unstable_opts.mir_enable_passes.clone(),
        mir_preserve_ub: tcx.sess.opts.unstable_opts.mir_preserve_ub,
        extra_const_ub_checks: tcx.sess.opts.unstable_opts.extra_const_ub_checks,
        always_encode_mir: tcx.sess.opts.unstable_opts.always_encode_mir,
        deduplicate_diagnostics: tcx.sess.opts.unstable_opts.deduplicate_diagnostics,
        qualification: "Hashes identify consumed artifacts; Miri sysroot equivalence requires matching an independently pinned reference manifest.",
    })
}

#[derive(serde::Serialize)]
pub(super) struct PointerSpec {
    pub pointer_size_bytes: u64,
    pub pointer_align_bytes: u64,
    pub pointer_offset_bytes: u64,
    pub is_fat: bool,
}
#[derive(serde::Serialize)]
pub(super) struct AddressSpaceInfo {
    pub address_space: u32,
    pub spec: PointerSpec,
    pub object_size_bound_bytes: Option<u64>,
}
#[derive(serde::Serialize)]
pub(super) struct VectorAlign {
    pub size_bytes: u64,
    pub align_bytes: u64,
}
#[derive(serde::Serialize)]
pub(super) struct TargetDataLayout {
    pub evidence_path: &'static str,
    pub llvm_data_layout: String,
    pub private_inventory_evidence: &'static str,
    pub alignment_evidence: &'static str,
    pub endian: &'static str,
    pub pointer_width_bits: u64,
    pub object_size_bound_bytes: Option<u64>,
    pub i1_align_bytes: u64,
    pub i8_align_bytes: u64,
    pub i16_align_bytes: u64,
    pub i32_align_bytes: u64,
    pub i64_align_bytes: u64,
    pub i128_align_bytes: u64,
    pub f16_align_bytes: u64,
    pub f32_align_bytes: u64,
    pub f64_align_bytes: u64,
    pub f128_align_bytes: u64,
    pub aggregate_align_bytes: u64,
    pub vector_align: Vec<VectorAlign>,
    pub default_address_space: u32,
    pub default_address_space_pointer_spec: PointerSpec,
    pub address_space_info: Vec<AddressSpaceInfo>,
    pub instruction_address_space: u32,
    pub c_enum_min_size: &'static str,
}
