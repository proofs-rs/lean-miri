//! Finite compiler invocation and consumed-artifact identity, not query answers.
use rustc_middle::ty::TyCtxt;

pub(super) fn capture(
    tcx: TyCtxt<'_>, rustc_version: &str, rustc_args: &[String],
) -> Result<super::Producer, String> {
    if rustc_version.is_empty() || rustc_args.is_empty() {
        return Err("foundation: missing validated compiler invocation evidence".into());
    }
    // Same artifact hashing and effective session flags as schema12. Hashes
    // identify consumed files; they do not certify an independently pinned
    // reference sysroot. Propagate every filesystem/hash failure.
    Ok(super::Producer {
        miri_commit: super::MIRI_COMMIT,
        rustc_commit: super::EXPECTED_RUSTC_COMMIT,
        rustc_version: rustc_version.to_owned(),
        target_triple: tcx.sess.opts.target_triple.to_string(),
        input_settings: super::producer::evidence(tcx, rustc_args)?,
    })
}
