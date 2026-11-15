//! Finite session inputs; runtime-check answers are computed by the Lean consumer.
//! Pinned rustc_session::Session::{ub_checks,contract_checks,overflow_checks}
//! reads these exact option fields (session.rs:1085-1095).
use rustc_middle::ty::TyCtxt;
use serde_json::{Value, json};

pub(super) fn export(tcx: TyCtxt<'_>) -> Value {
    let mut features = tcx.sess.internal_target_features.iter()
        .map(|name| name.as_str().to_owned()).collect::<Vec<_>>();
    features.sort();
    json!({
        "internal_target_features":features,
        "is_like_wasm":tcx.sess.target.is_like_wasm,
        "target_arch":tcx.sess.target.arch.to_string(),
        "debug_assertions":tcx.sess.opts.debug_assertions,
        "ub_checks":tcx.sess.opts.unstable_opts.ub_checks,
        "contract_checks":tcx.sess.opts.unstable_opts.contract_checks,
        "overflow_checks":tcx.sess.opts.cg.overflow_checks,
    })
}
