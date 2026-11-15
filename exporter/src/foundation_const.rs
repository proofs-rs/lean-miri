//! Finite required-constant source material; never invokes rustc CTFE.
//!
//! Pinned rustc_middle::mir::Body::required_consts requires even unreachable
//! syntactic constants to evaluate before entering a frame (rustc_const_eval
//! interpret/stack.rs). Keep the entire ordered list. Unevaluated definitions,
//! promoted allocations and pointer constants remain unsupported rather than
//! replacing their evaluation with successful evidence.
use rustc_middle::{mir, ty::TyCtxt};
use serde_json::Value;

impl<'tcx> super::Material<'tcx> {
    pub(super) fn required_constants(
        &mut self,
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
    ) -> super::Result<Vec<Value>> {
        let constants = body.required_consts.as_ref()
            .ok_or("foundation: uncomputed required constants")?;
        constants.iter().map(|constant| {
            self.operand(tcx, &mir::Operand::Constant(Box::new(*constant)))
        }).collect()
    }
}
