//! Exact pinned source-MIR selection for CompileTimeMachine::load_mir.
//! This captures source bodies only. It never evaluates a constant, normalizes
//! arguments, computes layouts, or creates compiler allocations. The CTFE
//! evaluator must separately handle body.tainted_by_errors before interpretation.
use rustc_middle::{mir,ty::{self,TyCtxt}};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum Role { Runtime, Ctfe }
impl Role {
    pub(super) fn wire(self)->&'static str {
        match self {Self::Runtime=>"runtime",Self::Ctfe=>"ctfe"}
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct Key<'tcx> {
    pub instance:ty::Instance<'tcx>,
    pub promoted:Option<mir::Promoted>,
    pub role:Role,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct TemplateKey {
    pub definition:rustc_hir::def_id::DefId,
    pub promoted:Option<mir::Promoted>,
    pub role:Role,
}

pub(super) fn load<'tcx>(
    tcx:TyCtxt<'tcx>, instance:ty::InstanceKind<'tcx>, promoted:Option<mir::Promoted>,
) -> &'tcx mir::Body<'tcx> {
    if let Some(index)=promoted {
        &tcx.promoted_mir(instance.def_id())[index]
    } else {
        match instance {
            ty::InstanceKind::Item(definition)=>tcx.mir_for_ctfe(definition),
            _=>tcx.instance_mir(instance),
        }
    }
}
