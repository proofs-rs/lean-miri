//! Pattern-type constraints are source structure, never erased into base types.
use super::*;
impl<'tcx> Material<'tcx> {
    pub(super) fn pattern_type(&mut self, tcx: TyCtxt<'tcx>, base: ty::Ty<'tcx>, pattern: ty::Pattern<'tcx>) -> Result<Value> {
        let pattern = match *pattern.0 {
            ty::PatternKind::NotNull => json!({"kind":"not_null"}),
            ty::PatternKind::Range {start,end} => {
                // Preserve the declaration/arguments of unevaluated bounds.
                // Capturing a pattern never evaluates CTFE or invents a range.
                let mut bound = |value: ty::Const<'tcx>| -> Result<Value> {
                    if let ty::ConstKind::Alias(rigidity,value) = value.kind() {
                        let (kind,definition) = match value.kind {
                            ty::AliasConstKind::Projection {def_id} => ("projection",def_id),
                            ty::AliasConstKind::InherentSelf {def_id} => ("inherent_self",def_id),
                            ty::AliasConstKind::InherentImpl {def_id} => ("inherent_impl",def_id),
                            ty::AliasConstKind::Free {def_id} => ("free",def_id),
                            ty::AliasConstKind::Anon {def_id} => ("anonymous",def_id),
                        };
                        Ok(json!({"kind":"alias","alias_kind":kind,
                            "rigidity":match rigidity {ty::IsRigid::Yes=>"rigid",ty::IsRigid::No=>"not_rigid"},
                            "definition":self.definition(tcx,definition),"arguments":self.args(tcx,value.args)?}))
                    } else { self.constant(tcx,value) }
                };
                json!({"kind":"range","start":bound(start)?,"end":bound(end)?})
            },
            other => return unsupported("source type pattern",other),
        };
        Ok(json!({"kind":"pattern_type","base":self.ty(tcx,base)?,"pattern":pattern}))
    }
}
