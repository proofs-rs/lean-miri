//! Aggregate CTFE MIR syntax. No const evaluation or allocation identity query.
use super::*;
impl<'tcx> Material<'tcx> {
    pub(super) fn constant_source_rvalue(&mut self, tcx: TyCtxt<'tcx>, value: &mir::Rvalue<'tcx>) -> Result<Value> {
        match value {
            mir::Rvalue::Aggregate(kind, operands) => {
                let mir::AggregateKind::Adt(definition,variant,args,annotation,active) = &**kind
                    else {return unsupported("const aggregate kind",kind)};
                let adt=tcx.adt_def(*definition);
                if !adt.is_struct() || variant.as_u32()!=0 || !args.is_empty() || annotation.is_some() || active.is_some() {
                    return unsupported("const aggregate declaration",kind);
                }
                Ok(json!({"kind":"aggregate_adt","definition":self.definition(tcx,*definition),
                    "variant":variant.as_u32(),"arguments":[],
                    "operands":operands.iter().map(|operand|self.operand(tcx,operand)).collect::<Result<Vec<_>>>()?}))
            },
            mir::Rvalue::Cast(mir::CastKind::IntToInt,operand,target) => Ok(json!({
                "kind":"integer_cast","operand":self.operand(tcx,operand)?,"target_type":self.ty(tcx,*target)?})),
            other => self.rvalue(tcx,other),
        }
    }
}
