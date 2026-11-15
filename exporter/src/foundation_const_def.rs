//! Unevaluated source keys and existing static initializer syntax.
//! Concrete evaluated-value witnesses are captured separately at export time.
use super::*;
#[path = "foundation_const_aggregate.rs"]
mod aggregate_material;

impl<'tcx> Material<'tcx> {
    pub(super) fn constant_definition(&mut self, tcx: TyCtxt<'tcx>, value: mir::UnevaluatedConst<'tcx>) -> Result<Value> {
        if !self.observed_constants.contains(&value) {self.observed_constants.push(value);}
        // Preserve the original unresolved key. The source body is not a
        // license to select an impl or reimplement CTFE in the consumer.
        Ok(json!({"kind":"unevaluated","definition":self.definition(tcx,value.def),
            "arguments":self.args(tcx,value.args)?,"promoted":value.promoted.map(|id|id.as_u32())}))
    }
    pub(super) fn constant_mir_body(&mut self, tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>, required: Vec<Value>) -> Result<Value> {
        let locals = body.local_decls.iter().map(|local|self.ty(tcx,local.ty)).collect::<Result<Vec<_>>>()?;
        let blocks = body.basic_blocks.iter().map(|block| {
            if block.is_cleanup { return unsupported("const cleanup block", block); }
            let statements = block.statements.iter().map(|statement| Ok(match &statement.kind {
                mir::StatementKind::Assign(assignment) => json!({"kind":"assign",
                    "place":self.place(tcx,assignment.0)?,"value":self.constant_source_rvalue(tcx,&assignment.1)?}),
                mir::StatementKind::StorageLive(local) => json!({"kind":"storage_live","local":local.as_u32()}),
                mir::StatementKind::StorageDead(local) => json!({"kind":"storage_dead","local":local.as_u32()}),
                mir::StatementKind::Nop => json!({"kind":"nop"}),
                other => return unsupported("const MIR statement",other),
            })).collect::<Result<Vec<_>>>()?;
            let terminator = match &block.terminator().kind {
                mir::TerminatorKind::Return => json!({"kind":"return"}),
                mir::TerminatorKind::Goto {target,..} => json!({"kind":"goto","target":target.as_u32()}),
                mir::TerminatorKind::SwitchInt {discr,targets} => json!({"kind":"switch_int",
                    "operand":self.operand(tcx,discr)?,"targets":targets.iter().map(|(value,target)|json!({"value":value.to_string(),"target":target.as_u32()})).collect::<Vec<_>>(),
                    "otherwise":targets.otherwise().as_u32()}),
                mir::TerminatorKind::Assert {cond,expected,msg,target,unwind} => {
                    if !matches!(unwind,mir::UnwindAction::Continue) { return unsupported("const assert unwind",unwind); }
                    let mir::AssertKind::Overflow(operator,left,right) = &**msg
                        else { return unsupported("const assert message",msg); };
                    json!({"kind":"assert","condition":self.operand(tcx,cond)?,"expected":expected,
                        "target":target.as_u32(),"unwind":"continue","message":{"kind":"overflow",
                            "operator":crate::binop_name(*operator),"left":self.operand(tcx,left)?,"right":self.operand(tcx,right)?}})
                },
                other => return unsupported("const MIR terminator",other),
            };
            Ok(json!({"statements":statements,"terminator":terminator}))
        }).collect::<Result<Vec<_>>>()?;
        Ok(json!({"locals":locals,"required_consts":required,"blocks":blocks}))
    }

}
