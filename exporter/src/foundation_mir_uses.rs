//! Raw generic optimized-MIR parameter-use syntax for selected ABI declarations.
//! Mirrors the MIR Visitor traversal, without deducing attributes or usage bits.
use super::*;
use rustc_middle::mir::visit::{Visitor, PlaceContext};
fn place(source: mir::Place<'_>) -> Value {
    let first = source.projection.first().map(|projection| if matches!(projection,mir::ProjectionElem::Deref) {"deref"} else {"other"});
    json!({"local":source.local.as_usize(),"first_projection":first})
}
struct Uses { argument_count:usize, events:Vec<Value> }
impl Uses {
    fn push(&mut self, location:mir::Location, kind:Value) {
        self.events.push(json!({"block":location.block.as_usize(),"statement":location.statement_index,"kind":kind}));
    }
}
impl<'tcx> Visitor<'tcx> for Uses {
    fn visit_place(&mut self, source:&mir::Place<'tcx>, context:PlaceContext, location:mir::Location) {
        if source.local.as_usize() > self.argument_count {return;}
        let context = match context {
            PlaceContext::NonUse(_) => json!({"kind":"non_use"}),
            PlaceContext::MutatingUse(context) => json!({"kind":"mutating","context":format!("{context:?}")}),
            PlaceContext::NonMutatingUse(context) => json!({"kind":"non_mutating","context":format!("{context:?}")}),
        };
        self.push(location,json!({"kind":"place","place":place(*source),"context":context}));
    }
    fn visit_terminator(&mut self, terminator:&mir::Terminator<'tcx>, location:mir::Location) {
        match &terminator.kind {
            mir::TerminatorKind::Call {args,..} => for argument in args {
                if let mir::Operand::Move(source) = argument.node {
                    if source.local.as_usize() <= self.argument_count {
                        self.push(location,json!({"kind":"call_move","place":place(source)}));
                    }
                }
            },
            mir::TerminatorKind::TailCall {..} => self.push(location,json!({"kind":"tail_call"})),
            _=>{},
        }
        self.super_terminator(terminator,location);
    }
}
impl<'tcx> Material<'tcx> {
    pub(super) fn mir_use_source(&mut self,tcx:TyCtxt<'tcx>,headers:&[Value]) -> Result<Value> {
        let mut declarations = Vec::new(); let mut seen=Vec::new();
        for header in headers {
            let index=header["definition"].as_u64().ok_or("missing ABI use owner")? as usize;
            let (&definition,_)=self.def_ids.iter().find(|(_,id)|**id==index).ok_or("missing ABI use raw owner")?;
            if seen.contains(&definition) {continue;} seen.push(definition);
            let body = if tcx.is_mir_available(definition) {
                let body=tcx.optimized_mir(definition);
                if body.source.instance != ty::InstanceKind::Item(definition) || body.source.promoted.is_some() {return unsupported("ABI use MIR source identity",body.source);}
                super::super::ensure_untainted_mir(body)?;
                let mut visitor=Uses {argument_count:body.arg_count,events:Vec::new()};
                visitor.visit_body(body);
                json!({"argument_count":body.arg_count,"spread_argument":body.spread_arg.map(|local|local.as_usize()),
                    "phase":crate::mir_phase_json(body.phase),"source_definition":index,
                    "block_statement_counts":body.basic_blocks.iter().map(|block|block.statements.len()).collect::<Vec<_>>(),
                    "event_count":visitor.events.len(),"events":visitor.events})
            } else {Value::Null};
            let compilation = if definition.is_local() {
                Some((tcx.sess.opts.optimize,tcx.sess.opts.incremental.is_some(),Some(tcx.lang_items().freeze_trait().is_some())))
            } else {
                #[cfg(feature = "allocation-identity-snapshot")]
                {
                    use rustc_session::config::OptLevel;
                    let raw=tcx.lean_miri_defining_compilation(definition.krate);
                    let optimization=match raw & 7 {0=>OptLevel::No,1=>OptLevel::Less,2=>OptLevel::More,
                        3=>OptLevel::Aggressive,4=>OptLevel::Size,5=>OptLevel::SizeMin,
                        _=>return unsupported("defining optimization source encoding",raw)};
                    if raw & !63 != 0 {return unsupported("defining option source encoding",raw);}
                    Some((optimization,raw & 8 != 0,if raw & 32 != 0 {Some(raw & 16 != 0)} else {None}))
                }
                #[cfg(not(feature = "allocation-identity-snapshot"))]
                {None}
            };
            let compilation=compilation.map(|(optimization,incremental,freeze)|json!({"optimization":format!("{optimization:?}"),"incremental":incremental,"freeze_lang_item_present":freeze}));
            declarations.push(json!({"definition":index,"body":body,"compilation":compilation,"always_const":matches!(tcx.constness(definition),rustc_hir::Constness::Const {always:true})}));
        }
        Ok(json!({"declarations":declarations}))
    }
}
