//! Observation-only allocator state. No allocation query, reservation, or salt probing.
use super::*;

impl<'tcx> Material<'tcx> {
    #[cfg(not(feature = "allocation-identity-snapshot"))]
    pub(super) fn allocation_identity_source(&mut self, _tcx: TyCtxt<'tcx>) -> Result<Value> {
        Ok(Value::Null)
    }

    #[cfg(feature = "allocation-identity-snapshot")]
    pub(super) fn allocation_identity_source(&mut self, tcx: TyCtxt<'tcx>) -> Result<Value> {
        use rustc_middle::mir::interpret::GlobalAlloc;
        fn kind(global: &GlobalAlloc<'_>) -> &'static str {
            match global {
                GlobalAlloc::Memory(_) => "memory",
                GlobalAlloc::Static(_) => "static",
                GlobalAlloc::Function { .. } => "function",
                GlobalAlloc::VTable(..) => "vtable",
                GlobalAlloc::TypeId { .. } => "type_id",
            }
        }
        if tcx.sess.opts.jobs.frontend.is_some_and(|jobs| jobs.get() > 1) {
            return Err("foundation: allocation identity snapshot requires single-threaded frontend".into());
        }
        // The driver runs after analysis with one compiler thread. This copies
        // all actual entries, including salts not selected by this exporter.
        let (frontier, mut globals, mut dedup) = tcx.lean_miri_complete_allocation_identity_snapshot();
        globals.sort_by_key(|(id, _)| id.0.get());
        dedup.sort_by_key(|(_, salt, id)| (id.0.get(), *salt));
        let global_rows = globals.iter().map(|(id, global)| json!({
            "source_alloc_id":id.0.get(), "kind":kind(global)
        })).collect::<Vec<_>>();
        let mut dedup_rows = Vec::with_capacity(dedup.len());
        for (global, salt, id) in &dedup {
            let key = match global {
                GlobalAlloc::VTable(ty, predicates) => {
                    let type_id = self.ty(tcx, *ty)?;
                    let dynamic = ty::Ty::new_dynamic(tcx, predicates, tcx.lifetimes.re_erased);
                    json!({"kind":"vtable", "type":type_id, "dynamic_type":self.ty(tcx,dynamic)?})
                }
                _ => json!({"kind":kind(global)}),
            };
            dedup_rows.push(json!({"source_alloc_id":id.0.get(),"salt":salt,"key":key}));
        }
        let (after_frontier, mut after_globals, mut after_dedup) = tcx.lean_miri_complete_allocation_identity_snapshot();
        after_globals.sort_by_key(|(id, _)| id.0.get());
        after_dedup.sort_by_key(|(_, salt, id)| (id.0.get(), *salt));
        if frontier != after_frontier || globals != after_globals || dedup != after_dedup {
            return Err("foundation: allocation identity changed while serializing source witness".into());
        }
        Ok(json!({"frontier":frontier,"globals":global_rows,"dedup":dedup_rows}))
    }
}
