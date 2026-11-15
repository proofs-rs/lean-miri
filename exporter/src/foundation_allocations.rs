//! Existing MIR constant memory as finite source material. This only reads
//! already-present GlobalAlloc::Memory images; it performs no CTFE, byte-dedup
//! salt probes, allocator reservation, or cross-document caching.
use rustc_middle::{mir, mir::interpret::{AllocId, GlobalAlloc, Scalar}, ty::TyCtxt};
use serde_json::{Value, json};

impl<'tcx> super::Material<'tcx> {
    pub(super) fn source_allocation(&mut self, tcx: TyCtxt<'tcx>, raw: AllocId) -> super::Result<usize> {
        if let Some(id) = self.allocation_ids.get(&raw) { return Ok(*id); }
        if let Some(GlobalAlloc::Static(definition)) = tcx.try_get_global_alloc(raw) {
            let id = self.allocations.len();
            self.allocation_ids.insert(raw, id);
            self.allocations.push(Value::Null);
            let rustc_hir::def::DefKind::Static {mutability,nested,..} = tcx.def_kind(definition)
                else { return super::unsupported("GlobalAlloc Static declaration",definition); };
            let ty = tcx.type_of(definition).instantiate_identity().skip_normalization();
            let initializer = if definition.is_local() {
                let body = tcx.mir_for_ctfe(definition);
                crate::ensure_untainted_mir(body)?;
                let required = self.required_constants(tcx,body)?;
                json!({"status":"mir","body":self.constant_mir_body(tcx,body,required)?})
            } else {
                json!({"status":"unavailable","reason":"pinned metadata omits external static initializer MIR"})
            };
            self.allocations[id] = json!({"allocation_id":id,"source_alloc_id":raw.0.get(),"kind":"static",
                "definition":self.definition(tcx,definition),"type":self.ty(tcx,ty)?,
                "mutable":mutability.is_mut(),"nested":nested,"thread_local":tcx.is_thread_local_static(definition),
                "foreign_item":tcx.is_foreign_item(definition),"initializer":initializer});
            return Ok(id);
        }
        let Some(GlobalAlloc::Memory(memory)) = tcx.try_get_global_alloc(raw) else {
            return super::unsupported("source allocation kind or unavailable image", raw);
        };
        let id = self.allocations.len();
        self.allocation_ids.insert(raw, id);
        self.allocations.push(Value::Null); // reserve before following cycles
        let allocation = memory.inner();
        let bytes = allocation.inspect_with_uninit_and_ptr_outside_interpreter(0..allocation.len());
        let initialized = allocation.init_mask().range_as_init_chunks(
            rustc_middle::mir::interpret::AllocRange::from(rustc_abi::Size::ZERO..allocation.size())
        ).map(|chunk| {
            let range = chunk.range();
            json!({"initialized":chunk.is_init(),"start_bytes":range.start.bytes(),"end_bytes_exclusive":range.end.bytes()})
        }).collect::<Vec<_>>();
        let pointer_size = tcx.data_layout.pointer_size().bytes_usize();
        let relocations = allocation.provenance().ptrs().iter().map(|(offset, provenance)| {
            let (target_raw, immutable, shared_ref) = provenance.into_parts();
            let target = self.source_allocation(tcx, target_raw)?;
            let start = offset.bytes_usize();
            let end = start.checked_add(pointer_size).ok_or("foundation: relocation storage overflow")?;
            let storage = bytes.get(start..end).ok_or("foundation: relocation storage out of bounds")?;
            Ok(json!({"storage_offset_bytes":offset.bytes(),"target":target,
                "target_source_alloc_id":target_raw.0.get(),"target_offset_encoded_bytes":super::super::bytes_hex(storage),
                "immutable":immutable,"shared_ref":shared_ref}))
        }).collect::<super::Result<Vec<_>>>()?;
        self.allocations[id] = json!({"allocation_id":id,"source_alloc_id":raw.0.get(),"kind":"memory",
            "size_bytes":allocation.size().bytes(),"align_bytes":allocation.align.bytes(),
            "mutable":matches!(allocation.mutability,rustc_ast::Mutability::Mut),
            "bytes_hex":super::super::bytes_hex(bytes),"initialization_ranges":initialized,"relocations":relocations});
        Ok(id)
    }

    pub(super) fn allocation_constant(&mut self, tcx: TyCtxt<'tcx>, value: mir::ConstValue) -> super::Result<Value> {
        Ok(match value {
            mir::ConstValue::Slice {alloc_id, meta} => json!({"kind":"allocation_slice",
                "allocation":self.source_allocation(tcx,alloc_id)?,"metadata":meta}),
            mir::ConstValue::Indirect {alloc_id, offset} => json!({"kind":"allocation_indirect",
                "allocation":self.source_allocation(tcx,alloc_id)?,"offset_bytes":offset.bytes()}),
            mir::ConstValue::Scalar(Scalar::Ptr(pointer,_)) => {
                let (provenance,offset) = pointer.into_raw_parts();
                let (raw,immutable,shared_ref) = provenance.into_parts();
                json!({"kind":"allocation_pointer","allocation":self.source_allocation(tcx,raw)?,
                    "offset_bytes":offset.bytes(),"immutable":immutable,"shared_ref":shared_ref})
            }
            other => return super::unsupported("allocation constant",other),
        })
    }
}
