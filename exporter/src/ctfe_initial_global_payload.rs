//! WIP encoder: frozen allocation payloads only, with explicit symbolic encoders.
//! Exact-representation candidate; requires freshly rebuilt safe mask/provenance accessors.
//! Not production-promoted before actual counterexample/World consumer controls pass.
use rustc_middle::{mir::interpret::GlobalAlloc, ty};
use rustc_abi::Size;
use serde_json::{json,Value};

pub trait Symbols<'tcx> {
    fn instance(&mut self, value: ty::Instance<'tcx>) -> Result<Value,String>;
    fn ty(&mut self, value: ty::Ty<'tcx>) -> Result<Value,String>;
    fn predicates(&mut self, value: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>) -> Result<Value,String>;
}

pub fn encode<'tcx>(value: &GlobalAlloc<'tcx>, symbols: &mut impl Symbols<'tcx>,
    pointer_bytes: u64, little_endian: bool) -> Result<Value,String> {
    Ok(match value {
        GlobalAlloc::Static(definition) => json!({"kind":"static",
            "definition":{"crate":definition.krate.as_u32(),"index":definition.index.as_u32()}}),
        GlobalAlloc::Function{instance} => json!({"kind":"function","instance":symbols.instance(*instance)?}),
        GlobalAlloc::TypeId{ty} => json!({"kind":"type_id","type":symbols.ty(*ty)?}),
        GlobalAlloc::VTable(ty,predicates) => json!({"kind":"vtable","type":symbols.ty(*ty)?,
            "predicates":symbols.predicates(predicates)?}),
        GlobalAlloc::Memory(memory) => {
            if ![1,2,4,8,16].contains(&pointer_bytes) {return Err("unsupported pointer width".into())}
            let allocation=memory.inner();
            if allocation.align>rustc_abi::Align::MAX {return Err("unsupported non-ABI alignment sentinel".into())}
            let bytes=allocation.inspect_with_uninit_and_ptr_outside_interpreter(0..allocation.len());
            let (mask_len,lazy_state,blocks)=allocation.init_mask().lean_miri_complete_init_mask_snapshot();
            if mask_len.bytes()!=allocation.len() as u64 || (lazy_state.is_none() && (blocks.len() as u128)*64<u128::from(mask_len.bytes())) {
                return Err("invalid compiler mask logical length or storage capacity".into())
            }
            let initialized:Vec<_>=(0..allocation.len()).map(|i|allocation.init_mask().get(Size::from_bytes(i as u64))).collect();
            let init_mask=match lazy_state {
                Some(state)=>json!({"kind":"lazy","len":mask_len.bytes(),"state":state}),
                None=>json!({"kind":"materialized","len":mask_len.bytes(),"blocks":blocks}),
            };
            let (pointers,fragments)=allocation.provenance().lean_miri_complete_provenance_snapshot();
            let provenance_fragments=fragments.map(|fragments| fragments.into_iter().map(|(slot,index,provenance,bytes)| {
                json!({"slot":slot.bytes(),"index":index,"target_source_alloc_id":provenance.alloc_id().0.get(),
                    "immutable":provenance.immutable(),"shared_reference":provenance.shared_ref(),"bytes":bytes})
            }).collect::<Vec<_>>());
            let mut relocations=Vec::new();
            for (slot,provenance) in &pointers {
                let start=usize::try_from(slot.bytes()).map_err(|_|"relocation slot too large")?;
                let width=usize::try_from(pointer_bytes).map_err(|_|"pointer width too large")?;
                let end=start.checked_add(width).ok_or("relocation range overflow")?;
                if end>bytes.len() || !initialized[start..end].iter().all(|v|*v) {
                    return Err("partial or uninitialized provenance is unsupported".into())
                }
                let mut offset=0u128;
                if little_endian {for (i,byte) in bytes[start..end].iter().enumerate(){offset|=u128::from(*byte)<<(8*i);}}
                else {for byte in &bytes[start..end]{offset=(offset<<8)|u128::from(*byte);}}
                relocations.push(json!({"slot":slot.bytes(),"target_source_alloc_id":provenance.alloc_id().0.get(),
                    "target_offset":offset.to_string(),"immutable":provenance.immutable(),"shared_reference":provenance.shared_ref()}));
            }
            json!({"kind":"memory","size":allocation.len(),"alignment":allocation.align.bytes(),
                "mutable":allocation.mutability.is_mut(),"bytes":bytes,"initialized":initialized,
                "pointer_bytes":pointer_bytes,"little_endian":little_endian,"relocations":relocations,
                "init_mask":init_mask,"provenance_fragments":provenance_fragments})
        }
    })
}
