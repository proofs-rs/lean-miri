#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_abi;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::{mir,ty};
struct Probe;
impl Callbacks for Probe {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:ty::TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();
  let before=tcx.lean_miri_complete_allocation_identity_snapshot();
  assert_eq!(before,tcx.lean_miri_complete_allocation_identity_snapshot());
  let def=tcx.hir_crate_items(()).definitions().find(|id|tcx.def_kind(id.to_def_id())==rustc_hir::def::DefKind::AssocConst && tcx.item_name(id.to_def_id()).as_str()=="ANCHOR").unwrap().to_def_id();
  let env=ty::TypingEnv::fully_monomorphized();
  let arg=ty::Const::from_bits(tcx,6,env,tcx.types.u32);
  let instance=ty::Instance::new_raw(def,tcx.mk_args(&[arg.into()]));
  let result=tcx.eval_to_allocation_raw(env.as_query_input(mir::interpret::GlobalId {instance,promoted:None})).unwrap();
  assert!(!before.1.iter().any(|(id,_)|*id==result.alloc_id));
  let after=tcx.lean_miri_complete_allocation_identity_snapshot();
  assert_eq!(after,tcx.lean_miri_complete_allocation_identity_snapshot());
  assert!(after.1.iter().any(|(id,_)|*id==result.alloc_id));
  let memory=tcx.global_alloc(result.alloc_id).unwrap_memory();
  assert!(!memory.inner().mutability.is_mut());
  let fresh=tcx.reserve_and_set_memory_alloc(memory);
  let key=tcx.reserve_and_set_memory_dedup(memory,0);
  assert_eq!(key,tcx.reserve_and_set_memory_dedup(memory,0));
  let complete=tcx.lean_miri_complete_allocation_identity_snapshot();
  assert!(complete.1.iter().any(|(id,_)|*id==fresh));
  assert!(!complete.2.iter().any(|(_,_,id)|*id==fresh));
  assert!(complete.2.iter().any(|(_,salt,id)|*salt==0&&*id==key));
  assert_eq!(complete,tcx.lean_miri_complete_allocation_identity_snapshot());
  let lazy=mir::interpret::Allocation::from_bytes_byte_aligned_immutable(vec![0u8;16],());
  let mut materialized=mir::interpret::Allocation::new(rustc_abi::Size::from_bytes(16),rustc_abi::Align::ONE,mir::interpret::AllocInit::Zero,());
  let range=(rustc_abi::Size::from_bytes(8)..rustc_abi::Size::from_bytes(9)).into();
  materialized.write_uninit(&tcx,range);
  materialized.write_scalar(&tcx,range,mir::interpret::Scalar::from_uint(0u8,rustc_abi::Size::from_bytes(1))).unwrap();
  materialized.mutability=lazy.mutability;
  assert_eq!(lazy.inspect_with_uninit_and_ptr_outside_interpreter(0..16),materialized.inspect_with_uninit_and_ptr_outside_interpreter(0..16));
  for n in 0..16 {assert_eq!(lazy.init_mask().get(rustc_abi::Size::from_bytes(n)),materialized.init_mask().get(rustc_abi::Size::from_bytes(n)));}
  assert!(lazy.init_mask()!=materialized.init_mask());assert!(lazy!=materialized);
  let a=mir::interpret::GlobalAlloc::Memory(tcx.mk_const_alloc(lazy));
  let b=mir::interpret::GlobalAlloc::Memory(tcx.mk_const_alloc(materialized));
  assert!(a!=b);
  let a_id=tcx.reserve_and_set_memory_dedup(a.unwrap_memory(),0);
  let b_id=tcx.reserve_and_set_memory_dedup(b.unwrap_memory(),0);
  assert_ne!(a_id,b_id);assert_eq!(a_id,tcx.reserve_and_set_memory_dedup(a.unwrap_memory(),0));assert_eq!(b_id,tcx.reserve_and_set_memory_dedup(b.unwrap_memory(),0));
  let (lazy_len,lazy_state,lazy_blocks)=a.unwrap_memory().inner().init_mask().lean_miri_complete_init_mask_snapshot();
  let (mat_len,mat_state,mat_blocks)=b.unwrap_memory().inner().init_mask().lean_miri_complete_init_mask_snapshot();
  assert_eq!(lazy_len.bytes(),16);assert_eq!(mat_len.bytes(),16);assert_eq!(lazy_state,Some(true));assert!(lazy_blocks.is_empty());assert_eq!(mat_state,None);assert_eq!(mat_blocks,vec![u64::MAX]);
  let size=rustc_abi::Size::from_bytes(8);
  let mut fragments=mir::interpret::Allocation::new(size,rustc_abi::Align::from_bytes(8).unwrap(),mir::interpret::AllocInit::Uninit,());
  let provenance=mir::interpret::CtfeProvenance::from_parts((a_id,true,true));
  fragments.write_scalar(&tcx,(rustc_abi::Size::ZERO..size).into(),mir::interpret::Scalar::from_pointer(mir::interpret::Pointer::new(provenance,rustc_abi::Size::from_bytes(3)),&tcx)).unwrap();
  fragments.write_uninit(&tcx,(rustc_abi::Size::ZERO..rustc_abi::Size::from_bytes(1)).into());
  let (ptrs,fragment_entries)=fragments.provenance().lean_miri_complete_provenance_snapshot();
  assert!(ptrs.is_empty());let fragment_entries=fragment_entries.unwrap();assert_eq!(fragment_entries.len(),7);
  for (slot,index,prov,raw) in &fragment_entries {assert_eq!(slot.bytes(),u64::from(*index));assert_eq!(prov.into_parts(),(a_id,true,true));assert_eq!(*raw,[3,0,0,0,0,0,0,0]);}
  fragments.write_uninit(&tcx,(rustc_abi::Size::from_bytes(1)..size).into());
  fragments.mutability=a.unwrap_memory().inner().mutability;
  let mut no_fragments=fragments.clone();assert!(no_fragments.provenance_merge_bytes(&tcx));
  assert_ne!(fragments.provenance(),no_fragments.provenance());
  assert_eq!(fragments.init_mask(),no_fragments.init_mask());
  let some_global=mir::interpret::GlobalAlloc::Memory(tcx.mk_const_alloc(fragments));
  let none_global=mir::interpret::GlobalAlloc::Memory(tcx.mk_const_alloc(no_fragments));
  let some_id=tcx.reserve_and_set_memory_dedup(some_global.unwrap_memory(),0);
  let none_id=tcx.reserve_and_set_memory_dedup(none_global.unwrap_memory(),0);assert_ne!(some_id,none_id);
  assert_eq!(some_id,tcx.reserve_and_set_memory_dedup(some_global.unwrap_memory(),0));
  assert_eq!(none_id,tcx.reserve_and_set_memory_dedup(none_global.unwrap_memory(),0));
  let mut zeros=mir::interpret::Allocation::new(rustc_abi::Size::from_bytes(16),rustc_abi::Align::ONE,mir::interpret::AllocInit::Uninit,());
  let mut sevens=mir::interpret::Allocation::from_bytes(vec![7u8;16],rustc_abi::Align::ONE,zeros.mutability,());
  sevens.write_uninit(&tcx,(rustc_abi::Size::ZERO..rustc_abi::Size::from_bytes(16)).into());
  zeros.mutability=a.unwrap_memory().inner().mutability;sevens.mutability=zeros.mutability;
  assert_eq!(zeros.init_mask(),sevens.init_mask());assert_eq!(zeros.provenance(),sevens.provenance());assert!(zeros!=sevens);
  let zeros_id=tcx.reserve_and_set_memory_dedup(tcx.mk_const_alloc(zeros),0);
  let sevens_id=tcx.reserve_and_set_memory_dedup(tcx.mk_const_alloc(sevens),0);assert_ne!(zeros_id,sevens_id);
  let before_read=tcx.lean_miri_complete_allocation_identity_snapshot();
  for _ in 0..3 {assert_eq!(b.unwrap_memory().inner().init_mask().lean_miri_complete_init_mask_snapshot(),(mat_len,mat_state,mat_blocks.clone()));assert_eq!(some_global.unwrap_memory().inner().provenance().lean_miri_complete_provenance_snapshot(),(Vec::new(),Some(Vec::new())));}
  assert_eq!(before_read,tcx.lean_miri_complete_allocation_identity_snapshot());
  println!("PASS exact representation: Lazy(true) vs Materialized[u64MAX] len16/trailingbits distinct;7fragments retain slots/index/packedflags/all8bytes;Someempty vsNone salt0dedup {some_id:?} vs {none_id:?};uninitbackingbytes IDs {zeros_id:?}/{sevens_id:?} remain distinct;allreads nonmutating");
  println!("PASS actual patched snapshot: before={} after={} root={:?} fresh={fresh:?} dedup={key:?}; repeated snapshots do not mutate complete maps/frontier",before.0,after.0,result.alloc_id);
  Compilation::Stop
 }
}
fn main(){rustc_driver::compiler_entrypoint(&std::env::args().collect::<Vec<_>>(),&mut Probe)}
