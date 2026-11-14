#![feature(rustc_private)]
// Independent pinned compiler oracle: obtain TyAndLayout::field(1), including
// the final layout_of normalization, directly from rustc. The shared exporter
// generic_material module is used ONLY to encode raw input/output Ty syntax;
// physical LayoutData components and the field query itself are observed here.
// The finite fixture intentionally requires scalar initialized-pointer fields;
// all assumptions about representation/niche primitive are asserted below.
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_abi;
extern crate rustc_hir;
extern crate rustc_attr_ir;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::{self,TyCtxt};
use rustc_middle::ty::layout::{LayoutCx,LayoutOf};
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  let def=tcx.hir_crate_items(()).definitions().find(|id|tcx.def_path_str(id.to_def_id())=="metadata_fields").unwrap();
  let sig=tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(def).instantiate_identity().skip_norm_wip());
  let env=ty::TypingEnv::fully_monomorphized();let cx=LayoutCx::new(tcx,env);
  let rows=sig.inputs().iter().enumerate().map(|(index,&ty)| {
   let layout=tcx.layout_of(env.as_query_input(ty)).unwrap();let field=layout.field(&cx,1);
   let rustc_abi::BackendRepr::Scalar(scalar)=field.backend_repr else {panic!("metadata field is not scalar")};
   let rustc_abi::Primitive::Pointer(space)=scalar.primitive() else {panic!("metadata field is not pointer")};
   assert!(matches!(scalar,rustc_abi::Scalar::Initialized{..}));
   let range=scalar.valid_range(&cx);
   assert!(matches!(field.fields,rustc_abi::FieldsShape::Primitive));
   let rustc_abi::Variants::Single{index:variant}=field.variants else {panic!("metadata field has multiple variants")};
   if let Some(niche)=field.largest_niche {assert!(niche.value == rustc_abi::Primitive::Pointer(space));}
   let niche=field.largest_niche.map(|n|format!("{{\"offset\":{},\"start\":{},\"end\":{}}}",n.offset.bytes(),n.valid_range.start,n.valid_range.end)).unwrap_or("null".to_owned());
   format!("{{\"index\":{},\"parent\":{},\"field_type\":{},\"size\":{},\"align\":{},\"unadjusted_align\":{},\"max_repr_align\":{},\"repr_c\":{},\"uninhabited\":{},\"randomization_seed\":{},\"address_space\":{},\"start\":{},\"end\":{},\"variant\":{},\"niche\":{},\"fields\":\"primitive\",\"backend\":\"initialized_pointer\"}}",
    index,generic_material::type_tree(tcx,ty).unwrap(),generic_material::type_tree(tcx,field.ty).unwrap(),field.size.bytes(),field.align.abi.bytes(),field.unadjusted_abi_align.bytes(),field.max_repr_align.map(|a|a.bytes().to_string()).unwrap_or("null".to_owned()),field.repr_c,field.uninhabited,field.randomization_seed.as_u64(),space.0,range.start,range.end,variant.as_u32(),niche)
  }).collect::<Vec<_>>();println!("[{}]",rows.join(","));Compilation::Stop
 }
}
fn main(){let args=std::env::args().collect::<Vec<_>>();rustc_driver::compiler_entrypoint(&args,&mut Oracle);}
