#![feature(rustc_private)]
// Direct pinned TyAndLayout::for_variant observations, including pruned variants.
// Shared generic_material code encodes raw Ty syntax only. Full selected-layout
// fields are serialized independently here; unsupported fixture representations
// panic rather than being mislabeled. This oracle makes finite comparisons.
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_abi;
extern crate rustc_index;
extern crate rustc_span;
extern crate rustc_attr_ir;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::{self,TyCtxt};
use rustc_middle::ty::layout::{LayoutCx,LayoutOf};
use rustc_index::Idx;
fn numbers(values:impl IntoIterator<Item=u64>)->String {format!("[{}]",values.into_iter().map(|n|n.to_string()).collect::<Vec<_>>().join(","))}
fn primitive(tcx:TyCtxt<'_>,p:rustc_abi::Primitive)->String {match p {
 rustc_abi::Primitive::Int(integer,signed)=>format!("{{\"kind\":\"integer\",\"integer_kind\":{:?},\"signed\":{},\"size_bytes\":{}}}",integer.int_ty_str(),signed,integer.size().bytes()),
 rustc_abi::Primitive::Pointer(space)=>format!("{{\"kind\":\"pointer\",\"address_space\":{},\"size_bytes\":{}}}",space.0,tcx.data_layout.pointer_size_in(space).bytes()),
 other=>panic!("finite variant oracle fixture primitive unsupported {other:?}"),
}}
fn range(r:rustc_abi::WrappingRange)->String {format!("{{\"start\":\"{}\",\"end\":\"{}\"}}",r.start,r.end)}
fn scalar(tcx:TyCtxt<'_>,value:rustc_abi::Scalar)->String {match value {
 rustc_abi::Scalar::Initialized{value,valid_range}=>format!("{{\"kind\":\"initialized\",\"primitive\":{},\"valid_range\":{}}}",primitive(tcx,value),range(valid_range)),
 rustc_abi::Scalar::Union{value}=>format!("{{\"kind\":\"union\",\"primitive\":{}}}",primitive(tcx,value)),
}}
fn backend(tcx:TyCtxt<'_>,value:rustc_abi::BackendRepr)->String {match value {
 rustc_abi::BackendRepr::Memory{sized}=>format!("{{\"kind\":\"memory\",\"sized\":{sized}}}"),
 rustc_abi::BackendRepr::Scalar(value)=>format!("{{\"kind\":\"scalar\",\"scalar\":{}}}",scalar(tcx,value)),
 rustc_abi::BackendRepr::ScalarPair{a,b,b_offset}=>format!("{{\"kind\":\"scalar_pair\",\"first\":{},\"second\":{},\"second_offset_bytes\":{}}}",scalar(tcx,a),scalar(tcx,b),b_offset.bytes()),
 other=>panic!("finite variant oracle fixture backend unsupported {other:?}"),
}}
fn layout(tcx:TyCtxt<'_>,value:rustc_middle::ty::layout::TyAndLayout<'_>)->String {
 let rustc_abi::Variants::Single{index}=value.variants else {panic!("for_variant did not return Single")};
 let fields=match &value.fields {
  rustc_abi::FieldsShape::Primitive=>"{\"kind\":\"primitive\",\"field_count\":0}".to_owned(),
  rustc_abi::FieldsShape::Union(count)=>format!("{{\"kind\":\"union\",\"field_count\":{},\"offset_bytes\":0}}",count),
  rustc_abi::FieldsShape::Arbitrary{offsets,in_memory_order}=>format!("{{\"kind\":\"arbitrary\",\"field_count\":{},\"offsets_bytes\":{},\"memory_order\":{}}}",offsets.len(),numbers(offsets.iter().map(|n|n.bytes())),numbers(in_memory_order.iter().map(|n|n.index() as u64))),
  other=>panic!("finite variant oracle fields unsupported {other:?}"),
 };
 let offsets=numbers((0..value.fields.count()).map(|i|value.fields.offset(i).bytes()));
 let niche=value.largest_niche.map(|n|format!("{{\"offset_bytes\":{},\"primitive\":{},\"valid_range\":{}}}",n.offset.bytes(),primitive(tcx,n.value),range(n.valid_range))).unwrap_or("null".into());
 format!("{{\"fields\":{},\"field_offsets_bytes\":{},\"variants\":{{\"kind\":\"single\",\"variant_index\":{}}},\"backend_repr\":{},\"size_bytes\":{},\"abi_align_bytes\":{},\"unadjusted_abi_align_bytes\":{},\"max_repr_align_bytes\":{},\"repr_c\":{},\"uninhabited\":{},\"largest_niche\":{},\"randomization_seed\":{}}}",fields,offsets,index.index(),backend(tcx,value.backend_repr),value.size.bytes(),value.align.abi.bytes(),value.unadjusted_abi_align.bytes(),value.max_repr_align.map(|a|a.bytes().to_string()).unwrap_or("null".into()),value.repr_c,value.uninhabited,niche,value.randomization_seed.as_u64())
}
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  let ordering=tcx.get_diagnostic_item(rustc_span::Symbol::intern("Ordering")).expect("actual Ordering diagnostic item");
  let mut types=vec![ty::Ty::new_adt(tcx,tcx.adt_def(ordering),tcx.mk_args(&[]))];
  for local in tcx.hir_crate_items(()).definitions() {
   if tcx.def_kind(local)==rustc_hir::def::DefKind::Fn && tcx.item_name(local.to_def_id()).as_str()=="variant_roots" {
    let signature=tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(local).instantiate_identity().skip_norm_wip());
    for &ty in signature.inputs() {if !types.contains(&ty){types.push(ty);}}
   }
  }
  let env=ty::TypingEnv::fully_monomorphized();let cx=LayoutCx::new(tcx,env);
  let rows=types.into_iter().map(|ty| {
   let ty::Adt(definition,_)=ty.kind() else {panic!("nonADT root")};
   let parent=tcx.layout_of(env.as_query_input(ty)).unwrap();
   let variants=definition.variants().indices().map(|index|format!("{{\"index\":{},\"layout\":{}}}",index.index(),layout(tcx,parent.for_variant(&cx,index)))).collect::<Vec<_>>();
   format!("{{\"source_type\":{},\"variants\":[{}]}}",generic_material::type_tree(tcx,ty).unwrap(),variants.join(","))
  }).collect::<Vec<_>>();println!("[{}]",rows.join(","));Compilation::Stop
 }
}
fn main(){let args=std::env::args().collect::<Vec<_>>();rustc_driver::compiler_entrypoint(&args,&mut Oracle);}
