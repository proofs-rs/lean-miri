#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_abi;
extern crate rustc_data_structures;
extern crate rustc_hashes;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::{self,TyCtxt};
use rustc_hir::def_id::DefId;
use rustc_data_structures::stable_hash::{StableHash,StableHasher};
fn hash(tcx:TyCtxt<'_>,value:&impl StableHash)->u128 {tcx.with_stable_hashing_context(|mut hcx|{let mut h=StableHasher::new();hcx.while_hashing_spans(false,|hcx|value.stable_hash(hcx,&mut h));h.finish::<rustc_hashes::Hash128>().as_u128()})}
fn did(tcx:TyCtxt<'_>,id:DefId)->String {format!("\"{}\"",u128::from_le_bytes(tcx.def_path_hash(id).0.to_le_bytes()))}
fn optional_id(tcx:TyCtxt<'_>,id:Option<DefId>)->String {id.map(|id|did(tcx,id)).unwrap_or("null".into())}
fn repr(value:&rustc_abi::ReprOptions)->String {
 let int=match value.int{None=>"null".into(),Some(rustc_abi::IntegerType::Pointer(s))=>format!("[\"pointer\",{s}]"),Some(rustc_abi::IntegerType::Fixed(i,s))=>format!("[\"fixed\",{},{s}]",i.size().bits())};
 let align=value.align.map(|v|v.bytes().trailing_zeros().to_string()).unwrap_or("null".into());let pack=value.pack.map(|v|v.bytes().trailing_zeros().to_string()).unwrap_or("null".into());
 let scalable=match value.scalable{None=>"null".into(),Some(rustc_abi::ScalableElt::ElementCount(n))=>format!("[\"count\",{n}]"),Some(rustc_abi::ScalableElt::Container)=>"[\"container\"]".into()};
 format!("{{\"int\":{int},\"align\":{align},\"pack\":{pack},\"flags\":{},\"scalable\":{scalable},\"shuffle\":{}}}",value.flags.bits(),value.field_shuffle_seed.as_u64())
}
fn const_json(tcx:TyCtxt<'_>, ct:ty::Const<'_>)->String {
 let ty::ConstKind::Value(value)=ct.kind() else {panic!("nonvalue oracle")};
 let tree=match **value.valtree {
  ty::ValTreeKind::Leaf(scalar)=>format!("{{\"bits\":\"{}\",\"size\":{}}}",scalar.to_bits_unchecked(),scalar.size().bytes()),
  ty::ValTreeKind::Branch(children)=>format!("{{\"children\":[{}]}}",children.iter().map(|child|const_json(tcx,child)).collect::<Vec<_>>().join(",")),
 };
 format!("{{\"ty\":{:?},\"tree\":{},\"hash\":\"{}\"}}",format!("{:?}",value.ty),tree,hash(tcx,&ct))
}
struct Oracle;
impl Callbacks for Oracle{fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation{
 tcx.dcx().abort_if_errors();let mut rows=Vec::new();
 for id in tcx.hir_crate_items(()).definitions().filter(|id|tcx.def_kind(*id).is_adt()).map(|id|id.to_def_id()){
 let adt=tcx.adt_def(id);let mut variants=Vec::new();
 for variant in adt.variants(){variant.has_errors().unwrap();let mut fields=Vec::new();
 for field in &variant.fields {
 let vis=match field.vis{ty::Visibility::Public=>"null".into(),ty::Visibility::Restricted(id)=>did(tcx,id.to_def_id())};
 let restriction=match field.mut_restriction{ty::RestrictionKind::Unrestricted=>"null".into(),ty::RestrictionKind::Restricted(id,_)=>did(tcx,id)};
 fields.push(format!("{{\"id\":{},\"name\":{:?},\"vis\":{vis},\"restriction\":{restriction},\"unsafe\":{},\"default\":{}}}",did(tcx,field.did),field.name.to_string(),field.safety.is_unsafe(),optional_id(tcx,field.value)));
 }
 let ctor=variant.ctor.map(|(kind,id)|format!("[{},{}]",match kind{rustc_hir::def::CtorKind::Fn=>0,rustc_hir::def::CtorKind::Const=>1},did(tcx,id))).unwrap_or("null".into());
 let discr=match variant.discr{ty::VariantDiscr::Relative(n)=>format!("[\"relative\",{n}]"),ty::VariantDiscr::Explicit(id)=>format!("[\"explicit\",{}]",did(tcx,id))};
 variants.push(format!("{{\"id\":{},\"ctor\":{ctor},\"name\":{:?},\"discr\":{discr},\"fields\":[{}],\"flags\":{}}}",did(tcx,variant.def_id),variant.name.to_string(),fields.join(","),u8::from(variant.is_field_list_non_exhaustive())));
 }
 let inner=tcx.with_stable_hashing_context(|mut hcx|{let mut h=StableHasher::new();hcx.while_hashing_spans(false,|hcx|{id.stable_hash(hcx,&mut h);adt.variants().stable_hash(hcx,&mut h);adt.flags().stable_hash(hcx,&mut h);adt.repr().stable_hash(hcx,&mut h)});h.finish::<rustc_hashes::Hash128>().as_u128()});
 rows.push(format!("{{\"name\":{:?},\"id\":{},\"variants\":[{}],\"flags\":{},\"repr\":{},\"inner\":\"{inner}\",\"outer\":\"{}\"}}",tcx.def_path_str(id),did(tcx,id),variants.join(","),adt.flags().bits(),repr(&adt.repr()),hash(tcx,&adt)));
 }
 let signature_id=tcx.hir_crate_items(()).definitions().find(|id|tcx.def_path_str(id.to_def_id())=="nominal_hashes").unwrap();
 let signature=tcx.fn_sig(signature_id).instantiate_identity().skip_norm_wip().skip_binder();
 let mut nominal=Vec::new(); let mut constants=Vec::new(); let mut types=Vec::new();
 for input in signature.inputs(){
  for argument in input.walk(){
   if let Some(ct)=argument.as_const(){if matches!(ct.kind(),ty::ConstKind::Value(_)){constants.push(const_json(tcx,ct));}}
   if let Some(ty)=argument.as_type(){
    types.push(format!("{{\"display\":{:?},\"type\":{},\"hash\":\"{}\"}}",format!("{ty:?}"),generic_material::type_tree(tcx,ty).expect("raw oracle syntax"),tcx.type_id_hash(ty).as_u128()));
    if let ty::Adt(adt,args)=ty.kind(){
   nominal.push(format!("{{\"display\":{:?},\"kind\":\"adt\",\"id\":{},\"adt_outer\":\"{}\",\"args_hash\":\"{}\",\"type_hash\":\"{}\"}}",format!("{ty:?}"),did(tcx,adt.did()),hash(tcx,adt),hash(tcx,&&tcx.erase_and_anonymize_regions(*args)[..]),tcx.type_id_hash(ty).as_u128()));
  }}}
 }
 let leaf_u8=ty::Const::new_value(tcx,ty::ValTree::from_scalar_int(tcx,3u8.into()),tcx.types.u8);
 let leaf_bool=ty::Const::new_value(tcx,ty::ValTree::from_scalar_int(tcx,1u8.into()),tcx.types.bool);
 let tuple=ty::Ty::new_tup(tcx,&[tcx.types.u8,tcx.types.bool]);
 let aggregate=ty::Const::new_value(tcx,ty::ValTree::from_branches(tcx,[leaf_u8,leaf_bool]),tuple);
 constants.push(const_json(tcx,aggregate));
 for id in tcx.hir_crate_items(()).definitions().filter(|id|tcx.def_kind(*id).is_fn_like()).map(|id|id.to_def_id()){
  if !["plain","generic"].contains(&tcx.def_path_str(id).as_str()){continue;}
  let args=if tcx.def_path_str(id)=="generic"{tcx.mk_args(&[tcx.types.u32.into()])}else{ty::GenericArgs::empty()};
  let ty=ty::Ty::new_fn_def(tcx,id,ty::Binder::dummy(args));
  let ty::FnDef(_,binder)=ty.kind()else{unreachable!()};
  types.push(format!("{{\"display\":{:?},\"type\":{},\"hash\":\"{}\"}}",format!("{ty:?}"),generic_material::type_tree(tcx,ty).expect("raw oracle syntax"),tcx.type_id_hash(ty).as_u128()));
  nominal.push(format!("{{\"display\":{:?},\"kind\":\"fn\",\"id\":{},\"args_hash\":\"{}\",\"variables_hash\":\"{}\",\"type_hash\":\"{}\"}}",format!("{ty:?}"),did(tcx,id),hash(tcx,&&tcx.erase_and_anonymize_regions(args)[..]),hash(tcx,&&binder.bound_vars()[..]),tcx.type_id_hash(ty).as_u128()));
 }
 println!("{{\"declarations\":[{}],\"nominal\":[{}],\"constants\":[{}],\"types\":[{}]}}",rows.join(","),nominal.join(","),constants.join(","),types.join(","));Compilation::Stop
}}
fn main(){let args=std::env::args().collect::<Vec<_>>();rustc_driver::compiler_entrypoint(&args,&mut Oracle);}
