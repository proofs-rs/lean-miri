#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
use rustc_driver::{Callbacks,Compilation};
use rustc_interface::interface;
use rustc_middle::ty::TyCtxt;
use rustc_hir::{def_id::DefId,definitions::DefPathData};
struct Oracle;
fn component(data:DefPathData)->(u8,Option<String>){match data {
 DefPathData::CrateRoot=>(0,None),DefPathData::Impl=>(1,None),DefPathData::ForeignMod=>(2,None),
 DefPathData::Use=>(3,None),DefPathData::GlobalAsm=>(4,None),DefPathData::TypeNs(s)=>(5,Some(s.to_string())),
 DefPathData::ValueNs(s)=>(6,Some(s.to_string())),DefPathData::MacroNs(s)=>(7,Some(s.to_string())),
 DefPathData::LifetimeNs(s)=>(8,Some(s.to_string())),DefPathData::Closure=>(9,None),DefPathData::TestBinderConstraints=>(10,None),
 DefPathData::Ctor=>(11,None),DefPathData::AnonConst=>(12,None),DefPathData::OpaqueTy=>(13,None),
 DefPathData::OpaqueLifetime(s)=>(14,Some(s.to_string())),DefPathData::AnonAssocTy(s)=>(15,Some(s.to_string())),
 DefPathData::SyntheticCoroutineBody=>(16,None),DefPathData::NestedStatic=>(17,None)}}
impl Callbacks for Oracle{
 fn after_analysis<'tcx>(&mut self,_:&interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation{
 let definitions=tcx.iter_local_def_id().map(|d|d.to_def_id()).chain([
   tcx.lang_items().option_type().unwrap(),tcx.lang_items().phantom_data().unwrap()]);
 let rows=definitions.map(|definition|{
  let stable=tcx.stable_crate_id(definition.krate).as_u64();let mut current=definition;let mut pieces=vec![];
  loop {let key=tcx.def_key(current);let (kind,name)=component(key.disambiguated_data.data);
   if key.parent.is_some(){pieces.push(format!("{{\"kind\":{},\"name\":{},\"disambiguator\":{}}}",kind,name.map(|s|format!("{s:?}")).unwrap_or("null".into()),key.disambiguated_data.disambiguator));}
   match key.parent{Some(index)=>current=DefId{krate:current.krate,index},None=>break}
  }
  pieces.reverse();format!("{{\"definition\":{:?},\"crate\":{},\"index\":{},\"stable_crate\":\"{}\",\"components\":[{}],\"hash\":\"{}\"}}",tcx.def_path_str(definition),definition.krate.as_u32(),definition.index.as_u32(),stable,pieces.join(","),u128::from_le_bytes(tcx.def_path_hash(definition).0.to_le_bytes()))
 }).collect::<Vec<_>>();println!("[{}]",rows.join(","));Compilation::Stop
 }}
fn main(){let args=std::env::args().skip(1).collect::<Vec<_>>();rustc_driver::compiler_entrypoint(&args,&mut Oracle);}
