#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
use rustc_driver::{Callbacks,Compilation};
use rustc_interface::interface;
use rustc_middle::ty::{TyCtxt,TypeVisitableExt};
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  let definition=tcx.hir_crate_items(()).definitions()
   .find(|id| tcx.def_path_str(id.to_def_id())=="type_hashes").expect("type_hashes fixture absent");
  let signature=tcx.fn_sig(definition).instantiate_identity().skip_norm_wip().skip_binder();
  let mut types=vec![];
  for input in signature.inputs() {
   for argument in input.walk() {
    if let Some(ty)=argument.as_type() {if !types.contains(&ty){types.push(ty);}}
   }
  }
  types.push(tcx.types.never);
  let rows=types.into_iter().filter(|ty| !ty.has_non_region_param() && !ty.has_escaping_bound_vars())
   .map(|ty|format!("{{\"display\":{:?},\"hash\":\"{}\"}}",format!("{ty:?}"),tcx.type_id_hash(ty).as_u128()))
   .collect::<Vec<_>>();
  println!("[{}]",rows.join(","));Compilation::Stop
 }
}
fn main(){let args=std::env::args().skip(1).collect::<Vec<_>>();rustc_driver::compiler_entrypoint(&args,&mut Oracle);}
