#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_target;
extern crate rustc_abi;
extern crate rustc_session;
use rustc_driver::{Callbacks,Compilation};
use rustc_hir::def::DefKind;
use rustc_middle::ty::{self,Ty,TyCtxt};
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();
  let mut trait_id=None; let mut receiver=None;
  for local in tcx.hir_crate_items(()).definitions() {
   if tcx.def_kind(local)==DefKind::Trait && tcx.item_name(local.to_def_id()).as_str()=="Consume" {trait_id=Some(local.to_def_id());}
   if tcx.def_kind(local)==DefKind::Fn && tcx.item_name(local.to_def_id()).as_str()=="source_receiver" {
    let sig=tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(local).instantiate_identity().skip_norm_wip());
    let ty::Ref(_,child,_) = *sig.inputs()[0].kind() else {panic!("source receiver is not raw shared dyn")};receiver=Some(child);
   }
  }
  let receiver=receiver.expect("source receiver");
  assert!(matches!(receiver.kind(),ty::Dynamic(..)));
  let method=tcx.associated_items(trait_id.expect("Consume trait")).in_definition_order()
    .find(|item| tcx.item_name(item.def_id).as_str()=="consume").expect("consume method").def_id;
  let args=tcx.mk_args(&[receiver.into()]);
  let instance=ty::Instance::try_resolve(tcx,ty::TypingEnv::fully_monomorphized(),method,args)
    .expect("normal source resolution error").expect("no source instance");
  let ty::InstanceKind::Virtual(found,slot)=instance.def else {panic!("not actual Virtual: {instance:?}")};assert_eq!(found,method);
  let abi=tcx.fn_abi_of_instance(ty::TypingEnv::fully_monomorphized().as_query_input((instance,ty::List::empty()))).expect("actual FnAbi");
  let source_sig=tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(method).instantiate(tcx,args).skip_norm_wip());
  let original=source_sig.inputs()[0];
  let expected_ty=match original.kind() {
    ty::Ref(..)|ty::RawPtr(..)=>original,
    ty::Dynamic(..)|ty::Adt(..)=>Ty::new_mut_ptr(tcx,receiver),
    _=>panic!("oracle fixture receiver outside requested families"),
  };
  let tracked=instance.def.requires_caller_location(tcx);
  let thin=tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(Ty::new_mut_ptr(tcx,tcx.types.unit))).expect("thin unit pointer layout");
  assert_eq!(abi.args.len(),if tracked {3} else {2});assert_eq!(abi.fixed_count,2);assert!(!abi.c_variadic);
  assert_eq!(abi.args[0].layout.ty,expected_ty,"logical receiver must be newly lowered raw-mut-dyn, not original dyn");
  assert_eq!(abi.args[0].layout.layout,thin.layout,"all physical layout fields must match actual raw unit pointer");
  let rustc_target::callconv::PassMode::Direct(attrs)=abi.args[0].mode else {panic!("non-direct self")};
  assert_eq!(attrs.regular.bits(),128,"raw receiver only NoUndef, never NonNull or borrow attrs");
  assert_eq!(attrs.pointee_size.bytes(),0);assert!(attrs.pointee_align.is_none());
  if tracked {
  let location=tcx.caller_location_ty();
  assert_eq!(abi.args[2].layout.ty,tcx.erase_and_anonymize_regions(location),"canonical caller location logical type");
  let caller_layout=tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(location)).expect("actual caller ref layout");
  assert_eq!(abi.args[2].layout.layout,caller_layout.layout,"complete caller-location physical layout");
  let rustc_target::callconv::PassMode::Direct(caller_attrs)=abi.args[2].mode else {panic!("caller ref not direct")};
  let optimized=tcx.sess.opts.optimize!=rustc_session::config::OptLevel::No;
  assert_eq!(caller_attrs.regular.bits(),if optimized {700} else {144});
  assert_eq!(caller_attrs.pointee_size.bytes(),if optimized {24} else {0});
  assert_eq!(caller_attrs.pointee_align.expect("location align").bytes(),8);
  }
  println!("method={method:?} args={args:?} slot={slot} logical={expected_ty:?}\nfull_actual_fn_abi={abi:#?}\nPASS actual normal-resolved Virtual receiver;full FnAbi/layout/attrs;tracked caller-location when required");
  Compilation::Stop
 }
}
fn main()->std::process::ExitCode {let args=std::env::args().collect::<Vec<_>>();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
