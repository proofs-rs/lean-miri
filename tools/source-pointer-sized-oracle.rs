//! Independent pinned-rustc oracle for the full-std v26 source3 fixture.
//! Physical IDs are guarded by source paths. No exporter module or evaluated
//! constant answer is used. Run with the document's exact recorded rustc argv.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::{CrateNum, DefId, DefIndex};
use rustc_middle::{
    mir::interpret::{EvalToAllocationRawResult, EvalToConstValueResult, EvalToValTreeResult, GlobalId},
    query::QueryCache,
    ty::{self, TyCtxt},
};
use std::sync::{atomic::{AtomicU64, Ordering}, OnceLock};
type Key<'tcx> = ty::PseudoCanonicalInput<'tcx, GlobalId<'tcx>>;
type ValueFn = for<'tcx> fn(TyCtxt<'tcx>, Key<'tcx>) -> EvalToConstValueResult<'tcx>;
type AllocFn = for<'tcx> fn(TyCtxt<'tcx>, Key<'tcx>) -> EvalToAllocationRawResult<'tcx>;
type TreeFn = for<'tcx> fn(TyCtxt<'tcx>, Key<'tcx>) -> EvalToValTreeResult<'tcx>;
static VALUE: OnceLock<ValueFn> = OnceLock::new();
static ALLOC: OnceLock<AllocFn> = OnceLock::new();
static TREE: OnceLock<TreeFn> = OnceLock::new();
static VALUES: AtomicU64 = AtomicU64::new(0);
static ALLOCS: AtomicU64 = AtomicU64::new(0);
static TREES: AtomicU64 = AtomicU64::new(0);
fn value<'tcx>(tcx: TyCtxt<'tcx>, key: Key<'tcx>) -> EvalToConstValueResult<'tcx> {
    VALUES.fetch_add(1, Ordering::Relaxed); VALUE.get().unwrap()(tcx, key)
}
fn alloc<'tcx>(tcx: TyCtxt<'tcx>, key: Key<'tcx>) -> EvalToAllocationRawResult<'tcx> {
    ALLOCS.fetch_add(1, Ordering::Relaxed); ALLOC.get().unwrap()(tcx, key)
}
fn tree<'tcx>(tcx: TyCtxt<'tcx>, key: Key<'tcx>) -> EvalToValTreeResult<'tcx> {
    TREES.fetch_add(1, Ordering::Relaxed); TREE.get().unwrap()(tcx, key)
}
fn counts() -> [u64; 3] {
    [VALUES.load(Ordering::Relaxed), ALLOCS.load(Ordering::Relaxed), TREES.load(Ordering::Relaxed)]
}
fn id(index: u32) -> DefId { DefId { krate: CrateNum::from_u32(2), index: DefIndex::from_u32(index) } }
fn slots(tcx: TyCtxt<'_>) -> [[bool; 3]; 3] {
    [69102, 54220, 38452].map(|index| {
        let key = ty::TypingEnv::new(ty::ParamEnv::empty(), ty::TypingMode::PostAnalysis)
            .as_query_input(GlobalId { instance: ty::Instance::mono(tcx, id(index)), promoted: None });
        [tcx.query_system.query_vtables.eval_to_const_value_raw.cache.lookup(&key).is_some(),
         tcx.query_system.query_vtables.eval_to_allocation_raw.cache.lookup(&key).is_some(),
         tcx.query_system.query_vtables.eval_to_valtree.cache.lookup(&key).is_some()]
    })
}
struct Probe;
impl Callbacks for Probe {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        config.override_queries = Some(|_, providers| {
            VALUE.set(providers.queries.eval_to_const_value_raw).unwrap(); providers.queries.eval_to_const_value_raw = value;
            ALLOC.set(providers.queries.eval_to_allocation_raw).unwrap(); providers.queries.eval_to_allocation_raw = alloc;
            TREE.set(providers.queries.eval_to_valtree).unwrap(); providers.queries.eval_to_valtree = tree;
        });
    }
    fn after_analysis<'tcx>(&mut self, _: &rustc_interface::interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.dcx().abort_if_errors();
        assert_eq!(tcx.def_path_str(id(36655)), "core::num::niche_types::NonZeroU64Inner");
        assert_eq!(tcx.def_path_str(id(69102)), "core::num::niche_types::NonZeroU64Inner::{constant#0}");
        let before = slots(tcx); let calls = counts();
        assert_eq!(before, [[false; 3]; 3], "selected roots must be cold to establish query absence");
        let pointee = ty::Ty::new_adt(tcx, tcx.adt_def(id(36655)), tcx.mk_args(&[]));
        let env = ty::TypingEnv::fully_monomorphized();
        assert!(pointee.is_sized(tcx, env));
        let pointer = ty::Ty::new_imm_ptr(tcx, pointee);
        let layout = tcx.layout_of(env.as_query_input(pointer)).expect("pointer layout");
        assert_eq!(layout.size, tcx.data_layout.pointer_size());
        assert_eq!(slots(tcx), before, "selected CTFE slots changed");
        assert_eq!(counts(), calls, "Sized/pointer layout entered a CTFE provider");
        println!("{{\"scope\":\"pinned full-std v26 physical fixture; fresh after_analysis replay before exporter queries\",\"sized\":true,\"pointer_size\":{},\"pointer_align\":{},\"selected_roots_cold\":true,\"ctfe_provider_delta\":[0,0,0],\"target_cache_unchanged\":true}}", layout.size.bytes(), layout.align.abi.bytes());
        Compilation::Stop
    }
}
fn main() -> std::process::ExitCode {
    let args = std::env::args().collect::<Vec<_>>();
    rustc_driver::catch_with_exit_code(|| rustc_driver::compiler_entrypoint(&args, &mut Probe))
}
