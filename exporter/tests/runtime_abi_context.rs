#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use std::path::PathBuf;

struct RuntimeAbiProbe {
    checked: bool,
}

impl Callbacks for RuntimeAbiProbe {
    fn after_analysis<'tcx>(
        &mut self,
        _: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let items = tcx.hir_crate_items(());
        let definition = items
            .definitions()
            .find(|definition| tcx.def_path_str(definition.to_def_id()) == "make_future")
            .expect("fixture must contain the concrete async function");
        let instance = ty::Instance::mono(tcx, definition.to_def_id());
        let body = tcx.instance_mir(instance.def);
        let analysis = body.typing_env(tcx);
        let runtime = ty::TypingEnv::fully_monomorphized();
        assert!(matches!(analysis.typing_mode(), ty::TypingMode::PostAnalysis));
        assert!(matches!(runtime.typing_mode(), ty::TypingMode::Codegen));
        assert!(!instance.args.has_non_region_param());
        let extra = ty::List::empty();
        let rejected = tcx.fn_abi_of_instance(analysis.as_query_input((instance, extra)));
        assert!(
            format!("{:?}", rejected.unwrap_err()).contains("TooGeneric(Coroutine("),
            "the old environment must reproduce the actual coroutine layout rejection"
        );
        let direct = tcx
            .fn_abi_of_instance(runtime.as_query_input((instance, extra)))
            .expect("the concrete coroutine return ABI must exist during runtime Codegen");
        assert!(matches!(direct.ret.layout.ty.kind(), ty::Coroutine(..)));
        // Miri's direct-call path uses the no-deduced-attributes variant.
        let interpreter = tcx
            .fn_abi_of_instance_no_deduced_attrs(runtime.as_query_input((instance, extra)))
            .expect("the exact pinned Miri runtime ABI query must succeed");
        assert!(direct.ret.eq_abi(&interpreter.ret));
        let signature = instance.ty(tcx, runtime).fn_sig(tcx);
        assert!(
            tcx.fn_abi_of_fn_ptr(analysis.as_query_input((signature, extra))).is_err(),
            "function-pointer ABI queries must also expose the old environment failure"
        );
        let indirect = tcx
            .fn_abi_of_fn_ptr(runtime.as_query_input((signature, extra)))
            .expect("the concrete function-pointer ABI must exist during runtime Codegen");
        assert!(direct.ret.eq_abi(&indirect.ret));
        self.checked = true;
        Compilation::Stop
    }
}

#[test]
fn concrete_coroutine_abi_requires_the_runtime_codegen_environment() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let sysroot = std::env::var_os("MIRI_SYSROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| root.parent().unwrap().join("scratch/miri-sysroot"));
    let output = std::env::temp_dir().join(format!(
        "lean-miri-runtime-abi-{}-{}.rmeta",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let args = vec![
        "rustc".to_owned(),
        root.join("fixtures/fail_closed/runtime_async_abi.rs").to_string_lossy().into_owned(),
        "--crate-name=runtime_abi_probe".to_owned(),
        "--crate-type=lib".to_owned(),
        "--edition=2021".to_owned(),
        "--sysroot".to_owned(),
        sysroot.to_string_lossy().into_owned(),
        "--emit=metadata".to_owned(),
        "-o".to_owned(),
        output.to_string_lossy().into_owned(),
    ];
    let mut probe = RuntimeAbiProbe { checked: false };
    let status = rustc_driver::catch_with_exit_code(|| {
        rustc_driver::compiler_entrypoint(&args, &mut probe)
    });
    assert_eq!(status, std::process::ExitCode::SUCCESS, "pinned compiler probe failed");
    std::fs::remove_file(output).ok();
    assert!(probe.checked, "the compiler did not execute the ABI probe");
}
