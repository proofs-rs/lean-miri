//! Exact helpers.rs::windows_ty_layout TypeNS path queries.
//! Windows types are resolved only under std::sys::pal::windows::c and laid
//! out by the selected rustc target; non-Windows targets retain unsupported
//! rows rather than receiving host or handwritten layouts.
use super::*;

const WINDOWS_TYPE_LAYOUTS: &[&str] = &[
    "INIT_ONCE",
    "BY_HANDLE_FILE_INFORMATION",
    "FILE_END_OF_FILE_INFO",
    "FILE_ALLOCATION_INFO",
    "IO_STATUS_BLOCK",
    "SYSTEM_INFO",
    "FILETIME",
];

fn query<'tcx>(tcx: TyCtxt<'tcx>, context: &mut ExportContext<'tcx>, name: &str) -> Value {
    let result = (|| -> Result<Value, String> {
        let path = ["std", "sys", "pal", "windows", "c", name];
        let instance = shim_abi::named_instance(tcx, &path, rustc_hir::def::Namespace::TypeNS)?;
        let ty = instance.ty(tcx, ty::TypingEnv::fully_monomorphized());
        if ty.has_escaping_bound_vars()
            || ty.has_non_region_param()
            || ty.has_infer()
            || ty.has_placeholders()
        {
            return Err("Windows type path did not resolve to a closed monomorphic type".into());
        }
        tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
            .map_err(|error| format!("rustc layout_of failed for windows::{name}: {error:?}"))?;
        Ok(type_json(context, tcx, ty))
    })();
    match result {
        Ok(value) => json!({"status":"supported","value":value}),
        Err(reason) => json!({"status":"unsupported","value":null,"reason":reason}),
    }
}

pub(super) fn export<'tcx>(tcx: TyCtxt<'tcx>, context: &mut ExportContext<'tcx>) -> Value {
    let mut entries = serde_json::Map::new();
    // helpers.rs::windows_ty_layout is only a valid source query for Windows
    // targets. Keep the catalog's exact source identity everywhere, but do
    // not manufacture unsupported Windows-query rows while compiling another
    // target; non-Windows consumers cannot select these Windows shim arms.
    let names: &[&str] = if tcx.sess.target.os == rustc_target::spec::Os::Windows {
        WINDOWS_TYPE_LAYOUTS
    } else {
        &[]
    };
    for name in names {
        entries.insert((*name).to_owned(), query(tcx, context, name));
    }
    json!({
        "crate_path": ["std", "sys", "pal", "windows", "c"],
        "namespace": "TypeNS",
        "typing_env": "fully_monomorphized",
        "entries": entries,
    })
}
