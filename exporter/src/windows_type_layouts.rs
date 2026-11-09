//! Exact helpers.rs::windows_ty_layout TypeNS path queries.
//! Windows types are resolved only under std::sys::pal::windows::c and laid
//! out by the selected rustc target. Non-Windows targets do not request these
//! Windows-only shim layouts.
use super::*;
#[derive(serde::Serialize)]
pub(super) struct Catalog {
    crate_path: [&'static str; 5],
    namespace: &'static str,
    typing_env: &'static str,
    entries: BTreeMap<String, u64>,
}

const WINDOWS_TYPE_LAYOUTS: &[&str] = &[
    "INIT_ONCE",
    "BY_HANDLE_FILE_INFORMATION",
    "FILE_END_OF_FILE_INFO",
    "FILE_ALLOCATION_INFO",
    "IO_STATUS_BLOCK",
    "SYSTEM_INFO",
    "FILETIME",
];

fn query<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    name: &str,
) -> Result<u64, String> {
    let result = (|| -> Result<u64, String> {
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
        Ok(type_json(context, tcx, ty)?)
    })();
    Ok::<_, String>(match result {
        Ok(value) => value,
        Err(reason) => export_failure("windows_type_layouts::query", reason)?,
    })
}

pub(super) fn export<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<Catalog, String> {
    let mut entries = BTreeMap::new();
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
        entries.insert((*name).to_owned(), query(tcx, context, name)?);
    }
    Ok::<_, String>(Catalog {
        crate_path: ["std", "sys", "pal", "windows", "c"],
        namespace: "TypeNS",
        typing_env: "fully_monomorphized",
        entries,
    })
}
