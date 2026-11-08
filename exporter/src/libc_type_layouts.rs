//! Exact `helpers.rs::libc_ty_layout` and `libc_array_ty_layout` path queries.
//! The finite names below were collected from pinned Miri source call sites;
//! target-specific paths follow the same source OS guards.
use super::*;

const LIBC_LAYOUT_PATHS: &[&str] = &[
    "_umtx_time",
    "addrinfo",
    "clockid_t",
    "dirent",
    "dirent64",
    "epoll_event",
    "iovec",
    "linger",
    "mach_timebase_info",
    "mode_t",
    "nfds_t",
    "off_t",
    "os_unfair_lock_s",
    "passwd",
    "pollfd",
    "pthread_attr_t",
    "pthread_cond_t",
    "pthread_condattr_t",
    "pthread_key_t",
    "pthread_mutex_t",
    "pthread_mutexattr_t",
    "pthread_rwlock_t",
    "pthread_t",
    "sa_family_t",
    "sem_t",
    "size_t",
    "sockaddr",
    "sockaddr_in",
    "sockaddr_in6",
    "sockaddr_storage",
    "socklen_t",
    "stack_t",
    "statx",
    "timespec",
    "time_t",
    "timeval",
    "timezone",
    "tm",
    "utsname",
    "wchar_t",
];

fn required_on(os: &rustc_target::spec::Os, name: &str) -> bool {
    use rustc_target::spec::Os;
    match name {
        "_umtx_time" => os == &Os::FreeBsd,
        "mach_timebase_info" | "os_unfair_lock_s" => os == &Os::MacOs,
        "dirent64" | "statx" => os == &Os::Linux,
        "epoll_event" => matches!(os, Os::Linux | Os::Android),
        _ => true,
    }
}

fn query<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    name: &str,
) -> Result<Value, String> {
    let result = (|| -> Result<Value, String> {
        // This is the same exact crate/type namespace query as Miri's
        // resolve_path(tcx, &["libc", name], TypeNS), followed by layout_of.
        let instance =
            shim_abi::named_instance(tcx, &["libc", name], rustc_hir::def::Namespace::TypeNS)?;
        let ty = instance.ty(tcx, ty::TypingEnv::fully_monomorphized());
        if ty.has_escaping_bound_vars()
            || ty.has_non_region_param()
            || ty.has_infer()
            || ty.has_placeholders()
        {
            return Err("libc type path did not resolve to a closed monomorphic type".into());
        }
        match tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty)) {
            Ok(_) => Ok(type_json(context, tcx, ty)?),
            Err(error) => Err(format!(
                "rustc layout_of failed for libc::{name}: {error:?}"
            )),
        }
    })();
    Ok::<_, String>(match result {
        Ok(value) => json!({"status":"supported","value":value}),
        Err(reason) => export_failure("libc_type_layouts::query", format!("{}", reason))?,
    })
}

pub(super) fn export<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<Value, String> {
    let mut entries = serde_json::Map::new();
    for name in LIBC_LAYOUT_PATHS.iter().filter(|name| {
        (shim_abi::is_unix_target(tcx)
            || (**name == "wchar_t" && tcx.sess.target.os != rustc_target::spec::Os::Windows))
            && required_on(&tcx.sess.target.os, name)
    }) {
        entries.insert((*name).to_owned(), query(tcx, context, name)?);
    }
    Ok::<_, String>(json!({
        "crate_path": ["libc"],
        "namespace": "TypeNS",
        "typing_env": "fully_monomorphized",
        "entries": entries,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_target::spec::Os;
    #[test]
    fn source_os_guards_select_type_layouts() {
        assert!(required_on(&Os::Linux, "pthread_mutex_t"));
        assert!(required_on(&Os::Linux, "statx"));
        assert!(!required_on(&Os::MacOs, "statx"));
        assert!(required_on(&Os::MacOs, "os_unfair_lock_s"));
        assert!(!required_on(&Os::Linux, "os_unfair_lock_s"));
        assert!(required_on(&Os::FreeBsd, "_umtx_time"));
        assert!(!required_on(&Os::Android, "dirent64"));
        assert!(required_on(&Os::Linux, "missing_required_type"));
    }
}
