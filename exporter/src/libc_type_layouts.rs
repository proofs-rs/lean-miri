//! Exact `helpers.rs::libc_ty_layout` and `libc_array_ty_layout` path queries.
//! The finite names below were collected from pinned Miri source call sites;
//! entries remain present when the target's libc crate lacks a path.
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

fn query<'tcx>(tcx: TyCtxt<'tcx>, context: &mut ExportContext<'tcx>, name: &str) -> Value {
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
            Ok(_) => Ok(type_json(context, tcx, ty)),
            Err(error) => Err(format!(
                "rustc layout_of failed for libc::{name}: {error:?}"
            )),
        }
    })();
    match result {
        Ok(value) => json!({"status":"supported","value":value}),
        Err(reason) => json!({"status":"unsupported","value":null,"reason":reason}),
    }
}

pub(super) fn export<'tcx>(tcx: TyCtxt<'tcx>, context: &mut ExportContext<'tcx>) -> Value {
    let mut entries = serde_json::Map::new();
    for name in LIBC_LAYOUT_PATHS {
        entries.insert((*name).to_owned(), query(tcx, context, name));
    }
    json!({
        "crate_path": ["libc"],
        "namespace": "TypeNS",
        "typing_env": "fully_monomorphized",
        "entries": entries,
    })
}
