//! helpers.rs::eval_windows compiler constants. Values come only from the
//! pinned std::sys::pal::windows ValueNS path and const-evaluation query.
use super::*;

fn query<'tcx>(tcx: TyCtxt<'tcx>, context: &mut ExportContext<'tcx>, path: &[&str]) -> Value {
    let instance = match shim_abi::named_instance(tcx, path, rustc_hir::def::Namespace::ValueNS) {
        Ok(instance) => instance,
        Err(reason) => return json!({"status":"unsupported","reason":reason}),
    };
    if !matches!(
        tcx.def_kind(instance.def_id()),
        rustc_hir::def::DefKind::Const | rustc_hir::def::DefKind::AssocConst
    ) {
        return unavailable_compiler_fact(
            "Windows named scalar query did not resolve to a constant item",
        );
    }
    let environment = ty::TypingEnv::fully_monomorphized();
    let ty = instance.ty(tcx, environment);
    let evaluation = match tcx.const_eval_instance(environment, instance, rustc_span::DUMMY_SP) {
        Ok(value) => compiler_fact(const_value_json(context, tcx, ty, value)),
        Err(error) => {
            json!({"status":"unsupported","reason":"compiler Windows constant evaluation failed","error_debug":format!("{error:?}")})
        }
    };
    json!({"status":"supported","instance_kind":instance_kind_json(context,tcx,instance.def),
        "generic_args":generic_args_json(context,tcx,instance.args),"type":type_json(context,tcx,ty),
        "evaluation":evaluation})
}

/// Exact literal constants queried by pinned Miri Windows shims and its
/// Windows I/O error table. Unsupported target items stay as explicit rows.
pub(super) fn export<'tcx>(tcx: TyCtxt<'tcx>, context: &mut ExportContext<'tcx>) -> Vec<Value> {
    let names = [
        "CREATE_ALWAYS",
        "CREATE_NEW",
        "DLL_THREAD_DETACH",
        "DUPLICATE_SAME_ACCESS",
        "ERROR_BAD_USER_PROFILE",
        "ERROR_ENVVAR_NOT_FOUND",
        "ERROR_INSUFFICIENT_BUFFER",
        "ERROR_INVALID_PARAMETER",
        "ERROR_NOT_SUPPORTED",
        "FALSE",
        "FILE_ATTRIBUTE_ARCHIVE",
        "FILE_ATTRIBUTE_DEVICE",
        "FILE_ATTRIBUTE_DIRECTORY",
        "FILE_ATTRIBUTE_NORMAL",
        "FILE_BEGIN",
        "FILE_CURRENT",
        "FILE_END",
        "FILE_FLAG_BACKUP_SEMANTICS",
        "FILE_FLAG_OPEN_REPARSE_POINT",
        "FILE_SHARE_DELETE",
        "FILE_SHARE_READ",
        "FILE_SHARE_WRITE",
        "FileAllocationInfo",
        "FileEndOfFileInfo",
        "GENERIC_READ",
        "GENERIC_WRITE",
        "INFINITE",
        "INIT_ONCE_INIT_FAILED",
        "MOVEFILE_REPLACE_EXISTING",
        "OPEN_ALWAYS",
        "OPEN_EXISTING",
        "STACK_SIZE_PARAM_IS_A_RESERVATION",
        "STATUS_NOT_IMPLEMENTED",
        "STD_ERROR_HANDLE",
        "STD_INPUT_HANDLE",
        "STD_OUTPUT_HANDLE",
        "TRUE",
        "TRUNCATE_EXISTING",
        "WAIT_OBJECT_0",
        "WSAEADDRINUSE",
        "WSAEADDRNOTAVAIL",
        "ERROR_FILE_EXISTS",
        "ERROR_ALREADY_EXISTS",
        "ERROR_NO_DATA",
        "WSAECONNABORTED",
        "WSAECONNREFUSED",
        "WSAECONNRESET",
        "ERROR_NOT_SAME_DEVICE",
        "ERROR_POSSIBLE_DEADLOCK",
        "ERROR_DIR_NOT_EMPTY",
        "ERROR_CANT_RESOLVE_FILENAME",
        "ERROR_DISK_QUOTA_EXCEEDED",
        "WSAEDQUOT",
        "ERROR_FILE_TOO_LARGE",
        "ERROR_HOST_UNREACHABLE",
        "WSAEHOSTUNREACH",
        "ERROR_INVALID_NAME",
        "ERROR_BAD_PATHNAME",
        "ERROR_FILENAME_EXCED_RANGE",
        "WSAEINVAL",
        "ERROR_DIRECTORY_NOT_SUPPORTED",
        "WSAENETDOWN",
        "ERROR_NETWORK_UNREACHABLE",
        "WSAENETUNREACH",
        "ERROR_DIRECTORY",
        "WSAENOTCONN",
        "ERROR_FILE_NOT_FOUND",
        "ERROR_PATH_NOT_FOUND",
        "ERROR_INVALID_DRIVE",
        "ERROR_BAD_NETPATH",
        "ERROR_BAD_NET_NAME",
        "ERROR_SEEK_ON_DEVICE",
        "ERROR_NOT_ENOUGH_MEMORY",
        "ERROR_OUTOFMEMORY",
        "ERROR_ACCESS_DENIED",
        "WSAEACCES",
        "ERROR_WRITE_PROTECT",
        "ERROR_BUSY",
        "ERROR_DISK_FULL",
        "ERROR_HANDLE_DISK_FULL",
        "WAIT_TIMEOUT",
        "WSAETIMEDOUT",
        "ERROR_DRIVER_CANCEL_TIMEOUT",
        "ERROR_OPERATION_ABORTED",
        "ERROR_SERVICE_REQUEST_TIMEOUT",
        "ERROR_COUNTER_TIMEOUT",
        "ERROR_TIMEOUT",
        "ERROR_RESOURCE_CALL_TIMED_OUT",
        "ERROR_CTX_MODEM_RESPONSE_TIMEOUT",
        "ERROR_CTX_CLIENT_QUERY_TIMEOUT",
        "FRS_ERR_SYSVOL_POPULATE_TIMEOUT",
        "ERROR_DS_TIMELIMIT_EXCEEDED",
        "DNS_ERROR_RECORD_TIMED_OUT",
        "ERROR_IPSEC_IKE_TIMED_OUT",
        "ERROR_RUNLEVEL_SWITCH_TIMEOUT",
        "ERROR_RUNLEVEL_SWITCH_AGENT_TIMEOUT",
        "ERROR_TOO_MANY_LINKS",
        "ERROR_CALL_NOT_IMPLEMENTED",
        "WSAEWOULDBLOCK",
        "ERROR_TOO_MANY_OPEN_FILES",
        "ERROR_IO_DEVICE",
    ];
    names
        .iter()
        .map(|name| {
            let path = ["std", "sys", "pal", "windows", "c", *name];
            json!({"name":name,"path":path,"typing_env":"fully_monomorphized",
            "query":query(tcx,context,&path)})
        })
        .collect()
}
