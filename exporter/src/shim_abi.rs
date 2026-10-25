//! Exact shims/sig.rs ShimSig::as_abi and shim_sig_arg constructors.
//! Recipes mirror currently ported alloc/foreign_items/mem/miri source arms.
use super::*;
// helpers.rs::try_resolve_did TypeNS path lookup. Try matching crates in the
// compiler's own order and select only module/type namespaces as the source.
pub(super) fn named_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    path: &[&str],
    namespace: rustc_hir::def::Namespace,
) -> Result<ty::Instance<'tcx>, String> {
    let Some((crate_name, rest)) = path.split_first() else {
        return Err("empty compiler type path".into());
    };
    let Some((item, modules)) = rest.split_last() else {
        return Err("compiler type path lacks item".into());
    };
    'crates: for krate in tcx
        .crates(())
        .iter()
        .copied()
        .filter(|krate| tcx.crate_name(*krate).as_str() == *crate_name)
    {
        let mut def = krate.as_def_id();
        for segment in modules {
            let next = tcx.module_children(def).iter().find_map(|child| {
                if child.ident.name.as_str() != *segment {
                    return None;
                }
                if let rustc_hir::def::Res::Def(rustc_hir::def::DefKind::Mod, def) = child.res {
                    Some(def)
                } else {
                    None
                }
            });
            let Some(next) = next else { continue 'crates };
            def = next;
        }
        if let Some(def) = tcx.module_children(def).iter().find_map(|child| {
            if child.ident.name.as_str() != *item {
                return None;
            }
            if let rustc_hir::def::Res::Def(kind, def) = child.res {
                (kind.ns() == Some(namespace)).then_some(def)
            } else {
                None
            }
        }) {
            let args = ty::GenericArgs::identity_for_item(tcx, def);
            if args.has_non_region_param() {
                return Err("compiler path requires type/const instantiation".into());
            }
            return Ok(ty::Instance::mono(tcx, def));
        }
    }
    Err(format!("compiler type path not found: {path:?}"))
}

fn named_type<'tcx>(tcx: TyCtxt<'tcx>, path: &[&str]) -> Result<ty::Ty<'tcx>, String> {
    Ok(
        named_instance(tcx, path, rustc_hir::def::Namespace::TypeNS)?
            .ty(tcx, ty::TypingEnv::fully_monomorphized()),
    )
}

pub(super) fn descriptor<'tcx>(tcx: TyCtxt<'tcx>, key: &str) -> Result<ty::Ty<'tcx>, String> {
    Ok(match key {
        "unit" => tcx.types.unit,
        "usize" => tcx.types.usize,
        "isize" => tcx.types.isize,
        "i32" => tcx.types.i32,
        "i64" => tcx.types.i64,
        "u32" => tcx.types.u32,
        "u64" => tcx.types.u64,
        "u16" => tcx.types.u16,
        "u8" => tcx.types.u8,
        "bool" => tcx.types.bool,
        "never" => tcx.types.never,
        "unitPointer" => ty::Ty::new_mut_ptr(tcx, tcx.types.unit),
        "pointer" => {
            // PrimitiveLayouts::new source fallback is explicit, including no_core.
            let pointee = match tcx.lang_items().c_void() {
                Some(def) => {
                    ty::Instance::mono(tcx, def).ty(tcx, ty::TypingEnv::fully_monomorphized())
                }
                None => tcx.types.unit,
            };
            ty::Ty::new_mut_ptr(tcx, pointee)
        }
        "alignment" => named_type(tcx, &["core", "mem", "Alignment"])?,
        "libc::pid_t" => named_type(tcx, &["libc", "pid_t"])?,
        "libc::nfds_t" => named_type(tcx, &["libc", "nfds_t"])?,
        "libc::socklen_t" => named_type(tcx, &["libc", "socklen_t"])?,
        "libc::size_t" => named_type(tcx, &["libc", "size_t"])?,
        "libc::ssize_t" => named_type(tcx, &["libc", "ssize_t"])?,
        "libc::mode_t" => named_type(tcx, &["libc", "mode_t"])?,
        "libc::stat_pointer" => ty::Ty::new_mut_ptr(tcx, named_type(tcx, &["libc", "stat"])?),
        "libc::stat64_pointer" => ty::Ty::new_mut_ptr(tcx, named_type(tcx, &["libc", "stat64"])?),
        "libc::off_t" => named_type(tcx, &["libc", "off_t"])?,
        "libc::off64_t" => named_type(tcx, &["libc", "off64_t"])?,
        "libc::clockid_t" => named_type(tcx, &["libc", "clockid_t"])?,
        "libc::time_t" => named_type(tcx, &["libc", "time_t"])?,
        "libc::timeval_pointer" => ty::Ty::new_mut_ptr(tcx, named_type(tcx, &["libc", "timeval"])?),
        "libc::timezone_pointer" => ty::Ty::new_mut_ptr(tcx, named_type(tcx, &["libc", "timezone"])?),
        "libc::time_t_pointer" => ty::Ty::new_mut_ptr(tcx, named_type(tcx, &["libc", "time_t"])?),
        "libc::tm_pointer" => ty::Ty::new_mut_ptr(tcx, named_type(tcx, &["libc", "tm"])?),
        "libc::timespec_pointer" => ty::Ty::new_mut_ptr(tcx, named_type(tcx, &["libc", "timespec"])?),

        "libc::uid_t" => named_type(tcx, &["libc", "uid_t"])?,
        "libc::pthread_t" => named_type(tcx, &["libc", "pthread_t"])?,
        "libc::pthread_key_t" => named_type(tcx, &["libc", "pthread_key_t"])?,
        "unwind_reason_code" => {
            named_type(tcx, &["panic_unwind", "imp", "uw", "_Unwind_Reason_Code"])?
        }
        "winapi::BOOL" => named_type(tcx, &["std", "sys", "pal", "windows", "c", "BOOL"])?,
        "byteSlice" => ty::Ty::new_imm_ref(
            tcx,
            tcx.lifetimes.re_erased,
            ty::Ty::new_slice(tcx, tcx.types.u8),
        ),
        "functionPointer" => ty::Ty::new_fn_ptr(
            tcx,
            ty::Binder::dummy(
                tcx.mk_fn_sig(
                    [],
                    tcx.types.unit,
                    ty::FnSigKind::default()
                        .set_abi(rustc_abi::ExternAbi::C { unwind: false })
                        .set_safety(rustc_hir::Safety::Safe),
                ),
            ),
        ),
        _ if key.starts_with("winapi::") => {
            let name = &key["winapi::".len()..];
            named_type(tcx, &["std", "sys", "pal", "windows", "c", name])?
        }
        _ => return Err(format!("unsupported exact shim type descriptor {key}")),
    })
}
fn query<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    abi: &str,
    args: &[&str],
    ret: &str,
) -> Value {
    variadic_query(tcx, context, abi, args, ret, false)
}
fn variadic_query<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    abi: &str,
    args: &[&str],
    ret: &str,
    variadic: bool,
) -> Value {
    let result = (|| -> Result<Value, String> {
        let inputs = args
            .iter()
            .map(|key| descriptor(tcx, key))
            .collect::<Result<Vec<_>, _>>()?;
        let output = descriptor(tcx, ret)?;
        let external = match abi {
            "C" => rustc_abi::ExternAbi::C { unwind: false },
            "Rust" => rustc_abi::ExternAbi::Rust,
            "System" => rustc_abi::ExternAbi::System { unwind: false },
            _ => return Err("unsupported exact shim ABI".into()),
        };
        let signature = ty::Binder::dummy(
            tcx.mk_fn_sig(
                inputs.iter().copied(),
                output,
                ty::FnSigKind::default()
                    .set_c_variadic(variadic)
                    .set_abi(external),
            ),
        );
        let input_types = inputs
            .iter()
            .map(|ty| type_json(context, tcx, *ty))
            .collect::<Vec<_>>();
        let output_type = type_json(context, tcx, output);
        let value = match tcx.fn_abi_of_fn_ptr(
            ty::TypingEnv::fully_monomorphized().as_query_input((signature, ty::List::empty())),
        ) {
            Ok(abi) => compiler_fact(fn_abi_json(context, tcx, abi)),
            Err(error) => {
                json!({"status":"unsupported","reason":"rustc fn_abi_of_fn_ptr failed","error_debug":format!("{error:?}")})
            }
        };
        Ok(
            json!({"status":"supported","input_types":input_types,"output_type":output_type,"abi_query":value}),
        )
    })();
    json!({"typing_env":"fully_monomorphized","signature":{"calling_convention":abi,"arguments":args,"return":ret,"c_variadic":variadic},
        "query":match result{Ok(value)=>value,Err(reason)=>json!({"status":"unsupported","reason":reason})}})
}
pub(super) fn export<'tcx>(tcx: TyCtxt<'tcx>, context: &mut ExportContext<'tcx>) -> Value {
    let recipes: &[(&str, &[&str], &str)] = &[
        ("Rust", &[], "unit"),
        ("Rust", &["usize", "alignment"], "unitPointer"),
        ("Rust", &["unitPointer", "usize", "alignment"], "unit"),
        (
            "Rust",
            &["unitPointer", "usize", "alignment", "usize"],
            "unitPointer",
        ),
        ("C", &["usize"], "pointer"),
        ("C", &["usize", "usize"], "pointer"),
        ("C", &["pointer", "usize"], "pointer"),
        ("C", &["pointer"], "unit"),
        ("C", &["i32"], "unit"),
        ("C", &[], "unit"),
        ("C", &["pointer", "pointer", "usize"], "i32"),
        ("C", &["pointer", "i32", "usize"], "pointer"),
        ("C", &["pointer"], "usize"),
        ("C", &["pointer", "usize"], "usize"),
        ("C", &["pointer", "pointer", "usize"], "pointer"),
        ("C", &["pointer", "pointer"], "pointer"),
        // CompilerShimAbi queries for pthread mutex/condition/semaphore
        // checks. The source wildcard pointers lower to the same canonical
        // c_void pointer type regardless of the shim operation using them.
        ("C", &["pointer"], "i32"),
        ("C", &["pointer", "i32"], "i32"),
        ("C", &["pointer", "pointer"], "i32"),
        ("C", &["pointer", "pointer", "pointer"], "i32"),
        ("C", &["pointer", "i32", "u32"], "i32"),
        ("Rust", &["usize", "usize"], "unitPointer"),
        ("Rust", &["unitPointer", "usize", "usize"], "unit"),
        ("Rust", &["unitPointer"], "unit"),
        ("Rust", &["unitPointer"], "never"),
        ("Rust", &["unitPointer"], "u64"),
        ("Rust", &["u64", "bool"], "unit"),
        ("Rust", &["unitPointer", "u8", "byteSlice"], "unit"),
        ("Rust", &["unitPointer", "unitPointer", "usize"], "usize"),
        ("Rust", &["functionPointer", "unitPointer"], "usize"),
        ("Rust", &["usize"], "bool"),
        ("Rust", &["byteSlice"], "unit"),
        ("Rust", &["unitPointer", "usize"], "unit"),
        ("Rust", &["bool"], "unit"),
        // shims/backtrace.rs strict APIs; deprecated resolve_frame intentionally
        // has no guessed full return-structure signature.
        ("Rust", &["u64"], "usize"),
        ("Rust", &["u64", "unitPointer"], "unit"),
        (
            "Rust",
            &["unitPointer", "u64", "unitPointer", "unitPointer"],
            "unit",
        ),
    ];
    Value::Array(
        recipes
            .iter()
            .map(|(abi, args, ret)| query(tcx, context, abi, args, ret))
            .collect(),
    )
}

// Source unix/foreign_items.rs sched_{get,set}affinity exact declarations.
pub(super) fn named_signatures<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Value {
    let recipes: &[(&str, &[&str], &str)] = &[
        // Unix environment/system-information checks from
        // shims/unix/foreign_items.rs. The libc aliases stay type queries: we
        // never substitute a host-sized or target-triple-derived integer.
        ("getenv", &["pointer"], "pointer"),
        ("unsetenv", &["pointer"], "i32"),
        ("setenv", &["pointer", "pointer", "i32"], "i32"),
        ("getcwd", &["pointer", "usize"], "pointer"),
        ("gethostname", &["pointer", "usize"], "i32"),
        ("chdir", &["pointer"], "i32"),
        ("getpid", &[], "libc::pid_t"),
        ("uname", &["pointer"], "i32"),
        ("sysconf", &["i32"], "isize"),
        ("strerror_r", &["i32", "pointer", "usize"], "i32"),
        ("getuid", &[], "libc::uid_t"),
        ("geteuid", &[], "libc::uid_t"),
        ("__xuname", &["i32", "pointer"], "i32"),
        // Unix descriptor and file shims from the same pinned source module.
        ("read", &["i32", "pointer", "usize"], "isize"),
        ("write", &["i32", "pointer", "usize"], "isize"),
        (
            "pread",
            &["i32", "pointer", "usize", "libc::off_t"],
            "isize",
        ),
        (
            "pwrite",
            &["i32", "pointer", "usize", "libc::off_t"],
            "isize",
        ),
        (
            "pread64",
            &["i32", "pointer", "usize", "libc::off64_t"],
            "isize",
        ),
        (
            "pwrite64",
            &["i32", "pointer", "usize", "libc::off64_t"],
            "isize",
        ),
        ("close", &["i32"], "i32"),
        ("dup", &["i32"], "i32"),
        ("dup2", &["i32", "i32"], "i32"),
        (
            "sched_getaffinity",
            &["libc::pid_t", "usize", "pointer"],
            "i32",
        ),
        (
            "sched_setaffinity",
            &["libc::pid_t", "usize", "pointer"],
            "i32",
        ),
        ("posix_memalign", &["pointer", "usize", "usize"], "i32"),
        (
            "mmap",
            &["pointer", "usize", "i32", "i32", "i32", "libc::off_t"],
            "pointer",
        ),
        ("munmap", &["pointer", "usize"], "i32"),
        ("mprotect", &["pointer", "usize", "i32"], "i32"),
        ("madvise", &["pointer", "usize", "i32"], "i32"),
        ("reallocarray", &["pointer", "usize", "usize"], "pointer"),
        ("aligned_alloc", &["usize", "usize"], "pointer"),
        (
            "pthread_create",
            &["pointer", "pointer", "functionPointer", "pointer"],
            "i32",
        ),
        ("pthread_join", &["libc::pthread_t", "pointer"], "i32"),
        ("pthread_detach", &["libc::pthread_t"], "i32"),
        ("pthread_self", &[], "libc::pthread_t"),
        ("sched_yield", &[], "i32"),
        ("poll", &["pointer", "libc::nfds_t", "i32"], "i32"),
        // Strict time and synchronization shim signatures from pinned
        // shims/unix/foreign_items.rs. Typed libc pointer slots use exact
        // TypeNS aliases; `*_` slots retain the source wildcard c_void pointer.
        (
            "gettimeofday",
            &["libc::timeval_pointer", "libc::timezone_pointer"],
            "i32",
        ),
        (
            "localtime_r",
            &["libc::time_t_pointer", "libc::tm_pointer"],
            "libc::tm_pointer",
        ),
        (
            "clock_gettime",
            &["libc::clockid_t", "libc::timespec_pointer"],
            "i32",
        ),
        ("nanosleep", &["pointer", "pointer"], "i32"),
        (
            "clock_nanosleep",
            &["libc::clockid_t", "i32", "pointer", "pointer"],
            "i32",
        ),
        // Strict Unix FS check_shim_sig! declarations in
        // shims/unix/foreign_items.rs. Named libc aliases and typed stat
        // pointers stay exact TypeNS compiler queries.
        ("unlink", &["pointer"], "i32"),
        ("symlink", &["pointer", "pointer"], "i32"),
        ("linkat", &["i32", "pointer", "i32", "pointer", "i32"], "i32"),
        ("stat", &["pointer", "libc::stat_pointer"], "i32"),
        ("lstat", &["pointer", "libc::stat_pointer"], "i32"),
        ("fstat", &["i32", "libc::stat_pointer"], "i32"),
        (
            "fstatat",
            &["i32", "pointer", "libc::stat_pointer", "i32"],
            "i32",
        ),
        ("chmod", &["pointer", "libc::mode_t"], "i32"),
        ("fchmod", &["i32", "libc::mode_t"], "i32"),
        ("rename", &["pointer", "pointer"], "i32"),
        ("mkdir", &["pointer", "libc::mode_t"], "i32"),
        ("rmdir", &["pointer"], "i32"),
        ("opendir", &["pointer"], "pointer"),
        ("readdir", &["pointer"], "pointer"),
        ("dirfd", &["pointer"], "i32"),
        ("closedir", &["pointer"], "i32"),
        (
            "lseek",
            &["i32", "libc::off_t", "i32"],
            "libc::off_t",
        ),
        ("ftruncate", &["i32", "libc::off_t"], "i32"),
        ("fsync", &["i32"], "i32"),
        ("fdatasync", &["i32"], "i32"),
        ("futimens", &["i32", "pointer"], "i32"),
        ("utimensat", &["i32", "pointer", "pointer", "i32"], "i32"),
        ("readlink", &["pointer", "pointer", "usize"], "isize"),
        (
            "posix_fadvise",
            &["i32", "libc::off_t", "libc::off_t", "i32"],
            "i32",
        ),
        (
            "posix_fallocate",
            &["i32", "libc::off_t", "libc::off_t"],
            "i32",
        ),
        ("realpath", &["pointer", "pointer"], "pointer"),
        ("mkstemp", &["pointer"], "i32"),
        ("flock", &["i32", "i32"], "i32"),
        ("isatty", &["i32"], "i32"),
        // Linux/Android exact strict large-file declarations in
        // shims/unix/{linux,android}/foreign_items.rs.
        (
            "lseek64",
            &["i32", "libc::off64_t", "i32"],
            "libc::off64_t",
        ),
        ("ftruncate64", &["i32", "libc::off64_t"], "i32"),
        (
            "fallocate",
            &["i32", "i32", "libc::off_t", "libc::off_t"],
            "i32",
        ),
        (
            "fallocate64",
            &["i32", "i32", "libc::off64_t", "libc::off64_t"],
            "i32",
        ),
        (
            "posix_fallocate64",
            &["i32", "libc::off64_t", "libc::off64_t"],
            "i32",
        ),
        ("fstat64", &["i32", "libc::stat64_pointer"], "i32"),
        // macOS strict ABI aliases; stat/lstat aliases in the same source
        // intentionally use the deprecated checker and are not listed.
        (
            "fstat$INODE64",
            &["i32", "libc::stat_pointer"],
            "i32",
        ),
        (
            "fstatat$INODE64",
            &["i32", "pointer", "libc::stat_pointer", "i32"],
            "i32",
        ),
        // Darwin dispatch semaphore/time shims use the exact strict
        // `check_shim_sig!(shim_sig!(extern "C" ...))` declarations in the
        // pinned unix/macos/foreign_items.rs. Keep their pointer wildcard and
        // signed 64-bit delta as compiler type descriptors.
        ("dispatch_semaphore_create", &["isize"], "pointer"),
        ("dispatch_semaphore_wait", &["pointer", "u64"], "isize"),
        ("dispatch_semaphore_signal", &["pointer"], "isize"),
        ("dispatch_release", &["pointer"], "unit"),
        ("dispatch_time", &["u64", "i64"], "u64"),
        // Unix socket and pipe check_shim_sig! declarations in
        // shims/unix/foreign_items.rs. libc typedefs resolve through rustc's
        // exact libc TypeNS paths; generic pointer slots use the same c_void
        // descriptor as the source shim signature wildcard.
        ("socketpair", &["i32", "i32", "i32", "pointer"], "i32"),
        ("pipe", &["pointer"], "i32"),
        ("pipe2", &["pointer", "i32"], "i32"),
        ("socket", &["i32", "i32", "i32"], "i32"),
        ("bind", &["i32", "pointer", "libc::socklen_t"], "i32"),
        ("listen", &["i32", "i32"], "i32"),
        ("accept", &["i32", "pointer", "pointer"], "i32"),
        ("accept4", &["i32", "pointer", "pointer", "i32"], "i32"),
        ("connect", &["i32", "pointer", "libc::socklen_t"], "i32"),
        (
            "send",
            &["i32", "pointer", "libc::size_t", "i32"],
            "libc::ssize_t",
        ),
        (
            "recv",
            &["i32", "pointer", "libc::size_t", "i32"],
            "libc::ssize_t",
        ),
        (
            "setsockopt",
            &["i32", "i32", "i32", "pointer", "libc::socklen_t"],
            "i32",
        ),
        (
            "getsockopt",
            &["i32", "i32", "i32", "pointer", "pointer"],
            "i32",
        ),
        ("getsockname", &["i32", "pointer", "pointer"], "i32"),
        ("getpeername", &["i32", "pointer", "pointer"], "i32"),
        ("shutdown", &["i32", "i32"], "i32"),
        ("getaddrinfo", &["pointer", "pointer", "pointer", "pointer"], "i32"),
        ("freeaddrinfo", &["pointer"], "unit"),
        // Solaris/illumos strict socket aliases in
        // shims/unix/solarish/foreign_items.rs. __xnet_socketpair is omitted
        // because the pinned source uses the deprecated ABI checker there.
        ("__xnet_socket", &["i32", "i32", "i32"], "i32"),
        ("__xnet7_socket", &["i32", "i32", "i32"], "i32"),
        (
            "__xnet_bind",
            &["i32", "pointer", "libc::socklen_t"],
            "i32",
        ),
        (
            "__xnet_connect",
            &["i32", "pointer", "libc::socklen_t"],
            "i32",
        ),
        (
            "__xnet_getaddrinfo",
            &["pointer", "pointer", "pointer", "pointer"],
            "i32",
        ),
        (
            "__xnet_getsockopt",
            &["i32", "i32", "i32", "pointer", "pointer"],
            "i32",
        ),
        // unix/foreign_items.rs random shims, exact shim_sig! recipes.
        ("getentropy", &["pointer", "usize"], "i32"),
        ("getrandom", &["pointer", "usize", "u32"], "isize"),
        ("arc4random_buf", &["pointer", "usize"], "unit"),
        ("readv", &["i32", "pointer", "i32"], "isize"),
        ("writev", &["i32", "pointer", "i32"], "isize"),
        ("preadv", &["i32", "pointer", "i32", "libc::off_t"], "isize"),
        (
            "pwritev",
            &["i32", "pointer", "i32", "libc::off_t"],
            "isize",
        ),
        ("dlsym", &["pointer", "pointer"], "pointer"),
        ("_Unwind_RaiseException", &["pointer"], "unwind_reason_code"),
        ("pthread_key_create", &["pointer", "functionPointer"], "i32"),
        ("pthread_key_delete", &["libc::pthread_key_t"], "i32"),
        ("pthread_getspecific", &["libc::pthread_key_t"], "pointer"),
        (
            "pthread_setspecific",
            &["libc::pthread_key_t", "pointer"],
            "i32",
        ),
        (
            "pthread_atfork",
            &["functionPointer", "functionPointer", "functionPointer"],
            "i32",
        ),
    ];
    let mut result = recipes
        .iter()
        .map(|(name, args, ret)| json!({"name":name,"recipe":query(tcx,context,"C",args,ret)}))
        .collect::<Vec<_>>();
    // Linux GNU TLS destructor registration is strict in
    // shims/unix/linux/foreign_items.rs. Preserve the source's three wildcard
    // pointer arguments and int result, and emit the record only for the GNU
    // environment where Miri accepts this symbol.
    if tcx.sess.target.env == rustc_target::spec::Env::Gnu {
        result.push(json!({
            "name":"__cxa_thread_atexit_impl",
            "recipe":query(tcx,context,"C",&["pointer","pointer","pointer"],"i32")
        }));
    }
    // The pinned Linux foreign-item arm checks this exact variadic C
    // declaration. Keep it Linux-targeted because the connected Miri/Lean
    // dispatch is selected only for Linux, and preserve the wildcard pointer
    // return and four fixed arguments from shim_sig!.
    if tcx.sess.target.os == rustc_target::spec::Os::Linux {
        result.push(json!({
            "name":"mremap",
            "recipe":variadic_query(tcx,context,"C",&["pointer","usize","usize","i32"],"pointer",true)
        }));
    }
    // `open` and `openat` have source-checked C varargs, so retain variadic
    // FnAbi and the exact fixed argument prefix in the named compiler query.
    for (name, args) in [
        ("open", &["pointer", "i32"][..]),
        ("openat", &["i32", "pointer", "i32"][..]),
        ("open64", &["pointer", "i32"][..]),
        ("openat64", &["i32", "pointer", "i32"][..]),
    ] {
        result.push(json!({"name":name,"recipe":variadic_query(tcx,context,"C",args,"i32",true)}));
    }
    // Windows foreign_items.rs strict check_shim_sig! declarations. The
    // Windows aliases are resolved from std's exact target module through
    // descriptor(); this makes non-Windows target absence explicit and keeps
    // pointer-width-dependent aliases under rustc's target ABI query.
    let windows: &[(&str, &[&str], &str)] = &[
        (
            "GetEnvironmentVariableW",
            &["pointer", "pointer", "u32"],
            "u32",
        ),
        (
            "SetEnvironmentVariableW",
            &["pointer", "pointer"],
            "winapi::BOOL",
        ),
        ("GetEnvironmentStringsW", &[], "pointer"),
        ("FreeEnvironmentStringsW", &["pointer"], "winapi::BOOL"),
        ("GetCurrentDirectoryW", &["u32", "pointer"], "u32"),
        ("SetCurrentDirectoryW", &["pointer"], "winapi::BOOL"),
        (
            "GetUserProfileDirectoryW",
            &["winapi::HANDLE", "pointer", "pointer"],
            "winapi::BOOL",
        ),
        ("GetCurrentProcessId", &[], "u32"),
        ("GetTempPathW", &["u32", "pointer"], "u32"),
        (
            "NtWriteFile",
            &[
                "winapi::HANDLE",
                "winapi::HANDLE",
                "pointer",
                "pointer",
                "pointer",
                "pointer",
                "u32",
                "pointer",
                "pointer",
            ],
            "i32",
        ),
        (
            "NtReadFile",
            &[
                "winapi::HANDLE",
                "winapi::HANDLE",
                "pointer",
                "pointer",
                "pointer",
                "pointer",
                "u32",
                "pointer",
                "pointer",
            ],
            "i32",
        ),
        (
            "GetFullPathNameW",
            &["pointer", "u32", "pointer", "pointer"],
            "u32",
        ),
        (
            "CreateFileW",
            &[
                "pointer",
                "u32",
                "u32",
                "pointer",
                "u32",
                "u32",
                "winapi::HANDLE",
            ],
            "winapi::HANDLE",
        ),
        (
            "GetFileInformationByHandle",
            &["winapi::HANDLE", "pointer"],
            "winapi::BOOL",
        ),
        (
            "SetFileInformationByHandle",
            &[
                "winapi::HANDLE",
                "winapi::FILE_INFO_BY_HANDLE_CLASS",
                "pointer",
                "u32",
            ],
            "winapi::BOOL",
        ),
        ("FlushFileBuffers", &["winapi::HANDLE"], "winapi::BOOL"),
        ("DeleteFileW", &["pointer"], "winapi::BOOL"),
        (
            "SetFilePointerEx",
            &["winapi::HANDLE", "i64", "pointer", "u32"],
            "winapi::BOOL",
        ),
        (
            "MoveFileExW",
            &["pointer", "pointer", "u32"],
            "winapi::BOOL",
        ),
        ("HeapAlloc", &["winapi::HANDLE", "u32", "usize"], "pointer"),
        (
            "HeapFree",
            &["winapi::HANDLE", "u32", "pointer"],
            "winapi::BOOL",
        ),
        (
            "HeapReAlloc",
            &["winapi::HANDLE", "u32", "pointer", "usize"],
            "pointer",
        ),
        ("LocalFree", &["winapi::HLOCAL"], "winapi::HLOCAL"),
        ("SetLastError", &["u32"], "unit"),
        ("GetLastError", &[], "u32"),
        ("RtlNtStatusToDosError", &["i32"], "u32"),
        ("GetSystemInfo", &["pointer"], "unit"),
        ("TlsAlloc", &[], "u32"),
        ("TlsGetValue", &["u32"], "pointer"),
        ("TlsSetValue", &["u32", "pointer"], "winapi::BOOL"),
        ("TlsFree", &["u32"], "winapi::BOOL"),
        ("FlsAlloc", &["winapi::PFLS_CALLBACK_FUNCTION"], "u32"),
        ("FlsGetValue", &["u32"], "pointer"),
        ("FlsSetValue", &["u32", "pointer"], "winapi::BOOL"),
        ("FlsFree", &["u32"], "winapi::BOOL"),
        ("IsThreadAFiber", &[], "winapi::BOOL"),
        ("GetCommandLineW", &[], "pointer"),
        ("GetSystemTimeAsFileTime", &["pointer"], "unit"),
        ("GetSystemTimePreciseAsFileTime", &["pointer"], "unit"),
        ("QueryPerformanceCounter", &["pointer"], "winapi::BOOL"),
        ("QueryPerformanceFrequency", &["pointer"], "winapi::BOOL"),
        ("Sleep", &["u32"], "unit"),
        (
            "CreateWaitableTimerExW",
            &["pointer", "pointer", "u32", "u32"],
            "winapi::HANDLE",
        ),
        (
            "InitOnceBeginInitialize",
            &["pointer", "u32", "pointer", "pointer"],
            "winapi::BOOL",
        ),
        (
            "InitOnceComplete",
            &["pointer", "u32", "pointer"],
            "winapi::BOOL",
        ),
        (
            "WaitOnAddress",
            &["pointer", "pointer", "usize", "u32"],
            "winapi::BOOL",
        ),
        ("WakeByAddressSingle", &["pointer"], "unit"),
        ("WakeByAddressAll", &["pointer"], "unit"),
        (
            "GetProcAddress",
            &["winapi::HMODULE", "pointer"],
            "winapi::FARPROC",
        ),
        (
            "CreateThread",
            &["pointer", "usize", "pointer", "pointer", "u32", "pointer"],
            "winapi::HANDLE",
        ),
        ("WaitForSingleObject", &["winapi::HANDLE", "u32"], "u32"),
        ("GetCurrentProcess", &[], "winapi::HANDLE"),
        ("GetCurrentThread", &[], "winapi::HANDLE"),
        (
            "SetThreadDescription",
            &["winapi::HANDLE", "pointer"],
            "i32",
        ),
        (
            "GetThreadDescription",
            &["winapi::HANDLE", "pointer"],
            "i32",
        ),
        ("GetThreadId", &["winapi::HANDLE"], "u32"),
        ("GetCurrentThreadId", &[], "u32"),
        ("ExitProcess", &["u32"], "unit"),
        (
            "GetConsoleScreenBufferInfo",
            &["winapi::HANDLE", "pointer"],
            "winapi::BOOL",
        ),
        ("GetStdHandle", &["u32"], "winapi::HANDLE"),
        (
            "DuplicateHandle",
            &[
                "winapi::HANDLE",
                "winapi::HANDLE",
                "winapi::HANDLE",
                "pointer",
                "u32",
                "winapi::BOOL",
                "u32",
            ],
            "winapi::BOOL",
        ),
        ("CloseHandle", &["winapi::HANDLE"], "winapi::BOOL"),
        (
            "GetModuleFileNameW",
            &["winapi::HMODULE", "pointer", "u32"],
            "u32",
        ),
        (
            "FormatMessageW",
            &["u32", "pointer", "u32", "u32", "pointer", "u32", "pointer"],
            "u32",
        ),
        (
            "NtQueryVolumeInformationFile",
            &["winapi::HANDLE", "pointer", "pointer", "u32", "i32"],
            "i32",
        ),
        ("GetProcessHeap", &[], "winapi::HANDLE"),
        ("GetModuleHandleA", &["pointer"], "winapi::HMODULE"),
        (
            "SetConsoleTextAttribute",
            &["winapi::HANDLE", "u16"],
            "winapi::BOOL",
        ),
        (
            "AddVectoredExceptionHandler",
            &["u32", "pointer"],
            "pointer",
        ),
        ("SetThreadStackGuarantee", &["pointer"], "winapi::BOOL"),
        ("SwitchToThread", &[], "winapi::BOOL"),
        (
            "GetFinalPathNameByHandleW",
            &["winapi::HANDLE", "pointer", "u32", "u32"],
            "u32",
        ),
    ];
    for (name, args, ret) in windows {
        result.push(json!({"name":name,"recipe":query(tcx,context,"System",args,ret)}));
    }
    // windows/foreign_items.rs random shims, preserving source System ABI.
    for (name, args, ret) in [
        ("SystemFunction036", &["pointer", "u32"][..], "u8"),
        ("ProcessPrng", &["pointer", "usize"][..], "winapi::BOOL"),
        (
            "BCryptGenRandom",
            &["pointer", "pointer", "u32", "u32"][..],
            "i32",
        ),
    ] {
        result.push(json!({"name":name,"recipe":query(tcx,context,"System",args,ret)}));
    }
    result.push(
        json!({"name":"syscall","recipe":variadic_query(tcx,context,"C",&["isize"],"isize",true)}),
    );
    result
        .push(json!({"name":"prctl","recipe":variadic_query(tcx,context,"C",&["i32"],"i32",true)}));
    result.push(
        json!({"name":"fcntl","recipe":variadic_query(tcx,context,"C",&["i32","i32"],"i32",true)}),
    );
    // unix/foreign_items.rs:328 target-spec query, not host/triple inference.
    let ulong = match tcx.sess.target.os {
        rustc_target::spec::Os::FreeBsd
        | rustc_target::spec::Os::NetBsd
        | rustc_target::spec::Os::MacOs => true,
        rustc_target::spec::Os::Linux if tcx.sess.target.env == rustc_target::spec::Env::Gnu => {
            true
        }
        _ => false,
    };
    result.push(json!({"name":"ioctl","recipe":variadic_query(tcx,context,"C",&["i32",if ulong{"usize"}else{"i32"}],"i32",true),
        "source_target_op_is_ulong":ulong}));
    Value::Array(result)
}

pub(super) fn named_types<'tcx>(tcx: TyCtxt<'tcx>, context: &mut ExportContext<'tcx>) -> Value {
    let mut result = serde_json::Map::new();
    for (name, path) in [
        ("c_ulong", &["core", "ffi", "c_ulong"][..]),
        ("pid_t", &["libc", "pid_t"][..]),
        ("uid_t", &["libc", "uid_t"][..]),
        ("nfds_t", &["libc", "nfds_t"][..]),
        ("off_t", &["libc", "off_t"][..]),
        ("off64_t", &["libc", "off64_t"][..]),
        ("wchar_t", &["libc", "wchar_t"][..]),
        ("pthread_t", &["libc", "pthread_t"][..]),
        ("pthread_key_t", &["libc", "pthread_key_t"][..]),
    ] {
        let value = match named_type(tcx, path) {
            Ok(ty) => compiler_fact(type_json(context, tcx, ty)),
            Err(reason) => json!({"status":"unsupported","reason":reason}),
        };
        result.insert(name.into(), value);
    }
    for (name, path) in [
        ("libc_c_void", &["libc", "c_void"][..]),
        ("libc_c_char", &["libc", "c_char"][..]),
        ("libc_sockaddr", &["libc", "sockaddr"][..]),
        ("libc_timespec", &["libc", "timespec"][..]),
        ("libc_socklen_t", &["libc", "socklen_t"][..]),
        ("libc_iovec", &["libc", "iovec"][..]),
    ] {
        let ty = named_type(tcx, path);
        let value = match &ty {
            Ok(ty) => compiler_fact(type_json(context, tcx, *ty)),
            Err(reason) => json!({"status":"unsupported","reason":reason}),
        };
        result.insert(name.into(), value);
        let value = match ty {
            Ok(ty) => compiler_fact(type_json(context, tcx, ty::Ty::new_mut_ptr(tcx, ty))),
            Err(reason) => json!({"status":"unsupported","reason":reason}),
        };
        result.insert(format!("{name}_pointer"), value);
    }
    // linux_like/sync.rs shim_varargs![*u32,...] constructs the primitive
    // pointee directly, independently of libc aliases or target widths.
    result.insert(
        "u32_pointer".into(),
        compiler_fact(type_json(
            context,
            tcx,
            ty::Ty::new_mut_ptr(tcx, tcx.types.u32),
        )),
    );
    result.insert(
        "i32_pointer".into(),
        compiler_fact(type_json(
            context,
            tcx,
            ty::Ty::new_mut_ptr(tcx, tcx.types.i32),
        )),
    );
    Value::Object(result)
}
