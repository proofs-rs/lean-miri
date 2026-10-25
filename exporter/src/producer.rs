//! Input identity for compiler-produced MIR. Hashes identify actual consumed
//! artifacts; a directory spelling or target triple never certifies a Miri
//! sysroot. Consumers must compare against their pinned reference manifest.
use std::fs;
use std::io::Write;
use std::path::Path;
use std::process::{Command,Stdio};
use rustc_middle::ty::TyCtxt;
use serde_json::{Value,json};

pub const MIRI_DEFAULT_ARGS: &[&str]=&[
    "--cfg=miri","-Zalways-encode-mir","-Zextra-const-ub-checks","-Zmir-preserve-ub",
    "-Zmir-opt-level=0","-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums",
    "-Zmir-enable-passes=-ReferencePropagation,-GVN","-Zdeduplicate-diagnostics=no",
];
fn digest_output(output:std::process::Output)->Result<String,String>{
    if !output.status.success(){return Err(format!("sha256sum failed: {}",String::from_utf8_lossy(&output.stderr)));}
    let output=String::from_utf8(output.stdout).map_err(|e|e.to_string())?;
    let digest=output.split_whitespace().next().ok_or("sha256sum returned no digest")?;
    if digest.len()!=64 || !digest.bytes().all(|b|b.is_ascii_hexdigit()){return Err("invalid sha256sum output".into());}
    Ok(digest.to_ascii_lowercase())
}
fn hash_file(path:&Path)->Result<(String,u64),String>{
    let file=fs::File::open(path).map_err(|e|e.to_string())?;
    let before=file.metadata().map_err(|e|e.to_string())?;
    let after_file=file.try_clone().map_err(|e|e.to_string())?;
    let output=Command::new("sha256sum").stdin(Stdio::from(file)).output().map_err(|e|e.to_string())?;
    let digest=digest_output(output)?;
    let after=after_file.metadata().map_err(|e|e.to_string())?;
    if before.len()!=after.len() || before.modified().ok()!=after.modified().ok(){return Err("artifact changed while hashing".into());}
    Ok((digest,after.len()))
}
fn hash_bytes(bytes:&[u8])->Result<String,String>{
    let mut child=Command::new("sha256sum").stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().map_err(|e|e.to_string())?;
    child.stdin.take().ok_or("sha256sum stdin missing")?.write_all(bytes).map_err(|e|e.to_string())?;
    digest_output(child.wait_with_output().map_err(|e|e.to_string())?)
}
fn artifact(path:&Path,crate_name:&str,kind:&str,sysroot:&Path)->Value{
    let result=(||{
        let canonical=fs::canonicalize(path).map_err(|e|e.to_string())?;
        let text=canonical.to_str().ok_or("artifact path is not UTF-8")?;
        let (hash,size)=hash_file(&canonical)?;
        Ok::<_,String>(json!({"status":"supported","path":text,"sha256":hash,"size_bytes":size,
            "crate_name":crate_name,"kind":kind,"within_sysroot":canonical.starts_with(sysroot),
            "sysroot_relative_path":canonical.strip_prefix(sysroot).ok().and_then(|path|path.to_str())}))
    })();
    match result{Ok(value)=>value,Err(error)=>json!({"status":"unsupported","path":path.to_string_lossy(),"crate_name":crate_name,"kind":kind,"reason":error})}
}
pub fn evidence(tcx:TyCtxt<'_>,invocation:Option<&Value>)->Value{
    let sysroot=tcx.sess.opts.sysroot.path();
    let canonical=fs::canonicalize(sysroot);
    let mut artifacts=Vec::new();
    let root=canonical.as_deref().unwrap_or(sysroot);
    for &number in tcx.crates(()) {
        let source=tcx.used_crate_source(number);
        let name=tcx.crate_name(number).to_string();
        for (kind,path) in [("rlib",&source.rlib),("rmeta",&source.rmeta),("dylib",&source.dylib),("sdylib_interface",&source.sdylib_interface)]{
            if let Some(path)=path{artifacts.push(artifact(path,&name,kind,root));}
        }
    }
    artifacts.sort_by(|a,b|a["path"].as_str().cmp(&b["path"].as_str()).then(a["kind"].as_str().cmp(&b["kind"].as_str())));
    let all_supported=canonical.is_ok() && artifacts.iter().all(|v|v["status"]=="supported");
    let key=|v:&Value|json!({"crate_name":v["crate_name"],"kind":v["kind"],"sha256":v["sha256"],"size_bytes":v["size_bytes"]});
    let sysroot_entries=artifacts.iter().filter(|v|v["within_sysroot"]==true).map(|v|{
        let mut entry=key(v); entry["relative_path"]=v["sysroot_relative_path"].clone(); entry
    }).collect::<Vec<_>>();
    let mut loaded_entries=artifacts.iter().map(key).collect::<Vec<_>>();
    loaded_entries.sort_by_key(Value::to_string);
    let manifest=if all_supported{hash_bytes(json!(sysroot_entries).to_string().as_bytes())}else{Err("artifact identity evidence is incomplete".into())};
    let loaded_manifest=if all_supported{hash_bytes(json!(loaded_entries).to_string().as_bytes())}else{Err("artifact identity evidence is incomplete".into())};
    let args=invocation.and_then(|v|v.get("rustc_args")).and_then(Value::as_array).cloned();
    let cfg_miri=args.as_ref().map(|args|args.iter().any(|v|v=="--cfg=miri") || args.windows(2).any(|v|v[0]=="--cfg" && v[1]=="miri"));
    let panic=match tcx.sess.panic_strategy(){rustc_target::spec::PanicStrategy::Unwind=>"unwind",rustc_target::spec::PanicStrategy::Abort=>"abort",rustc_target::spec::PanicStrategy::ImmediateAbort=>"immediate-abort"};
    json!({"status":if all_supported && args.is_some() && manifest.is_ok() && loaded_manifest.is_ok(){"supported"}else{"unsupported"},
        "sysroot_path":root.to_string_lossy(),"hash_algorithm":"sha256",
        "sysroot_manifest_sha256":manifest.as_ref().ok(),"loaded_artifacts_manifest_sha256":loaded_manifest.as_ref().ok(),
        "manifest_error":manifest.err(),"loaded_manifest_error":loaded_manifest.err(),"artifacts":artifacts,
        "requested_cfg_miri":cfg_miri,"miri_default_args":MIRI_DEFAULT_ARGS,"rustc_args":args,
        "effective_panic_strategy":panic,"mir_opt_level":tcx.sess.opts.unstable_opts.mir_opt_level,
        "mir_enable_passes":tcx.sess.opts.unstable_opts.mir_enable_passes,
        "mir_preserve_ub":tcx.sess.opts.unstable_opts.mir_preserve_ub,
        "extra_const_ub_checks":tcx.sess.opts.unstable_opts.extra_const_ub_checks,
        "always_encode_mir":tcx.sess.opts.unstable_opts.always_encode_mir,
        "deduplicate_diagnostics":tcx.sess.opts.unstable_opts.deduplicate_diagnostics,
        "qualification":"Hashes identify consumed artifacts; Miri sysroot equivalence requires matching an independently pinned reference manifest."})
}
