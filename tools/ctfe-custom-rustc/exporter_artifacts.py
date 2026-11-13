"""Verify the ordinary-target probe and derive its exact host-builder artifacts."""
import hashlib,json
from pathlib import Path
PIN='8144389c895da997dbdecaa635e41d6a50be6ffd'
NAMES='rustc_abi rustc_ast rustc_attr_ir rustc_codegen_ssa rustc_const_eval rustc_driver rustc_hir rustc_index rustc_interface rustc_middle rustc_session rustc_span rustc_structures rustc_symbol_mangling rustc_target'.split()
def sha(path):
    with Path(path).open('rb') as stream:return hashlib.file_digest(stream,'sha256').hexdigest()
def verified_config(root,attempt):
    root=Path(root).resolve();logs=root/'logs';probe_path=logs/f'attempt{attempt}-host-accessor-std-manifest.json'
    probe=json.loads(probe_path.read_text());prepared=json.loads((root/'prepared.json').read_text())
    assert prepared['pin']==PIN
    assert probe['attempt']==attempt and probe['result']=='PASS' and probe['compile_exit']==0 and probe['run_exit']==0 and probe['ldd_newdriver_verified'] is True
    assert probe['matching_target_std_hashes'] and probe['target_sysroot']
    result_path=logs/(('' if attempt==1 else f'attempt{attempt}-')+'stage1-result.json')
    result=json.loads(result_path.read_text());assert sha(result_path)==probe['build_result_sha256']
    assert result['exit_code']==0 and result['stop_reason'] is None and result['source_audit_valid'] is True
    protected=root/'protected-source.json';assert sha(protected)==probe['protected_manifest_sha256']==result['protected_source_manifest_sha256']
    for relative,entry in json.loads(protected.read_text()).items():
        source=root/'source'/relative;assert sha(source)==entry['sha256'] and entry['marker'] in source.read_text()
    pins=dict(probe['hashes']);pins.update(probe['matching_target_std_hashes'])
    for path,digest in pins.items():assert sha(path)==digest,('probe artifact changed',path)
    command=probe['compile_command'];rustc=Path(command[0]);sysroot=Path(command[command.index('--sysroot')+1]);deps=sysroot/'lib/rustlib/x86_64-unknown-linux-gnu/lib';base=sysroot.parent
    assert str(rustc) in pins
    def fresh(pattern,candidates):
        hashes={sha(p) for p in (base/'stage1-rustc').rglob(pattern)};assert hashes,pattern
        matches=[p for p in candidates if sha(p) in hashes];assert len(matches)==1,(pattern,matches)
        path=matches[0];pins[str(path)]=sha(path);return path
    metadata={name:fresh('lib'+name+'-*.rmeta',list(deps.glob('lib'+name+'-*.rmeta'))) for name in NAMES}
    drivers=[Path(p) for p in probe['hashes'] if Path(p).name.startswith('librustc_driver-') and p.endswith('.so')];assert len(drivers)==1
    driver=drivers[0];assert driver==fresh('librustc_driver-*.so',[driver])
    stds=[Path(p) for p in probe['hashes'] if Path(p).name.startswith('libstd-') and p.endswith('.rmeta')];assert len(stds)==1
    std=stds[0];std_so=std.with_suffix('.so');assert str(std_so) in pins and sha(deps/std.name)==sha(std)
    externs=['--extern','std='+str(std),'--extern','std='+str(std_so),'--extern','rustc_driver='+str(driver)]
    for name,path in metadata.items():externs+=['--extern',name+'='+str(path)]
    environment=dict(probe['environment']);environment.update(LEAN_MIRI_INITIAL_SNAPSHOT_DRIVER=str(driver),LEAN_MIRI_INITIAL_SNAPSHOT_DRIVER_SHA256=sha(driver))
    return {'rustc':str(rustc),'sysroot':str(sysroot),'dependency':str(deps),'externs':externs,'environment':environment,'target_sysroot':probe['target_sysroot'],'artifact_hashes':pins,'probe_manifest':str(probe_path),'probe_manifest_sha256':sha(probe_path)}
def verify_config(config):
    assert sha(config['probe_manifest'])==config['probe_manifest_sha256']
    for path,digest in config['artifact_hashes'].items():assert sha(path)==digest,('artifact changed',path)
