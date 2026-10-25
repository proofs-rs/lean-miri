"""Check producer config/artifact records against actual consumed files.
This identifies artifacts; it does not certify Miri sysroot build equivalence.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,tempfile
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'tools'))
from mir_json import load_mir_document
lock=json.loads((ROOT/'upstream/source-lock.json').read_text())
path='upstream/miri-source/src/lib.rs'
entry=next(x for x in lock['files'] if x['path']==path)
assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==entry['sha256']
block=(ROOT/path).read_text().split('pub const MIRI_DEFAULT_ARGS: &[&str] = &[',1)[1].split('];',1)[0]
defaults=re.findall(r'^\s*"([^"]+)"',block,re.M)
env={**os.environ,'RUSTUP_HOME':str(ROOT/'.rustup'),'CARGO_HOME':str(ROOT/'.cargo')}
env['PATH']=str(ROOT/'.rustup/toolchains/miri-exporter-8144389c895d/bin')+':'+env['PATH']
env['LD_LIBRARY_PATH']=str(ROOT/'.rustup/toolchains/miri-exporter-8144389c895d/lib')
canonical=lambda value:json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=False)
with tempfile.TemporaryDirectory() as tmp:
    output=Path(tmp)/'scope.json'
    command=[str(ROOT/'exporter/target/debug/lean-miri-mir-exporter'),'--output',str(output),'--root','add_one','exporter/fixtures/scope/simple.rs','--crate-type=lib','--crate-name=producer_check']
    absent={k:v for k,v in env.items() if k!='MIRI_SYSROOT'}
    rejected=subprocess.run(command,cwd=ROOT,env=absent,text=True,capture_output=True)
    assert rejected.returncode!=0 and 'requires explicit --sysroot or MIRI_SYSROOT' in rejected.stderr
    assert not output.exists()
    env['MIRI_SYSROOT']=str(ROOT/'scratch/miri-sysroot')
    subprocess.run(command,cwd=ROOT,env=env,check=True)
    doc=load_mir_document(output);settings=doc['producer']['input_settings']
    assert settings['status']=='supported'
    assert settings['miri_default_args']==defaults
    assert all(arg in settings['rustc_args'] for arg in defaults)
    assert settings['requested_cfg_miri'] is True
    assert settings['mir_opt_level']==0
    assert settings['mir_preserve_ub'] and settings['extra_const_ub_checks'] and settings['always_encode_mir']
    assert settings['deduplicate_diagnostics'] is False
    assert Path(settings['sysroot_path']).resolve()==(ROOT/'scratch/miri-sysroot').resolve()
    artifacts=settings['artifacts'];assert artifacts
    for artifact in artifacts:
        actual=Path(artifact['path'])
        assert actual.stat().st_size==artifact['size_bytes']
        assert hashlib.sha256(actual.read_bytes()).hexdigest()==artifact['sha256']
    def key(a):return {k:a[k] for k in ['crate_name','kind','sha256','size_bytes']}
    sysroot=[{**key(a),'relative_path':a['sysroot_relative_path']} for a in artifacts if a['within_sysroot']]
    loaded=sorted([key(a) for a in artifacts],key=canonical)
    assert hashlib.sha256(canonical(sysroot).encode()).hexdigest()==settings['sysroot_manifest_sha256']
    assert hashlib.sha256(canonical(loaded).encode()).hexdigest()==settings['loaded_artifacts_manifest_sha256']
    print(f'producer Miri settings and {len(artifacts)} actual consumed artifact hashes/manifests verified; absent sysroot rejected')
