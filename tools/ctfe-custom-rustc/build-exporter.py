#!/usr/bin/env python3
"""Build the snapshot exporter with the verified probe's exact stage0 host route."""
import argparse,json,os,subprocess,shutil,fcntl
from pathlib import Path
from exporter_artifacts import verified_config,verify_config,sha
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--root',type=Path,required=True);p.add_argument('--attempt',type=int,required=True)
p.add_argument('--target-dir',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
p.add_argument('--prepare-only',action='store_true',help='Verify pins and record command without running Cargo')
p.add_argument('--minimum-free-bytes',type=int,default=512*1024*1024)
a=p.parse_args();repo=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
config=verified_config(a.root,a.attempt);out=a.out.resolve();assert not out.exists(),'Refusing existing evidence';out.mkdir(parents=True)
config_path=out/'host-config.json';config_path.write_text(json.dumps(config,indent=2)+'\n')
target=a.target_dir.resolve();target.parent.mkdir(parents=True,exist_ok=True)
lease=(target.parent/(target.name+'.build.lock')).open('a');fcntl.flock(lease,fcntl.LOCK_EX|fcntl.LOCK_NB)
assert not target.exists() or not any(target.iterdir()),'Use an empty exclusive target directory'
source_files=sorted((repo/'exporter/src').rglob('*.rs'))+[repo/'exporter/Cargo.toml',repo/'exporter/Cargo.lock',repo/'exporter/build.rs',Path(__file__).resolve(),here/'exporter-host-wrapper.py',here/'exporter_artifacts.py']
before={str(f.relative_to(repo)):sha(f) for f in source_files}
env=dict(os.environ);env.update(config['environment']);env.update(RUSTC=str(here/'exporter-host-wrapper.py'),LEAN_MIRI_EXPORTER_HOST_CONFIG=str(config_path),CARGO_TARGET_DIR=str(target),CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_TEST_DEBUG='0',CARGO_INCREMENTAL='0',CARGO_BUILD_JOBS='1')
assert not env.get('RUSTFLAGS') and not env.get('CARGO_ENCODED_RUSTFLAGS'),'Unreviewed compiler flags are forbidden'
cargo=Path(config['rustc']).with_name('cargo');command=[str(cargo),'build','--locked','--offline','--manifest-path',str(repo/'exporter/Cargo.toml'),'--features','ctfe-initial-global-snapshot','--bin','lean-miri-mir-exporter']
record={'argv':command,'cwd':str(repo),'host_config':str(config_path),'host_config_sha256':sha(config_path),'before':before,'artifact_hashes':config['artifact_hashes'],'prepare_only':a.prepare_only,'wrapper_sha256':sha(here/'exporter-host-wrapper.py')}
(out/'command.json').write_text(json.dumps(record,indent=2)+'\n')
if a.prepare_only:print(out/'command.json');raise SystemExit(0)
target.parent.mkdir(parents=True,exist_ok=True);assert shutil.disk_usage(target.parent).free>=a.minimum_free_bytes,'Insufficient build budget'
with (out/'build.log').open('x') as log:result=subprocess.run(command,cwd=repo,env=env,stdout=log,stderr=subprocess.STDOUT)
after={str(f.relative_to(repo)):sha(f) for f in source_files};verify_config(config)
manifest={**record,'after':after,'build_exit':result.returncode,'source_same':before==after,'environment':config['environment'],'target_sysroot':config['target_sysroot']}
if result.returncode==0:
    binary=target/'debug/lean-miri-mir-exporter';manifest.update(binary=str(binary),binary_sha256=sha(binary))
    linked=subprocess.run(['ldd',str(binary)],env=env,text=True,capture_output=True)
    (out/'ldd.log').write_text(linked.stdout+linked.stderr)
    manifest['ldd_newdriver_verified']=linked.returncode==0 and config['environment']['LEAN_MIRI_INITIAL_SNAPSHOT_DRIVER'] in linked.stdout
(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');assert before==after,'Source changed during build'
assert result.returncode==0,'Exporter build failed; retained build.log'
assert manifest['ldd_newdriver_verified'],'Exporter does not load the verified new driver; retained ldd.log'
print(out/'manifest.json')
