#!/usr/bin/env python3
"""Prepare a separate pinned, vendored source tree. Never deletes existing data."""
import argparse,hashlib,json,os,shutil,subprocess,tarfile
from pathlib import Path
from urllib.request import urlopen
PIN='8144389c895da997dbdecaa635e41d6a50be6ffd'
BASE='https://ci-artifacts.rust-lang.org/rustc-builds/'+PIN+'/'
SOURCE_SHA='031f2e59d92cf9fd460a3238fdcac597fa0b25db570e8244605933a7b67235ca'
LLVM_SHA='d7cea0aff2334d77c2a75c9cfff81a78c8d9c66e8022a2d252441332048a9ae5'
class Reader:
 def __init__(self,response):self.response=response;self.sha=hashlib.sha256();self.count=0
 def read(self,n=-1):
  data=self.response.read(n);self.sha.update(data);self.count+=len(data);return data
 def close(self):pass
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,required=True);parser.add_argument('--repository',type=Path,required=True);parser.add_argument('--toolchain-root',type=Path,required=True);args=parser.parse_args()
root=args.root.resolve();repo=args.repository.resolve();source=root/'source';build=root/'build';pin=args.toolchain_root.resolve();assert (pin/'bin/rustc').is_file()
version_env=dict(os.environ,LD_LIBRARY_PATH=str(pin/'lib'))
version=subprocess.run([str(pin/'bin/rustc'),'-vV'],env=version_env,text=True,capture_output=True)
assert version.returncode==0 and 'commit-hash: '+PIN in version.stdout,'Original builder is not the exact pinned compiler'

if root.exists():raise SystemExit('Refusing existing root; no automatic overwrite or cleanup')
root.mkdir();source.mkdir();(root/'logs').mkdir();(root/'tmp').mkdir()
if shutil.disk_usage(root).free < 4_800_000_000:raise SystemExit('Need >=4.8GB free for source/vendor/LLVM preparation plus reserve; no cleanup attempted')
links=[]
with urlopen(BASE+'rustc-nightly-src.tar.xz',timeout=45) as response:
 reader=Reader(response)
 with tarfile.open(fileobj=reader,mode='r|xz') as archive:
  for member in archive:
   archive.members.clear()
   parts=Path(member.name).parts[1:]
   if not parts or parts[:2]==('src','llvm-project'):continue
   relative=Path(*parts)
   if relative.is_absolute() or '..' in relative.parts:raise RuntimeError('unsafe archive path')
   target=source/relative
   if member.isdir():target.mkdir(parents=True,exist_ok=True)
   elif member.isfile():
    target.parent.mkdir(parents=True,exist_ok=True)
    with archive.extractfile(member) as incoming,target.open('xb') as outgoing:shutil.copyfileobj(incoming,outgoing)
    target.chmod(0o755 if member.mode&0o111 else 0o644)
   elif member.issym() or member.islnk():links.append((relative,member.linkname,member.issym()))
   else:raise RuntimeError('unsupported archive member '+member.name)
 while reader.read(1024*1024):pass
 assert reader.sha.hexdigest()==SOURCE_SHA,'source checksum mismatch; preserve partial root, do not execute'
for relative,link,is_symbol in links:
 target=source/relative;target.parent.mkdir(parents=True,exist_ok=True)
 if is_symbol:
  (target.parent/link).resolve().relative_to(source);target.symlink_to(link)
 else:
  link_parts=Path(link).parts[1:];linked=source/Path(*link_parts);linked.resolve().relative_to(source);os.link(linked,target)
(source/'src/llvm-project').mkdir(parents=True,exist_ok=True)
llvm=build/'cache'/('llvm-x86_64-unknown-linux-gnu-'+PIN+'-false')/'rust-dev-nightly-x86_64-unknown-linux-gnu.tar.xz';llvm.parent.mkdir(parents=True)
with urlopen(BASE+llvm.name,timeout=45) as response,llvm.open('xb') as output:
 reader=Reader(response)
 while data:=reader.read(1024*1024):output.write(data)
 assert reader.sha.hexdigest()==LLVM_SHA,'LLVM checksum mismatch; preserve partial root'
# Unpack the measured component and builder-config, without fabricating a bootstrap stamp.
# Bootstrap may verify/re-unpack this exact cached archive itself.
ci=build/'x86_64-unknown-linux-gnu/ci-llvm';ci.mkdir(parents=True)
with tarfile.open(llvm,mode='r:xz') as archive:
 for member in archive:
  parts=Path(member.name).parts[1:]
  if not parts:continue
  if parts[0]=='rust-dev':parts=parts[1:]
  elif parts!=('builder-config',):continue
  if not parts:continue
  relative=Path(*parts);target=ci/relative
  if '..' in relative.parts or relative.is_absolute():raise RuntimeError('unsafe LLVM archive path')
  if member.isdir():target.mkdir(parents=True,exist_ok=True)
  elif member.isfile():
   target.parent.mkdir(parents=True,exist_ok=True)
   with archive.extractfile(member) as incoming,target.open('xb') as outgoing:shutil.copyfileobj(incoming,outgoing)
   target.chmod(0o755 if member.mode&0o111 else 0o644)
  elif member.issym():
   (target.parent/member.linkname).resolve().relative_to(ci);target.symlink_to(member.linkname)
  else:raise RuntimeError('unsupported LLVM archive member')
# Optimized compiler-builtins uses compiler-rt sources even with downloaded LLVM.
# Reuse the exact verified CI component; do not disable the normal builtins path.
compiler_rt=ci/'compiler-rt'
assert (compiler_rt/'lib/builtins/absvdi2.c').is_file(),'Verified LLVM artifact lacks compiler-rt source'
(source/'src/llvm-project/compiler-rt').symlink_to(compiler_rt,target_is_directory=True)
patch_root=Path(__file__).resolve().parent/'patches'
patches=[patch_root/name for name in ['preserve-instrumented-source.patch','complete-allocation-snapshot.patch','root-observation.patch','allocation-key-representation.patch']]
for patch in patches:
 subprocess.run(['patch','--dry-run','-p1','-i',str(patch)],cwd=source,check=True)
 subprocess.run(['patch','-p1','-i',str(patch)],cwd=source,check=True)
assert 'pub fn lean_miri_complete_allocation_identity_snapshot' in (source/'compiler/rustc_middle/src/mir/interpret/mod.rs').read_text()
assert 'LEAN_MIRI_OBSERVE_CTFE_ROOT' in (source/'compiler/rustc_const_eval/src/const_eval/eval_queries.rs').read_text()
protected={}
for relative,marker in [('src/bootstrap/src/core/build_steps/compile.rs','!relative.starts_with("rustlib/rustc-src")'),('compiler/rustc_middle/src/mir/interpret/mod.rs','pub fn lean_miri_complete_allocation_identity_snapshot'),('compiler/rustc_const_eval/src/const_eval/eval_queries.rs','LEAN_MIRI_OBSERVE_CTFE_ROOT'),('compiler/rustc_middle/src/mir/interpret/allocation/init_mask.rs','pub fn lean_miri_complete_init_mask_snapshot'),('compiler/rustc_middle/src/mir/interpret/allocation/provenance_map.rs','pub fn lean_miri_complete_provenance_snapshot')]:
 path=source/relative;assert marker in path.read_text();protected[relative]={'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'marker':marker}
(root/'protected-source.json').write_text(json.dumps(protected,indent=2)+'\n')
linkers=root/'linker-bin';linkers.mkdir();(linkers/'ld.lld').symlink_to(pin/'lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld')
linker=root/'linker-single-thread.sh';linker.write_text('#!/bin/sh\nexec /usr/bin/cc -B'+str(linkers)+' -fuse-ld=lld -Wl,--threads=1 "$@"\n');linker.chmod(0o755)
config=f'''profile = "compiler"
[build]
build-dir = "{build}"
rustc = "{pin}/bin/rustc"
cargo = "{pin}/bin/cargo"
rustdoc = "{pin}/bin/rustdoc"
host = ["x86_64-unknown-linux-gnu"]
target = ["x86_64-unknown-linux-gnu"]
jobs = 1
vendor = true
locked-deps = true
docs = false
extended = false
[llvm]
download-ci-llvm = true
assertions = false
[rust]
download-rustc = false
channel = "nightly"
debug = false
debuginfo-level = 0
incremental = false
lto = "off"
codegen-units = 1
codegen-units-std = 1
lld = false
[target.x86_64-unknown-linux-gnu]
linker = "{linker}"
'''
(root/'bootstrap.toml').write_text(config)
manifest={'pin':PIN,'toolchain_root':str(pin),'original_builder_sha256':hashlib.sha256((pin/'bin/rustc').read_bytes()).hexdigest(),'original_builder_version':version.stdout,'source_sha256':SOURCE_SHA,'llvm_sha256':LLVM_SHA,'patches':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in patches},'free_after_preparation':shutil.disk_usage(root).free,'source_archive_retained':False,'cargo_route':'full pinned vendor, offline; no crates.io required','stage2_fallback':'not automatic'}
(root/'prepared.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(manifest,indent=2))
