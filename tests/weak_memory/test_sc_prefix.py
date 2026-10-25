"""SHA-locked actual buffered_atomic_read outer body vs Lean preparation.
The buffered_read leaf deliberately stops at its boundary: selection/fetch,
validation internals and full atomic-machine equivalence are separate tests.
"""
from pathlib import Path
import hashlib,json,os,subprocess,tempfile
ROOT=Path(__file__).resolve().parents[2]
path='upstream/miri-source/src/concurrency/weak_memory.rs'
entry=next(e for e in json.loads((ROOT/'upstream/source-lock.json').read_text())['files'] if e['path']==path)
source=(ROOT/path).read_text();assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==entry['sha256']
a=source.index('    fn buffered_atomic_read(');o=source.index('{',a);depth=1;b=o+1
while depth:
 depth+=(source[b]=='{')-(source[b]=='}');b+=1
method=source[a:b]
template=r'''
use std::cell::{Cell,RefCell};
type VClock=u32;type Scalar=u32;type InterpResult<'a,T=()>=Result<T,&'static str>;
fn interp_ok<T>(v:T)->Result<T,&'static str>{Ok(v)}
#[derive(Clone,Copy,PartialEq)]enum AtomicReadOrd{Relaxed,SeqCst}
#[derive(PartialEq)]enum LoadRecency{Latest,Outdated}
struct Threads;struct Layout{size:u64}struct MPlaceTy<'a>{layout:Layout,life:std::marker::PhantomData<&'a()>}
impl MPlaceTy<'_>{fn ptr(&self)->u64{0}}
struct Global{read:Cell<u32>,track_outdated_loads:bool}
impl Global{fn race_detecting(&self)->bool{true}fn sc_read(&self,_:&Threads){self.read.set(5)}}
struct Race{global:Global}impl Race{fn as_vclocks_ref(&self)->Option<&Global>{Some(&self.global)}}
struct AllocRace{payload:Option<Buffers>}impl AllocRace{fn as_weak_memory_ref(&self)->Option<&Buffers>{self.payload.as_ref()}}
struct Extra{data_race:AllocRace}struct Buffers{present:bool}struct Buffer;
impl Buffers{fn get_store_buffer(&self,_:(u64,u64))->InterpResult<'_,Option<Buffer>>{Ok(self.present.then_some(Buffer))}}
impl Buffer{fn buffered_read(&self,_:&Global,_:&Threads,_:bool,_:&mut (),_:impl FnOnce(Option<&VClock>)->InterpResult<'_>)->InterpResult<'_,(Option<Scalar>,LoadRecency)>{Err("selection boundary")}}
struct Machine{data_race:Race,threads:Threads,rng:RefCell<()>}
struct Cx{machine:Machine,extra:Extra}
enum NonHaltingDiagnostic{WeakMemoryOutdatedLoad{ptr:u64}}
fn alloc_range(a:u64,b:u64)->(u64,u64){(a,b)}
impl<'tcx> Cx{
fn eval_context_ref(&self)->&Self{self}
fn ptr_get_alloc_id(&self,_:u64,_:u64)->InterpResult<'tcx,(u64,u64)>{Ok((0,0))}
fn get_alloc_extra(&self,_:u64)->InterpResult<'tcx,&Extra>{Ok(&self.extra)}
fn emit_diagnostic(&self,_:NonHaltingDiagnostic){}
METHOD
}
fn main(){for payload in 0..3{for sc in [false,true]{
 let cx=Cx{machine:Machine{data_race:Race{global:Global{read:Cell::new(0),track_outdated_loads:false}},threads:Threads,rng:RefCell::new(())},extra:Extra{data_race:AllocRace{payload:if payload==0{None}else{Some(Buffers{present:payload==2})}}}};
 let result=cx.buffered_atomic_read(&MPlaceTy{layout:Layout{size:4},life:std::marker::PhantomData},if sc{AtomicReadOrd::SeqCst}else{AtomicReadOrd::Relaxed},42,|clock|{assert!(clock.is_none());Ok(())});
 let label=match result{Ok(Some(42))=>"ready",Err("selection boundary")=>"select",_=>panic!("unexpected result")};
 println!("{}|{}|{}|{}",payload,sc,cx.machine.data_race.global.read.get(),label);
}}}
'''.replace('METHOD',method)
env={**os.environ,'ELAN_HOME':str(ROOT/'.elan')}
with tempfile.TemporaryDirectory(prefix='atomic-sc-prefix-') as tmp:
 p=Path(tmp);(p/'main.rs').write_text(template)
 subprocess.run([str(ROOT/'.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc'),'--edition=2024','-Awarnings',str(p/'main.rs'),'-o',str(p/'oracle')],check=True)
 expected=subprocess.check_output([str(p/'oracle')],text=True).splitlines()
lean=subprocess.run([str(ROOT/'.elan/bin/lake'),'env','lean','--run','tests/weak_memory/ScPrefix.lean'],cwd=ROOT,env=env,text=True,capture_output=True)
assert lean.returncode==0,lean.stdout+lean.stderr
actual=lean.stdout.splitlines()
assert actual==expected,(actual,expected)
assert actual==['0|false|0|ready','0|true|0|ready','1|false|0|ready','1|true|5|ready','2|false|0|select','2|true|5|select']
print('6 SHA-locked source outer SC payload/prefix cases agree; buffered selection leaf is an explicit boundary cut')
