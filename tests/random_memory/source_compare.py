#!/usr/bin/env python3
"""Exact helpers.rs gen_random body with fixture RNG/write leaves.
Compares outer ordering/error retention, not physical host RNG/memory equivalence.
"""
from pathlib import Path
import hashlib,json,os,subprocess,tempfile
ROOT=Path(__file__).resolve().parents[2]
def main():
 source=ROOT/'upstream/miri-source/src/helpers.rs'
 lock=json.loads((ROOT/'upstream/source-lock.json').read_text())
 locked=next(x for x in lock['files'] if x['path']=='upstream/miri-source/src/helpers.rs')
 assert hashlib.sha256(source.read_bytes()).hexdigest()==locked['sha256'],'pinned helpers.rs hash mismatch'
 print('source_sha256='+locked['sha256'])
 text=source.read_text(); start=text.index('    fn gen_random('); begin=text.index('{',start);depth=1;end=begin+1
 while depth:
  depth+=(text[end]=='{')-(text[end]=='}');end+=1
 body=text[begin:end]
 fixture=r'''
use std::cell::RefCell;
thread_local!{static EVENTS:RefCell<Vec<String>>=RefCell::new(vec![]);static HOST_ERROR:RefCell<bool>=RefCell::new(false);}
fn event(s:&str){EVENTS.with(|x|x.borrow_mut().push(s.into()));}
type Pointer=u64;type InterpResult<T>=Result<T,String>;
fn interp_ok<T>(x:T)->InterpResult<T>{Ok(x)}
macro_rules! err_unsup_format {($($x:tt)*)=>{{let _=format!($($x)*);"unsupported".to_string()}}}
mod getrandom {pub fn fill(data:&mut[u8])->Result<(),String>{super::event("host");if super::HOST_ERROR.with(|x|*x.borrow()){return Err("fixture host failure".into())}data.fill(7);Ok(())}}
struct Rng;impl Rng {fn get_mut(&mut self)->&mut Self{self}fn fill_bytes(&mut self,data:&mut[u8]){event("isolated");data.fill(7);}}
struct Machine{host:bool,rng:Rng}impl Machine{fn communicate(&self)->bool{self.host}}
struct Cx{machine:Machine,write_error:bool}impl Cx{
 fn eval_context_mut(&mut self)->&mut Self{self}
 fn write_bytes_ptr(&mut self,_:Pointer,data:impl Iterator<Item=u8>)->InterpResult<()>{let n=data.count();event(&format!("write{n}"));if self.write_error{Err("ub".into())}else{Ok(())}}
 fn gen_random(&mut self,ptr:Pointer,len:u64)->InterpResult<()>
'''+body+r'''
}
fn main(){for (host,host_error,write_error,n) in [(false,false,false,0),(true,true,true,0),(false,false,false,3),(true,false,false,3),(true,true,false,3),(false,false,true,3)]{
 EVENTS.with(|x|x.borrow_mut().clear());HOST_ERROR.with(|x|*x.borrow_mut()=host_error);
 let mut cx=Cx{machine:Machine{host,rng:Rng},write_error};let result=cx.gen_random(0,n);let kind=match result{Ok(())=>"ok".into(),Err(e)=>e};let events=EVENTS.with(|x|x.borrow().join(","));println!("{n}|{host}|{host_error}|{write_error}|{kind}|{events}");}}
'''
 with tempfile.TemporaryDirectory() as tmp:
  p=Path(tmp);(p/'fixture.rs').write_text(fixture)
  rustc=ROOT/'.rustup/toolchains/miri-exporter-8144389c895d/bin/rustc'
  subprocess.run([str(rustc),'--edition=2021',str(p/'fixture.rs'),'-o',str(p/'fixture')],check=True)
  expected=subprocess.check_output([str(p/'fixture')],text=True).splitlines()
  env={**os.environ,'ELAN_HOME':str(ROOT/'.elan')}
  actual=subprocess.check_output([str(ROOT/'.elan/bin/lake'),'env','lean','--run','tests/random_memory/Random.lean'],cwd=ROOT,env=env,text=True).splitlines()
  assert actual==expected,(expected,actual)
  print('6 exact pinned gen_random outer-body traces agree; host/RNG/write leaf effects are fixture boundaries')
if __name__=='__main__':main()
