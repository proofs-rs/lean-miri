"""Pinned scheduler method bodies with fixture dependencies, plus Lean counterparts."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[2]
PATH='upstream/miri-source/src/concurrency/scheduler.rs'

def extract(text,name):
    start=text.index('    fn '+name+'(')
    opening=text.index('{',start)
    depth,end=1,opening+1
    while depth:
        depth+=(text[end]=='{')-(text[end]=='}')
        end+=1
    return text[start:end].replace("InterpResult<'tcx, Poll<()>>",'Result<Poll<()>, String>').replace("InterpResult<'tcx, !>",'Result<(), String>').replace("InterpResult<'tcx>",'Result<(), String>')

class SourceRunLoop(unittest.TestCase):
    def test_actual_method_bodies(self):
        locked=next(f for f in json.loads((ROOT/'upstream/source-lock.json').read_text())['files'] if f['path']==PATH)
        self.assertEqual(hashlib.sha256((ROOT/PATH).read_bytes()).hexdigest(),locked['sha256'])
        source=(ROOT/PATH).read_text()
        methods='\n'.join(extract(source,n) for n in ['run_on_stack_empty','step_current_thread'])
        iteration=extract(source,'run_threads').replace('fn run_threads(', 'fn iteration(').replace('loop {','{',1)
        iteration=iteration[:-1]+'interp_ok(())\n    }'
        harness=r'''
use std::task::Poll;
use std::sync::atomic::{AtomicBool,Ordering};
use std::rc::Rc;
use std::cell::RefCell;
static CTRL_C_RECEIVED:AtomicBool=AtomicBool::new(false);
const DUMMY_SP:u8=0;
macro_rules! throw_machine_stop {($($t:tt)*)=>{return Err("interrupted".into())}}
fn interp_ok<T>(v:T)->Result<T,String>{Ok(v)}
#[derive(Clone,Copy)] enum SchedulingAction {ExecuteStep,SleepAndWaitForIo(Option<u64>)}
struct Clock{events:Rc<RefCell<Vec<u8>>>}
impl Clock{fn sleep(&mut self,_:u64){self.events.borrow_mut().push(9)}}
struct Machine{events:Rc<RefCell<Vec<u8>>>,communicate:bool,monotonic_clock:Clock}
impl Machine{fn communicate(&self)->bool{self.communicate} fn handle_abnormal_termination(&mut self){self.events.borrow_mut().push(7)}}
type Callback=fn(&mut Cx)->Result<Poll<()>,String>;
struct Thread{origin_span:u8,on_stack_empty:Option<Callback>}
struct Cx{thread:Thread,machine:Machine,core:Result<bool,String>,poll:Result<Poll<()>,String>,action:SchedulingAction}
fn callback(cx:&mut Cx)->Result<Poll<()>,String>{assert!(cx.thread.on_stack_empty.is_none());cx.machine.events.borrow_mut().push(3);cx.poll.clone()}
impl Cx{
fn eval_context_mut(&mut self)->&mut Self{self}
fn active_thread_mut(&mut self)->&mut Thread{&mut self.thread}
fn step(&mut self)->Result<bool,String>{self.machine.events.borrow_mut().push(1);self.core.clone()}
fn terminate_active_thread(&mut self,for_exit:bool)->Result<(),String>{assert!(!for_exit);self.machine.events.borrow_mut().push(5);Ok(())}
fn schedule(&mut self)->Result<SchedulingAction,String>{self.machine.events.borrow_mut().push(6);Ok(self.action)}
fn poll_and_unblock(&mut self,_:Option<u64>)->Result<(),String>{self.machine.events.borrow_mut().push(8);Ok(())}
METHODS
ITERATION
}
fn state(core:Result<bool,String>,poll:Result<Poll<()>,String>,communicate:bool,action:SchedulingAction)->Cx{
 let events=Rc::new(RefCell::new(vec![]));
 Cx{thread:Thread{origin_span:9,on_stack_empty:Some(callback)},machine:Machine{events:events.clone(),communicate,monotonic_clock:Clock{events}},core,poll,action}
}
fn output(cx:&Cx,r:Result<(),String>){println!("{:?}|{:?}|{}|{}",r,cx.machine.events.borrow(),cx.thread.on_stack_empty.is_some(),cx.thread.origin_span)}
fn main(){
 for (core,poll) in [(Ok(false),Ok(Poll::Pending)),(Ok(false),Ok(Poll::Ready(()))),(Ok(true),Ok(Poll::Pending)),(Err("core".into()),Ok(Poll::Pending)),(Ok(false),Err("callback".into()))]{
 let mut cx=state(core,poll,false,SchedulingAction::ExecuteStep);let r=cx.step_current_thread();output(&cx,r);
 }
 for (interrupt,comm,action) in [(true,false,SchedulingAction::ExecuteStep),(false,true,SchedulingAction::SleepAndWaitForIo(None)),(false,false,SchedulingAction::SleepAndWaitForIo(Some(10)))]{
 CTRL_C_RECEIVED.store(interrupt,Ordering::Relaxed);
 let mut cx=state(Ok(false),Ok(Poll::Pending),comm,action);let r=cx.iteration();output(&cx,r);
 }
}
'''.replace('METHODS',methods).replace('ITERATION',iteration)
        with tempfile.TemporaryDirectory() as tmp:
            src,exe=Path(tmp)/'scheduler.rs',Path(tmp)/'scheduler'
            src.write_text(harness)
            result=subprocess.run([str(ROOT/'.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc'),'--edition=2021',str(src),'-o',str(exe)],capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stderr)
            actual=subprocess.check_output([str(exe)],text=True).splitlines()
        self.assertEqual(actual,[
            'Ok(())|[1, 3]|true|0','Ok(())|[1, 3, 5]|true|0','Ok(())|[1]|true|9',
            'Err("core")|[1]|true|9','Err("callback")|[1, 3]|false|0',
            'Err("interrupted")|[7]|true|9','Ok(())|[6, 8]|true|9','Ok(())|[6, 9]|true|9'])
        subprocess.run(['.elan/bin/lake','env','lean','MiriTests/RunLoop/Callbacks.lean'],cwd=ROOT,
            env={**os.environ,'ELAN_HOME':str(ROOT/'.elan')},check=True)
if __name__=='__main__':unittest.main()
