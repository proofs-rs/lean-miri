"""Compile actual pinned helper/return bodies with fixture interpreter operations.
This checks orchestration and callback effects, not full Rust/Miri execution.
"""
from pathlib import Path
import os
import hashlib
import json
import subprocess
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]

def function(path, name):
    locked = next(f for f in json.loads((ROOT/'upstream/source-lock.json').read_text())['files'] if f['path'] == str(path))
    assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == locked['sha256'], f'pinned source mismatch: {path}'
    text = (ROOT/path).read_text()
    start = text.index('    pub', text.index('fn '+name)-20)
    opening = text.index('{', start)
    depth = 1
    end = opening + 1
    while depth:
        depth += (text[end] == '{') - (text[end] == '}')
        end += 1
    return text[start:end].replace("InterpResult<'tcx>", 'Result<(), String>').replace('pub(super)', 'pub')

class SourceTransitions(unittest.TestCase):
    def test_extracted_helpers_and_return(self):
        eval_path = Path('upstream/rustc-source/compiler/rustc_const_eval/src/interpret/eval_context.rs')
        call_path = Path('upstream/rustc-source/compiler/rustc_const_eval/src/interpret/call.rs')
        methods = '\n'.join(function(eval_path,n) for n in ['go_to_block','return_to_block','unwind_to_block'])
        methods += '\n' + function(call_path,'return_from_current_stack_frame')
        harness = r'''
macro_rules! trace { ($($t:tt)*) => {} }
macro_rules! info { ($($t:tt)*) => {} }
macro_rules! throw_ub { ($($t:tt)*) => {return Err("UB".into())} }
macro_rules! throw_ub_format { ($($t:tt)*) => {return Err("UB".into())} }
#[derive(Clone,Copy,Debug,PartialEq)] struct Loc { block: usize, statement_index:usize }
#[derive(Clone,Copy,Debug,PartialEq)] enum Either { Left(Loc), Right(u8) }
use Either::*;
mod mir {
 #[derive(Clone,Copy)] pub struct BasicBlock(pub usize);
 impl BasicBlock { pub fn start_location(self)->super::Loc {super::Loc{block:self.0,statement_index:0}} }
 #[derive(Clone,Copy)] pub enum UnwindAction { Cleanup(BasicBlock),Continue,Unreachable,Terminate(u8) }
 pub const RETURN_PLACE:u8=0;
}
#[derive(Clone,Copy)] enum ReturnContinuation {Goto{ret:Option<mir::BasicBlock>,unwind:mir::UnwindAction},Stop{cleanup:bool}}
#[derive(Clone,Copy)] enum ReturnAction {Normal,NoJump,NoCleanup}
struct Block { is_cleanup:bool }
struct Body { span:u8, basic_blocks:Vec<Block> }
struct Frame {loc:Either,body:Body,cont:ReturnContinuation}
impl Frame {fn return_place(&self){} fn return_cont(&self)->ReturnContinuation{self.cont}}
struct M;
impl M {fn unwind_terminate(cx:&mut Cx,reason:u8)->Result<(),String>{cx.events.push(5);if reason==1{cx.frame_mut().loc=Left(Loc{block:99,statement_index:0});}Ok(())}}
struct Cx {frames:Vec<Frame>,events:Vec<u8>,action:ReturnAction,fail_copy:bool}
fn interp_ok<T>(x:T)->Result<T,String>{Ok(x)}
impl Cx {
fn frame(&self)->&Frame{self.frames.last().unwrap()}
fn frame_mut(&mut self)->&mut Frame{self.frames.last_mut().unwrap()}
fn body(&self)->&Body{&self.frame().body}
fn frame_idx(&self)->usize{self.frames.len()-1}
fn stack(&self)->&Vec<Frame>{&self.frames}
fn local_to_op(&mut self,_:u8,_:Option<()>)->Result<(),String>{self.events.push(1);Ok(())}
fn pop_stack_frame_raw(&mut self)->Result<Frame,String>{self.events.push(2);Ok(self.frames.pop().unwrap())}
fn copy_op_allow_transmute(&mut self,_:&(),_:())->Result<(),String>{self.events.push(3);if self.fail_copy{Err("copy".into())}else{Ok(())}}
fn cleanup_stack_frame(&mut self,_:bool,_:Frame)->Result<ReturnAction,String>{self.events.push(4);Ok(self.action)}
METHODS
}
fn frame(cont:ReturnContinuation,unwinding:bool)->Frame{Frame{loc:if unwinding{Right(123)}else{Left(Loc{block:0,statement_index:0})},body:Body{span:123,basic_blocks:vec![Block{is_cleanup:false}]},cont}}
fn state(pair:bool,unwind:bool,action:ReturnAction,fail_copy:bool)->Cx{
 let stop=ReturnContinuation::Stop{cleanup:true};
 let frames=if pair{vec![frame(stop,false),frame(ReturnContinuation::Goto{ret:Some(mir::BasicBlock(8)),unwind:mir::UnwindAction::Cleanup(mir::BasicBlock(7))},unwind)]}else{vec![frame(stop,unwind)]};
 Cx{frames,events:vec![],action,fail_copy}
}
fn output(cx:&Cx,r:Result<(),String>){println!("{:?}|{:?}|{:?}",r,cx.events,cx.frames.last().map(|f|f.loc));}
fn main(){
 for (pair,unwind,action,fail_copy) in [(true,false,ReturnAction::Normal,false),(true,false,ReturnAction::NoJump,false),(false,false,ReturnAction::NoCleanup,false),(false,true,ReturnAction::Normal,false),(true,true,ReturnAction::Normal,false),(true,false,ReturnAction::Normal,true)] {
 let mut cx=state(pair,unwind,action,fail_copy);let r=cx.return_from_current_stack_frame(unwind);output(&cx,r);
 }
 for target in [mir::UnwindAction::Continue,mir::UnwindAction::Unreachable,mir::UnwindAction::Terminate(1)] {
 let mut cx=state(false,false,ReturnAction::Normal,false);let r=cx.unwind_to_block(target);output(&cx,r);
 }
 let mut cx=state(false,false,ReturnAction::Normal,false);let r=cx.return_to_block(None);output(&cx,r);
}
'''.replace('METHODS',methods)
        with tempfile.TemporaryDirectory() as tmp:
            src,exe=Path(tmp)/'source.rs',Path(tmp)/'source'
            src.write_text(harness)
            run=subprocess.run([str(ROOT/'.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc'),'--edition=2021',str(src),'-o',str(exe)],capture_output=True,text=True)
            self.assertEqual(run.returncode,0,run.stderr)
            output=subprocess.check_output([str(exe)],text=True).splitlines()
        loc=lambda b:f'Some(Left(Loc {{ block: {b}, statement_index: 0 }}))'
        self.assertEqual(output,[
            f'Ok(())|[1, 2, 3, 4]|{loc(8)}',f'Ok(())|[1, 2, 3, 4]|{loc(0)}',
            'Ok(())|[1, 2, 3, 4]|None','Err("UB")|[]|Some(Right(123))',
            f'Ok(())|[1, 2, 4]|{loc(7)}',f'Err("copy")|[1, 2, 3]|{loc(0)}',
            'Ok(())|[]|Some(Right(123))',f'Err("UB")|[]|{loc(0)}',
            f'Ok(())|[5]|{loc(99)}',f'Err("UB")|[]|{loc(0)}'])
        subprocess.run(['.elan/bin/lake','env','lean','MiriTests/ControlFlow/Transitions.lean'],cwd=ROOT,
            env={**os.environ,'ELAN_HOME':str(ROOT/'.elan')},check=True)
if __name__=='__main__':unittest.main()
