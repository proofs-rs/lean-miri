"""Execute the extracted pinned Rust driver and compare its event trace.
The fixture implements only driver dependencies, not MIR execution semantics.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]

class DriverSourceTest(unittest.TestCase):
    def test_extracted_driver(self):
        path = 'upstream/rustc-source/compiler/rustc_const_eval/src/interpret/step.rs'
        locked = next(f for f in json.loads((ROOT/'upstream/source-lock.json').read_text())['files'] if f['path'] == path)
        self.assertEqual(hashlib.sha256((ROOT/path).read_bytes()).hexdigest(), locked['sha256'])
        source = (ROOT/path).read_text()
        start = source.index('    pub fn step(&mut self)')
        end = source.index('\n    /// Runs the interpretation', start)
        driver = source[start:end].replace('InterpResult<\'tcx, bool>', 'Result<bool, String>')
        harness = r'''
use std::marker::PhantomData;
macro_rules! trace { ($($t:tt)*) => {} }
macro_rules! info { ($($t:tt)*) => {} }
#[derive(Clone,Copy,Debug)] struct Loc { block: usize, statement_index: usize }
#[derive(Clone,Copy)] enum Either { Left(Loc), Right }
impl Either { fn as_mut(&mut self) -> &mut Self { self } fn left(&mut self)->Option<&mut Loc> { match self { Self::Left(l)=>Some(l), _=>None } } }
struct Frame { loc: Either }
struct Block { statements: &'static [()], term: () }
impl Block { fn terminator(&self)->&() { &self.term } }
struct Body { basic_blocks: &'static [Block] }
static BODY: Body = Body { basic_blocks: &[Block { statements: &[()], term: () }] };
fn interp_ok<T>(x:T)->Result<T,String> { Ok(x) }
trait Machine { fn before_terminator(cx:&mut Cx<Self>)->Result<(),String> where Self:Sized; }
struct M;
impl Machine for M { fn before_terminator(cx:&mut Cx<Self>)->Result<(),String> { cx.event(9) } }
struct Cx<M> { frames:Vec<Frame>, events:Vec<u8>, fail:bool, marker:PhantomData<M> }
impl<M:Machine> Cx<M> {
fn stack(&self)->&Vec<Frame>{&self.frames}
fn frame(&self)->&Frame{self.frames.last().unwrap()}
fn frame_mut(&mut self)->&mut Frame{self.frames.last_mut().unwrap()}
fn body(&self)->&'static Body{&BODY}
fn frame_idx(&self)->usize{self.frames.len()-1}
fn event(&mut self,n:u8)->Result<(),String>{self.events.push(n);if self.fail{Err("stop".into())}else{Ok(())}}
fn return_from_current_stack_frame(&mut self,unwinding:bool)->Result<(),String>{assert!(unwinding);self.event(8)}
fn eval_statement(&mut self,_:&())->Result<(),String>{self.event(4)}
fn eval_terminator(&mut self,_:&())->Result<(),String>{self.event(10)}
DRIVER
}
fn main(){
 for (loc,fail) in [(None,false),(Some(Either::Right),false),(Some(Either::Left(Loc{block:0,statement_index:0})),false),(Some(Either::Left(Loc{block:0,statement_index:0})),true),(Some(Either::Left(Loc{block:0,statement_index:1})),false),(Some(Either::Left(Loc{block:0,statement_index:1})),true)] {
 let mut cx=Cx::<M>{frames:loc.map(|loc|vec![Frame{loc}]).unwrap_or_default(),events:vec![],fail,marker:PhantomData};
 let result=cx.step();
 let pc=cx.frames.last().and_then(|f|match f.loc{Either::Left(l)=>Some(l.statement_index),_=>None});
 println!("{:?}|{:?}|{:?}",result,cx.events,pc);
 }
}
'''.replace('DRIVER', driver)
        with tempfile.TemporaryDirectory() as tmp:
            src, exe = Path(tmp)/'driver.rs', Path(tmp)/'driver'
            src.write_text(harness)
            subprocess.run([str(ROOT/'.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc'), '--edition=2021', str(src), '-o', str(exe)], check=True, capture_output=True)
            actual = subprocess.check_output([str(exe)], text=True).splitlines()
        self.assertEqual(actual, [
            'Ok(false)|[]|None', 'Ok(true)|[8]|None',
            'Ok(true)|[4]|Some(1)', 'Err("stop")|[4]|Some(0)',
            'Ok(true)|[9, 10]|Some(1)', 'Err("stop")|[9]|Some(1)',
        ])
        # Lean examples exercise the same paths and check retained mutation/order.
        subprocess.run(['.elan/bin/lake', 'env', 'lean', 'MiriTests/Step/Driver.lean'],
                       cwd=ROOT, env={**__import__('os').environ, 'ELAN_HOME': str(ROOT/'.elan')}, check=True)

if __name__ == '__main__':
    unittest.main()
