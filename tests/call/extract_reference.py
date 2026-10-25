#!/usr/bin/env python3
"""SHA-checked extraction of source argument evaluation and disjointness block."""
import hashlib, json, pathlib, sys
root = pathlib.Path(__file__).resolve().parents[2]
path = 'upstream/rustc-source/compiler/rustc_const_eval/src/interpret/step.rs'
raw = (root/path).read_bytes()
locked = {x['path']:x for x in json.loads((root/'upstream/source-lock.json').read_text())['files']}
assert hashlib.sha256(raw).hexdigest() == locked[path]['sha256']
src = raw.decode()
def block(start):
    start = src.index('{',start)
    depth=0
    for i in range(start,len(src)):
        depth += (src[i]=='{') - (src[i]=='}')
        if depth==0: return src[start:i+1]
argument = block(src.index('fn eval_fn_call_argument('))
disjoint = block(src.index("let move_definitely_disjoint = 'move_definitely_disjoint:"))
prelude = r'''
use std::collections::HashSet as FxHashSet;
use std::iter;
fn interp_ok<T>(x:T)->Result<T,()> {Ok(x)}
mod mir {
 pub type Local=usize;
 #[derive(Clone,Copy)] pub struct Place {pub local:usize,pub indirect:bool}
 impl Place { pub fn is_indirect_first_projection(&self)->bool {self.indirect} }
 pub enum Operand {Copy(Place),Move(Place),Constant(()),RuntimeChecks(())}
}
struct Spanned {node:mir::Operand}
#[derive(Clone)] struct MPlace;
enum Either<L,R>{Left(L),Right(R)}
#[derive(Clone)] struct Op {indirect:bool}
impl Op {fn as_mplace_or_imm(&self)->Either<MPlace,()> {if self.indirect {Either::Left(MPlace)}else{Either::Right(())}}}
enum FnArg {Copy(Op),InPlace(MPlace)}
struct Cx {trace:Vec<String>,indirect:bool}
impl Cx {
 fn eval_operand(&mut self,_:&mir::Operand,_:Option<()>)->Result<Op,()>{self.trace.push("operand".into());Ok(Op{indirect:false})}
 fn eval_place(&mut self,_:mir::Place,skip:bool)->Result<(),()>{self.trace.push(format!("place:{skip}"));Ok(())}
 fn place_to_op(&mut self,_:&())->Result<Op,()>{self.trace.push("placeToOp".into());Ok(Op{indirect:self.indirect})}
 fn force_allocation(&mut self,_:&())->Result<MPlace,()>{self.trace.push("forceAllocation".into());Ok(MPlace)}
'''
main = r'''
}
fn disjoint(args:&[Spanned],dest:&mir::Place)->bool {
 let move_definitely_disjoint = 'move_definitely_disjoint: DISJOINT;
 move_definitely_disjoint
}
fn main(){
 for flag in [false,true] {for indirect in [false,true] {
 let mut cx = Cx{trace:vec![],indirect};
 let result=cx.eval_fn_call_argument(&mir::Operand::Move(mir::Place{local:1,indirect:false}),flag).unwrap();
 println!("A {flag} {indirect} {} {}",matches!(result,FnArg::InPlace(_)),cx.trace.join(","));
 }}
 let mut cx=Cx{trace:vec![],indirect:false};
 cx.eval_fn_call_argument(&mir::Operand::Copy(mir::Place{local:1,indirect:false}),false).unwrap();
 println!("C {}",cx.trace.join(","));
 for a in 0..3 {for b in 0..3 {for indirect in [false,true] {
 let args=vec![Spanned{node:mir::Operand::Move(mir::Place{local:a,indirect})}];
 println!("D {a} {b} {indirect} {}",disjoint(&args,&mir::Place{local:b,indirect:false}));
 }}}
}
'''.replace('DISJOINT',disjoint)
pathlib.Path(sys.argv[1]).write_text(prelude+'fn eval_fn_call_argument(&mut self,op:&mir::Operand,move_definitely_disjoint:bool)->Result<FnArg,()>'+argument+main)
