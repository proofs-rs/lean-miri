#!/usr/bin/env python3
"""Pinned FnAbi argument-construction body with explicit signature/type adapters.

Physical layout, target classification and signature normalization are outside
this comparison. Invalid rustc assertions/panics are compared as errors.
"""
from pathlib import Path
import sys
root = Path(__file__).resolve().parents[2]
source = (root/'upstream/rustc-source/compiler/rustc_ty_utils/src/abi.rs').read_text()
a=source.index('    let mut inputs = sig.inputs();', source.index('fn fn_abi_new_uncached'))
b=source.index('    let arg_of = ',a)
body=source[a:b]
prefix=r'''
#![allow(dead_code)]
macro_rules! bug {($($t:tt)*)=>{panic!($($t)*)}}
#[derive(Clone,Copy,PartialEq)] enum ExternAbi {Rust,RustCall,C}
#[derive(Clone,Copy)] struct Ty(usize);
mod ty {pub enum Kind {Tuple(&'static [super::Ty]),Scalar} pub use Kind::*;}
static TUPLE: [Ty;2]=[Ty(2),Ty(3)];
static FULL:ty::Kind=ty::Kind::Tuple(&TUPLE);
static EMPTY:ty::Kind=ty::Kind::Tuple(&[]);
static SCALAR:ty::Kind=ty::Kind::Scalar;
impl Ty {fn kind(&self)->&'static ty::Kind {match self.0 {100=>&FULL,101=>&EMPTY,_=>&SCALAR}}}
struct Sig{inputs:Vec<Ty>,abi:ExternAbi,variadic:bool}
impl Sig {fn abi(&self)->ExternAbi {self.abi} fn c_variadic(&self)->bool {self.variadic} fn inputs(&self)->&[Ty] {&self.inputs}}
fn plan(sig:&Sig,extra_args:&[Ty],caller:Option<Ty>)->String {
'''
suffix=r'''
 let fixed=inputs.len();
 let mut actual:Vec<_>=inputs.iter().copied().chain(extra_args.iter().copied()).collect();
 actual.extend(caller);
 format!("ok:{}:{}",actual.iter().map(|t|t.0.to_string()).collect::<Vec<_>>().join(","),fixed)
}
fn main() {
 std::panic::set_hook(Box::new(|_|{}));
 let cases=[(vec![0,1],ExternAbi::Rust,false,vec![]),
 (vec![0],ExternAbi::C,true,vec![2,3]),(vec![0],ExternAbi::C,false,vec![2]),
 (vec![0,100],ExternAbi::RustCall,false,vec![]),(vec![101],ExternAbi::RustCall,false,vec![]),
 (vec![0,100],ExternAbi::RustCall,false,vec![2]),(vec![0,100],ExternAbi::RustCall,true,vec![]),
 (vec![],ExternAbi::RustCall,false,vec![]),(vec![0,1],ExternAbi::RustCall,false,vec![]),
 (vec![],ExternAbi::C,true,vec![2])];
 for (inputs,abi,variadic,extra) in cases {
  let sig=Sig{inputs:inputs.into_iter().map(Ty).collect(),abi,variadic};
  let extra:Vec<_>=extra.into_iter().map(Ty).collect();
  for caller in [None,Some(Ty(9))] {
   match std::panic::catch_unwind(||plan(&sig,&extra,caller)) {
    Ok(x)=>println!("{x}"),Err(_)=>println!("error")
   }
  }
 }
}
'''
Path(sys.argv[1]).write_text(prefix+body+suffix)
