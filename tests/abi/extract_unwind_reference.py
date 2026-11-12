#!/usr/bin/env python3
"""Execute pinned fn_can_unwind with explicit raw-query dependency adapters.

This checks the decision procedure. It does not check rustc attribute queries;
the fresh producer serializes those materials from the pinned TyCtxt.
"""
from pathlib import Path
import sys
root = Path(__file__).resolve().parents[2]
source = (root / 'upstream/rustc-source/compiler/rustc_middle/src/ty/layout.rs').read_text()
start = source.index('pub fn fn_can_unwind(')
end = source.index('\n/// Error produced', start)
body = source[start:end].replace("tcx: TyCtxt<'_>, fn_def_id: Option<DefId>", 'tcx: TyCtxt, fn_def_id: Option<usize>')
prefix = r'''
#![allow(dead_code)]
#[derive(Clone,Copy)] enum ExternAbi {
 C{unwind:bool},System{unwind:bool},Cdecl{unwind:bool},Stdcall{unwind:bool},
 Fastcall{unwind:bool},Vectorcall{unwind:bool},Thiscall{unwind:bool},Aapcs{unwind:bool},
 Win64{unwind:bool},SysV64{unwind:bool},PtxKernel,Msp430Interrupt,X86Interrupt,
 GpuKernel,EfiApi,AvrInterrupt,AvrNonBlockingInterrupt,CmseNonSecureCall,
 CmseNonSecureEntry,Custom,RiscvInterruptM,RiscvInterruptS,RustInvalid,Swift,
 LlvmIntrinsic,Rust,RustCall,RustCold,RustPreserveNone,RustTail
}
struct CodegenFnAttrFlags;
impl CodegenFnAttrFlags {const NEVER_UNWIND:bool=true;}
struct Flags(bool); impl Flags {fn contains(&self,_:bool)->bool {self.0}}
struct Attributes{flags:Flags}
enum LangItem{DropGlue}
#[derive(Clone,Copy)] struct Panic(bool);impl Panic {fn unwinds(&self)->bool {self.0}}
#[derive(Clone,Copy)] struct Unstable {panic_in_drop:Panic}
#[derive(Clone,Copy)] struct Options {unstable_opts:Unstable}
#[derive(Clone,Copy)] struct Session {opts:Options,panic:Panic}
impl Session {fn panic_strategy(&self)->Panic {self.panic}}
#[derive(Clone,Copy)] struct TyCtxt {sess:Session,never:bool,foreign:bool,drop:bool}
impl TyCtxt {
 fn codegen_fn_attrs(&self,_:usize)->Attributes {Attributes{flags:Flags(self.never)}}
 fn is_foreign_item(&self,_:usize)->bool {self.foreign}
 fn is_lang_item(&self,_:usize,_:LangItem)->bool {self.drop}
}
'''
suffix = r'''
fn main() {
 for abi in [ExternAbi::C{unwind:false},ExternAbi::C{unwind:true},ExternAbi::System{unwind:true},
 ExternAbi::Rust,ExternAbi::RustCall,ExternAbi::Custom,ExternAbi::LlvmIntrinsic] {
  for flags in [None,Some((false,false,false)),Some((true,false,false)),
   Some((false,true,false)),Some((true,true,false)),Some((false,false,true)),
   Some((true,false,true)),Some((false,true,true)),Some((true,true,true))] {
   for panic in [false,true] {for drop in [false,true] {
    let (never,foreign,drop_flag)=flags.unwrap_or((false,false,false));
    let tcx=TyCtxt{sess:Session{opts:Options{unstable_opts:Unstable{panic_in_drop:Panic(drop)}},
      panic:Panic(panic)},never,foreign,drop:drop_flag};
    println!("{}",fn_can_unwind(tcx,flags.map(|_|0),abi));
   }}
  }
 }
}
'''
Path(sys.argv[1]).write_text(prefix+body+suffix)
