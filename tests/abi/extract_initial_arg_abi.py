#!/usr/bin/env python3
"""Run pinned ArgAbi::new bodies with explicit source-shaped layout adapters.

The adapters expose the fields and layout predicates read by these methods;
this is a component comparison, not rustc target ABI classification.
"""
from pathlib import Path
import sys
root = Path(__file__).resolve().parents[2]
source = (root / 'upstream/rustc-source/compiler/rustc_target/src/callconv/mod.rs').read_text()
start = source.index('    pub fn new(\n        layout: TyAndLayout')
end = source.index('    /// Pass this argument indirectly', start)
bodies = source[start:end]
ext_start = source.index('    pub fn extend_integer_width_to(')
ext_end = source.index('    pub fn cast_to<', ext_start)
bodies += source[ext_start:ext_end]
prefix = r'''
#![allow(dead_code, non_upper_case_globals)]
use std::ops::Deref;
#[derive(Clone,Copy)] struct Size(u64);
impl Size { fn bits(self)->u64 {self.0*8} }
impl Size { const ZERO: Self = Self(0); }
#[derive(Clone,Copy)] struct AbiAlign { abi: u8 }
#[derive(Clone,Copy)] enum BackendRepr {
 Scalar(Scalar), ScalarPair{a:Scalar,b:Scalar,b_offset:Size},
 SimdVector{}, SimdScalableVector{}, Memory{sized:bool}
}
#[derive(Clone,Copy)] enum Primitive {Int(Integer,bool), Float, Pointer}
#[derive(Clone,Copy)] struct Integer(u64);
impl Integer {fn size(self)->Size {Size(self.0)}}
#[derive(Clone,Copy)] struct Scalar {initialized:bool,primitive:Primitive,bool_:bool}
impl Scalar {fn primitive(self)->Primitive {self.primitive} fn is_uninit_valid(self)->bool {!self.initialized}}
impl BackendRepr {fn is_bool(self)->bool {matches!(self,Self::Scalar(Scalar{initialized:true,bool_:true,..}))}}
struct Layout { backend_repr: BackendRepr, size: Size, align: AbiAlign }
#[derive(Clone,Copy)] struct TyAndLayout<'a, Ty> { layout: &'a Layout, ty: Ty }
impl<Ty> Deref for TyAndLayout<'_, Ty> { type Target=Layout; fn deref(&self)->&Layout {self.layout} }
impl<Ty> TyAndLayout<'_, Ty> {
 fn is_zst(&self)->bool {matches!(self.backend_repr,BackendRepr::Memory{sized:true}) && self.size.0==0}
 fn is_unsized(&self)->bool {matches!(self.backend_repr,BackendRepr::Memory{sized:false})}
}
struct ArgAttribute;
impl ArgAttribute {
 const CapturesAddress:u16=6; const NoAlias:u16=8; const NonNull:u16=16;
 const NoUndef:u16=128; const NoFree:u16=512;
}
enum ArgExtension {None,Zext,Sext}
#[derive(Clone,Copy)] struct ArgAttributes { bits:u16, pointee_size:Size, pointee_align:Option<u8>,ext:u8 }
impl ArgAttributes {
 fn new()->Self {Self{bits:0,pointee_size:Size(0),pointee_align:None,ext:0}}
 fn ext(&mut self,e:ArgExtension)->&mut Self {self.ext=match e {ArgExtension::None=>0,ArgExtension::Zext=>1,ArgExtension::Sext=>2};self}
 fn set(&mut self,b:u16)->&mut Self {self.bits|=b;self}
}
enum IndirectMode {Pointer}
enum PassMode {
 Ignore, Direct(ArgAttributes), Pair(ArgAttributes,ArgAttributes),
 Indirect{attrs:ArgAttributes,address_space:Option<u8>,mode:IndirectMode},
 IndirectUnsized{attrs:ArgAttributes,meta_attrs:ArgAttributes}
}
struct ArgAbi<'a,Ty> {layout:TyAndLayout<'a,Ty>,mode:PassMode}
impl<'a,Ty> ArgAbi<'a,Ty> {
'''
suffix = r'''
}
fn attrs(a:ArgAttributes)->String {format!("{}/{}/{}/{}",a.bits,a.pointee_size.0,a.pointee_align.unwrap_or(99),a.ext)}
fn show(m:PassMode)->String {match m {
 PassMode::Ignore=>"ignore".into(), PassMode::Direct(a)=>format!("direct:{}",attrs(a)),
 PassMode::Pair(a,b)=>format!("pair:{}:{}",attrs(a),attrs(b)),
 PassMode::Indirect{attrs:a,..}=>format!("indirect:{}",attrs(a)),
 PassMode::IndirectUnsized{attrs:a,meta_attrs:b}=>format!("unsized:{}:{}",attrs(a),attrs(b))
}}
fn main() {
 let scalar=Scalar{initialized:false,primitive:Primitive::Int(Integer(1),false),bool_:false};
 let cases=[(BackendRepr::Memory{sized:true},0),(BackendRepr::Memory{sized:true},24),
 (BackendRepr::Memory{sized:false},0),(BackendRepr::Scalar(scalar),1),
 (BackendRepr::ScalarPair{a:scalar,b:scalar,b_offset:Size(8)},16),
 (BackendRepr::SimdVector{},4),(BackendRepr::SimdScalableVector{},0)];
 for (backend_repr,size) in cases {
  let layout=Layout{backend_repr,size:Size(size),align:AbiAlign{abi:3}};
  let l=TyAndLayout{layout:&layout,ty:()};
  println!("{}",show(ArgAbi::new(l,|_,_|ArgAttributes::new()).mode));
  println!("{}",show(ArgAbi::new(l,|_,offset|{let mut a=ArgAttributes::new();a.bits=(offset.0+1)as u16;a}).mode));
 }
 for (primitive,bool_) in [(Primitive::Int(Integer(1),false),true),
 (Primitive::Int(Integer(1),false),false),(Primitive::Int(Integer(1),true),false),
 (Primitive::Int(Integer(4),true),false),(Primitive::Float,false)] {
  for initialized in [true,false] {for bits in [0,8,32,64] {
   let scalar=Scalar{initialized,primitive,bool_};
   let layout=Layout{backend_repr:BackendRepr::Scalar(scalar),size:Size(8),align:AbiAlign{abi:3}};
   let mut arg=ArgAbi::new(TyAndLayout{layout:&layout,ty:()},|scalar,_| {
    let mut attrs=ArgAttributes::new();
    if !scalar.is_uninit_valid() {attrs.set(ArgAttribute::NoUndef);}
    attrs
   });
   arg.extend_integer_width_to(bits);
   println!("{}",show(arg.mode));
  }}
 }
}
'''
Path(sys.argv[1]).write_text(prefix + bodies + suffix)
