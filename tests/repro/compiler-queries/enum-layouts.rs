#![no_std]
#![allow(dead_code)]
pub enum Bool { Empty, Value(bool) }
pub enum Char { Empty, Value(char) }
pub enum Ref { Empty, Value(&'static u64) }
pub enum Function { Empty, Value(fn()) }
pub enum Pair { Empty, Value((bool,u64)) }
pub enum FitBefore { Bytes([u8;3]), Value((bool,u64)) }
pub enum ShiftAfter { Bytes([u8;3]), Value(&'static u64) }
pub enum ManyBool { A, B, C, D, Value(bool) }
pub enum ManyChar { A, B, C, D, Value(char) }
pub enum EqualSize { A((bool,u64)), B((char,u64)) }
pub enum NoNiche { Empty, Value(u64) }
pub enum Three { A, B, Value(&'static u64) }
#[repr(align(32))] pub enum Aligned { Empty, Value(bool) }
#[repr(C)] pub enum C { Empty, Value(bool) }
pub fn niche_layouts(_a:Bool,_b:Char,_c:Ref,_d:Function,_e:Pair,_f:FitBefore,_g:ShiftAfter,_h:ManyBool,_i:ManyChar,_j:EqualSize,_k:NoNiche,_l:Three,_m:Aligned,_n:C) {}
#[repr(i8)] pub enum Negative { A=-128, B=-1, C=127 }
#[repr(u8)] pub enum Wrap { A=0,B=128,C=255 }
#[repr(u64)] pub enum Wide { A=0,B=18446744073709551615 }
#[repr(C)] pub enum CUnits { A,B,C }
#[repr(C,u8)] pub enum CSmall { A(u64),B(u8) }
pub enum SignedPayload { A(i64),B(u64) }
pub enum PointerPayload { A(&'static u64),B(u64) }
pub enum TagGrowth { A(u64,u8),B(u32) }
pub enum Reordered { A(u8,u64,u16),B(u32,u8),C }
#[repr(align(64))] pub enum AlignedTag { A(u64),B(u8) }
pub fn tagged_layouts(_a:Negative,_b:Wrap,_c:Wide,_d:CUnits,_e:CSmall,_f:SignedPayload,_g:PointerPayload,_h:TagGrowth,_i:Reordered,_j:AlignedTag) {}

pub enum Generic<T> { Empty, Value(T) }
pub fn enum_layouts(_a:Bool,_b:Char,_c:Ref,_d:Function,_e:Pair,_f:FitBefore,_g:ShiftAfter,
    _h:ManyBool,_i:ManyChar,_j:EqualSize,_k:NoNiche,_l:Three,_m:Aligned,_n:C,
    _o:Negative,_p:Wrap,_q:Wide,_r:CUnits,_s:CSmall,_t:SignedPayload,_u:PointerPayload,
    _v:TagGrowth,_w:Reordered,_x:AlignedTag,_y:Generic<bool>,_z:Generic<[u8;1031]>) {}
pub fn enum_base(_value:Generic<bool>) {}
