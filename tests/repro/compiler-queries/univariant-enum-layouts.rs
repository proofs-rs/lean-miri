#![no_std]
#![feature(never_type)]
#![allow(dead_code)]

pub enum Empty {}
pub enum Unit { Only }
pub enum Explicit { Only = 37 }
pub enum Scalar { Only(u32) }
pub enum Pair { Only(u8, u64) }
pub enum Generic<T> { Only(T) }
#[repr(align(32))]
pub enum Aligned { Only(u8) }
pub enum Absent { Only(!) }
pub enum AlignedDead { Only(!, [u16; 0]) }
pub enum PresentDead { Only(!, u8) }
pub enum ZeroArray { Only([!; 0]) }
#[repr(C)]
pub enum CControl { Only(u8) }
#[repr(u8)]
pub enum IntegerControl { Only = 9 }
pub enum MultipleControl { A, B }
pub struct NestedDynamic(pub &'static dyn core::fmt::Debug);
pub enum NestedDynamicControl { Only(NestedDynamic) }
pub enum DynamicControl { Only(&'static dyn core::fmt::Debug) }

pub fn enum_layouts(_a: Empty, _b: Unit, _c: Explicit, _d: Scalar, _e: Pair,
    _f: Generic<u8>, _g: Generic<[u8; 1031]>, _h: Aligned, _i: Absent,
    _j: AlignedDead, _k: PresentDead, _l: ZeroArray, _m: CControl,
    _n: IntegerControl, _o: MultipleControl, _p: DynamicControl, _q: NestedDynamicControl) {}

pub fn enum_base(_value: Generic<u8>) {}
