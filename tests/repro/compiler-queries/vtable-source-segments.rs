#![no_std]
#![allow(dead_code)]
pub trait A {fn a(&self);}
pub trait B:A {fn b(&self);}
pub trait C:A {fn c(&self);}
pub trait D:B+C {fn d(&self);}
pub trait Empty {}
pub trait EmptyDerived:A {}
pub trait EmptyLeft:Empty {}
pub trait Combo:A+EmptyDerived {}
pub trait Sparse:A+EmptyLeft {}
pub trait Multi:B+EmptyDerived+C {}
pub trait E {fn e(&self);}
pub trait F:D+E {fn f(&self);}
pub trait Parent<T> {fn parent(&self);}
pub trait GenericRoot:Parent<u8>+Parent<u16> {}

pub fn vtable_root(_: &dyn A, _: &dyn B, _: &dyn C, _: &dyn D, _: &dyn Empty,
    _: &dyn EmptyDerived, _: &dyn EmptyLeft, _: &dyn Combo, _: &dyn Sparse,
    _: &dyn Multi, _: &dyn E, _: &dyn F, _: &dyn GenericRoot) {}
