#![no_std]
#![feature(freeze,unsafe_unpin)]
#![allow(dead_code)]
use core::marker::{Freeze,UnsafeUnpin};
pub trait Plain {}
pub trait Bound:Unpin {}
pub trait Deep:Bound {}
pub trait Frozen:Freeze {}
pub fn query_plain(_: &dyn Plain) {}
pub fn query_explicit(_: &(dyn Plain+Unpin)) {}
pub fn query_super(_: &dyn Deep) {}
pub fn query_auto_only(_: &dyn Unpin) {}
pub fn query_freeze(_: &(dyn Plain+Freeze)) {}
pub fn query_freeze_super(_: &dyn Frozen) {}
pub fn query_unsafe_unpin(_: &(dyn Plain+UnsafeUnpin)) {}
pub fn dynamic_auto_root(a:&dyn Plain,b:&(dyn Plain+Unpin),c:&dyn Deep,d:&dyn Unpin,e:&(dyn Plain+Freeze),f:&dyn Frozen,g:&(dyn Plain+UnsafeUnpin)) {
 query_plain(a);query_explicit(b);query_super(c);query_auto_only(d);query_freeze(e);query_freeze_super(f);query_unsafe_unpin(g);
}
