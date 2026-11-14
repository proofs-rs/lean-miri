#![no_std]
pub struct Wrap<T: ?Sized> { pub value: T }
pub struct RefWrap<T: ?Sized + 'static> { pub value: &'static T }
pub enum Either<T> { Value(T), Empty }
pub enum Only<T> { Value(T) }
pub union Union<T> { pub value: core::mem::ManuallyDrop<T> }
pub struct Dropper(pub u8);
impl Drop for Dropper { fn drop(&mut self) {} }
pub struct RefLoop<'a> { pub next: &'a RefLoop<'a> }
pub fn world_facts_root(_a: Wrap<u8>, _b: RefWrap<u8>, _c: Either<u8>, _d: Only<u8>,
    _e: Union<u8>, _f: Dropper, _g: &'static RefLoop<'static>) {}
