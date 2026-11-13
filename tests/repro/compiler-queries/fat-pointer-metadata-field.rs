use std::any::Any;
pub trait Root { fn root(&self); }
pub trait Left:Root {fn left(&self);}
pub trait Right:Root {fn right(&self);}
pub trait Diamond:Left+Right {fn leaf(&self);}
pub trait Narrow { fn entry(&self); fn sized(&self) where Self:Sized; fn generic<T>(&self) where Self:Sized; }
pub trait Borrow { fn borrow<'a>(&'a self)->&'a u8; }
pub trait Generic<T> { fn value(&self)->T; }
pub fn metadata_fields(_: &dyn Any, _: &(dyn Any+Send), _: *const dyn Send,
    _: *const dyn Diamond, _: &dyn Narrow, _: &dyn Borrow,
    _: &dyn Generic<u32>, _: &dyn Generic<u64>, _: &(dyn Diamond+Send)) {}
