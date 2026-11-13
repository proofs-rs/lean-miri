#![no_std]
#![allow(dead_code)]
pub trait Base { fn base(&self); }
pub trait Left: Base { fn left(&self); }
pub trait Right: Base { fn right(&self); }
pub trait Diamond: Left + Right { fn top(&self); }
pub trait Generic<T> { fn generic(&self, value:T); }
pub trait Multi: Generic<u8> + Generic<u16> { fn multi(&self); }
pub trait Project { type Item: Copy; fn take(&self) -> Self::Item; }
pub trait ProjectionSuper: Project<Item=u8> { fn projected(&self); }
pub trait Region<'a> { fn region(&self, value:&'a u8); }
pub fn query_base(_: &dyn Base) {}
pub fn query_diamond(_: &dyn Diamond) {}
pub fn query_multi(_: &dyn Multi) {}
pub fn query_projection(_: &dyn Project<Item=u8>) {}
pub fn query_projection_super(_: &dyn ProjectionSuper) {}
pub fn query_region(_: &dyn for<'a> Region<'a>) {}
pub fn query_auto(_: &(dyn Base + Send)) {}
pub fn query_auto_only(_: &dyn Send) {}
pub fn query_lifetime<'a>(_: &'a (dyn Base + 'a)) {}
pub fn dynamic_root(a:&dyn Base,b:&dyn Diamond,c:&dyn Multi,d:&dyn Project<Item=u8>,e:&dyn ProjectionSuper,f:&dyn for<'a> Region<'a>,g:&(dyn Base+Send),h:&dyn Send) {
 query_base(a);query_diamond(b);query_multi(c);query_projection(d);query_projection_super(e);query_region(f);query_auto(g);query_auto_only(h);query_lifetime(a);
}
