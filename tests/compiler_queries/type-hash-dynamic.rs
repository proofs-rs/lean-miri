#![allow(dead_code)]
pub trait Plain {fn f(&self);}
pub trait Param<T> {type Out; fn f(&self)->Self::Out;}
pub trait Lender<'a> {type Item; fn get(&self, x:&'a u8)->Self::Item;}
pub fn dynamic_hashes(
 _: &(dyn Plain+'static),
 _: &(dyn Plain+Send+Sync+'static),
 _: &(dyn Param<u32,Out=bool>+Send+'static),
 _: &(dyn Iterator<Item=u8>+'static),
 _: &(dyn for<'a> Lender<'a,Item=&'a u8>+'static),
 _: &(dyn for<'b> Fn(&'b u8)->bool+'static),
 _: &'static (dyn Plain+'static),
 _: &(dyn Send+'static),
) {}
