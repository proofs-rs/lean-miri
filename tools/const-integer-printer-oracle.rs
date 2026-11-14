#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_middle;
extern crate rustc_abi;
use rustc_middle::ty::{ConstInt,ScalarInt};
fn main() {
 let mut rows=Vec::new();
 for bytes in [1,2,4,8,16] {
  let midpoint=1u128 << (bytes*8-1);
  let max=u128::MAX >> (128-bytes*8);
  for signed in [false,true] {
   for pointer in [false,true] {
    if pointer && bytes!=8 {continue}
    for raw in [0,1,midpoint-1,midpoint,midpoint+1,max] {
     let value=ConstInt::new(ScalarInt::try_from_uint(raw,rustc_abi::Size::from_bytes(bytes)).unwrap(),signed,pointer);
     rows.push(format!("{{\"bytes\":{bytes},\"raw\":\"{raw}\",\"signed\":{signed},\"pointer\":{pointer},\"display\":{:?}}}",format!("{value:?}")));
    }
   }
  }
 }
 println!("[{}]",rows.join(","));
}
