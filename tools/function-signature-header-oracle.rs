#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_middle;
use rustc_middle::ty;
fn main() {
    let mut rows = Vec::new();
    for (count,index) in [(0,None),(0,Some(0)),(1,Some(0)),(1,Some(1)),
        (255,Some(254)),(256,Some(255)),(1,Some(254)),(512,None)] {
        let signature = ty::FnSigKind::dummy();
        let accepted = signature.set_splatted(index,count).is_ok();
        let index = index.map(|index|index.to_string()).unwrap_or_else(||"null".into());
        rows.push(format!("{{\"inputs\":{count},\"splatted\":{index},\"accepted\":{accepted}}}"));
    }
    println!("[{}]",rows.join(","));
}
