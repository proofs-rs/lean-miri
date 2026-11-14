#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_middle;
use rustc_middle::ty::Variance;
fn name(value: Variance) -> &'static str {
    match value {
        Variance::Covariant => "covariant", Variance::Contravariant => "contravariant",
        Variance::Invariant => "invariant", Variance::Bivariant => "bivariant",
    }
}
fn main() {
    let values = [Variance::Covariant, Variance::Contravariant,
        Variance::Invariant, Variance::Bivariant];
    let mut rows = Vec::new();
    for outer in values {
        for inner in values {
            rows.push(format!("{{\"outer\":\"{}\",\"inner\":\"{}\",\"result\":\"{}\"}}",
                name(outer), name(inner), name(outer.xform(inner))));
        }
    }
    println!("[{}]",rows.join(","));
}
