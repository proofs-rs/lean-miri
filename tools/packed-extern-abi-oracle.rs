#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_abi;
fn main() {
    let rows=rustc_abi::ExternAbi::ALL_VARIANTS.iter().map(|abi|
        format!("{{\"packed\":{},\"spelling\":\"{}\"}}",abi.as_packed(),abi.as_str()))
        .collect::<Vec<_>>();
    println!("[{}]",rows.join(","));
}
