#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_data_structures;
extern crate rustc_hashes;
use std::hash::Hasher;
use rustc_data_structures::stable_hash::StableHasher;
use rustc_hashes::Hash128;
fn main() {
 let rows=(0..=260).chain([511,512,513,1024]).map(|n| {
  let bytes=(0..n).map(|i| ((i*71+19)%256) as u8).collect::<Vec<_>>();
  let mut hasher=StableHasher::new();hasher.write(&bytes);
  let result:Hash128=hasher.finish();
  format!("{{\"bytes\":{:?},\"hash\":\"{}\"}}",bytes,result.as_u128())
 }).collect::<Vec<_>>();
 println!("[{}]",rows.join(","));
}
