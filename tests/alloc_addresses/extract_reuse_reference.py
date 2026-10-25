#!/usr/bin/env python3
"""Verify and wrap Miri's pinned reuse-pool source for controlled RNG tests."""
import hashlib
import json
from pathlib import Path
import sys


def checked(root: Path, relative: str) -> str:
    lock = json.loads((root / "upstream/source-lock.json").read_text())
    entries = {entry["path"]: entry for entry in lock["files"]}
    source = (root / relative).read_bytes()
    if hashlib.sha256(source).hexdigest() != entries[relative]["sha256"]:
        raise ValueError(f"source hash mismatch: {relative}")
    return source.decode()


def generate(root: Path) -> str:
    reuse = checked(root, "upstream/miri-source/src/alloc_addresses/reuse_pool.rs")
    template = (root / "tests/alloc_addresses/reuse_pool_reference.rs.in").read_text()
    shim = r'''
extern crate self as rand;
extern crate self as rustc_abi;

use std::ops::Range;

pub trait Rng {
    fn random_bool(&mut self, probability: f64) -> bool;
    fn random_range(&mut self, range: Range<usize>) -> usize;
}
pub trait RngExt {}
impl<T: Rng> RngExt for T {}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Size(pub u64);
impl Size { pub fn bytes(self) -> u64 { self.0 } }
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Align(pub u64);
impl Align { pub fn bytes(self) -> u64 { self.0 } }

pub mod concurrency {
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct VClock(pub u64);
}
pub mod helpers {
    pub trait ToUsize { fn to_usize(self) -> usize; }
    impl ToUsize for u32 { fn to_usize(self) -> usize { self as usize } }
}
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum MemoryKind { Stack, Other }
#[derive(Debug, Copy, Clone)]
pub struct MiriConfig {
    pub address_reuse_rate: f64,
    pub address_reuse_cross_thread_rate: f64,
}
pub type ThreadId = u32;

mod source {
'''
    helpers = r'''
impl ReusePool {
    pub fn snapshot(&self) -> String {
        self.pool.iter().enumerate().map(|(index, subpool)| {
            let entries = subpool.iter().map(|(addr, size, thread, clock)|
                format!("{addr}:{}:{thread}:{}", size.bytes(), clock.0))
                .collect::<Vec<_>>().join(",");
            format!("{index}[{entries}]")
        }).collect::<Vec<_>>().join(";")
    }
    pub fn rate_snapshot(&self) -> String {
        format!("{}:{}", self.address_reuse_rate, self.address_reuse_cross_thread_rate)
    }
}
}
'''
    return shim + reuse + "\n" + helpers + template


if __name__ == "__main__":
    Path(sys.argv[1]).write_text(generate(Path(__file__).resolve().parents[2]))
