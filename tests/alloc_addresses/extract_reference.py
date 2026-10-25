#!/usr/bin/env python3
"""Verify and wrap the pinned Miri address generator for differential tests."""
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
    generator = checked(root, "upstream/miri-source/src/alloc_addresses/address_generator.rs")
    template = (root / "tests/alloc_addresses/address_generator_reference.rs.in").read_text()
    shim = r'''
extern crate self as rand;
extern crate self as rustc_abi;
extern crate self as rustc_const_eval;
extern crate self as rustc_middle;

use std::ops::Range;

#[derive(Debug, Copy, Clone)]
pub enum AddressError { AddressSpaceFull }

pub trait Rng {
    fn random_range(&mut self, range: Range<u64>) -> u64;
}
pub trait RngExt {}
impl<T: Rng> RngExt for T {}

#[derive(Debug, Copy, Clone)]
pub struct Size(u64);
impl Size {
    pub fn bytes(self) -> u64 { self.0 }
}
#[derive(Debug, Copy, Clone)]
pub struct Align(u64);
impl Align {
    pub fn bytes(self) -> u64 { self.0 }
}

pub mod interpret {
    use crate::AddressError;
    pub type InterpResult<'tcx, T> = Result<T, AddressError>;
    pub fn interp_ok<'tcx, T>(value: T) -> InterpResult<'tcx, T> { Ok(value) }
}

#[macro_export]
macro_rules! err_exhaust {
    ($kind:ident) => { $crate::AddressError::AddressSpaceFull };
}
#[macro_export]
macro_rules! throw_exhaust {
    ($kind:ident) => { return Err($crate::AddressError::AddressSpaceFull); };
}

mod source {
'''
    return shim + generator + "\n}\n" + template


if __name__ == "__main__":
    Path(sys.argv[1]).write_text(generate(Path(__file__).resolve().parents[2]))
