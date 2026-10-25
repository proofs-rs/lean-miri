#!/usr/bin/env python3
"""Compile the complete pinned provenance_map.rs against the pinned rustc-dev.

Only the surrounding test construction/printing code is local. The source
module is inserted unchanged after checking its source-lock SHA-256.
"""
import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[2]
relative = "upstream/rustc-source/compiler/rustc_middle/src/mir/interpret/allocation/provenance_map.rs"
lock = json.loads((root / "upstream/source-lock.json").read_text())
expected = next(entry["sha256"] for entry in lock["files"] if entry["path"] == relative)
source = (root / relative).read_bytes()
if hashlib.sha256(source).hexdigest() != expected:
    raise SystemExit("provenance_map source hash mismatch")
prefix = '''#![feature(rustc_private, step_trait, range_bounds_is_empty)]
extern crate rustc_driver;
extern crate rustc_abi;
extern crate rustc_middle;
extern crate rustc_data_structures;
extern crate rustc_macros;
extern crate rustc_serialize;
extern crate tracing;
extern crate either;
use rustc_abi::{HasDataLayout,Size,TargetDataLayout};
use rustc_middle::mir::interpret::{AllocRange,CtfeProvenance,Provenance,alloc_range,AllocId,Pointer};
mod mir {pub mod interpret {pub use rustc_middle::mir::interpret::{AllocError,AllocResult};}}
mod source {
'''
helper = '''
pub fn fixture<Prov: Provenance>(ptrs: Vec<(u64,Prov)>, frags: Option<Vec<(u64,u8,Prov,[u8;8])>>) -> ProvenanceMap<Prov> {
    ProvenanceMap {
        ptrs: SortedMap::from_presorted_elements(ptrs.into_iter().map(|(offset,p)|(Size::from_bytes(offset),p)).collect()),
        bytes: frags.map(|values| Box::new(SortedMap::from_presorted_elements(values.into_iter().map(|(offset,idx,prov,bytes)|(Size::from_bytes(offset),PointerFrag{idx,prov,bytes})).collect())))
    }
}
pub fn snapshot<Prov:Provenance>(map:&ProvenanceMap<Prov>) -> (Vec<(u64,Prov)>,Option<Vec<(u64,u8,Prov,[u8;8])>>) {
    (map.ptrs.iter().map(|(s,p)|(s.bytes(),*p)).collect(),map.bytes.as_ref().map(|bytes|bytes.iter().map(|(s,f)|(s.bytes(),f.idx,f.prov,f.bytes)).collect()))
}
}
'''
template = (root / "tests/provenance_map/reference.rs.in").read_text()
Path(sys.argv[1]).write_text(prefix + source.decode() + helper + template)
