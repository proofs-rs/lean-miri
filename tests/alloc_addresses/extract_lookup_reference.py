#!/usr/bin/env python3
"""Extract pinned Miri's address lookup method for controlled differential tests."""
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


def item(source: str, marker: str) -> str:
    start = source.index(marker)
    opening = source.index("{", start)
    depth = 0
    for position in range(opening, len(source)):
        if source[position] == "{":
            depth += 1
        elif source[position] == "}":
            depth -= 1
            if depth == 0:
                return source[start:position + 1]
    raise ValueError(f"unterminated source item: {marker}")


def generate(root: Path) -> str:
    source = checked(root, "upstream/miri-source/src/alloc_addresses/mod.rs")
    mode = item(source, "pub enum ProvenanceMode")
    mode_start = mode.find("pub enum ProvenanceMode")
    derive_start = source.rfind("#[derive", 0, source.index("pub enum ProvenanceMode"))
    mode = source[derive_start:source.index("pub enum ProvenanceMode")] + mode[mode_start:]
    lookup = item(source, "fn alloc_id_from_addr(&self, addr: u64, size: i64)")
    template = (root / "tests/alloc_addresses/lookup_reference.rs.in").read_text()
    shim = r'''
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

mod rustc_abi {
    #[derive(Copy, Clone)]
    pub struct Size(pub u64);
    impl Size { pub fn bytes(self) -> u64 { self.0 } }
}
use rustc_abi::Size;
type AllocId = u64;

'''
    scaffolding = r'''
struct AddressGlobalState {
    int_to_ptr_map: Vec<(u64, AllocId)>,
    exposed: HashSet<AllocId>,
    provenance_mode: ProvenanceMode,
}
struct Machine { alloc_addresses: RefCell<AddressGlobalState> }
struct AllocInfo { size: Size }
struct InterpCx {
    machine: Machine,
    sizes: HashMap<AllocId, Size>,
    live: HashSet<AllocId>,
}
impl InterpCx {
    fn eval_context_ref(&self) -> &Self { self }
    fn get_alloc_info(&self, alloc_id: AllocId) -> AllocInfo {
        AllocInfo { size: *self.sizes.get(&alloc_id).expect("test allocation metadata") }
    }
    fn is_alloc_live(&self, alloc_id: AllocId) -> bool { self.live.contains(&alloc_id) }
'''
    return shim + mode + "\n" + scaffolding + lookup + "\n}\n" + template


if __name__ == "__main__":
    Path(sys.argv[1]).write_text(generate(Path(__file__).resolve().parents[2]))
