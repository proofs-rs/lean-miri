#!/usr/bin/env python3
"""Hash-check pinned sources and extract unchanged Rust items for comparison.

This extractor is deliberately tied to these exact source hashes. It is not a
general Rust parser. Shims supply data layout/diagnostic types; tested function
bodies are byte-for-byte source slices.
"""
import hashlib
import json
from pathlib import Path
import sys


def item(text, marker):
    start = text.index(marker)
    opening = text.index("{", start)
    depth = 0
    for pos in range(opening, len(text)):
        if text[pos] == "{":
            depth += 1
        elif text[pos] == "}":
            depth -= 1
            if depth == 0:
                return text[start:pos + 1]
    raise ValueError(f"unterminated source item: {marker}")


def checked(root, relative):
    lock = json.loads((root / "upstream/source-lock.json").read_text())
    entries = {entry["path"]: entry for entry in lock["files"]}
    data = (root / relative).read_bytes()
    if hashlib.sha256(data).hexdigest() != entries[relative]["sha256"]:
        raise ValueError(f"source hash mismatch: {relative}")
    return data.decode()


def generate(root):
    abi = checked(root, "upstream/rustc-source/compiler/rustc_abi/src/lib.rs")
    pointer = checked(root, "upstream/rustc-source/compiler/rustc_middle/src/mir/interpret/pointer.rs")
    tags = checked(root, "upstream/miri-source/src/borrow_tracker/mod.rs")
    machine = checked(root, "upstream/miri-source/src/machine.rs")
    size_methods = ["pub fn from_bytes(", "pub fn bytes(self)", "pub fn bits(self)",
                    "pub fn truncate(", "pub fn sign_extend(",
                    "pub fn unsigned_int_max(", "pub fn signed_int_min(", "pub fn signed_int_max("]
    pieces = ["use std::{fmt, num::NonZero};",
              "#[derive(Clone, Copy, Debug, PartialEq, Eq)] struct Size { raw: u64 }",
              "impl Size { pub const ZERO: Size = Size { raw: 0 };" + "\n".join(item(abi, method) for method in size_methods) + "}",
              "#[derive(Clone, Copy, Debug, PartialEq, Eq)] struct AllocId(NonZero<u64>);",
              "#[derive(Clone, Copy, Debug, PartialEq, Eq)] struct BorTag(NonZero<u64>);",
              item(tags, "impl BorTag {"),
              "#[derive(Clone, Copy)] struct DataLayout { size: Size }",
              "trait HasDataLayout { fn data_layout(&self) -> &DataLayout; }",
              "impl HasDataLayout for DataLayout { fn data_layout(&self)->&DataLayout { self } }",
              "impl DataLayout { fn pointer_size(&self)->Size { self.size } }",
              "mod engine { use super::*;",
              item(pointer, "pub trait PointerArithmetic:"),
              "impl<T: HasDataLayout> PointerArithmetic for T {}",
              item(pointer, "pub trait Provenance:"),
              "#[derive(Clone, Copy, PartialEq, Eq)] pub struct CtfeProvenance(NonZero<u64>);",
              item(pointer, "impl From<AllocId> for CtfeProvenance {"),
              item(pointer, "impl fmt::Debug for CtfeProvenance {"),
              pointer[pointer.index("const IMMUTABLE_MASK:"):pointer.index("impl CtfeProvenance {")],
              item(pointer, "impl CtfeProvenance {"),
              item(pointer, "impl Provenance for CtfeProvenance {"),
              "impl CtfeProvenance { pub fn raw_for_test(self)->u64 {self.0.get()} }",
              "#[derive(Clone, Copy, Debug, PartialEq, Eq)] pub struct Pointer<Prov = CtfeProvenance> { pub offset: Size, pub provenance: Prov }",
              item(pointer, "impl<Prov> Pointer<Prov> {"),
              item(pointer, "impl<Prov> From<Pointer<Prov>> for Pointer<Option<Prov>> {"),
              item(pointer, "impl<Prov> Pointer<Option<Prov>> {"),
              item(pointer, "impl Pointer<CtfeProvenance> {"),
              item(pointer, "impl From<AllocId> for Pointer {"),
              item(pointer, "impl From<CtfeProvenance> for Pointer {"),
              "}", "mod machine { use super::*; mod interpret { pub use crate::engine::*; }",
              "#[derive(Clone, Copy, Debug, PartialEq, Eq)]" + item(machine, "pub enum Provenance {"),
              "#[derive(Clone, Copy, Debug, PartialEq, Eq)]" + item(machine, "pub enum ProvenanceExtra {"),
              item(machine, "impl interpret::Provenance for Provenance {"),
              item(machine, "impl ProvenanceExtra {"), "}"]
    template = (root / "tests/pointer/reference.rs.in").read_text()
    return "\n".join(pieces) + "\n" + template


if __name__ == "__main__":
    Path(sys.argv[1]).write_text(generate(Path(__file__).resolve().parents[2]))
