#!/usr/bin/env python3
"""Check the bounded Lean retag pipeline follows pinned Miri call order.

This is deliberately an order check, not a semantic extraction of rustc's
interpreter method bodies: those bodies depend on the full Miri interpreter.
The checker hash-pins the caller and verifies every listed hook site appears
in source order before producing the corresponding Rust reference row.
"""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path


EXPECTED_MOD = "bf38ca356df45e5f365c0ae64bfe7738a0d43e1e"
ORDER = (
    "policy>placeConversion>size>tag>pointerAccess>allocationResolution>"
    "creationLog>protector>kind>freeze>allocationExtra>parentAccess>"
    "dataRace>newChild>replaceProvenance>rebuildValue"
)


def rust_blob_hash(contents: bytes) -> str:
    header = b"blob " + str(len(contents)).encode("ascii") + b"\0"
    return hashlib.sha1(header + contents).hexdigest()


def method_body(source: str, signature: str, next_signature: str) -> str:
    start = source.index(signature)
    end = source.index(next_signature, start)
    return source[start:end]


def require_order(label: str, body: str, markers: list[str]) -> None:
    positions = []
    for marker in markers:
        try:
            positions.append(body.index(marker))
        except ValueError as exc:
            raise ValueError(f"{label} lacks pinned source marker {marker!r}") from exc
    if positions != sorted(positions):
        raise ValueError(f"{label} source operations are out of expected order: {markers}")


def main() -> None:
    if len(sys.argv) != 4:
        raise SystemExit("usage: check_retag_pipeline_order.py MOD_RS RETAG_PIPELINE_LEAN OUT_RS")
    mod_path, lean_path, output_path = map(Path, sys.argv[1:])
    mod_bytes = mod_path.read_bytes()
    actual_hash = rust_blob_hash(mod_bytes)
    if actual_hash != EXPECTED_MOD:
        raise ValueError(f"pinned tree_borrows/mod.rs blob mismatch: {actual_hash}")
    mod = mod_bytes.decode("utf-8")
    lean = lean_path.read_text(encoding="utf-8")

    ptr_value = method_body(mod, "    fn tb_retag_ptr_value(\n", "    /// Protect a place")
    retag_place = method_body(mod, "    fn tb_retag_place(\n", "    fn tb_retag_ptr_value(\n")
    reborrow = method_body(mod, "    fn tb_reborrow(\n", "    fn tb_retag_place(\n")

    require_order("tb_retag_ptr_value type dispatch", ptr_value, [
        "_ if ty.is_box_global", "ty::Ref", "ty::RawPtr", "_ if ty.is_box()",
        "_ => panic!(\"tb_retag_ptr_value",
    ])
    require_order("tb_retag_ptr_value reborrow", ptr_value, [
        "NewPermission::new(", "imm_ptr_to_mplace(val)?", "tb_retag_place(&place, new_perm)?",
        "new_place.to_ref(this)",
    ])
    require_order("tb_retag_place", retag_place, [
        "size_and_align_of_val(place)?", ".new_ptr()", "this.tb_reborrow(",
        "map_provenance(|_| new_prov.unwrap())",
    ])
    require_order("tb_reborrow", reborrow, [
        "check_ptr_access(place.ptr(), ptr_size", "ptr_try_get_alloc_id(place.ptr(), 0)",
        "log_creation(this, None)?", "log_creation(this, Some(",
        ".protected_tags\n                .push((alloc_id, new_tag))", "get_alloc_info(alloc_id).kind",
        "get_tree_borrows_params().precise_interior_mut", "visit_freeze_sensitive(place, ptr_size",
        "get_alloc_extra(alloc_id)?", "is_not()",
        "tree_borrows.perform_access(", "data_race.read_non_atomic(",
        "data_race.write_non_atomic(", "tree_borrows.new_child(",
    ])

    require_order("Lean retagPointerValue", lean, [
        "request.typeShape.classify", "RetagPolicy.create", "request.hooks.placeConversion",
        "request.hooks.sizeAndAlignOfValue",
        "result.state.global.newPointerTag", "let reborrowed := runReborrow", ".placeProvenanceReplaced",
        ".retaggedValueReconstructed",
    ])
    lean_classifier = method_body(lean, "def classify (shape : RetagTypeShape)", "def reference : RetagTypeShape")
    require_order("Lean retag type classifier", lean_classifier, [
        "shape.isGlobalBox", "shape.isReference", "shape.isRawPointer", "shape.isBox",
    ])
    lean_reborrow = method_body(lean, "private def runReborrow", "/-- Source `tb_retag_ptr_value`")
    lean_access = method_body(lean, "private def accessTreeForReborrow", "private def runReborrow")
    require_order("Lean runReborrow", lean_reborrow, [
        "request.hooks.pointerAccess", "request.hooks.allocationResolution",
        "request.hooks.creationLog", "state.global.addProtector", "getAllocInfo",
        "buildInsidePermissions", "request.hooks.allocationExtra", "accessTreeForReborrow",
    ])
    require_order("Lean accessTreeForReborrow", lean_access, [
        "performBorrowAccessRange", "request.hooks.dataRace", ".newChild",
    ])

    output_path.write_text(
        'fn main() { println!("retag-source-order ' + ORDER + '"); }\n',
        encoding="utf-8",
    )
    print("checked tb_retag_ptr_value/tb_retag_place/tb_reborrow order against pinned mod.rs")


if __name__ == "__main__":
    main()
