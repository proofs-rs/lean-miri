#!/usr/bin/env python3
"""Regenerate the reviewed source-to-Lean ledger with current syn symbol IDs."""

from __future__ import annotations

import argparse
import gzip
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OP = "upstream/rustc-source/compiler/rustc_const_eval/src/interpret/operator.rs"
SCALAR = "upstream/rustc-source/compiler/rustc_middle/src/ty/consts/int.rs"
PERMS = "upstream/miri-source/src/borrow_tracker/tree_borrows/perms.rs"
INT_TESTS = [
    "tests/integer_ops/extract_reference.py", "tests/integer_ops/reference.rs.in",
    "tests/integer_ops/Differential.lean", "tests/integer_ops/run_differential.sh",
]
SCALAR_TESTS = [
    "tests/scalar/extract_reference.py", "tests/scalar/reference.rs.in",
    "tests/scalar/Differential.lean", "MiriTests/Scalar/LeanTests.lean",
    "tests/scalar/run_differential.sh",
]
TREE_TESTS = [
    "tests/tree_borrows/extract_reference.py", "tests/tree_borrows/permission_reference.rs.in",
    "tests/tree_borrows/Differential.lean", "tests/tree_borrows/run_differential.sh",
]

INT_LIMITS = [
    "The extractor copies the exact Rust method body after checking the pinned source SHA-256, but substitutes rustc interpreter context, types, and layouts with a standalone adapter.",
    "The input set is finite; this is not an exhaustive proof over all 128-bit values.",
    "Operand loading, real layout queries, pointer/float operations, and whole-MIR execution remain outside the row.",
    "The Lean theorems prove properties of the Lean model; they do not prove Rust-to-Lean equivalence.",
]
SCALAR_LIMITS = [
    "The harness verifies pinned source-file hashes and calls the API in the pinned rustc toolchain; it does not copy the ScalarInt method body into the reference program.",
    "The scalar suite compares 39 lines total: 24 ScalarInt-specific U/T/I/J/Q/C/E/P lines and 15 separate Scalar/Allocation-layer lines.",
    "No source-to-Lean equivalence proof is provided.",
]
TREE_LIMITS = [
    "The extractor checks exact pinned Git blob IDs and copies relevant source blocks into a standalone shim; surrounding Miri context/types and diagnostic adapters are local.",
    "The source behavior is exercised on the named finite permission/access domain.",
    "These rows do not establish full tree, memory, initialization, provenance, concurrency, or whole-Miri semantics.",
]


def main() -> int:
    global ROOT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the generated ledger differs")
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args()
    ROOT = args.root.resolve()
    inventory_path = ROOT / "tools/source-analysis/inventory.json.gz"
    with gzip.open(inventory_path, "rt", encoding="utf-8") as stream:
        inventory = json.load(stream)
    lock = json.loads((ROOT / "upstream/source-lock.json").read_text(encoding="utf-8"))
    lock_files = {row["path"]: row for row in lock["files"]}
    entries = []

    def add(scope, eid, path, line, display, needle, lean, claim, disposition,
            evidence_kind, evidence_files, evidence_note, *, extracted=False,
            selectors=None, rows=None, proofs=None, features=None, limits=None):
        matches = [
            sym for sym in inventory["symbols"]
            if sym.get("path") == path
            and sym.get("kind") in {"function", "method"}
            and sym.get("span", {}).get("line") == line
            and needle in sym.get("symbol", "")
        ]
        if len(matches) != 1:
            raise ValueError(f"AST lookup {path}:{line} {needle!r} matched {len(matches)} symbols")
        sym = matches[0]
        entry = {
            "id": eid,
            "scope_id": scope,
            "source": {
                "path": path,
                "line": line,
                "symbol": display,
                "sha256": lock_files[path]["sha256"],
                "ast_symbol_id": sym["id"],
                "ast_symbol": sym["symbol"],
            },
            "lean_definitions": lean,
            "review_disposition": disposition,
            "source_function_complete": False,
            "slice_claim": claim,
            "evidence": {
                "kind": evidence_kind,
                "source_body_extracted": extracted,
                "files": evidence_files,
                "observation_scope": evidence_note,
            },
            "limitations": limits or [
                "This row concerns only the named source operation slice and is not a whole-function or whole-module equivalence claim."
            ],
            "manual_feature_ids": features or [],
        }
        if selectors is not None:
            entry["evidence"]["output_selectors"] = selectors
        if rows is not None:
            entry["evidence"]["observed_rows"] = rows
        if proofs is not None:
            entry["proofs"] = proofs
        entries.append(entry)

    # Exact extracted integer, bool, and char operator method bodies.
    add("integer_ops", "integer_ops.binary_int_op", OP, 97, "InterpCx::binary_int_op", "binary_int_op",
        ["Miri.Interpreter.IntegerOps.binary", "Miri.Interpreter.IntegerOps.decode",
         "Miri.Interpreter.IntegerOps.shift", "Miri.Interpreter.IntegerOps.arithmetic",
         "Miri.Interpreter.IntegerOps.truncate", "Miri.Interpreter.IntegerOps.scalarResult"],
        "Selected integer binary branches (arithmetic, div/rem, shifts, comparisons, bitwise, overflow) on checked scalar operands and supplied integer types.",
        "body_extracted_and_differentialed", "byte_exact_body_differential", INT_TESTS,
        "22,052 finite observations: 10,290 same-size binary cases, 11,760 shift cases, and 2 target-sized asymmetry cases.",
        extracted=True, rows=22052,
        proofs=["Miri.Interpreter.IntegerOps.binary_division_by_zero", "Miri.Interpreter.IntegerOps.binary_remainder_by_zero",
                "Miri.Interpreter.IntegerOps.division_success_nonzero"],
        features=["rustc.interpret.integer_ops.selected", "rustc.interpret.integer_ops.zero_divisor_guard"], limits=INT_LIMITS)
    add("integer_ops", "integer_ops.binary_bool_op", OP, 51, "InterpCx::binary_bool_op", "binary_bool_op",
        ["Miri.Interpreter.IntegerOps.binaryBool"],
        "Boolean comparisons and bitwise bool operations, with other operators represented as invalid.",
        "body_extracted_and_differentialed", "byte_exact_body_differential", INT_TESTS,
        "104 cases from two boolean inputs and the finite operator list.", extracted=True, rows=104, selectors=["B"],
        features=["rustc.interpret.integer_ops.selected"], limits=["The body is byte-extracted, while context/result wrappers are harness adapters.", "No whole-function or whole-interpreter equivalence proof is provided."])
    add("integer_ops", "integer_ops.binary_char_op", OP, 32, "InterpCx::binary_char_op", "binary_char_op",
        ["Miri.Interpreter.IntegerOps.binaryChar"],
        "Character comparisons and Cmp over a selected set of valid Unicode scalar values.",
        "body_extracted_and_differentialed", "byte_exact_body_differential", INT_TESTS,
        "650 cases from a 5×5 character set and the finite operator list.", extracted=True, rows=650, selectors=["C"],
        features=["rustc.interpret.integer_ops.selected"], limits=["Only selected character values/operators are exercised.", "Context and result wrappers are harness adapters."])
    add("integer_ops", "integer_ops.three_way_compare_adapter", OP, 27, "InterpCx::three_way_compare", "three_way_compare",
        ["Miri.Interpreter.IntegerOps.binary", "Miri.Interpreter.IntegerOps.binaryChar"],
        "Reviewed Cmp dependency; the Rust harness substitutes generic Ord::cmp instead of extracting this helper body.",
        "reviewed_harness_boundary", "adapter_reporting", INT_TESTS,
        "Used for Cmp output; no separately extracted helper or separately counted test family.", selectors=["BinOp::Cmp"],
        limits=["The helper body is not copied into the harness, so it is not independently differential-tested.", "Lean compare is a model implementation, not a source-equivalence theorem."])

    # Selected rustc_middle ScalarInt methods. See SCALAR_LIMITS for the API
    # harness boundary and the 24-vs-15 output partition.
    def scalar(eid, line, display, needle, lean, claim, disposition, selectors, note,
               *, rows=None, kind="pinned_api_differential", limits=None):
        add("scalar_int", eid, SCALAR, line, display, needle, lean, claim, disposition,
            kind, SCALAR_TESTS, note, selectors=selectors, rows=rows, limits=limits)
    scalar("scalar_int.size_reporting", 207, "ScalarInt::size", "ScalarInt::size", ["Miri.Memory.ScalarInt.size"],
        "Used by output serialization to print byte width; no standalone behavioral claim.", "reviewed_reporting_adapter", ["U", "T", "I", "J"],
        "show_int formats constructor results using this width accessor.", kind="adapter_reporting", limits=["The source accessor serializes observations; no separate semantic test/proof is attributed."])
    scalar("scalar_int.raw_construction_helper", 203, "ScalarInt::raw", "ScalarInt::raw", ["Miri.Memory.ScalarInt.truncated", "Miri.Memory.ScalarInt.null"],
        "Reviewed helper stores data and nonzero size; Lean construction is inlined through checked/private constructors.", "reviewed_construction_boundary", ["U", "T", "I", "J", "P zero_size"],
        "Reached by constructor and null calls; no isolated output identifies raw independently.", limits=["No identical standalone Lean raw helper exists; behavior is represented across truncated/null.", "No source equivalence proof is claimed."])
    scalar("scalar_int.check_data_boundary", 212, "ScalarInt::check_data", "ScalarInt::check_data", ["Miri.Memory.ScalarInt.ScalarInt"],
        "Reviewed debug assertion that stored data fits its size; Lean uses private fields/constructors but has no corresponding assertion.", "reviewed_unmapped_source_boundary", [],
        "Reached internally by source reads but not isolated by the harness.", kind="source_audit_boundary", limits=["No Lean check_data implementation or theorem connects private construction to the Rust debug assertion.", "Prebuilt rustc library debug-assert configuration is outside this comparison."])
    scalar("scalar_int.null", 231, "ScalarInt::null", "ScalarInt::null", ["Miri.Memory.ScalarInt.null"],
        "Construct zero at selected widths; compare zero-width source panic with explicit Lean error.", "pinned_api_behavior_observed", ["P zero_size"],
        "One zero-width panic/error case; other calls construct fixtures.", rows=1,
        limits=SCALAR_LIMITS+["Lean rejects widths above 16; this is tested only against Lean expectations, not pinned source."])
    scalar("scalar_int.try_from_uint", 241, "ScalarInt::try_from_uint", "ScalarInt::try_from_uint", ["Miri.Memory.ScalarInt.tryFromUInt"],
        "Return a scalar only if conversion to the requested width loses no bits.", "pinned_api_behavior_observed", ["U"], "Six selected unsigned construction outputs.", rows=6,
        limits=SCALAR_LIMITS+["Only six selected unsigned inputs are compared."])
    scalar("scalar_int.truncate_from_uint", 247, "ScalarInt::truncate_from_uint", "ScalarInt::truncate_from_uint", ["Miri.Memory.ScalarInt.truncateFromUInt"],
        "Return low bits and truncation flag for selected unsigned values.", "pinned_api_behavior_observed", ["T"], "Two selected unsigned truncation outputs.", rows=2,
        limits=SCALAR_LIMITS+["Only two selected unsigned truncation inputs are compared."])
    scalar("scalar_int.try_from_int", 255, "ScalarInt::try_from_int", "ScalarInt::try_from_int", ["Miri.Memory.ScalarInt.tryFromInt"],
        "Return a scalar only when signed conversion preserves the value.", "pinned_api_behavior_observed", ["I"], "Five selected signed constructor outputs.", rows=5,
        limits=SCALAR_LIMITS+["Rust accepts i128 only. Lean additionally rejects arbitrary Int outside i128; that check is not source-compared."])
    scalar("scalar_int.truncate_from_int", 261, "ScalarInt::truncate_from_int", "ScalarInt::truncate_from_int", ["Miri.Memory.ScalarInt.truncateFromInt"],
        "Return selected truncated two’s-complement bits and signed truncation flags.", "pinned_api_behavior_observed", ["J"], "Two selected signed truncation outputs.", rows=2,
        limits=SCALAR_LIMITS+["Only two selected signed truncations are compared."])
    scalar("scalar_int.to_bits", 275, "ScalarInt::to_bits", "ScalarInt::to_bits", ["Miri.Memory.ScalarInt.toBits"],
        "Require expected width; compare one wrong-width panic with Lean’s explicit error.", "pinned_api_behavior_observed", ["P mismatch"], "One direct size mismatch output.", rows=1)
    scalar("scalar_int.to_bits_unchecked_reporting", 292, "ScalarInt::to_bits_unchecked", "ScalarInt::to_bits_unchecked", ["Miri.Memory.ScalarInt.toBitsUnchecked"],
        "Used to serialize source ScalarInt payload bits; no standalone behavior claim.", "reviewed_reporting_adapter", ["U", "T", "I", "J"],
        "show_int uses this method to render constructor results.", kind="adapter_reporting", limits=["This is an output-serialization dependency, not a standalone behavior test.", "Source check_data is debug-only and separately recorded as unmapped."])
    scalar("scalar_int.to_uint", 299, "ScalarInt::to_uint", "ScalarInt::to_uint", ["Miri.Memory.ScalarInt.toUInt"],
        "Size-checked decode reached underneath the separate Scalar API.", "reviewed_indirect_observation", ["S from_uint", "S addr_cast", "S to_pointer"],
        "Scalar wrapper outputs include ScalarInt conversion plus surrounding Scalar behavior.",
        limits=["These outputs do not isolate ScalarInt::to_uint from the Scalar layer.", "No standalone ScalarInt unsigned-decode matrix is included."])
    scalar("scalar_int.to_u8", 306, "ScalarInt::to_u8", "ScalarInt::to_u8", ["Miri.Memory.ScalarInt.toUInt8"],
        "Width-specific u8 conversion used by try_to_bool and Scalar::to_bool.", "reviewed_indirect_observation", ["Q bool_true", "Q bool_invalid", "S bool"],
        "Reached by two direct try_to_bool outputs and one Scalar wrapper output.", rows=3,
        limits=["The width conversion is observed through parent APIs rather than a standalone to_u8 matrix."])
    scalar("scalar_int.to_u32", 320, "ScalarInt::to_u32", "ScalarInt::to_u32", ["Miri.Memory.ScalarInt.toUInt32"],
        "Width-specific u32 conversion used by character, atomic-ordering, and SIMD-alignment conversions.", "reviewed_indirect_observation", ["C", "E atomic", "E simd"],
        "Reached by three character, one atomic-ordering, and one SIMD-alignment output.", rows=5,
        limits=["Only five selected values reach this conversion path."])
    scalar("scalar_int.try_to_bool", 380, "ScalarInt::try_to_bool", "ScalarInt::try_to_bool", ["Miri.Memory.ScalarInt.tryToBool"],
        "Accept 0/1 at byte width and reject one selected invalid representation.", "pinned_api_behavior_observed", ["Q bool_true", "Q bool_invalid"],
        "Two direct ScalarInt API outputs; distinct from Scalar::to_bool.", rows=2,
        limits=SCALAR_LIMITS+["Scalar::to_bool is a separate UB-producing wrapper and is outside this source method row."])
    scalar("scalar_int.to_int", 392, "ScalarInt::to_int", "ScalarInt::to_int", ["Miri.Memory.ScalarInt.toInt"],
        "Signed decode reached underneath Scalar::to_int.", "reviewed_indirect_observation", ["S signed"],
        "One Scalar wrapper output includes the conversion path.", rows=1,
        limits=["The observed output includes the surrounding Scalar layer; no standalone ScalarInt::to_int matrix is run."])
    scalar("scalar_int.from_char", 506, "From<char> for ScalarInt::from", "From < char > for ScalarInt::from", ["Miri.Memory.ScalarInt.ofChar"],
        "Character construction reached through Scalar::from_char.", "reviewed_indirect_observation", ["S char"],
        "One Scalar construction/decode output.", rows=1,
        limits=["The output is a Scalar fixture and does not isolate this From<char> implementation."])
    scalar("scalar_int.to_atomic_ordering", 346, "ScalarInt::to_atomic_ordering", "ScalarInt::to_atomic_ordering", ["Miri.Memory.ScalarInt.toAtomicOrdering"],
        "Decode one valid AcqRel representation.", "pinned_api_behavior_observed", ["E atomic"], "One valid enum output; invalid value is only checked in LeanTests.", rows=1,
        limits=SCALAR_LIMITS+["Invalid enum behavior is not source-differentially tested."])
    scalar("scalar_int.to_simd_alignment", 365, "ScalarInt::to_simd_alignment", "ScalarInt::to_simd_alignment", ["Miri.Memory.ScalarInt.toSimdAlignment"],
        "Decode one valid Vector SIMD alignment representation.", "pinned_api_behavior_observed", ["E simd"], "One valid enum output; invalid value is only checked in LeanTests.", rows=1,
        limits=SCALAR_LIMITS+["Invalid enum behavior is not source-differentially tested."])
    scalar("scalar_int.try_from_char", 562, "TryFrom<ScalarInt> for char::try_from", "TryFrom < ScalarInt > for char::try_from", ["Miri.Memory.ScalarInt.toChar"],
        "Decode valid ASCII and reject selected surrogate/out-of-range u32 values.", "pinned_api_behavior_observed", ["C"], "Three direct character conversion outputs.", rows=3)

    # Tree Borrows permission methods and per-node transition functions.
    def tree(eid, line, display, needle, lean, claim, disp, selectors, n, *, proofs=None,
             features=None, kind="byte_exact_body_differential", limits=None):
        add("tree_permissions", eid, PERMS, line, display, needle, lean, claim, disp,
            kind, TREE_TESTS, "Tree suite has 2,302 function-output observations overall; selectors/count identify permission cases only. A separate retag-caller order check is static source analysis, not an output row.",
            extracted=True, selectors=selectors, rows=n, proofs=proofs, features=features, limits=limits or TREE_LIMITS)
    tree("tree_permissions.partial_order", 59, "PartialOrd for PermissionPriv::partial_cmp", "partial_cmp",
        ["Miri.TreeBorrows.permissionLE", "Miri.TreeBorrows.permissionCompare"],
        "Permission reachability relation including all 49 pairs in the seven-state universe.", "body_extracted_and_differentialed", ["compare"], 49,
        proofs=["Miri.TreeBorrows.PermTransition.isPossible"])
    tree("tree_permissions.private_initial_predicate", 92, "PermissionPriv::is_initial", "PermissionPriv::is_initial",
        ["Miri.TreeBorrows.Permission.isInitial"], "Private initial predicate reached by public wrapper for each fixture state.",
        "body_extracted_and_differentialed", ["meta"], 7, limits=TREE_LIMITS+["The harness observes the public wrapper rather than separately calling this helper."])
    tree("tree_permissions.public_initial_predicate", 250, "Permission::is_initial", "Permission::is_initial",
        ["Miri.TreeBorrows.Permission.isInitial"], "Public initial predicate over seven fixture states.", "body_extracted_and_differentialed", ["meta"], 7)
    tree("tree_permissions.private_foreign_idempotence", 106, "PermissionPriv::strongest_idempotent_foreign_access", "PermissionPriv::strongest_idempotent_foreign_access",
        ["Miri.TreeBorrows.Permission.strongestIdempotentForeignAccess"], "Private idempotence branch reached through the public query.",
        "body_extracted_and_differentialed", ["strong"], 14, limits=TREE_LIMITS+["The helper is called through the public wrapper, not independently."])
    for eid,line,name,lean,feature in [
        ("tree_permissions.child_read",137,"transition::child_read","Miri.TreeBorrows.childRead","tree_borrows.permission.child_read"),
        ("tree_permissions.foreign_read",147,"transition::foreign_read","Miri.TreeBorrows.foreignRead","tree_borrows.permission.foreign_read"),
        ("tree_permissions.child_write",184,"transition::child_write","Miri.TreeBorrows.childWrite","tree_borrows.permission.child_write"),
        ("tree_permissions.foreign_write",201,"transition::foreign_write","Miri.TreeBorrows.foreignWrite","tree_borrows.permission.foreign_write")]:
        tree(eid,line,name,name,[lean],"Per-node rule reached in the seven-state × access-kind × relation × protector dispatcher sweep.",
             "body_extracted_and_differentialed",["transition"],56,features=[feature],
             limits=TREE_LIMITS+["The 56 matrix rows are shared across all four helper functions, not 56 calls to each helper."])
    tree("tree_permissions.transition_dispatch",219,"transition::perform_access","transition::perform_access",
        ["Miri.TreeBorrows.performAccess"],"Four-way dispatcher over seven states, two kinds, local/foreign relations, and both protector flags.",
        "body_extracted_and_differentialed",["transition"],56,features=["tree_borrows.permission.perform_access"],
        proofs=["Miri.TreeBorrows.cell_is_unchanged","Miri.TreeBorrows.successful_transition_is_monotone","Miri.TreeBorrows.valid_protector_avoids_invariant_failure"],
        limits=TREE_LIMITS+["Lean theorems are properties of Lean definitions; none proves equivalence to Rust."])
    constructors=[
        ("tree_permissions.new_unique",273,"Permission::new_unique","Permission::new_unique","Miri.TreeBorrows.Permission.Unique"),
        ("tree_permissions.new_reserved_frz",278,"Permission::new_reserved_frz","Permission::new_reserved_frz","Miri.TreeBorrows.Permission.ReservedFrz"),
        ("tree_permissions.new_reserved_im",283,"Permission::new_reserved_im","Permission::new_reserved_im","Miri.TreeBorrows.Permission.ReservedIM"),
        ("tree_permissions.new_frozen",288,"Permission::new_frozen","Permission::new_frozen","Miri.TreeBorrows.Permission.Frozen"),
        ("tree_permissions.new_disabled",293,"Permission::new_disabled","Permission::new_disabled","Miri.TreeBorrows.Permission.Disabled"),
        ("tree_permissions.new_cell",299,"Permission::new_cell","Permission::new_cell","Miri.TreeBorrows.Permission.Cell"),
    ]
    for eid,line,display,needle,lean in constructors:
        tree(eid,line,display,needle,[lean],"Source constructor supplies one of seven fixture states represented by the matching Lean constructor.",
             "fixture_construction_mapping",["meta","strong","compare","replace","transition"],175,
             kind="finite_source_differential",limits=TREE_LIMITS+["Fixture-state correspondence only; constructors are not isolated tests."])
    predicates=[
        ("tree_permissions.is_disabled",254,"Permission::is_disabled","Miri.TreeBorrows.Permission.isDisabled"),
        ("tree_permissions.is_frozen",258,"Permission::is_frozen","Miri.TreeBorrows.Permission.isFrozen"),
        ("tree_permissions.is_cell",263,"Permission::is_cell","Miri.TreeBorrows.Permission.isCell"),
        ("tree_permissions.is_unique",268,"Permission::is_unique","Miri.TreeBorrows.Permission.isUnique"),
    ]
    for eid,line,name,lean in predicates:
        tree(eid,line,name,name,[lean],"Public predicate result over seven fixture permission states.","body_extracted_and_differentialed",["meta"],7)
    tree("tree_permissions.associated_access",310,"Permission::associated_access","Permission::associated_access",
        ["Miri.TreeBorrows.Permission.associatedAccess"],"Associated access kind reported for each permission fixture.","body_extracted_and_differentialed",["meta"],7)
    tree("tree_permissions.public_perform_access",321,"Permission::perform_access","Permission::perform_access",
        ["Miri.TreeBorrows.performAccessTransition","Miri.TreeBorrows.PermTransition"],"Public wrapper returns transition, UB, or invariant-failure outcomes.",
        "body_extracted_and_differentialed",["transition"],56,features=["tree_borrows.permission.perform_access"],
        proofs=["Miri.TreeBorrows.reserved_local_write_activates"],
        limits=TREE_LIMITS+["The matrix covers permission transitions, not caller tree traversal or diagnostics."])
    tree("tree_permissions.can_be_replaced_by_child",333,"Permission::can_be_replaced_by_child","Permission::can_be_replaced_by_child",
        ["Miri.TreeBorrows.Permission.canBeReplacedByChild"],"Replacement result for all 49 parent/child pairs.","body_extracted_and_differentialed",["replace"],49,
        proofs=["Miri.TreeBorrows.can_replace_permission_by_itself"])
    tree("tree_permissions.public_foreign_idempotence",373,"Permission::strongest_idempotent_foreign_access","Permission::strongest_idempotent_foreign_access",
        ["Miri.TreeBorrows.Permission.strongestIdempotentForeignAccess"],"Idempotent foreign access result for each permission and protector flag.","body_extracted_and_differentialed",["strong"],14,
        proofs=["Miri.TreeBorrows.sifa_read_is_stable","Miri.TreeBorrows.sifa_write_is_stable"])
    tree("tree_permissions.strongest_local_access",380,"Permission::strongest_allowed_local_access","Permission::strongest_allowed_local_access",
        ["Miri.TreeBorrows.Permission.strongestAllowedLocalAccess"],"Strongest local access summary for each permission and protector flag.","body_extracted_and_differentialed",["strong"],14,
        proofs=["Miri.TreeBorrows.strongest_local_access_matches_transition"])
    transition_methods=[
        ("tree_permissions.transition_is_possible",399,"PermTransition::is_possible","Miri.TreeBorrows.PermTransition.isPossible",None),
        ("tree_permissions.transition_is_noop",407,"PermTransition::is_noop","Miri.TreeBorrows.PermTransition.isNoop",None),
        ("tree_permissions.transition_applied",411,"PermTransition::applied","Miri.TreeBorrows.PermTransition.applied",["Miri.TreeBorrows.transition_applied_at_source"]),
        ("tree_permissions.transition_produces_disabled",416,"PermTransition::produces_disabled","Miri.TreeBorrows.PermTransition.producesDisabled",None),
    ]
    for eid,line,name,lean,proof in transition_methods:
        tree(eid,line,name,name,[lean],"Transition metadata included for successful dispatcher outputs.","body_extracted_and_differentialed",["transition"],56,
             proofs=proof,limits=TREE_LIMITS+["These helpers are evaluated only for successful transitions; not every matrix case produces one."])
    tree("tree_permissions.transition_endpoint_adapter",614,"PermTransition::endpoint","PermTransition::endpoint",
        ["Miri.TreeBorrows.PermTransition.endpoint"],"Test adapter reads a successful transition endpoint to format the differential output.",
        "reviewed_test_adapter_boundary",["transition"],56,kind="finite_source_differential",
        limits=TREE_LIMITS+["This method is in diagnostics and is used by the test adapter; diagnostics are not ported by this row."])

    ledger = {
        "schema_version": 1,
        "source_lock_sha256": inventory["source_lock"]["sha256"],
        "purpose": "Reviewed granular Rust AST function/method to Lean definition and evidence mappings. Every row is a selected slice, never a whole-function completion claim.",
        "counting_policy": {
            "denominator": "All syn-indexed Rust function/method symbols in each named source file.",
            "reviewed": "A source symbol with an explicit row, including adapter-only, indirectly observed, and unmapped-boundary dispositions.",
            "unreviewed": "A candidate AST function/method in a named source file with no row; the checker reports its ID.",
            "percentage": "No repository-wide denominator or completion percentage is computed; module/file inventory is separate.",
        },
        "scopes": [
            {"id": "integer_ops", "description": "Selected integer/bool/char branches in rustc operator.rs; other operators and dispatch are unreviewed.", "source_paths": [OP]},
            {"id": "scalar_int", "description": "Selected ScalarInt constructors/conversions in rustc_middle int.rs; Scalar and Allocation behavior are outside this scope.", "source_paths": [SCALAR]},
            {"id": "tree_permissions", "description": "Selected per-permission functions in Miri perms.rs; diagnostics, optimization helpers, and other unentered functions remain pending.", "source_paths": [PERMS]},
        ],
        "entries": entries,
    }
    destination = ROOT / "tracking/implementation-ledger.json"
    rendered = json.dumps(ledger, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not destination.exists() or destination.read_text(encoding="utf-8") != rendered:
            print("implementation ledger is stale; run python3 tools/update_implementation_ledger.py")
            return 1
        print(f"implementation ledger is current ({len(entries)} mapped AST symbols)")
        return 0
    destination.write_text(rendered, encoding="utf-8")
    print(f"wrote {len(entries)} granular mappings to {destination.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
