#!/usr/bin/env python3
"""Insert byte-exact helper code from the pinned Miri source into a Rust shim."""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path


EXPECTED = {
    "perms": "0dd4712b85c7d660eb0a4395223335b2b766062b",
    "foreign_access_skipping": "90df05d36d965927eef11a4c1c8387349c87aa44",
    "wildcard": "a3f7d6176555d193163f909fbd48b08118294f8b",
    "tree": "b58a7cfeba92ece2dab1977f65f9070fd8cd71ad",
    "diagnostics": "79c182f5b02a2d9d17b46195908bf28aa31032b3",
    "tree_visitor": "ab3a19ad9e17c7fc3d61d06c93273c7c5a8f7d3e",
    "borrow_tracker": "65660956220eac0d8270b273ac1074454f1c6f75",
    "dedup_range_map": "56e9883b1caaf65a3f769cd5c91fbdbb81547f1b",
    "unimap": "6400a62f444f0a3ec481747e05fa90f2fb1cd40c",
    "tree_borrows_mod": "bf38ca356df45e5f365c0ae64bfe7738a0d43e1e",
}
MARKERS = {
    "perms": "// @PINNED_PERMISSION_IMPLS@",
    "endpoint": "// @PINNED_TRANSITION_ENDPOINT@",
    "foreign_access_skipping": "// @PINNED_FOREIGN_ACCESS_SKIPPING@",
    "wildcard": "// @PINNED_WILDCARD_PERMISSION_HELPERS@",
    "access_kind": "// @PINNED_ACCESS_KIND@",
    "access_relatedness": "// @PINNED_ACCESS_RELATEDNESS@",
    "tree_visitor_body": "// @PINNED_TREE_VISITOR_BODY@",
    "transition_error": "// @PINNED_TRANSITION_ERROR@",
    "location_state_decl": "// @PINNED_LOCATION_STATE_DECL@",
    "location_state_constructors": "// @PINNED_LOCATION_STATE_CONSTRUCTORS@",
    "location_state_access": "// @PINNED_LOCATION_STATE_ACCESS@",
    "location_state_skip_and_record": "// @PINNED_LOCATION_STATE_SKIP_AND_RECORD@",
    "dedup_range_map_body": "// @PINNED_DEDUP_RANGE_MAP_BODY@",
    "location_state_transition": "// @PINNED_LOCATION_STATE_TRANSITION@",
    "node_default_location_state": "// @PINNED_NODE_DEFAULT_LOCATION_STATE@",
    "wildcard_access": "// @PINNED_WILDCARD_ACCESS@",
    "wildcard_level_and_relatedness": "// @PINNED_WILDCARD_LEVEL_AND_RELATEDNESS@",
    "exposed_cache_types": "// @PINNED_EXPOSED_CACHE_TYPES@",
    "access_relatedness_body": "// @PINNED_ACCESS_RELATEDNESS_BODY@",
    "update_exposure_body": "// @PINNED_UPDATE_EXPOSURE_BODY@",
    "location_tree_access": "// @PINNED_LOCATION_TREE_ACCESS@",
    "location_tree_normal_access": "// @PINNED_LOCATION_TREE_NORMAL_ACCESS@",
    "min_exposed_child": "// @PINNED_MIN_EXPOSED_CHILD@",
    "tree_dealloc": "// @PINNED_TREE_DEALLOC@",
    "tree_perform_access": "// @PINNED_TREE_PERFORM_ACCESS@",
    "tree_protector_end_access": "// @PINNED_TREE_PROTECTOR_END_ACCESS@",
    "exposed_cache_remove": "// @PINNED_EXPOSED_CACHE_REMOVE@",
    "tree_gc": "// @PINNED_TREE_GC@",
    "unimap_equality": "// @PINNED_UNIMAP_EQUIVALITY@",
    "tree_expose_tag": "// @PINNED_TREE_EXPOSE_TAG@",
    "tree_protector_release_cache": "// @PINNED_TREE_PROTECTOR_RELEASE_CACHE@",
    "tree_release_protector": "// @PINNED_TREE_RELEASE_PROTECTOR@",
    "tree_visit_provenance": "// @PINNED_TREE_VISIT_PROVENANCE@",
}


def git_blob_sha1(contents: bytes) -> str:
    header = b"blob " + str(len(contents)).encode("ascii") + b"\0"
    return hashlib.sha1(header + contents).hexdigest()


def checked_source(source_path: Path, name: str) -> str:
    source_bytes = source_path.read_bytes()
    actual_blob = git_blob_sha1(source_bytes)
    if actual_blob != EXPECTED[name]:
        raise ValueError(
            f"pinned {name} source blob mismatch: expected {EXPECTED[name]}, got {actual_blob}"
        )
    return source_bytes.decode("utf-8")


def extract(
    perms_path: Path,
    skipping_path: Path,
    wildcard_path: Path,
    tree_path: Path,
    diagnostics_path: Path,
    visitor_path: Path,
    borrow_tracker_path: Path,
    dedup_range_map_path: Path,
    unimap_path: Path,
    tree_borrows_mod_path: Path,
    template_path: Path,
) -> str:
    perms = checked_source(perms_path, "perms")
    skipping = checked_source(skipping_path, "foreign_access_skipping")
    wildcard = checked_source(wildcard_path, "wildcard")
    tree = checked_source(tree_path, "tree")
    diagnostics = checked_source(diagnostics_path, "diagnostics")
    visitor = checked_source(visitor_path, "tree_visitor")
    borrow_tracker = checked_source(borrow_tracker_path, "borrow_tracker")
    dedup_range_map = checked_source(dedup_range_map_path, "dedup_range_map")
    unimap = checked_source(unimap_path, "unimap")
    tree_borrows_mod = checked_source(tree_borrows_mod_path, "tree_borrows_mod")

    def block(source: str, start_marker: str, end_marker: str, *, include_end: bool = False) -> str:
        start = source.index(start_marker)
        end = source.index(end_marker, start)
        if include_end:
            end += len(end_marker)
        return source[start:end].rstrip()

    perms_start = "impl PartialOrd for PermissionPriv {"
    perms_end = "\npub mod diagnostics {"
    start = perms.index(perms_start)
    end = perms.index(perms_end, start)
    permission_impls = perms[start:end].rstrip()

    endpoint_start = "        /// Endpoint of a transition."
    endpoint_end = "\n        }\n    }\n}"
    start = perms.index(endpoint_start)
    end = perms.index(endpoint_end, start) + len("\n        }")
    transition_endpoint = perms[start:end].strip()

    wildcard_start = "/// Represents the maximum access level"
    wildcard_end = "\n/// Where the access happened relative to the current node."
    start = wildcard.index(wildcard_start)
    end = wildcard.index(wildcard_end, start)
    wildcard_helpers = wildcard[start:end].rstrip()

    access_kind = block(
        borrow_tracker,
        "/// Indicates which kind of access is being performed.",
        "\n\nimpl fmt::Display for AccessKind",
    )
    access_relatedness = block(
        tree,
        "#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub enum AccessRelatedness {",
        "\n\nimpl AccessRelatedness",
    ) + "\n\n" + block(
        tree,
        "impl AccessRelatedness {",
        "\n}",
        include_end=True,
    )
    tree_visitor_body = visitor[visitor.index(
        "/// Data given to the transition function"
    ):].rstrip()
    transition_error = block(
        diagnostics,
        "#[derive(Debug, Clone, Copy)]\npub(super) enum TransitionError {",
        "\n}\n\nimpl History",
    ) + "\n}"
    location_state_decl = block(
        tree,
        "/// Data for a reference at single *location*.",
        "\n\nimpl LocationState",
    )
    location_state_constructors = block(
        tree,
        "    /// Constructs a new initial state.",
        "    /// Performs an access on this index",
    )
    location_state_access = block(
        tree,
        "    /// Apply the effect of an access to one location, including",
        "    /// Like `perform_access`, but ignores the concrete error cause",
    )
    location_state_skip_and_record = block(
        tree,
        "    /// Tree traversal optimizations. See `foreign_access_skipping.rs`.",
        "\n}\n\nimpl fmt::Display for LocationState",
    )
    location_state_transition = block(
        tree,
        "    /// Performs an access on this index and updates node,",
        "    /// Apply the effect of an access to one location, including",
    )
    node_default_location_state = block(
        tree,
        "impl Node {\n    pub fn default_location_state(&self) -> LocationState {",
        "\n\nimpl VisitProvenance for Tree",
    )
    wildcard_access_start = tree.index("    fn perform_wildcard_access(")
    wildcard_access_end = tree.index("\n    }\n}\n\nimpl Node {", wildcard_access_start) + len("\n    }")
    wildcard_access = tree[wildcard_access_start:wildcard_access_end].rstrip()
    location_tree_access = block(
        tree,
        "    fn perform_access(\n        &mut self,\n        roots: impl Iterator<Item = UniIndex>,",
        "    /// Performs a normal access on the tree containing `access_source`.",
    )
    location_tree_normal_access = block(
        tree,
        "    fn perform_normal_access(\n        &mut self,\n        access_source: UniIndex,",
        "    /// Performs a wildcard access on the tree with root `root`.",
    )
    min_exposed_child = block(
        tree,
        "    fn get_min_exposed_child(root: UniIndex, nodes: &UniValMap<Node>) -> Option<BorTag> {",
        "    /// Performs an access on this location.",
    )
    tree_dealloc = block(
        tree,
        "    pub fn dealloc(\n        &mut self,\n        prov: ProvenanceExtra,",
        "    /// Map the per-node and per-location `LocationState::perform_access`",
    )
    tree_perform_access = block(
        tree,
        "    pub fn perform_access(\n        &mut self,\n        prov: ProvenanceExtra,",
        "    /// This is the special access that is applied on protector release:",
    )
    tree_protector_end_access_start = tree.index("    pub fn perform_protector_end_access(")
    tree_protector_end_access_end = tree.index(
        "\n    }\n}\n\n/// Integration with the BorTag garbage collector",
        tree_protector_end_access_start,
    ) + len("\n    }")
    tree_protector_end_access = tree[
        tree_protector_end_access_start:tree_protector_end_access_end
    ].rstrip()
    wildcard_level_and_relatedness = block(
        wildcard,
        "/// Where the access happened relative to the current node.",
        "/// Caches information about where in the tree",
    )
    exposed_cache_types = block(
        wildcard,
        "/// Caches information about where in the tree",
        "impl ExposedCache {",
    )
    access_relatedness_body = block(
        wildcard,
        "    pub fn access_relatedness(",
        "    pub fn update_exposure(",
    )
    update_exposure_body = block(
        wildcard,
        "    pub fn update_exposure(",
        "    /// Removes a node from the datastructure.",
    )
    exposed_cache_remove = block(
        wildcard,
        "    /// Removes a node from the datastructure.",
        "\n}",
    )
    tree_gc = block(
        tree,
        "    pub fn remove_unreachable_tags(&mut self, live_tags: &FxHashSet<BorTag>) {",
        "\n}\n\nimpl<'tcx> LocationTree",
    )
    tree_visit_provenance = block(
        tree,
        "    fn visit_provenance(&self, visit: &mut VisitWith<'_>) {",
        "\n}\n\n/// Relative position of the access",
    )
    tree_expose_tag = block(
        wildcard,
        "    pub fn expose_tag(&mut self, tag: BorTag, protected: bool) {",
        "    /// This updates the wildcard tracking data structure to reflect the release",
    )
    tree_protector_release_cache = block(
        wildcard,
        "    pub(super) fn update_exposure_for_protector_release(&mut self, tag: BorTag) {",
        "\n}",
    )
    tree_release_start = tree_borrows_mod.index("    pub fn release_protector(")
    tree_release_end = tree_borrows_mod.index(
        "\n    }\n}\n\n/// Policy for a new borrow.", tree_release_start
    ) + len("\n    }")
    tree_release_protector = tree_borrows_mod[tree_release_start:tree_release_end].rstrip()
    unimap_equality = block(
        unimap,
        "impl<V: PartialEq> UniValMap<V> {",
        "\nimpl<V: PartialEq> PartialEq for UniValMap<V> {",
    ) + "\n\n" + block(
        unimap,
        "impl<V: PartialEq> PartialEq for UniValMap<V> {",
        "\n\nimpl<V> Default for UniValMap",
    )

    template = template_path.read_text(encoding="utf-8")
    extracted = {
        "perms": permission_impls,
        "endpoint": transition_endpoint,
        "foreign_access_skipping": skipping.rstrip(),
        "wildcard": wildcard_helpers,
        "access_kind": access_kind,
        "access_relatedness": access_relatedness,
        "tree_visitor_body": tree_visitor_body,
        "transition_error": transition_error,
        "location_state_decl": location_state_decl,
        "location_state_constructors": location_state_constructors,
        "location_state_access": location_state_access,
        "location_state_skip_and_record": location_state_skip_and_record,
        "dedup_range_map_body": dedup_range_map.rstrip(),
        "location_state_transition": location_state_transition,
        "node_default_location_state": node_default_location_state,
        "wildcard_access": wildcard_access,
        "wildcard_level_and_relatedness": wildcard_level_and_relatedness,
        "exposed_cache_types": exposed_cache_types,
        "access_relatedness_body": access_relatedness_body,
        "update_exposure_body": update_exposure_body,
        "location_tree_access": location_tree_access,
        "location_tree_normal_access": location_tree_normal_access,
        "min_exposed_child": min_exposed_child,
        "tree_dealloc": tree_dealloc,
        "tree_perform_access": tree_perform_access,
        "tree_protector_end_access": tree_protector_end_access,
        "exposed_cache_remove": exposed_cache_remove,
        "tree_gc": tree_gc,
        "unimap_equality": unimap_equality,
        "tree_expose_tag": tree_expose_tag,
        "tree_protector_release_cache": tree_protector_release_cache,
        "tree_release_protector": tree_release_protector,
        "tree_visit_provenance": tree_visit_provenance,
    }
    for name, marker in MARKERS.items():
        if template.count(marker) != 1:
            raise ValueError(f"Rust shim must contain exactly one {name} marker")
        template = template.replace(marker, extracted[name])
    return template


def main() -> None:
    if len(sys.argv) != 13:
        raise SystemExit(
        "usage: extract_reference.py PINNED_PERMS_RS "
            "PINNED_FOREIGN_ACCESS_SKIPPING_RS PINNED_WILDCARD_RS "
            "PINNED_TREE_RS PINNED_DIAGNOSTICS_RS PINNED_TREE_VISITOR_RS "
            "PINNED_BORROW_TRACKER_RS PINNED_DEDUP_RANGE_MAP_RS PINNED_UNIMAP_RS PINNED_TREE_BORROWS_MOD_RS "
            "RUST_TEMPLATE OUTPUT_RS"
        )
    perms, skipping, wildcard, tree, diagnostics, visitor, borrow_tracker, dedup_range_map, unimap, tree_borrows_mod, template, output = map(Path, sys.argv[1:])
    generated = extract(perms, skipping, wildcard, tree, diagnostics, visitor, borrow_tracker, dedup_range_map, unimap, tree_borrows_mod, template)
    output.write_text(generated, encoding="utf-8")
    print("extracted pinned permission, location-state, visitor, range-map, UniValMap equality, wildcard cache/traversal, protector release, deallocation, and tree-GC bodies after Git blob hash checks")


if __name__ == "__main__":
    main()
