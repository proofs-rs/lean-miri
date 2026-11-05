"""Expand the normalized world for producer comparisons, not an acceptance gate.

The Lean parser independently checks every reconstructed row and the complete
catalog. Keeping this adapter separate lets the old producer assertions compare
the same facts under both encodings.
"""


def allocation_world_rows(document):
    world = document["compiler_alloc_id_world"]
    if world["schema"] == "rustc_alloc_id_world_v1":
        return world["raw_pool"]
    if world["schema"] != "rustc_alloc_id_world_v2" or "raw_pool" in world:
        raise ValueError("unknown or mixed allocator-world encoding")
    kinds = world["raw_kinds"]
    if type(kinds) is not str or len(kinds) != world["frontier"]["last_reserved_source_alloc_id"]:
        raise ValueError("wrong source prefix length")
    nodes = {}
    for node in document["allocations"]:
        source = node["source_alloc_id"]
        if source in nodes:
            raise ValueError("duplicate source witness")
        nodes[source] = node
    exceptions = {}
    for row in world["opaque_memory"]:
        source = row["source_alloc_id"]
        if (type(source) is not int or not 1 <= source <= len(kinds) or source in exceptions
                or row["kind"] != "memory" or row["status"] != "opaque"):
            raise ValueError("invalid opaque memory projection")
        exceptions[source] = row
    tags = dict(d="dangling", m="memory", f="function", v="vtable", s="static", t="type_id")
    rows = []
    for source, tag in enumerate(kinds, 1):
        if tag not in tags:
            raise ValueError("unknown source kind")
        kind, node = tags[tag], nodes.get(source)
        if source in exceptions:
            if kind != "memory" or node is not None and node["status"] == "supported":
                raise ValueError("redundant or mismatched memory projection")
            rows.append(exceptions[source])
            continue
        row = dict(source_alloc_id=source, kind=kind, allocation_id=None)
        if kind == "dangling":
            row["status"] = "dangling"
        elif node is None or node["status"] != "supported":
            if kind == "memory":
                raise ValueError("missing opaque memory projection")
            row["status"] = "opaque"
            if node is not None:
                row["opaque_allocation_id"] = node["allocation_id"]
        else:
            row.update(status="serialized", allocation_id=node["allocation_id"])
            if kind == "memory":
                initialized = all(r["state"] == "initialized" for r in node["initialization_ranges"])
                provenance = bool(node["relocations"])
                row.update(memory_mutability=node["mutability"], memory_align_bytes=node["align_bytes"],
                           memory_all_bytes_initialized=initialized, memory_has_provenance=provenance)
                if node["mutability"] == "immutable" and node["align_bytes"] == 1 and initialized and not provenance:
                    row["byte_image_hex"] = node["bytes_hex"]
        rows.append(row)
    return rows
