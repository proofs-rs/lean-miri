"""Strict schema-13 coroutine wire shapes; Lean validates compiler relationships.

Auxiliary bodies retain their owner/role identity and never join callable bodies.
These inspection checks do not establish compiler authenticity or guest safety.
"""


def _record(value, keys, label):
    if not isinstance(value, dict) or set(value) != set(keys.split()):
        raise ValueError(f"{label}: expected exactly {keys}")


def _reference(value, count, label):
    if type(value) is not int or not 0 <= value < count:
        raise ValueError(f"{label}: dangling reference")


def validate_catalog(document):
    catalog = document.get("compiler_coroutine_coverage")
    _record(catalog, "body_coroutines coroutines auxiliary_bodies", "coroutine catalog")
    markers = catalog["body_coroutines"]
    if not isinstance(markers, list) or len(markers) != len(document["bodies"]) or any(type(flag) is not bool for flag in markers):
        raise ValueError("coroutine catalog: incomplete or invalid body markers")
    for name in ("coroutines", "auxiliary_bodies"):
        if not isinstance(catalog[name], list):
            raise ValueError(f"coroutine catalog: {name} must be an array")
    owners, used = set(), set()
    for row in catalog["coroutines"]:
        _record(row, "owner_body coroutine_type coroutine_kind yield_type resume_type layout drop_sync drop_async drop_proxy_async", "coroutine witness")
        owner = row["owner_body"]
        _reference(owner, len(markers), "coroutine owner")
        if owner in owners or not markers[owner]:
            raise ValueError("coroutine catalog: duplicate owner or missing marker")
        owners.add(owner)
        _reference(row["coroutine_type"], len(document["types"]), "coroutine type")
        kind = row["coroutine_kind"]
        if not isinstance(kind, dict):
            raise ValueError("coroutine kind must be an object")
        if kind.get("kind") == "coroutine":
            _record(kind, "kind movability", "coroutine kind")
            if kind["movability"] not in ("static", "movable"):
                raise ValueError("unknown coroutine movability")
        elif kind.get("kind") == "desugared":
            _record(kind, "kind desugaring source", "coroutine kind")
            if kind["desugaring"] not in ("async", "gen", "async_gen") or kind["source"] not in ("block", "closure", "function"):
                raise ValueError("unknown coroutine desugaring/source")
        else:
            raise ValueError("unknown coroutine kind")
        if row["yield_type"] is not None or row["resume_type"] is not None:
            raise ValueError("unlowered coroutine yield/resume types")
        layout = row["layout"]
        _record(layout, "field_tys variant_fields variant_source_info storage_conflicts", "coroutine layout")
        if any(not isinstance(layout[key], list) for key in layout):
            raise ValueError("coroutine layout members must be arrays")
        fields = layout["field_tys"]
        for field in fields:
            _record(field, "type source_info ignore_for_traits debuginfo_name", "coroutine saved field")
            _reference(field["type"], len(document["types"]), "saved field type")
            _reference(field["source_info"], len(document["source_infos"]), "saved field source info")
            if type(field["ignore_for_traits"]) is not bool or field["debuginfo_name"] is not None and not isinstance(field["debuginfo_name"], str):
                raise ValueError("invalid saved field flags/name")
        if len(layout["variant_fields"]) < 3 or len(layout["variant_fields"]) != len(layout["variant_source_info"]) or len(fields) != len(layout["storage_conflicts"]):
            raise ValueError("coroutine layout dimensions disagree")
        for source in layout["variant_source_info"]:
            _record(source, "span scope", "coroutine variant source")
            _reference(source["span"], len(document["spans"]), "variant span")
            _reference(source["scope"], len(document["bodies"][owner]["source_scopes"]), "variant scope")
        for indices in layout["variant_fields"] + layout["storage_conflicts"]:
            if not isinstance(indices, list):
                raise ValueError("coroutine layout index row must be an array")
            for index in indices:
                _reference(index, len(fields), "saved field index")
            if len(set(indices)) != len(indices):
                raise ValueError("duplicate saved field index")
        sync, async_, proxy = (row[key] for key in ("drop_sync", "drop_async", "drop_proxy_async"))
        if (sync is None) == (async_ is None) or (proxy is None) != (sync is None):
            raise ValueError("inconsistent coroutine drop roles")
        for reference, role in ((sync, "sync"), (async_, "async"), (proxy, "proxy_async")):
            if reference is None:
                continue
            _reference(reference, len(catalog["auxiliary_bodies"]), "auxiliary body")
            auxiliary = catalog["auxiliary_bodies"][reference]
            _record(auxiliary, "owner_body role source_kind body", "coroutine auxiliary")
            if reference in used or auxiliary["owner_body"] != owner or auxiliary["role"] != role or not isinstance(auxiliary["body"], dict):
                raise ValueError("mismatched/duplicate auxiliary owner or role")
            _reference(auxiliary["owner_body"], len(markers), "auxiliary owner")
            body = auxiliary["body"]
            owner_body = document["bodies"][owner]
            _reference(body.get("instance_id"), len(document["instances"]), "auxiliary normalization instance")
            _reference(body.get("source_def_id"), len(document["definitions"]), "auxiliary source definition")
            if body["instance_id"] != owner_body["instance_id"]:
                raise ValueError("auxiliary normalization context differs from owner")
            source_kind = auxiliary["source_kind"]
            if not isinstance(source_kind, dict):
                raise ValueError("auxiliary source kind must be an object")
            if source_kind.get("kind") == "item":
                _record(source_kind, "kind def_id", "auxiliary source kind")
            elif source_kind.get("kind") == "shim" and source_kind.get("shim_kind") == "drop_glue":
                _record(source_kind, "kind shim_kind def_id drop_type", "auxiliary source kind")
                _reference(source_kind["drop_type"], len(document["types"]), "drop source type")
            elif source_kind.get("kind") == "shim" and source_kind.get("shim_kind") == "async_drop_glue":
                _record(source_kind, "kind shim_kind def_id coroutine_type", "auxiliary source kind")
                _reference(source_kind["coroutine_type"], len(document["types"]), "async drop source type")
            else:
                raise ValueError("unknown auxiliary source kind")
            _reference(source_kind["def_id"], len(document["definitions"]), "auxiliary source definition")
            if source_kind["def_id"] != body["source_def_id"]:
                raise ValueError("auxiliary source kind differs from body definition")
            phase = body.get("phase")
            _record(phase, "kind phase", "auxiliary snapshot phase")
            valid_phase = (phase["kind"], phase["phase"]) == ("runtime", "initial")
            if role != "sync":
                valid_phase |= (phase["kind"], phase["phase"]) == ("analysis", "post_cleanup")
            if not valid_phase:
                raise ValueError("unexpected auxiliary snapshot phase")
            used.add(reference)
    if owners != {index for index, flag in enumerate(markers) if flag} or len(used) != len(catalog["auxiliary_bodies"]):
        raise ValueError("coroutine catalog: missing witness or orphan auxiliary body")
