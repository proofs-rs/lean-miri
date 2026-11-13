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


def _natural(value, label, bound=None):
    if type(value) is not int or value < 0 or bound is not None and value >= bound:
        raise ValueError(f"{label}: invalid natural")


def _identity(value, label):
    _record(value, "crate index", label)
    for part in value.values():
        _natural(part, label, 2**32)
    return value["crate"], value["index"]


def _bound_identity(value):
    if not isinstance(value, dict):
        raise ValueError("generic bound identity must be an object")
    kind = value.get("kind")
    if kind in ("anonymous", "closure_environment"):
        _record(value, "kind", "generic bound identity")
    elif kind == "named":
        _record(value, "kind definition", "generic bound identity")
        _identity(value["definition"], "generic bound definition")
    elif kind == "named_for_printing":
        _record(value, "kind name", "generic bound identity")
        if not isinstance(value["name"], str):
            raise ValueError("generic bound name must be a string")
    else:
        raise ValueError("unknown generic bound identity")


def _term(value, parameters, fuel=256):
    if fuel <= 0 or not isinstance(value, dict):
        raise ValueError("generic source term malformed or depth exhausted")
    kind = value.get("kind")
    if kind == "binder":
        _record(value, "kind variables value", "generic binder")
        if not isinstance(value["variables"], list):
            raise ValueError("generic binder variables must be an array")
        for variable in value["variables"]:
            if not isinstance(variable, dict) or variable.get("kind") not in ("type", "region", "constant"):
                raise ValueError("invalid generic binder variable")
            _record(variable, "kind" if variable["kind"] == "constant" else "kind identity", "generic binder variable")
            if variable["kind"] != "constant":
                _bound_identity(variable["identity"])
        return _term(value["value"], parameters, fuel - 1)
    sort = value.get("sort")
    if sort not in ("type", "region", "constant", "aggregate"):
        raise ValueError("unknown generic source term sort")
    if kind == "parameter":
        _record(value, "kind sort index", "generic parameter")
        _reference(value["index"], len(parameters), "generic parameter")
        if parameters[value["index"]] != sort:
            raise ValueError("generic parameter sort mismatch")
    elif kind == "bound":
        _record(value, "kind sort index variable identity", "generic bound term")
        if value["index"] is not None:
            _natural(value["index"], "generic deBruijn index", 2**32)
        _natural(value["variable"], "generic bound variable", 2**32)
        _bound_identity(value["identity"])
    elif kind in ("placeholder", "inference"):
        raise ValueError("unresolved generic source term")
    elif kind in ("atom", "node", "definition"):
        keys = "kind sort tag " + ("definition" if kind == "definition" else "payload")
        if kind != "atom":
            keys += " children"
        _record(value, keys, "generic constructor")
        if not isinstance(value["tag"], str) or kind != "definition" and not isinstance(value["payload"], str):
            raise ValueError("generic constructor tag/payload must be strings")
        if kind == "definition":
            _identity(value["definition"], "generic constructor definition")
        if kind != "atom":
            if not isinstance(value["children"], list):
                raise ValueError("generic children must be an array")
            for child in value["children"]:
                _term(child, parameters, fuel - 1)
    else:
        raise ValueError("unknown generic source term kind")
    return sort


def _layout(document, layout, child, scope_count=None):
    _record(layout, "field_tys variant_fields variant_source_info storage_conflicts", "coroutine layout")
    if any(not isinstance(layout[key], list) for key in layout):
        raise ValueError("coroutine layout members must be arrays")
    fields = layout["field_tys"]
    for field in fields:
        _record(field, "type source_info ignore_for_traits debuginfo_name", "coroutine saved field")
        child(field["type"])
        _reference(field["source_info"], len(document["source_infos"]), "saved field source info")
        if type(field["ignore_for_traits"]) is not bool or field["debuginfo_name"] is not None and not isinstance(field["debuginfo_name"], str):
            raise ValueError("invalid saved field flags/name")
    if len(layout["variant_fields"]) < 3 or len(layout["variant_fields"]) != len(layout["variant_source_info"]) or len(fields) != len(layout["storage_conflicts"]):
        raise ValueError("coroutine layout dimensions disagree")
    for source in layout["variant_source_info"]:
        _record(source, "span scope", "coroutine variant source")
        _reference(source["span"], len(document["spans"]), "variant span")
        if scope_count is None:
            _natural(source["scope"], "variant scope")
        else:
            _reference(source["scope"], scope_count, "variant scope")
    for indices in layout["variant_fields"] + layout["storage_conflicts"]:
        if not isinstance(indices, list):
            raise ValueError("coroutine layout index row must be an array")
        for index in indices:
            _reference(index, len(fields), "saved field index")
        if len(set(indices)) != len(indices):
            raise ValueError("duplicate saved field index")


def _generic_sources(document, sources):
    if not isinstance(sources, list):
        raise ValueError("coroutine catalog: generic_sources must be an array")
    registered = {(row["crate"], row["index"]) for row in document["definitions"]}
    seen, groups = set(), {}
    for row in sources:
        _record(row, "owner physical_owner typeck_owner parent_count parameters witness_parameters type_expression identity_kind by_move_owner layout", "coroutine generic source")
        identities = [_identity(row[key], "coroutine generic owner") for key in ("owner", "physical_owner", "typeck_owner")]
        if row["by_move_owner"] is not None:
            identities.append(_identity(row["by_move_owner"], "coroutine by-move owner"))
        if any(identity not in registered for identity in identities):
            raise ValueError("coroutine generic source: declaration identity absent")
        owner, physical, _ = identities[:3]
        if (owner, physical) in seen:
            raise ValueError("coroutine generic source: duplicate physical owner")
        seen.add((owner, physical))
        parameters, witness = row["parameters"], row["witness_parameters"]
        if any(not isinstance(values, list) or any(sort not in ("type", "region", "constant") for sort in values) for values in (parameters, witness)):
            raise ValueError("coroutine generic source: invalid parameter sorts")
        parent = row["parent_count"]
        _natural(parent, "coroutine parent count")
        if len(parameters) != parent + 5 or parameters[parent:] != ["type"] * 5:
            raise ValueError("coroutine generic source: synthetic argument domain mismatch")
        if len(witness) > parent or parameters[:len(witness)] != witness:
            raise ValueError("coroutine generic source: witness/typeck prefix mismatch")
        expression = row["type_expression"]
        _term(expression, parameters)
        if expression.get("kind") != "definition" or expression["sort"] != "type" or expression["tag"] != "coroutine" or expression["definition"] != row["owner"]:
            raise ValueError("coroutine generic source: declaration owner/constructor mismatch")
        arguments = expression["children"]
        if len(arguments) != len(parameters) or [_term(arg, parameters) for arg in arguments] != parameters:
            raise ValueError("coroutine generic source: declaration argument domain mismatch")
        kind = row["identity_kind"]
        if kind != arguments[parent]:
            raise ValueError("coroutine generic source: identity kind differs")
        regular = {"kind": "node", "sort": "type", "tag": "tuple", "payload": "", "children": []}
        closure = kind.get("payload") if kind.get("kind") == "atom" and kind.get("sort") == "type" and kind.get("tag") == "int" else None
        if kind != regular and closure not in ("i8", "i16", "i32"):
            raise ValueError("coroutine generic source: unknown body kind")
        moved = row["by_move_owner"]
        if moved is not None and (moved == row["owner"] or closure not in ("i8", "i16")):
            raise ValueError("coroutine generic source: invalid by-move owner")
        if row["physical_owner"] != row["owner"] and row["physical_owner"] != moved:
            raise ValueError("coroutine generic source: unrelated physical owner")
        def child(value):
            if _term(value, parameters) != "type":
                raise ValueError("coroutine generic source: saved field is not a type")
        _layout(document, row["layout"], child)
        groups.setdefault(owner, []).append(row)
    for rows in groups.values():
        first = rows[0]
        header = {key: value for key, value in first.items() if key not in ("physical_owner", "layout")}
        if any({key: value for key, value in row.items() if key not in ("physical_owner", "layout")} != header for row in rows):
            raise ValueError("coroutine generic source: inconsistent logical owner")
        for required in (first["owner"], first["by_move_owner"]):
            if required is not None and not any(row["physical_owner"] == required for row in rows):
                raise ValueError("coroutine generic source: physical owner missing")


def validate_catalog(document):
    catalog = document.get("compiler_coroutine_coverage")
    _record(catalog, "body_coroutines coroutines auxiliary_bodies generic_sources", "coroutine catalog")
    _generic_sources(document, catalog["generic_sources"])
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
        _layout(document, row["layout"],
                lambda value: _reference(value, len(document["types"]), "saved field type"),
                len(document["bodies"][owner]["source_scopes"]))
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
