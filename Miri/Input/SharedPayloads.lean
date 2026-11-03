import Lean
import Miri.Input.AbiWire

/-! Shared JSON payload graph transport. Nodes are resolved once in topological
order, and resolved Json values are reused directly at every reference site. -/
namespace Miri.Input.SharedPayloads

open Lean

private def markerKey : String := "$lean_miri_shared_ref"

private def pathKey (path key : String) : String :=
  if path.isEmpty then key else path ++ "." ++ key

private def objectFields (value : Json) : Except String (Array (String × Json)) := do
  match value with
  | .obj fields => pure fields.toList.toArray
  | _ => throw "expected object"

private def field (value : Json) (key path : String) : Except String Json := do
  value.getObjVal? key |>.mapError fun error =>
    s!"{path}: missing/invalid field `{key}` ({error})"

private def exactObjectFields (value : Json) (expected : List String)
    (path description : String) : Except String (Array (String × Json)) := do
  let fields ← objectFields value |>.mapError fun _ => s!"{path}: {description} must be an object"
  let names := fields.map Prod.fst
  unless names.size == expected.length && expected.all names.contains do
    throw s!"{path}: {description} has unexpected or missing fields"
  pure fields

/-- Resolved graph output. `nodeResolutionCount` is the number of catalog nodes
processed by the one-pass topological resolver. -/
structure ResolvedGraph where
  nodes : Array Json
  root : Json
  nodeResolutionCount : Nat
  /-- Optional producer summaries. They must be checked against the real graph
  before any decoder uses them to prune a traversal. -/
  scanFlags : Option ByteArray := none
  typedAbi : AbiWire.Table := {}
  deriving Inhabited

private def parseReference (value : Json) (path : String) : Except String Nat := do
  let _ ← exactObjectFields value [markerKey] path "shared reference"
  let descriptor ← field value markerKey path
  let index ← descriptor.getNat? |>.mapError fun error =>
    s!"{pathKey path markerKey}: expected unsigned integer node ID ({error})"
  pure index

private partial def resolveValue (available : Array Json) (totalCount limit : Nat)
    (value : Json) (path : String) : Except String (Option Json) := do
  match value with
  | .obj fields =>
    if AbiWire.hasMarker value then
      throw s!"{path}: typed ABI record is only permitted at a catalog node root"
    if (value.getObjVal? markerKey).isOk then
      let index ← parseReference value path
      if index >= available.size then
        if index >= totalCount then
          throw s!"{pathKey path markerKey}: node reference {index} is out of range"
        else if index >= limit then
          throw s!"{pathKey path markerKey}: node reference {index} is a forward reference"
        else
          throw s!"{pathKey path markerKey}: node reference {index} is out of range"
      match available[index]? with
      | some node => pure (some node)
      | none => throw s!"{pathKey path markerKey}: node reference {index} is out of range"
    else do
      let mut resolved := fields
      let mut changed := false
      for (key, child) in fields.toList do
        if let some replacement ← resolveValue available totalCount limit child (pathKey path key) then
          resolved := resolved.insert key replacement
          changed := true
      if changed then pure (some (.obj resolved)) else pure none
  | .arr values => do
    let mut resolved := #[]
    let mut changed := false
    for h : index in [:values.size] do
      have indexBound : index < values.size := Membership.mem.upper h
      let child := values[index]'indexBound
      match ← resolveValue available totalCount limit child s!"{path}[{index}]" with
      | none =>
        if changed then resolved := resolved.push child
      | some replacement =>
        if !changed then
          resolved := values.extract 0 index
          changed := true
        resolved := resolved.push replacement
    if changed then pure (some (.arr resolved)) else pure none
  | _ => pure none

private def parseCatalog (catalog : Json) : Except String (Array Json × Option ByteArray × Bool) := do
  let withFlags := (catalog.getObjVal? "scan_flags").isOk
  let names := if withFlags then ["schema_version", "nodes", "scan_flags"] else ["schema_version", "nodes"]
  let typed := (catalog.getObjVal? "typed_abi_version").isOk
  let names := if typed then names ++ ["typed_abi_version"] else names
  let _ ← exactObjectFields catalog names "$.shared_payloads" "catalog"
  let version ← field catalog "schema_version" "$.shared_payloads"
  let version ← version.getNat? |>.mapError fun error =>
    s!"$.shared_payloads.schema_version: expected unsigned integer ({error})"
  unless version == 2 do
    throw "$.shared_payloads.schema_version: unsupported shared-payload schema version (expected 2)"
  if typed then
    unless ((← field catalog "typed_abi_version" "$.shared_payloads").getNat?).toOption == some 1 do
      throw "$.shared_payloads.typed_abi_version: expected 1"
  let nodesValue ← field catalog "nodes" "$.shared_payloads"
  let nodes ← nodesValue.getArr? |>.mapError fun error =>
    s!"$.shared_payloads.nodes: expected array ({error})"
  let flags ← if withFlags then do
      let values ← (← field catalog "scan_flags" "$.shared_payloads").getArr?
        |>.mapError fun _ => "$.shared_payloads.scan_flags: expected array"
      unless values.size == nodes.size do
        throw "$.shared_payloads.scan_flags: expected one summary per node"
      let mut flags := ByteArray.empty
      for (value, index) in values.toList.zipIdx do
        let flag ← value.getNat? |>.mapError fun _ =>
          s!"$.shared_payloads.scan_flags[{index}]: expected unsigned integer"
        unless flag < 16 do
          throw s!"$.shared_payloads.scan_flags[{index}]: unknown scan bits"
        flags := flags.push (UInt8.ofNat flag)
      pure (some flags)
    else pure none
  pure (nodes, flags, typed)

/-- Resolve the mandatory v2 shared-payload graph and strip its transport field.
Every node is resolved exactly once in array order; node references can only
point to earlier entries, while document references can point anywhere. -/
def resolveGraph (document : Json) : Except String ResolvedGraph := do
  let fields ← objectFields document |>.mapError fun _ =>
    "$: document must be an object containing shared_payloads"
  if fields.any (fun (key, _) => key == markerKey) then
    throw "$: a shared reference cannot occupy the document root"
  let some catalog := (document.getObjVal? "shared_payloads").toOption
    | throw "$.shared_payloads: missing mandatory shared-payload graph"
  let (rawNodes, scanFlags, typed) ← parseCatalog catalog
  let mut nodes := #[]
  let mut abi : AbiWire.Table := {}
  for (node, index) in rawNodes.toList.zipIdx do
    let nodePath := s!"$.shared_payloads.nodes[{index}]"
    let record ← if typed then AbiWire.parse node nodePath else pure none
    match record with
    | some (.argument arg) =>
      let layout ← resolveValue nodes rawNodes.size index arg.layout s!"{nodePath}.layout"
      let mode ← resolveValue nodes rawNodes.size index arg.mode s!"{nodePath}.mode"
      let arg := { arg with layout := layout.getD arg.layout, mode := mode.getD arg.mode }
      nodes := nodes.push arg.toJson
      abi := { abi with arguments := abi.arguments.insert index arg }
    | some (.function fn) =>
      let arguments ← match fn.argumentVector with
        | none => pure (.arr #[])
        | some id =>
          unless id < index && abi.vectors.contains id do
            throw s!"{nodePath}: function ABI argument vector is absent or not earlier"
          match nodes[id]? with
          | some value => pure value
          | none => throw s!"{nodePath}: function ABI argument vector is absent"
      unless fn.returnId < index && abi.arguments.contains fn.returnId do
        throw s!"{nodePath}: function ABI return argument is absent or not earlier"
      let some returned := nodes[fn.returnId]? | throw s!"{nodePath}: ABI return is absent"
      let convention ← resolveValue nodes rawNodes.size index fn.convention s!"{nodePath}.calling_convention"
      let fn := { fn with convention := convention.getD fn.convention }
      nodes := nodes.push (fn.toJson arguments returned)
      abi := { abi with functions := abi.functions.push fn }
    | none =>
      let resolved ← resolveValue nodes rawNodes.size index node nodePath
      nodes := nodes.push (resolved.getD node)
      if typed then
        if let some ids := AbiWire.argumentVector? abi node then
          abi := { abi with vectors := abi.vectors.insert index ids }
  let mut rootFields := #[]
  for (key, value) in fields do
    if key == "shared_payloads" then continue
    let resolved ← resolveValue nodes nodes.size nodes.size value (pathKey "$" key)
    rootFields := rootFields.push (key, resolved.getD value)
  pure {
    nodes := nodes
    root := Json.mkObj rootFields.toList
    nodeResolutionCount := nodes.size
    scanFlags := scanFlags
    typedAbi := abi
  }

/-- Resolve a shared graph, returning only its business document for decoder
callers that do not need the resolved node table. -/
def resolveCatalog (document : Json) : Except String Json := do
  return (← resolveGraph document).root

end Miri.Input.SharedPayloads
