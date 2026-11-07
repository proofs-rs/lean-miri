import Miri.Input.Reader.StartupQueries
import Miri.Input.Reader.AllocationFunctions
import Miri.Input.Reader.RetagQueries
import Miri.Input.Reader.AbiQueries
import Miri.Input.Reader.ReferenceBounds
import Miri.Input.Reader.PlaceTypes
import Miri.Input.Reader.CastQueries
import Miri.Input.Reader.Instances
import Miri.Input.Reader.Functions
import Miri.Input.Reader.RuntimeInstances
import Miri.Input.Reader.RuntimeQueries
import Miri.Input.Reader.BodyMetadata
import Miri.Input.Reader.Patterns
import Miri.Input.Reader.SessionMetadata
import Miri.Input.Reader.PanicQueries
import Miri.Input.Reader.NamedGlobals
import Miri.Input.Reader.NamedConstants
import Miri.Input.Reader.MainQueries
import Miri.Input.Reader.ValueConstants
import Miri.Input.Reader.GlobalBytes
import Miri.Input.Reader.ForeignSymbols
import Miri.Input.Reader.ExternStatics

namespace Miri.Input.Reader
open Lean Miri.MIR

private def promotedInputs (catalog : Catalog) (source : Array PromotedBody) (input : Json)
    (path : String) : Except String (Array (Json × BodyCore × String)) := do
  let values ← match ← catalog.optionalField input "promoted_bodies" path with
    | none | some .null => pure #[]
    | some values => catalog.array values path
  unless values.size == source.size do throw s!"{path}: promoted body count mismatch"
  let mut result := #[]
  for (value, index) in values.toList.zipIdx do
    let some child := source[index]? | throw s!"{path}: promoted body absent"
    if let some body := child.body then
      result := result.push (← catalog.field value "body" path, body, s!"{path}.promoted_bodies[{index}].body")
  return result

def Catalog.readMIR (catalog : Catalog) (types : Array TypeNode) (layouts : SharedTable Layout)
    (abiTables : AbiTables) (allocations : Array AllocationNode) (bodies : Array Body) (instances : Array InstanceNode) : Except String (MIRInputTables × AbiQueries) := do
  let allocationCount := allocations.size
  let mut inputs : Array (Json × BodyCore × String) := #[]
  let rawBodies ← catalog.array (← catalog.field catalog.root "bodies" "$") "$.bodies"
  unless rawBodies.size == bodies.size do throw "$.bodies: MIR body count mismatch"
  for (raw, index) in rawBodies.toList.zipIdx do
    let some body := bodies[index]? | throw "$.bodies: MIR body absent"
    let path := s!"$.bodies[{index}]"
    inputs := inputs.push (raw, body.toBodyCore, path)
    inputs := inputs ++ (← promotedInputs catalog body.promotedBodies raw path)
  let rawInstances ← catalog.array (← catalog.field catalog.root "instances" "$") "$.instances"
  unless rawInstances.size == instances.size do throw "$.instances: MIR instance count mismatch"
  for (raw, index) in rawInstances.toList.zipIdx do
    let some row := instances[index]? | throw "$.instances: MIR instance absent"
    if let some body := row.body then
      let path := s!"$.instances[{index}].body"
      let rawBody ← catalog.field raw "body" path
      inputs := inputs.push (rawBody, body.toBodyCore, path)
      if body.promotedBodies.isEmpty then
        inputs := inputs ++ (← promotedInputs catalog row.promotedBodies raw s!"$.instances[{index}]")
      else inputs := inputs ++ (← promotedInputs catalog body.promotedBodies rawBody path)
  let mut definitions := #[]
  let mut seen : Std.HashSet (Nat × Nat) := {}
  for id in inputs.filterMap (fun (_, body, _) => body.definitionId) ++ instances.filterMap (·.definitionId) do
    let key := (id.crateIndex, id.index)
    unless seen.contains key do
      definitions := definitions.push id
      seen := seen.insert key
  -- Allocation graph identities belong to the same canonical definition table.
  -- Preserve all body/instance indices and append graph-only items afterwards.
  for allocation in allocations do
    let definition := match allocation.data with
      | some (.static source) => some source.definitionId
      | some (.function source) => some source.definitionId
      | _ => none
    if let some id := definition then
      let key := (id.crateIndex,id.index)
      unless seen.contains key do
        definitions := definitions.push id
        seen := seen.insert key
  let ctx : ConstantReader.Context := {
    typeCount := types.size
    allocationCount
    scalarSizes := types.map fun node =>
      match layouts.lookup node.layoutId with
      | .ok layout => if layout.status == .supported then layout.sizeBytes else none
      | .error _ => none }
  let mut state := MIRReader.initial catalog.nodes.size {definitions}
  let mut ids := #[]
  for (raw, _, path) in inputs do
    let (id, next) ← (BodyReader.body catalog ctx raw path).run state
    ids := ids.push id
    state := next
  let mut instanceSlots : Array (Option (Except String Miri.Interpreter.CallInstance)) := Array.replicate rawInstances.size none
  for (raw,index) in rawInstances.toList.zipIdx do
    let path := s!"$.instances[{index}]"
    let id ← catalog.natural (← catalog.field raw "instance_id" path) path
    if bound : id < instanceSlots.size then
      unless instanceSlots[id].isNone do throw s!"{path}: duplicate instance ID {id}"
      let result ← match (InstanceReader.read catalog types.size raw path).run state with
        | .ok (value,next) => state := next; pure (.ok value)
        | .error reason => pure (.error reason)
      instanceSlots := instanceSlots.set id (some result) bound
    else throw s!"{path}: instance ID {id} outside table"
  let compiledInstances ← instanceSlots.mapIdxM fun id slot =>
    match slot with
    | some value => pure value
    | none => throw s!"instance {id} absent from dense table"
  let mut normalizedBodies := #[]
  let mut validatedIds := ids
  for ((raw, _, path), index) in inputs.toList.zipIdx do
    let result := do
      let normalization ← catalog.field (← catalog.field raw "constant_query_context" path) "normalization" path
      catalog.requireSupported normalization path
      match ← catalog.optionalField normalization "body" path,
          ← catalog.optionalField normalization "body_ref" path with
      | some body, none => BodyReader.body catalog ctx body s!"{path}.normalization.body" |>.run state
      | none, some reference =>
        unless (← catalog.string reference path) == "source_body" do throw s!"{path}: unknown normalization body reference"
        let some id := ids[index]? | throw s!"{path}: source body ID absent"
        pure (id, state)
      | _, _ => throw s!"{path}: normalization must supply exactly one body or body_ref"
    match result with
    | .ok (id, next) =>
      normalizedBodies := normalizedBodies.push (.ok id)
      validatedIds := validatedIds.push id
      state := next
    | .error reason => normalizedBodies := normalizedBodies.push (.error reason)
  ReferenceBounds.validate state validatedIds
  let mut functionTypes := #[]
  let rawTypes ← catalog.array (← catalog.field catalog.root "types" "$") "$.types"
  for (raw,index) in rawTypes.toList.zipIdx do
    let some node := types[index]? | throw "function metadata type row absent"
    match (FunctionReader.typeData catalog types.size (node.compilerFacts.bind (·.definition)) raw s!"$.types[{index}]").run state with
    | .ok (value,next) =>
      functionTypes := functionTypes.push (.ok value)
      state := next
    | .error reason => functionTypes := functionTypes.push (.error reason)
  let (functions,next) ← (FunctionReader.queries catalog types.size).run state
  state := next
  let (abiQueries,next) ← (AbiQueryReader.read catalog abiTables types.size).run state
  state := next
  let runtimeInstances := catalog.readRuntimeInstances compiledInstances.size
  let runtimeTypes := RuntimeQueryReader.types catalog types.size compiledInstances.size
  let nativeSignatures := RuntimeQueryReader.nativeSignatures catalog types.size compiledInstances.size
  let runtimeVirtual ← match (RuntimeQueryReader.virtuals catalog types.size compiledInstances.size).run state with
    | .ok (value,next) => state := next; pure (.ok value)
    | .error reason => pure (.error reason)
  let mut bodySources := #[]
  for (raw,_,path) in inputs do
    let (metadata,next) ← (BodyMetadataReader.read catalog ctx raw path).run state
    state := next
    bodySources := bodySources.push metadata
  let (patternIds,next) ← (PatternReader.types catalog types.size).run state
  state := next
  let (panicQueries,next) ← (PanicQueryReader.read catalog).run state
  state := next
  let (namedGlobals,next) ← (NamedGlobalReader.read catalog types.size allocationCount).run state
  state := next
  let (externStatics,next) ← (ExternStaticReader.read catalog types.size allocationCount).run state
  state := next
  let (retagAttributes,next) ← (RetagQueryReader.read catalog).run state
  state := next
  let (namedConstants,next) ← (NamedConstantReader.read catalog ctx).run state
  state := next
  let (mainQueries,next) ← (MainQueryReader.read catalog types.size allocationCount).run state
  state := next
  let (allocationFunctions,next) ← (AllocationFunctionReader.read catalog types.size allocations compiledInstances).run state
  state := next
  let castQueries ← match (CastQueryReader.read catalog types.size compiledInstances).run state with
    | .ok (value,next) => state := next; pure (.ok value)
    | .error reason => pure (.error reason)
  let (foreignSymbols,next) ← (ForeignSymbolReader.read catalog types.size).run state
  state := next
  let mut normalization := #[]
  let mut compiled : Std.HashMap (Nat × Nat) (Except String NormalizationData) := {}
  for (result, index) in normalizedBodies.toList.zipIdx do
    let some original := ids[index]? | throw "source body ID absent for normalization"
    match result with
    | .error reason => normalization := normalization.push (.error reason)
    | .ok normalized =>
      let key := (original.index, normalized.index)
      let result := match compiled[key]? with
        | some result => result
        | none => PlaceTypeReader.build state.tables original normalized
      compiled := compiled.insert key result
      normalization := normalization.push result
  return ({
    startupQueries := StartupQueryReader.read catalog
    panicUnwinds := StartupQueryReader.panicUnwinds catalog
    castQueries := castQueries
    mir := {state.tables with regions := state.regions, arguments := state.arguments}
    compiler := state.compiler
    bodies := ids
    normalizedBodies := normalizedBodies
    normalization := normalization
    instances := compiledInstances
    functionTypes := functionTypes
    functions := functions
    runtimeInstances := runtimeInstances
    runtimeTypes := runtimeTypes
    runtimeVirtual := runtimeVirtual
    nativeSignatures := nativeSignatures
    bodySources := bodySources
    patterns := state.patterns
    patternIds := patternIds
    sessionMetadata := SessionMetadataReader.session catalog
    frameMetadata := SessionMetadataReader.frame catalog
    panicQueries := panicQueries
    namedGlobals := namedGlobals
    namedConstants := namedConstants
    mainQueries := mainQueries
    globalByteQueries := GlobalByteReader.read catalog
    typeNameConstants := ValueConstantReader.typeNames catalog ctx
    callerLocationConstants := ValueConstantReader.callerLocations catalog ctx
    foreignSymbols := foreignSymbols
    retagAttributes := retagAttributes
    threadLocals := ThreadLocalQueryReader.finish state
    allocationFunctions := allocationFunctions
    externStatics := externStatics
  }, abiQueries)

end Miri.Input.Reader
