import Miri.Input.Model
import Miri.Input.DecoderValues
import Miri.Input.ValidateTables
import Miri.Input.TypeConstCodec
import Miri.Input.DecodeMIR
import Miri.Input.CatalogDecoder

namespace Miri.Input
open Lean DecoderValues

private def validateDense (ids : Array Nat) (what : String) : Except String Unit := do
  for (id, index) in ids.toList.zipIdx do
    unless id == index do throw s!"{what}: expected ID {index} at table position {index}, got {id}"

private def jsonToNatArray (nodes : Array α) (getId : α → Nat) : Array Nat := nodes.map getId

private def validateSelectedScope (scope : SelectedScope) (_bodies : Array Body)
    (instances : Array InstanceNode) (bodyRoots : Array BodyRoot) : Except String Unit := do
  if scope.kind != "rooted_structural_closure" then
    throw ("$.selected_scope.kind" ++ ": " ++ s!"unrecognized selected-scope kind `{scope.kind}`")
  if scope.semantics != "structural_export_closure_only" then
    throw ("$.selected_scope.semantics" ++ ": " ++ s!"unrecognized scope guarantee `{scope.semantics}`")
  if scope.roots.isEmpty then throw ("$.selected_scope.roots" ++ ": " ++ "selected structural closure has no root")
  for (root, index) in scope.roots.toList.zipIdx do
    let resolvedBody := bodyRoots.any fun body =>
      body.definitionId == root.definitionId && body.defPath == root.defPath
    let resolvedInstance := instances.any fun inst =>
      inst.definitionId == some root.definitionId && inst.defPath == some root.defPath
    if !resolvedBody && !resolvedInstance then
      throw (s!"$.selected_scope.roots[{index}]" ++ ": " ++ "selected DefId and path do not resolve to an emitted body or instance")
  return ()

private def parseTypeArray (values : Array JsonReader.Slice) : Except String (Array TypeNode) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    result := result.push (← parseTypeNode value s!"$.types[{index}]")
    index := index + 1
  pure result

private def parseAllocationArray (values : Array JsonReader.Slice) : Except String (Array AllocationNode) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    result := result.push (← parseAllocation value s!"$.allocations[{index}]")
    index := index + 1
  pure result

private def parseInstanceArray (values : Array JsonReader.Slice) : Except String (Array InstanceNode) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    result := result.push (← parseInstance value s!"$.instances[{index}]")
    index := index + 1
  pure result

private def parseDocument (input : JsonReader.Object) (profile : Options := {}) : Except String ExecutionInput := do
  let root := input.fields
  let rootField (key : String) : Except String JsonReader.Slice := do
    let some (_, value) := root.find? (fun entry => entry.1 == key) | throw s!"$: missing field `{key}`"
    pure value
  let rootArray (key : String) := do (← rootField key).array
  let rootOptional (key : String) :=
    ((root.find? (fun entry => entry.1 == key)).map Prod.snd).filter (! ·.isNull)
  if (← (rootField "schema" >>= JsonReader.Slice.string)) != expectedSchema then
    throw s!"$.schema: expected `{expectedSchema}`"
  if (← (rootField "schema_version" >>= JsonReader.Slice.natural)) != expectedSchemaVersion then
    throw s!"$.schema_version: unsupported schema version"
  let producerJson ← rootField "producer"
  let producer : Producer := {
    miriCommit := ← fieldString producerJson "miri_commit" "$.producer"
    rustcCommit := ← fieldString producerJson "rustc_commit" "$.producer"
    rustcVersion := ← fieldString producerJson "rustc_version" "$.producer"
    targetTriple := ← fieldString producerJson "target_triple" "$.producer"
  }
  if producer.miriCommit != expectedMiriCommit then throw "$.producer.miri_commit: input is from the wrong pinned Miri revision"
  if producer.rustcCommit != expectedRustcCommit then throw "$.producer.rustc_commit: input is from the wrong pinned rustc revision"
  let predicates ← ((← rootArray "predicates").toList.zipIdx.mapM fun ((value, index) : JsonReader.Slice × Nat) =>
    parseVtablePredicate value s!"$.predicates[{index}]").map List.toArray
  let mut predicateIdentities : Std.HashMap Nat (Array VtablePredicate) := {}
  for (predicate, index) in predicates.toList.zipIdx do
    let previous := predicateIdentities.getD predicate.definitionId #[]
    if previous.any (fun other => decide (other.kind = predicate.kind ∧ other.genericArgs = predicate.genericArgs ∧
        other.boundVariables = predicate.boundVariables ∧ other.projectionTerm = predicate.projectionTerm)) then
      throw s!"$.predicates[{index}]: duplicate compiler predicate identity"
    predicateIdentities := predicateIdentities.insert predicate.definitionId (previous.push predicate)
  let compilerPredicates ← (← rootArray "compiler_predicate_queries").mapM decodeCompilerPredicateEvidence
  unless compilerPredicates.size == predicates.size do
    throw "$.compiler_predicate_queries: predicate query and definition tables differ in size"
  for (query, index) in compilerPredicates.toList.zipIdx do
    unless query.id == index && query.original == index do
      throw s!"$.compiler_predicate_queries[{index}]: predicate query identity mismatch"
    let some definition := predicates[index]? | throw "compiler predicate table index invariant"
    unless query.autoTrait == (definition.kind == .autoTrait) do
      throw s!"$.compiler_predicate_queries[{index}]: auto-trait query disagrees with predicate definition"
    if let some normalized := query.normalizedId then
      unless normalized < predicates.size do
        throw s!"$.compiler_predicate_queries[{index}]: dangling normalized predicate reference {normalized}"
  let definitions ← ((← rootArray "definitions").toList.zipIdx.mapM fun ((value, index) : JsonReader.Slice × Nat) =>
    parseDefinitionId value s!"$.definitions[{index}]").map List.toArray
  let mut definitionKeys : Std.HashSet (Nat × Nat) := {}
  for (definition, index) in definitions.toList.zipIdx do
    let key := (definition.crateIndex, definition.index)
    if definitionKeys.contains key then throw s!"$.definitions[{index}]: duplicate compiler definition identity"
    definitionKeys := definitionKeys.insert key
  let typeConstants ← ((← rootArray "type_constants").toList.zipIdx.mapM fun ((value, index) : JsonReader.Slice × Nat) =>
    TypeConstCodec.decode value s!"$.type_constants[{index}]").map List.toArray
  let mut constantValues : Array MIR.TypeConst := #[]
  for (constant, index) in typeConstants.toList.zipIdx do
    if constantValues.contains constant then
      throw s!"$.type_constants[{index}]: duplicate compiler type-constant identity"
    constantValues := constantValues.push constant
  let spans ← ((← rootArray "spans").toList.zipIdx.mapM fun ((value, index) : JsonReader.Slice × Nat) =>
    parseSourceSpan value s!"$.spans[{index}]").map List.toArray
  let layouts ← ((← rootArray "layouts").toList.zipIdx.mapM fun ((value, index) : JsonReader.Slice × Nat) =>
    parseLayout value s!"$.layouts[{index}]").map List.toArray
  let functionAbis ← ((← rootArray "fn_abis").toList.zipIdx.mapM fun ((value, index) : JsonReader.Slice × Nat) =>
    parseFunctionAbi value s!"$.fn_abis[{index}]").map List.toArray
  let typesJson ← rootArray "types"
  if typesJson.isEmpty then throw "$.types: input has no type graph; refusing an empty import"
  let types ← profileit "decoder.types" profile fun _ => parseTypeArray typesJson
  let allocationsJson ← rootArray "allocations"
  let allocations ← profileit "decoder.allocations" profile fun _ => parseAllocationArray allocationsJson
  let compilerAllocIdWorld ← profileit "decoder.compiler_alloc_id_world" profile fun _ => do
    match rootOptional "compiler_alloc_id_world" with
    | none => pure none
    | some value => pure (some (← parseCompilerAllocIdWorld value allocations))
  let instancesJson ← rootArray "instances"
  let instances ← profileit "decoder.instances" profile fun _ => parseInstanceArray instancesJson
  let mut instanceIdentities : Std.HashMap Nat (Array InstanceNode) := {}
  for (node, index) in instances.toList.zipIdx do
    let definition := node.instanceKind.defId
    let previous := instanceIdentities.getD definition #[]
    if previous.any (fun other => decide (other.instanceKind = node.instanceKind ∧ other.genericArgs = node.genericArgs)) then
      throw s!"$.instances[{index}]: duplicate compiler instance identity"
    instanceIdentities := instanceIdentities.insert definition (previous.push node)
  let selectedScope ← match rootOptional "selected_scope" with
    | none => pure none
    | some value =>
      pure (some (← parseSelectedScope value "$.selected_scope"))
  let compilerAbiLayoutSchema ← (rootField "compiler_abi_layout_schema" >>= JsonReader.Slice.string)
  unless compilerAbiLayoutSchema == expectedCompilerAbiLayoutSchema do
    throw s!"$.compiler_abi_layout_schema: unsupported schema `{compilerAbiLayoutSchema}`"
  let bodiesJson ← rootArray "bodies"
  if bodiesJson.isEmpty then throw "$.bodies: input has no MIR bodies; refusing an empty import"
  let bodyContext : DecodeMIR.Context := {
    typeCount := types.size, allocationCount := allocations.size,
    definitionCount := definitions.size, typeConstantCount := typeConstants.size,
    spanCount := spans.size,
    scalarSizes := types.map fun ty => (layouts[ty.layoutId]?).bind (·.sizeBytes),
    threadLocal := fun value => parseThreadLocal value }
  let bodies ← profileit "decoder.bodies" profile fun _ =>
    (bodiesJson.toList.zipIdx.mapM fun ((value, index) : JsonReader.Slice × Nat) =>
      DecodeMIR.decodeBody bodyContext value s!"$.bodies[{index}]").map List.toArray
  let bodyRoots ← ((← rootArray "body_roots").toList.zipIdx.mapM fun ((value, index) : JsonReader.Slice × Nat) =>
    parseBodyRoot value s!"$.body_roots[{index}]").map List.toArray
  let typeIds := jsonToNatArray types (·.id)
  let allocationIds := jsonToNatArray allocations (·.id)
  let instanceIds := jsonToNatArray instances (·.id)
  profileit "decoder.validate_dense_type_ids" profile fun _ => validateDense typeIds "type IDs"
  profileit "decoder.validate_dense_allocation_ids" profile fun _ => validateDense allocationIds "allocation IDs"
  profileit "decoder.validate_dense_instance_ids" profile fun _ => validateDense instanceIds "instance IDs"
  match selectedScope with
  | some scope => profileit "decoder.selected_scope_validation" profile fun _ =>
      validateSelectedScope scope bodies instances bodyRoots
  | none => pure ()
  let runtimeTargetDataLayout ← match rootOptional "runtime_target_data_layout" with
    | none => pure none
    | some value => some <$> CatalogDecoder.targetDataLayout value
  let queries ← CatalogDecoder.decodeObject bodyContext input
  let producerSettings ← CatalogDecoder.producerSettings (← field producerJson "input_settings" "$.producer")
  let core : ImportDocument := {
    compilerPredicates := compilerPredicates
    compilerAbiLayoutSchema := some compilerAbiLayoutSchema
    producer := producer
    runtimeTargetDataLayout := runtimeTargetDataLayout
    predicates := predicates
    definitions := definitions
    typeConstants := typeConstants
    layouts := layouts
    spans := spans
    types := types
    allocations := allocations
    compilerAllocIdWorld := compilerAllocIdWorld
    instances := instances
    selectedScope := selectedScope
    functionAbis := functionAbis
    bodyRoots := bodyRoots
    bodies := bodies
    queries
    producerSettings
  }
  validatePrimaryTables core
  pure ⟨core⟩

def decodeJsonProfiled (text : String) (profile : Options) : Except String ExecutionInput := do
  let source ← profileit "decoder.syntax" profile fun _ => JsonReader.parseObject text
  profileit "decoder.document" profile fun _ => parseDocument source profile

def decodeJson (text : String) : Except String ExecutionInput := decodeJsonProfiled text {}

def decodeFile (path : System.FilePath) : IO (Except String ExecutionInput) := do
  try
    pure (decodeJson (← IO.FS.readFile path))
  catch error => pure (.error s!"could not read {path}: {error}")

def decodeAllocationMemoryEvidence (value : JsonReader.Slice) : Except String AllocationMemory :=
  parseAllocationMemory value "$allocation"

end Miri.Input
