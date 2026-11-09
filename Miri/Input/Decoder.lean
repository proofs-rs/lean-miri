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

private structure ProducerFields where
  miriCommit : Option String := none
  rustcCommit : Option String := none
  rustcVersion : Option String := none
  targetTriple : Option String := none
  settings : Option Catalog.ProducerSettings := none

private def parseProducer : JsonReader.Parser (Producer × Catalog.ProducerSettings) := do
  let p ← JsonReader.object ({} : ProducerFields) fun p key => do
    match key with
    | "miri_commit" => return {p with miriCommit := some (← JsonReader.string)}
    | "rustc_commit" => return {p with rustcCommit := some (← JsonReader.string)}
    | "rustc_version" => return {p with rustcVersion := some (← JsonReader.string)}
    | "target_triple" => return {p with targetTriple := some (← JsonReader.string)}
    | "input_settings" => return {p with settings := some (← CatalogDecoder.producerSettings)}
    | _ => JsonReader.skipValue; return p
  let producer : Producer := {
    miriCommit := ← JsonReader.required p.miriCommit "miri_commit"
    rustcCommit := ← JsonReader.required p.rustcCommit "rustc_commit"
    rustcVersion := ← JsonReader.required p.rustcVersion "rustc_version"
    targetTriple := ← JsonReader.required p.targetTriple "target_triple"
  }
  return (producer, ← JsonReader.required p.settings "input_settings")

/-- Concrete unresolved input. It owns typed data only, never JSON source ranges. -/
structure DraftDocument where
  schema : String
  schemaVersion : Nat
  producer : Producer × Catalog.ProducerSettings
  predicates : Array VtablePredicate
  compilerPredicates : Array CompilerPredicateEvidence
  definitions : Array DefinitionId
  typeConstants : Array MIR.TypeConst
  spans : Array SourceSpanData
  layouts : Array Layout
  functionAbis : Array FunctionAbi
  types : Array TypeNode
  allocations : Array AllocationNode
  instances : Array InstanceNode
  compilerAbiLayoutSchema : String
  bodies : Array DecodeMIR.DraftBody
  bodyRoots : Array BodyRoot
  compilerAllocIdWorld : Option CompilerAllocIdWorld
  selectedScope : Option SelectedScope
  runtimeTargetDataLayout : Option TargetDataLayoutEvidence
  queries : CatalogDecoder.UnresolvedQueries

private structure DocumentFields where
  schema : Option (String) := none
  schemaVersion : Option (Nat) := none
  producer : Option (Producer × Catalog.ProducerSettings) := none
  predicates : Option (Array VtablePredicate) := none
  compilerPredicates : Option (Array CompilerPredicateEvidence) := none
  definitions : Option (Array DefinitionId) := none
  typeConstants : Option (Array MIR.TypeConst) := none
  spans : Option (Array SourceSpanData) := none
  layouts : Option (Array Layout) := none
  functionAbis : Option (Array FunctionAbi) := none
  types : Option (Array TypeNode) := none
  allocations : Option (Array AllocationNode) := none
  instances : Option (Array InstanceNode) := none
  compilerAbiLayoutSchema : Option (String) := none
  bodies : Option (Array DecodeMIR.DraftBody) := none
  bodyRoots : Option (Array BodyRoot) := none
  compilerAllocIdWorld : Option CompilerAllocIdWorld := none
  selectedScope : Option SelectedScope := none
  runtimeTargetDataLayout : Option TargetDataLayoutEvidence := none
  queries : CatalogDecoder.DraftQueries := {}

def parseDocument : JsonReader.Parser DraftDocument := do
  let d ← JsonReader.object ({} : DocumentFields) fun d key => do
    match key with
    | "schema" => return {d with schema := some (← JsonReader.string)}
    | "schema_version" => return {d with schemaVersion := some (← JsonReader.natural)}
    | "producer" => return {d with producer := some (← parseProducer)}
    | "predicates" => return {d with predicates := some (← JsonReader.arrayIndexed (fun index => parseVtablePredicate s!"$.predicates[{index}]"))}
    | "compiler_predicate_queries" => return {d with compilerPredicates := some (← JsonReader.array decodeCompilerPredicateEvidence)}
    | "definitions" => return {d with definitions := some (← JsonReader.arrayIndexed (fun index => parseDefinitionId s!"$.definitions[{index}]"))}
    | "type_constants" => return {d with typeConstants := some (← JsonReader.arrayIndexed (fun index => TypeConstCodec.decode s!"$.type_constants[{index}]"))}
    | "spans" => return {d with spans := some (← JsonReader.arrayIndexed (fun index => parseSourceSpan s!"$.spans[{index}]"))}
    | "layouts" => return {d with layouts := some (← JsonReader.arrayIndexed (fun index => parseLayout s!"$.layouts[{index}]"))}
    | "fn_abis" => return {d with functionAbis := some (← JsonReader.arrayIndexed (fun index => parseFunctionAbi s!"$.fn_abis[{index}]"))}
    | "types" => return {d with types := some (← JsonReader.arrayIndexed (fun index => parseTypeNode s!"$.types[{index}]"))}
    | "allocations" => return {d with allocations := some (← JsonReader.arrayIndexed (fun index => parseAllocation s!"$.allocations[{index}]"))}
    | "instances" => return {d with instances := some (← JsonReader.arrayIndexed (fun index => parseInstance s!"$.instances[{index}]"))}
    | "compiler_abi_layout_schema" => return {d with compilerAbiLayoutSchema := some (← JsonReader.string)}
    | "bodies" => return {d with bodies := some (← JsonReader.arrayIndexed (fun index => DecodeMIR.parseBody s!"$.bodies[{index}]"))}
    | "body_roots" => return {d with bodyRoots := some (← JsonReader.arrayIndexed (fun index => parseBodyRoot s!"$.body_roots[{index}]"))}
    | "compiler_alloc_id_world" => return {d with compilerAllocIdWorld := ← JsonReader.nullable (parseCompilerAllocIdWorld)}
    | "selected_scope" => return {d with selectedScope := ← JsonReader.nullable (parseSelectedScope "$.selected_scope")}
    | "runtime_target_data_layout" => return {d with runtimeTargetDataLayout := ← JsonReader.nullable (CatalogDecoder.targetDataLayout)}
    | _ =>
      match ← CatalogDecoder.parseField d.queries key with
      | some queries => return {d with queries}
      | none => JsonReader.skipValue; return d
  return {
    schema := ← JsonReader.required d.schema "schema"
    schemaVersion := ← JsonReader.required d.schemaVersion "schema_version"
    producer := ← JsonReader.required d.producer "producer"
    predicates := ← JsonReader.required d.predicates "predicates"
    compilerPredicates := ← JsonReader.required d.compilerPredicates "compiler_predicate_queries"
    definitions := ← JsonReader.required d.definitions "definitions"
    typeConstants := ← JsonReader.required d.typeConstants "type_constants"
    spans := ← JsonReader.required d.spans "spans"
    layouts := ← JsonReader.required d.layouts "layouts"
    functionAbis := ← JsonReader.required d.functionAbis "fn_abis"
    types := ← JsonReader.required d.types "types"
    allocations := ← JsonReader.required d.allocations "allocations"
    instances := ← JsonReader.required d.instances "instances"
    compilerAbiLayoutSchema := ← JsonReader.required d.compilerAbiLayoutSchema "compiler_abi_layout_schema"
    bodies := ← JsonReader.required d.bodies "bodies"
    bodyRoots := ← JsonReader.required d.bodyRoots "body_roots"
    compilerAllocIdWorld := d.compilerAllocIdWorld
    selectedScope := d.selectedScope
    runtimeTargetDataLayout := d.runtimeTargetDataLayout
    queries := ← CatalogDecoder.finish d.queries
  }

def resolveDocument (d : DraftDocument) (profile : Options := {}) : Except String ExecutionInput := do
  let schema := d.schema
  let schemaVersion := d.schemaVersion
  let producer := d.producer
  let predicates := d.predicates
  let compilerPredicates := d.compilerPredicates
  let definitions := d.definitions
  let typeConstants := d.typeConstants
  let spans := d.spans
  let layouts := d.layouts
  let functionAbis := d.functionAbis
  let types := d.types
  let allocations := d.allocations
  let instances := d.instances
  let compilerAbiLayoutSchema := d.compilerAbiLayoutSchema
  let bodies := d.bodies
  let bodyRoots := d.bodyRoots
  let compilerAllocIdWorld := d.compilerAllocIdWorld
  let selectedScope := d.selectedScope
  let runtimeTargetDataLayout := d.runtimeTargetDataLayout
  let producerSettings := producer.2
  let producer := producer.1
  if schema != expectedSchema then throw s!"$.schema: expected `{expectedSchema}`"
  if schemaVersion != expectedSchemaVersion then throw "$.schema_version: unsupported schema version"
  if producer.miriCommit != expectedMiriCommit then throw "$.producer.miri_commit: input is from the wrong pinned Miri revision"
  if producer.rustcCommit != expectedRustcCommit then throw "$.producer.rustc_commit: input is from the wrong pinned rustc revision"
  unless compilerAbiLayoutSchema == expectedCompilerAbiLayoutSchema do
    throw s!"$.compiler_abi_layout_schema: unsupported schema `{compilerAbiLayoutSchema}`"
  if types.isEmpty then throw "$.types: input has no type graph; refusing an empty import"
  if bodies.isEmpty then throw "$.bodies: input has no MIR bodies; refusing an empty import"
  let mut predicateIdentities : Std.HashMap Nat (Array VtablePredicate) := {}
  for (predicate, index) in predicates.toList.zipIdx do
    let previous := predicateIdentities.getD predicate.definitionId #[]
    if previous.any (fun other => decide (other.kind = predicate.kind ∧ other.genericArgs = predicate.genericArgs ∧
        other.boundVariables = predicate.boundVariables ∧ other.projectionTerm = predicate.projectionTerm)) then
      throw s!"$.predicates[{index}]: duplicate compiler predicate identity"
    predicateIdentities := predicateIdentities.insert predicate.definitionId (previous.push predicate)
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
  let mut definitionKeys : Std.HashSet (Nat × Nat) := {}
  for (definition, index) in definitions.toList.zipIdx do
    let key := (definition.crateIndex, definition.index)
    if definitionKeys.contains key then throw s!"$.definitions[{index}]: duplicate compiler definition identity"
    definitionKeys := definitionKeys.insert key
  let mut constantValues : Array MIR.TypeConst := #[]
  for (constant, index) in typeConstants.toList.zipIdx do
    if constantValues.contains constant then
      throw s!"$.type_constants[{index}]: duplicate compiler type-constant identity"
    constantValues := constantValues.push constant
  let mut instanceIdentities : Std.HashMap Nat (Array InstanceNode) := {}
  for (node, index) in instances.toList.zipIdx do
    let definition := node.instanceKind.defId
    let previous := instanceIdentities.getD definition #[]
    if previous.any (fun other => decide (other.instanceKind = node.instanceKind ∧ other.genericArgs = node.genericArgs)) then
      throw s!"$.instances[{index}]: duplicate compiler instance identity"
    instanceIdentities := instanceIdentities.insert definition (previous.push node)
  if let some world := compilerAllocIdWorld then validateCompilerAllocIdWorld allocations world
  let bodyContext : DecodeMIR.Context := {
    typeCount := types.size, allocationCount := allocations.size,
    definitionCount := definitions.size, typeConstantCount := typeConstants.size,
    spanCount := spans.size,
    scalarSizes := types.map fun ty => (layouts[ty.layoutId]?).bind (·.sizeBytes) }
  let bodies ← profileit "decoder.resolve_bodies" profile fun _ =>
    bodies.mapM (DecodeMIR.resolveBody bodyContext)
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
  let queries ← CatalogDecoder.resolveQueries bodyContext d.queries
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
  let draft ← profileit "decoder.parse" profile fun _ => JsonReader.run parseDocument text
  profileit "decoder.resolve" profile fun _ => resolveDocument draft profile

def decodeJson (text : String) : Except String ExecutionInput := decodeJsonProfiled text {}

def decodeFile (path : System.FilePath) : IO (Except String ExecutionInput) := do
  try
    pure (decodeJson (← IO.FS.readFile path))
  catch error => pure (.error s!"could not read {path}: {error}")

def decodeAllocationMemoryEvidence (text : String) : Except String AllocationMemory :=
  JsonReader.run (parseAllocationMemory "$allocation") text

end Miri.Input
