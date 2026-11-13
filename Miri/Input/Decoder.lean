import Miri.Input.TraitSelection.Codec
import Miri.Input.Model
import Miri.Input.DecoderValues
import Miri.Input.ValidateTables
import Miri.Input.TypeConstCodec
import Miri.Input.DecodeMIR
import Miri.Input.CatalogDecoder
import Miri.Input.SharedPools
import Miri.Input.CoroutineCoverage
import Miri.Input.RuntimeMetadata
import Miri.Input.SourceMir
import Miri.Input.CtfeMirSourceCodec

namespace Miri.Input
open Lean DecoderValues

private def validateSelectedScope (scope : SelectedScope) (_bodies : Array BodySeed)
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

private structure AbiSessionFields where
  panic : Option PanicStrategy := none
  panicInDrop : Option PanicStrategy := none
  optimization : Option OptimizationLevel := none
  llvmWritable : Option Bool := none
  boxNoalias : Option Bool := none
  incrementalEnabled : Option Bool := none
  sanitizers : Option (Array String) := none

private def parsePanicStrategy : JsonReader.Parser PanicStrategy := do
  match ← JsonReader.string with
  | "unwind" => pure .unwind | "abort" => pure .abort
  | "immediate-abort" => pure .immediateAbort
  | value => JsonReader.fail s!"unknown raw ABI panic strategy {value}"

private def parseAbiSession : JsonReader.Parser AbiSessionMaterial := do
  let p ← JsonReader.object ({} : AbiSessionFields) fun p key => do
    match key with
    | "panic" => return {p with panic := some (← parsePanicStrategy)}
    | "panic_in_drop" => return {p with panicInDrop := some (← parsePanicStrategy)}
    | "optimization" =>
      let level ← match ← JsonReader.string with
        | "no" => pure OptimizationLevel.no | "less" => pure .less
        | "more" => pure .more | "aggressive" => pure .aggressive
        | "size" => pure .size | "size_min" => pure .sizeMin
        | value => JsonReader.fail s!"unknown raw ABI optimization level {value}"
      return {p with optimization := some level}
    | "llvm_writable" => return {p with llvmWritable := some (← JsonReader.boolean)}
    | "box_noalias" => return {p with boxNoalias := some (← JsonReader.boolean)}
    | "incremental_enabled" => return {p with incrementalEnabled := some (← JsonReader.boolean)}
    | "sanitizers" => return {p with sanitizers := some (← JsonReader.array JsonReader.string)}
    | _ => JsonReader.fail s!"unknown raw ABI session field {key}"
  pure ⟨← JsonReader.required p.panic "abi_session.panic",
    ← JsonReader.required p.panicInDrop "abi_session.panic_in_drop",
    ← JsonReader.required p.optimization "abi_session.optimization",
    ← JsonReader.required p.llvmWritable "abi_session.llvm_writable",
    ← JsonReader.required p.boxNoalias "abi_session.box_noalias",
    ← JsonReader.required p.incrementalEnabled "abi_session.incremental_enabled",
    ← JsonReader.required p.sanitizers "abi_session.sanitizers"⟩

private structure ProducerFields where
  miriCommit : Option String := none
  rustcCommit : Option String := none
  rustcVersion : Option String := none
  targetTriple : Option String := none
  settings : Option Catalog.ProducerSettings := none
  abiSession : Option AbiSessionMaterial := none
  freezeLangItem : Option (Option DefinitionRef) := none

private def parseProducer : JsonReader.Parser (Producer × Catalog.ProducerSettings) := do
  let p ← JsonReader.object ({} : ProducerFields) fun p key => do
    match key with
    | "miri_commit" => return {p with miriCommit := some (← JsonReader.string)}
    | "rustc_commit" => return {p with rustcCommit := some (← JsonReader.string)}
    | "rustc_version" => return {p with rustcVersion := some (← JsonReader.string)}
    | "target_triple" => return {p with targetTriple := some (← JsonReader.string)}
    | "abi_session" => return {p with abiSession := some (← parseAbiSession)}
    | "freeze_lang_item" => return {p with freezeLangItem := some (← JsonReader.nullable JsonReader.natural)}
    | "input_settings" => return {p with settings := some (← CatalogDecoder.producerSettings)}
    | _ => JsonReader.skipValue; return p
  let producer : Producer := {
    miriCommit := ← JsonReader.required p.miriCommit "miri_commit"
    rustcCommit := ← JsonReader.required p.rustcCommit "rustc_commit"
    rustcVersion := ← JsonReader.required p.rustcVersion "rustc_version"
    targetTriple := ← JsonReader.required p.targetTriple "target_triple"
    abiSession := some (← JsonReader.required p.abiSession "abi_session")
    freezeLangItem := ← JsonReader.required p.freezeLangItem "freeze_lang_item"
  }
  return (producer, ← JsonReader.required p.settings "input_settings")

/-- The completed import plus numeric reference bounds that require all tables.
MIR and catalogs already have their final representation. -/
private structure ParsedDocument where
  value : ImportDocument
  schema : String
  schemaVersion : Nat
  bodyReferences : Array DecodeMIR.References
  abiArguments : Array AbiArgument

private def denseRow (what : String) (index : Nat) (getId : α → Nat)
    (parser : JsonReader.Parser α) : JsonReader.Parser α := do
  let value ← parser
  unless getId value == index do
    JsonReader.fail s!"{what}: expected ID {index} at table position {index}, got {getId value}"
  pure value

private def parsePredicates : JsonReader.Parser (Array VtablePredicate) :=
  JsonReader.arrayWithState ({} : Std.HashMap Nat (Array VtablePredicate)) fun seen index => do
    let value ← parseVtablePredicate s!"$.predicates[{index}]"
    let previous := seen.getD value.definitionId #[]
    if previous.any (fun other => decide (other.kind = value.kind ∧ other.genericArgs = value.genericArgs ∧
        other.boundVariables = value.boundVariables ∧ other.projectionTerm = value.projectionTerm)) then
      JsonReader.fail s!"$.predicates[{index}]: duplicate compiler predicate identity"
    pure (value, seen.insert value.definitionId (previous.push value))

private def parseDefinitions : JsonReader.Parser (Array DefinitionId) :=
  JsonReader.arrayWithState ({} : Std.HashSet (Nat × Nat)) fun seen index => do
    let value ← parseDefinitionId s!"$.definitions[{index}]"
    let key := (value.crateIndex, value.index)
    if seen.contains key then JsonReader.fail s!"$.definitions[{index}]: duplicate compiler definition identity"
    pure (value, seen.insert key)

private def parseConstants : JsonReader.Parser (Array MIR.TypeConst) :=
  JsonReader.arrayWithState (#[] : Array MIR.TypeConst) fun seen index => do
    let value ← TypeConstCodec.decode s!"$.type_constants[{index}]"
    if seen.contains value then JsonReader.fail s!"$.type_constants[{index}]: duplicate compiler type-constant identity"
    pure (value, seen.push value)

private def parseInstances : JsonReader.Parser (Array InstanceNode) :=
  JsonReader.arrayWithState ({} : Std.HashMap Nat (Array InstanceNode)) fun seen index => do
    let value ← denseRow "instance IDs" index (·.id) (parseInstance s!"$.instances[{index}]")
    let definition := value.instanceKind.defId
    let previous := seen.getD definition #[]
    if previous.any (fun other => decide (other.instanceKind = value.instanceKind ∧ other.genericArgs = value.genericArgs)) then
      JsonReader.fail s!"$.instances[{index}]: duplicate compiler instance identity"
    pure (value, seen.insert definition (previous.push value))

private def parseFiles : JsonReader.Parser (Array String) :=
  JsonReader.arrayWithState ({} : Std.HashSet String) fun seen index => do
    let value ← JsonReader.string
    if seen.contains value then JsonReader.fail s!"$.files[{index}]: duplicate filename identity"
    pure (value, seen.insert value)

private def parseByteImages : JsonReader.Parser (Array (AllocationBytes × String)) :=
  JsonReader.arrayWithState ({} : Std.HashSet String) fun seen index => do
    let hex ← JsonReader.string
    unless canonicalLowerHex hex do JsonReader.fail s!"$.byte_images[{index}]: expected canonical lowercase hexadecimal"
    if seen.contains hex then JsonReader.fail s!"$.byte_images[{index}]: duplicate exact byte image"
    let bytes ← JsonReader.liftExcept (decodeAllocationHex hex)
    pure ((.image bytes, hex), seen.insert hex)

private def finishAllocations (images : Array AllocationBytes) (groups : Array (Array AllocationNode))
    (pendingNodes : Array AllocationNode) :
    Except String (Array AllocationNode) := do
  let mut nodes := pendingNodes
  let mut sources : Std.HashSet UInt64 := {}
  let mut functions : Std.HashSet InstanceId := {}
  for group in groups do
    let some first := group[0]? | throw "$.allocations: empty allocation group"
    if let some (.function value) := first.data then
      if functions.contains value.instanceId then throw "$.allocations: duplicate exact function Instance group"
      functions := functions.insert value.instanceId
  let mut finalized := #[]
  for node in nodes do
    let path := s!"$.allocations[graph_id={node.id}]"
    let some source := node.sourceAllocId | throw s!"{path}: missing source AllocId"
    if source == 0 || sources.contains source then throw s!"{path}: invalid or duplicate source AllocId"
    sources := sources.insert source
    let node ← match node.data with
    | some (.memory memory) =>
      let memory ← resolveAllocationMemory images path memory
      pure { node with memory := some memory, data := some (.memory memory) }
    | some (.static value) =>
      let initializer ← value.initializer.mapM (resolveAllocationMemory images (path ++ ".initializer"))
      pure { node with data := some (.static { value with initializer }) }
    | _ => pure node
    finalized := finalized.push node
  nodes := finalized
  for (node, index) in nodes.toList.zipIdx do
    unless node.id == index do throw s!"$.allocations: expected graph ID {index}, got {node.id}"
  pure nodes

private def finishBodies (images : Array AllocationBytes) (bodies : Array Body) : Except String (Array Body) :=
  bodies.mapM fun body => do
    unless body.nodeFacts.any (fun block => block.any (fun facts => !facts.threadLocals.isEmpty)) do
      return body
    let nodeFacts ← body.nodeFacts.mapM fun block => block.mapM fun facts => do
      if facts.threadLocals.isEmpty then return facts
      let threadLocals ← facts.threadLocals.mapM fun declaration => do
        let initializer ← declaration.initializer.mapM (resolveAllocationMemory images "$thread_local.initializer")
        pure { declaration with initializer }
      pure { facts with threadLocals }
    pure { body with nodeFacts }

private def finishWorld (nodes : Array AllocationNode) (hexByGraph : Array (Option String))
    (pending : PendingCompilerAllocIdWorld) : Except String CompilerAllocIdWorld := do
  let mut bySource : Std.HashMap UInt64 AllocationNode := {}
  for node in nodes do
    let some source := node.sourceAllocId | throw "$.compiler_alloc_id_world: missing source identity"
    bySource := bySource.insert source node
  let mut rawPool := #[]
  for (row, index) in pending.rawPool.toList.zipIdx do
    let source := UInt64.ofNat (index + 1)
    match row with
    | some exception =>
      if bySource.contains source then throw "$.compiler_alloc_id_world.raw_pool: exceptional row has a serialized source allocation"
      rawPool := rawPool.push exception
    | none =>
      let some node := bySource[source]? | throw "$.compiler_alloc_id_world.raw_pool: null row has no serialized source allocation"
      let kind := match node.kind with
        | .memory => SourceAllocIdKind.memory
        | .function => .function
        | .static => .static
        | .vtable => .vtable
        | .typeId => .typeId
      rawPool := rawPool.push { sourceAllocId := source, kind, status := .serialized, allocationId := some node.id }
  let dedupCatalog ← pending.dedupCatalog.mapM fun row => do
    let some key := nodes[row.keyAllocationId]? | throw "$.compiler_alloc_id_world.dedup_catalog: key allocation is absent"
    let byteImageHex ← if row.keyKind == .bytes then do
        let some (.memory _) := key.data | throw "$.compiler_alloc_id_world.dedup_catalog: byte key is not memory"
        let some hex := (hexByGraph[row.keyAllocationId]?).bind id | throw "$.compiler_alloc_id_world.dedup_catalog: byte key lacks exact pooled image"
        pure (some hex)
      else pure none
    let salts ← row.salts.mapIdxM fun salt graph => do
      let some node := nodes[graph]? | throw "$.compiler_alloc_id_world.dedup_catalog.salts: allocation is absent"
      let some source := node.sourceAllocId | throw "$.compiler_alloc_id_world.dedup_catalog.salts: source identity is absent"
      pure (⟨salt, graph, source⟩ : SourceAllocIdSaltResult)
    pure (⟨row.keyKind, row.keyAllocationId, byteImageHex, salts⟩ : SourceAllocIdDedupRow)
  pure ⟨pending.lastReservedSourceAllocId, pending.nextSourceAllocId, pending.finalSentinelSourceAllocId,
    rawPool, dedupCatalog, pending.completeKeyFamilies, pending.nonExhaustiveKeyFamilies⟩

private structure DocumentFields where
  traitProgram : Option Json := none
  schema : Option (String) := none
  schemaVersion : Option (Nat) := none
  producer : Option (Producer × Catalog.ProducerSettings) := none
  predicates : Option (Array VtablePredicate) := none
  compilerPredicates : Option (Array CompilerPredicateEvidence) := none
  definitions : Option (Array DefinitionId) := none
  typeConstants : Option (Array MIR.TypeConst) := none
  files : Option (Array String) := none
  spans : Option (Array SourceSpanData) := none
  layouts : Option (Array Layout) := none
  functionAbis : Option (Array FunctionAbi) := none
  types : Option (Array TypeNode) := none
  byteImages : Option (Array (AllocationBytes × String)) := none
  allocations : Option (Array (Array AllocationNode)) := none
  instances : Option (Array InstanceNode) := none
  compilerAbiLayoutSchema : Option (String) := none
  bodies : Option (Array BodySeed) := none
  mirTemplates : Option (Array CopyTemplateSource) := none
  ctfeScalarSources : Option (Array CtfeMirSource.Source) := none
  bodyReferences : Array DecodeMIR.References := #[]
  coroutineCoverage : Option CoroutineCoverageCodec.Parsed := none
  bodyRoots : Option (Array BodyRoot) := none
  compilerAllocIdWorld : Option PendingCompilerAllocIdWorld := none
  selectedScope : Option SelectedScope := none
  runtimeTargetDataLayout : Option TargetDataLayoutEvidence := none
  queries : CatalogDecoder.QueryFields := {}

private def parseDocumentFields (pools : SharedPools) : JsonReader.Parser ParsedDocument := do
  let d ← JsonReader.object ({} : DocumentFields) fun d key => do
    match key with
    | "compiler_initial_global_snapshot" | "compiler_initial_ctfe_roots" =>
      JsonReader.fail "initial compiler allocation/CTFE profiles require the dedicated initial-profile decoder; legacy decoding is unsupported"
    | "schema" => return {d with schema := some (← JsonReader.string)}
    | "schema_version" => do
      let version ← JsonReader.natural
      -- Reject a known obsolete header before interpreting later body fields
      -- under the BodySeed contract. Earlier malformed fields still take
      -- precedence; valid current inputs retain arbitrary root-field order.
      unless version == expectedSchemaVersion do
        JsonReader.fail "$.schema_version: unsupported schema version"
      return {d with schemaVersion := some version}
    | "compiler_trait_program" => return {d with traitProgram := some (← Lean.Json.Parser.anyCore)}
    | "producer" => return {d with producer := some (← parseProducer)}
    | "predicates" => return {d with predicates := some (← parsePredicates)}
    | "compiler_predicate_queries" => return {d with compilerPredicates := some (← JsonReader.array decodeCompilerPredicateEvidence)}
    | "definitions" => return {d with definitions := some (← parseDefinitions)}
    | "type_constants" => return {d with typeConstants := some (← parseConstants)}
    | "files" => return {d with files := some (← parseFiles)}
    | "spans" => return {d with spans := some (← JsonReader.arrayIndexed (fun index => parseSourceSpan s!"$.spans[{index}]"))}
    | "layouts" =>
      let values ← JsonReader.arrayIndexed fun index => do
        let id ← JsonReader.natural
        let some value := pools.layouts[id]? | JsonReader.fail s!"$.layouts[{index}]: unresolved layout value {id}"
        pure value
      return {d with layouts := some values}
    | "fn_abis" => return {d with functionAbis := some (← JsonReader.arrayIndexed (fun index => parseFunctionAbi s!"$.fn_abis[{index}]" (some pools.abiArguments)))}
    | "types" => return {d with types := some (← JsonReader.arrayIndexed (fun index => denseRow "type IDs" index (·.id) (parseTypeNode s!"$.types[{index}]" pools.booleans pools.discriminants)))}
    | "byte_images" => return {d with byteImages := some (← parseByteImages)}
    | "allocations" => return {d with allocations := some (← JsonReader.arrayIndexed (fun index => parseAllocation s!"$.allocations[{index}]" pools.mir.initializationRanges pools.mir.relocations))}
    | "instances" => return {d with instances := some (← parseInstances)}
    | "compiler_abi_layout_schema" => return {d with compilerAbiLayoutSchema := some (← JsonReader.string)}
    | "bodies" =>
      let bodies ← JsonReader.arrayIndexed (fun index => DecodeMIR.parseBodySeed s!"$.bodies[{index}]" (some pools.mir))
      return {d with bodies := some (bodies.map (·.value)), bodyReferences := bodies.map (·.references)}
    | "ctfe_scalar_sources" => return {d with ctfeScalarSources := some (← JsonReader.arrayIndexed (fun _ => do JsonReader.liftExcept (CtfeMirSourceCodec.read (← Lean.Json.Parser.anyCore))))}
    | "mir_templates" => return {d with mirTemplates := some (← JsonReader.arrayIndexed (fun index => DecodeMIR.parseCopyTemplate s!"$.mir_templates[{index}]"))}
    | "compiler_coroutine_coverage" => return {d with coroutineCoverage := some (← CoroutineCoverageCodec.parse pools.mir)}
    | "body_roots" => return {d with bodyRoots := some (← JsonReader.arrayIndexed (fun index => parseBodyRoot s!"$.body_roots[{index}]"))}
    | "compiler_alloc_id_world" => return {d with compilerAllocIdWorld := ← JsonReader.nullable (parseCompilerAllocIdWorld)}
    | "selected_scope" => return {d with selectedScope := ← JsonReader.nullable (parseSelectedScope "$.selected_scope")}
    | "runtime_target_data_layout" => return {d with runtimeTargetDataLayout := ← JsonReader.nullable (CatalogDecoder.targetDataLayout)}
    | _ =>
      match ← CatalogDecoder.parseField d.queries key with
      | some queries => return {d with queries}
      | none => JsonReader.skipValue; return d
  let schema ← JsonReader.required d.schema "schema"
  let schemaVersion ← JsonReader.required d.schemaVersion "schema_version"
  let (producer, producerSettings) ← JsonReader.required d.producer "producer"
  let compilerAbiLayoutSchema ← JsonReader.required d.compilerAbiLayoutSchema "compiler_abi_layout_schema"
  let byteImages ← JsonReader.required d.byteImages "byte_images"
  let groups ← JsonReader.required d.allocations "allocations"
  let pendingNodes := groups.flatten.qsort (fun a b => a.id < b.id)
  let hexByGraph ← pendingNodes.mapM fun node => do
    match node.data with
    | some (.memory memory) =>
      match memory.bytesHex with
      | .reference id =>
        let some (_, hex) := byteImages[id]? | JsonReader.fail s!"$.allocations.byte_image_id: out of bounds byte image {id}"
        pure (some hex)
      | _ => JsonReader.fail "$.allocations: expected pooled bytes"
    | _ => pure none
  let images := byteImages.map (·.1)
  let allocations ← JsonReader.liftExcept (finishAllocations images groups pendingNodes)
  let seeds ← JsonReader.required d.bodies "bodies"
  let bodies ← seeds.mapM fun seed => do
    match seed with
    | .copyTemplate _ | .noopDrop _ | .fnPointerShim _ => pure seed
    | .material body =>
      let values ← JsonReader.liftExcept (finishBodies images #[body])
      let some value := values[0]? | JsonReader.fail "material body disappeared during allocation resolution"
      pure (BodySeed.material value)
  let compilerAllocIdWorld ← JsonReader.liftExcept (d.compilerAllocIdWorld.mapM (finishWorld allocations hexByGraph))
  let coroutineCoverage ← d.coroutineCoverage.mapM fun parsed => do
    let auxiliaryBodies ← parsed.value.auxiliaryBodies.mapM fun row => do
      let resolved ← JsonReader.liftExcept (finishBodies images #[row.body])
      let some body := resolved[0]? | JsonReader.fail "coroutine auxiliary body disappeared during allocation resolution"
      pure {row with body}
    pure {parsed.value with auxiliaryBodies}
  let definitions ← JsonReader.required d.definitions "definitions"
  let rawTraitProgram ← JsonReader.required d.traitProgram "compiler_trait_program"
  -- Invocation-local source identity index; catalog size must not multiply
  -- canonical definition lookup work. This is never shared across executions.
  let mut sourceTemplates : Std.HashMap (Nat × Nat) (Option GenericSubstitution.DefinitionTemplate) := {}
  for definition in definitions do
    let key := (definition.crateIndex, definition.index)
    if sourceTemplates.contains key then
      JsonReader.fail "trait RHS source definition reference ambiguous"
    sourceTemplates := sourceTemplates.insert key definition.genericTemplate
  let traitProgram ← JsonReader.liftExcept (TraitSelection.Codec.readProgram (fun identity => do
    let some expression := sourceTemplates[(identity.crateIndex, identity.index)]?
      | throw "trait RHS source definition reference missing"
    pure expression) rawTraitProgram)
  let value : ImportDocument := {
    producer, producerSettings, traitProgram
    predicates := ← JsonReader.required d.predicates "predicates"
    compilerPredicates := ← JsonReader.required d.compilerPredicates "compiler_predicate_queries"
    definitions := definitions
    typeConstants := ← JsonReader.required d.typeConstants "type_constants"
    files := ← JsonReader.required d.files "files"
    spans := ← JsonReader.required d.spans "spans"
    layouts := ← JsonReader.required d.layouts "layouts"
    functionAbis := ← JsonReader.required d.functionAbis "fn_abis"
    types := ← JsonReader.required d.types "types"
    allocations := allocations
    instances := ← JsonReader.required d.instances "instances"
    compilerAbiLayoutSchema := some compilerAbiLayoutSchema
    bodies := bodies
    mirTemplates := ← JsonReader.required d.mirTemplates "mir_templates"
    ctfeScalarSources := ← JsonReader.required d.ctfeScalarSources "ctfe_scalar_sources"
    coroutineCoverage := coroutineCoverage
    bodyRoots := ← JsonReader.required d.bodyRoots "body_roots"
    compilerAllocIdWorld := compilerAllocIdWorld
    selectedScope := d.selectedScope
    runtimeTargetDataLayout := d.runtimeTargetDataLayout
    queries := ← CatalogDecoder.finish d.queries
  }
  return ⟨value, schema, schemaVersion,
    d.bodyReferences ++ (d.coroutineCoverage.map (·.references)).getD #[], pools.abiArguments⟩

private def validateParsedDocument (parsed : ParsedDocument) (profile : Options) : Except String ImportDocument := do
  let d := parsed.value
  let schema := parsed.schema
  let schemaVersion := parsed.schemaVersion
  let producer := d.producer
  let predicates := d.predicates
  let compilerPredicates := d.compilerPredicates
  let definitions := d.definitions
  let typeConstants := d.typeConstants
  let spans := d.spans
  let layouts := d.layouts
  let types := d.types
  let allocations := d.allocations
  let instances := d.instances
  let compilerAbiLayoutSchema := d.compilerAbiLayoutSchema
  let bodies := d.bodies
  let bodyRoots := d.bodyRoots
  let compilerAllocIdWorld := d.compilerAllocIdWorld
  let selectedScope := d.selectedScope
  if schema != expectedSchema then throw s!"$.schema: expected `{expectedSchema}`"
  unless schemaVersion == expectedSchemaVersion do
    throw "$.schema_version: unsupported schema version"
  match d.coroutineCoverage with
  | none => throw "schema 13 requires compiler_coroutine_coverage"
  | some coverage => CoroutineCoverageCodec.validate d coverage
  if producer.miriCommit != expectedMiriCommit then throw "$.producer.miri_commit: input is from the wrong pinned Miri revision"
  if producer.rustcCommit != expectedRustcCommit then throw "$.producer.rustc_commit: input is from the wrong pinned rustc revision"
  unless compilerAbiLayoutSchema == some expectedCompilerAbiLayoutSchema do
    throw s!"$.compiler_abi_layout_schema: unsupported schema `{compilerAbiLayoutSchema}`"
  let mut crateIdentities : Std.HashMap Nat UInt64 := {}
  let mut identityCrates : Std.HashMap Nat Nat := {}
  for definition in definitions do
    if let some path := definition.rawPath then
      if let some previous := crateIdentities[definition.crateIndex]? then
        unless previous == path.stableCrateId do
          throw "$.definitions: physical crate has conflicting stable crate identities"
      if let some previous := identityCrates[path.stableCrateId.toNat]? then
        unless previous == definition.crateIndex do
          throw "$.definitions: stable crate identity belongs to multiple physical crates"
      crateIdentities := crateIdentities.insert definition.crateIndex path.stableCrateId
      identityCrates := identityCrates.insert path.stableCrateId.toNat definition.crateIndex
    if let some material := definition.adtDrop then
      if let some destructor := material.destructor then
        unless destructor < definitions.size do
          throw "$.definitions: ADT destructor definition identity out of bounds"
  if types.isEmpty then throw "$.types: input has no type graph; refusing an empty import"
  if bodies.isEmpty then throw "$.bodies: input has no MIR bodies; refusing an empty import"
  profileit "decoder.validate_predicate_queries" profile fun _ => do
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
  profileit "decoder.validate_alloc_id_world" profile fun _ => do
    if let some world := compilerAllocIdWorld then validateCompilerAllocIdWorld allocations world
  -- Scalar wire width is storage geometry, not a Pattern-validity query.
  -- Range endpoints/niches remain a separate full-layout/CTFE obligation.
  let target : RuntimeMetadata.Result Miri.ABI.RuntimeTargetDataLayout := do
    let evidence ← RuntimeMetadata.require d.runtimeTargetDataLayout "runtime_target_data_layout"
    RuntimeMetadata.importTarget evidence
  let scalarQuery : RuntimeMetadata.Result (Nat → RuntimeMetadata.Result Nat) := do
    RuntimeMetadata.scalarStorageQuery (← target) types layouts definitions typeConstants predicates
  let scalarSize := fun id => match scalarQuery with
    | .error _ => none
    | .ok query => match query id with
      | .ok bytes => some bytes
      | .error _ => none
  let bodyContext : DecodeMIR.Context := {
    typeCount := types.size, allocationCount := allocations.size,
    definitionCount := definitions.size, typeConstantCount := typeConstants.size,
    spanCount := spans.size,
    scalarSize
    typeConstantType := fun id => do
      match ← typeConstants[id]? with
      | .Value ty _ => some ty
      | .Param _ _ ty => ty
      | _ => none }
  profileit "decoder.validate_body_references" profile fun _ =>
    parsed.bodyReferences.forM (DecodeMIR.validateReferences bodyContext)
  match selectedScope with
  | some scope => profileit "decoder.selected_scope_validation" profile fun _ =>
      validateSelectedScope scope bodies instances bodyRoots
  | none => pure ()
  profileit "decoder.validate_catalog_queries" profile fun _ =>
    CatalogDecoder.validateQueries bodyContext d.queries
  CtfeMirSource.validateCatalogue spans.size (fun identity => definitions.any fun definition =>
    definition.crateIndex == identity.crateIndex && definition.index == identity.index) d.ctfeScalarSources
  let core := d
  profileit "decoder.validate_cross_table_references" profile fun _ => validateParsedTables core
  for (argument, index) in parsed.abiArguments.toList.zipIdx do
    unless argument.typeId < types.size do
      throw s!"$.abi_arguments[{index}].type: dangling type reference {argument.typeId}"
    unless argument.layoutId < layouts.size do
      throw s!"$.abi_arguments[{index}].layout: dangling layout reference {argument.layoutId}"
  pure core

/-- Parse complete input, including all forward-reference and graph checks,
before returning the final import. Completion bookkeeping stays internal. -/
def parseDocument (profile : Options := {}) : JsonReader.Parser ImportDocument := do
  let pools ← readSharedPools
  let parsed ← parseDocumentFields pools
  JsonReader.liftExcept (profileit "decoder.validate_forward_references" profile fun _ =>
    validateParsedDocument parsed profile)

def decodeJsonProfiled (text : String) (profile : Options) : Except String ExecutionInput := do
  let document ← profileit "decoder.parse" profile fun _ => JsonReader.run (parseDocument profile) text
  pure ⟨document⟩

def decodeJson (text : String) : Except String ExecutionInput := decodeJsonProfiled text {}

def decodeFile (path : System.FilePath) : IO (Except String ExecutionInput) := do
  try
    pure (decodeJson (← IO.FS.readFile path))
  catch error => pure (.error s!"could not read {path}: {error}")

def decodeAllocationMemoryEvidence (text : String) (images : Array String) : Except String AllocationMemory := do
  let images ← images.mapM fun hex => do
    unless canonicalLowerHex hex do throw "allocation byte image is not canonical lowercase hexadecimal"
    pure (AllocationBytes.image (← decodeAllocationHex hex))
  resolveAllocationMemory images "$allocation" (← JsonReader.run (parseAllocationMemoryInline "$allocation") text)

end Miri.Input
