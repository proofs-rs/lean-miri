import Miri.Input.Model
import Miri.Input.DecoderValues
import Miri.Input.ValidateTables
import Miri.Input.TypeConstCodec
import Miri.Input.DecodeMIR
import Miri.Input.CatalogDecoder
import Miri.Input.SharedPools
import Miri.Input.CoroutineCoverage
import Miri.Input.SourceTraitsDecoder
import Miri.Input.SourceVTablesDecoder
import Miri.Input.SourceAbiDecoder
import Miri.Input.SourceCastTargetsCodec
import Miri.Input.SourceHygiene

namespace Miri.Input
open Lean DecoderValues

private def validateSelectedScope (scope : SelectedScope) (_bodies : Array Body)
    (instances : Array InstanceNode) (bodyRoots : Array BodyRoot)
    (declarations : Array RootDeclaration) : Except String Unit := do
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
    let declared := declarations.any fun declaration =>
      declaration.definition == root.definitionId && declaration.defPath == root.defPath
    if !resolvedBody && !resolvedInstance && !declared then
      throw (s!"$.selected_scope.roots[{index}]" ++ ": " ++ "selected DefId and path do not resolve to an emitted body or instance")
  return ()

private structure RootDeclarationFields where
  definition : Option Nat := none
  defPath : Option String := none
  parameters : Option (Array SourceParameterKind) := none

private def parseRootDeclaration : JsonReader.Parser RootDeclaration := do
  let value ← JsonReader.object ({} : RootDeclarationFields) fun value key => do
    match key with
    | "definition" => return {value with definition := some (← JsonReader.natural)}
    | "def_path" => return {value with defPath := some (← JsonReader.string)}
    | "generic_parameters" => return {value with parameters := some (← JsonReader.array SourceTraitsDecoder.parameterKind)}
    | _ => JsonReader.skipValue; return value
  return ⟨← JsonReader.required value.definition "definition",← JsonReader.required value.defPath "def_path",
    ← JsonReader.required value.parameters "generic_parameters"⟩

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

/-- The completed import plus numeric reference bounds that require all tables.
MIR and catalogs already have their final representation. -/
private structure ParsedDocument where
  value : ImportDocument
  schema : String
  schemaVersion : Nat
  bodyReferences : Array DecodeMIR.References

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
  sourceCastTargets : Option (Array SourceCastTarget) := none
  rootDeclarations : Option (Array RootDeclaration) := none
  sourceVtables : Option SourceVTableMaterial := none
  sourceTraits : Option SourceTraitMaterial := none
  sourceAbi : Option SourceAbiMaterial := none
  schema : Option (String) := none
  schemaVersion : Option (Nat) := none
  producer : Option (Producer × Catalog.ProducerSettings) := none
  predicates : Option (Array VtablePredicate) := none
  compilerPredicates : Option (Array CompilerPredicateEvidence) := none
  definitions : Option (Array DefinitionId) := none
  typeConstants : Option (Array MIR.TypeConst) := none
  files : Option (Array String) := none
  spans : Option (Array SourceSpanData) := none
  syntaxContexts : Option (Array SyntaxContext) := none
  expansions : Option (Array SourceExpansion) := none
  types : Option (Array TypeNode) := none
  byteImages : Option (Array (AllocationBytes × String)) := none
  allocations : Option (Array (Array AllocationNode)) := none
  instances : Option (Array InstanceNode) := none
  bodies : Option (Array Body) := none
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
    | "schema" => return {d with schema := some (← JsonReader.string)}
    | "schema_version" => return {d with schemaVersion := some (← JsonReader.natural)}
    | "producer" => return {d with producer := some (← parseProducer)}
    | "source_abi" => return {d with sourceAbi := some (← SourceAbiDecoder.parse)}
    | "source_cast_targets" => return {d with sourceCastTargets := some (← JsonReader.array SourceCastTargetsCodec.parse)}
    | "source_trait_material" => return {d with sourceTraits := some (← SourceTraitsDecoder.material)}
    | "source_vtables" => return {d with sourceVtables := some (← SourceVTablesDecoder.parse)}
    | "root_declarations" => return {d with rootDeclarations := some (← JsonReader.array parseRootDeclaration)}
    | "predicates" => return {d with predicates := some (← parsePredicates)}
    | "compiler_predicate_queries" => return {d with compilerPredicates := some (← JsonReader.array decodeCompilerPredicateEvidence)}
    | "definitions" => return {d with definitions := some (← parseDefinitions)}
    | "type_constants" => return {d with typeConstants := some (← parseConstants)}
    | "files" => return {d with files := some (← parseFiles)}
    | "syntax_contexts" => return {d with syntaxContexts := some (← JsonReader.array SourceHygiene.syntaxContext)}
    | "expansions" => return {d with expansions := some (← JsonReader.array SourceHygiene.expansion)}
    | "spans" => return {d with spans := some (← JsonReader.arrayIndexed (fun index => parseSourceSpan s!"$.spans[{index}]"))}
    | "types" => return {d with types := some (← JsonReader.arrayIndexed (fun index => denseRow "type IDs" index (·.id) (parseTypeNode s!"$.types[{index}]")))}
    | "byte_images" => return {d with byteImages := some (← parseByteImages)}
    | "allocations" => return {d with allocations := some (← JsonReader.arrayIndexed (fun index => parseAllocation s!"$.allocations[{index}]" pools.mir.initializationRanges pools.mir.relocations))}
    | "instances" => return {d with instances := some (← parseInstances)}
    | "bodies" =>
      let bodies ← JsonReader.arrayIndexed (fun index => DecodeMIR.parseBody s!"$.bodies[{index}]" (some pools.mir))
      return {d with bodies := some (bodies.map (·.value)), bodyReferences := bodies.map (·.references)}
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
  let bodies ← JsonReader.liftExcept (finishBodies images (← JsonReader.required d.bodies "bodies"))
  let compilerAllocIdWorld ← JsonReader.liftExcept (d.compilerAllocIdWorld.mapM (finishWorld allocations hexByGraph))
  let coroutineCoverage ← d.coroutineCoverage.mapM fun parsed => do
    let auxiliaryBodies ← parsed.value.auxiliaryBodies.mapM fun row => do
      let resolved ← JsonReader.liftExcept (finishBodies images #[row.body])
      let some body := resolved[0]? | JsonReader.fail "coroutine auxiliary body disappeared during allocation resolution"
      pure {row with body}
    pure {parsed.value with auxiliaryBodies}
  let value : ImportDocument := {
    sourceCastTargets := ← JsonReader.required d.sourceCastTargets "source_cast_targets"
    sourceAbi := some (← JsonReader.required d.sourceAbi "source_abi")
    sourceTraits := ← JsonReader.required d.sourceTraits "source_trait_material"
    sourceVtables := ← JsonReader.required d.sourceVtables "source_vtables"
    rootDeclarations := ← JsonReader.required d.rootDeclarations "root_declarations"
    producer, producerSettings
    predicates := ← JsonReader.required d.predicates "predicates"
    compilerPredicates := ← JsonReader.required d.compilerPredicates "compiler_predicate_queries"
    definitions := ← JsonReader.required d.definitions "definitions"
    typeConstants := ← JsonReader.required d.typeConstants "type_constants"
    files := ← JsonReader.required d.files "files"
    spans := ← JsonReader.required d.spans "spans"
    syntaxContexts := ← JsonReader.required d.syntaxContexts "syntax_contexts"
    expansions := ← JsonReader.required d.expansions "expansions"
    types := ← JsonReader.required d.types "types"
    allocations := allocations
    instances := ← JsonReader.required d.instances "instances"
    bodies := bodies
    coroutineCoverage := coroutineCoverage
    bodyRoots := ← JsonReader.required d.bodyRoots "body_roots"
    compilerAllocIdWorld := compilerAllocIdWorld
    selectedScope := d.selectedScope
    runtimeTargetDataLayout := d.runtimeTargetDataLayout
    queries := ← CatalogDecoder.finish d.queries
  }
  return ⟨value, schema, schemaVersion,
    d.bodyReferences ++ (d.coroutineCoverage.map (·.references)).getD #[]⟩

private def validateParsedDocument (parsed : ParsedDocument) (profile : Options) : Except String ImportDocument := do
  let d := parsed.value
  SourceHygiene.validate d.spans d.syntaxContexts d.expansions
  SourceCastTargetsCodec.validate d.types d.sourceCastTargets
  if let some material := d.sourceAbi then SourceAbiDecoder.validate d.types d.instances material
  SourceTraitsDecoder.validate d.definitions d.typeConstants d.sourceTraits
  SourceVTablesDecoder.validate d.types d.definitions d.predicates d.instances d.sourceVtables
  let mut declared : Std.HashSet Nat := {}
  for declaration in d.rootDeclarations do
    unless declaration.definition < d.definitions.size do throw "root declaration definition is absent"
    if declared.contains declaration.definition then throw "duplicate root declaration"
    declared := declared.insert declaration.definition
    unless declaration.genericParameters.any (· != .lifetime) do
      throw "declaration-only root has no type or constant parameters"
    if d.bodyRoots.any (·.definitionId == declaration.definition) then
      throw "declaration-only root also has an executable root body"
  let schema := parsed.schema
  let schemaVersion := parsed.schemaVersion
  let producer := d.producer
  let predicates := d.predicates
  let compilerPredicates := d.compilerPredicates
  let definitions := d.definitions
  let typeConstants := d.typeConstants
  let spans := d.spans
  let types := d.types
  let allocations := d.allocations
  let instances := d.instances
  let bodies := d.bodies
  let bodyRoots := d.bodyRoots
  let compilerAllocIdWorld := d.compilerAllocIdWorld
  let selectedScope := d.selectedScope
  if schema != expectedSchema then throw s!"$.schema: expected `{expectedSchema}`"
  unless schemaVersion == expectedSchemaVersion do
    throw "$.schema_version: unsupported schema version"
  let some coverage := d.coroutineCoverage | throw "$.compiler_coroutine_coverage: source coverage is absent"
  CoroutineCoverageCodec.validate d coverage
  if producer.miriCommit != expectedMiriCommit then throw "$.producer.miri_commit: input is from the wrong pinned Miri revision"
  if producer.rustcCommit != expectedRustcCommit then throw "$.producer.rustc_commit: input is from the wrong pinned rustc revision"
  if types.isEmpty && d.rootDeclarations.isEmpty then throw "$.types: input has no type graph"
  if bodies.isEmpty && d.rootDeclarations.isEmpty then throw "$.bodies: input has no executable or declared root"
  profileit "decoder.validate_predicate_queries" profile fun _ => do
    unless compilerPredicates.size == predicates.size do
      throw "$.compiler_predicate_queries: predicate query and definition tables differ in size"
    for (query, index) in compilerPredicates.toList.zipIdx do
      unless query.id == index && query.original == index do
        throw s!"$.compiler_predicate_queries[{index}]: predicate query identity mismatch"
      unless query.typingEnvironment == "fully_monomorphized" do
        throw "predicate normalization has a non-monomorphic typing environment"
      let some definition := predicates[index]? | throw "compiler predicate table index invariant"
      unless query.autoTrait == (definition.kind == .autoTrait) do
        throw s!"$.compiler_predicate_queries[{index}]: auto-trait query disagrees with predicate definition"
      let some normalized := query.normalizedId | throw "predicate normalization result is absent"
      unless normalized < predicates.size && query.erasedId < predicates.size do
        throw s!"$.compiler_predicate_queries[{index}]: dangling normalized or erased predicate reference"
  profileit "decoder.validate_alloc_id_world" profile fun _ => do
    if let some world := compilerAllocIdWorld then validateCompilerAllocIdWorld allocations world
  let metadata ← RuntimeMetadata.ofDocument d |>.mapError toString
  let bodyContext : DecodeMIR.Context := {
    typeCount := types.size, allocationCount := allocations.size,
    definitionCount := definitions.size, typeConstantCount := typeConstants.size,
    spanCount := spans.size,
    scalarSize := fun id => (metadata.lookup id).toOption.map (·.layout.size.bytes.toNat) }
  profileit "decoder.validate_body_references" profile fun _ =>
    parsed.bodyReferences.forM (DecodeMIR.validateReferences bodyContext)
  match selectedScope with
  | some scope => profileit "decoder.selected_scope_validation" profile fun _ =>
      validateSelectedScope scope bodies instances bodyRoots d.rootDeclarations
  | none => pure ()
  profileit "decoder.validate_catalog_queries" profile fun _ =>
    CatalogDecoder.validateQueries bodyContext d.queries
  let core := d
  profileit "decoder.validate_cross_table_references" profile fun _ => validateParsedTables core
  for node in d.types do
    let checkChild := fun (child : TypeId) => do
      let some source := d.types[child]? | throw s!"missing validation child {child}"
      unless source.validationRank < node.validationRank do
        throw s!"validation rank does not decrease from type {node.id} to {child}"
    if node.sourceLayout.normalizedType != node.id then
      checkChild node.sourceLayout.normalizedType
    else
      match node.shape with
      | .adt data =>
        for variant in data.variants do
          for field in variant.fields do checkChild field.typeId
      | .array element .. | .slice element => checkChild element
      | .patternType base _ | .unsafeBinder base _ => checkChild base
      | .tuple elements => for child in elements do checkChild child
      | .closure .. | .coroutineClosure .. =>
        for child in node.sourceLayout.closureUpvars do checkChild child
      | .coroutine .. =>
        if let some layout := node.sourceLayout.coroutine then
          for child in layout.prefix do checkChild child
          for variant in layout.variants do
            for field in variant do
              let some child := layout.savedTypes[field]? | throw "missing coroutine saved type"
              checkChild child
      | _ => pure ()
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
